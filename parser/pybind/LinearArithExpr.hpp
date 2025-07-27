#ifndef LINEAR_VNNLIB_WRAPPERS_HPP
#define LINEAR_VNNLIB_WRAPPERS_HPP

#include <vector>
#include <string>
#include <memory>
#include <stdexcept>

#include "VNNLIBWrappers.hpp" 
#include "ExtendedAbsyn.h"  

class LinearExpression;
class LinearBoolExprWrapper;
class LinearAssertionWrapper;
class LinearQueryWrapper;


class LinearArithExpression {
public:
    std::vector<double> coeffs;
    std::vector<std::string> vars;
    double constant;

    LinearArithExpression(LinearArithExpr c_struct) : constant(0.0) {
        if (!c_struct) {
            throw std::runtime_error("Cannot create LinearArithExpression from null C struct.");
        }
        
        constant = c_struct->constant;
        for (int i = 0; i < c_struct->num_terms; ++i) {
            coeffs.push_back(c_struct->coeffs[i]);
            vars.push_back(std::string(c_struct->vars[i]));
        }

        freeLinearArithExpr(c_struct);
    }
    
    virtual ~LinearArithExpression() = default;
};


class LinearBoolExprWrapper {
public:
    virtual ~LinearBoolExprWrapper() = default;
};


class LinearComparisonExpr : public LinearBoolExprWrapper {
public:
    std::unique_ptr<LinearArithExpression> expr1;
    std::unique_ptr<LinearArithExpression> expr2;

    LinearComparisonExpr(std::unique_ptr<LinearArithExpression> e1, std::unique_ptr<LinearArithExpression> e2)
        : expr1(std::move(e1)), expr2(std::move(e2)) {}
};

class LinearGreaterThan : public LinearComparisonExpr { using LinearComparisonExpr::LinearComparisonExpr; };
class LinearLessThan    : public LinearComparisonExpr { using LinearComparisonExpr::LinearComparisonExpr; };
class LinearGreaterEqual: public LinearComparisonExpr { using LinearComparisonExpr::LinearComparisonExpr; };
class LinearLessEqual   : public LinearComparisonExpr { using LinearComparisonExpr::LinearComparisonExpr; };
class LinearEqual       : public LinearComparisonExpr { using LinearComparisonExpr::LinearComparisonExpr; };
class LinearNotEqual    : public LinearComparisonExpr { using LinearComparisonExpr::LinearComparisonExpr; };


class LinearConnectiveExpr : public LinearBoolExprWrapper {
public:
    std::vector<std::unique_ptr<LinearBoolExprWrapper>> operands;
};

class LinearAnd : public LinearConnectiveExpr {};
class LinearOr  : public LinearConnectiveExpr {};


class LinearAssertionWrapper {
public:
    virtual ~LinearAssertionWrapper() = default;
};

class LinearAssert : public LinearAssertionWrapper {
public:
    std::unique_ptr<LinearBoolExprWrapper> expr;
    LinearAssert(std::unique_ptr<LinearBoolExprWrapper> e) : expr(std::move(e)) {}
};


class LinearQueryWrapper {
public:
    std::vector<NetworkDefinitionWrapper*> networks;
    std::vector<std::unique_ptr<LinearAssertionWrapper>> assertions;

    virtual ~LinearQueryWrapper() = default;
};


class LinearVNNLibQuery : public LinearQueryWrapper {};


// Helper functions to create LinearVNNLibQuery from VNNLibQuery

std::unique_ptr<LinearArithExpression> lineariseArithExpr(ArithExprWrapper* arith_expr) {
    if (!arith_expr) return nullptr;
    LinearArithExpr c_linear_struct = linearise(arith_expr->get_struct());
    if (!c_linear_struct) {
        throw std::runtime_error("The C linearise function failed for an arithmetic expression.");
    }
    return std::make_unique<LinearArithExpression>(c_linear_struct);
}

std::unique_ptr<LinearBoolExprWrapper> lineariseBoolExpr(BoolExprWrapper* boolExpr) {
    if (!boolExpr) return nullptr;

    if (auto gt = dynamic_cast<GreaterThan*>(boolExpr)) {
        return std::make_unique<LinearGreaterThan>(lineariseArithExpr(gt->arithexpr_1.get()), lineariseArithExpr(gt->arithexpr_2.get()));
    }

    if (auto lt = dynamic_cast<LessThan*>(boolExpr)) {
        return std::make_unique<LinearLessThan>(lineariseArithExpr(lt->arithexpr_1.get()), lineariseArithExpr(lt->arithexpr_2.get()));
    }

    if (auto ge = dynamic_cast<GreaterEqual*>(boolExpr)) {
        return std::make_unique<LinearGreaterEqual>(lineariseArithExpr(ge->arithexpr_1.get()), lineariseArithExpr(ge->arithexpr_2.get()));
    }
    if (auto le = dynamic_cast<LessEqual*>(boolExpr)) {
        return std::make_unique<LinearLessEqual>(lineariseArithExpr(le->arithexpr_1.get()), lineariseArithExpr(le->arithexpr_2.get()));
    }
    if (auto eq = dynamic_cast<Equal*>(boolExpr)) {
        return std::make_unique<LinearEqual>(lineariseArithExpr(eq->arithexpr_1.get()), lineariseArithExpr(eq->arithexpr_2.get()));
    }
    if (auto neq = dynamic_cast<NotEqual*>(boolExpr)) {
        return std::make_unique<LinearNotEqual>(lineariseArithExpr(neq->arithexpr_1.get()), lineariseArithExpr(neq->arithexpr_2.get()));
    }

    if (auto and_expr = dynamic_cast<And*>(boolExpr)) {
        auto linear_and = std::make_unique<LinearAnd>();
        if (and_expr->listboolexpr_) {
            BoolExprList *currentNode = dynamic_cast<BoolExprList*>(and_expr->listboolexpr_.get());
            for (auto it = currentNode->begin(); it != currentNode->end(); ++it) {
                linear_and->operands.push_back(lineariseBoolExpr(*it));
            }
        }
        return linear_and;
    }

    if (auto or_expr = dynamic_cast<Or*>(boolExpr)) {
        auto linear_or = std::make_unique<LinearOr>();
        if (or_expr->listboolexpr_) {
            auto currentNode = dynamic_cast<BoolExprList*>(or_expr->listboolexpr_.get());
            for (auto it = currentNode->begin(); it != currentNode->end(); ++it) {
                linear_or->operands.push_back(lineariseBoolExpr(*it));
            }
        }
        return linear_or;
    }

    throw std::runtime_error("Unknown BoolExpr type during linearization.");
}

std::unique_ptr<LinearAssertionWrapper> lineariseAssertion(AssertionWrapper* assertion) {
    if (!assertion) return nullptr;

    if (auto assert_expr = dynamic_cast<Assert*>(assertion)) {
        auto linearBoolExpr = lineariseBoolExpr(assert_expr->boolexpr_.get());
        return std::make_unique<LinearAssert>(std::move(linearBoolExpr));
    }

    throw std::runtime_error("Unknown Assertion type during linearization.");
}

std::unique_ptr<LinearVNNLibQuery> lineariseQuery(const VNNLibQuery* query) {
    if (!query) return nullptr;

    auto linear_query = std::make_unique<LinearVNNLibQuery>();

    auto current_network = dynamic_cast<NetworkDefinitionList*>(query->listnetworkdefinition_.get());
    for (auto it = current_network->begin(); it != current_network->end(); ++it) {
        linear_query->networks.push_back(*it);
    }

    auto current_assertion = dynamic_cast<AssertionList*>(query->listassertion_.get());
    for (auto it = current_assertion->begin(); it != current_assertion->end(); ++it) {
        linear_query->assertions.push_back(lineariseAssertion(*it));
    }

    return linear_query;
}

#endif 