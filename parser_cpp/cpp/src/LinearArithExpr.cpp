#include "LinearArithExpr.h"
#include <algorithm>
#include <sstream>
#include <stdexcept>
#include <cmath>
#include <iomanip>

namespace LinearAlgebra {

// Constructors and Destructor
LinearArithExpr::LinearArithExpr() : constant_(0.0) {}

LinearArithExpr::LinearArithExpr(double constant) : constant_(constant) {}

LinearArithExpr::LinearArithExpr(const LinearArithExpr& other) 
    : terms_(other.terms_), constant_(other.constant_) {}

LinearArithExpr& LinearArithExpr::operator=(const LinearArithExpr& other) {
    if (this != &other) {
        terms_ = other.terms_;
        constant_ = other.constant_;
    }
    return *this;
}

LinearArithExpr::~LinearArithExpr() {}

// Member functions
void LinearArithExpr::addTerm(double coeff, const std::string& varName) {
    if (std::abs(coeff) < 1e-9) {
        return; 
    }
    
    int index = findTermIndex(varName);
    if (index >= 0) {   // Variable already exists, add to its coefficient
        terms_[index].coeff += coeff;
        if (std::abs(terms_[index].coeff) < 1e-9) {
            // Remove term if coefficient becomes zero
            terms_.erase(terms_.begin() + index);
        }
    } else {            // New variable, add new term
        terms_.emplace_back(coeff, varName);
    }
}

void LinearArithExpr::negate() {
    constant_ = -constant_;
    for (auto& term : terms_) {
        term.coeff = -term.coeff;
    }
}

void LinearArithExpr::multiply(double scalar) {
    constant_ *= scalar;
    for (auto& term : terms_) {
        term.coeff *= scalar;
    }
}

void LinearArithExpr::addLinearExpr(const LinearArithExpr& other) {
    constant_ += other.constant_;
    for (const auto& term : other.terms_) {
        addTerm(term.coeff, term.varName);
    }
}

void LinearArithExpr::subtractLinearExpr(const LinearArithExpr& other) {
    constant_ -= other.constant_;
    for (const auto& term : other.terms_) {
        addTerm(-term.coeff, term.varName);
    }
}

std::string LinearArithExpr::toString() const {
    std::ostringstream oss;
    bool firstTerm = true;

    // Handle constant term first if it's non-zero or if there are no variable terms
    if (std::abs(constant_) > 1e-9 || terms_.empty()) {
        oss << std::fixed << std::setprecision(4) << constant_;
        firstTerm = false;
    }
    // Handle variable terms
    for (const auto& term : terms_) {
        if (std::abs(term.coeff) < 1e-9) {
            continue; // Skip small coefficients
        }
        // Determine sign and operator
        if (firstTerm) {
            if (term.coeff < 0) oss << "-";
        } else {
            if (term.coeff < 0) {
                oss << " - ";
            } else {
                oss << " + ";
            }
        }
        double absCoeff = std::abs(term.coeff);
        // Print coefficient only if it's not 1.0
        if (std::abs(absCoeff - 1.0) > 1e-9) {
            oss << std::fixed << std::setprecision(4) << absCoeff << " * ";
        }
        oss << term.varName;
        if (firstTerm) firstTerm = false;   
    }
    // If nothing was printed, represent as "0"
    if (firstTerm) {
        oss << "0";
    }
    return oss.str();
}

void LinearArithExpr::clear() {
    terms_.clear();
    constant_ = 0.0;
}

bool LinearArithExpr::isEmpty() const {
    return terms_.empty() && std::abs(constant_) < 1e-9;
}

double LinearArithExpr::getCoefficient(const std::string& varName) const {
    int index = findTermIndex(varName);
    return (index >= 0) ? terms_[index].coeff : 0.0;
}

void LinearArithExpr::simplify() {
    // Remove terms with zero coefficients
    terms_.erase(
        std::remove_if(terms_.begin(), terms_.end(),
                      [](const Term& term) { return std::abs(term.coeff) < 1e-9; }),
        terms_.end()
    );
}

int LinearArithExpr::findTermIndex(const std::string& varName) const {
    for (size_t i = 0; i < terms_.size(); ++i) {
        if (terms_[i].varName == varName) {
            return static_cast<int>(i);
        }
    }
    return -1;
}

// Helper function to extract variable name from TVarExpr
std::string extractVariableName(const TVarExpr* varExpr) {
    if (!varExpr || !varExpr->symbol) {
        throw std::runtime_error("Invalid TVarExpr or missing symbol");
    }
    
    std::string name = varExpr->symbol->name;
    
    // Handle indexed variables (e.g., x[0], y[1,2])
    if (!varExpr->indices.empty()) {
        name += "[";
        bool first = true;
        for (const auto& index : varExpr->indices) {
            if (!first) name += ",";
            name += std::to_string(index);
            first = false;
        }
        name += "]";
    }
    
    return name;
}

// Helper function to extract numeric value from TLiteral
double extractNumericValue(const TLiteral* literal) {
    // Check if it's a TFloat or TInt
    if (const auto* floatLit = dynamic_cast<const TFloat*>(literal)) {
        return floatLit->value;
    } else if (const auto* intLit = dynamic_cast<const TInt*>(literal)) {
        return static_cast<double>(intLit->value);
    } else {
        throw VNNLibException("Unsupported literal type");
    }
}

// Main linearization function
std::unique_ptr<LinearArithExpr> linearize(const TArithExpr* arithExpr) {
    auto result = std::make_unique<LinearArithExpr>();

    // --- Base Cases ---

    if (const auto* varExpr = dynamic_cast<const TVarExpr*>(arithExpr)) {
        // Single variable with coefficient 1.0
        std::string varName = extractVariableName(varExpr);
        result->addTerm(1.0, varName);
        
    } else if (const auto* literal = dynamic_cast<const TLiteral*>(arithExpr)) {
        // Constant value
        double value = extractNumericValue(literal);
        result->setConstant(value);

    // --- Recursive Cases ---
        
    } else if (const auto* negateExpr = dynamic_cast<const TNegate*>(arithExpr)) {
        // Negation: linearize sub-expression and negate
        auto subResult = linearize(negateExpr->expr.get());
        *result = *subResult;
        result->negate();
        
    } else if (const auto* plusExpr = dynamic_cast<const TPlus*>(arithExpr)) {        
        for (const auto& operand : plusExpr->args) {
            auto operandResult = linearize(operand.get());
            result->addLinearExpr(*operandResult);
        }

    } else if (const auto* minusExpr = dynamic_cast<const TMinus*>(arithExpr)) {
        // Subtraction: first operand minus sum of remaining operands
        auto firstResult = linearize(minusExpr->head.get());
        *result = *firstResult;
        
        for (const auto& operand : minusExpr->rest) {
            auto operandResult = linearize(operand.get());
            result->subtractLinearExpr(*operandResult);
        }

    } else if (const auto* multiplyExpr = dynamic_cast<const TMultiply*>(arithExpr)) {
        std::vector<std::unique_ptr<LinearArithExpr>> operands;
        for (const auto& operand : multiplyExpr->args) {
            operands.push_back(linearize(operand.get()));
        }
        
        // Check for linearity: at most one operand can have variables
        LinearArithExpr* varOperand = nullptr;
        double constantProduct = 1.0;
        
        for (const auto& operand : operands) {
            if (operand->getNumTerms() > 0) {
                if (varOperand != nullptr) {
                    throw VNNLibException("Non-linear expression: multiplication of variables detected");
                }
                varOperand = operand.get();
            } else {
                constantProduct *= operand->getConstant();
            }
        }
        
        if (varOperand) {
            // Copy variable operand and multiply by constant product
            *result = *varOperand;
            result->multiply(constantProduct);
        } else {
            // All operands are constants
            result->setConstant(constantProduct);
        }  

    } else {
        throw VNNLibException("Unsupported TArithExpr type for linearization");
    }

    result->simplify();
    return result;
}

} // namespace LinearAlgebra
