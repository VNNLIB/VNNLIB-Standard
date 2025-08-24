#include "TypedBuilder.h"
#include <cassert>
#include <utility>

template <class T>
std::unique_ptr<T> TypedBuilder::pop(std::vector<std::unique_ptr<T>>& stack) {
    assert(!stack.empty());
    auto p = std::move(stack.back());
    stack.pop_back();
    return p;
}

template <class T>
std::vector<std::unique_ptr<T>> TypedBuilder::popRange(std::vector<std::unique_ptr<T>>& stack,
                                                        size_t lo, size_t hi) {
    std::vector<std::unique_ptr<T>> out;
    out.reserve(hi - lo);
    for (size_t i = lo; i < hi; ++i) {
        out.push_back(std::move(stack[i]));
    }
    stack.resize(lo);
    return out;
}


// --- Entry Point (API) ---

std::unique_ptr<TQuery> TypedBuilder::build(VNNLibQuery* root) {
    root->accept(this);
    return std::move(tquery_);
}


// --- ArithExpr ---

void TypedBuilder::visitVarExpr(VarExpr* p) {
    // Do type checks
    TypeChecker::visitVarExpr(p);

    auto node = std::make_unique<TVarExpr>();
    node->src_ArithExpr = static_cast<ArithExpr*>(p);
    node->indices = mapIndices(p->listint_);

    auto it = symbolMap_.find(p->variablename_);
    if (it != symbolMap_.end()) {
        node->symbol = it->second;
        node->dtype = node->symbol->dtype;
    }
    arithStack_.push_back(std::move(node));
}

void TypedBuilder::visitDoubleExpr(DoubleExpr* p) {
    TypeChecker::visitDoubleExpr(p);

    auto node = std::make_unique<TDoubleExpr>();
    node->src_ArithExpr = p;
    node->lexeme = p->sdouble_;

    try {
        node->value = std::stod(p->sdouble_);
    } catch (...) {
        node->value = 0.0;
    }
    node->dtype = DType::FloatConstant;
    arithStack_.push_back(std::move(node));
}

void TypedBuilder::visitSIntExpr(SIntExpr* p) {
    TypeChecker::visitSIntExpr(p);

    auto node = std::make_unique<TSIntExpr>();
    node->src_ArithExpr = p;
    node->lexeme = p->sint_;

    try {
        node->value = std::stoll(p->sint_);
    } catch (...) {
        node->value = 0;
    }
    node->dtype = DType::NegativeIntConstant;
    arithStack_.push_back(std::move(node));
}

void TypedBuilder::visitIntExpr(IntExpr* p) {
    TypeChecker::visitIntExpr(p);

    auto node = std::make_unique<TIntExpr>();
    node->src_ArithExpr = p;
    node->lexeme = p->int_;

    try {
        node->value = std::stoll(p->int_);
    } catch (...) {
        node->value = 0;
    }
    node->dtype = DType::PositiveIntConstant;
    arithStack_.push_back(std::move(node));
}

void TypedBuilder::visitNegate(Negate* p) {
    auto mark = arithStack_.size();
    TypeChecker::visitNegate(p);     // visits child using overridden function (dynamic dispatch)

    auto node = std::make_unique<TNegate>();
    node->src_ArithExpr = static_cast<ArithExpr*>(p);

    assert(arithStack_.size() == mark + 1); // ensure only one child was pushed
    node->expr = pop(arithStack_);
    node->dtype = getContext().currentDataType;
    arithStack_.push_back(std::move(node));
}

void TypedBuilder::visitPlus(Plus* p) {
    const auto mark = arithStack_.size();
    TypeChecker::visitPlus(p);       // visits list of args

    auto node = std::make_unique<TPlus>();
    node->src_ArithExpr = static_cast<ArithExpr*>(p);

    node->args = popRange(arithStack_, mark, arithStack_.size());
    node->dtype = getContext().currentDataType;
    arithStack_.push_back(std::move(node));
}

void TypedBuilder::visitMinus(Minus* p) {
    const auto mark = arithStack_.size();
    TypeChecker::visitMinus(p);      // visits head + rest

    auto node = std::make_unique<TMinus>();
    node->src_ArithExpr = static_cast<ArithExpr*>(p);

    auto children = popRange(arithStack_, mark, arithStack_.size());
    assert(!children.empty());        // subtraction must have at least one operand

    node->head = std::move(children.front());
    children.erase(children.begin());
    node->rest = std::move(children);
    node->dtype = getContext().currentDataType;
    arithStack_.push_back(std::move(node));
}

void TypedBuilder::visitMultiply(Multiply* p) {
    const auto mark = arithStack_.size();
    TypeChecker::visitMultiply(p);

    auto node = std::make_unique<TMultiply>();
    node->src_ArithExpr = static_cast<ArithExpr*>(p);
    node->args = popRange(arithStack_, mark, arithStack_.size());
    node->dtype = getContext().currentDataType;
    arithStack_.push_back(std::move(node));
}


// --- BoolExpr ---

void TypedBuilder::visitGreaterThan(GreaterThan* p) {
    // Let base visit both sides
    TypeChecker::visitGreaterThan(p);
    auto rhs = pop(arithStack_);
    auto lhs = pop(arithStack_);

    auto node = std::make_unique<TGreaterThan>();
    node->src_BoolExpr = static_cast<BoolExpr*>(p);

    node->lhs = std::move(lhs);
    node->rhs = std::move(rhs);
    boolStack_.push_back(std::move(node));
}

void TypedBuilder::visitLessThan(LessThan* p) {
    TypeChecker::visitLessThan(p);
    auto rhs = pop(arithStack_);
    auto lhs = pop(arithStack_);

    auto node = std::make_unique<TLessThan>();
    node->src_BoolExpr = static_cast<BoolExpr*>(p);

    node->lhs = std::move(lhs);
    node->rhs = std::move(rhs);
    boolStack_.push_back(std::move(node));
}

void TypedBuilder::visitGreaterEqual(GreaterEqual* p) {
    TypeChecker::visitGreaterEqual(p);
    auto rhs = pop(arithStack_);
    auto lhs = pop(arithStack_);

    auto node = std::make_unique<TGreaterEqual>();
    node->src_BoolExpr = static_cast<BoolExpr*>(p);

    node->lhs = std::move(lhs);
    node->rhs = std::move(rhs);
    boolStack_.push_back(std::move(node));
}

void TypedBuilder::visitLessEqual(LessEqual* p) {
    TypeChecker::visitLessEqual(p);
    auto rhs = pop(arithStack_);
    auto lhs = pop(arithStack_);

    auto node = std::make_unique<TLessEqual>();
    node->src_BoolExpr = static_cast<BoolExpr*>(p);

    node->lhs = std::move(lhs);
    node->rhs = std::move(rhs);
    boolStack_.push_back(std::move(node));
}

void TypedBuilder::visitNotEqual(NotEqual* p) {
    TypeChecker::visitNotEqual(p);
    auto rhs = pop(arithStack_);
    auto lhs = pop(arithStack_);

    auto node = std::make_unique<TNotEqual>();
    node->src_BoolExpr = static_cast<BoolExpr*>(p);

    node->lhs = std::move(lhs);
    node->rhs = std::move(rhs);
    boolStack_.push_back(std::move(node));
}

void TypedBuilder::visitEqual(Equal* p) {
    TypeChecker::visitEqual(p);
    auto rhs = pop(arithStack_);
    auto lhs = pop(arithStack_);

    auto node = std::make_unique<TEqual>();
    node->src_BoolExpr = static_cast<BoolExpr*>(p);

    node->lhs = std::move(lhs);
    node->rhs = std::move(rhs);
    boolStack_.push_back(std::move(node));
}

void TypedBuilder::visitAnd(And* p) {
    const auto mark = boolStack_.size();
    TypeChecker::visitAnd(p);        // visits list of args

    auto node = std::make_unique<TAnd>();
    node->src_BoolExpr = static_cast<BoolExpr*>(p);

    node->args = popRange(boolStack_, mark, boolStack_.size());
    boolStack_.push_back(std::move(node));
}

void TypedBuilder::visitOr(Or* p) {
    const auto mark = boolStack_.size();
    TypeChecker::visitOr(p);       

    auto node = std::make_unique<TOr>();
    node->src_BoolExpr = static_cast<BoolExpr*>(p);

    node->args = popRange(boolStack_, mark, boolStack_.size());
    boolStack_.push_back(std::move(node));
}

// --- Assertion ---

void TypedBuilder::visitAssert(Assert* p) {
    TypeChecker::visitAssert(p);

    auto node = std::make_unique<TAssertion>();
    node->src_Assertion = static_cast<Assertion*>(p);

    node->cond = pop(boolStack_);
    tquery_->assertions.push_back(std::move(node));
}

// --- Definitions ---

void TypedBuilder::visitInputDef(InputDef* p) {
    TypeChecker::visitInputDef(p);

    auto symbol = std::make_shared<SymbolInfo>(
        p->variablename_, "", mapDType(p->elementtype_), mapShape(p->tensorshape_), SymbolKind::Input
    );
    if (!netStack_.empty()) symbol->networkName = netStack_.back()->networkName;
    symbolMap_[symbol->name] = symbol;

    auto node = std::make_unique<TInputDefinition>();
    node->symbol = std::move(symbol);
    node->src_InputDefinition = static_cast<InputDefinition*>(p);

    auto lastNetwork = netStack_.back();
    lastNetwork->inputs.push_back(std::move(node));
}

void TypedBuilder::visitInputOnnxDef(InputOnnxDef* p) {
    TypeChecker::visitInputOnnxDef(p);

    auto symbol = std::make_shared<SymbolInfo>(
        p->variablename_, p->string_, mapDType(p->elementtype_), mapShape(p->tensorshape_), SymbolKind::Input
    );
    if (!netStack_.empty()) symbol->networkName = netStack_.back()->networkName;
    symbolMap_[symbol->name] = symbol;

    auto node = std::make_unique<TInputDefinition>();
    node->symbol = std::move(symbol);
    node->src_InputDefinition = static_cast<InputDefinition*>(p);

    auto lastNetwork = netStack_.back();
    lastNetwork->inputs.push_back(std::move(node));
}

void TypedBuilder::visitHiddenDef(HiddenDef* p) {
    TypeChecker::visitHiddenDef(p);

    auto symbol = std::make_shared<SymbolInfo>(
        p->variablename_, p->string_, mapDType(p->elementtype_), mapShape(p->tensorshape_), SymbolKind::Hidden
    );
    if (!netStack_.empty()) symbol->networkName = netStack_.back()->networkName;
    symbolMap_[symbol->name] = symbol;

    auto node = std::make_unique<THiddenDefinition>();
    node->symbol = std::move(symbol);
    node->src_HiddenDefinition = static_cast<HiddenDefinition*>(p);

    auto lastNetwork = netStack_.back();
    lastNetwork->hidden.push_back(std::move(node));
}

void TypedBuilder::visitOutputDef(OutputDef* p) {
    TypeChecker::visitOutputDef(p);

    auto symbol = std::make_shared<SymbolInfo>(
        p->variablename_, "", mapDType(p->elementtype_), mapShape(p->tensorshape_), SymbolKind::Output
    );
    if (!netStack_.empty()) symbol->networkName = netStack_.back()->networkName;
    symbolMap_[symbol->name] = symbol;

    auto node = std::make_unique<TOutputDefinition>();
    node->symbol = std::move(symbol);
    node->src_OutputDefinition = static_cast<OutputDefinition*>(p);

    auto lastNetwork = netStack_.back();
    lastNetwork->outputs.push_back(std::move(node));
}

void TypedBuilder::visitOutputOnnxDef(OutputOnnxDef* p) {
    TypeChecker::visitOutputOnnxDef(p);

    auto symbol = std::make_shared<SymbolInfo>(
        p->variablename_, p->string_, mapDType(p->elementtype_), mapShape(p->tensorshape_), SymbolKind::Output
    );
    if (!netStack_.empty()) symbol->networkName = netStack_.back()->networkName;
    symbolMap_[symbol->name] = symbol;

    auto node = std::make_unique<TOutputDefinition>();
    node->symbol = std::move(symbol);
    node->src_OutputDefinition = static_cast<OutputDefinition*>(p);

    auto lastNetwork = netStack_.back();
    lastNetwork->outputs.push_back(std::move(node));
}


// --- Network ---

void TypedBuilder::visitNetworkDef(NetworkDef* p) {
    TypeChecker::visitNetworkDefinition(p);

    auto node = std::make_unique<TNetworkDefinition>();
    node->src_NetworkDefinition = static_cast<NetworkDefinition*>(p);
    node->networkName = p->variablename_;

    // Add network to context stack that can be accessed by its children
    netStack_.push_back(node.get());
    TypeChecker::visitNetworkDef(p);

    netStack_.pop_back();
    tquery_->networks.push_back(std::move(node)); // Add network to query
}

// --- Query ---

void TypedBuilder::visitVNNLibQuery(VNNLibQuery* p) {
    tquery_ = std::make_unique<TQuery>();
    tquery_->src_Query = static_cast<Query*>(p);

    TypeChecker::visitVNNLibQuery(p);
}