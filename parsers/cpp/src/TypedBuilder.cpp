#include "TypedBuilder.h"

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
    node->indices = mapIndices(p->listnumber_);

    auto it = symbolMap_.find(p->variablename_->string_);
    if (it != symbolMap_.end()) {
        node->symbol = it->second;
        node->line = p->variablename_->integer_;
        node->dtype = node->symbol->dtype;
    }
    arithStack_.push_back(std::move(node));
}

void TypedBuilder::visitValExpr(ValExpr* p) {
    TypeChecker::visitValExpr(p);

    std::unique_ptr<TLiteral> node;
    auto node_str = p->number_->string_;
    if (node_str.find('.') != std::string::npos) {
        node = std::make_unique<TFloat>();
        static_cast<TFloat*>(node.get())->value = std::stod(node_str);
    } else {
        node = std::make_unique<TInt>();
        static_cast<TInt*>(node.get())->value = std::stoll(node_str);
    }
    
    node->lexeme = node_str;
    node->line = p->number_->integer_;
    node->src_ArithExpr = static_cast<ArithExpr*>(p);
    arithStack_.push_back(std::move(node));
}

void TypedBuilder::visitNegate(Negate* p) {
    auto mark = arithStack_.size();
    // visits child using overridden function (dynamic dispatch). The child is then pushed onto the stack.
    TypeChecker::visitNegate(p);

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
        p->variablename_->string_, mapDType(p->elementtype_), mapShape(p->tensorshape_), SymbolKind::Input, ""
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
        p->variablename_->string_, mapDType(p->elementtype_), mapShape(p->tensorshape_), SymbolKind::Input, p->string_
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
        p->variablename_->string_, mapDType(p->elementtype_), mapShape(p->tensorshape_), SymbolKind::Hidden, p->string_
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
        p->variablename_->string_, mapDType(p->elementtype_), mapShape(p->tensorshape_), SymbolKind::Output, ""
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
        p->variablename_->string_, mapDType(p->elementtype_), mapShape(p->tensorshape_), SymbolKind::Output, p->string_
    );
    if (!netStack_.empty()) symbol->networkName = netStack_.back()->networkName;
    symbolMap_[symbol->name] = symbol;

    auto node = std::make_unique<TOutputDefinition>();
    node->symbol = std::move(symbol);
    node->src_OutputDefinition = static_cast<OutputDefinition*>(p);

    auto lastNetwork = netStack_.back();
    lastNetwork->outputs.push_back(std::move(node));
}

// --- Relations ---

void TypedBuilder::visitEqualTo(EqualTo *p) {
    TypeChecker::visitEqualTo(p);

    if (!netStack_.empty()) {
        netStack_.back()->equalTo = p->variablename_->string_;
    }
}

void TypedBuilder::visitIsomorphicTo(IsomorphicTo *p) {
    TypeChecker::visitIsomorphicTo(p);

    if (!netStack_.empty()) {
        netStack_.back()->isometricTo = p->variablename_->string_;
    }
}

// --- Network ---

void TypedBuilder::visitNetworkDef(NetworkDef* p) {
    TypeChecker::visitNetworkDefinition(p);

    auto node = std::make_unique<TNetworkDefinition>();
    node->src_NetworkDefinition = static_cast<NetworkDefinition*>(p);
    node->networkName = p->variablename_->string_;

    // Add network to context stack that can be accessed by its children
    netStack_.push_back(node.get());
    TypeChecker::visitNetworkDef(p);

    netStack_.pop_back();
    tquery_->networks.push_back(std::move(node)); // Add network to query
}

// --- Version ---

void TypedBuilder::visitVNNLibVersion(VNNLibVersion *p) {
    TypeChecker::visitVNNLibVersion(p);

    auto node = std::make_unique<TVersion>();
    node->src_Version = static_cast<Version*>(p);
    // Format: <Major.Minor>
    node->major = std::stoi(p->versiontoken_->string_.substr(1));  
    node->minor = std::stoi(p->versiontoken_->string_.substr(3));
    tquery_->version = std::move(node);    
}

// --- Query ---

void TypedBuilder::visitVNNLibQuery(VNNLibQuery* p) {
    tquery_ = std::make_unique<TQuery>();
    tquery_->src_Query = static_cast<Query*>(p);

    TypeChecker::visitVNNLibQuery(p);
}

// --- Unused visitor methods ---
// These methods delegate to the parent TypeChecker class

void TypedBuilder::visitScalarDims(ScalarDims *p) {
    TypeChecker::visitScalarDims(p);
}

void TypedBuilder::visitTensorDims(TensorDims *p) {
    TypeChecker::visitTensorDims(p);
}

void TypedBuilder::visitGenericElementType(GenericElementType *p) {
    TypeChecker::visitGenericElementType(p);
}

void TypedBuilder::visitElementTypeF16(ElementTypeF16 *p) {
    TypeChecker::visitElementTypeF16(p);
}

void TypedBuilder::visitElementTypeF32(ElementTypeF32 *p) {
    TypeChecker::visitElementTypeF32(p);
}

void TypedBuilder::visitElementTypeF64(ElementTypeF64 *p) {
    TypeChecker::visitElementTypeF64(p);
}

void TypedBuilder::visitElementTypeBF16(ElementTypeBF16 *p) {
    TypeChecker::visitElementTypeBF16(p);
}

void TypedBuilder::visitElementTypeF8E4M3FN(ElementTypeF8E4M3FN *p) {
    TypeChecker::visitElementTypeF8E4M3FN(p);
}

void TypedBuilder::visitElementTypeF8E5M2(ElementTypeF8E5M2 *p) {
    TypeChecker::visitElementTypeF8E5M2(p);
}

void TypedBuilder::visitElementTypeF8E4M3FNUZ(ElementTypeF8E4M3FNUZ *p) {
    TypeChecker::visitElementTypeF8E4M3FNUZ(p);
}

void TypedBuilder::visitElementTypeF8E5M2FNUZ(ElementTypeF8E5M2FNUZ *p) {
    TypeChecker::visitElementTypeF8E5M2FNUZ(p);
}

void TypedBuilder::visitElementTypeF4E2M1(ElementTypeF4E2M1 *p) {
    TypeChecker::visitElementTypeF4E2M1(p);
}

void TypedBuilder::visitElementTypeI8(ElementTypeI8 *p) {
    TypeChecker::visitElementTypeI8(p);
}

void TypedBuilder::visitElementTypeI16(ElementTypeI16 *p) {
    TypeChecker::visitElementTypeI16(p);
}

void TypedBuilder::visitElementTypeI32(ElementTypeI32 *p) {
    TypeChecker::visitElementTypeI32(p);
}

void TypedBuilder::visitElementTypeI64(ElementTypeI64 *p) {
    TypeChecker::visitElementTypeI64(p);
}

void TypedBuilder::visitElementTypeU8(ElementTypeU8 *p) {
    TypeChecker::visitElementTypeU8(p);
}

void TypedBuilder::visitElementTypeU16(ElementTypeU16 *p) {
    TypeChecker::visitElementTypeU16(p);
}

void TypedBuilder::visitElementTypeU32(ElementTypeU32 *p) {
    TypeChecker::visitElementTypeU32(p);
}

void TypedBuilder::visitElementTypeU64(ElementTypeU64 *p) {
    TypeChecker::visitElementTypeU64(p);
}

void TypedBuilder::visitElementTypeC64(ElementTypeC64 *p) {
    TypeChecker::visitElementTypeC64(p);
}

void TypedBuilder::visitElementTypeC128(ElementTypeC128 *p) {
    TypeChecker::visitElementTypeC128(p);
}

void TypedBuilder::visitElementTypeBool(ElementTypeBool *p) {
    TypeChecker::visitElementTypeBool(p);
}

void TypedBuilder::visitElementTypeString(ElementTypeString *p) {
    TypeChecker::visitElementTypeString(p);
}

void TypedBuilder::visitListArithExpr(ListArithExpr *p) {
    TypeChecker::visitListArithExpr(p);
}

void TypedBuilder::visitListBoolExpr(ListBoolExpr *p) {
    TypeChecker::visitListBoolExpr(p);
}

void TypedBuilder::visitListAssertion(ListAssertion *p) {
    TypeChecker::visitListAssertion(p);
}

void TypedBuilder::visitListInputDefinition(ListInputDefinition *p) {
    TypeChecker::visitListInputDefinition(p);
}

void TypedBuilder::visitListHiddenDefinition(ListHiddenDefinition *p) {
    TypeChecker::visitListHiddenDefinition(p);
}

void TypedBuilder::visitListOutputDefinition(ListOutputDefinition *p) {
    TypeChecker::visitListOutputDefinition(p);
}

void TypedBuilder::visitListCompStm(ListCompStm *p) {
    TypeChecker::visitListCompStm(p);
}

void TypedBuilder::visitListNetworkDefinition(ListNetworkDefinition *p) {
    TypeChecker::visitListNetworkDefinition(p);
}

void TypedBuilder::visitListNumber(ListNumber *p) {
    TypeChecker::visitListNumber(p);
}

void TypedBuilder::visitInteger(Integer x) {
    TypeChecker::visitInteger(x);
}

void TypedBuilder::visitChar(Char x) {
    TypeChecker::visitChar(x);
}

void TypedBuilder::visitDouble(Double x) {
    TypeChecker::visitDouble(x);
}

void TypedBuilder::visitString(String x) {
    TypeChecker::visitString(x);
}

void TypedBuilder::visitIdent(Ident x) {
    TypeChecker::visitIdent(x);
}

void TypedBuilder::visitVariableName(VariableName *x) {
    TypeChecker::visitVariableName(x);
}

void TypedBuilder::visitNumber(Number *p) {
    TypeChecker::visitNumber(p);
}

void TypedBuilder::visitVersionToken(VersionToken *p) {
    TypeChecker::visitVersionToken(p);
}
