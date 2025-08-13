#include "TypeChecker.h"

// Utility function for string formatting (@iFreilicht)
template<typename ... Args>
std::string string_format( const std::string& format, Args ... args )
{
    int size_s = std::snprintf( nullptr, 0, format.c_str(), args ... ) + 1; // Extra space for '\0'
    if( size_s <= 0 ){ throw std::runtime_error( "Error during formatting." ); }
    auto size = static_cast<size_t>( size_s );
    std::unique_ptr<char[]> buf( new char[ size ] );
    std::snprintf( buf.get(), size, format.c_str(), args ... );
    return std::string( buf.get(), buf.get() + size - 1 ); // We don't want the '\0' inside
}


// TypeCheckError methods
std::string TypeCheckError::makeJson(ErrorCode code, 
                                    std::string message, 
                                    std::string offending_symbol, 
                                    std::string hint) {
    nlohmann::json j;
    j["errorCode"] = codeToString(code);  // Use string representation instead of int
    j["message"] = message;
    j["offendingSymbol"] = offending_symbol;
    j["hint"] = hint;
    return j.dump();
}

std::string TypeCheckError::codeToString(ErrorCode code) {
    switch (code) {
        case MultipleDeclaration: return "MultipleDeclaration";
        case TypeMismatch: return "TypeMismatch";
        case UndeclaredVariable: return "UndeclaredVariable";
        case IndexOutOfBounds: return "IndexOutOfBounds";
        case TooManyIndices: return "TooManyIndices";
        case NotEnoughIndices: return "NotEnoughIndices";
        case UnexpectedOnnxName: return "UnexpectedOnnxName";
        case InvalidDimensions: return "InvalidDimensions";
        default: return "UnknownErrorCode";
    }
}

TypeCheckError::TypeCheckError(ErrorCode code,
                               std::string message,
                               std::string offending_symbol,
                               std::string hint) :
    std::runtime_error(makeJson(code, message, offending_symbol, hint)),
    code_(code),
    message_(message),
    offending_symbol_(std::move(offending_symbol)),
    hint_(std::move(hint)) {}


// SymbolInfo methods

bool SymbolInfo::operator==(const SymbolInfo &other) const {
    return name == other.name;
}

// Context methods

Context::Context(TypeChecker* typeChecker) :
    currentDataType(nullptr),
    lastScannedVariable(""),
    usesOnnxNames(OnnxNamesUsage::Unknown),
    symbolMap(),
    checker(typeChecker) {}

bool Context::addSymbol(VariableName name, ElementType *type, ListInt shape, SymbolKind kind, std::string onnxName) {
    auto it = symbolMap.find(name);
    if (it != symbolMap.end()) {
        if (checker) {
            checker->addError(
                MultipleDeclaration,
                "Duplicate variable declaration",
                name,
                "Variable names must be unique within the context."
            );
        }
        return false;
    }

    std::vector<int> shapeVec;

    for (const auto &dim : shape) {
        int dimension = std::stoi(dim);
        if (dimension < 1) {
            if (checker) {
                checker->addError(
                    InvalidDimensions,
                    "Invalid dimension size",
                    name,
                    "Dimension sizes must be positive integers."
                );
            }
            return false;
        }
        shapeVec.push_back(dimension);
    }

    auto [insertIt, inserted] = symbolMap.try_emplace(
        name,
        name,
        std::move(type),
        std::move(shapeVec),
        kind,
        std::move(onnxName)
    );

    if (!inserted) {
        if (checker) {
            checker->addError(
                MultipleDeclaration,
                "Failed to add symbol to context during type checking.",
                name,
                ""
            );
        }
        return false;
    }
    
    return true;
}

SymbolInfo *Context::getSymbol(const VariableName &name) {
    auto it = symbolMap.find(name);
    if (it != symbolMap.end()) {
        return &it->second;
    }
    return nullptr; // Symbol not found
}

// Traversal methods

TypeChecker::TypeChecker() {
    registerTypeFlags();  // Register type flags for the type system
    ctx = new Context(this);
}

TypeChecker::~TypeChecker() {
    delete ctx;
}

// Error collection and reporting methods
void TypeChecker::addError(ErrorCode code, const std::string& message, 
                          const std::string& offending_symbol, 
                          const std::string& hint) {
    errors.emplace_back(code, message, offending_symbol, hint);
}

bool TypeChecker::hasErrors() const {
    return !errors.empty();
}

size_t TypeChecker::getErrorCount() const {
    return errors.size();
}

std::string TypeChecker::getErrorReport(bool json) const {
    if (errors.empty()) {
        return json ? "{\"status\":\"success\",\"errors\":[]}" : "No errors found.";
    }

    if (json) {
        nlohmann::json report;
        report["status"] = "failure";
        report["error_count"] = errors.size();
        report["errors"] = nlohmann::json::array();
        
        for (const auto& error : errors) {
            nlohmann::json errorJson = nlohmann::json::parse(error.what());
            report["errors"].push_back(errorJson);
        }
        
        return report.dump(2);
    } else {
        std::string report = "Type Check Results:\n";
        report += "==================\n";
        report += "Total errors found: " + std::to_string(errors.size()) + "\n\n";
        
        for (size_t i = 0; i < errors.size(); ++i) {
            nlohmann::json errorJson = nlohmann::json::parse(errors[i].what());
            report += "Error " + std::to_string(i + 1) + ":\n";
            
            // Error code is now a string
            std::string errorCodeStr = errorJson["errorCode"].get<std::string>();
            
            report += "  Code: " + errorCodeStr + "\n";
            report += "  Message: " + errorJson["message"].get<std::string>() + "\n";
            if (!errorJson["offendingSymbol"].get<std::string>().empty()) {
                report += "  Symbol: " + errorJson["offendingSymbol"].get<std::string>() + "\n";
            }
            if (!errorJson["hint"].get<std::string>().empty()) {
                report += "  Hint: " + errorJson["hint"].get<std::string>() + "\n";
            }
            report += "\n";
        }
        
        return report;
    }
}

void TypeChecker::clearErrors() {
    errors.clear();
}

void TypeChecker::visitListInt(ListInt *p) {
    for (const auto &intValue : *p) {
        visitInt(intValue);
    }
}

void TypeChecker::visitTensorShape(TensorShape *p) {} // abstract class

void TypeChecker::visitScalarDims(ScalarDims *p) {}

void TypeChecker::visitTensorDims(TensorDims *p) {
    visitListInt(p->listint_);
}

void TypeChecker::visitArithExpr(ArithExpr *p) {} // abstract class

void TypeChecker::visitVarExpr(VarExpr *p) {
    ElementType* nodeType;
    ElementType* exprType = ctx->currentDataType;
    // bool isPreviousTypeUndefined = (exprType == nullptr); // Unused variable

    const SymbolInfo *symbol = ctx->getSymbol(p->variablename_);
    if (!symbol) {
        addError(
            UndeclaredVariable,
            "Undeclared variable",
            p->variablename_,
            "Variable must be declared before use."
        );
        return;
    }

    // Apply scope checking to tensor access
    visitTensorElement(&p->variablename_, convertListIntToVector(p->listint_));

    nodeType = symbol->type;

    if (exprType == nullptr) {
        ctx->currentDataType = nodeType;
        ctx->lastScannedVariable = p->variablename_;
    } else if (isConstant(*exprType)) {
        // Don't delete exprType - it might not be dynamically allocated
        if (sameFamily(*nodeType, *exprType)) {  // Fixed argument order: (variable, constant)
            ctx->currentDataType = nodeType;
            ctx->lastScannedVariable = p->variablename_;
        } else {
            string_format("Expected a %s type to match constant '%s', but variable '%s' has type '%s'.",
                elementTypeToString(*exprType), 
                ctx->lastScannedVariable,
                p->variablename_,
                elementTypeToString(*nodeType));

            addError(
                TypeMismatch,
                "Type mismatch in arithmetic expression",
                p->variablename_,
                "Variable type does not match the expected constant type."
            );
            return;
        }
    } else if (!sameType(*exprType, *nodeType)) {
        string_format("Expected type '%s' (from variable '%s'), but variable '%s' has type '%s'.",
            elementTypeToString(*exprType), 
            ctx->lastScannedVariable,
            p->variablename_,
            elementTypeToString(*nodeType));

        addError(
            TypeMismatch,
            "Type mismatch in arithmetic expression",
            p->variablename_,
            "Variable type does not match the expected expression type."
        );
        return;
    } else {
        ctx->currentDataType = nodeType;
        ctx->lastScannedVariable = p->variablename_;
    }
}

void TypeChecker::visitDoubleExpr(DoubleExpr *p) {
    auto exprType = ctx->currentDataType;

    if (ctx->currentDataType == nullptr) {
        ctx->currentDataType = new FloatConstant();
        ctx->lastScannedVariable = p->sdouble_;
    } else if (!isFloat(*exprType)) {
        string_format("Expected type '%s' (from '%s'), but found a floating-point constant '%s'.",
            elementTypeToString(*exprType),
            ctx->lastScannedVariable, 
            p->sdouble_);

        addError(
            TypeMismatch,
            "Type mismatch in arithmetic expression",
            p->sdouble_,
            "Expected a floating-point type for the constant expression."
        );
        return;
    }
}

void TypeChecker::visitSIntExpr(SIntExpr *p) {
    auto exprType = ctx->currentDataType;

    if (ctx->currentDataType == nullptr) {
        ctx->currentDataType = new NegativeIntConstant();
        ctx->lastScannedVariable = p->sint_;
    } else if (!isSignedInteger(*exprType)) {
        string_format("Expected type '%s' (from '%s'), but found a negative integer constant '%s'.",
            elementTypeToString(*exprType),
            ctx->lastScannedVariable, 
            p->sint_);

        addError(
            TypeMismatch,
            "Type mismatch in arithmetic expression",
            p->sint_,
            "Expected a signed integer type for the constant expression."
        );
    }
    return;
}

void TypeChecker::visitIntExpr(IntExpr *p) {
    auto exprType = ctx->currentDataType;
    auto nodeType = new PositiveIntConstant();

    if (ctx->currentDataType == nullptr) {
        ctx->currentDataType = nodeType;
        ctx->lastScannedVariable = p->int_;
    } else if (!isInteger(*exprType)) {
        string_format("Expected type '%s' (from '%s'), but found an integer constant '%s'.",
            elementTypeToString(*exprType),
            ctx->lastScannedVariable, 
            p->int_);

        addError(
            TypeMismatch,
            "Type mismatch in arithmetic expression",
            p->int_,
            "Expected an integer type for the constant expression."
        );
        return;
    }
}

void TypeChecker::visitNegate(Negate *p) {
    p->arithexpr_->accept(this);
}

void TypeChecker::visitPlus(Plus *p) {
    visitListArithExpr(p->listarithexpr_);
}

void TypeChecker::visitMinus(Minus *p) {
    p->arithexpr_->accept(this);
    visitListArithExpr(p->listarithexpr_);
}

void TypeChecker::visitMultiply(Multiply *p) {
    visitListArithExpr(p->listarithexpr_);
}

void TypeChecker::visitListArithExpr(ListArithExpr *p) {
    for (auto &arithExpr : *p) {
        arithExpr->accept(this);
    }
}

void TypeChecker::visitBoolExpr(BoolExpr *p) {} // abstract class

void TypeChecker::visitGreaterThan(GreaterThan *p) {
    ctx->currentDataType = nullptr;
    p->arithexpr_1->accept(this);
    p->arithexpr_2->accept(this);
}

void TypeChecker::visitLessThan(LessThan *p) {
    ctx->currentDataType = nullptr;
    p->arithexpr_1->accept(this);
    p->arithexpr_2->accept(this);
}

void TypeChecker::visitGreaterEqual(GreaterEqual *p) {
    ctx->currentDataType = nullptr;
    p->arithexpr_1->accept(this);
    p->arithexpr_2->accept(this);
}

void TypeChecker::visitLessEqual(LessEqual *p) {
    ctx->currentDataType = nullptr;
    p->arithexpr_1->accept(this);
    p->arithexpr_2->accept(this);
}

void TypeChecker::visitNotEqual(NotEqual *p) {
    ctx->currentDataType = nullptr;
    p->arithexpr_1->accept(this);
    p->arithexpr_2->accept(this);
}

void TypeChecker::visitEqual(Equal *p) {
    ctx->currentDataType = nullptr;
    p->arithexpr_1->accept(this);
    p->arithexpr_2->accept(this);
}

void TypeChecker::visitAnd(And *p) {
    visitListBoolExpr(p->listboolexpr_);
}

void TypeChecker::visitOr(Or *p) {
    visitListBoolExpr(p->listboolexpr_);
}

void TypeChecker::visitListBoolExpr(ListBoolExpr *p) {
    for (auto &boolExpr : *p) {
        boolExpr->accept(this);
    }
}

void TypeChecker::visitAssertion(Assertion *p) {} // abstract class

void TypeChecker::visitAssert(Assert *p) {
    p->boolexpr_->accept(this);
}

// Variable types
void TypeChecker::visitListAssertion(ListAssertion *p) {
    for (auto &assertion : *p) {
        assertion->accept(this);
    }
}
void TypeChecker::visitElementType(ElementType *p) {}
void TypeChecker::visitGenericElementType(GenericElementType *p) {}
void TypeChecker::visitElementTypeF16(ElementTypeF16 *p) {}
void TypeChecker::visitElementTypeF32(ElementTypeF32 *p) {}
void TypeChecker::visitElementTypeF64(ElementTypeF64 *p) {}
void TypeChecker::visitElementTypeBF16(ElementTypeBF16 *p) {}
void TypeChecker::visitElementTypeF8E4M3FN(ElementTypeF8E4M3FN *p) {}
void TypeChecker::visitElementTypeF8E5M2(ElementTypeF8E5M2 *p) {}
void TypeChecker::visitElementTypeF8E4M3FNUZ(ElementTypeF8E4M3FNUZ *p) {}
void TypeChecker::visitElementTypeF8E5M2FNUZ(ElementTypeF8E5M2FNUZ *p) {}
void TypeChecker::visitElementTypeF4E2M1(ElementTypeF4E2M1 *p) {}
void TypeChecker::visitElementTypeI8(ElementTypeI8 *p) {}
void TypeChecker::visitElementTypeI16(ElementTypeI16 *p) {}
void TypeChecker::visitElementTypeI32(ElementTypeI32 *p) {}
void TypeChecker::visitElementTypeI64(ElementTypeI64 *p) {}
void TypeChecker::visitElementTypeU8(ElementTypeU8 *p) {}
void TypeChecker::visitElementTypeU16(ElementTypeU16 *p) {}
void TypeChecker::visitElementTypeU32(ElementTypeU32 *p) {}
void TypeChecker::visitElementTypeU64(ElementTypeU64 *p) {}
void TypeChecker::visitElementTypeC64(ElementTypeC64 *p) {} 
void TypeChecker::visitElementTypeC128(ElementTypeC128 *p) {} 
void TypeChecker::visitElementTypeBool(ElementTypeBool *p) {}
void TypeChecker::visitElementTypeString(ElementTypeString *p) {}

void TypeChecker::visitInputDefinition(InputDefinition *p) {} // abstract class

void TypeChecker::visitInputDef(InputDef *p) {
    visitVariableName(p->variablename_);
    p->elementtype_->accept(this);
    p->tensorshape_->accept(this);

    auto* shape = dynamic_cast<TensorDims*>(p->tensorshape_);
    ListInt dims = (shape && shape->listint_) ? *shape->listint_ : ListInt{};

    ctx->addSymbol(
        p->variablename_,
        p->elementtype_,
        dims,
        SymbolKind::SYM_INPUT
    );
}

void TypeChecker::visitInputOnnxDef(InputOnnxDef *p) {
    visitVariableName(p->variablename_);
    p->elementtype_->accept(this);
    p->tensorshape_->accept(this);

    std::string onnxName = p->string_;
    auto* shape = dynamic_cast<TensorDims*>(p->tensorshape_);
    ListInt dims = (shape && shape->listint_) ? *shape->listint_ : ListInt{};

    ctx->addSymbol(
        p->variablename_,
        p->elementtype_,
        dims,
        SymbolKind::SYM_INPUT,
        onnxName);
}

void TypeChecker::visitHiddenDefinition(HiddenDefinition *p) {} // abstract class

void TypeChecker::visitHiddenDef(HiddenDef *p) {
    visitVariableName(p->variablename_);
    p->elementtype_->accept(this);
    p->tensorshape_->accept(this);

    std::string onnxName = p->string_;
    auto* shape = dynamic_cast<TensorDims*>(p->tensorshape_);
    ListInt dims = (shape && shape->listint_) ? *shape->listint_ : ListInt{};

    ctx->addSymbol(
        p->variablename_,
        p->elementtype_,
        dims,
        SymbolKind::SYM_HIDDEN,
        onnxName
    );
}

void TypeChecker::visitOutputDefinition(OutputDefinition *p) {} //abstract class

void TypeChecker::visitOutputDef(OutputDef *p) {
    visitVariableName(p->variablename_);
    p->elementtype_->accept(this);
    p->tensorshape_->accept(this);

    auto* shape = dynamic_cast<TensorDims*>(p->tensorshape_);
    ListInt dims = (shape && shape->listint_) ? *shape->listint_ : ListInt{};

    ctx->addSymbol(
        p->variablename_,
        p->elementtype_,
        dims,
        SymbolKind::SYM_OUTPUT
    );
}

void TypeChecker::visitOutputOnnxDef(OutputOnnxDef *p) {
    visitVariableName(p->variablename_);
    p->elementtype_->accept(this);
    p->tensorshape_->accept(this);

    std::string onnxName = p->string_;
    auto* shape = dynamic_cast<TensorDims*>(p->tensorshape_);
    ListInt dims = (shape && shape->listint_) ? *shape->listint_ : ListInt{};

    ctx->addSymbol(
        p->variablename_,
        p->elementtype_,
        dims,
        SymbolKind::SYM_OUTPUT,
        onnxName);
}

void TypeChecker::visitListInputDefinition(ListInputDefinition *listinputdefinition)
{
    for (auto &inputDef : *listinputdefinition) {
        inputDef->accept(this);
        switch (ctx->usesOnnxNames) {
            case OnnxNamesUsage::Unknown:
                if (dynamic_cast<InputOnnxDef*>(inputDef)) {
                    ctx->usesOnnxNames = OnnxNamesUsage::OnnxNamesUsed;
                } else {
                    ctx->usesOnnxNames = OnnxNamesUsage::OnnxNamesNotUsed;
                }
                break;
            case OnnxNamesUsage::OnnxNamesNotUsed:
                if (auto p = dynamic_cast<InputOnnxDef*>(inputDef)) {
                    addError(
                        UnexpectedOnnxName,
                        "Expected ordered input variables but got an ONNX-named input variable.",
                        p->variablename_,
                        "ONNX names are used in this context, but this input definition does not specify one."
                    );
                }
                break;
            case OnnxNamesUsage::OnnxNamesUsed:
                if (auto p = dynamic_cast<InputDef*>(inputDef)) {
                    addError(
                        UnexpectedOnnxName,
                        "Expected ONNX-named input variable but got an ordered input variable",
                        p->variablename_,
                        "All (input/output) variables for a network must have an ONNX name OR no (input/output) variables may have an ONNX name."
                    );
                }
        }
    }
}

void TypeChecker::visitListHiddenDefinition(ListHiddenDefinition *listhiddendefinition)
{
    for (auto &hiddenDef : *listhiddendefinition) {
        hiddenDef->accept(this);
    }
}

void TypeChecker::visitListOutputDefinition(ListOutputDefinition *listoutputdefinition)
{
    for (auto &outputDef : *listoutputdefinition) {
        outputDef->accept(this);
        switch (ctx->usesOnnxNames) {
            case OnnxNamesUsage::Unknown:
                if (dynamic_cast<OutputOnnxDef*>(outputDef)) {
                    ctx->usesOnnxNames = OnnxNamesUsage::OnnxNamesUsed;
                } else {
                    ctx->usesOnnxNames = OnnxNamesUsage::OnnxNamesNotUsed;
                }
                break;
            case OnnxNamesUsage::OnnxNamesNotUsed:
                if (auto p = dynamic_cast<OutputOnnxDef*>(outputDef)) {
                    addError(
                        UnexpectedOnnxName,
                        "Expected ordered output variables but got an ONNX-named output variable.",
                        p->variablename_,
                        "ONNX names are used in this context, but this output definition does not specify one."
                    );
                }
                break;
            case OnnxNamesUsage::OnnxNamesUsed:
                if (auto p = dynamic_cast<OutputDef*>(outputDef)) {
                    addError(
                        UnexpectedOnnxName,
                        "Expected ONNX-named output variable but got an ordered output variable",
                        p->variablename_,
                        "All (input/output) variables for a network must have an ONNX name OR no (input/output) variables may have an ONNX name."
                    );
                }
        }
    }
}

void TypeChecker::visitNetworkDefinition(NetworkDefinition *p) {} // abstract base class

void TypeChecker::visitNetworkDef(NetworkDef *p) {
    ctx->usesOnnxNames = OnnxNamesUsage::Unknown;
    visitVariableName(p->variablename_);
    visitListInputDefinition(p->listinputdefinition_);
    visitListHiddenDefinition(p->listhiddendefinition_);
    visitListOutputDefinition(p->listoutputdefinition_);
}

void TypeChecker::visitListNetworkDefinition(ListNetworkDefinition *listnetworkdefinition)
{
    for (auto &networkDef : *listnetworkdefinition) {
        networkDef->accept(this);
    }
}

void TypeChecker::visitQuery(Query *p) {} // abstract base class

void TypeChecker::visitVNNLibQuery(VNNLibQuery *p) {
    if (p->listnetworkdefinition_) {
        p->listnetworkdefinition_->accept(this);
    }
    if (p->listassertion_) {
        p->listassertion_->accept(this);
    }
}

std::string make_element(std::string_view name, const std::vector<int>& indices) {
    std::string out;
    out.reserve(name.size() + 2 + indices.size() * 12);
    out.append(name);
    out.push_back('[');

    bool first = true;
    for (int idx : indices) {
        if (!first) out.push_back(',');
        first = false;

        char buf[24];
        auto [p, ec] = std::to_chars(std::begin(buf), std::end(buf), idx);
        out.append(buf, p);
    }

    out.push_back(']');
    return out;
}

// Utility function to apply scope checking to tensor elements
void TypeChecker::visitTensorElement(VariableName *name, std::vector<int> indices) {
    const SymbolInfo *symbol = ctx->getSymbol(*name);

    std::string element_str = *name + "[";
    for (const auto &index : indices) {
        element_str += std::to_string(index) + ",";
    }
    element_str.pop_back();  // Remove the trailing comma
    element_str += "]";

    if (symbol->shape.size() == 0) {
        // For scalars (empty shape), allow access with index [0] only
        if (indices.size() == 1 && indices[0] == 0) {
            return; // Valid scalar access
        } else if (indices.size() > 1) {
            addError(
                TooManyIndices,
                "Too many indices for scalar variable",
                *name,
                "Scalar variables can only be accessed with a single index [0]."
            );
            return;
        } else if (indices.size() == 1 && indices[0] != 0) {
            addError(
                IndexOutOfBounds,
                "Index out of bounds for scalar variable",
                *name,
                "Scalar variables can only be accessed with index [0]."
            );
            return;
        }
    }

    for (size_t i = 0; i < indices.size(); ++i) {
        if (i >= symbol->shape.size()) {
            addError(
                TooManyIndices,
                "Too many indices for variable",
                *name,
                string_format("Expected %zu indices but encountered %zu.", 
                    symbol->shape.size(), indices.size())
            );
            return;
        }
        if (indices[i] < 0 || indices[i] >= symbol->shape[i]) {
            addError(
                IndexOutOfBounds,
                "Index out of bounds for variable",
                *name,
                string_format("Index %d is out of bounds for dimension %zu with size %d.",
                              indices[i], i, symbol->shape[i])
            );
            return;
        }
    }

    if (indices.size() < symbol->shape.size()) {
        addError(
            NotEnoughIndices,
            "Not enough indices for variable",
            *name,
            string_format("Expected %zu indices but encountered %zu.", symbol->shape.size(), indices.size())
        );
        return;
    }
}

// Basic type visitors (required by Visitor interface)
void TypeChecker::visitInteger(Integer x) {
    // No-op for basic integer values
}

void TypeChecker::visitChar(Char x) {
    // No-op for basic char values
}

void TypeChecker::visitDouble(Double x) {
    // No-op for basic double values
}

void TypeChecker::visitString(String x) {
    // No-op for basic string values
}

void TypeChecker::visitIdent(Ident x) {
    // No-op for basic identifier values
}

void TypeChecker::visitSDouble(SDouble x) {
    // No-op for basic SDouble values
}

void TypeChecker::visitSInt(SInt x) {
    // No-op for basic SInt values
}

void TypeChecker::visitInt(Int x) {
    // No-op for basic Int values
}

void TypeChecker::visitVariableName(VariableName x) {
    // No-op for basic VariableName values
}