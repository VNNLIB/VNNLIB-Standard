#include "TypeChecker.h"

// --- Utility methods ---

// Map ElementType to DType
DType TypeChecker::mapDType(ElementType* e) {
    if (!e) return DType::Unknown;
    #define MAP(E,T) if (dynamic_cast<const E*>(e)) return DType::T
    MAP(GenericElementType, Real); 
    MAP(ElementTypeF16, F16); 
    MAP(ElementTypeF32, F32); 
    MAP(ElementTypeF64, F64);
    MAP(ElementTypeBF16, BF16);
    MAP(ElementTypeF8E4M3FN, F8E4M3FN); 
    MAP(ElementTypeF8E5M2, F8E5M2);
    MAP(ElementTypeF8E4M3FNUZ, F8E4M3FNUZ); 
    MAP(ElementTypeF8E5M2FNUZ, F8E5M2FNUZ);
    MAP(ElementTypeF4E2M1, F4E2M1);
    MAP(ElementTypeI8, I8); 
    MAP(ElementTypeI16, I16); 
    MAP(ElementTypeI32, I32); 
    MAP(ElementTypeI64, I64);
    MAP(ElementTypeU8, U8); 
    MAP(ElementTypeU16, U16); 
    MAP(ElementTypeU32, U32); 
    MAP(ElementTypeU64, U64);
    MAP(ElementTypeC64, C64); 
    MAP(ElementTypeC128, C128);
    MAP(ElementTypeBool, Bool); 
    MAP(ElementTypeString, String);
    #undef MAP
    return DType::Unknown;
}

// Map TensorShape to Indices
Shape TypeChecker::mapShape(TensorShape* shape) {
    Shape out;
    if (!shape || dynamic_cast<ScalarDims*>(shape)) return out; // scalar
    if (auto tensorShape = dynamic_cast<TensorDims*>(shape)) {
        if (tensorShape->listnumber_) {
            out.reserve(tensorShape->listnumber_->size());
            for (auto& dim : *tensorShape->listnumber_) {
                try { 
                    out.push_back(std::stoll(dim->string_)); 
                } catch (const std::exception& e) { 
                    out.push_back(-1); 
                }
            }
        }
    }
    return out;
}

// Map ListInt to Indices
Indices TypeChecker::mapIndices(const ListNumber* inds) {
    Indices out;
    if (!inds) return out;
    out.reserve(inds->size());
    for (const auto& indTok : *inds) {
        try { 
            out.push_back(std::stoll(indTok->string_)); 
        } catch (const std::invalid_argument& e) { 
            out.push_back(-1); 
        }
    }
    return out;
}

// Utility function for string formatting (@iFreilicht)
template<typename ... Args>
static std::string string_format( const std::string& format, Args ... args )
{
    int size_s = std::snprintf( nullptr, 0, format.c_str(), args ... ) + 1; // Extra space for '\0'
    if( size_s <= 0 ){ throw std::runtime_error( "Error during formatting." ); }
    auto size = static_cast<size_t>( size_s );
    std::unique_ptr<char[]> buf( new char[ size ] );
    std::snprintf( buf.get(), size, format.c_str(), args ... );
    return std::string( buf.get(), buf.get() + size - 1 ); // We don't want the '\0' inside
}

// --- Context methods ---

Context::Context(TypeChecker* typeChecker) :
    currentDataType(DType::Unknown),
    lastScannedVariable(""),
    usesOnnxNames(OnnxNamesUsage::Unknown),
    symbolMap(),
    checker(typeChecker) {}

// Add a symbol to the context. Returns true if successful, false if a symbol with the same name already exists, or if the symbol is invalid.
bool Context::addSymbol(VariableName *name, ElementType *type, ListNumber shape, SymbolKind kind, std::string onnxName) {
    if (symbolMap.find(name->string_) != symbolMap.end()) {
        checker->addDiagnostic(Severity::Error, 
                    static_cast<int>(ErrorCode::MultipleDeclaration), 
                    "Duplicate variable declaration", 
                    name->string_,
                    "Variable names must be unique within the specification");
        return false;
    }

    Indices tmp;
    for (const auto& dim : shape) {
        int64_t dim_val;
        try {
            dim_val = std::stoll(dim->string_); // If conversion fails, user has passed a non-int to shape
        } catch (const std::exception& e) {
            checker->addDiagnostic(Severity::Error, 
                static_cast<int>(ErrorCode::InvalidDimensions), 
                "Failed to parse dimension", 
                name->string_,
                "Failed to parse dimension size");
            dim_val = -1;
        }
        if (dim_val < 1) {
            checker->addDiagnostic(Severity::Error, 
                static_cast<int>(ErrorCode::InvalidDimensions), 
                "Failed to parse dimension", 
                name->string_,
                "Dimension sizes must be positive integers.");
            return false;
        }
        tmp.push_back(dim_val);
    }

    symbolMap.try_emplace(
        name->string_,
        name->string_,
        TypeChecker::mapDType(type),
        std::move(tmp),
        kind,
        onnxName
    );
    return true;
}

// Get a symbol from the context by name. Returns a pointer to the symbol if found, or nullptr if not.
SymbolInfo *Context::getSymbol(const VariableName &name) {
    auto it = symbolMap.find(name.string_);
    if (it != symbolMap.end()) {
        return &it->second;
    }
    return nullptr; // Symbol not found
}

TypeChecker::TypeChecker() {
    ctx = std::make_unique<Context>(this);
}

TypeChecker::~TypeChecker() = default;

// --- Error collection and reporting methods ---

// Convert error code to string representation
std::string Diagnostic::codeToString() const {
    if (severity_ == Severity::Error) {
        auto ec = static_cast<ErrorCode>(code_);
        switch (ec) {
            case ErrorCode::MultipleDeclaration: return "MultipleDeclaration";
            case ErrorCode::TypeMismatch: return "TypeMismatch";
            case ErrorCode::UndeclaredVariable: return "UndeclaredVariable";
            case ErrorCode::IndexOutOfBounds: return "IndexOutOfBounds";
            case ErrorCode::TooManyIndices: return "TooManyIndices";
            case ErrorCode::NotEnoughIndices: return "NotEnoughIndices";
            case ErrorCode::UnexpectedOnnxName: return "UnexpectedOnnxName";
            case ErrorCode::InvalidDimensions: return "InvalidDimensions";
            case ErrorCode::MissingNetwork: return "MissingNetwork";
            default: break;
        }
    } else if (severity_ == Severity::Warning) {
        auto wc = static_cast<WarningCode>(code_);
        switch (wc) {
            case WarningCode::MinorVersionMismatch: return "MinorVersionMismatch";
            default: break;
        }
    }
    return "UnknownCode";
}

// Create a JSON representation of a type-check error
std::string Diagnostic::toJson() const {
    nlohmann::json j;
    j["errorCode"] = codeToString();  // Use string representation instead of int
    j["message"] = message_;
    j["offendingSymbol"] = offending_symbol_;
    j["hint"] = hint_;
    return j.dump();
}

// Add a diagnostic to the collection
void TypeChecker::addDiagnostic(Severity severity, int code, const std::string &message,
                                const std::string &offending_symbol,
                                const std::string &hint) {
    if (severity == Severity::Error) {
        errors.emplace_back(severity, code, message, offending_symbol, hint);
    } else if (severity == Severity::Warning) {
        warnings.emplace_back(severity, code, message, offending_symbol, hint);
    }
}

int TypeChecker::getErrorCount() const {
    return static_cast<int>(errors.size());
}

int TypeChecker::getWarningCount() const {
    return static_cast<int>(warnings.size());
}

// Get a JSON representation of all the errors collected
std::string TypeChecker::getErrorReport() const {
    nlohmann::json report;
    if (errors.size() > 0) {
        report["status"] = "failure";
    } else {
        report["status"] = "success";
    }
    report["error_count"] = errors.size();
    report["errors"] = nlohmann::json::array();
    
    for (const auto& error : errors) {
        nlohmann::json errorJson = nlohmann::json::parse(error.toJson());
        report["errors"].push_back(errorJson);
    }

    report["warning_count"] = warnings.size();
    report["warnings"] = nlohmann::json::array();

    for (const auto& warning : warnings) {
        nlohmann::json warningJson = nlohmann::json::parse(warning.toJson());
        report["warnings"].push_back(warningJson);
    }

    return report.dump(2);
}

// --- Visitor Methods --- 

void TypeChecker::visitTensorShape(TensorShape *p) {}       // Abstract class
void TypeChecker::visitScalarDims(ScalarDims *p) {}

void TypeChecker::visitTensorDims(TensorDims *p) {
    visitListNumber(p->listnumber_);
}

void TypeChecker::visitArithExpr(ArithExpr *p) {} // abstract class

void TypeChecker::visitVarExpr(VarExpr *p) {
    const SymbolInfo *symbol = ctx->getSymbol(*p->variablename_);
    if (!symbol) {
        addDiagnostic(
            Severity::Error,
            static_cast<int>(ErrorCode::UndeclaredVariable),
            "Undeclared variable",
            p->variablename_->string_,
            "Variable must be declared before use."
        );
        return;
    }
    // Check for valid tensor access
    visitTensorElement(p->variablename_, TypeChecker::mapIndices(p->listnumber_));
    // Check for valid variable name
    p->variablename_->accept(this);

    DType nodeType = symbol->dtype;
    DType exprType = ctx->currentDataType;

    if (exprType == DType::Unknown) {
        ctx->currentDataType = nodeType;
        ctx->lastScannedVariable = p->variablename_->string_;
    }
    // if exprType is a constant type, check if nodeType is of the same family. E.g., Float and Float
    else if (isConstant(exprType)) {
        if (sameFamily(nodeType, exprType)) {
            ctx->currentDataType = nodeType;
            ctx->lastScannedVariable = p->variablename_->string_;
        } else {
            addDiagnostic(
                Severity::Error,
                static_cast<int>(ErrorCode::TypeMismatch),
                "Type mismatch in arithmetic expression",
                p->variablename_->string_,
                string_format(
                    "Expected a %s type to match constant '%s', but variable '%s' has type '%s'.",
                    dtypeToString(exprType).c_str(),
                    ctx->lastScannedVariable.c_str(),
                    p->variablename_->string_.c_str(),
                    dtypeToString(nodeType).c_str()
                )
            );
        }
    }
    // if exprType is a variable type, check if nodeType is of the same type
    else if (!sameType(exprType, nodeType)) {
        addDiagnostic(
            Severity::Error,
            static_cast<int>(ErrorCode::TypeMismatch),
            "Type mismatch in arithmetic expression",
            p->variablename_->string_,
            string_format(
                "Expected type '%s' (from variable '%s'), but variable '%s' has type '%s'.",
                dtypeToString(exprType).c_str(), 
                ctx->lastScannedVariable.c_str(),
                p->variablename_->string_.c_str(),
                dtypeToString(nodeType).c_str()
            )
        );
    }
    else {
        ctx->currentDataType = nodeType;
        ctx->lastScannedVariable = p->variablename_->string_;
    }
}

void TypeChecker::visitValExpr(ValExpr *p) {
    // If currentDataType is unset, assign a new FloatConstant
    std::string valTok = p->number_->string_;
    DType newType = DType::Unknown;

    if (valTok.find('.') != std::string::npos) {
        newType = DType::FloatConstant;
    } else {
        if (valTok.find('-') != std::string::npos) {
            newType = DType::NegativeIntConstant;
        } else {
            newType = DType::PositiveIntConstant;
        }
    }

    if (ctx->currentDataType == DType::Unknown) {
        ctx->currentDataType = newType;
        ctx->lastScannedVariable = valTok;
    // if the currentDataType is incompatible with the constant type, add error
    } else if (!sameFamily(ctx->currentDataType, newType)) {
        addDiagnostic(
            Severity::Error,
            static_cast<int>(ErrorCode::TypeMismatch),
            "Type mismatch in arithmetic expression",
            valTok,
            string_format(
                "Expected type '%s' (from '%s'), but found a %s constant '%s'.",
                dtypeToString(ctx->currentDataType).c_str(),
                ctx->lastScannedVariable.c_str(), 
                dtypeToString(newType).c_str(),
                valTok.c_str()
            )
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
    ctx->currentDataType = DType::Unknown;
    p->arithexpr_1->accept(this);
    p->arithexpr_2->accept(this);
}

void TypeChecker::visitLessThan(LessThan *p) {
    ctx->currentDataType = DType::Unknown;
    p->arithexpr_1->accept(this);
    p->arithexpr_2->accept(this);
}

void TypeChecker::visitGreaterEqual(GreaterEqual *p) {
    ctx->currentDataType = DType::Unknown;
    p->arithexpr_1->accept(this);
    p->arithexpr_2->accept(this);
}

void TypeChecker::visitLessEqual(LessEqual *p) {
    ctx->currentDataType = DType::Unknown;
    p->arithexpr_1->accept(this);
    p->arithexpr_2->accept(this);
}

void TypeChecker::visitNotEqual(NotEqual *p) {
    ctx->currentDataType = DType::Unknown;
    p->arithexpr_1->accept(this);
    p->arithexpr_2->accept(this);
}

void TypeChecker::visitEqual(Equal *p) {
    ctx->currentDataType = DType::Unknown;
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

void TypeChecker::visitListAssertion(ListAssertion *p) {
    for (auto &assertion : *p) {
        assertion->accept(this);
    }
}

// Data Type leaf node visitors
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
    // Set dims to an empty list if shape is null or shape->listnumber_ is null
    ListNumber dims = (shape && shape->listnumber_) ? *shape->listnumber_ : ListNumber{};

    ctx->addSymbol(
        p->variablename_,
        p->elementtype_,
        dims,
        SymbolKind::Input
    );
}

void TypeChecker::visitInputOnnxDef(InputOnnxDef *p) {
    visitVariableName(p->variablename_);
    p->elementtype_->accept(this);
    p->tensorshape_->accept(this);

    std::string onnxName = p->string_;
    auto* shape = dynamic_cast<TensorDims*>(p->tensorshape_);
    ListNumber dims = (shape && shape->listnumber_) ? *shape->listnumber_ : ListNumber{};

    ctx->addSymbol(
        p->variablename_,
        p->elementtype_,
        dims,
        SymbolKind::Input,
        onnxName);
}

void TypeChecker::visitHiddenDefinition(HiddenDefinition *p) {} // abstract class

void TypeChecker::visitHiddenDef(HiddenDef *p) {
    visitVariableName(p->variablename_);
    p->elementtype_->accept(this);
    p->tensorshape_->accept(this);

    std::string onnxName = p->string_;  // Hidden nodes have a mandatory ONNX name
    auto* shape = dynamic_cast<TensorDims*>(p->tensorshape_);
    ListNumber dims = (shape && shape->listnumber_) ? *shape->listnumber_ : ListNumber{};

    ctx->addSymbol(
        p->variablename_,
        p->elementtype_,
        dims,
        SymbolKind::Hidden,
        onnxName
    );
}

void TypeChecker::visitOutputDefinition(OutputDefinition *p) {} //abstract class

void TypeChecker::visitOutputDef(OutputDef *p) {
    visitVariableName(p->variablename_);
    p->elementtype_->accept(this);
    p->tensorshape_->accept(this);

    auto* shape = dynamic_cast<TensorDims*>(p->tensorshape_);
    ListNumber dims = (shape && shape->listnumber_) ? *shape->listnumber_ : ListNumber{};

    ctx->addSymbol(
        p->variablename_,
        p->elementtype_,
        dims,
        SymbolKind::Output
    );
}

void TypeChecker::visitOutputOnnxDef(OutputOnnxDef *p) {
    visitVariableName(p->variablename_);
    p->elementtype_->accept(this);
    p->tensorshape_->accept(this);

    std::string onnxName = p->string_;
    auto* shape = dynamic_cast<TensorDims*>(p->tensorshape_);
    ListNumber dims = (shape && shape->listnumber_) ? *shape->listnumber_ : ListNumber{};

    ctx->addSymbol(
        p->variablename_,
        p->elementtype_,
        dims,
        SymbolKind::Output,
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
                // Check if inputDef is an ONNX-named input variable
                if (auto p = dynamic_cast<InputOnnxDef*>(inputDef)) {
                    addDiagnostic(
                        Severity::Error,
                        static_cast<int>(ErrorCode::UnexpectedOnnxName),
                        "Expected ordered input variables but got an ONNX-named input variable.",
                        p->variablename_->string_,
                        "ONNX names are used in this context, but this input definition does not specify one."
                    );
                }
                break;
            case OnnxNamesUsage::OnnxNamesUsed:
                // Check if inputDef is an ordered input variable
                if (auto p = dynamic_cast<InputDef*>(inputDef)) {
                    addDiagnostic(
                        Severity::Error,
                        static_cast<int>(ErrorCode::UnexpectedOnnxName),
                        "Expected ONNX-named input variable but got an ordered input variable",
                        p->variablename_->string_,
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
                // Check if outputDef is an ONNX-named output variable
                if (auto p = dynamic_cast<OutputOnnxDef*>(outputDef)) {
                    addDiagnostic(
                        Severity::Error,
                        static_cast<int>(ErrorCode::UnexpectedOnnxName),
                        "Expected ordered output variables but got an ONNX-named output variable.",
                        p->variablename_->string_,
                        "ONNX names are used in this context, but this output definition does not specify one."
                    );
                }
                break;
            case OnnxNamesUsage::OnnxNamesUsed:
                // Check if outputDef is an ordered output variable
                if (auto p = dynamic_cast<OutputDef*>(outputDef)) {
                    addDiagnostic(
                        Severity::Error,
                        static_cast<int>(ErrorCode::UnexpectedOnnxName),
                        "Expected ONNX-named output variable but got an ordered output variable",
                        p->variablename_->string_,
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

void TypeChecker::visitVersion(Version *p) {} // abstract base class

void TypeChecker::visitVNNLibVersion(VNNLibVersion *p) {
    std::string ver = p->versiontoken_->string_;
    int major = 0, minor = 0;
    std::sscanf(ver.c_str(), "<%d.%d>", &major, &minor);

    if (major != VNNLIB_MAJOR_VERSION) {
        addDiagnostic(
            Severity::Error,
            static_cast<int>(ErrorCode::MajorVersionMismatch),
            "Incompatible VNNLib version",
            ver,
            string_format("Expected VNNLib version <%d.x>, but found version <%d.%d>.", VNNLIB_MAJOR_VERSION, major, minor)
        );
    }

    if (minor != VNNLIB_MINOR_VERSION) {
        addDiagnostic(
            Severity::Warning,
            static_cast<int>(WarningCode::MinorVersionMismatch),
            "Minor version mismatch",
            ver,
            string_format("Expected VNNLib version <%d.%d>, but found version <%d.%d>.", VNNLIB_MAJOR_VERSION, VNNLIB_MINOR_VERSION, major, minor)
        );
    }
}

void TypeChecker::visitQuery(Query *p) {} // abstract base class

void TypeChecker::visitVNNLibQuery(VNNLibQuery *p) {
    assert(p->version_); p->version_->accept(this);
    if (p->listnetworkdefinition_) {
        p->listnetworkdefinition_->accept(this);
    } else {
        addDiagnostic(
            Severity::Error,
            static_cast<int>(ErrorCode::MissingNetwork),
            "No network definition found in VNNLib specification",
            "",
            "A VNNLib specification must contain at least one network definition."
        );
    }
    assert(p->listassertion_); p->listassertion_->accept(this);
}

// Helper function to efficiently create strings to represent tensor element access
std::string make_element(std::string_view name, const Indices& indices) {
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

// Checks for valid tensor element access
void TypeChecker::visitTensorElement(VariableName *name, Indices indices) {
    const SymbolInfo *symbol = ctx->getSymbol(*name);
    std::string name_str = name->string_;
    std::string element_str = make_element(name_str, indices);

    if (symbol->shape.size() == 0) {
        // For scalars (empty shape), allow access with index [0] only
        if (indices.size() == 1 && indices[0] == 0) {
            return;  // Correct access
        } else {
            addDiagnostic(
                Severity::Error,
                static_cast<int>(ErrorCode::InvalidScalarAccess),
                "Invalid index for scalar variable",
                element_str,
                "Scalar variables can only be accessed with index [0]."
            );
            return;
        }
    }

    for (size_t i = 0; i < indices.size(); ++i) {
        // Check for too many indices
        if (i >= symbol->shape.size()) {
            addDiagnostic(
                Severity::Error,
                static_cast<int>(ErrorCode::TooManyIndices),
                "Too many indices for variable",
                element_str,
                string_format("Expected %zu indices but encountered %zu.",
                    symbol->shape.size(), indices.size())
            );
            return;
        }
        // Check that the index is within the variable's declared shape
        if (indices[i] >= symbol->shape[i]) {
            addDiagnostic(
                Severity::Error,
                static_cast<int>(ErrorCode::IndexOutOfBounds),
                "Index out of bounds for variable",
                element_str,
                string_format("Index %d is out of bounds for dimension %zu with size %d.",
                              indices[i], i, symbol->shape[i])
            );
            return;
        }
    }

    // Check for not enough indices
    if (indices.size() < symbol->shape.size()) {
        addDiagnostic(
            Severity::Error,
            static_cast<int>(ErrorCode::NotEnoughIndices),
            "Not enough indices for variable",
            element_str,
            string_format("Expected %zu indices but encountered %zu.", symbol->shape.size(), indices.size())
        );
        return;
    }
}

// Visitors for default BNFC tokens
void TypeChecker::visitInteger(Integer x) {}
void TypeChecker::visitChar(Char x) {}
void TypeChecker::visitDouble(Double x) {}
void TypeChecker::visitString(String x) {}
void TypeChecker::visitIdent(Ident x) {}
void TypeChecker::visitVariableName(VariableName *p) {}     // Token for variable names

void TypeChecker::visitListNumber(ListNumber *p) {
    for (const auto &num : *p) {
        num->accept(this);
    }
}

void TypeChecker::visitNumber(Number *p) {}                 // Token for number literals

void TypeChecker::visitVersionToken(VersionToken *x) {}     // Token for version