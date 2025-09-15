#pragma once

#define MAX_DIMENSIONS 10

#include <memory>
#include <unordered_map>
#include <vector>
#include <string>
#include <stdexcept>
#include <iostream>
#include <string_view>
#include <charconv>
#include <set>

#include "Absyn.H"
#include "json.hpp"
#include "TypedAbsyn.h"


class TypeChecker; // Forward declaration


#define VNNLIB_MAJOR_VERSION 2
#define VNNLIB_MINOR_VERSION 0


enum class ErrorCode {
    MultipleDeclaration,
    TypeMismatch,
    UndeclaredVariable,
    IndexOutOfBounds,
    InvalidScalarAccess,
    TooManyIndices,
    NotEnoughIndices,
    UnexpectedOnnxName,
    InvalidDimensions,
    MajorVersionMismatch,
    MissingNetwork,
    VariableCountMismatch,
    VariableShapeMismatch,
    VariableKindMismatch,
    OnnxNameMismatch
};

enum class WarningCode {
    MinorVersionMismatch
};

enum class Severity {
    Error,
    Warning,
    Info
};

// Structure to store diagnostic information that will be reported to the user as errors or warnings
struct Diagnostic {
    Diagnostic(Severity severity, int code, std::string message, std::string offending_symbol, std::string hint, int line)
        : severity_(severity), code_(code), message_(std::move(message)), offending_symbol_(std::move(offending_symbol)), hint_(std::move(hint)), line_(line) {}

    std::string toJson() const;
    std::string codeToString() const;

private:
    Severity severity_;
    int code_;
    std::string message_;
    std::string offending_symbol_;
    std::string hint_;
    int line_;
};

// Status of whether input or output variables in the network are using ONNX names
typedef enum {
    OnnxNamesUsed,
    OnnxNamesNotUsed,
    Unknown
} OnnxNamesUsage; 

// Structure to store network information for validation
struct NetworkInfo {
    std::string name;
    bool usesOnnxNames{false};              // Whether the network uses ONNX names for any input/output
    std::vector<const SymbolInfo*> vars;    // References to input and output variables
    NetworkInfo() = default;
    NetworkInfo(const std::string& networkName) : name(networkName) {}
};

// Context class to manage symbols and current scope
class Context {
public:
    Context(TypeChecker* typeChecker = nullptr);
    bool addSymbol(VariableName *name, ElementType *type, ListNumber shape, SymbolKind kind, std::string onnxName = "");
    SymbolInfo *getSymbol(const VariableName &name);
    
    DType currentDataType;                                      // Data type of the last scanned variable
    std::string lastScannedVariable;                            // Name of the last scanned variable
    OnnxNamesUsage usesOnnxNames;                               // Whether ONNX names are used in the current input/output definitions

private:
    std::unordered_map<std::string, SymbolInfo> symbolMap;      // Map to store symbols
    TypeChecker* checker;                                       // Reference to parent TypeChecker for error reporting
};

// TypeChecker class implementing the Visitor pattern
class TypeChecker : public Visitor {
public:
    TypeChecker();
    ~TypeChecker();

    // --- Visitor methods for concrete nodes ---

    void visitScalarDims(ScalarDims *p) override;
    void visitTensorDims(TensorDims *p) override;

    void visitVarExpr(VarExpr* p) override;
    void visitValExpr(ValExpr* p) override;
    void visitNegate(Negate* p) override;
    void visitPlus(Plus* p) override;
    void visitMinus(Minus* p) override;
    void visitMultiply(Multiply* p) override;

    void visitGreaterThan(GreaterThan* p) override;
    void visitLessThan(LessThan* p) override;
    void visitGreaterEqual(GreaterEqual* p) override;
    void visitLessEqual(LessEqual* p) override;
    void visitNotEqual(NotEqual* p) override;
    void visitEqual(Equal* p) override;
    void visitAnd(And* p) override;
    void visitOr(Or* p) override;

    void visitAssert(Assert* p) override;

    void visitInputDef(InputDef* p) override;
    void visitInputOnnxDef(InputOnnxDef* p) override;
    void visitHiddenDef(HiddenDef* p) override;
    void visitOutputDef(OutputDef* p) override;
    void visitOutputOnnxDef(OutputOnnxDef* p) override;

    void visitIsomorphicTo(IsomorphicTo *p) override;
    void visitEqualTo(EqualTo *p) override;
    void visitNetworkDef(NetworkDef* p) override;
    void visitVNNLibVersion(VNNLibVersion *p) override;
    void visitVNNLibQuery(VNNLibQuery* p) override;

    // --- Visitor methods for abstract classes ---

    void visitTensorShape(TensorShape *p) override;
    void visitArithExpr(ArithExpr *p) override;
    void visitBoolExpr(BoolExpr *p) override;
    void visitAssertion(Assertion *p) override;
    void visitElementType(ElementType *p) override;
    void visitInputDefinition(InputDefinition *p) override;
    void visitHiddenDefinition(HiddenDefinition *p) override;
    void visitOutputDefinition(OutputDefinition *p) override;
    void visitCompStm(CompStm *p) override;
    void visitNetworkDefinition(NetworkDefinition *p) override;
    void visitVersion(Version *p) override;
    void visitQuery(Query *p) override;

    // --- Visitor methods for element types ---

    void visitGenericElementType(GenericElementType *p) override;
    void visitElementTypeF16(ElementTypeF16 *p) override;
    void visitElementTypeF32(ElementTypeF32 *p) override;
    void visitElementTypeF64(ElementTypeF64 *p) override;
    void visitElementTypeBF16(ElementTypeBF16 *p) override;
    void visitElementTypeF8E4M3FN(ElementTypeF8E4M3FN *p) override;
    void visitElementTypeF8E5M2(ElementTypeF8E5M2 *p) override;
    void visitElementTypeF8E4M3FNUZ(ElementTypeF8E4M3FNUZ *p) override;
    void visitElementTypeF8E5M2FNUZ(ElementTypeF8E5M2FNUZ *p) override;
    void visitElementTypeF4E2M1(ElementTypeF4E2M1 *p) override;
    void visitElementTypeI8(ElementTypeI8 *p) override;
    void visitElementTypeI16(ElementTypeI16 *p) override;
    void visitElementTypeI32(ElementTypeI32 *p) override;
    void visitElementTypeI64(ElementTypeI64 *p) override;
    void visitElementTypeU8(ElementTypeU8 *p) override;
    void visitElementTypeU16(ElementTypeU16 *p) override;
    void visitElementTypeU32(ElementTypeU32 *p) override;
    void visitElementTypeU64(ElementTypeU64 *p) override;
    void visitElementTypeC64(ElementTypeC64 *p) override;
    void visitElementTypeC128(ElementTypeC128 *p) override;
    void visitElementTypeBool(ElementTypeBool *p) override;
    void visitElementTypeString(ElementTypeString *p) override;

    // --- Visitor methods for list types ---

    void visitListNumber(ListNumber *p) override;
    void visitListArithExpr(ListArithExpr *p) override;
    void visitListBoolExpr(ListBoolExpr *p) override;
    void visitListAssertion(ListAssertion *p) override;
    void visitListInputDefinition(ListInputDefinition *p) override;
    void visitListHiddenDefinition(ListHiddenDefinition *p) override;
    void visitListOutputDefinition(ListOutputDefinition *p) override;
    void visitListCompStm(ListCompStm *p) override;
    void visitListNetworkDefinition(ListNetworkDefinition *p) override;

    // --- Visitor methods for tokens ---

    void visitInteger(Integer x) override;
    void visitChar(Char x) override;
    void visitDouble(Double x) override;
    void visitString(String x) override;
    void visitIdent(Ident x) override;
    void visitVariableName(VariableName *x) override;
    void visitNumber(Number *x) override;
    void visitVersionToken(VersionToken *x) override;

    // Apply scope checking to tensor elements
    void visitTensorElement(VariableName *name, std::vector<int64_t> indices);

    // Error collection and reporting methods
    void addDiagnostic(Severity severity, int code, const std::string& message,
                       const std::string& offending_symbol = "",
                       const std::string& hint = "",
                       int line = -1);
    int getErrorCount() const;
    int getWarningCount() const;
    std::string getErrorReport() const;
    
    static DType mapDType(ElementType *e);
    static Shape mapShape(TensorShape *s);
    static std::vector<int64_t> mapIndices(const ListNumber *i);

    // Helper methods for network congruence validation
    void validateNetworkCongruence(VariableName* referencedNetworkName, const std::string& statementType);
    void collectNetworkVariables(NetworkInfo& networkInfo, const ListInputDefinition* inputs, const ListOutputDefinition* outputs);
    bool areVariablesCongruent(const NetworkInfo& current, const NetworkInfo& target, int line);
    bool validateSymbolCongruence(const SymbolInfo& a, const SymbolInfo& b, const NetworkInfo& current, const NetworkInfo& target, size_t i, int line);

protected:
    Context& getContext() { return *ctx; }

private:
    std::unique_ptr<Context> ctx;
    std::vector<Diagnostic> errors;
    std::vector<Diagnostic> warnings;
    std::unordered_map<std::string, NetworkInfo> networks;
    std::string currentNetworkName;
};
