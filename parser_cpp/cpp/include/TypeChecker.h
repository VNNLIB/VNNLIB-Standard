#ifndef TYPE_CHECKER_H
#define TYPE_CHECKER_H

#define MAX_DIMENSIONS 10

#include <memory>
#include <unordered_map>
#include <vector>
#include <string>
#include <stdexcept>
#include <iostream>
#include <string_view>
#include <charconv>

#include "Absyn.H"
#include "json.hpp"
#include "TypedAbsyn.h"


typedef enum {
    MultipleDeclaration,
    TypeMismatch,
    UndeclaredVariable,
    IndexOutOfBounds,
    TooManyIndices,
    NotEnoughIndices,
    UnexpectedOnnxName,
    InvalidDimensions,
} ErrorCode;


typedef enum {
    OnnxNamesUsed,
    OnnxNamesNotUsed,
    Unknown
} OnnxNamesUsage;


// Stores information about a type checking error
class TypeCheckError final : public std::runtime_error {
public:
    TypeCheckError(ErrorCode code,
                   std::string message,
                   std::string offending_symbol = {},
                   std::string hint = {});
    
    static std::string codeToString(ErrorCode code);
    
private:
    ErrorCode   code_;
    std::string message_, offending_symbol_, hint_;

    static std::string makeJson(ErrorCode code, 
                                std::string message, 
                                std::string offending_symbol, 
                                std::string hint);
};


class TypeChecker;

class Context {
public:
    Context(TypeChecker* typeChecker = nullptr);
    bool addSymbol(VariableName name, ElementType *type, ListInt shape, SymbolKind kind, std::string onnxName = "");
    SymbolInfo *getSymbol(const VariableName &name);
    
    DType currentDataType;                                      // Data type of the last scanned variable
    VariableName lastScannedVariable;                           // Name of the last scanned variable
    OnnxNamesUsage usesOnnxNames;                               // Whether ONNX names are used in the current input/output definitions

private:
    std::unordered_map<std::string, SymbolInfo> symbolMap;      // Map to store symbols
    TypeChecker* checker;                                       // Reference to parent TypeChecker for error reporting
};


class TypeChecker : public Visitor {
public:
    TypeChecker();
    ~TypeChecker();

    void visitListInt(ListInt *p);
    void visitTensorShape(TensorShape *p); /* abstract class */
    void visitScalarDims(ScalarDims *p);
    void visitTensorDims(TensorDims *p);
    void visitArithExpr(ArithExpr *p); /* abstract class */
    void visitVarExpr(VarExpr *p);
    void visitDoubleExpr(DoubleExpr *p);
    void visitSIntExpr(SIntExpr *p);
    void visitIntExpr(IntExpr *p);
    void visitNegate(Negate *p);
    void visitPlus(Plus *p);
    void visitMinus(Minus *p);
    void visitMultiply(Multiply *p);
    void visitListArithExpr(ListArithExpr *p);
    void visitBoolExpr(BoolExpr *p); /* abstract class */
    void visitGreaterThan(GreaterThan *p);
    void visitLessThan(LessThan *p);
    void visitGreaterEqual(GreaterEqual *p);
    void visitLessEqual(LessEqual *p);
    void visitNotEqual(NotEqual *p);
    void visitEqual(Equal *p);
    void visitAnd(And *p);
    void visitOr(Or *p);
    void visitListBoolExpr(ListBoolExpr *p);
    void visitAssertion(Assertion *p); /* abstract class */
    void visitAssert(Assert *p);
    void visitListAssertion(ListAssertion *p);
    void visitElementType(ElementType *p); /* abstract class */
    void visitGenericElementType(GenericElementType *p);
    void visitElementTypeF16(ElementTypeF16 *p);
    void visitElementTypeF32(ElementTypeF32 *p);
    void visitElementTypeF64(ElementTypeF64 *p);
    void visitElementTypeBF16(ElementTypeBF16 *p);
    void visitElementTypeF8E4M3FN(ElementTypeF8E4M3FN *p);
    void visitElementTypeF8E5M2(ElementTypeF8E5M2 *p);
    void visitElementTypeF8E4M3FNUZ(ElementTypeF8E4M3FNUZ *p);
    void visitElementTypeF8E5M2FNUZ(ElementTypeF8E5M2FNUZ *p);
    void visitElementTypeF4E2M1(ElementTypeF4E2M1 *p);
    void visitElementTypeI8(ElementTypeI8 *p);
    void visitElementTypeI16(ElementTypeI16 *p);
    void visitElementTypeI32(ElementTypeI32 *p);
    void visitElementTypeI64(ElementTypeI64 *p);
    void visitElementTypeU8(ElementTypeU8 *p);
    void visitElementTypeU16(ElementTypeU16 *p);
    void visitElementTypeU32(ElementTypeU32 *p);
    void visitElementTypeU64(ElementTypeU64 *p);
    void visitElementTypeC64(ElementTypeC64 *p);
    void visitElementTypeC128(ElementTypeC128 *p);
    void visitElementTypeBool(ElementTypeBool *p);
    void visitElementTypeString(ElementTypeString *p);
    void visitInputDefinition(InputDefinition *p); /* abstract class */
    void visitInputDef(InputDef *p);
    void visitInputOnnxDef(InputOnnxDef *p);
    void visitHiddenDefinition(HiddenDefinition *p); /* abstract class */
    void visitHiddenDef(HiddenDef *p);
    void visitOutputDefinition(OutputDefinition *p); /* abstract class */
    void visitOutputDef(OutputDef *p);
    void visitOutputOnnxDef(OutputOnnxDef *p);
    void visitListInputDefinition(ListInputDefinition *p);
    void visitListHiddenDefinition(ListHiddenDefinition *p);
    void visitListOutputDefinition(ListOutputDefinition *p);
    void visitNetworkDefinition(NetworkDefinition *p); /* abstract class */
    void visitNetworkDef(NetworkDef *p);
    void visitListNetworkDefinition(ListNetworkDefinition *p);
    void visitQuery(Query *p); /* abstract class */
    void visitVNNLibQuery(VNNLibQuery *p);

    void visitInteger(Integer i);
    void visitDouble(Double d);
    void visitChar(Char c);
    void visitString(String s);
    void visitIdent(String s);
    void visitSDouble(String s);
    void visitSInt(String s);
    void visitInt(String s);
    void visitVariableName(String s);

    // Apply scope checking to tensor elements
    void visitTensorElement(VariableName *name, std::vector<int64_t> indices);

    // Error collection and reporting methods
    void addError(ErrorCode code, const std::string& message, 
                    const std::string& offending_symbol = "", 
                    const std::string& hint = "");
    bool hasErrors() const;
    size_t getErrorCount() const;
    std::string getErrorReport() const;
    void clearErrors();
    
    static DType mapDType(ElementType *e);
    static Shape mapShape(TensorShape *s);
    static std::vector<int64_t> mapIndices(const ListInt *i);

protected:
    Context& getContext() { return *ctx; }

private:
    Context *ctx = nullptr;
    std::vector<TypeCheckError> errors;  // Store collected errors
};

#endif
