#pragma once
#include <memory>
#include <unordered_map>
#include <vector>
#include "TypeChecker.h"  
#include "TypedAbsyn.h" 
#include "Absyn.H"  

class TypedBuilder : public TypeChecker {
public:
    TypedBuilder() = default;

    std::unique_ptr<TQuery> build(VNNLibQuery* root);

    void visitVarExpr(VarExpr* p) override;
    void visitDoubleExpr(DoubleExpr* p) override;
    void visitSIntExpr(SIntExpr* p) override;
    void visitIntExpr(IntExpr* p) override;
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

    void visitNetworkDef(NetworkDef* p) override;
    void visitVNNLibQuery(VNNLibQuery* p) override;

    // Missing abstract visitor methods from base Visitor class
    void visitTensorShape(TensorShape *p) override;
    void visitArithExpr(ArithExpr *p) override;
    void visitBoolExpr(BoolExpr *p) override;
    void visitAssertion(Assertion *p) override;
    void visitElementType(ElementType *p) override;
    void visitInputDefinition(InputDefinition *p) override;
    void visitHiddenDefinition(HiddenDefinition *p) override;
    void visitOutputDefinition(OutputDefinition *p) override;
    void visitNetworkDefinition(NetworkDefinition *p) override;
    void visitQuery(Query *p) override;
    
    void visitScalarDims(ScalarDims *p) override;
    void visitTensorDims(TensorDims *p) override;
    
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
    
    void visitListInt(ListInt *p) override;
    void visitListArithExpr(ListArithExpr *p) override;
    void visitListBoolExpr(ListBoolExpr *p) override;
    void visitListAssertion(ListAssertion *p) override;
    void visitListInputDefinition(ListInputDefinition *p) override;
    void visitListHiddenDefinition(ListHiddenDefinition *p) override;
    void visitListOutputDefinition(ListOutputDefinition *p) override;
    void visitListNetworkDefinition(ListNetworkDefinition *p) override;

    void visitInteger(Integer x) override;
    void visitChar(Char x) override;
    void visitDouble(Double x) override;
    void visitString(String x) override;
    void visitIdent(Ident x) override;
    void visitSDouble(SDouble x) override;
    void visitSInt(SInt x) override;
    void visitInt(Int x) override;
    void visitVariableName(VariableName x) override;

private:
    std::unique_ptr<TQuery> tquery_;
    std::vector<TNetworkDefinition*> netStack_;
    std::vector<std::unique_ptr<TArithExpr>> arithStack_;
    std::vector<std::unique_ptr<TBoolExpr>>  boolStack_;

    std::unordered_map<std::string, std::shared_ptr<const SymbolInfo>> symbolMap_;

    template <class T>
    static std::unique_ptr<T> pop(std::vector<std::unique_ptr<T>>& stack);

    template <class T>
    static std::vector<std::unique_ptr<T>> popRange(std::vector<std::unique_ptr<T>>& stack, size_t lowerBound, size_t upperBound);
};

