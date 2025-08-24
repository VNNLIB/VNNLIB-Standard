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

