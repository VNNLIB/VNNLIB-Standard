#pragma once
#include <cstdint>
#include <memory>
#include <optional>
#include <string>
#include <vector>
#include <variant>

#include "Absyn.H"

enum class DType {
	Real,
	F16, F32, F64, BF16,
	F8E4M3FN, F8E5M2, F8E4M3FNUZ, F8E5M2FNUZ, F4E2M1,
	I8, I16, I32, I64,
	U8, U16, U32, U64,
	C64, C128, Bool, String, Unknown,
	FloatConstant, NegativeIntConstant, PositiveIntConstant
};

std::string dtypeToString(DType dt);
bool isConstant(DType dt);
bool sameFamily(DType varDt, DType constDt);
bool sameType(DType a, DType b);

enum class SymbolKind {Input, Hidden, Output, Network, Unknown};
using Shape = std::vector<int64_t>;
using Indices = std::vector<int64_t>;

class SymbolInfo final {
public:
	std::string name{};
	std::string onnxName{};
	DType dtype{DType::Unknown};
	Shape shape{};
	SymbolKind kind{SymbolKind::Unknown};
	std::string networkName{};

	bool isScalar() const;
	size_t rank() const;

	SymbolInfo(std::string name, DType dtype, Shape shape, SymbolKind kind, std::string onnxName = "")
        : name(name), onnxName(onnxName), dtype(dtype), shape(std::move(shape)), kind(kind) {}

    bool operator==(const SymbolInfo &other) const;
};

class TNode {
public:
	virtual ~TNode() = default;
	virtual void children(std::vector<const TNode*>& out) const = 0;
	virtual std::string toString() const = 0;

protected:
	TNode() = default;                               
	TNode(const TNode&) = delete;
	TNode& operator=(const TNode&) = delete;
	TNode(TNode&&) noexcept = default;            
	TNode& operator=(TNode&&) noexcept = default;
};

class TElementType : public TNode {
friend class TypedBuilder;
public:
	DType dtype{DType::Unknown};
	virtual ~TElementType() = default;
	void children(std::vector<const TNode*>& out) const override;
	std::string toString() const override;
protected:
	ElementType* src_ElementType{nullptr};
};

// --- Arithmetic Expressions ---

class TArithExpr : public TNode {
friend class TypedBuilder;
public:
	DType dtype{DType::Unknown};
	virtual ~TArithExpr() = default;
	std::string toString() const override;
protected:
	ArithExpr* src_ArithExpr{nullptr};
};

class TVarExpr final : public TArithExpr {
public:
	std::shared_ptr<const SymbolInfo> symbol{};
	Indices indices{};
	int line{-1};
	void children(std::vector<const TNode*>& out) const override;
};

class TLiteral : public TArithExpr {
public:
	std::string lexeme;
	int line{-1};
	void children(std::vector<const TNode*>& out) const override;
};

class TFloat final : public TLiteral {
public:
	double value{};
};

class TInt final : public TLiteral {
public:
	int64_t value{};
};

class TNegate final : public TArithExpr {
public:
	std::unique_ptr<TArithExpr> expr;
	void children(std::vector<const TNode*>& out) const override;
};

class TPlus final : public TArithExpr {
public:
	std::vector<std::unique_ptr<TArithExpr>> args;
	void children(std::vector<const TNode*>& out) const override;
};

class TMinus final : public TArithExpr {
public:
	std::unique_ptr<TArithExpr> head;
	std::vector<std::unique_ptr<TArithExpr>> rest;
	void children(std::vector<const TNode*>& out) const override;
};

class TMultiply final : public TArithExpr {
public:
	std::vector<std::unique_ptr<TArithExpr>> args;
	void children(std::vector<const TNode*>& out) const override;
};

// --- Boolean Expressions ---

class TBoolExpr : public TNode {
friend class TypedBuilder;
public:
	virtual ~TBoolExpr() = default;
	std::string toString() const override;
protected:
	BoolExpr* src_BoolExpr{nullptr};
};

class TCompare : public TBoolExpr {
public:
	std::unique_ptr<TArithExpr> lhs, rhs;
	void children(std::vector<const TNode*>& out) const override;
};

class TGreaterThan final : public TCompare {};
class TLessThan final : public TCompare {};
class TGreaterEqual final : public TCompare {};
class TLessEqual final : public TCompare {};
class TEqual final : public TCompare {};
class TNotEqual final : public TCompare {};

class TConnective : public TBoolExpr {
public:
	std::vector<std::unique_ptr<TBoolExpr>> args;
	void children(std::vector<const TNode*>& out) const override;
};

class TAnd final : public TConnective {};
class TOr final : public TConnective {};

// --- Assertion ---

class TAssertion final : public TNode {
friend class TypedBuilder;
public:
	std::unique_ptr<TBoolExpr> cond;
	void children(std::vector<const TNode*>& out) const override;
	std::string toString() const override;
protected:
	Assertion* src_Assertion{nullptr};
};

// --- Definitions ---

class TInputDefinition final : public TNode {
friend class TypedBuilder;
public:
	std::shared_ptr<const SymbolInfo> symbol{};
	void children(std::vector<const TNode*>& out) const override;
	std::string toString() const override;
protected:
	InputDefinition* src_InputDefinition{nullptr};
};

class THiddenDefinition final : public TNode {
friend class TypedBuilder;
public:
	std::shared_ptr<const SymbolInfo> symbol{};
	void children(std::vector<const TNode*>& out) const override;
	std::string toString() const override;
protected:
	HiddenDefinition* src_HiddenDefinition{nullptr};
};

class TOutputDefinition final : public TNode {
friend class TypedBuilder;
public:
	std::shared_ptr<const SymbolInfo> symbol{};
	void children(std::vector<const TNode*>& out) const override;
	std::string toString() const override;
protected:
	OutputDefinition* src_OutputDefinition{nullptr};
};

// --- Network ---

class TNetworkDefinition final : public TNode {
friend class TypedBuilder;
public:
	std::string isometricTo{};
	std::string equalTo{};
	std::string networkName{};
	std::vector<std::unique_ptr<TInputDefinition>> inputs{};
	std::vector<std::unique_ptr<THiddenDefinition>> hidden{};
	std::vector<std::unique_ptr<TOutputDefinition>> outputs{};
	void children(std::vector<const TNode*>& out) const override;
	std::string toString() const override;
protected:
	NetworkDefinition* src_NetworkDefinition{nullptr};
};

// --- Version ---

class TVersion final : public TNode {
friend class TypedBuilder;
public:
	int major{0};
  	int minor{0};
	void children(std::vector<const TNode*>& out) const override;
	std::string toString() const override;
protected:
	Version* src_Version{nullptr};
};

// --- Query ---

class TQuery final : public TNode {
friend class TypedBuilder;
public:
	std::unique_ptr<TVersion> version{};
	std::vector<std::unique_ptr<TNetworkDefinition>> networks{};
	std::vector<std::unique_ptr<TAssertion>> assertions{};
	void children(std::vector<const TNode*>& out) const override;
	std::string toString() const override;
protected:
	Query* src_Query{nullptr};
};









