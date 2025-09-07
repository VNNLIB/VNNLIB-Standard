#include <sstream>
#include <typeinfo>
#include <algorithm>

#include "TypedAbsyn.h"  
#include "Absyn.H"
#include "Printer.H"

std::string dtypeToString(DType dt) {
  switch (dt) {
    case DType::Real: return "Real";
    case DType::F16: return "F16";
    case DType::F32: return "F32";
    case DType::F64: return "F64";
    case DType::BF16: return "BF16";
    case DType::F8E4M3FN: return "F8E4M3FN";
    case DType::F8E5M2: return "F8E5M2";
    case DType::F8E4M3FNUZ: return "F8E4M3FNUZ";
    case DType::F8E5M2FNUZ: return "F8E5M2FNUZ";
    case DType::F4E2M1: return "F4E2M1";
    case DType::I8: return "I8";
    case DType::I16: return "I16";
    case DType::I32: return "I32";
    case DType::I64: return "I64";
    case DType::U8: return "U8";
    case DType::U16: return "U16";
    case DType::U32: return "U32";
    case DType::U64: return "U64";
    case DType::C64: return "C64";
    case DType::C128: return "C128";
    case DType::Bool: return "Bool";
    case DType::String: return "String";
    case DType::FloatConstant: return "FloatConstant";
    case DType::NegativeIntConstant: return "NegativeIntConstant";
    case DType::PositiveIntConstant: return "PositiveIntConstant";
    default: return "Unknown";
  }
}

bool isConstant(DType dt) {
    return dt == DType::FloatConstant || dt == DType::NegativeIntConstant || dt == DType::PositiveIntConstant;
}

// Returns true if the data type of the expression is in the same family as a constant data type
bool sameFamily(DType exprType, DType constType) {
    if (isConstant(constType)) {
        switch (exprType) {
            case DType::Real:
            case DType::F16:
            case DType::F32:
            case DType::F64:
            case DType::BF16:
            case DType::F8E4M3FN:
            case DType::F8E5M2:
            case DType::F8E4M3FNUZ:
            case DType::F8E5M2FNUZ:
            case DType::F4E2M1:
              return constType == DType::FloatConstant;
            case DType::I8:
            case DType::I16:
            case DType::I32:
            case DType::I64:
              return constType == DType::NegativeIntConstant || constType == DType::PositiveIntConstant;
            case DType::U8:
            case DType::U16:
            case DType::U32:
            case DType::U64:
              return constType == DType::PositiveIntConstant;
            case DType::FloatConstant:
              return constType == DType::FloatConstant;
            case DType::NegativeIntConstant:
            case DType::PositiveIntConstant:
              return constType == DType::NegativeIntConstant || constType == DType::PositiveIntConstant;
            default:
                return false;
        }
    }
    return false; // If constDt is not a constant type
}

bool sameType(DType a, DType b) {
    return a == b;
}

std::string shapeToString(const Shape& s) {
	if (s.empty()) return "[]";
	std::ostringstream oss;
	oss << '[';
	for (size_t i = 0; i < s.size(); ++i) {
	if (i) oss << ',';
	oss << s[i];
	}
	oss << ']';
	return oss.str();
}

template <class T>
std::string bnfcPrint(const T* p) {
	if (!p) return "<null>";
	PrintAbsyn pr;
	return pr.print(const_cast<T*>(p));
}

// ---------- SymbolInfo ----------

bool SymbolInfo::isScalar() const { return shape.empty(); }
size_t SymbolInfo::rank() const { return shape.size(); }

// ---------- TElementType ----------

void TElementType::children(std::vector<const TNode*>& out) const {
	(void)out; // leaf
}

std::string TElementType::toString() const {
    return bnfcPrint(src_ElementType);
}

// ---------- TArithExpr ----------

std::string TArithExpr::toString() const {
    return bnfcPrint(src_ArithExpr);
}

void TVarExpr::children(std::vector<const TNode*>& out) const {
	(void)out;
}

void TLiteral::children(std::vector<const TNode*>& out) const {
	(void)out;
}

void TNegate::children(std::vector<const TNode*>& out) const {
	if (expr) out.push_back(expr.get());
}

void TPlus::children(std::vector<const TNode*>& out) const {
	for (auto const& a : args) if (a) out.push_back(a.get());
}

void TMinus::children(std::vector<const TNode*>& out) const {
	if (head) out.push_back(head.get());
	for (auto const& r : rest) if (r) out.push_back(r.get());
}

void TMultiply::children(std::vector<const TNode*>& out) const {
	for (auto const& a : args) if (a) out.push_back(a.get());
}

// ---------- TBoolExpr ----------

std::string TBoolExpr::toString() const {
    return bnfcPrint(src_BoolExpr);
}

void TCompare::children(std::vector<const TNode*>& out) const {
	if (lhs) out.push_back(lhs.get());
	if (rhs) out.push_back(rhs.get());
}

void TConnective::children(std::vector<const TNode*>& out) const {
	for (auto const& a : args) if (a) out.push_back(a.get());
}

// --- Assertion ---

void TAssertion::children(std::vector<const TNode*>& out) const {
	if (cond) out.push_back(cond.get());
}

std::string TAssertion::toString() const {
    return bnfcPrint(src_Assertion);
}

// --- Definitions ---

void TInputDefinition::children(std::vector<const TNode*>& out) const {
	(void)out; 
}

std::string TInputDefinition::toString() const {
    return bnfcPrint(src_InputDefinition);
}


void THiddenDefinition::children(std::vector<const TNode*>& out) const {
	(void)out;
}

std::string THiddenDefinition::toString() const {
    return bnfcPrint(src_HiddenDefinition);
}

void TOutputDefinition::children(std::vector<const TNode*>& out) const {
	(void)out; 
}

std::string TOutputDefinition::toString() const {
    return bnfcPrint(src_OutputDefinition);
}

// --- Network ---

void TNetworkDefinition::children(std::vector<const TNode*>& out) const {
    for (auto const& n : inputs)  if (n) out.push_back(n.get());
    for (auto const& n : hidden)  if (n) out.push_back(n.get());
    for (auto const& n : outputs) if (n) out.push_back(n.get());
}

std::string TNetworkDefinition::toString() const {
    return bnfcPrint(src_NetworkDefinition);
}

// --- Version ---

void TVersion::children(std::vector<const TNode*>& out) const {
	(void)out;
}

std::string TVersion::toString() const {
    return bnfcPrint(src_Version);
}

// --- Query ---

void TQuery::children(std::vector<const TNode*>& out) const {
	for (auto const& n : networks)   if (n) out.push_back(n.get());
	for (auto const& a : assertions) if (a) out.push_back(a.get());
}

std::string TQuery::toString() const {
    return bnfcPrint(src_Query);
}



