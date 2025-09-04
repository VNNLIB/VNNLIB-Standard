#pragma once
#include <cstdint>
#include <typeindex>
#include <typeinfo>
#include <unordered_map>
#include <memory>

#if defined(__GNUG__)
    #include <cxxabi.h>
#endif

#include "Absyn.H"

// Extra derived classes for constant types
class FloatConstant final : public ElementType {
public:
    FloatConstant() = default;
    FloatConstant(const FloatConstant&) = default;
    FloatConstant& operator=(const FloatConstant&) = default;
    ~FloatConstant() override = default;

    void accept(Visitor*) override { /* no-op */ }
    FloatConstant* clone() const override { return new FloatConstant(*this); }

    void swap(FloatConstant&) {}
};

class PositiveIntConstant final : public ElementType {
public:
    PositiveIntConstant() = default;
    PositiveIntConstant(const PositiveIntConstant&) = default;
    PositiveIntConstant& operator=(const PositiveIntConstant&) = default;
    ~PositiveIntConstant() override = default;

    void accept(Visitor*) override { /* no-op */ }
    PositiveIntConstant* clone() const override { return new PositiveIntConstant(*this); }
    void swap(PositiveIntConstant&) {}
};

class NegativeIntConstant final : public ElementType {
public:
    NegativeIntConstant() = default;
    NegativeIntConstant(const NegativeIntConstant&) = default;
    NegativeIntConstant& operator=(const NegativeIntConstant&) = default;
    ~NegativeIntConstant() override = default;

    void accept(Visitor* /*v*/) override { /* no-op */ }
    NegativeIntConstant* clone() const override { return new NegativeIntConstant(*this); }
    void swap(NegativeIntConstant&) {}
};

enum class TypeFlag : uint32_t {
    None = 0,
    Float = 1u << 0,
    Integer = 1u << 1,
    Signed = 1u << 2,
    Unsigned = 1u << 3,
    Constant = 1u << 4,
    NonNumeric = 1u << 5,
    Complex = 1u << 6,
};

constexpr TypeFlag operator|(TypeFlag lhs, TypeFlag rhs) {
    return static_cast<TypeFlag>(static_cast<uint32_t>(lhs) | static_cast<uint32_t>(rhs));
}

constexpr TypeFlag operator&(TypeFlag lhs, TypeFlag rhs) {
    return static_cast<TypeFlag>(static_cast<uint32_t>(lhs) & static_cast<uint32_t>(rhs));
}

constexpr bool has(TypeFlag flags, TypeFlag test) {
    return (static_cast<uint32_t>(flags & test) != 0u);
}

struct ElementTypeFlagRegistry {
    static ElementTypeFlagRegistry& instance() {
        static ElementTypeFlagRegistry R;
        return R;
    }
    template <class T>
    void add(TypeFlag f) {
        map_.emplace(std::type_index(typeid(T)), f);
    }
    TypeFlag get(const ElementType &t) const {
        auto it = map_.find(std::type_index(typeid(t)));
        return (it == map_.end()) ? TypeFlag::None : it->second;
    }
private:
    std::unordered_map<std::type_index, TypeFlag> map_;
};

inline void registerTypeFlags() {
    auto& registry = ElementTypeFlagRegistry::instance();
    registry.add<GenericElementType>(TypeFlag::Float | TypeFlag::Integer | TypeFlag::Signed);
    registry.add<ElementTypeF16>(TypeFlag::Float);
    registry.add<ElementTypeF32>(TypeFlag::Float);
    registry.add<ElementTypeF64>(TypeFlag::Float);
    registry.add<ElementTypeBF16>(TypeFlag::Float);
    registry.add<ElementTypeF8E4M3FN>(TypeFlag::Float);
    registry.add<ElementTypeF8E5M2>(TypeFlag::Float);
    registry.add<ElementTypeF8E4M3FNUZ>(TypeFlag::Float);
    registry.add<ElementTypeF8E5M2FNUZ>(TypeFlag::Float);
    registry.add<ElementTypeF4E2M1>(TypeFlag::Float);
    registry.add<ElementTypeI8>(TypeFlag::Integer | TypeFlag::Signed);
    registry.add<ElementTypeI16>(TypeFlag::Integer | TypeFlag::Signed);
    registry.add<ElementTypeI32>(TypeFlag::Integer | TypeFlag::Signed);
    registry.add<ElementTypeI64>(TypeFlag::Integer | TypeFlag::Signed);
    registry.add<ElementTypeU8>(TypeFlag::Integer | TypeFlag::Unsigned);
    registry.add<ElementTypeU16>(TypeFlag::Integer | TypeFlag::Unsigned);
    registry.add<ElementTypeU32>(TypeFlag::Integer | TypeFlag::Unsigned);
    registry.add<ElementTypeU64>(TypeFlag::Integer | TypeFlag::Unsigned);
    registry.add<ElementTypeC64>(TypeFlag::Complex);
    registry.add<ElementTypeC128>(TypeFlag::Complex);
    registry.add<ElementTypeBool>(TypeFlag::NonNumeric);
    registry.add<ElementTypeString>(TypeFlag::NonNumeric);
    registry.add<FloatConstant>(TypeFlag::Float | TypeFlag::Constant);
    registry.add<PositiveIntConstant>(TypeFlag::Integer | TypeFlag::Constant);
    registry.add<NegativeIntConstant>(TypeFlag::Integer | TypeFlag::Signed | TypeFlag::Constant);
}

inline TypeFlag getFlags(const ElementType& t) {
    return ElementTypeFlagRegistry::instance().get(t);
}

inline bool isFloat(const ElementType &t) {
    return has(getFlags(t), TypeFlag::Float);
}

inline bool isInteger(const ElementType &t) {
    return has(getFlags(t), TypeFlag::Integer);
}

inline bool isSignedInteger(const ElementType &t) {
    return has(getFlags(t), TypeFlag::Signed);
}

inline bool isUnsignedInteger(const ElementType &t) {
    return has(getFlags(t), TypeFlag::Unsigned);
}

inline bool isConstant(const ElementType &t) {
    return has(getFlags(t), TypeFlag::Constant);
}

// Check if the variable type is compatible with the constant expression type
inline bool sameFamily(const ElementType &variable, const ElementType &constant) {
    return  (isFloat(variable) && isFloat(constant)) ||
            (isSignedInteger(variable) && isInteger(constant)) ||
            (isUnsignedInteger(variable) && typeid(constant) == typeid(PositiveIntConstant));
}

// Checks if two ElementType objects are of the same type
inline bool sameType(const ElementType& a, const ElementType& b) {
    return std::type_index(typeid(a)) == std::type_index(typeid(b));
}

inline std::string demangle(const char* name) {
#if defined(__GNUG__)
    int status = 0;
    std::unique_ptr<char, void(*)(void*)> p{
        abi::__cxa_demangle(name, nullptr, nullptr, &status),
        std::free
    };
    return (status == 0 && p) ? std::string(p.get()) : std::string(name);
#else
    return std::string(name); // MSVC/others
#endif
}

inline std::string elementTypeToString(const ElementType &t) {
    return demangle(typeid(t).name());
}
