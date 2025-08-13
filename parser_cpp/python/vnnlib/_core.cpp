#include <pybind11/pybind11.h>
#include <pybind11/stl.h>      
#include <memory>
#include <exception>

#include "VNNLib.h" 
#include "Absyn.H" 
#include "Printer.H"
#include "TypeChecker.h"

class VNNLibException : public std::exception {
private:
    std::string message_;
public:
    VNNLibException(const std::string &message) : message_(message) {}
    const char* what() const noexcept override {
        return message_.c_str();
    }
};

// Helper function to convert AST nodes to strings
std::string nodeToString(Visitable* node) {
    if (!node) return "";
    ShowAbsyn printer;
    char* result = printer.show(node);
    return result ? std::string(result) : "";
}

// Helper function to convert AST nodes to pretty-printed strings
std::string nodeToPrettyString(Visitable* node) {
    if (!node) return "";
    PrintAbsyn printer;
    char* result = printer.print(node);
    return result ? std::string(result) : "";
}

namespace py = pybind11;

PYBIND11_MODULE(_core, m) {
    m.doc() = "Python bindings for VNNLib parsing and AST traversal";

    py::register_exception<VNNLibException>(m, "VNNLibException");

    // Helper functions
    m.def("node_to_string", &nodeToString, "Convert an AST node to its string representation");
    m.def("node_to_pretty_string", &nodeToPrettyString, "Convert an AST node to a pretty-printed string representation");

    // --- Base Classes ---
    py::class_<Visitable>(m, "Visitable")
        .def("__str__", [](Visitable* self) { return nodeToString(self); });

    // --- ElementType and Concrete Types ---
    py::class_<ElementType, Visitable>(m, "ElementType")
        .def("__str__", [](ElementType* self) { return nodeToString(self); });

    py::class_<GenericElementType, ElementType>(m, "GenericElementType");
    py::class_<ElementTypeF16, ElementType>(m, "ElementTypeF16");
    py::class_<ElementTypeF32, ElementType>(m, "ElementTypeF32");
    py::class_<ElementTypeF64, ElementType>(m, "ElementTypeF64");
    py::class_<ElementTypeBF16, ElementType>(m, "ElementTypeBF16");
    py::class_<ElementTypeF8E4M3FN, ElementType>(m, "ElementTypeF8E4M3FN");
    py::class_<ElementTypeF8E5M2, ElementType>(m, "ElementTypeF8E5M2");
    py::class_<ElementTypeF8E4M3FNUZ, ElementType>(m, "ElementTypeF8E4M3FNUZ");
    py::class_<ElementTypeF8E5M2FNUZ, ElementType>(m, "ElementTypeF8E5M2FNUZ");
    py::class_<ElementTypeF4E2M1, ElementType>(m, "ElementTypeF4E2M1");
    py::class_<ElementTypeI8, ElementType>(m, "ElementTypeI8");
    py::class_<ElementTypeI16, ElementType>(m, "ElementTypeI16");
    py::class_<ElementTypeI32, ElementType>(m, "ElementTypeI32");
    py::class_<ElementTypeI64, ElementType>(m, "ElementTypeI64");
    py::class_<ElementTypeU8, ElementType>(m, "ElementTypeU8");
    py::class_<ElementTypeU16, ElementType>(m, "ElementTypeU16");
    py::class_<ElementTypeU32, ElementType>(m, "ElementTypeU32");
    py::class_<ElementTypeU64, ElementType>(m, "ElementTypeU64");
    py::class_<ElementTypeC64, ElementType>(m, "ElementTypeC64");
    py::class_<ElementTypeC128, ElementType>(m, "ElementTypeC128");
    py::class_<ElementTypeBool, ElementType>(m, "ElementTypeBool");
    py::class_<ElementTypeString, ElementType>(m, "ElementTypeString");

    // --- TensorShape ---
    py::class_<TensorShape, Visitable>(m, "TensorShape")
        .def("__str__", [](TensorShape* self) { return nodeToString(self); });

    py::class_<ScalarDims, TensorShape>(m, "ScalarDims");
    
    py::class_<TensorDims, TensorShape>(m, "TensorDims")
        .def_readonly("dims", &TensorDims::listint_);

    // --- ListInt ---
    py::class_<ListInt>(m, "ListInt")
        .def("__len__", [](const ListInt &v) { return v.size(); })
        .def("__iter__", [](const ListInt &v) {
            return py::make_iterator(v.begin(), v.end());
        }, py::keep_alive<0, 1>())
        .def("__getitem__", [](const ListInt &v, size_t i) {
            if (i >= v.size()) throw py::index_error();
            return v[i];
        })
        .def("__str__", [](const ListInt &v) {
            std::string result = "[";
            for (size_t i = 0; i < v.size(); ++i) {
                if (i > 0) result += ", ";
                result += v[i];
            }
            result += "]";
            return result;
        });

    // --- ArithExpr and Concrete Types ---
    py::class_<ArithExpr, Visitable>(m, "ArithExpr")
        .def("__str__", [](ArithExpr* self) { return nodeToString(self); });

    py::class_<VarExpr, ArithExpr>(m, "VarExpr")
        .def_readonly("variable_name", &VarExpr::variablename_)
        .def_readonly("indices", &VarExpr::listint_);

    py::class_<DoubleExpr, ArithExpr>(m, "DoubleExpr")
        .def_readonly("value", &DoubleExpr::sdouble_);

    py::class_<SIntExpr, ArithExpr>(m, "SIntExpr")
        .def_readonly("value", &SIntExpr::sint_);

    py::class_<IntExpr, ArithExpr>(m, "IntExpr")
        .def_readonly("value", &IntExpr::int_);

    py::class_<Negate, ArithExpr>(m, "Negate")
        .def_readonly("expr", &Negate::arithexpr_);

    py::class_<Plus, ArithExpr>(m, "Plus")
        .def_readonly("operands", &Plus::listarithexpr_);

    py::class_<Minus, ArithExpr>(m, "Minus")
        .def_readonly("left", &Minus::arithexpr_)
        .def_readonly("right_operands", &Minus::listarithexpr_);

    py::class_<Multiply, ArithExpr>(m, "Multiply")
        .def_readonly("operands", &Multiply::listarithexpr_);

    // --- ListArithExpr ---
    py::class_<ListArithExpr>(m, "ListArithExpr")
        .def("__len__", [](const ListArithExpr &v) { return v.size(); })
        .def("__iter__", [](const ListArithExpr &v) {
            return py::make_iterator(v.begin(), v.end());
        }, py::keep_alive<0, 1>())
        .def("__getitem__", [](const ListArithExpr &v, size_t i) -> ArithExpr* {
            if (i >= v.size()) throw py::index_error();
            return v[i];
        }, py::return_value_policy::reference_internal);

    // --- BoolExpr and Concrete Types ---
    py::class_<BoolExpr, Visitable>(m, "BoolExpr")
        .def("__str__", [](BoolExpr* self) { return nodeToString(self); });

    py::class_<GreaterThan, BoolExpr>(m, "GreaterThan")
        .def_readonly("expr1", &GreaterThan::arithexpr_1)
        .def_readonly("expr2", &GreaterThan::arithexpr_2);

    py::class_<LessThan, BoolExpr>(m, "LessThan")
        .def_readonly("expr1", &LessThan::arithexpr_1)
        .def_readonly("expr2", &LessThan::arithexpr_2);

    py::class_<GreaterEqual, BoolExpr>(m, "GreaterEqual")
        .def_readonly("expr1", &GreaterEqual::arithexpr_1)
        .def_readonly("expr2", &GreaterEqual::arithexpr_2);

    py::class_<LessEqual, BoolExpr>(m, "LessEqual")
        .def_readonly("expr1", &LessEqual::arithexpr_1)
        .def_readonly("expr2", &LessEqual::arithexpr_2);

    py::class_<NotEqual, BoolExpr>(m, "NotEqual")
        .def_readonly("expr1", &NotEqual::arithexpr_1)
        .def_readonly("expr2", &NotEqual::arithexpr_2);

    py::class_<Equal, BoolExpr>(m, "Equal")
        .def_readonly("expr1", &Equal::arithexpr_1)
        .def_readonly("expr2", &Equal::arithexpr_2);

    py::class_<And, BoolExpr>(m, "And")
        .def_readonly("operands", &And::listboolexpr_);

    py::class_<Or, BoolExpr>(m, "Or")
        .def_readonly("operands", &Or::listboolexpr_);

    // --- ListBoolExpr ---
    py::class_<ListBoolExpr>(m, "ListBoolExpr")
        .def("__len__", [](const ListBoolExpr &v) { return v.size(); })
        .def("__iter__", [](const ListBoolExpr &v) {
            return py::make_iterator(v.begin(), v.end());
        }, py::keep_alive<0, 1>())
        .def("__getitem__", [](const ListBoolExpr &v, size_t i) -> BoolExpr* {
            if (i >= v.size()) throw py::index_error();
            return v[i];
        }, py::return_value_policy::reference_internal);

    // --- Assertion ---
    py::class_<Assertion, Visitable>(m, "Assertion")
        .def("__str__", [](Assertion* self) { return nodeToString(self); });

    py::class_<Assert, Assertion>(m, "Assert")
        .def_readonly("expr", &Assert::boolexpr_);

    // --- ListAssertion ---
    py::class_<ListAssertion>(m, "ListAssertion")
        .def("__len__", [](const ListAssertion &v) { return v.size(); })
        .def("__iter__", [](const ListAssertion &v) {
            return py::make_iterator(v.begin(), v.end());
        }, py::keep_alive<0, 1>())
        .def("__getitem__", [](const ListAssertion &v, size_t i) -> Assertion* {
            if (i >= v.size()) throw py::index_error();
            return v[i];
        }, py::return_value_policy::reference_internal);

    // --- InputDefinition ---
    py::class_<InputDefinition, Visitable>(m, "InputDefinition")
        .def("__str__", [](InputDefinition* self) { return nodeToString(self); });

    py::class_<InputDef, InputDefinition>(m, "InputDef")
        .def_readonly("variable_name", &InputDef::variablename_)
        .def_readonly("element_type", &InputDef::elementtype_)
        .def_readonly("shape", &InputDef::tensorshape_);

    py::class_<InputOnnxDef, InputDefinition>(m, "InputOnnxDef")
        .def_readonly("variable_name", &InputOnnxDef::variablename_)
        .def_readonly("element_type", &InputOnnxDef::elementtype_)
        .def_readonly("shape", &InputOnnxDef::tensorshape_)
        .def_readonly("onnx_name", &InputOnnxDef::string_);

    // --- ListInputDefinition ---
    py::class_<ListInputDefinition>(m, "ListInputDefinition")
        .def("__len__", [](const ListInputDefinition &v) { return v.size(); })
        .def("__iter__", [](const ListInputDefinition &v) {
            return py::make_iterator(v.begin(), v.end());
        }, py::keep_alive<0, 1>())
        .def("__getitem__", [](const ListInputDefinition &v, size_t i) -> InputDefinition* {
            if (i >= v.size()) throw py::index_error();
            return v[i];
        }, py::return_value_policy::reference_internal);

    // --- HiddenDefinition ---
    py::class_<HiddenDefinition, Visitable>(m, "HiddenDefinition")
        .def("__str__", [](HiddenDefinition* self) { return nodeToString(self); });

    py::class_<HiddenDef, HiddenDefinition>(m, "HiddenDef")
        .def_readonly("variable_name", &HiddenDef::variablename_)
        .def_readonly("element_type", &HiddenDef::elementtype_)
        .def_readonly("shape", &HiddenDef::tensorshape_)
        .def_readonly("onnx_name", &HiddenDef::string_);

    // --- ListHiddenDefinition ---
    py::class_<ListHiddenDefinition>(m, "ListHiddenDefinition")
        .def("__len__", [](const ListHiddenDefinition &v) { return v.size(); })
        .def("__iter__", [](const ListHiddenDefinition &v) {
            return py::make_iterator(v.begin(), v.end());
        }, py::keep_alive<0, 1>())
        .def("__getitem__", [](const ListHiddenDefinition &v, size_t i) -> HiddenDefinition* {
            if (i >= v.size()) throw py::index_error();
            return v[i];
        }, py::return_value_policy::reference_internal);

    // --- OutputDefinition ---
    py::class_<OutputDefinition, Visitable>(m, "OutputDefinition")
        .def("__str__", [](OutputDefinition* self) { return nodeToString(self); });

    py::class_<OutputDef, OutputDefinition>(m, "OutputDef")
        .def_readonly("variable_name", &OutputDef::variablename_)
        .def_readonly("element_type", &OutputDef::elementtype_)
        .def_readonly("shape", &OutputDef::tensorshape_);

    py::class_<OutputOnnxDef, OutputDefinition>(m, "OutputOnnxDef")
        .def_readonly("variable_name", &OutputOnnxDef::variablename_)
        .def_readonly("element_type", &OutputOnnxDef::elementtype_)
        .def_readonly("shape", &OutputOnnxDef::tensorshape_)
        .def_readonly("onnx_name", &OutputOnnxDef::string_);

    // --- ListOutputDefinition ---
    py::class_<ListOutputDefinition>(m, "ListOutputDefinition")
        .def("__len__", [](const ListOutputDefinition &v) { return v.size(); })
        .def("__iter__", [](const ListOutputDefinition &v) {
            return py::make_iterator(v.begin(), v.end());
        }, py::keep_alive<0, 1>())
        .def("__getitem__", [](const ListOutputDefinition &v, size_t i) -> OutputDefinition* {
            if (i >= v.size()) throw py::index_error();
            return v[i];
        }, py::return_value_policy::reference_internal);

    // --- NetworkDefinition ---
    py::class_<NetworkDefinition, Visitable>(m, "NetworkDefinition")
        .def("__str__", [](NetworkDefinition* self) { return nodeToString(self); });

    py::class_<NetworkDef, NetworkDefinition>(m, "NetworkDef")
        .def_readonly("variable_name", &NetworkDef::variablename_)
        .def_readonly("inputs", &NetworkDef::listinputdefinition_)
        .def_readonly("hiddens", &NetworkDef::listhiddendefinition_)
        .def_readonly("outputs", &NetworkDef::listoutputdefinition_);

    // --- ListNetworkDefinition ---
    py::class_<ListNetworkDefinition>(m, "ListNetworkDefinition")
        .def("__len__", [](const ListNetworkDefinition &v) { return v.size(); })
        .def("__iter__", [](const ListNetworkDefinition &v) {
            return py::make_iterator(v.begin(), v.end());
        }, py::keep_alive<0, 1>())
        .def("__getitem__", [](const ListNetworkDefinition &v, size_t i) -> NetworkDefinition* {
            if (i >= v.size()) throw py::index_error();
            return v[i];
        }, py::return_value_policy::reference_internal);

    // --- Query ---
    py::class_<Query, Visitable>(m, "Query")
        .def("__str__", [](Query* self) { return nodeToString(self); });

    py::class_<VNNLibQuery, Query>(m, "VNNLibQuery") 
        .def_readonly("networks", &VNNLibQuery::listnetworkdefinition_)
        .def_readonly("assertions", &VNNLibQuery::listassertion_);

    // --- Parsing Functions ---
    m.def("parse_vnnlib", [](const std::string& path) -> VNNLibQuery* {
        VNNLibQuery* result = parse_vnnlib(path.c_str());
        if (!result) {
            throw VNNLibException("Failed to parse VNNLIB file: " + path);
        }
        // Perform semantic checking
        auto typeChecker = std::make_unique<TypeChecker>();
        typeChecker->visitVNNLibQuery(result);
        if (typeChecker->hasErrors()) {
            std::string errorReport = typeChecker->getErrorReport(true); // Get JSON format
            throw VNNLibException(errorReport);
        }
        return result;
    }, py::return_value_policy::take_ownership, 
       py::doc("Parses a VNNLib file and returns a VNNLibQuery AST object."));

    m.def("parse_vnnlib_str", [](const std::string& content) -> VNNLibQuery* {
        VNNLibQuery* result = parse_vnnlib_str(content.c_str());
        if (!result) {
            throw VNNLibException("Failed to parse VNNLIB string");
        }
        // Perform semantic checking
        auto typeChecker = std::make_unique<TypeChecker>();
        typeChecker->visitVNNLibQuery(result);
        if (typeChecker->hasErrors()) {
            std::string errorReport = typeChecker->getErrorReport(true); // Get JSON format
            throw VNNLibException(errorReport);
        }
        return result;
    }, py::return_value_policy::take_ownership,
       py::doc("Parses a VNNLib string and returns a VNNLibQuery AST object."));

    m.def("write_vnnlib_str", &write_vnnlib_str,
          py::doc("Converts a VNNLibQuery AST object back to a VNNLIB string."));

    m.def("check_query", [](VNNLibQuery* query, bool json = false) -> py::dict {
        int result = check_query(query, json ? 1 : 0);
        py::dict ret;
        ret["success"] = (result == 0);
        ret["exit_code"] = result;
        return ret;
    }, py::arg("query"), py::arg("json") = false,
       py::doc("Performs semantic checks on a VNNLibQuery and returns the result."));

#ifdef VERSION_INFO
    m.attr("__version__") = VERSION_INFO;
#else
    m.attr("__version__") = "dev";
#endif
}
