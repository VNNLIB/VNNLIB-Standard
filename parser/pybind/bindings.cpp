#include <pybind11/pybind11.h>
#include <pybind11/stl.h>      
#include <memory>

#include "VNNLib.h" 
#include "Absyn.h" 
#include "VNNLIBWrappers.hpp" 

namespace py = pybind11;

std::unique_ptr<QueryWrapper> generate(Query ptr);

PYBIND11_MODULE(vnnlib, m) {
    m.doc() = "Python bindings for VNNLib parsing and AST traversal";

    // --- Base ElementType Wrappers ---
    py::class_<ElementTypeWrapper> elemTypeWrapper(m, "ElementType");
    elemTypeWrapper
        .def("__str__", &ElementTypeWrapper::to_string); 

    // Concrete ElementTypes
    py::class_<GenericElementType, ElementTypeWrapper>(m, "GenericElementType");
    py::class_<ElementTypeF16, ElementTypeWrapper>(m, "ElementTypeF16");
    py::class_<ElementTypeF32, ElementTypeWrapper>(m, "ElementTypeF32");
    py::class_<ElementTypeF64, ElementTypeWrapper>(m, "ElementTypeF64");
    py::class_<ElementTypeBF16, ElementTypeWrapper>(m, "ElementTypeBF16");
    py::class_<ElementTypeF8E4M3FN, ElementTypeWrapper>(m, "ElementTypeF8E4M3FN");
    py::class_<ElementTypeF8E5M2, ElementTypeWrapper>(m, "ElementTypeF8E5M2");
    py::class_<ElementTypeF8E4M3FNUZ, ElementTypeWrapper>(m, "ElementTypeF8E4M3FNUZ");
    py::class_<ElementTypeF8E5M2FNUZ, ElementTypeWrapper>(m, "ElementTypeF8E5M2FNUZ");
    py::class_<ElementTypeF4E2M1, ElementTypeWrapper>(m, "ElementTypeF4E2M1");
    py::class_<ElementTypeI8, ElementTypeWrapper>(m, "ElementTypeI8");
    py::class_<ElementTypeI16, ElementTypeWrapper>(m, "ElementTypeI16");
    py::class_<ElementTypeI32, ElementTypeWrapper>(m, "ElementTypeI32");
    py::class_<ElementTypeI64, ElementTypeWrapper>(m, "ElementTypeI64");
    py::class_<ElementTypeU8, ElementTypeWrapper>(m, "ElementTypeU8");
    py::class_<ElementTypeU16, ElementTypeWrapper>(m, "ElementTypeU16");
    py::class_<ElementTypeU32, ElementTypeWrapper>(m, "ElementTypeU32");
    py::class_<ElementTypeU64, ElementTypeWrapper>(m, "ElementTypeU64");
    py::class_<ElementTypeC64, ElementTypeWrapper>(m, "ElementTypeC64");
    py::class_<ElementTypeC128, ElementTypeWrapper>(m, "ElementTypeC128");
    py::class_<ElementTypeBool, ElementTypeWrapper>(m, "ElementTypeBool");
    py::class_<ElementTypeString, ElementTypeWrapper>(m, "ElementTypeString");

    // --- ListInt ---
    py::class_<ListIntWrapper> listIntWrapper(m, "ListInt");
    listIntWrapper
        .def("__str__", &ListIntWrapper::to_string);

    py::class_<IntList, ListIntWrapper>(m, "IntList")
        .def_readonly("current", &IntList::int_)
        .def_property_readonly("next", [](const IntList &obj) {
            return obj.listint_.get();
        }, py::return_value_policy::reference_internal)
        .def("__iter__", [](IntList &self) {
            return py::make_iterator(self.begin(), self.end());
        }, py::keep_alive<0, 1>()); // Keep the list alive while iterating

    // --- ArithExpr --- 
    py::class_<ArithExprWrapper> arithExprWrapper(m, "ArithExpr");
    arithExprWrapper
        .def("__str__", &ArithExprWrapper::to_string);
    
    // ArithExpr (Operands)
    py::class_<VarExpr, ArithExprWrapper>(m, "VarExpr")
        .def_readonly("variable_name", &VarExpr::variablename_)
        .def_property_readonly("indices", [](const VarExpr &obj) { return obj.listint_.get(); }, py::return_value_policy::reference_internal);

    py::class_<DoubleExpr, ArithExprWrapper>(m, "DoubleExpr")
        .def_readonly("value", &DoubleExpr::sdouble_);

    py::class_<SIntExpr, ArithExprWrapper>(m, "SIntExpr")
        .def_readonly("value", &SIntExpr::sint_);

    py::class_<IntExpr, ArithExprWrapper>(m, "IntExpr")
        .def_readonly("value", &IntExpr::int_);

    py::class_<Negate, ArithExprWrapper>(m, "Negate")
        .def_property_readonly("expr", [](const Negate &obj) {
            return obj.arithexpr_.get();
        }, py::return_value_policy::reference_internal);

    // ArithExpr (Operators)
    py::class_<Plus, ArithExprWrapper>(m, "Plus")
        .def_property_readonly("operands", [](const Plus &obj) {
            return obj.listarithexpr_.get();
        }, py::return_value_policy::reference_internal);

    py::class_<Minus, ArithExprWrapper>(m, "Minus")
        .def_property_readonly("left", [](const Minus &obj) { // Assuming arithexpr_ is left
            return obj.arithexpr_.get();
        }, py::return_value_policy::reference_internal)
        .def_property_readonly("right_operands", [](const Minus &obj) { // Assuming listarithexpr_ are subsequent operands
            return obj.listarithexpr_.get();
        }, py::return_value_policy::reference_internal);

    py::class_<Multiply, ArithExprWrapper>(m, "Multiply")
        .def_property_readonly("operands", [](const Multiply &obj) {
            return obj.listarithexpr_.get();
        }, py::return_value_policy::reference_internal);

    // ListArithExpr
    py::class_<ListArithExprWrapper> listArithExprWrapper(m, "ListArithExpr");
    listArithExprWrapper
        .def("__str__", &ListArithExprWrapper::to_string);

    py::class_<ArithExprList, ListArithExprWrapper>(m, "ArithExprList")
        .def_property_readonly("current", [](const ArithExprList &obj) {
            return obj.arithexpr_.get();
        }, py::return_value_policy::reference_internal)
        .def_property_readonly("next", [](const ArithExprList &obj) {
            return obj.listarithexpr_.get();
        }, py::return_value_policy::reference_internal)
        .def("__iter__", [](ArithExprList &self) {
            return py::make_iterator(self.begin(), self.end());
        }, py::keep_alive<0, 1>());

    // --- BoolExpr ---
    py::class_<BoolExprWrapper> boolExprWrapper(m, "BoolExpr");
    boolExprWrapper
        .def("__str__", &BoolExprWrapper::to_string);

    // BoolExpr (Comparison)
    py::class_<GreaterThan, BoolExprWrapper>(m, "GreaterThan")
        .def_property_readonly("expr1", [](const GreaterThan &obj) { return obj.arithexpr_1.get(); }, py::return_value_policy::reference_internal)
        .def_property_readonly("expr2", [](const GreaterThan &obj) { return obj.arithexpr_2.get(); }, py::return_value_policy::reference_internal);

    py::class_<LessThan, BoolExprWrapper>(m, "LessThan")
        .def_property_readonly("expr1", [](const LessThan &obj) { return obj.arithexpr_1.get(); }, py::return_value_policy::reference_internal)
        .def_property_readonly("expr2", [](const LessThan &obj) { return obj.arithexpr_2.get(); }, py::return_value_policy::reference_internal);

    py::class_<GreaterEqual, BoolExprWrapper>(m, "GreaterEqual")
        .def_property_readonly("expr1", [](const GreaterEqual &obj) { return obj.arithexpr_1.get(); }, py::return_value_policy::reference_internal)
        .def_property_readonly("expr2", [](const GreaterEqual &obj) { return obj.arithexpr_2.get(); }, py::return_value_policy::reference_internal);

    py::class_<LessEqual, BoolExprWrapper>(m, "LessEqual")
        .def_property_readonly("expr1", [](const LessEqual &obj) { return obj.arithexpr_1.get(); }, py::return_value_policy::reference_internal)
        .def_property_readonly("expr2", [](const LessEqual &obj) { return obj.arithexpr_2.get(); }, py::return_value_policy::reference_internal);

    py::class_<NotEqual, BoolExprWrapper>(m, "NotEqual")
        .def_property_readonly("expr1", [](const NotEqual &obj) { return obj.arithexpr_1.get(); }, py::return_value_policy::reference_internal)
        .def_property_readonly("expr2", [](const NotEqual &obj) { return obj.arithexpr_2.get(); }, py::return_value_policy::reference_internal);

    py::class_<Equal, BoolExprWrapper>(m, "Equal")
        .def_property_readonly("expr1", [](const Equal &obj) { return obj.arithexpr_1.get(); }, py::return_value_policy::reference_internal)
        .def_property_readonly("expr2", [](const Equal &obj) { return obj.arithexpr_2.get(); }, py::return_value_policy::reference_internal);

    // BoolExpr (And, Or)
    py::class_<And, BoolExprWrapper>(m, "And")
        .def_property_readonly("operands", [](const And &obj) {
            return obj.listboolexpr_.get();
        }, py::return_value_policy::reference_internal);

    py::class_<Or, BoolExprWrapper>(m, "Or")
        .def_property_readonly("operands", [](const Or &obj) {
            return obj.listboolexpr_.get();
        }, py::return_value_policy::reference_internal);

    // ListBoolExpr
    py::class_<ListBoolExprWrapper> listBoolExprWrapper(m, "ListBoolExpr");
    listBoolExprWrapper
        .def("__str__", &ListBoolExprWrapper::to_string);

    py::class_<BoolExprList, ListBoolExprWrapper>(m, "BoolExprList")
        .def_property_readonly("current", [](const BoolExprList &obj) {
            return obj.boolexpr_.get();
        }, py::return_value_policy::reference_internal)
        .def_property_readonly("next", [](const BoolExprList &obj) {
            return obj.listboolexpr_.get();
        }, py::return_value_policy::reference_internal)
        .def("__iter__", [](BoolExprList &self) {
            return py::make_iterator(self.begin(), self.end());
        }, py::keep_alive<0, 1>());

    // --- Assertion --- 
    py::class_<AssertionWrapper> assertionWrapper(m, "AssertionBase"); // Changed name to avoid conflict if Query is also a property
    assertionWrapper
        .def("__str__", &AssertionWrapper::to_string);

    py::class_<Assert, AssertionWrapper>(m, "Assertion") // This is likely the main property type
        .def_property_readonly("expr", [](const Assert &obj) {
            return obj.boolexpr_.get();
        }, py::return_value_policy::reference_internal);

    // ListAssertion
    py::class_<ListAssertionWrapper> listAssertionWrapper(m, "ListAssertion");
    listAssertionWrapper
        .def("__str__", &ListAssertionWrapper::to_string);

    py::class_<AssertionList, ListAssertionWrapper>(m, "AssertionList")
        .def_property_readonly("current", [](const AssertionList &obj) { // Renamed to avoid conflict
            return obj.assertion_.get();
        }, py::return_value_policy::reference_internal)
        .def_property_readonly("next", [](const AssertionList &obj) {
            return obj.listassertion_.get();
        }, py::return_value_policy::reference_internal)
        .def("__iter__", [](AssertionList &self) {
            return py::make_iterator(self.begin(), self.end());
        }, py::keep_alive<0, 1>());

    // --- TensorShape ---
    py::class_<TensorShapeWrapper> tensorShapeWrapper(m, "TensorShape");
    tensorShapeWrapper
        .def("__str__", &TensorShapeWrapper::to_string);
    py::class_<TensorDims, TensorShapeWrapper>(m, "TensorDims")
        .def_property_readonly("dims", [](const TensorDims &obj) { return obj.listint_.get(); }, py::return_value_policy::reference_internal);
    py::class_<ScalarDims, TensorShapeWrapper>(m, "ScalarDims");

    // --- InputDefinition ---
    py::class_<InputDefinitionWrapper> inputDefWrapper(m, "InputDefinition");
    inputDefWrapper
        .def("__str__", &InputDefinitionWrapper::to_string);

    py::class_<InputDef, InputDefinitionWrapper>(m, "InputDef")
        .def_readonly("variable_name", &InputDef::variablename_)
        .def_property_readonly("element_type", [](const InputDef &obj) { return obj.elementtype_.get(); }, py::return_value_policy::reference_internal)
        .def_property_readonly("shape", [](const InputDef &obj) { return obj.tensorshape_.get(); }, py::return_value_policy::reference_internal);

    // ListInputDefinition
    py::class_<ListInputDefinitionWrapper> listInputDefWrapper(m, "ListInputDefinition");
    listInputDefWrapper
        .def("__str__", &ListInputDefinitionWrapper::to_string);

    py::class_<InputDefinitionList, ListInputDefinitionWrapper>(m, "InputDefinitionList")
        .def_property_readonly("current", [](const InputDefinitionList &obj) { 
            return obj.inputdefinition_.get(); 
        }, py::return_value_policy::reference_internal)
        .def_property_readonly("next", [](const InputDefinitionList &obj) { 
            return obj.listinputdefinition_.get(); 
        }, py::return_value_policy::reference_internal)
        .def("__iter__", [](InputDefinitionList &self) {
            return py::make_iterator(self.begin(), self.end());
        }, py::keep_alive<0, 1>());

    // --- HiddenDefinition ---
    py::class_<HiddenDefinitionWrapper> hiddenDefWrapper(m, "HiddenDefinition");
    hiddenDefWrapper
        .def("__str__", &HiddenDefinitionWrapper::to_string);
    
    py::class_<HiddenDef, HiddenDefinitionWrapper>(m, "HiddenDef")
        .def_readonly("onnx_name", &HiddenDef::string_) // Assuming 'string_' is a comment or similar
        .def_readonly("variable_name", &HiddenDef::variablename_)
        .def_property_readonly("element_type", [](const HiddenDef &obj) { return obj.elementtype_.get(); }, py::return_value_policy::reference_internal)
        .def_property_readonly("shape", [](const HiddenDef &obj) { return obj.tensorshape_.get(); }, py::return_value_policy::reference_internal);
        
    // ListHiddenDefinition
    py::class_<ListHiddenDefinitionWrapper> listHiddenDefWrapper(m, "ListHiddenDefinition");
    listHiddenDefWrapper
        .def("__str__", &ListHiddenDefinitionWrapper::to_string);

    py::class_<HiddenDefinitionList, ListHiddenDefinitionWrapper>(m, "HiddenDefinitionList")
        .def_property_readonly("current", [](const HiddenDefinitionList &obj) { 
            return obj.hiddendefinition_.get(); 
        }, py::return_value_policy::reference_internal)
        .def_property_readonly("next", [](const HiddenDefinitionList &obj) { 
            return obj.listhiddendefinition_.get(); 
        }, py::return_value_policy::reference_internal)
        .def("__iter__", [](HiddenDefinitionList &self) {
            return py::make_iterator(self.begin(), self.end());
        }, py::keep_alive<0, 1>());

    // --- OutputDefinition ---
    py::class_<OutputDefinitionWrapper> outputDefWrapper(m, "OutputDefinition");
    outputDefWrapper
        .def("__str__", &OutputDefinitionWrapper::to_string);

    py::class_<OutputDef, OutputDefinitionWrapper>(m, "OutputDef")
        .def_readonly("variable_name", &OutputDef::variablename_)
        .def_property_readonly("element_type", [](const OutputDef &obj) { return obj.elementtype_.get(); }, py::return_value_policy::reference_internal)
        .def_property_readonly("shape", [](const OutputDef &obj) { return obj.tensorshape_.get(); }, py::return_value_policy::reference_internal);
    
    // ListOutputDefinition
    py::class_<ListOutputDefinitionWrapper> listOutputDefWrapper(m, "ListOutputDefinition");
    listOutputDefWrapper
        .def("__str__", &ListOutputDefinitionWrapper::to_string);
    
    py::class_<OutputDefinitionList, ListOutputDefinitionWrapper>(m, "OutputDefinitionList")
        .def_property_readonly("current", [](const OutputDefinitionList &obj) { 
            return obj.outputdefinition_.get(); 
        }, py::return_value_policy::reference_internal)
        .def_property_readonly("next", [](const OutputDefinitionList &obj) { 
            return obj.listoutputdefinition_.get(); 
        }, py::return_value_policy::reference_internal)
        .def("__iter__", [](OutputDefinitionList &self) {
            return py::make_iterator(self.begin(), self.end());
        }, py::keep_alive<0, 1>());

    // --- NetworkDefinition ---
    py::class_<NetworkDefinitionWrapper> networkDefWrapper(m, "NetworkDefinition");
    networkDefWrapper
        .def("__str__", &NetworkDefinitionWrapper::to_string);

    py::class_<NetworkDef, NetworkDefinitionWrapper>(m, "NetworkDef")
        .def_readonly("variable_name", &NetworkDef::variablename_)
        .def_property_readonly("inputs", [](const NetworkDef &obj) { return obj.listinputdefinition_.get(); }, py::return_value_policy::reference_internal)
        .def_property_readonly("hiddens", [](const NetworkDef &obj) { return obj.listhiddendefinition_.get(); }, py::return_value_policy::reference_internal)
        .def_property_readonly("outputs", [](const NetworkDef &obj) { return obj.listoutputdefinition_.get(); }, py::return_value_policy::reference_internal);
    
    // ListNetworkDefinition
    py::class_<ListNetworkDefinitionWrapper> listNetworkDefWrapper(m, "ListNetworkDefinition");
    listNetworkDefWrapper
        .def("__str__", &ListNetworkDefinitionWrapper::to_string);

    py::class_<NetworkDefinitionList, ListNetworkDefinitionWrapper>(m, "NetworkDefinitionList")
        .def_property_readonly("current", [](const NetworkDefinitionList &obj) { 
            return obj.networkdefinition_.get(); 
        }, py::return_value_policy::reference_internal)
        .def_property_readonly("next", [](const NetworkDefinitionList &obj) { 
            return obj.listnetworkdefinition_.get(); 
        }, py::return_value_policy::reference_internal)
        .def("__iter__", [](NetworkDefinitionList &self) {
            return py::make_iterator(self.begin(), self.end());
        }, py::keep_alive<0, 1>());

    // --- Query ---
    py::class_<QueryWrapper> queryWrapper(m, "QueryBase");
    queryWrapper
        .def("__str__", &QueryWrapper::to_string);

    py::class_<VNNLibQuery, QueryWrapper>(m, "Query") 
        .def_property_readonly("networks", [](const VNNLibQuery &obj) {
            return obj.listnetworkdefinition_.get();
        }, py::return_value_policy::reference_internal)
        .def_property_readonly("assertions", [](const VNNLibQuery &obj) {
            return obj.listassertion_.get();
        }, py::return_value_policy::reference_internal);


    // Main Parsing Function
    m.def("parse_vnnlib", [](const std::string& path) -> std::unique_ptr<QueryWrapper> {
        // This calls the C function from VNNLib.h
        Query raw_c_query = parse_vnnlib(path.c_str());
        if (!raw_c_query) {
            throw std::runtime_error("Failed to parse VNNLib file: C parser returned null.");
        }

        // Scope Checking
        char *error_message = check_query(raw_c_query, 1);
        if (error_message != nullptr) {
            std::string error_str(error_message);
            free(error_message); 
            free_Query(raw_c_query); 
            throw std::runtime_error("VNNLib query parsing error:\n" + error_str);
        }

        std::unique_ptr<QueryWrapper> query_ast_wrapper = generate(raw_c_query);
        
        if (!query_ast_wrapper) {
            free_Query(raw_c_query); // Clean up the raw C pointer if wrapper generation failed
            throw std::runtime_error("Failed to generate C++ AST wrappers from parsed VNNLib query.");
        }
        
        return query_ast_wrapper;
    }, py::doc("Parses a VNNLib file and returns a traversable AST Query object."));


#ifdef VERSION_INFO
    m.attr("__version__") = VERSION_INFO;
#else
    m.attr("__version__") = "dev";
#endif
}