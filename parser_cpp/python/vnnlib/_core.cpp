#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include <memory>
#include <exception>
#include <string>
#include <vector>

#include "VNNLib.h"                
#include "TypeChecker.h"     
#include "TypedAbsyn.h"     
#include "TypedBuilder.h"

namespace py = pybind11;

PYBIND11_MODULE(_core, m) {
	m.doc() = "Python bindings for VNNLib parsing and AST traversal";

	py::register_exception<VNNLibException>(m, "VNNLibException");

	// Helper Types
	py::enum_<DType>(m, "DType")
		.value("Real", DType::Real)
		.value("F16", DType::F16).value("F32", DType::F32).value("F64", DType::F64).value("BF16", DType::BF16)
		.value("F8E4M3FN", DType::F8E4M3FN).value("F8E5M2", DType::F8E5M2)
		.value("F8E4M3FNUZ", DType::F8E4M3FNUZ).value("F8E5M2FNUZ", DType::F8E5M2FNUZ)
		.value("F4E2M1", DType::F4E2M1)
		.value("I8", DType::I8).value("I16", DType::I16).value("I32", DType::I32).value("I64", DType::I64)
		.value("U8", DType::U8).value("U16", DType::U16).value("U32", DType::U32).value("U64", DType::U64)
		.value("C64", DType::C64).value("C128", DType::C128)
		.value("Bool", DType::Bool).value("String", DType::String)
		.value("Unknown", DType::Unknown)
		.value("NegativeIntConstant", DType::NegativeIntConstant)
		.value("PositiveIntConstant", DType::PositiveIntConstant)
		.value("FloatConstant", DType::FloatConstant);

	py::enum_<SymbolKind>(m, "SymbolKind")
		.value("Input", SymbolKind::Input)
		.value("Hidden", SymbolKind::Hidden)
		.value("Output", SymbolKind::Output)
		.value("Unknown", SymbolKind::Unknown);

	py::class_<TNode>(m, "Node")
		.def("__str__", [](const TNode& n){ return n.toString(); })
		.def("children", [](py::object self){ 
			const TNode& n = self.cast<const TNode&>();
			std::vector<const TNode*> children;
			n.children(children);
			py::tuple out(children.size());

			for (int i = 0; i < children.size(); ++i) {
				out[i] = py::cast(children[i], py::return_value_policy::reference_internal, self);
			}
			return out;
		});

	// --- Arithmetic Operations --- 
	py::class_<TArithExpr, TNode>(m, "ArithExpr")
		.def_property_readonly("dtype", [](const TArithExpr& e){ return e.dtype; });

	py::class_<TVarExpr, TArithExpr>(m, "Var")
		.def_property_readonly("name",      [](const TVarExpr& v){ return v.symbol ? v.symbol->name : std::string{}; })
		.def_property_readonly("onnx_name", [](const TVarExpr& v)->py::object{
			if (v.symbol->onnxName.empty()) return py::none();
			return py::str(v.symbol->onnxName);
		})
		.def_property_readonly("dtype",       [](const TVarExpr& v){ return v.symbol->dtype; })
		.def_property_readonly("shape",       [](const TVarExpr& v){ return v.symbol->shape; })
		.def_property_readonly("kind",        [](const TVarExpr& v){ return v.symbol->kind; })
		.def_property_readonly("network_name",[](const TVarExpr& v){ return v.symbol->networkName; })
		.def_property_readonly("indices",     [](const TVarExpr& v){ return v.indices; });

	py::class_<TDoubleExpr, TArithExpr>(m, "Double")
		.def_property_readonly("value",  [](const TDoubleExpr& e){ return e.value; })
		.def_property_readonly("lexeme", [](const TDoubleExpr& e){ return e.lexeme; });

	py::class_<TSIntExpr, TArithExpr>(m, "SInt")
		.def_property_readonly("value",  [](const TSIntExpr& e){ return e.value; })
		.def_property_readonly("lexeme", [](const TSIntExpr& e){ return e.lexeme; });

	py::class_<TIntExpr, TArithExpr>(m, "Int")
		.def_property_readonly("value",  [](const TIntExpr& e){ return e.value; })
		.def_property_readonly("lexeme", [](const TIntExpr& e){ return e.lexeme; });

	py::class_<TPlus, TArithExpr>(m, "Plus")
	.def_property_readonly("args", [](const TPlus& n){
		py::tuple args_tuple(n.args.size());
		for (size_t i = 0; i < n.args.size(); ++i)
			args_tuple[i] = py::cast(n.args[i].get(), py::return_value_policy::reference_internal, py::cast(&n));
		return args_tuple;
	});

	py::class_<TMinus, TArithExpr>(m, "Minus")
	.def_property_readonly("head", [](const TMinus& n){ return n.head.get(); }, py::return_value_policy::reference_internal)
	.def_property_readonly("rest", [](const TMinus& n){
		py::tuple rest_tuple(n.rest.size());
		for (size_t i = 0; i < n.rest.size(); ++i)
			rest_tuple[i] = py::cast(n.rest[i].get(), py::return_value_policy::reference_internal, py::cast(&n));
		return rest_tuple;
	});

	py::class_<TMultiply, TArithExpr>(m, "Multiply")
	.def_property_readonly("args", [](const TMultiply& n){
		py::tuple args_tuple(n.args.size());
		for (size_t i = 0; i < n.args.size(); ++i)
			args_tuple[i] = py::cast(n.args[i].get(), py::return_value_policy::reference_internal, py::cast(&n));
		return args_tuple;
	});

  	// ---------- Boolean Operations ----------
	py::class_<TBoolExpr, TNode>(m, "BoolExpr");

	py::class_<TGreaterThan, TBoolExpr>(m, "GreaterThan")
		.def_property_readonly("lhs", [](const TGreaterThan& n){ return n.lhs.get(); }, py::return_value_policy::reference_internal)
		.def_property_readonly("rhs", [](const TGreaterThan& n){ return n.rhs.get(); }, py::return_value_policy::reference_internal);
	py::class_<TLessThan, TBoolExpr>(m, "LessThan")
		.def_property_readonly("lhs", [](const TLessThan& n){ return n.lhs.get(); }, py::return_value_policy::reference_internal)
		.def_property_readonly("rhs", [](const TLessThan& n){ return n.rhs.get(); }, py::return_value_policy::reference_internal);
	py::class_<TGreaterEqual, TBoolExpr>(m, "GreaterEqual")
		.def_property_readonly("lhs", [](const TGreaterEqual& n){ return n.lhs.get(); }, py::return_value_policy::reference_internal)
		.def_property_readonly("rhs", [](const TGreaterEqual& n){ return n.rhs.get(); }, py::return_value_policy::reference_internal);
	py::class_<TLessEqual, TBoolExpr>(m, "LessEqual")
		.def_property_readonly("lhs", [](const TLessEqual& n){ return n.lhs.get(); }, py::return_value_policy::reference_internal)
		.def_property_readonly("rhs", [](const TLessEqual& n){ return n.rhs.get(); }, py::return_value_policy::reference_internal);
	py::class_<TNotEqual, TBoolExpr>(m, "NotEqual")
		.def_property_readonly("lhs", [](const TNotEqual& n){ return n.lhs.get(); }, py::return_value_policy::reference_internal)
		.def_property_readonly("rhs", [](const TNotEqual& n){ return n.rhs.get(); }, py::return_value_policy::reference_internal);
	py::class_<TEqual, TBoolExpr>(m, "Equal")
		.def_property_readonly("lhs", [](const TEqual& n){ return n.lhs.get(); }, py::return_value_policy::reference_internal)
		.def_property_readonly("rhs", [](const TEqual& n){ return n.rhs.get(); }, py::return_value_policy::reference_internal);

	py::class_<TAnd, TBoolExpr>(m, "And")
		.def_property_readonly("args", [](const TAnd& n){
			py::tuple args_tuple(n.args.size());
			for (size_t i = 0; i < n.args.size(); ++i)
				args_tuple[i] = py::cast(n.args[i].get(), py::return_value_policy::reference_internal, py::cast(&n));
			return args_tuple;
		});

	py::class_<TOr, TBoolExpr>(m, "Or")
		.def_property_readonly("args", [](const TOr& n){
			py::tuple args_tuple(n.args.size());
			for (size_t i = 0; i < n.args.size(); ++i)
				args_tuple[i] = py::cast(n.args[i].get(), py::return_value_policy::reference_internal, py::cast(&n));
			return args_tuple;
		});

	// --- Assertion ---
	py::class_<TAssertion, TNode>(m, "Assertion")
		.def_property_readonly("expr", [](const TAssertion& a){ return a.cond.get(); }, py::return_value_policy::reference_internal);
	
	// --- Definitions ---
	py::class_<TInputDefinition, TNode>(m, "InputDefinition")
		.def_property_readonly("name", [](const TInputDefinition& d){ return d.symbol ? d.symbol->name : std::string{}; })
		.def_property_readonly("onnx_name", [](const TInputDefinition& d)->py::object{
			if (d.symbol->onnxName.empty()) return py::none();
			return py::str(d.symbol->onnxName);
		})
		.def_property_readonly("dtype", [](const TInputDefinition& d){ return d.symbol ? d.symbol->dtype : DType::Unknown; })
		.def_property_readonly("shape", [](const TInputDefinition& d){ return d.symbol ? d.symbol->shape : Shape{}; })
		.def_property_readonly("kind",  [](const TInputDefinition& d){ return d.symbol ? d.symbol->kind : SymbolKind::Unknown; })
		.def_property_readonly("network_name", [](const TInputDefinition& d){ return d.symbol ? d.symbol->networkName : std::string{}; });

	py::class_<THiddenDefinition, TNode>(m, "HiddenDefinition")
		.def_property_readonly("name", [](const THiddenDefinition& d){ return d.symbol ? d.symbol->name : std::string{}; })
		.def_property_readonly("onnx_name", [](const THiddenDefinition& d)->py::object{
			if (d.symbol->onnxName.empty()) return py::none();
			return py::str(d.symbol->onnxName);
		})
		.def_property_readonly("dtype", [](const THiddenDefinition& d){ return d.symbol ? d.symbol->dtype : DType::Unknown; })
		.def_property_readonly("shape", [](const THiddenDefinition& d){ return d.symbol ? d.symbol->shape : Shape{}; })
		.def_property_readonly("kind",  [](const THiddenDefinition& d){ return d.symbol ? d.symbol->kind : SymbolKind::Unknown; })
		.def_property_readonly("network_name", [](const THiddenDefinition& d){ return d.symbol ? d.symbol->networkName : std::string{}; });

	py::class_<TOutputDefinition, TNode>(m, "OutputDefinition")
		.def_property_readonly("name", [](const TOutputDefinition& d){ return d.symbol ? d.symbol->name : std::string{}; })
		.def_property_readonly("onnx_name", [](const TOutputDefinition& d)->py::object{
			if (d.symbol->onnxName.empty()) return py::none();
			return py::str(d.symbol->onnxName);
		})
		.def_property_readonly("dtype", [](const TOutputDefinition& d){ return d.symbol ? d.symbol->dtype : DType::Unknown; })
		.def_property_readonly("shape", [](const TOutputDefinition& d){ return d.symbol ? d.symbol->shape : Shape{}; })
		.def_property_readonly("kind",  [](const TOutputDefinition& d){ return d.symbol ? d.symbol->kind : SymbolKind::Unknown; })
		.def_property_readonly("network_name", [](const TOutputDefinition& d){ return d.symbol ? d.symbol->networkName : std::string{}; });

	// --- Network ---
	py::class_<TNetworkDefinition, TNode>(m, "Network")
	.def_property_readonly("name", [](const TNetworkDefinition& n){ return n.networkName; })
	.def_property_readonly("inputs", [](const TNetworkDefinition& n){
		py::tuple input_tuple(n.inputs.size());
		for (size_t i = 0; i < n.inputs.size(); ++i)
			input_tuple[i] = py::cast(n.inputs[i].get(), py::return_value_policy::reference_internal, py::cast(&n));
		return input_tuple;
	})
	.def_property_readonly("hidden", [](const TNetworkDefinition& n){
		py::tuple hidden_tuple(n.hidden.size());
		for (size_t i = 0; i < n.hidden.size(); ++i)
			hidden_tuple[i] = py::cast(n.hidden[i].get(), py::return_value_policy::reference_internal, py::cast(&n));
		return hidden_tuple;
	})
	.def_property_readonly("outputs", [](const TNetworkDefinition& n){
		py::tuple output_tuple(n.outputs.size());
		for (size_t i = 0; i < n.outputs.size(); ++i)
			output_tuple[i] = py::cast(n.outputs[i].get(), py::return_value_policy::reference_internal, py::cast(&n));
		return output_tuple;
	});

	// --- Query ---
	py::class_<TQuery, TNode>(m, "Query")
    .def_property_readonly("networks", [](const TQuery& q){
		py::tuple network_tuple(q.networks.size());
		for (size_t i = 0; i < q.networks.size(); ++i)
			network_tuple[i] = py::cast(q.networks[i].get(), py::return_value_policy::reference_internal, py::cast(&q));
		return network_tuple;
	})
    .def_property_readonly("assertions", [](const TQuery& q){
		py::tuple assertion_tuple(q.assertions.size());
		for (size_t i = 0; i < q.assertions.size(); ++i)
			assertion_tuple[i] = py::cast(q.assertions[i].get(), py::return_value_policy::reference_internal, py::cast(&q));
		return assertion_tuple;
	});

	// --- API ---
	m.def("parse_vnnlib", [](const std::string& path) {
		return parse_query(path);
	},
	py::return_value_policy::move,
	py::arg("path"),
	R"pbdoc(
		Parse a VNNLib file and return a typed Query object.

		Parameters
		----------
		path : str
			Path to the VNNLib file to be parsed.

		Returns
		-------
		Query
			The parsed Query object representing the contents of the VNNLib file.

		Raises
		------
		VNNLibException
			If the file cannot be read, if there is an error during parsing, or if the specification is not well-formed.
	)pbdoc");
	
	m.def("parse_vnnlib_str", [](const std::string& content) {
		return parse_query_str(content);
	},
	py::return_value_policy::move,
	py::arg("content"),
	R"pbdoc(
		Parse a VNNLib string and return a typed Query object.

		Parameters
		----------
		content : str
			The VNNLib string to be parsed.

		Returns
		-------
		Query
			The parsed Query object representing the contents of the VNNLib string.

		Raises
		------
		VNNLibException
			If there is an error during parsing, or if the specification is not well-formed.
	)pbdoc");

	m.attr("__version__") = "0.2.0";
}

