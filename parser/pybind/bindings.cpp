#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include "VNNLib.h"
#include "Absyn.h"
#include "QueryWrapper.hpp"

namespace py = pybind11;

PYBIND11_MODULE(vnnlib, m) {
    py::class_<QueryWrapper>(m, "Query")
        .def("to_string", &QueryWrapper::to_string)
        .def("__str__", &QueryWrapper::to_string);

    m.def("parse_vnnlib", [](const std::string& path) {
        Query q = parse_vnnlib(path.c_str());
        if (!q) {
            throw std::runtime_error("Failed to parse VNNLib file.");
        }
        return std::make_unique<QueryWrapper>(q);
    });

    m.def("check_query", [](const QueryWrapper& wrapper, bool json) {
        char* res = check_query(wrapper.get(), json ? 1 : 0);
        if (res != nullptr) {
            std::string result(res);
            free(res);
            return result;
        }
        return std::string();
    });
}