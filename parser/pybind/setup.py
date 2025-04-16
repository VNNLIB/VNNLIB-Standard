from setuptools import setup, Extension
import pybind11
from pybind11.setup_helpers import Pybind11Extension, build_ext


ext_modules = [
    Pybind11Extension(
        "vnnlib",  # name of Python module
        ["bindings.cpp"],  # source files
        include_dirs=["../include", "../src/bisonParser"],
		library_dirs=["../bin/"],
		libraries=["VNNLib"],
        language="c++",
		extra_link_args=["-Wl,-rpath,$ORIGIN"]
    ),
]

setup (
    name="vnnlib",
    version="1.0",
    ext_modules=ext_modules,
    cmdclass={"build_ext": build_ext},
)