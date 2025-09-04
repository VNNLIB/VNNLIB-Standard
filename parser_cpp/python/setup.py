#!/usr/bin/env python3

from pybind11.setup_helpers import Pybind11Extension, build_ext
from setuptools import setup, Extension
import pybind11
import os
import glob

ext_modules = [
    Pybind11Extension(
        "vnnlib._core",
        sources=[
            "vnnlib/_core.cpp",
            "../cpp/src/VNNLib.cpp",
            "../cpp/src/TypeChecker.cpp",
            "../cpp/src/TypedAbsyn.cpp",
            "../cpp/src/TypedBuilder.cpp",
            "../cpp/src/LinearArithExpr.cpp",
        ] + glob.glob("../cpp/src/generated/*.C"),
        include_dirs=[
            pybind11.get_include(),
            "../cpp/include",
            "../cpp/include/util", 
            "../cpp/src/generated",
        ],
        language='c++',
        cxx_std=17,
        define_macros=[("VERSION_INFO", '"dev"')],
    ),
]

setup(
    name="vnnlib",
    version="0.0.1",
    description="Python bindings for VNNLib parsing and AST manipulation",
    long_description="",
    author="Allen Antony",
    author_email="allenantony2001@gmail.com",
    url="https://github.com/VNNLIB/VNNLIB-Standard",
    packages=["vnnlib"],
    ext_modules=ext_modules,
    cmdclass={"build_ext": build_ext},
    zip_safe=False,
    python_requires=">=3.7",
    install_requires=[
        "pybind11>=2.6.0",
    ],
    package_data={
        "vnnlib": ["*.so", "*.pyi", "py.typed"],
    }
)
