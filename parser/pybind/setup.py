from setuptools import setup
from pathlib import Path
from pybind11.setup_helpers import Pybind11Extension, build_ext

PKG_DIR = Path("vnnlib")
CORE_CPP = PKG_DIR / "_core.cpp"
SHARED_SO = PKG_DIR / "libVNNLib.so"
VNNLIB_INCLUDE = PKG_DIR / ".." / ".." / "include"
BISON_INCLUDE = PKG_DIR / ".." / ".." / "src" / "bisonParser"

ext_modules = [
	Pybind11Extension(
		name="vnnlib._core",  
		sources=[CORE_CPP.as_posix()],  # source files
		include_dirs=[
			VNNLIB_INCLUDE.as_posix(),
			BISON_INCLUDE.as_posix()
		],
		library_dirs=[PKG_DIR.as_posix()],
		libraries=["VNNLib"],
		language="c++",
		extra_link_args=["-Wl,-rpath,$ORIGIN"]
	),
]

setup (
	name="vnnlib",
	version="0.1.0",
	packages=["vnnlib"],
	include_package_data=True,
	package_data={"vnnlib": ["*.so", "*.pyi", ".typed"]},
	ext_modules=ext_modules,
	zip_safe=False,
	cmdclass={"build_ext": build_ext},
)