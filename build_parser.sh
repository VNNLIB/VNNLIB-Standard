
# Remove old parser directory if it exists
echo "Cleaning up old parser directory..."

if [ -d "parser/src/bisonParser" ]; then
    rm -rf parser/src/bisonParser
fi

cd parser/pybind
python setup.py clean --all
rm vnnlib/*.so
cd ../..

# Build the BNFC parser and make the C library
echo "Building BNFC parser..."

bnfc --c -m -o parser/src/bisonParser syntax.cf 

# make the C parser and terminate if it fails
echo "Building C parser..."

make clean -C parser
make -C parser || { echo "Make failed"; exit 1; }

sed -i '/#define PRINTER_HEADER/a\
\nextern char *buf_;\
' parser/src/bisonParser/Printer.h

# Generate the Python library
echo "Building Python parser..."

cd parser/pybind
python generate_wrappers.py

python -m pip install -e . --no-deps

printf '%s\n' 'from ._core import *' > vnnlib/__init__.pyi
pybind11-stubgen vnnlib._core -o .
touch vnnlib/py.typed

pip install -e . --upgrade --no-deps
cd ../../

