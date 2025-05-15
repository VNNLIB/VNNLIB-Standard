
# Remove old parser directory if it exists

if [ -d "parser/src/bisonParser" ]; then
    rm -rf parser/src/bisonParser
fi

cd parser/pybind
python setup.py clean --all
cd ../..

# Build the BNFC parser and make the C library
bnfc --c -m -o parser/src/bisonParser syntax.cf 

# make the C parser and terminate if it fails
make -C parser || { echo "Make failed"; exit 1; }

sed -i '/#define PRINTER_HEADER/a\
\nextern char *buf_;\
' parser/src/bisonParser/Printer.h

# Generate the Python library
cd parser/pybind
python generate_wrappers.py
python setup.py build_ext --inplace
cd ../../

