
bnfc --c -m -o parser/src/bisonParser VNNLib_LBNF.cf && make -C parser

sed -i '/#define PRINTER_HEADER/a\
\nextern char *buf_;\
' parser/src/bisonParser/Printer.h

cd parser/pybind

python generate_wrappers.py

python setup.py build_ext --inplace

