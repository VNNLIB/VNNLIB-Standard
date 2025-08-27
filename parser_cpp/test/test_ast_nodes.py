"""Simple script for traversing vnnlib AST nodes.
Usage: test_ast_nodes.py <vnnlib_file>"""

import sys
from vnnlib import parse_vnnlib as parse

def walk(n, d=0):
    print("  " * d + f"{type(n).__name__}: {n}")
    for c in n.children():
        walk(c, d + 1)

if __name__ == "__main__":
    q = parse(sys.argv[1])  # path to a .vnnlib file
    walk(q)