from clang.cindex import Index, CursorKind, TypeKind
from collections import deque, defaultdict

import os

INDENT_SIZE = 3

fpath = os.path.dirname(os.path.abspath(__file__))
HEADER_FILE = f"{fpath}/../src/bisonParser/Absyn.h"

to_generate = []

# Start from top-level: struct Query_
index = Index.create()
tu = index.parse(HEADER_FILE, args=["-x", "c", "-std=c11", "-D_POSIX_C_SOURCE=200809L"])

for cursor in tu.cursor.get_children():
    if cursor.kind == CursorKind.STRUCT_DECL and cursor.is_definition():
        # Check if the struct name ends with an underscore
        if cursor.spelling.endswith("_"):  # e.g., Query_
            to_generate.append(cursor)


def generate_field(field_cursor, num_indent=0):
    """Generates a field declaration for a given field cursor."""
    field_name = field_cursor.spelling
    field_type = field_cursor.type
    canonical_type = field_type.get_canonical()

    ret_str = " " * num_indent * INDENT_SIZE

    # Detect char*
    if canonical_type.kind == TypeKind.POINTER and canonical_type.get_pointee().kind == TypeKind.CHAR_S:
        ret_str += f"std::string {field_name};"

    # Detect pointer to AST node
    elif canonical_type.kind == TypeKind.POINTER and canonical_type.get_pointee().kind == TypeKind.RECORD:
        ret_str += f"std::unique_ptr<{field_type.spelling}Wrapper> {field_name};"

    # Unhandled types
    else:
        raise ValueError(f"Unhandled field: {field_name} of type {canonical_type.spelling}")\
        
    return ret_str


def extract_struct_fields(struct_cursor, num_indent=0):
    """Extracts the fields from a struct, including nested unions and regular fields."""
    fields = []
    variant_names = []
    indent = " " * num_indent * INDENT_SIZE

    for field in struct_cursor.get_children():
        if field.kind == CursorKind.UNION_DECL and field.is_definition():
            decl = field.type.get_declaration()
            variant_body = []

            for child in decl.get_children():
                if child.kind == CursorKind.STRUCT_DECL and child.is_definition():
                    for field in child.get_children():
                        if field.kind == CursorKind.FIELD_DECL:
                            variant_body.append(generate_field(field, num_indent + 1))
                else:
                    variant_name = child.spelling
                    variant_code = [f"{indent}struct {variant_name} {{"] + variant_body + [f"{indent}}};"]
                    fields.append("\n".join(variant_code))
                    variant_body.clear()
                    variant_names.append(variant_name)

        elif field.kind == CursorKind.FIELD_DECL and field.is_definition():
            if field.type.get_named_type().kind == TypeKind.TYPEDEF:
                # Add plain fields as members outside the variant
                fields.append(generate_field(field, num_indent))

    return fields, variant_names


def generate_class(struct_cursor):
    """Generates a C++ wrapper class for a given struct cursor."""
    indent = " " * INDENT_SIZE

    struct_name = struct_cursor.spelling.rstrip('_')
    class_name = struct_name + "Wrapper"
    is_list_node = struct_name.startswith("List")
    struct_as_field = "_" + struct_name.lower()

    fields, variant_names = extract_struct_fields(struct_cursor, num_indent=2)
    has_variants = bool(variant_names)

    cpp_class = [
        f"{indent * 0}class {class_name} {{",
        f"{indent * 1}private:",
        f"{indent * 2}{struct_name} {struct_as_field};"
    ]

    cpp_class += fields

    if has_variants:
        cpp_class.append(
            f"{indent * 2}using WrapperVariant = std::variant<std::monostate, " + ", ".join(variant_names) + ">;"
        )
        cpp_class.append(f"{indent * 2}WrapperVariant wrapper_;")

    cpp_class.append("\n  public:")

    # Constructor
    init_line = f"{class_name}({struct_name} ptr) : {struct_as_field}(ptr)"
    if has_variants:
        init_line += ", wrapper_(std::monostate{})"
    init_line += " {}"
    cpp_class.append(f"{indent * 2}{init_line}\n")

    # to_string
    cpp_class += [
        f"{indent * 2}std::string to_string() const {{",
        f"{indent * 3}char* s = pp{struct_name}({struct_as_field}, 0);",
        f"{indent * 3}if (!s) return {{}};",
        f"{indent * 3}std::string result(s);",
        f"{indent * 3}free(s);",
        f"{indent * 3}return result;",
        f"{indent * 2}}}"
    ]

    # __str__
    cpp_class += [
        f"{indent * 2}std::string __str__() const {{",
        f"{indent * 3}return to_string();",
        f"{indent * 2}}}"
    ]

    # get variant
    if has_variants:
        cpp_class += [f"{indent * 2}WrapperVariant get_wrapper() const {{"]
        for variant_name in variant_names:
            cpp_class += [
                f"{indent * 3}if (std::holds_alternative<{variant_name}>(wrapper_))",
                f"{indent * 4}return *std::get_if<{variant_name}>(&wrapper_);"
            ]
        cpp_class += [
            f"{indent * 3}return std::monostate{{}};",
            f"{indent * 2}}}"
        ]

    # Delete the class
    cpp_class += [
        f"{indent * 2}~{class_name}() {{",
        f"{indent * 3}free_{struct_name}({struct_as_field});",
        f"{indent * 2}}}"
    ]

    cpp_class.append("};\n")
    return "\n".join(cpp_class)


# Generate the C++ wrapper classes
cpp_code = []
for struct_cursor in to_generate:
    print(f"Generating wrapper for {struct_cursor.spelling}...")
    cpp_code.append(generate_class(struct_cursor))

print("\n".join(cpp_code))
