from clang.cindex import Index, CursorKind, TypeKind
from collections import deque, defaultdict

import os

INDENT_SIZE = 2

fpath = os.path.dirname(os.path.abspath(__file__))
HEADER_FILE = f"{fpath}/../src/bisonParser/Absyn.h"


def extract_fields(struct_cursor):
    """Extracts string and pointer fields from a given struct cursor."""
    string_fields = []
    pointer_fields = {}

    for field in struct_cursor.get_children():
        if field.kind == CursorKind.FIELD_DECL and field.is_definition():
            canonical_type = field.type.get_canonical()
            if canonical_type.kind == TypeKind.POINTER and canonical_type.get_pointee().kind == TypeKind.CHAR_S:
                string_fields.append(field.spelling) 
            elif canonical_type.kind == TypeKind.POINTER and canonical_type.get_pointee().kind == TypeKind.RECORD:
                pointer_fields[field.spelling] = field.type.spelling

    return string_fields, pointer_fields


def construct_subclass(struct, class_name, super_struct, super_class):
    """Constructs a subclass from a given struct, representing a variant of the base class."""
    indent = " " * INDENT_SIZE

    cpp_class = [
        f"{indent * 0}class {class_name} : public {super_class} {{",
    ]

    string_fields = []
    pointer_fields = {}

    if struct is not None:
        string_fields, pointer_fields = extract_fields(struct)

    # Public
    cpp_class += [f"{indent * 1}public:"]

    # Field declarations
    for field_name in string_fields:
        cpp_class += [f"{indent * 2}std::string {field_name};"]
    for field_name, field_type in pointer_fields.items():
        cpp_class += [f"{indent * 2}std::unique_ptr<{field_type}Wrapper> {field_name};"]

    # Constructor
    if struct is not None:
        constructor = [f"{indent * 2}{class_name}("]

        for field_name in string_fields:
            constructor += [f"{indent * 3}std::string _{field_name},"]
        for field_name, field_type in pointer_fields.items():
            constructor += [f"{indent * 3}std::unique_ptr<{field_type}Wrapper> _{field_name},"]

        constructor += [f"{indent * 3}{super_struct} {super_struct.lower()}_struct",
                        f"{indent * 2}): ",
                        f"{indent * 4}{super_class}({super_struct.lower()}_struct),"]

        for field_name in string_fields + list(pointer_fields.keys()):
            constructor += [f"{indent * 4}{field_name}(std::move(_{field_name})),"]
        constructor[-1] = constructor[-1].rstrip(",")
        constructor += [f"{indent * 2}{{}}"]
    else:
        constructor = [
            f"{indent * 2}{class_name}({super_struct} _{super_struct.lower()}) : {super_class}(_{super_struct.lower()}) {{}}"
        ]

    cpp_class += constructor + ["};\n"]
    return cpp_class


def construct_base_class(struct_name, class_name):
    """Constructs a base wrapper class for a given struct_name and class_name."""
    indent = " " * INDENT_SIZE
    struct_as_field = "_" + struct_name.lower()

    # Generate the top-level class
    cpp_class = [
        f"{indent * 0}class {class_name} {{",
        f"{indent * 1}protected:",
        f"{indent * 2}{struct_name} {struct_as_field};"
    ]

    # Constructor
    cpp_class += [
        f"{indent * 1}public:",
        f"{indent * 2}{class_name}({struct_name} ptr) : {struct_as_field}(ptr) {{}}",
    ]

    # To string
    cpp_class += [
        f"{indent * 2}std::string to_string() const {{",
        f"{indent * 3}bufReset();",
        f"{indent * 3}pp{struct_name}({struct_as_field}, 0);",
        f"{indent * 3}std::string result(buf_);",
        f"{indent * 3}return result;",
        f"{indent * 2}}}"
    ]

    # __str__
    cpp_class += [
        f"{indent * 2}std::string __str__() const {{",
        f"{indent * 3}return to_string();",
        f"{indent * 2}}}"
    ]

    # Destructor
    cpp_class += [
        f"{indent * 2}virtual ~{class_name}() {{",
        f"{indent * 3}free_{struct_name}({struct_as_field});",
        f"{indent * 2}}}"
    ]

    cpp_class += ["};\n"]
    return cpp_class


def add_includes():
    """Adds necessary includes for the generated code."""
    return [
        '#include <string>',
        '#include <stdexcept>',
        '#include <memory>',
        '#include "Absyn.h"',
        '#include "Printer.h"'
        '\n'
    ]


def construct_variant_generator(struct, 
                             string_fields, 
                             pointer_fields, 
                             class_name, 
                             path_to_field,
                             num_indent = 0):
    """A helper function that generates the code for recursively constructing a subclass and its fields."""
    indent = " " * INDENT_SIZE

    fun_code = []

    string_fields, pointer_fields = extract_fields(struct)
    for field_name in string_fields:
        fun_code += [
            f"{indent * num_indent}char* s = {path_to_field}{field_name};",
            f"{indent * num_indent}std::string {field_name} = s ? std::string(s) : std::string();",
        ]
    for field_name in pointer_fields:
        fun_code += [
            f"{indent * num_indent}auto {field_name} = generate({path_to_field}{field_name});",
        ]

    fun_code += [f"{indent * num_indent}return std::make_unique<{class_name}>("]

    for field_name in string_fields + list(pointer_fields.keys()):
        fun_code += [f"{indent * (num_indent + 1)}std::move({field_name}),"]

    fun_code += [
        f"{indent * (num_indent + 1)}ptr",
        f"{indent * num_indent});",
    ]
    return fun_code


def construct_generator(variants, 
                        variant_names, 
                        subclass_names, 
                        struct_cursor, 
                        class_name):
    """Generates a function that constructs and returns the appropriate subclass based on the variant."""
    indent = " " * INDENT_SIZE

    struct_name = struct_cursor.spelling.rstrip('_')

    fun_code = []
    fun_code += [
        f"{indent * 0}std::unique_ptr<{class_name}> generate({struct_name} ptr) {{"
    ]

    if struct_name.startswith("List"):
        subcls_name = struct_name.lstrip("List") + "List"       # Special case for list types
        string_fields, pointer_fields = extract_fields(struct_cursor)
        fun_code += construct_variant_generator(struct_cursor,
                                                string_fields,
                                                pointer_fields,
                                                subcls_name,
                                                f"ptr->",
                                                num_indent=1)
    elif variants:
        fun_code += [f"{indent * 1}switch (ptr->kind) {{"]  
        for i, variant in enumerate(variants):
            fun_code += [f"{indent * 2}case {i}: {{"]
            string_fields, pointer_fields = extract_fields(variant)
            fun_code += construct_variant_generator(variant, 
                                                    string_fields, 
                                                    pointer_fields, 
                                                    subclass_names[i],
                                                    f"ptr->u.{variant_names[i]}.",
                                                    num_indent=3)  
            fun_code += [
                f"{indent * 3}break;",
                f"{indent * 2}}}",
            ]
        fun_code += [
            f"{indent * 2}default: {{",
            f"{indent * 3}throw std::runtime_error(\"Unknown variant\");",
            f"{indent * 2}}}",
            f"{indent * 1}}}",
        ]
    
    fun_code += [
        f"{indent * 0}}}\n",
    ]

    return fun_code


def decode_struct(struct_cursor):
    """Generates a C++ wrapper class for a given struct cursor."""
    variants = [] # List of structs in the union (to be generated as subclasses)
    subclass_names = []
    variant_names = []

    # Traverse the fields of the struct
    for field in struct_cursor.get_children():
        if field.kind == CursorKind.UNION_DECL and field.is_definition(): # Extracting from field "u"
            decl = field.type.get_declaration()
            for child in decl.get_children():
                if child.kind == CursorKind.FIELD_DECL and child.is_definition():
                    variant_body = child.type.get_declaration()
                    variants.append(variant_body)
                    variant_names.append(child.spelling)

        elif field.kind == CursorKind.FIELD_DECL and field.is_definition():
            decl = field.type.get_declaration()
            if decl.kind == CursorKind.ENUM_DECL: # Extracting from field "kind"
                for child in decl.get_children():
                    if child.kind == CursorKind.ENUM_CONSTANT_DECL:
                        subclass_names.append(child.spelling.lstrip('is_')) # Remove the prefix "is_" from the enum constant

    cpp_code = []

    struct_name = struct_cursor.spelling.rstrip('_')
    class_name = f"{struct_name}Wrapper"
    cpp_code += construct_base_class(struct_name, class_name)

    # Generate an additional subclass for list types
    if struct_name.startswith("List"):
        subcls_name = struct_name[4:] + "List"
        cpp_code += construct_subclass(struct_cursor, subcls_name, struct_name, class_name)
    # Generate the subclass for each variant
    elif subclass_names:
        for i, subcls_name in enumerate(subclass_names):
            variant = variants[i] if variants else None
            cpp_code += construct_subclass(variant, subcls_name, struct_name, class_name)
    else:
        raise ValueError(f"Unexpected struct: {struct_name}")
    
    # Generate the function to create the appropriate subclass
    cpp_code += construct_generator(variants, 
                                    variant_names,
                                    subclass_names, 
                                    struct_cursor, 
                                    class_name)
    
    return cpp_code


if __name__ == "__main__":
    index = Index.create()
    tu = index.parse(HEADER_FILE, args=["-x", "c", "-std=c11", "-D_POSIX_C_SOURCE=200809L"])

    cpp_code = []
    cpp_code += add_includes()

    for cursor in tu.cursor.get_children():
        if cursor.kind == CursorKind.STRUCT_DECL and cursor.is_definition():
            # Check if the struct name ends with an underscore
            if cursor.spelling.endswith("_"):  # e.g., Query_
                cpp_code += decode_struct(cursor)

    output = "\n".join(cpp_code)

    output_file = os.path.join(fpath, "generated_wrapper.hpp")
    with open(output_file, "w") as f:
        f.write(output)
