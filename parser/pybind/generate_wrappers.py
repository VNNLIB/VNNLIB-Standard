from clang.cindex import Index, CursorKind, TypeKind

import os

fpath = os.path.dirname(os.path.abspath(__file__))
HEADER_FILE = f"{fpath}/../src/bisonParser/Absyn.h"

INDENT_SIZE = 2
TOP_LEVEL_CLASS = "Query"


def ind(n):
	"""Returns a string with n indents."""
	return " " * INDENT_SIZE * n


class Field:
	def __init__(self, name, type_str, is_string=False):
		self.name = name
		self.type_str = type_str
		self.is_string = is_string

	def declaration(self):
		# return f"std::string {self.name};" if self.is_string else f"std::unique_ptr<{self.type_str}Wrapper> {self.name};"
		if self.is_string:
			return f"std::string {self.name};"
		else:
			return f"std::unique_ptr<{self.type_str}Wrapper> {self.name};"
		
	
	@staticmethod
	def from_cursor(field):
		# Check if the field is a string
		canonical_type = field.type.get_canonical()
		if canonical_type.kind == TypeKind.POINTER and canonical_type.get_pointee().kind == TypeKind.CHAR_S:
			return Field(field.spelling, field.type.spelling, is_string=True)
		elif canonical_type.kind == TypeKind.POINTER and canonical_type.get_pointee().kind == TypeKind.RECORD:
			return Field(field.spelling, field.type.spelling)
		else:
			raise ValueError(f"Unsupported field type: {field.type.spelling}")
		
	
	@staticmethod
	def from_struct(struct):
		fields = []
		for field in struct.get_children():
			if field.kind == CursorKind.FIELD_DECL and field.is_definition():
				fields.append(Field.from_cursor(field))
		return fields
	

class Leaf:
	def __init__(self, class_name, base_class, base_struct):
		self.cpp_code = []
		self.name = class_name
		self.base_class = base_class
		self.base_struct = base_struct
		self.fields = []
		self.is_list = False

		self.construct_class()

	
	def construct_class(self):
		self.cpp_code = [
			f"{ind(0)}class {self.name} : public {self.base_class} {{",
			f"{ind(1)}public:",
			f"{ind(2)}{self.name}({self.base_struct} _{self.base_struct.lower()}) : {self.base_class}(_{self.base_struct.lower()}) {{}}"
		]
		self.cpp_code += ["};\n"]
		

class Node:
	def __init__(self, class_name, struct_cursor, base_struct, base_class):
		self.cpp_code = []
		self.name = class_name
		self.base_class = base_class
		self.base_struct = base_struct
		self.fields = Field.from_struct(struct_cursor)
		self.is_list = False

		self.construct_class()


	def construct_class(self):
		cpp_class = [
			f"{ind(0)}class {self.name} : public {self.base_class} {{",
		]
		
		# Public
		cpp_class += [f"{ind(1)}public:"]

		# Field declarations
		for field in self.fields:
			if field.is_string:
				cpp_class += [f"{ind(2)}std::string {field.name};"]
			else:
				cpp_class += [f"{ind(2)}std::unique_ptr<{field.type_str}Wrapper> {field.name};"]

		# Constructor
		constructor = [f"{ind(2)}{self.name}("]

		for field in self.fields:
			if field.is_string:
				constructor += [f"{ind(3)}std::string _{field.name},"]
			else:
				constructor += [f"{ind(3)}std::unique_ptr<{field.type_str}Wrapper> _{field.name},"]

		constructor += [f"{ind(3)}{self.base_struct} {self.base_struct.lower()}_struct",
						f"{ind(2)}): ",
						f"{ind(4)}{self.base_class}({self.base_struct.lower()}_struct),"]

		for field in self.fields:
			# E.g., name(std::move(_name)), kind(std::move(_kind)), ...
			constructor += [f"{ind(4)}{field.name}(std::move(_{field.name})),"]
		constructor[-1] = constructor[-1].rstrip(",")	 # Remove the last comma
		
		constructor += [f"{ind(2)}{{}}"] # End of constructor

		cpp_class += constructor + ["};\n"]
		self.cpp_code += cpp_class


class ListNode(Node):
	def __init__(self, class_name, struct_cursor, base_struct, base_class):
		super().__init__(class_name, struct_cursor, base_struct, base_class)
		self.is_list = True

		self.modify_class()
		self.construct_iterator()
	

	def construct_iterator(self):
		""" Constructs an iterator struct for the node """
		struct_code = []
		iterator_name = self.name + "Iterator"
		[node_field, next_field] = self.fields 

		if node_field.is_string:
			node_type = "std::string"
		else:
			node_type = f"{node_field.type_str}Wrapper"

		# Constructor for the iterator
		struct_code += [
			f"{ind(0)}struct {iterator_name} {{",
			f"{ind(1)}{self.name}* current_node;",
			f"{ind(1)}{iterator_name}({self.name}* start_node) : current_node(start_node) {{}}"
		]

		# operator* for dereferencing the iterator
		if node_field.is_string:
			struct_code += [f"{ind(1)}{node_type} operator*() const {{"]
		else:
			struct_code += [f"{ind(1)}{node_type}* operator*() const {{"]
		struct_code += [
			f"{ind(2)} if (!current_node) {{",
			f"{ind(3)}throw std::runtime_error(\"Dereferencing null list iterator\");",
			f"{ind(2)}}}",
		]
		if node_field.is_string:
			struct_code += [f"{ind(2)}return current_node->{node_field.name};"]
		else:
			struct_code += [f"{ind(2)}return current_node->{node_field.name}.get();"]
		struct_code += [f"{ind(1)}}}\n"]
	
		# operator++ for incrementing the iterator
		struct_code += [
			f"{ind(1)}{iterator_name}& operator++() {{",
			f"{ind(2)}if (current_node) {{",
			f"{ind(3)}{self.base_class}* next_list_wrapper = current_node->{next_field.name}.get();",
			f"{ind(3)}current_node = dynamic_cast<{self.name}*>(next_list_wrapper);",
			f"{ind(2)}}}",
			f"{ind(2)}return *this;",
			f"{ind(1)}}}\n"
		]

		# operator== for comparing iterators
		struct_code += [
			f"{ind(1)}bool operator==(const {iterator_name}& other) const {{",
			f"{ind(2)}return current_node == other.current_node;",
			f"{ind(1)}}}",
		]

		# operator!= for comparing iterators
		struct_code += [
			f"{ind(1)}bool operator!=(const {iterator_name}& other) const {{",
			f"{ind(2)}return current_node != other.current_node;",
			f"{ind(1)}}}"
		]

		struct_code += ["};\n"]
		self.cpp_code += struct_code

		self.cpp_code += [
			f"{ind(0)}inline {iterator_name} {self.name}::begin() {{return {iterator_name}(this);}}",
			f"{ind(0)}inline {iterator_name} {self.name}::end() {{return {iterator_name}(nullptr);}}\n"
		]

	
	def modify_class(self):
		"""Modifies the class to include the iterator."""
		iterator_name = self.name + "Iterator"
		self.cpp_code = self.cpp_code[:-1]  # Remove the last closing brace

		self.cpp_code += [
			f"{ind(2)}{iterator_name} begin();",
			f"{ind(2)}{iterator_name} end();",
		]

		self.cpp_code += ["};\n"]


class Wrapper:
	def __init__(self, struct):
		self.current_class_code = []
		self.subclass_code = []
		self.generator_code = []

		self.subcls_names = []
		self.variant_structs = {}
		self.subclasses = []

		self.struct = struct
		self.struct_name = struct.spelling.rstrip('_') # E.g., Query
		self.name = self.struct_name + "Wrapper" # E.g., QueryWrapper
		self.is_list = self.struct_name.startswith("List") # E.g., ListNetwork
		self.is_root = self.struct_name == TOP_LEVEL_CLASS # E.g., Query

		# Traverse the fields of the struct
		for field in struct.get_children():
			decl = field.type.get_declaration()

			# Extracting from field "name". E.g.,  std::string name;
			if field.kind == CursorKind.UNION_DECL and field.is_definition(): 
				for child in decl.get_children():
					if child.kind == CursorKind.FIELD_DECL and child.is_definition():
						self.variant_structs[child.spelling] = child.type.get_declaration()

			# Extracting from enum field "kind". E.g.,  enum { is_VNNLibQuery } kind;
			elif field.kind == CursorKind.FIELD_DECL and field.is_definition() and decl.kind == CursorKind.ENUM_DECL:
				for child in decl.get_children():
					if child.kind == CursorKind.ENUM_CONSTANT_DECL and child.is_definition():
						subcls_name = child.spelling.lstrip('is_') # Remove the prefix "is_" from the enum constant
						self.subcls_names.append(subcls_name)

		self.construct_class()
		self.construct_subclasses()
		self.construct_generator()


	def construct_class(self):
		"""Constructs a base wrapper class for a given struct_name and class_name."""
		struct_field = "_" + self.struct_name.lower()
		cpp_class = []

		# Generate the top-level class
		cpp_class = [
			f"{ind(0)}class {self.name} {{",
			f"{ind(1)}protected:",
			f"{ind(2)}{self.struct_name} {struct_field};"
		]

		# Constructor
		cpp_class += [
			f"{ind(1)}public:",
			f"{ind(2)}{self.name}({self.struct_name} ptr) : {struct_field}(ptr) {{}}",
		]

		# To string
		cpp_class += [
			f"{ind(2)}std::string to_string() const {{",
			f"{ind(3)}bufReset();",
			f"{ind(3)}pp{self.struct_name}({struct_field}, 0);",
			f"{ind(3)}std::string result(buf_);",
			f"{ind(3)}return result;",
			f"{ind(2)}}}"
		]

		cpp_class += [
			f"{ind(2)}{self.struct_name} get_struct() const {{",
			f"{ind(3)}return {struct_field};",
			f"{ind(2)}}}",
		]

		# Destructor
		cpp_class += [
			f"{ind(2)}virtual ~{self.name}() {{",
		]

		if self.is_root:	# Add a recursive destructor for the root class
			cpp_class += [
				f"{ind(3)}if ({struct_field}) {{",
				f"{ind(4)}free_{self.struct_name}({struct_field});",
				f"{ind(3)}}}",
			]

		cpp_class += [
			f"{ind(2)}}}"
		]
		cpp_class += ["};\n"]

		self.current_class_code += cpp_class

	
	def construct_subclasses(self):
		if self.is_list:
			subcls_name = self.struct_name[4:] + "List" # E.g., ListNetwork -> NetworkList
			subcls = ListNode(subcls_name, self.struct, self.struct_name, self.name)
			self.subclasses.append(subcls)
			self.subcls_names.append(subcls_name)

		else:
			for i in range(len(self.subcls_names)):
				variant_name = self.subcls_names[i].lower() + "_"

				if variant_name in self.variant_structs:
					subcls = Node(self.subcls_names[i], self.variant_structs[variant_name], self.struct_name, self.name)
				else:
					subcls = Leaf(self.subcls_names[i], self.name, self.struct_name)

				self.subclasses.append(subcls)
		
		for subclass in self.subclasses:
			self.subclass_code += subclass.cpp_code

	
	def construct_generator_for_subclass(self, subcls_name, fields, path_to_field, indent):
		fun_code = []

		s_n = 0
		for field in fields:
			if field.is_string:
				fun_code += [
					f"{ind(indent)}char* s{s_n} = {path_to_field}{field.name};",
					f"{ind(indent)}std::string {field.name} = s{s_n} ? std::string(s{s_n}) : std::string();",
				]
				s_n += 1
			else:
				fun_code += [
					f"{ind(indent)}auto {field.name} = {path_to_field}{field.name}? generate({path_to_field}{field.name}) : nullptr;",
				]

		fun_code += [f"{ind(indent)}return std::make_unique<{subcls_name}>("]

		for field in fields:
			fun_code += [f"{ind(indent + 1)}std::move({field.name}),"]

		fun_code += [
			f"{ind(indent + 1)}ptr",
			f"{ind(indent)});",
		]
		return fun_code
		
	
	def construct_generator(self):
		"""Constructs a generator function for the class."""
		fun_code = []
		fun_code += [
			f"{ind(0)}std::unique_ptr<{self.name}> generate({self.struct_name} ptr) {{",
			f"{ind(1)}if (!ptr) return nullptr;"
		]

		if self.is_list:
			fields = Field.from_struct(self.struct)
			subcls_name = self.subcls_names[0]
			fun_code += self.construct_generator_for_subclass(subcls_name, fields, "ptr->", indent=1)

		elif self.subcls_names:
			fun_code += [f"{ind(1)}switch (ptr->kind) {{"]  
			for i in range(len(self.subcls_names)):
				fun_code += [f"{ind(2)}case {i}: {{"]
				fields = self.subclasses[i].fields

				variant_name = self.subcls_names[i].lower() + "_"
				path_to_field = ""
				if variant_name in self.variant_structs:
					path_to_field = f"ptr->u.{variant_name}."

				fun_code += self.construct_generator_for_subclass(self.subcls_names[i], fields, path_to_field, indent=3)
				fun_code += [
					f"{ind(2)}}}",
				]
			fun_code += [
				f"{ind(2)}default: {{",
				f"{ind(3)}throw std::runtime_error(\"Unknown variant\");",
				f"{ind(2)}}}",
				f"{ind(1)}}}",
			]
		
		fun_code += [
			f"{ind(0)}}}\n",
		]
		self.generator_code += fun_code


class CodeWriter:
	def __init__(self, clang_header_path):
		index = Index.create()
		self.tu = index.parse(clang_header_path, args=["-x", "c", "-std=c11", "-D_POSIX_C_SOURCE=200809L"])
		self.clang_header_path = clang_header_path
		self.base_classes = []

		self.construct_cpp_classes()


	def construct_cpp_classes(self):
		for cursor in self.tu.cursor.get_children():
			if cursor.kind == CursorKind.STRUCT_DECL and cursor.is_definition() and cursor.spelling.endswith("_"):
				base_class = Wrapper(cursor)
				self.base_classes.append(base_class)


	def write_code(self, output_path):
		lines = ["#ifndef VNNLIBWRAPPERS_HPP", "#define VNNLIBWRAPPERS_HPP"]
		lines += [
			'#include <string>',
			'#include <stdexcept>',
			'#include <memory>',
			'#include "Absyn.h"',
			'#include "Printer.h"'
			'\n'
		]

		# Write forward declarations of the classes
		for cls in self.base_classes:
			lines += [f"class {cls.name};"]
			subcls_decls = ""
			line_count = 1

			for subclass in cls.subclasses:
				subcls_decls += f"class {subclass.name}; "
				line_count += 1

				if line_count % 5 == 0:
					subcls_decls += "\n"

				if subclass.is_list:
					subcls_decls += f"\nstruct {subclass.name}Iterator; "
					line_count += 1

			lines += [subcls_decls]
		
		lines += ["\n"]

		# Write forward declarations of the generate functions
		for cls in self.base_classes:
			lines += [f"std::unique_ptr<{cls.name}> generate(struct {cls.struct_name}_ *ptr);"]
				
		lines += ["\n"]

		# Write the constructed classes to the file
		for cls in self.base_classes:
			lines += cls.current_class_code
		
		for cls in self.base_classes:
			lines += cls.subclass_code

		for cls in self.base_classes:
			lines += cls.generator_code

		lines += ["#endif // VNNLIBWRAPPERS_HPP"]

		with open(output_path, "w") as f:
			f.write("\n".join(lines))


if __name__ == "__main__":
	# Create the CodeWriter instance
	output_path = os.path.join(os.path.dirname(__file__), "VNNLIBWrappers.hpp")
	code_writer = CodeWriter(HEADER_FILE)

	# Write the constructed code to a file
	code_writer.write_code(output_path)