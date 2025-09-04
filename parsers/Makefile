CXX = g++
CXXFLAGS = -Wall -Wextra -g -fPIC -std=c++17 -Wno-unused-parameter -Wno-unused-function
BISON_OPTS = -t -psyntax_ -d
FLEX_OPTS = -Psyntax_

CPP_DIR = cpp
SRC_DIR = $(CPP_DIR)/src
GENERATED_DIR = $(SRC_DIR)/generated
OBJ_DIR = $(CPP_DIR)/build
BIN_DIR = $(CPP_DIR)/bin
INCLUDE_DIR = $(CPP_DIR)/include

# Source files
MAIN_SRCS = $(SRC_DIR)/VNNLib.cpp $(SRC_DIR)/TypeChecker.cpp $(SRC_DIR)/TypedAbsyn.cpp $(SRC_DIR)/TypedBuilder.cpp $(SRC_DIR)/LinearArithExpr.cpp
PARSER_MAIN = $(SRC_DIR)/VNNLibParser.cpp

# Generated source files (need to be created first)
GENERATED_SRCS = $(GENERATED_DIR)/Absyn.C \
                 $(GENERATED_DIR)/Parser.C \
                 $(GENERATED_DIR)/Lexer.C \
                 $(GENERATED_DIR)/Printer.C \
                 $(GENERATED_DIR)/Buffer.C

# Object files
MAIN_OBJS = $(patsubst $(SRC_DIR)/%.cpp, $(OBJ_DIR)/%.o, $(MAIN_SRCS))
PARSER_MAIN_OBJ = $(patsubst $(SRC_DIR)/%.cpp, $(OBJ_DIR)/%.o, $(PARSER_MAIN))
GENERATED_OBJS = $(patsubst $(GENERATED_DIR)/%.C, $(OBJ_DIR)/generated/%.o, $(GENERATED_SRCS))

ALL_LIB_OBJS = $(MAIN_OBJS) $(GENERATED_OBJS)

# Executable and library names
TARGET_EXEC = $(BIN_DIR)/VNNLibParser
TARGET_LIB = $(BIN_DIR)/libVNNLib.so

# Includes
INCLUDES = -I$(GENERATED_DIR) -I$(INCLUDE_DIR) -I$(INCLUDE_DIR)/util

# Libraries
LDFLAGS = -Wl,--no-undefined
LDLIBS = -lm

.PHONY: all clean generated

all: generated $(TARGET_EXEC) $(TARGET_LIB)

# Generate parser files first
generated: $(GENERATED_DIR)/Parser.C $(GENERATED_DIR)/Lexer.C

# Build the shared library
$(TARGET_LIB): $(ALL_LIB_OBJS) | $(BIN_DIR)
	$(CXX) -shared -o $@ $^ $(LDFLAGS) $(LDLIBS)

# Link final executable  
$(TARGET_EXEC): $(ALL_LIB_OBJS) $(PARSER_MAIN_OBJ) | $(BIN_DIR)
	$(CXX) $(CXXFLAGS) $(INCLUDES) -o $@ $^ $(LDFLAGS) $(LDLIBS)

# Compile main source object files
$(OBJ_DIR)/%.o: $(SRC_DIR)/%.cpp | $(OBJ_DIR)
	$(CXX) $(CXXFLAGS) $(INCLUDES) -c $< -o $@

# Compile generated object files
$(OBJ_DIR)/generated/%.o: $(GENERATED_DIR)/%.C | $(OBJ_DIR)/generated
	$(CXX) $(CXXFLAGS) $(INCLUDES) -Wno-sign-conversion -c $< -o $@

# Create directories
$(OBJ_DIR):
	mkdir -p $(OBJ_DIR)

$(OBJ_DIR)/generated:
	mkdir -p $(OBJ_DIR)/generated

$(BIN_DIR):
	mkdir -p $(BIN_DIR)

# Generate parser and lexer from BNF
$(GENERATED_DIR)/Parser.C $(GENERATED_DIR)/Bison.H: $(GENERATED_DIR)/syntax.y
	cd $(GENERATED_DIR) && \
	bison $(BISON_OPTS) syntax.y -o Parser.C

$(GENERATED_DIR)/Lexer.C: $(GENERATED_DIR)/syntax.l $(GENERATED_DIR)/Bison.H
	cd $(GENERATED_DIR) && \
	flex $(FLEX_OPTS) -oLexer.C syntax.l

clean:
	rm -rf $(OBJ_DIR) $(BIN_DIR)
	cd $(GENERATED_DIR) && rm -f Parser.C Lexer.C Bison.H

distclean: clean
	cd $(GENERATED_DIR) && make distclean

.PHONY: all clean distclean generated
