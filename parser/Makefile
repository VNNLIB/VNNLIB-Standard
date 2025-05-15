CC = gcc
CFLAGS = -Wall -Wextra -g -fPIC -Wno-unused-parameter
BISON_OPTS = -t -psyntax_ -d
FLEX_OPTS = -Psyntax_

SRC_DIR = src
OBJ_DIR = build
BIN_DIR = bin
PYBIND11_DIR = pybind

# Source files
SRCS = $(wildcard $(SRC_DIR)/*.c)

BISON_SRCS = $(SRC_DIR)/bisonParser/Absyn.c \
			 $(SRC_DIR)/bisonParser/Parser.c \
			 $(SRC_DIR)/bisonParser/Lexer.c \
			 $(SRC_DIR)/bisonParser/Printer.c \
			 $(SRC_DIR)/bisonParser/Buffer.c

OBJS = $(patsubst $(SRC_DIR)/%.c, $(OBJ_DIR)/%.o, $(SRCS))
OBJS += $(patsubst $(SRC_DIR)/bisonParser/%.c, $(OBJ_DIR)/bisonParser/%.o, $(BISON_SRCS))

# Executable name
TARGET_EXEC = $(BIN_DIR)/VNNLibParser
TARGET_LIB = $(BIN_DIR)/libVNNLib.so

# Includes
INCLUDES = -I$(SRC_DIR)/bisonParser -I$(SRC_DIR)/../include

# Libraries
LDFLAGS = -lm

all: $(TARGET_EXEC) $(TARGET_LIB)

# Build the shared library
$(TARGET_LIB): $(OBJS) | $(BIN_DIR)
	$(CC) -shared -o $@ $^
	cp $(TARGET_LIB) $(PYBIND11_DIR)
	

# Link final executable
$(TARGET_EXEC): $(OBJS) | $(BIN_DIR)
	$(CC) $(CFLAGS) $(INCLUDES) -o $@ $^

# Compile src object files
$(OBJ_DIR)/%.o: $(SRC_DIR)/%.c | $(OBJ_DIR)
	$(CC) $(CFLAGS) $(INCLUDES) -c $< -o $@

# Compile bisonParser object files
$(OBJ_DIR)/bisonParser/%.o: $(SRC_DIR)/bisonParser/%.c | $(OBJ_DIR)/bisonParser
	$(CC) $(CFLAGS) $(INCLUDES) -c $< -o $@

$(OBJ_DIR):
	mkdir -p $(OBJ_DIR)

$(OBJ_DIR)/bisonParser:
	mkdir -p $(OBJ_DIR)/bisonParser

$(BIN_DIR):
	mkdir -p $(BIN_DIR)

# Generate parser and lexer from BNF
$(SRC_DIR)/bisonParser/Parser.c $(SRC_DIR)/bisonParser/Bison.h: 
	cd $(SRC_DIR)/bisonParser && \
	bison $(BISON_OPTS) syntax.y -o Parser.c && \
	cd ../..

$(SRC_DIR)/bisonParser/Lexer.c:
	cd $(SRC_DIR)/bisonParser && \
	flex $(FLEX_OPTS) -o Lexer.c syntax.l && \
	cd ../..

clean:
	rm -f $(OBJS) $(TARGET_EXEC)

.PHONY: all clean