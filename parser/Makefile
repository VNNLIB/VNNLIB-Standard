CC = gcc
CFLAGS = -Wall -Wextra -g
BISON_OPTS = -t -pvnn_lib_lbnf_ -d
FLEX_OPTS = -Pvnn_lib_lbnf_

SRC_DIR = src
OBJ_DIR = build
BIN_DIR = bin

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
TARGET = $(BIN_DIR)/ExtendedParser

# Includes
INCLUDES = -I $(SRC_DIR)/bisonParser

# Libraries
LDFLAGS = -lm

all: $(TARGET)

# Link final executable
$(TARGET): $(OBJS) | $(BIN_DIR)
	$(CC) $(CFLAGS) $(INCLUDES) -o $@ $^ $(LIBS) 

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
	bison $(BISON_OPTS) VNNLib_LBNF.y -o Parser.c && \
	cd ../..

$(SRC_DIR)/bisonParser/Lexer.c:
	cd $(SRC_DIR)/bisonParser && \
	flex $(FLEX_OPTS) -o Lexer.c VNNLib_LBNF.l && \
	cd ../..

clean:
	rm -f $(OBJS) $(TARGET)

.PHONY: all clean