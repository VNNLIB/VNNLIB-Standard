#ifndef SEMANTIC_CHECKER_H
#define SEMANTIC_CHECKER_H

#include <stdlib.h>
#include <stdarg.h> 
#include <string.h> 
#include <stdio.h>
#include "Absyn.h" 
#include "Util.h"

#define MAX_DIMENSIONS 10 // Maximum number of dimensions for a tensor


typedef enum {
    MultipleDeclaration,
    TypeMismatch,
    UndeclaredVariable,
    IndexOutOfBounds,
    TooManyIndices,
    NotEnoughIndices,
} ErrorCode;


// Structure to store semantic errors
typedef struct {
    char* message;         
    char* offendingSymbol; 
    char* hint;            
    ErrorCode errorCode;
    // TODO: Add line/number information if BNFC supports it in the future
} VNNLibError;


// Enum to distinguish variable kinds
typedef enum {
    SYM_INPUT,
    SYM_OUTPUT,
    SYM_INTERMEDIATE
} SymbolKind;


// Structure to store information about a declared variable
typedef struct SymbolInfo {
    char        *name;          // Pointer to the VariableName node
    ElementType type;           // Pointer to the ElementType node 
    int         numDimensions;  // Number of dimensions
    int        *shape;          // Array of dimensions
    SymbolKind  kind;           // Kind of variable (input, output, intermediate)
    struct SymbolInfo *next;    // Pointer to the next symbol in the linked list
} SymbolInfo;


// Structure to hold state during semantic checking
typedef struct SemanticContext {
    SymbolInfo *symbolTableHead;    // Head of the symbol linked list
    VNNLibError *errors;            // List of semantic errors
    int errorCapacity;              // Capacity of the error list
    int errorCount;                 // Counter for detected errors
} SemanticContext;


// Error reporting functions
#define ERR_INITIAL_CAPACITY 4  // Initial capacity for the error list

char *reportErrors(SemanticContext *ctx);
char *reportErrorsJSON(SemanticContext *ctx);


// Context Management
int initSemanticContext(SemanticContext *ctx);
void destroySemanticContext(SemanticContext *ctx);
SymbolInfo* addSymbol(SemanticContext *ctx, VariableName name, ElementType type, ListInt dims, SymbolKind kind);
SymbolInfo* findSymbol(SemanticContext *ctx, VariableName name);

// Error Management
void addError(SemanticContext *ctx, VNNLibError error);

// Checker functions
int checkQuery(Query p, SemanticContext *ctx);
int checkListNetworkDefinition(ListNetworkDefinition listnetworkdefinition, SemanticContext *ctx);
int checkNetworkDefinition(NetworkDefinition p, SemanticContext *ctx);
int checkListInputDefinition(ListInputDefinition listinputdefinition, SemanticContext *ctx);
int checkInputDefinition(InputDefinition p, SemanticContext *ctx);
int checkListHiddenDefinition(ListHiddenDefinition listintermediatedefinition, SemanticContext *ctx);
int checkHiddenDefinition(HiddenDefinition p, SemanticContext *ctx);
int checkListOutputDefinition(ListOutputDefinition listoutputdefinition, SemanticContext *ctx);
int checkOutputDefinition(OutputDefinition p, SemanticContext *ctx);
int checkElementType(ElementType p, SemanticContext *ctx);
int checkListProperty(ListProperty listproperty, SemanticContext *ctx);
int checkProperty(Property p, SemanticContext *ctx);
int checkBoolExpr(BoolExpr p, SemanticContext *ctx);
int checkListBoolExpr(ListBoolExpr listboolexpr, SemanticContext *ctx);
int checkArithExpr(ArithExpr p, SemanticContext *ctx);
int checkListArithExpr(ListArithExpr listarithexpr, SemanticContext *ctx);
int checkTensorElement(TensorElement p, SemanticContext *ctx);
int checkVariableName(VariableName p, SemanticContext *ctx);
int checkListInt(ListInt listint, SemanticContext *ctx, int *shape, int *numDimensions);

// Base types
int checkSDouble(SDouble p, SemanticContext *ctx);
int checkSInt(SInt p, SemanticContext *ctx);
int checkInt(Int p, SemanticContext *ctx);
int checkIdent(Ident i, SemanticContext *ctx);
int checkInteger(Integer i, SemanticContext *ctx);
int checkDouble(Double d, SemanticContext *ctx);
int checkChar(Char c, SemanticContext *ctx);
int checkString(String s, SemanticContext *ctx);

#endif 