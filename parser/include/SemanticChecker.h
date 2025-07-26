#ifndef SEMANTIC_CHECKER_H
#define SEMANTIC_CHECKER_H

#include <stdlib.h>
#include <stdarg.h> 
#include <string.h> 
#include <stdio.h>
#include <stdbool.h>
#include "Absyn.h" 
#include "Util.h"
#include "hashmap.h"

#define MAX_DIMENSIONS 10 // Maximum number of dimensions for a tensor


typedef enum {
    MultipleDeclaration,
    TypeMismatch,
    UndeclaredVariable,
    IndexOutOfBounds,
    TooManyIndices,
    NotEnoughIndices,
    UnexpectedOnnxName
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
    SYM_HIDDEN
} SymbolKind;

typedef enum { 
    Real, 
    F16, 
    F32, 
    F64, 
    BF16, 
    F8E4M3FN, 
    F8E5M2, 
    F8E4M3FNUZ, 
    F8E5M2FNUZ, 
    F4E2M1, 
    I8, 
    I16, 
    I32, 
    I64, 
    U8, 
    U16, 
    U32, 
    U64, 
    C64, 
    C128, 
    Bool, 
    Str, 
    Undefined,
    FloatConstant,
    NegIntConstant,
    PosIntConstant
} ElementTypeKind;

#define UNDEFINED_ELEMENT_TYPE Undefined


// Structure to store information about a declared variable
typedef struct SymbolInfo {
    char        *name;          // Pointer to the VariableName node
    char        *onnxName;      // Optional ONNX name for the variable
    ElementType type;           // Pointer to the ElementType node 
    int         numDimensions;  
    int        *shape;         
    SymbolKind  kind;           // Kind of variable (input, output, intermediate)
} SymbolInfo;

// Structure to hold state during semantic checking
typedef struct SemanticContext {
    struct hashmap *symbolMap;                   

    VNNLibError *errors;           
    int errorCapacity;              
    int errorCount;  

    ElementTypeKind currentDataType;        // Current data type being checked
    char *lastScannedVariable;       // Used to track the last scanned variable for error reporting
} SemanticContext;


// Error reporting functions
#define ERR_INITIAL_CAPACITY 4  // Initial capacity for the error list

char *reportErrors(SemanticContext *ctx);
char *reportErrorsJSON(SemanticContext *ctx);


// Context Management
int initSemanticContext(SemanticContext *ctx);
void destroySemanticContext(SemanticContext *ctx);
SymbolInfo* addSymbol(SemanticContext *ctx, VariableName name, ElementType type, ListInt dims, SymbolKind kind, String onnxName);
const SymbolInfo* findSymbol(SemanticContext *ctx, VariableName name);

// Error Management
void addError(SemanticContext *ctx, VNNLibError error);

// Checker functions
int checkQuery(Query p, SemanticContext *ctx);
int checkListNetworkDefinition(ListNetworkDefinition listnetworkdefinition, SemanticContext *ctx);
int checkNetworkDefinition(NetworkDefinition p, SemanticContext *ctx);
int checkListInputDefinition(ListInputDefinition listinputdefinition, int *usesOnnxNames, SemanticContext *ctx);
int checkInputDefinition(InputDefinition p, SemanticContext *ctx);
int checkListHiddenDefinition(ListHiddenDefinition listintermediatedefinition, SemanticContext *ctx);
int checkHiddenDefinition(HiddenDefinition p, SemanticContext *ctx);
int checkListOutputDefinition(ListOutputDefinition listoutputdefinition, int *usesOnnxNames, SemanticContext *ctx);
int checkOutputDefinition(OutputDefinition p, SemanticContext *ctx);
int checkElementType(ElementType p, SemanticContext *ctx);
int checkListAssertion(ListAssertion listassertion, SemanticContext *ctx);
int checkAssertion(Assertion p, SemanticContext *ctx);
int checkBoolExpr(BoolExpr p, SemanticContext *ctx);
int checkListBoolExpr(ListBoolExpr listboolexpr, SemanticContext *ctx);
int checkArithExpr(ArithExpr p, SemanticContext *ctx);
int checkListArithExpr(ListArithExpr listarithexpr, SemanticContext *ctx);
int checkTensorElement(VariableName p, ListInt dims, SemanticContext *ctx);
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