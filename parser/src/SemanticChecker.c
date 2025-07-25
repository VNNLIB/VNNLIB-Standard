/*** Semantic Error Checking using Visitor Traversal. ***/

#include "SemanticChecker.h"


// --- Error Reporting ---

// Helper to intitialise the error list
int initErrorList(SemanticContext *ctx) {
    ctx->errors = malloc(ERR_INITIAL_CAPACITY * sizeof(VNNLibError));
    if (!ctx->errors) {
        perror("Failed to allocate memory for error list");
        return 1;
    }
    ctx->errorCount = 0;
    ctx->errorCapacity = ERR_INITIAL_CAPACITY;
    return 0;
}


// Add an error to the list
void addError(SemanticContext *ctx, VNNLibError error) {
    int errorCount = ctx->errorCount;
    int errorCapacity = ctx->errorCapacity;

    if (errorCount >= errorCapacity) {
        size_t new_capacity = errorCapacity * 2;
        VNNLibError* new_errors = realloc(ctx->errors, new_capacity * sizeof(VNNLibError));
        if (!new_errors) {
            perror("Failed to reallocate memory for error list");
            return;
        }
        ctx->errors = new_errors;
        ctx->errorCapacity = new_capacity;
    }

    // Create a deep copy of the error
    VNNLibError copy = {
        .message = strdup_safe(error.message),
        .offendingSymbol = strdup_safe(error.offendingSymbol),
        .hint = strdup_safe(error.hint),
        .errorCode = error.errorCode
    };

    ctx->errors[ctx->errorCount] = copy;
    ctx->errorCount++;
}


// Helper to free the error list
void freeErrorList(SemanticContext *ctx) {
    for (int i = 0; i < ctx->errorCount; i++) {
        free_safe(ctx->errors[i].message);
        free_safe(ctx->errors[i].offendingSymbol);
        free_safe(ctx->errors[i].hint);
    }
    free_safe(ctx->errors);
    ctx->errors = NULL;
    ctx->errorCount = 0;
    ctx->errorCapacity = 0;
}


// Basic error reporting to stderr
void reportError(SemanticContext *ctx, const char *format, ...) {
    if (ctx) {
        fprintf(stderr, "Semantic Error: ");
        va_list args;
        va_start(args, format);
        vfprintf(stderr, format, args);
        va_end(args);
        fprintf(stderr, "\n");
    } else {
        fprintf(stderr, "Semantic Error: Context unavailable. Message: %s\n", format);
    }
}


// Helper to convert error codes to strings
const char* errorCodeToString(ErrorCode code) {
    switch (code) {
        case MultipleDeclaration: return "MultipleDeclaration";
        case TypeMismatch: return "TypeMismatch";
        case UndeclaredVariable: return "UndeclaredVariable";
        case IndexOutOfBounds: return "IndexOutOfBounds";
        case TooManyIndices: return "TooManyIndices";
        case NotEnoughIndices: return "NotEnoughIndices";
        default: return "UnknownErrorCode";
    }
}


// Helper to return errors as a string in a human-readable format
char *reportErrors(SemanticContext *ctx) {
    size_t size = 1024;
    size_t used = 0;
    char *buffer = malloc(size);
    if (!buffer) {
        perror("Failed to allocate memory for error report");
        return NULL;
    }
    buffer[0] = '\0';

    if (ctx && ctx->errorCount > 0) {
        for (int i = 0; i < ctx->errorCount; i++) {
            VNNLibError e = ctx->errors[i];
            buffer = append_str(buffer, &size, &used, 
                "[%s] %s (symbol: %s)\nHint: %s\n", 
                errorCodeToString(e.errorCode),
                e.message, 
                e.offendingSymbol, 
                e.hint);

            buffer = append_str(buffer, &size, &used, "\n");

            if (!buffer) {
                fprintf(stderr, "Error: Buffer overflow while reporting errors.\n");
                return NULL;
            }
        }
    }

    return buffer;
}


// Helper to return errors as a JSON string
char *reportErrorsJSON(SemanticContext *ctx) {
    size_t size = 1024;
    size_t used = 0;
    char *buffer = malloc(size);
    if (!buffer) {
        perror("Failed to allocate memory for JSON error report");
        return NULL;
    }
    buffer[0] = '\0';
    buffer = append_str(buffer, &size, &used, "{\n  \"errors\": [\n");


    if (ctx && ctx->errorCount > 0) {
        for (int i = 0; i < ctx->errorCount; i++) {
            VNNLibError e = ctx->errors[i];
            buffer = append_str(buffer, &size, &used,
                "    {\n"
                "      \"message\": \"%s\",\n"
                "      \"offendingSymbol\": \"%s\",\n"
                "      \"hint\": \"%s\",\n"
                "      \"errorCode\": \"%s\"\n"
                "    }",
                e.message,
                e.offendingSymbol,
                e.hint,
                errorCodeToString(e.errorCode));

            if (i < ctx->errorCount - 1) {
                buffer = append_str(buffer, &size, &used, ",");
            }
            buffer = append_str(buffer, &size, &used, "\n");

            if (buffer == NULL) {
                fprintf(stderr, "Error: Buffer overflow while reporting errors.\n");
                free(buffer);
                return NULL;
            }
        }
    }

    buffer = append_str(buffer, &size, &used, "  ]\n}\n");
    return buffer;
}


// --- Semantic Context Initialization and Cleanup ---

int symbol_compare(const void *a, const void *b, void *udata) {
    const SymbolInfo *symA = (const SymbolInfo *)a;
    const SymbolInfo *symB = (const SymbolInfo *)b;
    return strcmp(symA->name, symB->name);
}


uint64_t symbol_hash(const void *item, uint64_t seed0, uint64_t seed1) {
    const SymbolInfo *sym = (const SymbolInfo *)item;
    return hashmap_sip(sym->name, strlen(sym->name), seed0, seed1);
}


// Helper to free symbol info (does not free nodes from original AST)
void freeSymbolInfo(void *info) {
    if (!info) return;
    SymbolInfo *symbol = (SymbolInfo *)info;
    free_safe(symbol->shape);
}


// Add symbol to table
// Returns the added symbol or NULL if an error occurred
SymbolInfo* addSymbol(SemanticContext *ctx, VariableName name, ElementType type, ListInt listInt, SymbolKind kind, char* onnxName) {
    SymbolInfo lookup_key = { .name = name };
    if (hashmap_get(ctx->symbolMap, &lookup_key) != NULL) {
        addError(ctx, (VNNLibError) {
            .message = "Duplicate variable declaration",
            .offendingSymbol = name,
            .hint = "Variable names must be unique within the VNNLib file.",
            .errorCode = MultipleDeclaration
        });
        return NULL;
    }

    SymbolInfo newSymbol;
    int *symbolShape = malloc(sizeof(int) * MAX_DIMENSIONS);
    if (!symbolShape) {
        perror("Failed to allocate memory for symbol shape");
        return NULL;
    }

    int numDimensions = 0;
    if (listInt && checkListInt(listInt, ctx, symbolShape, &numDimensions) != 0) {
        free(symbolShape); 
        return NULL;
    }
    
    int* finalShape = realloc(symbolShape, sizeof(int) * numDimensions);
    if (numDimensions > 0 && !finalShape) {
        perror("Failed to reallocate memory for symbol shape");
        free(symbolShape); 
        return NULL;
    }

    newSymbol.name = name; 
    newSymbol.onnxName = onnxName; 
    newSymbol.type = type;
    newSymbol.numDimensions = numDimensions;
    newSymbol.shape = finalShape;
    newSymbol.kind = kind;

    hashmap_set(ctx->symbolMap, &newSymbol);
    if (hashmap_oom(ctx->symbolMap)) {
        fprintf(stderr, "Checker Error: Out of memory while adding symbol '%s'.\n", name);
        free(finalShape);
        return NULL;
    }

    return (SymbolInfo*)hashmap_get(ctx->symbolMap, &lookup_key);
}


// Find symbol by name
const SymbolInfo* findSymbol(SemanticContext *ctx, VariableName name) {
    SymbolInfo lookup_key = {.name = name};
    return hashmap_get(ctx->symbolMap, &lookup_key);
}


// Initialize the semantic context
int initSemanticContext(SemanticContext *ctx) {
    if (!ctx) {
        fprintf(stderr, "Checker Error: Semantic context provided is NULL.\n");
        return 1;
    }
    ctx->symbolMap = hashmap_new(sizeof(SymbolInfo), 0, 0, 0,
        symbol_hash, symbol_compare, freeSymbolInfo, NULL);
    ctx->errorCount = 0;
    return initErrorList(ctx);
}


// Free all symbols in the context
void destroySemanticContext(SemanticContext *ctx) {
    if (!ctx) return;
    hashmap_free((ctx->symbolMap));
    ctx->errorCount = 0;
    freeErrorList(ctx);
}


// ----------------- Recursive Traversal Functions -----------------

int checkListInt(ListInt p, SemanticContext *ctx, int *symbolShape, int *numDimensions)
{
    if (!p) return 0;
    int err = 0; 
    while(p != 0 && err == 0)
    {
        err |= checkInt(p->int_, ctx);
        if (err) {
            fprintf(stderr, "Checker Error: Unexpected failure in checkInt within ListInt.\n");
            return 1;
        }
        if (*numDimensions >= MAX_DIMENSIONS) {
            fprintf(stderr, "Checker Error: Too many dimensions in ListInt, exceeds MAX_DIMENSIONS.\n");
            return 1;
        }

        symbolShape[*numDimensions] = strtol(p->int_, NULL, 10);
        p = p->listint_;
        (*numDimensions)++;
    }
    return err;
}


int checkArithExpr(ArithExpr p, SemanticContext *ctx)
{
    if (!p) {
        fprintf(stderr, "Checker Error: ArithExpr node is NULL.\n");
        return 1;
    }
    int err = 0;
    switch(p->kind)
    {
        case is_VarExpr:
            err |= checkTensorElement(p->u.varexpr_.variablename_, p->u.varexpr_.listint_, ctx);
            break;
        case is_DoubleExpr:
            err |= checkSDouble(p->u.doubleexpr_.sdouble_, ctx);
            break;
        case is_SIntExpr:
            err |= checkSInt(p->u.sintexpr_.sint_, ctx);
            break;
        case is_IntExpr:
            err |= checkInt(p->u.intexpr_.int_, ctx);
            break;
        case is_Negate:
            err |= checkArithExpr(p->u.negate_.arithexpr_, ctx);
            break;
        case is_Plus:
            err |= checkListArithExpr(p->u.plus_.listarithexpr_, ctx);
            break;
        case is_Minus:
            err |= checkArithExpr(p->u.minus_.arithexpr_, ctx);
            err |= checkListArithExpr(p->u.minus_.listarithexpr_, ctx);
            break;
        case is_Multiply:
            err |= checkListArithExpr(p->u.multiply_.listarithexpr_, ctx);
            break;
        default:
            fprintf(stderr, "Checker Error: Bad kind field in ArithExpr node.\n");
            return 1;
    }
    return err;
}


int checkListArithExpr(ListArithExpr p, SemanticContext *ctx)
{
    if (!p) {
        fprintf(stderr, "Checker Error: ListArithExpr node is NULL where a list was expected.\n");
        return 1;
    }
    int err = 0;
    while(p != 0 && err == 0)
    {
        err |= checkArithExpr(p->arithexpr_, ctx);
        p = p->listarithexpr_;
    }
    return err;
}


int checkBoolExpr(BoolExpr p, SemanticContext *ctx)
{
    if (!p) {
        fprintf(stderr, "Checker Error: BoolExpr node is NULL.\n");
        return 1;
    }
    int err = 0;
    switch(p->kind)
    {
        case is_GreaterThan:
            err |= checkArithExpr(p->u.greaterthan_.arithexpr_1, ctx);
            err |= checkArithExpr(p->u.greaterthan_.arithexpr_2, ctx);
            break;
        case is_LessThan:
            err |= checkArithExpr(p->u.lessthan_.arithexpr_1, ctx);
            err |= checkArithExpr(p->u.lessthan_.arithexpr_2, ctx);
            break;
        case is_GreaterEqual:
            err |= checkArithExpr(p->u.greaterequal_.arithexpr_1, ctx);
            err |= checkArithExpr(p->u.greaterequal_.arithexpr_2, ctx);
            break;
        case is_LessEqual:
            err |= checkArithExpr(p->u.lessequal_.arithexpr_1, ctx);
            err |= checkArithExpr(p->u.lessequal_.arithexpr_2, ctx);
            break;
        case is_NotEqual:
            err |= checkArithExpr(p->u.notequal_.arithexpr_1, ctx);
            err |= checkArithExpr(p->u.notequal_.arithexpr_2, ctx);
            break;
        case is_Equal:
            err |= checkArithExpr(p->u.equal_.arithexpr_1, ctx);
            err |= checkArithExpr(p->u.equal_.arithexpr_2, ctx);
            break;
        case is_And:
            err |= checkListBoolExpr(p->u.and_.listboolexpr_, ctx);
            break;
        case is_Or:
            err |= checkListBoolExpr(p->u.or_.listboolexpr_, ctx);
            break;
        default:
            fprintf(stderr, "Checker Error: Bad kind field in BoolExpr node.\n");
            return 1;
    }
    return err;
}


int checkListBoolExpr(ListBoolExpr p, SemanticContext *ctx)
{
    if (!p) {
        fprintf(stderr, "Checker Error: ListBoolExpr node is NULL where a list was expected.\n");
        return 1;
    }
    int err = 0;
    while(p != 0 && err == 0)
    {
        err |= checkBoolExpr(p->boolexpr_, ctx);
        p = p->listboolexpr_;
    }
    return err;
}


int checkAssertion(Assertion p, SemanticContext *ctx)
{
    if (!p) {
        fprintf(stderr, "Checker Error: Assertion node is NULL.\n");
        return 1;
    }
    int err = 0;
    switch(p->kind)
    {
        case is_Assert:
            err |= checkBoolExpr(p->u.assert_.boolexpr_, ctx);
            break;
        default:
            fprintf(stderr, "Checker Error: Bad kind field in Assertion node.\n");
            return 1;
    }
    return err;
}


int checkListAssertion(ListAssertion p, SemanticContext *ctx)
{
    if (!p) {
        fprintf(stderr, "Checker Error: ListAssertion node is NULL\n");
        return 1;
    }
    int err = 0;
    while(p != 0)
    {
        err |= checkAssertion(p->assertion_, ctx);
        p = p->listassertion_;
    }
    return err;
}


int checkElementType(ElementType p, SemanticContext *ctx)
{
    if (!p) {
        fprintf(stderr, "Checker Error: ElementType node is NULL.\n");
        return 1;
    }
    switch(p->kind)
    {
        case is_GenericElementType: break;
        case is_ElementTypeF16: break;
        case is_ElementTypeF32: break;
        case is_ElementTypeF64: break;
        case is_ElementTypeF4E2M1: break;
        case is_ElementTypeF8E5M2: break;
        case is_ElementTypeF8E5M2FNUZ: break;
        case is_ElementTypeF8E4M3FN: break;
        case is_ElementTypeF8E4M3FNUZ: break;
        case is_ElementTypeI8: break;
        case is_ElementTypeI16: break;
        case is_ElementTypeI32: break;
        case is_ElementTypeI64: break;
        case is_ElementTypeU8: break;
        case is_ElementTypeU16: break;
        case is_ElementTypeU32: break;
        case is_ElementTypeU64: break;
        case is_ElementTypeC64: break;
        case is_ElementTypeC128: break;
        case is_ElementTypeBool: break;
        case is_ElementTypeString: break;
        default:
            fprintf(stderr, "Checker Error: Bad kind field in ElementType node.\n");
            return 1; 
    }
    return 0; 
}


int checkInputDefinition(InputDefinition p, SemanticContext *ctx)
{
    if (!p) {
        fprintf(stderr, "Checker Error: InputDefinition node is NULL.\n");
        return 1;
    }

    int err = 0;

    char* onnxName = NULL;
    SymbolInfo* newSymbol = NULL;
    TensorShape shapeDef = NULL;
    ListInt dims = NULL;

    switch (p->kind) {
        case is_InputOnnxDef:
            err |= checkVariableName(p->u.inputonnxdef_.variablename_, ctx);
            err |= checkElementType(p->u.inputonnxdef_.elementtype_, ctx);
            err |= checkString(p->u.inputonnxdef_.string_, ctx);

            shapeDef = p->u.inputonnxdef_.tensorshape_;
            if (shapeDef->kind == is_TensorDims) {
                dims = shapeDef->u.tensordims_.listint_;
            }
            onnxName = p->u.inputonnxdef_.string_;
            newSymbol = addSymbol(ctx, p->u.inputonnxdef_.variablename_, p->u.inputonnxdef_.elementtype_, dims, SYM_INPUT, onnxName);
            if (!newSymbol) {
                err = 1;
            }
            break;

        case is_InputDef:
            err |= checkVariableName(p->u.inputdef_.variablename_, ctx);
            err |= checkElementType(p->u.inputdef_.elementtype_, ctx);

            shapeDef = p->u.inputdef_.tensorshape_;
            if (shapeDef->kind == is_TensorDims) {
                dims = shapeDef->u.tensordims_.listint_;
            }
            newSymbol = addSymbol(ctx, p->u.inputdef_.variablename_, p->u.inputdef_.elementtype_, dims, SYM_INPUT, onnxName);
            if (!newSymbol) {
                err = 1;
            }
            break;

        default:
            fprintf(stderr, "Checker Error: Bad kind field in InputDefinition node.\n");
            err = 1;
            break;
    }

    if (newSymbol == NULL) {
        err = 1;
    }
    return err;
}


int checkHiddenDefinition(HiddenDefinition p, SemanticContext *ctx)
{
    if (!p) {
        fprintf(stderr, "Checker Error: HiddenDefinition node is NULL.\n");
        return 1;
    }

    int err = 0;
    err |= checkVariableName(p->u.hiddendef_.variablename_, ctx);
    err |= checkElementType(p->u.hiddendef_.elementtype_, ctx);
    err |= checkString(p->u.hiddendef_.string_, ctx);
    if (err) return err;

    char* onnxName = p->u.hiddendef_.string_;
    TensorShape shape = p->u.hiddendef_.tensorshape_;
    ListInt dims = NULL;
    if (shape->kind == is_TensorDims) {
        dims = shape->u.tensordims_.listint_;
    }

    if (!addSymbol(ctx, p->u.hiddendef_.variablename_, p->u.hiddendef_.elementtype_, dims, SYM_HIDDEN, onnxName)) {
        err = 1;
    }
    return err;
}


int checkOutputDefinition(OutputDefinition p, SemanticContext *ctx)
{
    if (!p) {
        fprintf(stderr, "Checker Error: InputDefinition node is NULL.\n");
        return 1;
    }

    int err = 0;

    char* onnxName = NULL;
    SymbolInfo* newSymbol = NULL;
    TensorShape shapeDef = NULL;
    ListInt dims = NULL;

    switch (p->kind) {
        case is_OutputOnnxDef:
            err |= checkVariableName(p->u.outputonnxdef_.variablename_, ctx);
            err |= checkElementType(p->u.outputonnxdef_.elementtype_, ctx);
            err |= checkString(p->u.outputonnxdef_.string_, ctx);

            shapeDef = p->u.outputonnxdef_.tensorshape_;
            if (shapeDef->kind == is_TensorDims) {
                dims = shapeDef->u.tensordims_.listint_;
            }
            onnxName = p->u.outputonnxdef_.string_;
            newSymbol = addSymbol(ctx, p->u.outputonnxdef_.variablename_, p->u.outputonnxdef_.elementtype_, dims, SYM_OUTPUT, onnxName);
            if (!newSymbol) {
                err = 1;
            }
            break;

        case is_OutputDef:
            err |= checkVariableName(p->u.outputdef_.variablename_, ctx);
            err |= checkElementType(p->u.outputdef_.elementtype_, ctx);

            shapeDef = p->u.outputdef_.tensorshape_;
            if (shapeDef->kind == is_TensorDims) {
                dims = shapeDef->u.tensordims_.listint_;
            }
            newSymbol = addSymbol(ctx, p->u.outputdef_.variablename_, p->u.outputdef_.elementtype_, dims, SYM_OUTPUT, onnxName);
            if (!newSymbol) {
                err = 1;
            }
            break;

        default:
            fprintf(stderr, "Checker Error: Bad kind field in InputDefinition node.\n");
            err = 1;
            break;
    }

    if (newSymbol == NULL) {
        err = 1;
    } 
    return err;
}


int checkListInputDefinition(ListInputDefinition p, int *usesOnnxNames, SemanticContext *ctx)
{   
    if (!p) {
        fprintf(stderr, "Checker Error: Network definition requires at least one input. ListInputDefinition is NULL.\n");
        return 1;
    }
    int err = 0;
    while(p != 0)
    {
        err |= checkInputDefinition(p->inputdefinition_, ctx);

        switch (*usesOnnxNames) {
            case -1:
                *usesOnnxNames = (p->inputdefinition_->kind == is_InputOnnxDef) ? 1 : 0;
                break;
            case 0:
                if (p->inputdefinition_->kind == is_InputOnnxDef) {
                    err = 1;
                    addError(ctx, (VNNLibError) {
                        .message = "Expected ordered input variables but got an ONNX-named input variable",
                        .offendingSymbol = p->inputdefinition_->u.inputdef_.variablename_,
                        .hint = "All (input/output) variables for a network must have an ONNX name OR no (input/output) variables may have an ONNX name.",
                        .errorCode = UnexpectedOnnxName
                    });
                }
                break;
            case 1:
                if (p->inputdefinition_->kind == is_InputDef) 
                {
                    err = 1;
                    addError(ctx, (VNNLibError) {
                        .message = "Expected ONNX-named input variable but got an ordered input variable",
                        .offendingSymbol = p->inputdefinition_->u.inputdef_.variablename_,
                        .hint = "All (input/output) variables for a network must have an ONNX name OR no (input/output) variables may have an ONNX name.",
                        .errorCode = UnexpectedOnnxName
                    });
                }
                break;
            default:
                fprintf(stderr, "Checker Error: Unexpected value for usesOnnxNames flag: %d\n", *usesOnnxNames);
                return 1;   
        }

        p = p->listinputdefinition_;
    }
    return err;
}


int checkListHiddenDefinition(ListHiddenDefinition p, SemanticContext *ctx)
{
    if (!p) return 0; // ListHiddenDefinition is optional
    int err = 0;
    while(p != 0)
    {
        err |= checkHiddenDefinition(p->hiddendefinition_, ctx);
        p = p->listhiddendefinition_;
    }
    return err;
}


int checkListOutputDefinition(ListOutputDefinition p, int *usesOnnxNames, SemanticContext *ctx)
{
    if (!p) {
        fprintf(stderr, "Checker Error: Network definition requires at least one output. ListOutputDefinition is NULL.\n");
        return 1;
    }
    int err = 0;
    while(p  != 0 && err == 0)
    {
        err |= checkOutputDefinition(p->outputdefinition_, ctx);

        switch (*usesOnnxNames) {
            case -1:
                *usesOnnxNames = (p->outputdefinition_->kind == is_OutputOnnxDef) ? 1 : 0;
                break;
            case 0:
                if (p->outputdefinition_->kind == is_OutputOnnxDef) {
                    err = 1;
                    addError(ctx, (VNNLibError) {
                        .message = "Expected ordered output variables but got an ONNX-named output variable",
                        .offendingSymbol = p->outputdefinition_->u.outputonnxdef_.variablename_,
                        .hint = "All (input/output) variables for a network must have an ONNX name OR no (input/output) variables may have an ONNX name.",
                        .errorCode = UnexpectedOnnxName
                    });
                }
                break;
            case 1:
                if (p->outputdefinition_->kind == is_OutputDef) 
                {
                    err = 1;
                    addError(ctx, (VNNLibError) {
                        .message = "Expected ONNX-named output variable but got an ordered output variable",
                        .offendingSymbol = p->outputdefinition_->u.outputdef_.variablename_,
                        .hint = "All (input/output) variables for a network must have an ONNX name OR no (input/output) variables may have an ONNX name.",
                        .errorCode = UnexpectedOnnxName
                    });
                }
                break;
            default:
                fprintf(stderr, "Checker Error: Unexpected value for usesOnnxNames flag: %d\n", *usesOnnxNames);
                return 1;   
        }

        p = p->listoutputdefinition_;
    }
    return err;
}


int checkNetworkDefinition(NetworkDefinition p, SemanticContext *ctx)
{
    if (!p) {
        fprintf(stderr, "Checker Error: NetworkDefinition node is NULL.\n");
        return 1;
    }

    // Flag to track if any ONNX names are used for inputs/outputs
    int usesOnnxNames = -1;
    int err = 0;

    switch(p->kind)
    {
        case is_NetworkDef:
            err |= checkVariableName(p->u.networkdef_.variablename_, ctx);
            err |= checkListInputDefinition(p->u.networkdef_.listinputdefinition_, &usesOnnxNames, ctx);
            err |= checkListHiddenDefinition(p->u.networkdef_.listhiddendefinition_, ctx);
            err |= checkListOutputDefinition(p->u.networkdef_.listoutputdefinition_, &usesOnnxNames, ctx);
            break;
        default:
            fprintf(stderr, "Checker Error: Bad kind field in NetworkDefinition node.\n");
            return 1; 
    }

    return err;
}


int checkListNetworkDefinition(ListNetworkDefinition p, SemanticContext *ctx)
{
    if (!p) {
        fprintf(stderr, "Checker Error: VNNLib file requires at least one network definition. ListNetworkDefinition is NULL.\n");
        return 1;
    }
    int err = 0;
    while(p != 0)
    {
        err |= checkNetworkDefinition(p->networkdefinition_, ctx);
        p = p->listnetworkdefinition_;
    }
    return err;
}


int checkQuery(Query p, SemanticContext *ctx)
{
    if (!p) {
        fprintf(stderr, "Checker Error: Top-level Query node is NULL.\n");
        return 1;
    }
    int err = 0;
    switch(p->kind)
    {
    case is_VNNLibQuery:
        err |= checkListNetworkDefinition(p->u.vnnlibquery_.listnetworkdefinition_, ctx);
        err |= checkListAssertion(p->u.vnnlibquery_.listassertion_, ctx);
        break;
    default:
        fprintf(stderr, "Checker Error: Bad kind field in Query node.\n");
        return 1;
    }
    return err;
}


// --- Base Type Checkers ---

int checkSDouble(SDouble p, SemanticContext *ctx) { return 0; }
int checkSInt(SInt p, SemanticContext *ctx) { return 0; }
int checkInt(Int p, SemanticContext *ctx) { return 0; }
int checkVariableName(VariableName p, SemanticContext *ctx) { return 0; }
int checkIdent(Ident i, SemanticContext *ctx) { return 0; }      
int checkInteger(Integer i, SemanticContext *ctx) { return 0; }
int checkDouble(Double d, SemanticContext *ctx) { return 0; }
int checkChar(Char c, SemanticContext *ctx) { return 0; }
int checkString(char* s, SemanticContext *ctx) { return 0; }


int checkTensorElement(VariableName tensorName, ListInt tensorIndex, SemanticContext *ctx) {
    if (!tensorName) {
        fprintf(stderr, "Checker Error: tensorName is NULL in checkTensorElement.\n");
        return 1;
    }
    int err = 0;

    const SymbolInfo *symbol = findSymbol(ctx, tensorName); 

    if (!symbol) {
        err = 1;
        addError(ctx, (VNNLibError) {
            .message = "Undeclared variable",
            .offendingSymbol = tensorName,
            .hint = "Variable must be declared before use.",
            .errorCode = UndeclaredVariable
        });
        return err;
    }

    if (!tensorIndex) {
        err = 1;
        addError(ctx, (VNNLibError) {
            .message = "No indices provided for tensor element",
            .offendingSymbol = tensorName,
            .hint = "Tensor element access requires indices.",
            .errorCode = NotEnoughIndices
        });
        return err;
    }

    if (symbol->numDimensions == 0) {
        int firstIndex = atoi(tensorIndex->int_);
        if (firstIndex != 0 || tensorIndex->listint_ != NULL) {
            err = 1;
            addError(ctx, (VNNLibError) {
                .message = "Indexing on scalar variable",
                .offendingSymbol = tensorName,
                .hint = "Scalar variables cannot be indexed. Only the dummy index 0 is allowed.",
                .errorCode = IndexOutOfBounds
            });
        }
        return err;
    }

    int numIndices = 0;
    ListInt currentIndexNode = tensorIndex;
    while (currentIndexNode != NULL) {
        numIndices++;

        if (numIndices > symbol->numDimensions) {
            err = 1;
            addError(ctx, (VNNLibError) {
                .message = "Too many indices provided",
                .offendingSymbol = tensorName,
                .hint = format_string("Expected %d indices but encountered %d.", symbol->numDimensions, numIndices),
                .errorCode = TooManyIndices
            });
            return err;
        }

        int index = atoi(currentIndexNode->int_);
        if (index < 0 || index >= symbol->shape[numIndices - 1]) {
            err = 1;
            addError(ctx, (VNNLibError) {
                .message = "Index out of bounds",
                .offendingSymbol = tensorName,
                .hint = format_string("Expected index in range [0, %d), but got %d.", symbol->shape[numIndices - 1], index),
                .errorCode = IndexOutOfBounds
            });
        }
        currentIndexNode = currentIndexNode->listint_;
    }

    if (!err && numIndices < symbol->numDimensions) {
        err = 1;
        addError(ctx, (VNNLibError) {
            .message = "Not enough indices provided",
            .offendingSymbol = tensorName,
            .hint = format_string("Expected %d indices but encountered %d.", symbol->numDimensions, numIndices),
            .errorCode = NotEnoughIndices
        });
    }
    
    return err;
}