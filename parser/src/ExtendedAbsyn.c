#include "ExtendedAbsyn.h"


void freeLinearArithExpr(LinearArithExpr expr) {
    if (expr) {
        free(expr->coeffs);
        free(expr->vars);
        free(expr);
    }
}

/**
 * @brief Copies the contents of one LinearArithExpr to another.
 * @param dest The destination LinearArithExpr to copy into.
 * @param src The source LinearArithExpr to copy from.
 */
void copyLinearArithExpr(LinearArithExpr dest, const LinearArithExpr src) {
    if (!dest || !src) return;

    dest->num_terms = src->num_terms;
    dest->constant = src->constant;

    dest->vars = (VariableName *) malloc(src->num_terms * sizeof(VariableName));
    if (!dest->vars) {
        fprintf(stderr, "Error: out of memory when copying vars in LinearArithExpr!\n");
        return;
    }
    memcpy(dest->vars, src->vars, src->num_terms * sizeof(VariableName));

    dest->coeffs = (double *) malloc(src->num_terms * sizeof(double));
    if (!dest->coeffs) {
        fprintf(stderr, "Error: out of memory when copying coeffs in LinearArithExpr!\n");
        return;
    }
    memcpy(dest->coeffs, src->coeffs, src->num_terms * sizeof(double));
}

/**
 * @brief Pretty-prints a LinearArithExpr into a human-readable string.
 * @param p The LinearArithExpr to pretty-print.
 * @return A dynamically allocated string representing the expression.
 */
char *ppLinearArithExpr(LinearArithExpr p) {
    if (!p) return strdup("NULL");

    size_t size = 128;
    size_t used = 0;
    char *buffer = (char *) malloc(size);
    if (!buffer) {
        fprintf(stderr, "Error: out of memory for ppLinearArithExpr buffer!\n");
        return NULL;
    }
    buffer[0] = '\0';

    bool first_term_printed = false;

    // 1. Handle the constant term first. Only print if non-zero, or if it's the only term in the expression.
    if (fabs(p->constant) > 1e-9 || p->num_terms == 0) {
        buffer = append_str(buffer, &size, &used, "%.4g", p->constant);
        first_term_printed = true;
    }

    // 2. Handle the variable terms
    for (int i = 0; i < p->num_terms; i++) {
        double coeff = p->coeffs[i];

        // Skip terms with a zero coefficient
        if (fabs(coeff) < 1e-9) {
            continue;
        }

        // Determine the sign and operator to print
        const char* op = (coeff > 0) ? " + " : " - ";
        if (first_term_printed) {
            buffer = append_str(buffer, &size, &used, "%s", op);
        } else if (coeff < 0) {
            // If this is the first term and it's negative, print a minus sign
            buffer = append_str(buffer, &size, &used, "-");
        }

        double abs_coeff = fabs(coeff);

        // Print the coefficient only if it's not 1.0
        if (fabs(abs_coeff - 1.0) > 1e-9) {
            buffer = append_str(buffer, &size, &used, "%.4g * ", abs_coeff);
        }

        // Print the variable name
        buffer = append_str(buffer, &size, &used, "%s", p->vars[i]);

        first_term_printed = true;
    }

    // If after all that, nothing was printed (e.g., all coeffs and constant were zero),
    // represent it as "0".
    if (!first_term_printed) {
        buffer = append_str(buffer, &size, &used, "0");
    }
    
    // Trim unused buffer space before returning
    buffer = (char *)realloc(buffer, used + 1);
    return buffer;
}

/**
 * @brief Linearises an ArithExpr into a LinearArithExpr.
 * @param arith_expr The ArithExpr to linearise.
 * @return A LinearArithExpr representing the linearised form of the input expression.
 */ 
LinearArithExpr linearise(ArithExpr arith_expr) {
    LinearArithExpr expr = (LinearArithExpr) malloc(sizeof(*expr));
    if (!expr) {
        fprintf(stderr, "Error: out of memory when allocating LinearArithExpr!\n");
        return NULL;
    }

    expr->coeffs = NULL;
    expr->vars = NULL;
    expr->num_terms = 0;
    expr->constant = 0.0;

    switch (arith_expr->kind) {

        // --- Base Cases ---

        // Handle the case of a single variable
        case is_VarExpr: {
            expr->num_terms = 1;
            expr->vars = (VariableName *) realloc(expr->vars, sizeof(VariableName));
            if (!expr->vars) {
                fprintf(stderr, "Error: out of memory when allocating vars in LinearArithExpr!\n");
                freeLinearArithExpr(expr);
                return NULL;
            }
            expr->vars[0] = arith_expr->u.varexpr_.variablename_;
            expr->coeffs = (double *) realloc(expr->coeffs, sizeof(double));
            if (!expr->coeffs) {
                freeLinearArithExpr(expr);
                return NULL;
            }
            expr->coeffs[0] = 1.0;
            break;
        }

        case is_DoubleExpr: {
            expr->constant = atof(arith_expr->u.doubleexpr_.sdouble_);
            break;
        }

        case is_SIntExpr: {
            expr->constant = atoi(arith_expr->u.sintexpr_.sint_);
            break;
        }

        case is_IntExpr: {
            expr->constant = atoi(arith_expr->u.intexpr_.int_);
            break;
        }

        // --- Recursive Cases ---

        // Negate operation performs a unary negation on its sub-expression
        case is_Negate: {
            LinearArithExpr sub_expr = linearise(arith_expr->u.negate_.arithexpr_);
            if (!sub_expr) {
                freeLinearArithExpr(expr);
                return NULL;
            }
            expr->num_terms = sub_expr->num_terms;
            expr->constant = -sub_expr->constant;

            expr->vars = (VariableName *) realloc(expr->vars, expr->num_terms * sizeof(VariableName));
            if (!expr->vars) {
                fprintf(stderr, "Error: out of memory when allocating vars in LinearArithExpr!\n");
                freeLinearArithExpr(sub_expr);
                freeLinearArithExpr(expr);
                return NULL;
            }
            memcpy(expr->vars, sub_expr->vars, expr->num_terms * sizeof(VariableName));

            expr->coeffs = (double *) realloc(expr->coeffs, expr->num_terms * sizeof(double));
            if (!expr->coeffs) {
                fprintf(stderr, "Error: out of memory when allocating coeffs in LinearArithExpr!\n");
                freeLinearArithExpr(sub_expr);
                freeLinearArithExpr(expr);
                return NULL;
            }
            // Apply negation to coefficients
            for (int i = 0; i < sub_expr->num_terms; i++) {
                expr->coeffs[i] = -sub_expr->coeffs[i];
            }

            freeLinearArithExpr(sub_expr);   
            break;
        }

        // Plus and Minus operations combine multiple linear expressions
        case is_Plus: {
            ListArithExpr list = arith_expr->u.plus_.listarithexpr_;
            LinearArithExpr first_expr = linearise(list->arithexpr_);
            if (!first_expr) {
                freeLinearArithExpr(expr);
                return NULL;
            }
            copyLinearArithExpr(expr, first_expr);
            freeLinearArithExpr(first_expr);

            ListArithExpr current = list->listarithexpr_;
            while (current) {
                LinearArithExpr sub_expr = linearise(current->arithexpr_);
                if (!sub_expr) {
                    freeLinearArithExpr(expr);
                    return NULL;
                }

                int *found = (int *)calloc(sub_expr->num_terms, sizeof(int));
                if (!found && sub_expr->num_terms > 0) {
                    fprintf(stderr, "Error: out of memory for 'found' array.\n");
                    freeLinearArithExpr(sub_expr);
                    freeLinearArithExpr(expr);
                    return NULL;
                }
                
                int num_new_terms = 0;

                // First pass: find matching terms and count new ones
                for (int i = 0; i < sub_expr->num_terms; i++) {
                    bool term_found_in_expr = false;
                    for (int j = 0; j < expr->num_terms; j++) {
                        if (strcmp(expr->vars[j], sub_expr->vars[i]) == 0) {
                            expr->coeffs[j] += sub_expr->coeffs[i];
                            found[i] = 1; 
                            term_found_in_expr = true;
                            break;
                        }
                    }
                    if (!term_found_in_expr) {
                        num_new_terms++;
                    }
                }

                // Second pass: if there are new terms, allocate space and add them
                if (num_new_terms > 0) {
                    int old_num_terms = expr->num_terms;
                    int new_total_terms = old_num_terms + num_new_terms;

                    // Reallocate memory for vars and coeffs
                    VariableName *temp_vars = realloc(expr->vars, new_total_terms * sizeof(VariableName));
                    if (!temp_vars) {
                        fprintf(stderr, "Error: out of memory when reallocating vars in LinearArithExpr!\n");
                        free(found);
                        freeLinearArithExpr(sub_expr);
                        freeLinearArithExpr(expr); // The original expr is still valid, but we are failing
                        return NULL;
                    }
                    expr->vars = temp_vars;
                    
                    double *temp_coeffs = realloc(expr->coeffs, new_total_terms * sizeof(double));
                    if (!temp_coeffs) {
                        fprintf(stderr, "Error: out of memory when reallocating coeffs in LinearArithExpr!\n");
                        free(found);
                        freeLinearArithExpr(sub_expr);
                        freeLinearArithExpr(expr);
                        return NULL;
                    }
                    expr->coeffs = temp_coeffs;
                    
                    expr->num_terms = new_total_terms;

                    // Add the new terms to the end of the arrays
                    int new_term_cursor = old_num_terms;
                    for (int i = 0; i < sub_expr->num_terms; i++) {
                        if (!found[i]) {
                            expr->vars[new_term_cursor] = sub_expr->vars[i];
                            expr->coeffs[new_term_cursor] = sub_expr->coeffs[i];
                            new_term_cursor++;
                        }
                    }
                }

                // Add the constant term
                expr->constant += sub_expr->constant;

                free(found); 
                freeLinearArithExpr(sub_expr);
                current = current->listarithexpr_;
            }
            break;
        }

        case is_Minus: {
            LinearArithExpr first_expr = linearise(arith_expr->u.minus_.arithexpr_);
            if (!first_expr) {
                freeLinearArithExpr(expr);
                return NULL;
            }
            copyLinearArithExpr(expr, first_expr);
            freeLinearArithExpr(first_expr);

            ListArithExpr current = arith_expr->u.minus_.listarithexpr_;
            while (current) {
                LinearArithExpr sub_expr = linearise(current->arithexpr_);
                if (!sub_expr) {
                    freeLinearArithExpr(expr);
                    return NULL;
                }

                int *found = (int *)calloc(sub_expr->num_terms, sizeof(int));
                if (!found && sub_expr->num_terms > 0) {
                    fprintf(stderr, "Error: out of memory for 'found' array.\n");
                    freeLinearArithExpr(sub_expr);
                    freeLinearArithExpr(expr);
                    return NULL;
                }
                
                int num_new_terms = 0;

                // First pass: find matching terms and count new ones
                for (int i = 0; i < sub_expr->num_terms; i++) {
                    bool term_found_in_expr = false;
                    for (int j = 0; j < expr->num_terms; j++) {
                        if (strcmp(expr->vars[j], sub_expr->vars[i]) == 0) {
                            expr->coeffs[j] -= sub_expr->coeffs[i];
                            found[i] = 1; 
                            term_found_in_expr = true;
                            break;
                        }
                    }
                    if (!term_found_in_expr) {
                        num_new_terms++;
                    }
                }

                // Second pass: if there are new terms, allocate space and add them
                if (num_new_terms > 0) {
                    int old_num_terms = expr->num_terms;
                    int new_total_terms = old_num_terms + num_new_terms;

                    // Reallocate memory for vars and coeffs
                    VariableName *temp_vars = realloc(expr->vars, new_total_terms * sizeof(VariableName));
                    if (!temp_vars) {
                        fprintf(stderr, "Error: out of memory when reallocating vars in LinearArithExpr!\n");
                        free(found);
                        freeLinearArithExpr(sub_expr);
                        freeLinearArithExpr(expr);
                        return NULL;
                    }
                    expr->vars = temp_vars;
                    
                    double *temp_coeffs = realloc(expr->coeffs, new_total_terms * sizeof(double));
                    if (!temp_coeffs) {
                        fprintf(stderr, "Error: out of memory when reallocating coeffs in LinearArithExpr!\n");
                        free(found);
                        freeLinearArithExpr(sub_expr);
                        freeLinearArithExpr(expr);
                        return NULL;
                    }
                    expr->coeffs = temp_coeffs;
                    
                    expr->num_terms = new_total_terms;

                    int new_term_cursor = old_num_terms;
                    for (int i = 0; i < sub_expr->num_terms; i++) {
                        if (!found[i]) {
                            expr->vars[new_term_cursor] = sub_expr->vars[i];
                            expr->coeffs[new_term_cursor] = -sub_expr->coeffs[i];
                            new_term_cursor++;
                        }
                    }
                }

                expr->constant -= sub_expr->constant;

                free(found);
                freeLinearArithExpr(sub_expr);
                current = current->listarithexpr_;
            }
            break;
        }

        case is_Multiply: {
            ListArithExpr list = arith_expr->u.multiply_.listarithexpr_;

            // Linearise each sub-expression in the multiplication
            int num_operands = 0;
            for (ListArithExpr l = list; l; l = l->listarithexpr_) num_operands++;

            LinearArithExpr *sub_exprs = (LinearArithExpr *)malloc(num_operands * sizeof(LinearArithExpr));
            if (!sub_exprs) {
                fprintf(stderr, "Error: out of memory for sub-expression array!\n");
                freeLinearArithExpr(expr);
                return NULL;
            }

            ListArithExpr current = list;
            for (int i = 0; i < num_operands; ++i) {
                sub_exprs[i] = linearise(current->arithexpr_);
                if (!sub_exprs[i]) { 
                    for (int j = 0; j < i; j++) freeLinearArithExpr(sub_exprs[j]);
                    free(sub_exprs);
                    freeLinearArithExpr(expr);
                    return NULL;
                }
                current = current->listarithexpr_;
            }

            // Check for linearity and compute the constant product
            LinearArithExpr var_expr = NULL;
            double constant_product = 1.0;
            bool non_linear = false;

            for (int i = 0; i < num_operands; ++i) {
                if (sub_exprs[i]->num_terms > 0) {
                    if (var_expr != NULL) {
                        non_linear = true;
                        break;
                    }
                    var_expr = sub_exprs[i];
                } else {
                    constant_product *= sub_exprs[i]->constant;
                }
            }

            if (non_linear) {
                fprintf(stderr, "Error: Multiple variables detected in multiplication. Cannot linearise non-linear expression\n");
            } else {
                // Construct final LinearArithExpr
                if (var_expr) {
                    copyLinearArithExpr(expr, var_expr);
                    expr->constant *= constant_product;
                    for (int i = 0; i < expr->num_terms; ++i) {
                        expr->coeffs[i] *= constant_product;
                    }
                } else { // No variables, just a multiplication of constants
                    expr->constant = constant_product;
                }
            }

            // Cleanup
            for (int i = 0; i < num_operands; ++i) {
                freeLinearArithExpr(sub_exprs[i]);
            }
            free(sub_exprs);
            
            if (non_linear) {
                freeLinearArithExpr(expr);
                return NULL;
            }
            break;
        }
        default: {
            fprintf(stderr, "Error: Unsupported ArithExpr kind for linearisation!\n");
            freeLinearArithExpr(expr);
            return NULL;
        }
    }

    return expr;
}


// Forward declarations of helper functions

static void debugBoolExpr(BoolExpr p, int indent_level);
static void debugListBoolExpr(ListBoolExpr p, int indent_level);
static void debugAssertion(Assertion p, int indent_level);
static void debugListAssertion(ListAssertion p, int indent_level);

/* --- Helper Functions --- */

// A simple helper to print indentation.
static void print_indent(int level) {
    for (int i = 0; i < level; ++i) {
        printf("  ");
    }
}

// Helper to process and print a single ArithExpr.
static void process_and_print_arithexpr(const char* label, ArithExpr arith_expr, int indent_level) {
    LinearArithExpr linear_expr = linearise(arith_expr);
    char *pretty_str = ppLinearArithExpr(linear_expr);
    
    print_indent(indent_level);
    printf("%s: %s\n", label, pretty_str);
    
    // Clean up memory
    free(pretty_str);
    freeLinearArithExpr(linear_expr);
}

/* --- Core Traversal and Debugging Logic --- */

/**
 * @brief Recursively traverses a BoolExpr, printing its structure and
 * linearizing any arithmetic expressions it contains.
 * @param p The BoolExpr node to process.
 * @param indent_level The current depth for pretty-printing.
 */
static void debugBoolExpr(BoolExpr p, int indent_level) {
    if (!p) return;

    print_indent(indent_level);

    switch (p->kind) {
        // --- Base cases: Comparisons ---
        case is_GreaterThan:
            printf("GreaterThan (>) {\n");
            process_and_print_arithexpr("LHS", p->u.greaterthan_.arithexpr_1, indent_level + 1);
            process_and_print_arithexpr("RHS", p->u.greaterthan_.arithexpr_2, indent_level + 1);
            break;
        case is_LessThan:
            printf("LessThan (<) {\n");
            process_and_print_arithexpr("LHS", p->u.lessthan_.arithexpr_1, indent_level + 1);
            process_and_print_arithexpr("RHS", p->u.lessthan_.arithexpr_2, indent_level + 1);
            break;
        case is_GreaterEqual:
            printf("GreaterEqual (>=) {\n");
            process_and_print_arithexpr("LHS", p->u.greaterequal_.arithexpr_1, indent_level + 1);
            process_and_print_arithexpr("RHS", p->u.greaterequal_.arithexpr_2, indent_level + 1);
            break;
        case is_LessEqual:
            printf("LessEqual (<=) {\n");
            process_and_print_arithexpr("LHS", p->u.lessequal_.arithexpr_1, indent_level + 1);
            process_and_print_arithexpr("RHS", p->u.lessequal_.arithexpr_2, indent_level + 1);
            break;
        case is_NotEqual:
            printf("NotEqual (!=) {\n");
            process_and_print_arithexpr("LHS", p->u.notequal_.arithexpr_1, indent_level + 1);
            process_and_print_arithexpr("RHS", p->u.notequal_.arithexpr_2, indent_level + 1);
            break;
        case is_Equal:
            printf("Equal (==) {\n");
            process_and_print_arithexpr("LHS", p->u.equal_.arithexpr_1, indent_level + 1);
            process_and_print_arithexpr("RHS", p->u.equal_.arithexpr_2, indent_level + 1);
            break;

        // --- Recursive cases: Logical connectives ---
        case is_And:
            printf("And (&&) [\n");
            debugListBoolExpr(p->u.and_.listboolexpr_, indent_level + 1);
            print_indent(indent_level);
            printf("]\n");
            return; // Return early to avoid printing closing brace
        case is_Or:
            printf("Or (||) [\n");
            debugListBoolExpr(p->u.or_.listboolexpr_, indent_level + 1);
            print_indent(indent_level);
            printf("]\n");
            return; // Return early to avoid printing closing brace
    }
    print_indent(indent_level);
    printf("}\n");
}

/**
 * @brief Traverses a list of BoolExpr nodes.
 */
static void debugListBoolExpr(ListBoolExpr p, int indent_level) {
    ListBoolExpr current = p;
    while (current) {
        debugBoolExpr(current->boolexpr_, indent_level);
        current = current->listboolexpr_;
    }
}

/**
 * @brief Traverses a Assertion node.
*/
static void debugAssertion(Assertion p, int indent_level) {
    if (!p) return;
    if (p->kind == is_Assert) {
        print_indent(indent_level);
        printf("Assertion {\n");
        debugBoolExpr(p->u.assert_.boolexpr_, indent_level + 1);
        print_indent(indent_level);
        printf("}\n");
    }
}

/**
 * @brief Traverses a list of Assertion nodes.
*/
static void debugListAssertion(ListAssertion p, int indent_level) {
    ListAssertion current = p;
    int prop_num = 1;
    while (current) {
        print_indent(indent_level);
        printf("--- Processing Assertion #%d ---\n", prop_num++);
        debugAssertion(current->assertion_, indent_level);
        current = current->listassertion_;
        if (current) printf("\n");
    }
}

/**
 * @brief Main entry point to start the debugging process from a Query object.
 * @param query The top-level Query AST node.
*/
void debugQuery(Query query) {
    if (!query) {
        printf("Query is NULL.\n");
        return;
    }
    printf("=======================================\n");
    printf("  STARTING VNNLibQuery DEBUG         \n");
    printf("=======================================\n\n");
    if (query->kind == is_VNNLibQuery) {
        // We ignore network definitions and go straight to properties.
        debugListAssertion(query->u.vnnlibquery_.listassertion_, 0);
    }
    printf("\n=======================================\n");
    printf("  FINISHED VNNLibQuery DEBUG         \n");
    printf("=======================================\n");
}