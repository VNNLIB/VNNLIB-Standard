#ifndef EXTENDED_ABSYN_H
#define EXTENDED_ABSYN_H

#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <math.h>
#include "Absyn.h"
#include "Parser.h"
#include "Printer.h"
#include "Util.h"

struct LinearArithExpr_;
typedef struct LinearArithExpr_ *LinearArithExpr;

struct LinearArithExpr_ {
    double *coeffs;  // Coefficients for the linear terms
    VariableName *vars; // Variables in the linear expression
    int num_terms;   // Number of terms in the linear expression
    double constant; // Constant term
};

LinearArithExpr linearise(ArithExpr arith_expr);

void freeLinearArithExpr(LinearArithExpr expr);

void debugQuery(Query q);

#endif // EXTENDED_ABSYN_H