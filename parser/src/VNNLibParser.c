#define _GNU_SOURCE 
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <argp.h>

#include "SemanticChecker.h"
#include "Parser.h"
#include "Absyn.h"
#include "Printer.h"


// Program Information
const char *argp_program_version = "argp-ex3 1.0";
const char *argp_program_bug_address = "<bug-gnu-utils@gnu.org>";

static const char usage_message[] = 
    "Usage: VNNLibParser check [-v] VNNLIBFILE \n\n"
    "  MODE:\n"
    "    check        Parse and perform semantic checks on the VNNLIB file.\n\n"
    "  ARGUMENTS:\n"
    "    VNNLIBFILE   Path to the input VNNLIB specification file.\n\n"
    "  OPTIONS:\n"
    "    -v, --verbose  Produce verbose output.\n"
    "    -h, --help     Display this help message and exit.\n";

static char args_doc[] = "VNNLIBFILE";


// Argument Parsing Options
static struct argp_option options[] = {
    { "verbose",    'v',    0,      0,  "Produce verbose output",   0 },
    {"json",        'j',    0,      0,  "Output in JSON format",    0},
    {"output",      'o',    "FILE", 0,  "Output to FILE",           0},
    { 0 }
};


// Mode Types
typedef enum {
    MODE_NONE,
    MODE_CHECK 
} parser_mode_t;


// Arguments Structure
struct arguments {
    parser_mode_t mode;
    char *spec_file;          
    int verbose;       // Verbose output flag  
    int json;          // JSON output flag
    FILE *out;         // Output file pointer   
};  


// Helper function for usage
void usage(const char *prog_name) {
    fprintf(stderr, "%s: %s\n", prog_name, usage_message);
}


// Argument Parsing Function
static error_t parse_opt(int key, char *arg, struct argp_state *state) {
    struct arguments *arguments = state->input;

    switch (key) {
        case 'v':
            arguments->verbose = 1;
            break;
        case 'j':
            arguments->json = 1;
            break;
        case 'o':
            arguments->out = fopen(arg, "w");
            if (!arguments->out) {
                fprintf(stderr, "Error: Cannot open output file '%s': ", arg);
                return ARGP_ERR_UNKNOWN;
            }
            break;

        case ARGP_KEY_ARG:
            // Check execution mode
            if (state->arg_num == 0) {
                if (strcmp(arg, "check") == 0) {
                    arguments->mode = MODE_CHECK;
                } else {
                    fprintf(stderr, "Error: Unknown or unsupported mode '%s'. Only 'check' is currently supported.\n", arg);
                    argp_usage(state);
                }
            // Check for the VNNLIB file argument
            } else if (state->arg_num == 1) {
                arguments->spec_file = arg;
            } else {
                argp_usage(state);
            }
            break;
        case ARGP_KEY_END:
            if (state->arg_num < 2)
                argp_usage(state);
            break;
        default:
            return ARGP_ERR_UNKNOWN;
    }
    return 0;
}


/**
 * @brief Executes the check command: performs semantic checks on the VNNLIB file.
 * @param args Parsed command line arguments.
 * @return int 0 on success (parsing and semantic checks passed), 1 on failure.
 */
int do_check(Query parse_tree, int verbose, int json, FILE *out) {
    if (!out) out = stdout; // Default to stdout

    if (verbose) {
        printf("Running semantic checks...\n\n");
    }
    
    // Initialize the semantic context
    SemanticContext ctx;
    initSemanticContext(&ctx);

    // Start traversal
    checkQuery(parse_tree, &ctx);

    // Check for semantic errors
    if (ctx.errorCount > 0) {
        char *errorReport = NULL;
        if (json) {
            errorReport = reportErrorsJSON(&ctx);
        } else {
            errorReport = reportErrors(&ctx);
        }
        
        fprintf(out, "%s", errorReport);
        free(errorReport);
    }

    int finalErrorCount = ctx.errorCount;
    destroySemanticContext(&ctx); // Clean up allocated symbols

    if (finalErrorCount > 0) {
        printf("Found %d semantic error(s).\n\n", finalErrorCount);
    }

    if (verbose && finalErrorCount == 0) {
        printf("Semantic Checks Completed: OK\n");
    } else if (verbose) {
        printf("Semantic Checks Completed: FAILED\n");
    }

    return finalErrorCount > 0 ? 1 : 0;
}


static struct argp argp = {options, parse_opt, args_doc, usage_message, 0, 0, 0};


int main(int argc, char **argv) {
    struct arguments arguments; 
    int exit_status = EXIT_SUCCESS;

    arguments.mode = MODE_NONE;
    arguments.spec_file = NULL;
    arguments.verbose = 0;
    arguments.json = 0;
    arguments.out = NULL;

    // 0. Parse command line arguments
    argp_parse(&argp, argc, argv, 0, 0, &arguments);

    if (arguments.verbose) {
        printf("Verbose mode enabled.\n");
        printf("Running Check Mode\n");
        printf("Spec File: %s\n", arguments.spec_file);
    }

    // 1. Open the input file
    FILE *input_file = fopen(arguments.spec_file, "r");
    if (!input_file) {
        fprintf(stderr, "Error: Cannot open input file '%s': ", arguments.spec_file);
        return 1;
    }
    if (arguments.verbose) {
        printf("File opened successfully: %s\n", arguments.spec_file);
    }

    // 2. Parse the file using the BNFC-generated parser
    Query parse_tree = pQuery(input_file);
    if (!parse_tree) {
        fprintf(stderr, "Error: Parsing failed.\n");
        return 1;
    }

    if (arguments.verbose) {
        printf("Parse tree generated successfully.\n\n");
        printf("[Linearized Tree]\n");
        printf("%s\n\n", printQuery(parse_tree));
    }

    // 3. Execute the check command
    if (arguments.mode == MODE_CHECK) { 
        if (do_check(parse_tree, arguments.verbose, arguments.json, arguments.out) != 0) {
            exit_status = EXIT_FAILURE;
        }
    } 

    // 4. Clean up the AST
    free_Query(parse_tree);
    if (arguments.verbose) {
        printf("Parse tree freed successfully.\n");
    }

    return exit_status;
}