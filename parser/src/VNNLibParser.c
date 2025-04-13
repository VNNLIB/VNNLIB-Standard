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
    { "verbose",  'v', 0,    0,  "Produce verbose output", 0 },
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
    int verbose;          
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
        case ARGP_KEY_ARG:
            if (state->arg_num == 0) {
                if (strcmp(arg, "check") == 0) {
                    arguments->mode = MODE_CHECK;
                } else {
                    fprintf(stderr, "Error: Unknown or unsupported mode '%s'. Only 'check' is currently supported.\n", arg);
                    argp_usage(state);
                }
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
int do_check(Query parse_tree, int verbose) {
    if (verbose) {
        printf("\tRunning semantic checks...\n\n");
    }

    int check_status = checkSemantics(parse_tree);

    if (verbose && check_status == 0) {
        printf("\n\tSemantic Checks Completed: OK\n");
    } else if (verbose) {
        printf("\n\tSemantic Checks Completed: FAILED\n");
    }

    return check_status; // Return 0 on success, 1 on failure
}


static struct argp argp = {options, parse_opt, args_doc, usage_message, 0, 0, 0};


int main(int argc, char **argv) {
    struct arguments arguments; 
    int exit_status = EXIT_SUCCESS;

    arguments.mode = MODE_NONE;
    arguments.spec_file = NULL;
    arguments.verbose = 0;

    // 0. Parse command line arguments
    argp_parse(&argp, argc, argv, 0, 0, &arguments);

    if (arguments.verbose) {
        printf("\tVerbose mode enabled.\n");
        printf("\tRunning Check Mode\n");
        printf("\tSpec File: %s\n", arguments.spec_file);
    }

    // 1. Open the input file
    FILE *input_file = fopen(arguments.spec_file, "r");
    if (!input_file) {
        fprintf(stderr, "Error: Cannot open input file '%s': ", arguments.spec_file);
        return 1;
    }
    if (arguments.verbose) {
        printf("\tFile opened successfully: %s\n", arguments.spec_file);
    }

    // 2. Parse the file using the BNFC-generated parser
    Query parse_tree = pQuery(input_file);
    if (!parse_tree) {
        fprintf(stderr, "Error: Parsing failed.\n");
        return 1;
    }

    if (arguments.verbose) {
        printf("\tParse tree generated successfully.\n\n");
        printf("[Linearized Tree]\n");
        printf("%s\n\n", printQuery(parse_tree));
    }

    // 3. Execute the check command
    if (arguments.mode == MODE_CHECK) { 
        if (do_check(parse_tree, arguments.verbose) != 0) {
            exit_status = EXIT_FAILURE;
        }
    } 

    // 4. Clean up the AST
    free_Query(parse_tree);
    if (arguments.verbose) {
        printf("\tParse tree freed successfully.\n");
    }

    return exit_status;
}