#define _GNU_SOURCE 
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "SemanticChecker.h"
#include "Parser.h"
#include "Absyn.h"


// --- Program Information ---
static const char *usage_message =
    "Usage: parser check VNNLIBFILE [-v] [-o FILE]\n\n"
    "  MODE:\n"
    "    check        Parse and perform semantic checks on the VNNLIB file.\n\n"
    "  ARGUMENTS:\n"
    "    VNNLIBFILE   Path to the input VNNLIB specification file.\n\n"
    "  OPTIONS:\n"
    "    -v, --verbose  Produce verbose output.\n"
    "    -o FILE        Specify output file (usage may depend on future modes).\n"
    "                   Default is '-' for stdout.\n"
    "    -h, --help     Display this help message and exit.\n";


// --- Mode Definition (Simplified) ---
typedef enum {
    MODE_NONE,
    MODE_CHECK 
} parser_mode_t;


// --- Arguments Structure (Simplified) ---
struct arguments {
    parser_mode_t mode;
    char *spec_file;        
    char *output_file;     
    int verbose;          
};


// --- Helper function for usage ---
void usage(const char *prog_name) {
    fprintf(stderr, "%s\n", usage_message);
}

// --- Mode Execution Functions ---


/**
 * @brief Executes the check command: Parses the input file and runs semantic checks.
 * (Implementation kept exactly as provided by user)
 * @param args Parsed command line arguments.
 * @return int 0 on success (parsing and semantic checks passed), 1 on failure.
 */
int do_check(struct arguments *args) {
    if (args->verbose) {
        printf("  Verbose mode enabled.\n");
        printf("--- Running Check Mode ---\n");
        printf("  Spec File: %s\n", args->spec_file);
    }

    FILE *input_file = NULL;
    Query parse_tree = NULL;

    // 1. Open the input file
    input_file = fopen(args->spec_file, "r");
    if (!input_file) {
        fprintf(stderr, "Error: Cannot open input file '%s': ", args->spec_file);
        perror(NULL); // Prints the OS error message
        return 1;
    }

    if (args->verbose) {
        printf("  File opened successfully: %s\n", args->spec_file);
    }

    // 2. Parse the file using the BNFC-generated parser
    parse_tree = pQuery(input_file);
    fclose(input_file);

    if (!parse_tree) {
        fprintf(stderr, "Error: Parsing failed.\n");
        return 1;
    }

    if (args->verbose) {
        printf("  Parse tree generated successfully.\n");
        printf("[Linearized Tree]\n");
        printf("%s\n\n", printQuery(parse_tree));
    }

    // 3. Perform Semantic Checks
    if (args->verbose) {
        printf("  Running semantic checks...\n");
    }

    int check_status = checkSemantics(parse_tree);

    if (args->verbose && check_status == 0) {
        printf("--- Semantic Checks Completed: OK ---\n");
    } else if (args->verbose) {
        printf("--- Semantic Checks Completed: FAILED ---\n");
    }

    // 4. Clean up the AST
    free_Query(parse_tree);
    if (args->verbose) {
        printf("  AST freed.\n");
    }

    return check_status; // Return 0 on success, 1 on failure
}


// --- Main Function ---
int main(int argc, char **argv) {
    struct arguments arguments; 
    int exit_status = EXIT_SUCCESS;

    arguments.mode = MODE_NONE;
    arguments.spec_file = NULL;
    arguments.output_file = "-"; // Default to stdout
    arguments.verbose = 0;

    // --- Manual Argument Parsing ---
    int positional_arg_index = 0; // To track 'check' and 'filename'

    for (int i = 1; i < argc; ++i) {
        // Check for options first
        if (strcmp(argv[i], "-v") == 0 || strcmp(argv[i], "--verbose") == 0) {
            arguments.verbose = 1;
        } else if (strcmp(argv[i], "-o") == 0) {
            if (i + 1 < argc) { // Check if filename exists after -o
                arguments.output_file = argv[i + 1];
                i++; // Consume the filename argument
            } else {
                fprintf(stderr, "Error: Missing filename after -o option.\n");
                usage(argv[0]);
                return EXIT_FAILURE;
            }
        } else if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
            usage(argv[0]);
            return EXIT_SUCCESS;
        } else if (argv[i][0] == '-') {
             fprintf(stderr, "Error: Unknown option '%s'.\n", argv[i]);
             usage(argv[0]);
             return EXIT_FAILURE;
        } else {
            // Positional argument processing
            if (positional_arg_index == 0) { // Expecting mode
                if (strcmp(argv[i], "check") == 0) {
                    arguments.mode = MODE_CHECK;
                } else {
                    fprintf(stderr, "Error: Unknown or unsupported mode '%s'. Only 'check' is currently supported.\n", argv[i]);
                    usage(argv[0]);
                    return EXIT_FAILURE;
                }
            } else if (positional_arg_index == 1) { // Expecting filename
                arguments.spec_file = argv[i];
            } else { // Too many positional arguments
                fprintf(stderr, "Error: Too many positional arguments. Unexpected argument: '%s'\n", argv[i]);
                usage(argv[0]);
                return EXIT_FAILURE;
            }
            positional_arg_index++;
        }
    }

    // --- Validation after parsing loop ---
    if (argc <= 1) { // No arguments provided at all
        usage(argv[0]);
        return EXIT_FAILURE;
    }

    if (arguments.mode != MODE_CHECK) {
         fprintf(stderr, "Error: Mode 'check' must be specified as the first non-option argument.\n");
         usage(argv[0]);
         return EXIT_FAILURE;
    }
    if (arguments.spec_file == NULL) {
         fprintf(stderr, "Error: Input VNNLIB file must be specified after 'check'.\n");
         usage(argv[0]);
         return EXIT_FAILURE;
    }

    // --- Execute the selected mode ---
    if (arguments.mode == MODE_CHECK) { 
        if (do_check(&arguments) != 0) {
            exit_status = EXIT_FAILURE;
        }
    } 

    return exit_status;
}