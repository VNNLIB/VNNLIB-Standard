#include "VNNLib.h"


/**
 * Parse a VNNLib specification from a file
 * @param path The path to the VNNLib file.
 * @return A pointer to the parsed Query object, or NULL on failure.
 */
Query parse_vnnlib(const char* path) {
	FILE *file = fopen(path, "r");
	if (!file) {
		perror("Failed to open file");
		return NULL;
	}

	Query query = pQuery(file);
	fclose(file);

	if (!query) {
		fprintf(stderr, "Failed to parse VNNLib file.\n");
		return NULL;
	}

	return query;
}


/**
 * Parse a VNNLib specification from a string
 * @param str The VNNLib string to parse.
 * @return A pointer to the parsed Query object, or NULL on failure.
 */
Query parse_vnnlib_str(const char* str) {
	Query query = psQuery(str);

	if (!query) {
		fprintf(stderr, "Failed to parse VNNLib string.\n");
		return NULL;
	}

	return query;
}


/**
 * Free a VNNLib query.
 * @param q The query to free.
 */
void free_query(Query q) {
	free_Query(q);
}


/** 
 * Write a VNNLib query to a file.
 * @param q The query to write.
 * @param path The path to the file to write.
 * @return 0 on success, -1 on failure.
 */
int write_vnnlib(const Query q, const char* path) {
	FILE *file = fopen(path, "w");
	if (!file) {
		perror("Failed to open file for writing");
		return -1;
	}

	char *vnnlib_str = showQuery(q);
	if (!vnnlib_str) {
		fprintf(stderr, "Failed to convert VNNLib query to string.\n");
		fclose(file);
		return -1;
	}

	int result = fprintf(file, "%s", vnnlib_str);
	if (result != 0) {
		fprintf(stderr, "Failed to write VNNLib file.\n");
		return -1;
	}
	
	fclose(file);
	free(vnnlib_str);

	return 0;
}


/**
 * Write a VNNLib query to a string.
 * @param q The query to write.
 * @return A string containing the VNNLib representation of the query. The caller is responsible for freeing this string.
 */
char* write_vnnlib_str(const Query q) {
	char *vnnlib_str = showQuery(q);
	if (!vnnlib_str) {
		fprintf(stderr, "Failed to convert VNNLib query to string.\n");
	}
	return vnnlib_str;
}


/**
 * Check the semantic correctness of a VNNLib query.
 * @param q The query to check.
 * @param json If 1, return errors in JSON format; otherwise, return in plain text.
 * @return A string containing the error report. The caller is responsible for freeing this string.
 */
char* check_query(const Query q, int json) {
	char *errorReport = NULL;

    SemanticContext ctx;
    initSemanticContext(&ctx);

    // Start traversal
    checkQuery(q, &ctx);

    // Check for semantic errors
    if (ctx.errorCount > 0) {
        if (json) {
            errorReport = reportErrorsJSON(&ctx);
        } else {
            errorReport = reportErrors(&ctx);
        }
    }

	// Free the semantic context
	destroySemanticContext(&ctx);

	return errorReport;
}

