#include <stdio.h>
#include <stdlib.h>

typedef int (*handler_func_type)(int a);

int my_power(int a, int n) {
	if (n == 0)
		return 1;
	else
		return a * my_power(a, n - 1);
}

int my_handler(int a) {
	return my_power(a, 2);
}

typedef struct {
	handler_func_type handler;
} handler_info_type;

handler_info_type handler_info = {
	my_handler,
};

// return 0 on success, non-zero on error
int update_data(const char *dat_file) {
	int data;
	FILE *fp = NULL;
	char *outfile = NULL;

	fp = fopen(dat_file, "rb");
	if (fp == NULL) {
		printf("Error openning %s\n", dat_file);
		return -1;
	}
	if (fread(&data, sizeof(data), 1, fp) != 1) {
		printf("Error reading %s\n", dat_file);
		return -2;
	}
	fclose(fp);
	data = handler_info.handler(data);
	outfile = getenv("OUTFILE");
	if (outfile) {
		fp = fopen(outfile, "w");
		if (fp == NULL) {
			printf("Error openning %s\n", outfile);
			return -3;
		}
		fprintf(fp, "Data: %d\n", data);
		fclose(fp);
	} else
		printf("Data: %d\n", data);
	return 0;
}

int main(int argc, char *argv[]) {
	if (argc < 2) {
		printf("Usage: print input_file\n");
		return 0;
	}
	if (!update_data(argv[1]))
		printf("Data is updated\n");
	else
		printf("Data is not updated\n");
	return 0;
}

