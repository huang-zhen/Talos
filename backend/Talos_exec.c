/*
 * Copyright (C) 2018 Zhen Huang
 */
#include <stdlib.h>
#include <stdio.h>

static char *EXEC_logfile = NULL;

void EXEC_log(const char *msg) {
	static FILE *fp = NULL;
	if (fp == NULL)
		fp = fopen(EXEC_logfile, "a");
	if (fp) {
		fprintf(fp, "%d:%s\n", getpid(), msg);
		fflush(fp);
	}
}

void EXEC_exit() {
	char buf[255];
	int i;

	for (i = 0; i < sizeof(EXEC_flags)/sizeof(EXEC_flags[0]); i++) {
		if (EXEC_flags[i]) {
			sprintf(buf, "%s %d", EXEC_flags_names[i], i);
			EXEC_log(buf);
		}
	}
	sprintf(buf, "Exiting...%s", EXEC_entry);
	EXEC_log(buf);
}

void EXEC_loader() {
	char buf[255];

	EXEC_logfile = getenv("TALOS_EXECLOG");
	if (!EXEC_logfile)
		EXEC_logfile = "/tmp/talos_exec.log";
	sprintf(buf, "Starting...%s", EXEC_entry);
	EXEC_log(buf);
	if (atexit(EXEC_exit) != 0)
		EXEC_log("Cannot set exit function");
}

