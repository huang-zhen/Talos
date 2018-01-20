/*
 * Copyright (C) 2018 Zhen Huang
 */
#include <stdlib.h>
#include <stdio.h>
#include <time.h>

static char *SWRR_logfile = NULL;

void SWRR_log(const char *msg) {
	static FILE *fp = NULL;
	if (fp == NULL)
		fp = fopen(SWRR_logfile, "a");
	if (fp)
		fprintf(fp, "%s\n", msg);
}

void SWRR_exit() {
	char buf[255];

	sprintf(buf, "Exiting...%s", SWRR_entry);
	SWRR_log(buf);
}

void SWRR_loader() {
	int i;
	char buf[255];

	SWRR_logfile = getenv("TALOS_SWRRLOG");
	if (!SWRR_logfile)
		SWRR_logfile = "/tmp/talos_swrr.log";
	time_t t;
	time(&t); 
	sprintf(buf, "%s Starting...%s", ctime(&t), SWRR_entry);
	SWRR_log(buf);
	if (atexit(SWRR_exit) != 0)
		SWRR_log("Cannot register exit function!");
	for (i = 0; i < sizeof(SWRR_flags_names)/sizeof(SWRR_flags_names[0]); i++) {
		if (getenv(SWRR_flags_names[i])) {
			SWRR_flags[i] = 1;
			sprintf(buf, "%s %d", SWRR_flags_names[i], i);
			SWRR_log(buf);
		}
	}
}

