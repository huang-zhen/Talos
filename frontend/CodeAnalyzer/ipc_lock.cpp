/*
 * Copyright (C) 2016 Zhen Huang
 */

#include <iostream>
#include <sys/mman.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <semaphore.h>
#include <errno.h>
#include <unistd.h>
#include <sys/types.h>
#include "ipc_lock.h"

IPC_Lock::IPC_Lock(const char *name) {
	ptr = NULL;
#if 1
	fd = shm_open(name, O_CREAT|O_RDWR|O_EXCL, 0644);
	if (fd == -1) {
		if (errno != EEXIST) {
			std::cerr << "shm_open failed with " << errno << std::endl;
			return;
		}
		fd = shm_open(name, O_RDWR, 0644);
		sz = sizeof(sem_t);
		ftruncate(fd, sz);
		ptr = mmap(0, sz, PROT_READ|PROT_WRITE, MAP_SHARED, fd, 0);
		std::cerr << "open " << ptr << std::endl;
	} else {
		sz = sizeof(sem_t);
		ftruncate(fd, sz);
		ptr = mmap(0, sz, PROT_READ|PROT_WRITE, MAP_SHARED, fd, 0);
		std::cerr << "create " << ptr << std::endl;
		sem_init((sem_t *)ptr, 1, 1);
	}
#else
	ptr = sem_open(name, O_CREAT|O_RDWR, 0644, 1);
#endif
}

IPC_Lock::~IPC_Lock() {
	if (ptr) {
#if 1
		munmap(ptr, sz);
#else
		sem_close((sem_t *)ptr);
#endif
	}
}

int IPC_Lock::lock(const char *tag) {
	std::cerr << tag << ":ipc_lock lock " << ptr << std::endl;
	if (ptr) {
		sem_wait((sem_t *)ptr);
		return 0;
	} else {
		std::cerr << "ipc_lock lock failed" << std::endl;
		return -1;
	}
}

void IPC_Lock::unlock(const char *tag) {
	std::cerr << tag << ":ipc_lock unlock " << ptr << std::endl;
	if (ptr) {
		sem_post((sem_t *)ptr);
	}
}

