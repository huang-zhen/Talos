// ipc_lock.h
#ifndef IPC_LOCK_H
class IPC_Lock {
public:
	IPC_Lock(const char *name);
	~IPC_Lock();
	int lock(const char *tag);
	void unlock(const char *tag);
private:
	static int initialized;
	void *ptr;
	int fd;
	size_t sz;
};
#endif
