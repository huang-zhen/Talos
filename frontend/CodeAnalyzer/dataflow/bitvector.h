#ifndef BITVECTOR_H
#define BITVECTOR_H

#include <vector>
#include <string>

class Bitvector {
public:
	int *m_bits;
	int m_size; // size of m_bits
	int m_bsize; // size in bits
	Bitvector(int size);
	Bitvector(unsigned char a[], int size);
	Bitvector(const Bitvector& bv);
	~Bitvector();
	int size() const;
	bool get(int bit) const;
	void set(int bit, bool val);
	void merge(const Bitvector& bv);
	void diff(const Bitvector& bv);
	void intersect(const Bitvector& bv);
	void print() const;
	void operator=(const Bitvector& bv);
	bool operator!=(const Bitvector& bv);
	bool operator==(const Bitvector& bv);
	std::string tostring() const;
	unsigned char *toarray(int &size) const;
};

#endif
