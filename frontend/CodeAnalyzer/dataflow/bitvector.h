#ifndef BITVECTOR_H
#define BITVECTOR_H

#include <vector>
#include <string>

class Bitvector {
private:
	std::vector<unsigned char> m_bits;
public:
	Bitvector(int size);
	~Bitvector();
	int size() const;
	void merge(Bitvector bv);
	void diff(Bitvector bv);
	void intersect(Bitvector bv);
	void print() const;
	Bitvector& operator=(const Bitvector bv);
	bool operator!=(const Bitvector bv);
	bool operator==(const Bitvector bv);
	bool get(int bit) const {
		return m_bits[bit];
	};
	void set(int bit, bool val) {
		m_bits[bit] = val;
	};
	std::string tostring() const;
};

#endif
