// bitvector.cc
#include <iostream>
//#include <assert.h>
#include <string.h>
#include "bitvector.h"
using namespace std;

#define BITS_UNIT 32

Bitvector::Bitvector(int size)
{
	//std::cerr << "Bitvector " << this << ':' << size << std::endl;
	m_bsize = size;
	m_size = (size%BITS_UNIT==0)? size/BITS_UNIT : size/BITS_UNIT + 1;
	m_bits = new int[m_size];
	//for (int i = 0; i < m_size; i++)
	//	m_bits[i] = 0;
	memset(m_bits, 0, m_size * sizeof(int));
}

Bitvector::Bitvector(unsigned char a[], int size)
{
	//std::cerr << "Bitvector " << this << ':' << size << std::endl;
	m_bsize = size;
	m_size = (size%BITS_UNIT==0)? size/BITS_UNIT : size/BITS_UNIT + 1;
	m_bits = new int[m_size];
	//for (int i = 0; i < m_size; i++)
	//	m_bits[i] = 0;
	memset(m_bits, 0, m_size * sizeof(int));
	for (int i = 0; i < size; i++)
		m_bits[i/BITS_UNIT] = m_bits[i/BITS_UNIT] | a[i] << (i % BITS_UNIT);
}

Bitvector::Bitvector(const Bitvector& bv)
{
	m_bsize = bv.m_bsize;
	m_size = bv.m_size;
	m_bits = new int[m_size];
	//for (int i = 0; i < m_size; i++)
	//	m_bits[i] = bv.m_bits[i];
	memcpy(m_bits, bv.m_bits, m_size * sizeof(int));
}

Bitvector::~Bitvector()
{
	//std::cerr << "~Bitvector " << this << std::endl;
	delete[] m_bits;
}

int Bitvector::size() const
{
	return m_bsize;
}

void Bitvector::merge(const Bitvector& bv)
{
	//assert(m_bsize == bv.m_bsize);
	for (int i = 0; i < m_size; i++)
		m_bits[i] |= bv.m_bits[i]; 
}

void Bitvector::intersect(const Bitvector& bv)
{
	//assert(m_bsize == bv.m_bsize);
	for (int i = 0; i < m_size; i++)
		m_bits[i] &= bv.m_bits[i]; 
}

void Bitvector::diff(const Bitvector& bv)
{
	//assert(m_bsize == bv.m_bsize);
	for (int i = 0; i < m_size; i++) {
		int temp = m_bits[i];
		m_bits[i] ^= bv.m_bits[i];
		m_bits[i] &= temp;
	}
}

Bitvector& Bitvector::operator=(const Bitvector& bv)
{
	//assert(m_bsize == bv.m_bsize);
	//for (int i = 0; i < m_size; i++)
	//	m_bits[i] = bv.m_bits[i]; 
	memcpy(m_bits, bv.m_bits, m_size * sizeof(int));
}

bool Bitvector::operator==(const Bitvector& bv)
{
	for (int i = 0; i < m_size; i++)
		if (m_bits[i] != bv.m_bits[i])
			return false;
	return true;
}

bool Bitvector::operator!=(const Bitvector& bv)
{
	for (int i = 0; i < m_size; i++)
		if (m_bits[i] != bv.m_bits[i])
			return true;
	return false;
}

bool Bitvector::get(int bit) const {
	int i = bit/BITS_UNIT;
	return (m_bits[i]>>(bit%BITS_UNIT) & 1UL);
};

void Bitvector::set(int bit, bool val) {
	int i = bit/BITS_UNIT;
	m_bits[i] ^= (-(unsigned int)val ^ m_bits[i]) & (1UL << (bit%BITS_UNIT));
};

void Bitvector::print() const
{
	cout << tostring();
}

string Bitvector::tostring() const
{
	string str;
	
	for (int i = 0; i < m_bsize; i++) {
		str.append(get(i)? "1" : "0");
	}
	return str;
}

unsigned char *Bitvector::toarray(int& size) const
{
	unsigned char *a = new unsigned char(m_bsize);
	for (int i = 0; i < m_bsize; i++)
		a[i] = get(i);
	size = m_bsize;
	return a;
}

