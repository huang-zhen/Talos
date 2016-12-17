// bitvector.cc
// 
// Copyright (C) 2016 Zhen Huang
//
#include <iostream>
#include "bitvector.h"
using namespace std;

Bitvector::Bitvector(int size)
{
	for (int i = 0; i < size; i++)
		m_bits.push_back(0);
}

Bitvector::~Bitvector()
{
}

int Bitvector::size() const
{
	return m_bits.size();
}

void Bitvector::merge(Bitvector bv)
{
	for (int i = 0; i < m_bits.size(); i++)
		m_bits[i] |= bv.get(i); 
}

void Bitvector::intersect(Bitvector bv)
{
	for (int i = 0; i < m_bits.size(); i++)
		m_bits[i] &= bv.get(i); 
}

void Bitvector::diff(Bitvector bv)
{
	for (int i = 0; i < m_bits.size(); i++)
		if (m_bits[i] & bv.get(i))
			m_bits[i] = 0;
}

Bitvector& Bitvector::operator=(const Bitvector bv)
{
	m_bits.resize(bv.size());
	for (int i = 0; i < m_bits.size(); i++)
		m_bits[i] = bv.get(i); 
}

bool Bitvector::operator==(const Bitvector bv)
{
	for (int i = 0; i < m_bits.size(); i++)
		if (m_bits[i] != bv.get(i))
			return false;
	return true;
}

bool Bitvector::operator!=(const Bitvector bv)
{
	for (int i = 0; i < m_bits.size(); i++)
		if (m_bits[i] != bv.get(i))
			return true;
	return false;
}

/*
bool Bitvector::get(int bit) const
{
	return m_bits[bit];
}

void Bitvector::set(int bit, bool val)
{
	m_bits[bit] = val;
}
*/

void Bitvector::print() const
{
	for (int i = 0; i < m_bits.size(); i++) {
		cout <<	m_bits[i]? '1' : '0';
	}
}

string Bitvector::tostring() const
{
	string str;
	
	for (int i = 0; i < m_bits.size(); i++) {
		str.append(m_bits[i]? "1" : "0");
	}
	return str;
}

