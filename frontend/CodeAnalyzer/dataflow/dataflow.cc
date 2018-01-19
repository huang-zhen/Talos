// dataflow.cc
//
// Copyright (C) 2016 Zhen Huang
//
#include <iostream>
#include <vector>
#include "dataflow.h"
#include "cfg.h"
using namespace std;

//#define DEBUG

Dataflow::Dataflow(Cfg *cfg, int size)
{
	m_cfg = cfg;
	m_set_size = size;
}

Dataflow::~Dataflow()
{
}

Bitvector Dataflow::meet(int block)
{
	Bitvector meet_set(m_set_size);
	vector<int> blocks;

	if (m_direction == FORWARD) {
		blocks = m_cfg->get_predecessors(block);
		
	} else {
		blocks = m_cfg->get_successors(block);
	}
	for (int i = 0; i < blocks.size(); i++) {
		Bitvector input(m_set_size);
		if (m_direction == FORWARD)
			input = m_out_set[blocks[i]];
		else
			input = m_in_set[blocks[i]];
		if (m_meet == ANYPATH) {
#ifdef DEBUG
			cout << block << ":union " << blocks[i] << ": ";
			input.print();
			cout << endl;
#endif
			if (i == 0)
				meet_set = input;
			else
				meet_set.merge(input);
		} else {
#ifdef DEBUG
			cout << block << ":intersect " << blocks[i] << ": ";
			input.print();
			cout << endl;
#endif
			if (i == 0)
				meet_set = input;
			else
				meet_set.intersect(input);
		}
	}
	return meet_set;
}

void Dataflow::analyze()
{
	int bb_count = m_cfg->get_basicblockcount();

	// Initialize
	for (int i = 0; i < bb_count; i++) {
		m_in_set.push_back(get_init_in_set(i));
		m_out_set.push_back(get_init_out_set(i));
	}
	if (m_direction == FORWARD) {
		for (int i = 0; i < bb_count; i++)
			m_worklist.push(i);
	} else {
		for (int i = bb_count - 1; i >= 0; i--)
			m_worklist.push(i);
	}

	// Iterate
	while (!m_worklist.empty()) {
		int b = m_worklist.front();
		m_worklist.pop();

		if (m_direction == FORWARD) {
			m_in_set[b] = meet(b);
			Bitvector old_out_set = m_out_set[b];
			Bitvector temp = m_in_set[b];
			temp.diff(get_kill_set(b));
			m_out_set[b] = get_gen_set(b);
			m_out_set[b].merge(temp);
			if (old_out_set != m_out_set[b]) {
				vector<int> succ = m_cfg->get_successors(b);
				for (int i = 0; i < succ.size(); i++)
					m_worklist.push(succ[i]);
			}
		} else {
			m_out_set[b] = meet(b);
			Bitvector old_in_set = m_in_set[b];
			Bitvector temp = m_out_set[b];
			temp.diff(get_kill_set(b));
			m_in_set[b] = get_gen_set(b);
			m_in_set[b].merge(temp);
			if (old_in_set != m_in_set[b]) {
				vector<int> pred = m_cfg->get_predecessors(b);
				for (int i = 0; i < pred.size(); i++)
					m_worklist.push(pred[i]);
			}
		}
#ifdef DEBUG
		cout << "out(" << b << "): ";
		m_out_set[b].print();
		cout << endl;
		cout << "in(" << b << "): ";
		m_in_set[b].print();
		cout << endl;
#endif
	}
}

Bitvector Dataflow::get_in_set(int block)
{
	return m_in_set[block];
}

vector<Bitvector> Dataflow::get_in_sets()
{
	return m_in_set;
}

vector<Bitvector> Dataflow::get_out_sets()
{
	return m_out_set;
}

