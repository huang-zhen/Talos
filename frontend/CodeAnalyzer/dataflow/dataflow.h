#ifndef DATAFLOW_H
#define DATAFLOW_H

#include <queue>
#include <vector>
#include "bitvector.h"
#include "cfg.h"

class Dataflow {
private:
	// variables
	std::vector<Bitvector > m_in_set;
	std::vector<Bitvector > m_out_set;
	std::queue<int> m_worklist;

	// methods
	Bitvector meet(int block);
protected:
	Cfg *m_cfg;
	int m_set_size;
	virtual Bitvector get_gen_set(int) = 0;
	virtual Bitvector get_kill_set(int) = 0;
	virtual Bitvector get_init_in_set(int block_num) = 0;
	virtual Bitvector get_init_out_set(int block_num) = 0;

	enum Direction {
		FORWARD,
		BACKWARD
	};
	enum Meet {
		ANYPATH,
		ALLPATH
	};
	Direction m_direction;
	Meet m_meet;
public:
	Dataflow(Cfg *cfg, int size);
	virtual ~Dataflow();
	void analyze();
	Bitvector get_in_set(int);
	std::vector<Bitvector> get_in_sets();
	std::vector<Bitvector> get_out_sets();
};

#endif
