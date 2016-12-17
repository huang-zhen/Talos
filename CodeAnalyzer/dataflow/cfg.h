#ifndef CFG_H
#define CFG_H

#include <vector>
#include "bitvector.h"

class Cfg {
	public:
		virtual ~Cfg() {}; 
		virtual int get_basicblockcount() = 0;
		virtual std::vector<int> get_predecessors(int block) = 0;
		virtual std::vector<int> get_successors(int block) = 0;
		//virtual Bitvector get_use_set(int block) = 0;
		//virtual Bitvector get_def_set(int block) = 0;
		virtual Bitvector get_access_set(int block) = 0;
		virtual Bitvector get_gen_set(int block) = 0;
		virtual Bitvector get_kill_set(int block) = 0;
};

#endif

