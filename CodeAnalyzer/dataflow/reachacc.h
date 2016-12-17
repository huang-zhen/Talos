#ifndef REACHACC_H
#define REACHACC_H

#include "bitvector.h"
#include "dataflow.h"

class ReachAcc : public Dataflow {
public:
		ReachAcc(Cfg *cfg, int size);
private:
		virtual Bitvector get_init_in_set(int);
		virtual Bitvector get_init_out_set(int);
		virtual Bitvector get_gen_set(int);
		virtual Bitvector get_kill_set(int);
};
#endif	
