#ifndef REACHDEF_H
#define REACHDEF_H

#include "bitvector.h"
#include "dataflow.h"

class ReachDef : public Dataflow {
public:
		ReachDef(Cfg *cfg, int size);
private:
		virtual Bitvector get_init_in_set(int);
		virtual Bitvector get_init_out_set(int);
		virtual Bitvector get_gen_set(int);
		virtual Bitvector get_kill_set(int);
};
#endif	
