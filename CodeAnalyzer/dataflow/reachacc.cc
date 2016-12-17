// ReachAcc
//
// Copyright (C) 2016 Zhen Huang
//
#include "reachacc.h"

ReachAcc::ReachAcc(Cfg *cfg, int size) : Dataflow(cfg, size)
{
	m_direction = FORWARD;
	m_meet = ANYPATH;
}

Bitvector ReachAcc::get_init_in_set(int block)
{
	Bitvector bv(m_set_size);

	return bv;
}

Bitvector ReachAcc::get_init_out_set(int block)
{
	Bitvector bv(m_set_size);

	return bv;
}

Bitvector ReachAcc::get_gen_set(int block)
{
	Bitvector bv(m_set_size);
	bv = m_cfg->get_access_set(block);

	return bv;
}

Bitvector ReachAcc::get_kill_set(int block)
{
	Bitvector bv(m_set_size);

	return bv;
}
