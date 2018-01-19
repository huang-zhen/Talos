// ReachDef
// 
// Copyright (C) 2016 Zhen Huang
//
#include "reachdef.h"

ReachDef::ReachDef(Cfg *cfg, int size) : Dataflow(cfg, size)
{
	m_direction = FORWARD;
	m_meet = ANYPATH;
}

Bitvector ReachDef::get_init_in_set(int block)
{
	Bitvector bv(m_set_size);

	return bv;
}

Bitvector ReachDef::get_init_out_set(int block)
{
	Bitvector bv(m_set_size);

	return bv;
}

Bitvector ReachDef::get_gen_set(int block)
{
	Bitvector bv(m_set_size);
	bv = m_cfg->get_gen_set(block);

	return bv;
}

Bitvector ReachDef::get_kill_set(int block)
{
	Bitvector bv(m_set_size);
	bv = m_cfg->get_kill_set(block);

	return bv;
}

