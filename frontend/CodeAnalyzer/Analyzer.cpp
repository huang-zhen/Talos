/*
 * CodeAnalyzer
 * 
 * Copyright (C) 2016 Zhen Huang
 */

#define DEBUG_TYPE "Analyzer"
#include <list>
#include <string>
#include <fstream>
#include <sstream>
#include <set>
#include <cxxabi.h>
#include <iostream>
#include <utility>
#include <algorithm>

#define LLVM_VERSION(major, minor) (((major) << 8) | (minor))
#define LLVM_VERSION_CODE LLVM_VERSION(LLVM_VERSION_MAJOR, LLVM_VERSION_MINOR)

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Constant.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Operator.h"
#include <map>

#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/IR/DerivedTypes.h"
//#include "llvm/TypeSymbolTable.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

#include "llvm/IR/CallingConv.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 8)
#include "llvm/IR/InstIterator.h"
#else
#include "llvm/Support/InstIterator.h"
#endif
// LLVM 3.3
//#include "llvm/IR/CFG.h"
// LLVM 3.4.2
#include "llvm/Analysis/CFG.h"
// LLVM 3.3
//#include "llvm/IR/InstIterator.h"
// LLVM 3.4.2
#include "llvm/Support/Debug.h"
// LLVM 3.3
//#include "llvm/IR/CallSite.h"
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 8)
#include "llvm/IR/CallSite.h"
#else
#include "llvm/Support/CallSite.h"
#endif
// LLVM 3.3
//#include "llvm/IR/DebugInfo.h"
// LLVM 3.4.2
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 8)
#include "llvm/IR/DebugInfo.h"
#else
#include "llvm/DebugInfo.h"
#endif
#include "llvm/Analysis/PostDominators.h"
// LLVM 3.3
//#include "llvm/IR/Dominators.h"
// LLVM 3.4.2
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 8)
#include "llvm/IR/Dominators.h"
#else
#include "llvm/Analysis/Dominators.h"
#endif
#include "llvm/Support/CommandLine.h"

#include "dataflow/cfg.h"
#include "dataflow/bitvector.h"
#include "dataflow/reachacc.h"
#include "dataflow/reachdef.h"

#include "ipc_lock.h"

using namespace llvm;

static cl::opt<std::string> AnalyzerOutput("analyzer-output", cl::desc("Specify output filename"), cl::Required);
static cl::opt<std::string> AnalyzerCfg("analyzer-config", cl::desc("Specify configuration filename"), cl::Required);
static cl::opt<bool> AnalyzerUseGV("analyzer-globalvar", cl::desc("Include global variables in the analysis"), cl::init(false));

//#define DEBUG2 - general
//#define DEBUG3  // including control flow analysis and data flow analysis

#ifdef DEBUG
#undef DEBUG
#define DEBUG(a) a
#endif

namespace {
  // Analyzer
	typedef std::map<Value*, std::string> VarMap;
	std::string errout;
	raw_string_ostream errrawout(errout);
	//int accesses = 0;
	//int unmatched = 0;

	class LLVMCfg : public Cfg {
		private:
		int m_accesscount;
		int m_basicblockcount;
		std::vector<std::vector<int> > m_predecessors;
		std::vector<std::vector<int> > m_successors;
		std::vector<Bitvector*> m_access_sets;
		std::vector<Bitvector*> m_gen_sets;
		std::vector<Bitvector*> m_kill_sets;
		std::map<BasicBlock *, int> m_blocknums;
		std::map<Instruction *, int> m_accessnums;
		std::map<int, Instruction *> m_accessnums_rev;
		std::vector<int> m_accessmatches;

		int m_definitioncount;
		std::map<Value *, std::list<int> > m_definitions;	// pointer -> def1, def2, ...
		std::map<Instruction *, int> m_definitionnums;		// def -> id
		std::map<int, Instruction *> m_definitionnums_rev;	// id -> def
		std::map<Instruction *, std::list<Instruction *> > m_use_def; // use -> def1, def2, ...

		int get_accesses(Function *F, VarMap& LSV) {
			int nAccess = 0;

			for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
				if (isa<LoadInst>(*I) || isa<StoreInst>(*I)) {
				  	Instruction *pi = dyn_cast<Instruction>(&*I);
				  	for (User::op_iterator i = pi->op_begin(), e = pi->op_end(); i != e; ++i) {
						Value *v = *i;
						if (LSV.find(v) != LSV.end()) {

							m_accessnums[&*I] = nAccess;
							m_accessnums_rev[nAccess] = &*I;
							m_accessmatches.push_back(0);
							nAccess++;
							break;
						}
					}
				}
			}
			return nAccess;
		}
		
		int get_definitions(Function *F) {
			int nDefinitions = 0;

			for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
				if (isa<StoreInst>(*I)) {
				  	StoreInst *pStore = dyn_cast<StoreInst>(&*I);
					m_definitionnums[pStore] = nDefinitions;
					Value *pointer = pStore->getPointerOperand();
					m_definitions[pointer].push_back(nDefinitions);
					m_definitionnums_rev[nDefinitions] = pStore;
					nDefinitions ++;
				}
			}
			return nDefinitions;
		}

		Bitvector* gen_BB_access(Function::iterator &BB) {
#ifdef DEBUG3
		      	DEBUG(errrawout << "========BB===========\n");
#endif
			Bitvector *bv = new Bitvector(m_accesscount);
		      	for (BasicBlock::iterator BI = BB->begin(), BE = BB->end();
			   BI != BE; ++BI) {
				Instruction *pi = dyn_cast<Instruction>(BI);
				if (m_accessnums.find(pi) != m_accessnums.end()) {
#ifdef DEBUG3
					DEBUG(errrawout << "*");
#endif
					bv->set(m_accessnums[pi], true);
				} else {
#ifdef DEBUG3
					DEBUG(errrawout << " ");
#endif
				}
#ifdef DEBUG3
			        DEBUG(errrawout << BI->getOpcodeName() << "\n");
#endif
			}
			return bv;
		}

		void gen_BB_definition(Function::iterator &BB) {
#ifdef DEBUG3
		      	DEBUG(errrawout << "========BB===========\n");
#endif
			Bitvector *genset = new Bitvector(m_definitioncount);
			Bitvector *killset = new Bitvector(m_definitioncount);
		      	for (BasicBlock::iterator BI = BB->begin(), BE = BB->end();
			   BI != BE; ++BI) {
				if (StoreInst *pStore = dyn_cast<StoreInst>(BI)) {
#ifdef DEBUG3
					DEBUG(errrawout << "Gen def" << m_definitionnums[pStore] << '\n');
#endif
					genset->set(m_definitionnums[pStore], true);
					Value *pointer = pStore->getPointerOperand();
					for (std::list<int>::iterator i = m_definitions[pointer].begin(); i != m_definitions[pointer].end(); i++) {
						if (*i != m_definitionnums[pStore]) {
#ifdef DEBUG3
							DEBUG(errrawout << "kill def" << *i << '\n');
#endif
							killset->set(*i, true);
						}
					}
				}
			}
			m_gen_sets.push_back(genset);
			m_kill_sets.push_back(killset);
		}

		public:
		LLVMCfg(Function *F, VarMap& LSV) {
		     	int nBB = 0;

			for (Function::iterator BB = F->begin(), E = F->end(); BB != E; ++BB) {
				BasicBlock *pBB = &(*BB);
				m_blocknums[pBB] = nBB++;
			}
			m_basicblockcount = nBB;
			
			// Do not use reaching access
			//m_accesscount = get_accesses(F, LSV);

			m_definitioncount = get_definitions(F);

			for (Function::iterator BB = F->begin(), E = F->end(); BB != E; ++BB) {
				std::vector<int> predecessors;
				for (pred_iterator PI = pred_begin(&(*BB)), E = pred_end(&(*BB)); PI != E; ++PI) {
					BasicBlock *pred = *PI;
					predecessors.push_back(m_blocknums[pred]);
				}
				m_predecessors.push_back(predecessors);

				std::vector<int> successors;
				for (succ_iterator PI = succ_begin(&(*BB)), E = succ_end(&(*BB)); PI != E; ++PI) {
					BasicBlock *succ = *PI;
					successors.push_back(m_blocknums[succ]);
				}
				m_successors.push_back(successors);
				// Do not use reaching access
				// m_access_sets.push_back(gen_BB_access(BB));
				gen_BB_definition(BB);
			}
		}
		~LLVMCfg() {}
		int get_basicblockcount() {
			return m_basicblockcount;
		}		
		std::vector<int> get_predecessors(int block) {
			return m_predecessors[block];
		}
		std::vector<int> get_successors(int block) {
			return m_successors[block];
		}
		Bitvector get_access_set(int block) {
			return *m_access_sets[block];
		}
		Bitvector get_gen_set(int block) {
			return *m_gen_sets[block];
		}
		Bitvector get_kill_set(int block) {
			return *m_kill_sets[block];
		}
		std::vector<int> get_accessmatches() {
			return m_accessmatches;
		}
		Value *get_lsv_use(Instruction *pi, VarMap& LSV) {
		  	for (User::op_iterator i = pi->op_begin(), e = pi->op_end(); i != e; ++i) {
				Value *v = *i;
				if (LSV.find(v) != LSV.end()) {
					return v;
				}
			}
			return NULL;
		}	

		void gen_use_def(Function *F, Dataflow *df) {
			std::vector<Bitvector> in_sets = df->get_in_sets();
			for (Function::iterator bb=F->begin(), bbEnd=F->end(); bb != bbEnd; ++bb){
				BasicBlock* pBB = &*bb;
				Bitvector bv = in_sets[m_blocknums[pBB]];
				for (BasicBlock::iterator i=bb->begin(), iend=bb->end(); i != iend; ++i){
					if (StoreInst *pStore = dyn_cast<StoreInst>(i)) {
						bv.set(m_definitionnums[pStore], true);
						Value *pointer = pStore->getPointerOperand();
						for (std::list<int>::iterator i = m_definitions[pointer].begin(); i != m_definitions[pointer].end(); i++) {
							if (*i != m_definitionnums[pStore]) {
								bv.set(*i, false);
							}
						}
					} else if (LoadInst *pLoad = dyn_cast<LoadInst>(i)) {
						std::list<Instruction *> li;
						for (int i = 0; i < bv.size(); i++)
							if (bv.get(i)) {
								StoreInst *pStore = dyn_cast<StoreInst>(m_definitionnums_rev[i]);
								if (pLoad->getPointerOperand() == pStore->getPointerOperand())
									li.push_back(m_definitionnums_rev[i]);
							}
						if (li.size() > 1) {
							DEBUG(errrawout << "Warning: more than one def for a use at line " << getLineNumber(pLoad) << '\n');
						}
						m_use_def[pLoad] = li;
					}
				}
			}
		}

		std::list<Instruction *> get_use_def(Instruction *use) {
			return m_use_def[use];
		}

		void dump() {
			for (int b = 0; b < get_basicblockcount(); ++b) {
				DEBUG(errrawout << "BasicBlock " << b << ":\n");
				DEBUG(errrawout << "\tsuccessors: ");
				std::vector<int> successors = get_successors(b);
				for (unsigned i = 0; i < successors.size(); ++i)
					DEBUG(errrawout << successors[i] << ' ');
				DEBUG(errrawout << "\n");
				DEBUG(errrawout << "\tpredecessors: ");
				std::vector<int> predecessors = get_predecessors(b);
				for (unsigned i = 0; i < predecessors.size(); ++i)
					DEBUG(errrawout << predecessors[i] << ' ');
				DEBUG(errrawout << "\n");
			}
		}

		void dump_definitions() {
			DEBUG(errrawout << "Definitions:\n");
			for (int i = 0; i < m_definitioncount; i++) {
				int line = getLineNumber(m_definitionnums_rev[i]);
				DEBUG(errrawout << i << ": " << line << '\n');
			}
			DEBUG(errrawout << "\nGen/Kill:\n");
			for (int i = 0; i < get_basicblockcount(); i++) {
				DEBUG(errrawout << "BB" << i << ":\n");
				DEBUG(errrawout << "\tgen: " << get_gen_set(i).tostring() << '\n');
				DEBUG(errrawout << "\tkill: " << get_kill_set(i).tostring() << '\n');
			}		
		}

		void dump_use_def() {
			DEBUG(errrawout << "Use-def:\n");
			for (std::map<Instruction *, std::list<Instruction *> >::iterator i = m_use_def.begin(); i != m_use_def.end(); i ++) {
				DEBUG(errrawout << getLineNumber(i->first) << '\n');
				for (std::list<Instruction *>::iterator ii = i->second.begin(); ii != i->second.end(); ii ++) {
					DEBUG(errrawout << '\t' << getLineNumber(*ii) << '\n');
				}
			}
		}

		int getLineNumber(Instruction *i) {
			int line = 0;

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 8)
			auto& Loc = i->getDebugLoc();
			if (Loc) 
				line = Loc.getLine();
#else
			if (MDNode *N = i->getMetadata("dbg")) {
			   DILocation Loc(N);
			   line = Loc.getLineNumber();
			}
#endif
			return line;
		}

#if 0
		void instrument(Function::iterator &BB, VarMap& LSV, Bitvector reachAcc, Constant *Begin_atomicFn, Constant *End_atomicFn, const Type *Int32) {
			std::vector<Instruction *> reached;

			for (int i = 0; i < reachAcc.size(); i++) {
				if (reachAcc.get(i)) {
					Instruction *ins = m_accessnums_rev[i];
					reached.push_back(ins);
				}
			}
			for (BasicBlock::iterator BI = BB->begin(), BE = BB->end(); BI != BE; ++BI) {
				Instruction *pi = dyn_cast<Instruction>(BI);
				BasicBlock::iterator BN = BI;
				++BN;
				if (m_accessnums.find(pi) != m_accessnums.end()) {
					int parm = m_accessnums[pi];
					std::vector<Value*> inst(1);
					inst[0] = ConstantInt::get(Int32, parm);
					CallInst::Create(Begin_atomicFn, inst.begin(), inst.end(), "", BI);
					Value *gv = get_lsv_use(pi, LSV);
					for (int i = 0; i < reached.size(); i++) {
						if (gv == get_lsv_use(reached[i], LSV)) {
							int parm = m_accessnums[reached[i]];
							std::vector<Value*> inst(1);
							inst[0] = ConstantInt::get(Int32, parm);
							CallInst::Create(End_atomicFn, inst.begin(), inst.end(), "", BN);
							m_accessmatches[parm] ++;
						}
					}
					reached.push_back(pi);
				}
			}
		}
#endif
	};

  struct APIMethodType {
	int type;
	int argNum;
	Constant *function;
	int references;
  };
  struct Analyzer : public ModulePass {
	std::map<int, std::map<const Instruction*, int> > lineID;
    static char ID; // Pass identification, replacement for typeid
    std::map<GlobalVariable, int> wordcounts; // Constant map for global variables

    std::map<std::string, APIMethodType> APIMethods;
    std::map<std::string, int> Structs;
    const PointerType *UIntPtr, *Int8Ptr;
    const Type *Int32;
    const Type *Void;
    std::stringstream output;
    std::set<Function *> traversedFunctions;
    std::map<std::string, std::string> demangled_names;
    static const char FIELD_SEP = '@';
    std::map<const BasicBlock*, std::set<std::pair<const Instruction*, int> > > dependency;
    bool includeGlobalVar;
	std::set<std::string> entryFunctions;
	std::set<std::string> simpleFunctions;

    LLVMCfg *cfg;
    Dataflow *df;
	std::map<std::string, std::string> internalFunctions;
	std::string ModuleName, File, Dir;
	int fp_count;
	std::map<std::string, std::set<int> > analyzed_lines;
	std::map<std::string, int> first_lines;
	std::map<const BasicBlock*, std::pair<int, std::string> > const_returns;
	std::map<const BasicBlock*, int> cond_const_returns;
	PostDominatorTree *postDT;
	DominatorTree *DT;
	std::set<Instruction *> checkedGuardingConditions;
	std::map<Value *, std::map<CallInst *, std::pair<int, int> > > CallErrorHandling;
	std::map<CallInst *, CmpInst *> checkedCalls;
	std::map<std::string, std::string> prototypes;
	std::map<std::string, std::pair<std::string, std::string> > FuncLocations; 

    Analyzer() : ModulePass(ID), cfg(NULL), df(NULL), fp_count(0) {}

	const std::string getLineID(const std::pair<const Instruction*, int>& ll) {
		// include callee name in BBDependency
		std::string callee_name;
		const BasicBlock *bb = ll.first->getParent();
		for (BasicBlock::const_reverse_iterator it = bb->rbegin(); it != bb->rend(); it++) {
			const Instruction *ci = &*it;
			if (const CallInst *pCall = dyn_cast<CallInst>(ci)) {
				Function *callee = pCall->getCalledFunction();
				if (callee) {
					callee_name = decorateInternalName(callee);
				}
				break;
			}
		}
		int line = getLineNumber(ll.first);
		int id;
		if (lineID.find(line) == lineID.end()) {
			lineID[line] = std::map<const Instruction*, int>();
			lineID[line][ll.first] = 0;
			id = 0;
		} else {
			if (lineID[line].find(ll.first) != lineID[line].end())
				id = lineID[line][ll.first];
			else {
				id = lineID[line].size();
				lineID[line][ll.first] = id;
			}
		}
		std::stringstream ss;
		ss << line;
		if (callee_name != "")
			ss << '.' << callee_name; 
		//if (id != 0)
		//	ss << '.' << id;
		ss << ';' << ll.second;
		return ss.str();
	}

    int loadCfg(Module &M) {
	//const char *cfgfile = getenv("ANALYZER_CFG");
	const char *cfgfile = AnalyzerCfg.c_str();
	if (cfgfile == NULL) {
		DEBUG(errrawout << "\nANALYZER_CFG not set\n");
		//return -1;
		cfgfile = "./analyzer.cfg";
	}
	std::ifstream infile;
	infile.open(cfgfile);
	if (infile.is_open()) {
		int line_no = 0;
		while (infile.good()) {
			std::string line;
			getline(infile, line);
			line_no ++;
			if (line[0] == '#')
				continue;
			if (line == "")
				continue;				
			std::stringstream ts(line);
			std::string field;
			int index, count;
			std::string name;
			APIMethodType method;
			for (count = 0; getline(ts, field, ','); count++) {
			}
			if (count >= 3) {
				std::stringstream ss(line);
				index = 0;
				while (getline(ss, field, ',')) {
					if (index == 0) {
						std::stringstream fs(field);
						fs >> method.type;
					} else if (index == count - 1) {
						std::stringstream fs(field);
						fs >> method.argNum;
					} else {
						// trim leading spaces
						size_t startpos = field.find_first_not_of(" \t");
						if(std::string::npos != startpos )
						{
						    field = field.substr( startpos );
						}
						if (name == "")
							name = field;
						else
							name += ", " + field;
					} 
					index++;
				}
				switch (method.type) {
				case 0:
				case 1:
				case 2:
					method.function = M.getFunction(name);
					// account for the first "this" argument of the call to a C++ method
					//if (name.find(':') != std::string::npos)
					//	method.argNum ++;
					method.references = 0;
					if (APIMethods.find(name) != APIMethods.end())
						DEBUG(errrawout << "Error at line " << line_no << " in " << cfgfile << ": " << "Duplicate entry\n");
					else {
#ifdef DEBUG2
						DEBUG(errrawout << "Adding method " << name << " argNum:" << method.argNum << '\n');
#endif
						APIMethods[name] = method;
					}
					break;
				case 3:
					name = "struct." + name;
					if (Structs.find(name) != Structs.end())
						DEBUG(errrawout << "Error at line " << line_no << " in " << cfgfile << ": " << "Duplicate entry\n");
					else {
#ifdef DEBUG2
						DEBUG(errrawout << "Adding struct " << name << '\n');
#endif
						Structs[name] = method.argNum;
					}
					break;
				case 4:
					entryFunctions.insert(name);
					break;
				case 5:
					break;
				case 6:
				case 7:
					break;
				case 8:
					DEBUG(errrawout << "Adding simple function " << name << '\n');
					simpleFunctions.insert(name);
					break;
				default:
					DEBUG(errrawout << "\nInvalid type at line " << line_no << " in " << cfgfile << '\n');
					break;
				}
			} else
				DEBUG(errrawout << "\nError at line " << line_no << " in " << cfgfile << '\n');
		}
		infile.close();
	} else {
		DEBUG(errrawout << "Error openning " << cfgfile << '\n');
		//return -1;
	}
	return 0;
    }
    virtual bool doInitialization(Module &M) {
		return false;// Did not change anything
	}

	void splitLocPath(DIScope *pLoc, std::string &Dir, std::string &File) {
			std::string path = pLoc->getDirectory();
			if (path[path.size() - 1] != '/')
				path += '/';
			std::string file = pLoc->getFilename();
			if (file.size() > 2) {
				if (file[0] == '.' && file[1] == '/') {
					file.erase(0, 2);
				}
			}
			if (file[0] == '/')
				path = file;
			else
				path += file;
			size_t pos = path.rfind('/');
			File = path.substr(pos + 1);
			Dir = path.substr(0, pos + 1);
			if (Dir[0] == '.')
				Dir = std::string(pLoc->getDirectory()) + Dir.substr(1);
			if (Dir[Dir.size() - 1] == '/')
				Dir.erase(Dir.size() - 1);
	}

	void getModulePath(Module &M) {
	  NamedMDNode *nmd = M.getNamedMetadata("llvm.dbg.cu");
	  if (nmd) {
	  	MDNode *md = nmd->getOperand(0);
		for (unsigned i = 0; i < md->getNumOperands(); i++) {
	  		if (DIFile *pLoc = dyn_cast<DIFile>(md->getOperand(i))) {
				Dir = pLoc->getDirectory();
				File = pLoc->getFilename();
				DEBUG(errrawout << "File: " << File << '\n');
				DEBUG(errrawout << "Directory: " << Dir << '\n');
				break;
			}
		}
	  }
	}

	void getFuncLocation(Module &M, Function *F) {
		std::string funcName = decorateInternalName(F);
		DEBUG(errrawout << "getFuncLocation " << funcName << '\n');
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 8)
		SmallVector<std::pair<unsigned, MDNode *>, 4> MDs;
		F->getAllMetadata(MDs);
		for (auto &MD : MDs) {
		  if (MDNode *N = MD.second) {
			 if (auto *subProgram = dyn_cast<DISubprogram>(N)) {
				FuncLocations[funcName] = std::make_pair(subProgram->getDirectory(), subProgram->getFilename());
				break;
			 }
		  }
		}
#endif
	}

    virtual bool runOnModule(Module &M) {
	  ModuleName = M.getModuleIdentifier();
      DEBUG(errrawout << "\nModule: " << ModuleName << '\n');
	  getModulePath(M);

      LLVMContext &Context = M.getContext();
      UIntPtr = Type::getInt32PtrTy(Context);
      Int32 = Type::getInt32Ty(Context);
      Int8Ptr = PointerType::get(Type::getInt8Ty(Context), 0);
      Void = Type::getVoidTy(Context);

      if (loadCfg(M) != 0)
		return true;

	//const char *outputfile = getenv("ANALYZER_OUTPUT");
	const char *outputfile = AnalyzerOutput.c_str();
	if (outputfile == NULL) {
		//return true;
		outputfile = "/tmp/analyzer.out";
		DEBUG(errrawout << "ANALYZER_OUTPUT not set " << "using " << outputfile << "\n");
	}
#if 0
 	const char *includeGlobalVarOpt = getenv("ANALYZER_GLOBALVAR");
	if (includeGlobalVarOpt) { 
		if (atoi(includeGlobalVarOpt)) {
			DEBUG(errrawout << "ANALYZER_GLOBALVAR is set to 1\n");
			includeGlobalVar = true;
		} else {
			DEBUG(errrawout << "ANALYZER_GLOBALVAR is set to 0\n");
			includeGlobalVar = false;
		}
	} else {
		DEBUG(errrawout << "ANALYZER_GLOBALVAR is not set\n");
		includeGlobalVar = false;
	}
#else
 	includeGlobalVar = AnalyzerUseGV; 
#endif
      for (Module::iterator F = M.begin(), E = M.end(); F != E; ++F) {
	Function *FunPtr = &*F;
	if (F->empty())
		continue;

	getFuncLocation(M, &*F);
	reachDefAnalysis(FunPtr);	// Initialize cfg, df, and use-def
	postDT = &getAnalysis<PostDominatorTree>(*F);
	// LLVM 3.3, 3.8
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 8)
	DT = &getAnalysis<DominatorTreeWrapperPass>(*F).getDomTree();
	// LLVM 3.4.2
#else
	DT = &getAnalysis<DominatorTree>(*F);
#endif
	checkedCalls.clear();
	checkedGuardingConditions.clear();
	findDependency(FunPtr);
    findConstReturn(FunPtr);
	labelSimplePath(FunPtr);
	findMethod(FunPtr);
      }	

	findFPinGV(M);
#ifdef DEBUG3
	for (std::map<std::string, APIMethodType>::iterator it = APIMethods.begin(); it != APIMethods.end(); it ++) {
		if (it->second.references == 0)
			DEBUG(errrawout << "Warning: API method " << it->first << " is never referenced!\n");
	}
#endif
	int tot_analyzed_lines = 0;
	for (std::map<std::string, std::set<int> >::iterator it = analyzed_lines.begin(); it != analyzed_lines.end(); it++) {
		tot_analyzed_lines += it->second.size();
		int first_line = 0;
		if (first_lines.find(it->first) != first_lines.end())
			first_line = first_lines[it->first];

		std::string funcDir = FuncLocations[it->first].first;
		std::string funcFile = FuncLocations[it->first].second;
		std::string protoType = prototypes[it->first];

		DEBUG(errrawout << "\t*Analyzed " << it->second.size() << "@" << first_line << " lines for " << it->first << ' ' << funcDir << '/' << funcFile << ' ' << protoType << '\n');
		std::stringstream ss;
		ss << it->second.size() << ';' << funcDir << '/' << funcFile << ';' << protoType;
		dumpCallEx(first_line, it->first, "", ss.str(), -2, 14, NULL, NULL);
	}
	DEBUG(errrawout << "Analyzed " << tot_analyzed_lines << " lines for " << Dir << '/' << File << '\n');
	//for (std::set<int>::iterator i = analyzed_lines.begin(); i != analyzed_lines.end(); i++)
	//		DEBUG(errrawout << "\tLine " << *i << '\n');
	IPC_Lock lock(outputfile);
	lock.lock(ModuleName.c_str());
	std::ofstream outfile;
	outfile.open(outputfile, std::fstream::out | std::fstream::app);
	if (!outfile.good()) {
		DEBUG(errrawout << "Failed to open " << outputfile << '\n');
		fprintf(stderr, "Failed to open %s\n", outputfile);
		return true;
	}
	outfile << output.str();
	outfile.close();

	std::cerr << errrawout.str();
	std::cerr.flush();

	lock.unlock(ModuleName.c_str());
	return true;
    }
	
	std::list<std::pair<Value *, std::string> > getDependentVars(Instruction *i) {
		std::list<std::pair<Value *, std::string> > vars;
	
		std::set<std::pair<const Instruction*, int> > dependentInstrs;
		if (getDependentInstr(i, dependentInstrs)) {
			for (std::set<std::pair<const Instruction*, int> >::iterator ii = dependentInstrs.begin(); ii != dependentInstrs.end(); ii++) {
				const BranchInst *br = dyn_cast<BranchInst>(ii->first);
				if (br) {
					if (CmpInst *cmp = dyn_cast<CmpInst>(br->getCondition())) {
						int varIdx, valIdx;
						LoadInst *pLoad = getCmpVar(cmp, varIdx, valIdx);
						if (pLoad) {
							Value *arg = pLoad->getPointerOperand();
							if (GetElementPtrInst *pGEP = dyn_cast<GetElementPtrInst>(arg))
								arg = pGEP->getPointerOperand();
							else if (ConstantExpr* pExp = dyn_cast<ConstantExpr>(arg)) {
 							    GEPOperator *pGEP = dyn_cast<GEPOperator>(pExp);
								arg = pGEP->getPointerOperand();
							}
							std::string pred, val;
							getConstValue(cmp->getOperand(valIdx), val);
							if (ii->second == 0)
								pred = predicate2String(cmp->getPredicate());
							else
								pred = predicate2String(reversePredicate(cmp->getPredicate()));
							pred += val;
							vars.push_back(make_pair(arg, pred));
						}
					}
				}
			}
		}
		return vars;
	}

	void labelSimplePath(Function *F) {
		std::string res = funcModifyLocalOnly(F);
		if (res != "") {
			std::string funcName = decorateInternalName(F);
			dumpCallEx(0, funcName, "", res, -2, 10, NULL, NULL);
		}
	}

	bool isNonLocalVar(Value *val, std::set<Value *> arguments) {
		if (LoadInst *pLoad = dyn_cast<LoadInst>(val)) {
			val = pLoad->getPointerOperand();
			//DEBUG(errrawout << "\tLoad " << val << '\n');
		}
		if (dyn_cast<GlobalVariable>(val)) {
			DEBUG(errrawout << "\tAccessing global " << val->getName() << '\n');
			return true;
		} else if (arguments.find(val) == arguments.end()) {
			DEBUG(errrawout << "\tAccessing non-argument " << val->getName() << '\n');
			return true;
		} else
			return false;
	}

	bool BBModifyLocalOnly(BasicBlock *bb, std::set<Value *>& arguments) {
		for (BasicBlock::iterator i=bb->begin(), iend=bb->end(); i != iend; ++i){
			if (AllocaInst *pAlloc = dyn_cast<AllocaInst>(i)) {
				arguments.insert(pAlloc);
			} else if (StoreInst *pStore = dyn_cast<StoreInst>(i)) {
				//DEBUG(errrawout << "\tChecking store at line " << getLineNumber(pStore) << '\n');
				Value *arg = pStore->getPointerOperand();
				if (AllocaInst *pAlloc = dyn_cast<AllocaInst>(arg)) {
					if (arguments.find(pStore->getValueOperand()) != arguments.end()) {
						arguments.insert(pAlloc);
						//DEBUG(errrawout << "\tAdding alloc " << pAlloc << '\n');

					}
				} else {
				Value *val = pStore->getValueOperand();
				if (!dyn_cast<Constant>(val) && (arguments.find(val) == arguments.end()))
					return false;
				//if (isNonLocalVar(arg, arguments))
				//	return false;
				if (LoadInst *pLoad = dyn_cast<LoadInst>(arg)) {
					std::list<Instruction *> lu = cfg->get_use_def(pLoad);
					for (std::list<Instruction *>::iterator it = lu.begin(); it != lu.end(); it++) {
						if (StoreInst *pStore = dyn_cast<StoreInst>(*it)) {
							if (isNonLocalVar(pStore->getValueOperand(), arguments))
								return false;
						}
					}
				} else if (GetElementPtrInst *pGEP = dyn_cast<GetElementPtrInst>(arg)) {
					if (isNonLocalVar(pGEP->getPointerOperand(), arguments))
						return false;
				} else if (ConstantExpr* pExp = dyn_cast<ConstantExpr>(arg)) {
				    GEPOperator *pGEP = dyn_cast<GEPOperator>(pExp);
					bool ret;
					if (pGEP) {
						ret = isNonLocalVar(pGEP->getPointerOperand(), arguments);
					}
					if (pGEP)
						return !ret;
				}
				}
#if 0
			} else if (CallInst *call = dyn_cast<CallInst>(i)) {
				Function* callee = call->getCalledFunction();
				if (callee) {
					std::string calleeName = callee->getName();

					if (calleeName == "llvm.dbg.declare")
						continue;
					else if (simpleFunctions.find(calleeName) != simpleFunctions.end())
						continue;
					DEBUG(errrawout << "\tCalling non-simple function " << calleeName << '\n');
				}
				return false;
			} else if (dyn_cast<InvokeInst>(i)) {
				return false;
#endif
			} else if (LoadInst *pLoad = dyn_cast<LoadInst>(i)) {
				if (arguments.find(pLoad->getPointerOperand()) != arguments.end()) {
					arguments.insert(pLoad);
					DEBUG(errrawout << "\tAdding load " << pLoad << '\n');
				}
			} else if (GetElementPtrInst *pGEP = dyn_cast<GetElementPtrInst>(i)) {
				if (arguments.find(pGEP->getPointerOperand()) != arguments.end()) {
					arguments.insert(pGEP);
					DEBUG(errrawout << "\tAdding getelementptr " << pGEP << '\n');
				}
			}
		}
		return true;
	}

	bool isNULLCheck(std::string pred) {
		static std::string NULLChecks[] = {"==NULL", "==0"};

		for (size_t i = 0; i < sizeof(NULLChecks)/sizeof(NULLChecks[0]); i++)
			if (pred == NULLChecks[i])
				return true;
		return false;
	}

	bool BBDependentOnNULLCheck(std::set<Value *>& arguments, BasicBlock *bb) {
		if (bb->empty())
			return false;
		std::list<std::pair<Value*, std::string> > vars = getDependentVars(&*(bb->begin()));
		DEBUG(errrawout << "\tchecking if line " << getLineNumber(bb) << " is dependent on null check\n");
		for (std::list<std::pair<Value*, std::string> >::iterator ii = vars.begin(); ii != vars.end(); ii++) {
			DEBUG(errrawout << '\t' << ii->first->getName() << ii->second << '\n');
#if 1
			if ((arguments.find(ii->first) != arguments.end()) && isNULLCheck(ii->second)) {
#else
			if (isNonLocalVar(ii->first, arguments)) {
#endif
				DEBUG(errrawout << "\t\tyes\n");
				return true;
			}
		}
		return false;
	}

	bool pathDependentOnNULLCheck(std::set<Value *>& arguments, std::list<BasicBlock *> path) {
		for (std::list<BasicBlock *>::reverse_iterator i = path.rbegin(); i != path.rend(); i++)
			if (BBDependentOnNULLCheck(arguments, *i))
				return true;
		return false;
	}

	std::string pathModifyLocalOnly(BasicBlock *bb, std::set<BasicBlock *>& visited, std::set<Value *>& arguments, std::list<BasicBlock *>& path) {
		path.push_back(bb);
		if (visited.find(bb) != visited.end()) {
			path.pop_back();
			return "";
		}
		if (!BBModifyLocalOnly(bb, arguments)) {
			path.pop_back();
			return "";
		}
#if 0 // does not concern constant return 
		if (const_returns.find(bb) != const_returns.end()) {
#if 0
			std::vector<int> lines;
			DEBUG(errrawout << "pathModifyLocalOnly end line " << getLineNumber(bb) << '\n');
			for (std::set<BasicBlock *>::iterator it = visited.begin(); it != visited.end(); it++)
				DEBUG(errrawout << "\tline " << getLineNumber(*it) << '\n');
#endif
#if 1
			if (pathDependentOnNULLCheck(arguments, path))
				return const_returns[bb].second;
			return "";
#else
			return const_returns[bb].second;
#endif
		}
#endif
		visited.insert(bb);
		for (succ_iterator I = succ_begin(bb), E = succ_end(bb); I != E; ++I) {
			std::string res = pathModifyLocalOnly(*I, visited, arguments, path);
			if (res != "")
				return res;
		}
		path.pop_back();
		return "";
	}

	std::string funcModifyLocalOnly(Function *F) {
		if (F->empty())
			return "";
		DEBUG(errrawout << "funcModifyLocalOnly " << F->getName() << '\n');
		std::set<BasicBlock *> visited;
		std::set<Value *> arguments;
		std::list<BasicBlock *> path;
		for (Function::arg_iterator I = F->arg_begin(), E = F->arg_end(); I != E; ++I) {
			Argument* arg = &*I;
			DEBUG(errrawout << "\tArg: " << arg->getName() << '\n');
			// Check whether it's passed by reference
#if 1
			const Type* T = arg->getType();
			if (!T->isPointerTy()) {
				DEBUG(errrawout << "\tAdding argument " << arg->getName() << '\n');
				arguments.insert(arg);
			}
#else
			arguments.insert(arg);
#endif
		}
		//return pathModifyLocalOnly(F->begin(), visited, arguments, path);
		for (Function::iterator i = F->begin(), e = F->end(); i != e; ++i) {
			if (!BBModifyLocalOnly(&(*i), arguments))
				return "";
		}
		return "0";
	}

	// get the next line number of an instruction within a BB
	static int getNextLineNumber(BasicBlock *b, BasicBlock::iterator i) {
		Instruction *ii = &(*i);
		int line = getLineNumber(ii);
		while (i != b->end()) {
			i++;
			if (i == b->end())
				break;
			if (getLineNumber(ii) > line) {
				line = getLineNumber(ii);
				break;
			}
		}
		return line;
	}

    static int getLineNumber(const Instruction *i) {
		int line = 0;
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 8)
			const DebugLoc& Loc = i->getDebugLoc();
			if (Loc) 
				line = Loc.getLine();
#else
			if (MDNode *N = i->getMetadata("dbg")) {
			   DILocation Loc(N);
			   line = Loc.getLineNumber();
			}
#endif	
			return line;
    }

	static int getLineNumber(const BasicBlock *b) {
		if (!b->empty()) {
			return getLineNumber(&b->front());
		} else
			return 0;
	}
	
	static int getLastLineNumber(const BasicBlock *b) {
		if (!b->empty()) {
			return getLineNumber(&b->back());
		} else
			return 0;
	}

    std::string demangle(std::string name) {
	int status;
	std::string fname;

	if (demangled_names.find(name) != demangled_names.end())
		return demangled_names[name];
	char *dname = abi::__cxa_demangle(name.c_str(), NULL, NULL, &status);
	if (dname) {
		fname = dname;
		size_t pos= fname.find('(');
                if (pos != std::string::npos)
                        fname = fname.substr(0, pos);
                fname += "_" + name;
		//errrawout << "demangle " << name << " to " << dname << '\n';
		free(dname);
	} else {
		//errrawout << "demangle " << name << " failed\n";
		fname = name;
	}
	demangled_names[name] = fname;
	return fname;
    }
    std::string getLiteralString(Value *arg) {
	std::string parm;
	if (ConstantExpr *pCE = dyn_cast<ConstantExpr>(arg)) {
		if (GlobalVariable *pGV = dyn_cast<GlobalVariable>(pCE->getOperand(0))) {
			if (pGV->hasInitializer())
				if (ConstantDataSequential *pCA = dyn_cast<ConstantDataSequential>(pGV->getInitializer())) {
				if (pCA->isString())
					parm = pCA->getAsString();
			}
		}
	}
	if (parm != "") {
		if (parm[parm.length() - 1] == '\0')
			parm.erase(parm.length() - 1);
	}
	return parm;
    }
	std::string ConvArgToStr(Instruction *i, Value *arg) {  
		bool foundArg = false;
		BasicBlock *bb = i->getParent();
		std::string parm = getLiteralString(arg);
		if (parm != "") {
#ifdef DEBUG2
			DEBUG(errrawout << "arg is literal string\n");
#endif
			foundArg = true;
			parm = '"' + parm + '"';
			//output << M.getModuleIdentifier() << FIELD_SEP << Dir.str() << FIELD_SEP << File.str() << FIELD_SEP << Line << FIELD_SEP << demangle(F->getName().str()) << FIELD_SEP << bb << FIELD_SEP << pb << FIELD_SEP << fname << FIELD_SEP << '"' << parm.c_str() << '"' << FIELD_SEP << APIMethods[fname].type << FIELD_SEP << '1' << std::endl;
		} else if (dyn_cast<ConstantPointerNull>(arg)) {
			foundArg = true;
			parm = "NULL";
		} else if (ConstantInt *pInt = dyn_cast<ConstantInt>(arg)) {
#ifdef DEBUG2
			DEBUG(errrawout << "arg is constant integer\n");
#endif
			foundArg = true;
			std::stringstream ss;
			ss << pInt->getZExtValue();
			parm = ss.str();
			//output << M.getModuleIdentifier() << FIELD_SEP << Dir.str() << FIELD_SEP << File.str() << FIELD_SEP << Line << FIELD_SEP << demangle(F->getName().str()) << FIELD_SEP << bb << FIELD_SEP << pb << FIELD_SEP << fname << FIELD_SEP << '"' << pInt->getZExtValue() << '"' << FIELD_SEP << APIMethods[fname].type << FIELD_SEP << '1' << std::endl;
		} else if (dyn_cast<AllocaInst>(arg)) {
			//assume the value is the result of calling a string class constructor, which takes a literal string as the second argument (the first argument is always the pointer to the string itself)
#ifdef DEBUG2
			DEBUG(errrawout << "arg is dynamically allocated\n");
#endif
			// arg may have multiple use
			bool foundUse = false;
			Instruction *inst = NULL;
			for (Value::use_iterator iu = arg->use_begin(), eu = arg->use_end(); iu != eu; iu++) {
				if ((inst = dyn_cast<Instruction>(*iu))) {
					if (inst == i)
						continue;
					if (inst->getParent() == i->getParent())
						foundUse = true;
					else {
						for (pred_iterator PI = pred_begin(bb), E = pred_end(bb); PI != E; PI++) {
							BasicBlock *pred = *PI;
							if (inst->getParent() == pred) {
#ifdef DEBUG2
								DEBUG(errrawout << "arg is used in " << *inst << '\n');
#endif
								foundUse = true;
								break;
							}
						} // end for
					}
				}
				if (foundUse)
					break;
			} // end for
			InvokeInst *pI = dyn_cast<InvokeInst>(inst);
			CallInst *pC =dyn_cast<CallInst>(inst);
			if (pI || pC) {
#ifdef DEBUG2
				DEBUG(errrawout << "arg is result of a call/invoke\n");
#endif
				CallSite call(inst);
				for (unsigned i = 1; i < call.arg_size(); i++) {
					arg = call.getArgument(i);
#ifdef DEBUG2
					DEBUG(errrawout << "try arg no " << i << '\n');
#endif
					parm = getLiteralString(arg);
					if (parm != "") {
						foundArg = true;
						parm = '"' + parm + '"';
						//output << M.getModuleIdentifier() << FIELD_SEP << Dir.str() << FIELD_SEP << File.str() << FIELD_SEP << Line << FIELD_SEP << demangle(F->getName().str()) << FIELD_SEP << bb << FIELD_SEP << pb << FIELD_SEP << fname << FIELD_SEP << '"' << parm.c_str() << '"' << FIELD_SEP << APIMethods[fname].type << FIELD_SEP << '1' << std::endl;
						break;
					}
				}
			}
						
		} else if (LoadInst *pLoad = dyn_cast<LoadInst>(arg)) {
#ifdef DEBUG2
			DEBUG(errrawout << "arg is from a load\n");
#endif
			Value *op = pLoad->getPointerOperand();
			if (Instruction *pInst = dyn_cast<Instruction>(op)) {
#ifdef DEBUG2
				DEBUG(errrawout << "arg is an " << pInst->getOpcodeName() << " instruction\n");
#endif
				if (dyn_cast<AllocaInst>(pInst)) {
					StoreInst *pStore = NULL;
#if 1
					std::list<Instruction *> lu = cfg->get_use_def(pLoad);
					if (!lu.empty())
						pStore = dyn_cast<StoreInst>(lu.back());
#else
					for (Value::use_iterator iu = pAlloca->use_begin(), eu = pAlloca->use_end(); iu != eu; iu++) {
						if (Instruction *i = dyn_cast<Instruction>(*iu)) {
#ifdef DEBUG2
							DEBUG(errrawout << "\tuse is an " << i->getOpcodeName() << " instruction\n");
#endif
							if (pStore = dyn_cast<StoreInst>(i)) {
								// assume store and load are in the same basicblock
								//if (pStore->getParent() != pLoad->getParent())
								//	continue;
								// assume there is just one store for arg
								break;
							}
						} else
							DEBUG(errrawout << "use is not an instruction\n");
					}
#endif
					if (pStore) {
						Value *op = pStore->getValueOperand();
	#ifdef DEBUG2
						DEBUG(errrawout << "\t\targ type is " << op->getValueID() << '\n');
	#endif
						if (op->getValueID() == Value::ArgumentVal) {
							Argument *pArg = dyn_cast<Argument>(op);
	#ifdef DEBUG2
							DEBUG(errrawout << "\t\targ is formal argument " << pArg->getArgNo() << '\n');
	#endif
							std::stringstream ss;
							ss << pArg->getArgNo();
							parm = ss.str();
							foundArg = true;
							parm = "'" + parm + "'";
						} else {
							parm = getLiteralString(op);									
							if (parm != "") {
								foundArg = true;
								parm = '"' + parm + '"';
							}
	#ifdef DEBUG2
							DEBUG(errrawout << "\t\targ is " << parm << '\n');
	#endif
						}
					}
	
				}
			}
		}   
		if (!foundArg)
			parm = "";
		else if (parm.find('\n') !=  std::string::npos) // discard strings containing line feed
			parm = "";
#ifdef DEBUG2
		DEBUG(errrawout << "arg is " << parm << '\n');
#endif
		return parm;
	}

/*
	const Instruction* getDependentInstr(const Instruction* i) {
		const BasicBlock *bb = i->getParent();
		const Instruction* di = NULL;

		const BasicBlock *pb = bb->getSinglePredecessor();
		if (pb) {
			const TerminatorInst *inst = pb->getTerminator();
			if (const BranchInst *branch = dyn_cast<BranchInst>(inst)) {
				if (branch->isConditional()) {
					Value *cond = branch->getCondition();
#ifdef DEBUG2
					DEBUG(errrawout << "condition:\n\t");
					cond->print(errrawout);
#endif
					di = dyn_cast<Instruction>(cond);
				}
			}
		}
		return di;
	}
*/
	bool getDependentInstr(const Instruction* i, std::set<std::pair<const Instruction*, int> >& dependentInstrs) {
		const BasicBlock *bb = i->getParent();

		//DEBUG(errrawout << "\tgetDependentInstr " << bb << '@' << getLineNumber(bb) << '\n');
		if (dependency.find(bb) != dependency.end()) {
			dependentInstrs = dependency[bb];
			return true;
		} else
			return false;
	}

	/*
 	 * ii - only present if followed-by-return info and call arguments is needed in output, it must be a call or invoke instrucation
	 * i - only present if dependency is needed in output
	 * loc_i - only present for retrieval of source filename
	 */
	void dumpCallEx(int line, const std::string &funcName, const std::string &calleeName, const std::string &parm, int accType, int callType, Instruction* ii, Instruction* i, Instruction *loc_i = NULL) {
		std::set<std::string> funcTyArgs;
		std::stringstream dependency;
		std::stringstream returnInfo;
		std::string dir=Dir, file=File;

		if (loc_i) {
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 8)
			#warning "dumpCallEx loc_i is not supported for LLVM 3.8!"
#else
			if (MDNode *N = loc_i->getMetadata("dbg")) {
			   DILocation Loc(N);
			   dir = Loc.getDirectory();
			   file = Loc.getFilename();
			}
#endif
		}
		output << ModuleName << FIELD_SEP << dir << FIELD_SEP << file << FIELD_SEP << line << FIELD_SEP << funcName << FIELD_SEP << line << FIELD_SEP;
		if (i) {
#if 0		
			const Instruction *di = getDependentInstr(i);
			if (di) {
				output << getLineNumber(di);
			} else
				output << 0;
#else
			std::set<std::pair<const Instruction*, int> > dependentInstrs;
			if (getDependentInstr(i, dependentInstrs)) {
				for (std::set<std::pair<const Instruction*, int> >::iterator ii = dependentInstrs.begin(); ii != dependentInstrs.end(); ii++) {
					const std::string l = getLineID(*ii);
					if (ii == dependentInstrs.begin())
					  //dependency << line << '(' << ii->first << ')' << ';' << ii->second;
					  dependency << l;
					else
					  dependency << ',' << l;
				}
			} else
				dependency << 0;
			output << dependency.str();
#endif
		}
		if (ii) {
			const BasicBlock *constReturn = NULL;
			if (const_returns.find(ii->getParent()) != const_returns.end()) {
				DEBUG(errrawout << getLineNumber(ii) << " is followed by const return" << '\n');
				constReturn = ii->getParent();
			} else {
#if 0
				Function *F = ii->getParent()->getParent();
				for (std::map<const BasicBlock*, std::pair<int, int> >::iterator it = const_returns.begin(); it != const_returns.end(); it++) {
					if (it->first->getParent() != F)
						continue;
					if (DT->dominates(ii->getParent(), it->first)) {
						constReturn = it->first;
						break;
					}
				}
#else 
				BasicBlock *bb = ii->getParent();
				for (auto ret : const_returns) {
					if (postDT->dominates(ret.first, bb)) {
						constReturn = ret.first;
						break;
					}
				}
/*
				while (1) {
					std::vector<BasicBlock*> succs;
					for (succ_iterator I = succ_begin(bb), E = succ_end(bb); I != E; ++I) {
						succs.push_back(*I);
					}
					//DEBUG(errrawout << getLineNumber(i) << " has " << succs.size() << " successors" << '\n');
					if (succs.size() == 1) {
						//DEBUG(errrawout << '\t' << getLineNumber(succs[0]) << '\n');
						if ((const_returns.find(succs[0]) != const_returns.end()) && (cond_const_returns.find(succs[0]) == cond_const_returns.end())) {
							DEBUG(errrawout << getLineNumber(i) << " is followed by const return" << '\n');
							constReturn = succs[0];
							break;
						} else if (bb != succs[0])
							bb = succs[0];
						else
							break;
					} else
						break;
				}
*/
#endif
			}
			if (constReturn) {
				DEBUG((errrawout << '\t' << "Line " << line << " is followed by return " << const_returns[constReturn].second << " at line " << const_returns[constReturn].first << '\n'));
				returnInfo << ',' << const_returns[constReturn].first << ',' << const_returns[constReturn].second;
			}
		}
		output << FIELD_SEP << calleeName << FIELD_SEP << parm.c_str() << FIELD_SEP << accType << FIELD_SEP << callType << returnInfo.str();
		if (!ii) {
			output << std::endl;
			return;
		}
		CallSite call(ii);
		// ii can be LoadInst
		if (call.isCall() || call.isInvoke()) {
			for (unsigned n = 0; n < call.arg_size(); n++) {
				Value *arg = call.getArgument(n);
				std::string parm = ConvArgToStr(i, arg);
	#ifdef DEBUG2
				DEBUG(errrawout << "argument#" << (int)n << ':' << parm << '\n');
	#endif			
				output << FIELD_SEP << parm.c_str();
			}

			//std::string str;
			//llvm::raw_string_ostream os(str);

			for (unsigned n = 0; n < call.arg_size(); n++) {
				Value *arg = call.getArgument(n);
				Type *type = arg->getType();

				if (type->isPointerTy()) {
					if (CastInst *cast = dyn_cast<CastInst>(arg)) {
						type = cast->getSrcTy();
					}
					Type *ptType = NULL;
					if (type->isPointerTy())
						ptType = type->getPointerElementType();
					else
						ptType = type;
					if (ptType->isStructTy() && cast<StructType>(ptType)->hasName())
						output << FIELD_SEP << ptType->getStructName().str() << '*';
					else if (ptType->isFunctionTy()) {
						std::string name;
						if (dyn_cast<Function>(arg))
							name = decorateInternalName(dyn_cast<Function>(arg));
						else {
							name = arg->getName();
							if (name == "") {
								LoadInst *load = NULL;
							 	if ((load = dyn_cast<LoadInst>(arg))) {
									name = "*" + getLoadStructVarName(load, 0);
								}
							}
						}
						output << FIELD_SEP << name << "()*";
						funcTyArgs.insert(name);
					} else
						output << FIELD_SEP << "i8*";
				} else
					output << FIELD_SEP;
			}
		}
		output << std::endl;
		if (funcTyArgs.size() > 0) {
			// generate a psuedo call for each function pointer that is used as an argument
			for (std::set<std::string>::iterator it = funcTyArgs.begin(); it != funcTyArgs.end(); it++) {
				output << ModuleName << FIELD_SEP << Dir << FIELD_SEP << File << FIELD_SEP << line << FIELD_SEP << funcName << FIELD_SEP << line << FIELD_SEP << dependency.str() << FIELD_SEP << *it << FIELD_SEP << FIELD_SEP << -1 << FIELD_SEP << 0 << std::endl;
			}
		}
	}

	void dumpUseOfCall(int line, const std::string &funcName, const std::string &calleeName, const std::string &parm, int accType, int callType, const BasicBlock::iterator& ii, StoreInst *pStore) {
		Value *op = pStore->getPointerOperand();
#ifdef DEBUG2
		DEBUG(errrawout << "arg type is " << op->getValueID() << '\n');
#endif
		for (Value::use_iterator iu2 = op->use_begin(), eu2 = op->use_end(); iu2 != eu2; iu2++) {
			if (Instruction *i = dyn_cast<Instruction>(*iu2)) {
				// for each use of store
				if (dyn_cast<StoreInst>(i))
				//	dumpUseOfCall(M, dirName, fileName, line, funcName, calleeName, parm, accType, callType, ii, pStore);
				;
				else {
					dumpCallEx(getLineNumber(i), funcName, "", "", line, 6, &(*ii), i);
				}
			} else
				DEBUG(errrawout << "use2 is not an instruction\n");
		}
	}

	void dumpCall(int line, const std::string &funcName, const std::string &calleeName, const std::string &parm, int accType, int callType, const BasicBlock::iterator& ii) {
		dumpCallEx(line, funcName, calleeName, parm, accType, callType, &(*ii), &(*ii));
		// dump use of call
		Instruction *call = dyn_cast<Instruction>(ii);
		for (Value::use_iterator iu = call->use_begin(), eu = call->use_end(); iu != eu; iu++) {
			if (Instruction *i = dyn_cast<Instruction>(*iu)) {
				// for each store
				if (StoreInst *pStore = dyn_cast<StoreInst>(i)) {
					dumpUseOfCall(line, funcName, calleeName, parm, accType, callType, ii, pStore);
				}
			} else
				DEBUG(errrawout << "use of " << i << " is not an instruction\n");
		}
	}

	/*
	 * simluateHalfCall: value must be a struct value, i is the index of the field
	 */
	void simulateHalfCall(std::string vname, const Value *value, int i, std::string callee) {
		// simulate a half-call
		std::string caller;
		if (internalFunctions.find(callee) != internalFunctions.end())
			callee = internalFunctions[callee];
		raw_string_ostream oss(caller);
		//oss << gv->getName() << ',';
		Type* type = value->getType();
		std::string name;
		if (!dyn_cast<StructType>(type)->isLiteral())
			name = type->getStructName();
		if (name == "")
			oss << vname;
		else
			oss << name;
		oss << ',' << i;
		oss.flush();
		fp_count++;
		dumpCallEx(-fp_count, "*" + caller, callee, "", -2, 4, NULL, NULL);
	}

	void findFPinOneStruct(const Constant *value, std::string &vname) {
		if (dyn_cast<ConstantStruct>(value)) {
			DEBUG(errrawout << "\tstruct " << value->getName() << '\n');
			int i = 0;
			Constant *elm = NULL;
			do {
				std::string caller, callee;
				elm = value->getAggregateElement(i);
				if (elm == NULL)
					break;
				if (dyn_cast<ConstantExpr>(elm)) {
					DEBUG(errrawout << "\t\tfield " << i << ": " << "expr" << '\n');
					ConstantExpr *exp = dyn_cast<ConstantExpr>(elm);
					Instruction *inst = exp->getAsInstruction();
					CastInst *cinst = dyn_cast<CastInst>(inst);
					if (cinst) {
						Value *oprand = cinst->getOperand(0);
						DEBUG(errrawout << "\t\t\toprand " << ": ");
						oprand->getType()->print(errrawout);
						DEBUG(errrawout << oprand->getName() << '\n');
						callee = oprand->getName();
					}
					if (inst) {
						inst->dropAllReferences();
						if (inst->getParent())
							inst->eraseFromParent();
					}
				} else {
					DEBUG(errrawout << "\t\tfield " << i << ": ");
					elm->getType()->print(errrawout);	
					DEBUG(errrawout << elm->getName() << '\n');
					callee = elm->getName();
				}
				if (callee != "")
					simulateHalfCall(vname, value, i, callee);
				i++;
			} while (elm);
		} else {
			DEBUG(errrawout << "non-struct " << value->getName() << '\n');
		}
	}

	void findFPinGV(Module &M) {
		DEBUG(errrawout << "findFPinGV " << ModuleName << '\n');
		for (llvm::Module::global_iterator ii = M.global_begin(); ii != M.global_end(); ++ii) { 
	        GlobalVariable* gv = &(*ii);
		if (gv->hasInitializer()) {
			const Constant *value = gv->getInitializer();
			std::string vname = gv->getName();
			DEBUG(errrawout << "global variable " << vname << '\n');
			if (value) {
				if (dyn_cast<ConstantStruct>(value))
					findFPinOneStruct(value, vname);
				else if (dyn_cast<ConstantArray>(value)) {
					DEBUG(errrawout << "\tarray " << value->getName() << '\n');
					int i = 0;
					Constant *elm = NULL;
					do {
						std::string caller, callee;
						elm = value->getAggregateElement(i);
						if (elm == NULL)
							break;
						if (dyn_cast<ConstantStruct>(elm))
							findFPinOneStruct(elm, vname);
						i++;
					} while (elm);
				}
			}
		}
		}
	}

	bool static compareByLineNumber(const BasicBlock *b1, const BasicBlock *b2) {
		return getLineNumber(b1) < getLineNumber(b2);
	}

	bool static compareBBsByLineNumber(const std::vector<BasicBlock *> v1, const std::vector<BasicBlock *> v2) {
		if (v1.size() == 0)
			return 0;
		else if (v2.size() == 0)
			return 1;
		else
			return compareByLineNumber(v1[0], v2[0]);
	}

	std::vector<BasicBlock *> getPath(int conditionLine, BasicBlock *succ, BasicBlock *CD) {
		std::queue<BasicBlock*> q;
		std::set<BasicBlock*> v;

		DEBUG(errrawout << "\tgetPath " << conditionLine << ", " << succ->getName() << ':' << getLineNumber(succ) << '\n');
		q.push(succ);
		while (!q.empty()) {
			BasicBlock* bb = q.front();
			q.pop();
			DEBUG(errrawout << '\t' << "visit " << getLineNumber(bb) << '\n');
			v.insert(bb);

			if (bb != CD) {
			  //int branchLine = getLineNumber(bb);

				for (succ_iterator I = succ_begin(bb), E = succ_end(bb); I != E; ++I) {
					BasicBlock *succ = *I;
					int line = getLineNumber(succ);
					//if ((line == 0) || ((line > 0) && (line > conditionLine) && (line > branchLine))) {
					if ((line == 0) || ((line > 0) && (line > conditionLine))) {
						if (v.find(succ) == v.end()) {
							q.push(succ);
						}
					}
				}
			}
		}
		std::vector<BasicBlock*> r;
		std::copy(v.begin(), v.end(), std::back_inserter(r));
		std::sort(r.begin(), r.end(), compareByLineNumber);
		std::vector<BasicBlock *>::iterator it = r.begin();
		for (; it != r.end(); it++)
			if (getLineNumber(*it) > 0)
				break;
		if (it != r.begin())
			r.erase(r.begin(), it);
		DEBUG(errrawout << '\t' << "path\n");
		for (size_t i = 0; i < r.size(); i++)
			DEBUG(errrawout << '\t' << getLineNumber(r[i]) << '\n');
		return r;
	}

	/*
		labelDependency:
			find instructions that are dependent on a branch instruction and store
			them into dependency map
	*/
	void labelDependency(Function *func, BasicBlock* bbb, Instruction *branch) {
		DEBUG(errrawout << "labelDependency " << getLineNumber(branch) << "\n");
		//Function& func = *(branch->getParent()->getParent());
		//BasicBlock* bbb = branch->getParent();
		
		int conditionLine = getLineNumber(branch);
		if (conditionLine == 0)
			return;

		std::vector<BasicBlock*> succ;
		for (succ_iterator I = succ_begin(bbb), E = succ_end(bbb); I != E; ++I) {

		  DEBUG(errrawout << "\t" << getLineNumber(*I) << '\n');
			succ.push_back(*I);
		}
		DEBUG(errrawout << "\t" << succ.size() << " successors." << '\n');
		BasicBlock* CD; 
		if (succ[0] != NULL && succ[1] != NULL)
			CD = postDT->findNearestCommonDominator(succ[0], succ[1]);
		else
			CD = NULL;
		
		if (CD == NULL)
			DEBUG(errrawout << "\tWarning: No CommonDominator" << '\n');
		else
			DEBUG(errrawout << "\tCommonDominator@" << getLineNumber(CD) << '\n');

		std::vector<std::vector<BasicBlock*> > paths, origPaths;
		for (size_t i = 0; i < succ.size(); i++) {
		  std::vector<BasicBlock*> p = getPath(conditionLine, succ[i], CD);
		  if (p.size() > 0)
			paths.push_back(p);
		}
		//if ((paths[0].back() == paths[1].front()) || dyn_cast<UnreachableInst>(paths[0].back()->getTerminator())) {
		if (paths.size() > 1 && (paths[0].back() == paths[1].front())) {
		  DEBUG(errrawout << "\tNo else block\n");
		  paths.pop_back();
		}
		
		//assert(count >= 2);
		//if (paths.size() > 1)
		//origPaths = paths;
		std::sort(paths.begin(), paths.end(), compareBBsByLineNumber);

		//for (size_t i = 0; i < paths.size(); i++)
		//	DEBUG(errrawout << "\tSuccessor@" << getLineNumber(paths[i][0]) << '\n');

		std::vector<BasicBlock *> intersection;
		if (paths.size() > 1) {
			intersection = paths[0];
			for (size_t i = 1; i < paths.size(); i++) {
				std::vector<BasicBlock *> tmp;
				std::set_intersection(intersection.begin(), intersection.end(), paths[i].begin(), paths[i].end(), back_inserter(tmp), compareByLineNumber);
				if (tmp.size() > 0)
				   intersection = tmp;
				else
				  intersection.clear();
			}
		
		        DEBUG(errrawout << '\t' << "intersection " << intersection.size() << '\n');
			for (size_t i = 0; i < intersection.size(); i++)
			  DEBUG(errrawout << '\t' << "intersection " << i << ':' << getLineNumber(intersection[i]) << '\n');

			// fix the case when only the then block exists
			if (intersection.size() > 0) {
			if (intersection[0] == paths[0][0]) {
			  paths.erase(paths.begin());
			  DEBUG(errrawout << '\t' << "Removed branch 0\n");
			} else if (intersection[0] == paths[1][0]) {
			  paths.pop_back();
			  DEBUG(errrawout << '\t' << "Removed branch 1\n");
		        }
			}
		}

		if ((CD == NULL) && (paths.size() > 1)  && (intersection.size() > 0)) {
		   CD = intersection[0];
		   std::set<BasicBlock *> visited;
		   while (getLineNumber(CD) < conditionLine) {
			visited.insert(CD);
			DEBUG(errrawout << '\t' << "Finding CD" << getLineNumber(CD) << '\n');
			if (succ_begin(CD) == succ_end(CD))
				break;
			BasicBlock *next = *succ_begin(CD);
			if (visited.find(next) == visited.end()) {
				CD = next;
			} else
				break;
		   }
		}
		if (CD)
		  DEBUG(errrawout << "\tFound CommonDominator@" << getLineNumber(CD) << '\n');
		
		//paths = origPaths;
		for (size_t i = 0; i < paths.size(); i++) {
			DEBUG(errrawout << '\t' << "branch " << i << ':' << '\n');
			for (std::vector<BasicBlock*>::iterator ii = paths[i].begin(), e = paths[i].end(); ii != e; ++ii) {
				if ((*ii != bbb) && (*ii != CD)) {
					int branchLine = getLineNumber(*ii);
					if (branchLine > 0 && (branchLine >= conditionLine)) {
						DEBUG(errrawout << "\t\t" << getLineNumber(*ii) << '\n');
						std::pair<const Instruction *, int> branch_idx = std::make_pair(branch, i);
						dependency[*ii].insert(branch_idx);
					}
				}
			}
		}
	}

	std::string decorateInternalName(Function *F) {
		std::string funcName = demangle(F->getName().str());
		if ((entryFunctions.find(funcName) != entryFunctions.end()) || GlobalValue::isInternalLinkage(F->getLinkage())) {
			if (internalFunctions.find(funcName) != internalFunctions.end())
				return internalFunctions[funcName];
			//std::string hash;
			//raw_string_ostream hashstros(hash);
			
			//hashstros << (void *)F;
			//hashstros.flush();
			//funcName +=  "_" + hash;
			std::string orgFuncName = funcName;
			funcName += "_" + Dir + '/' + File;
			internalFunctions[orgFuncName] = funcName;
		}
		return funcName;
	}

	std::string getStoreStructVarName(StoreInst *store, int checkConf) {
		return getStructVarName(store->getPointerOperand(), checkConf);
	}

	std::string getLoadStructVarName(LoadInst *load, int checkConf) {
		return getStructVarName(load->getPointerOperand(), checkConf);
	}

	std::string getStructVarNameFromGEP(GEPOperator *gep, int checkConf) {
		std::string vname;
		Type *type = gep->getPointerOperandType()->getPointerElementType();
		if (type->isStructTy()) {
			if (!dyn_cast<StructType>(type)->isLiteral())
				vname = type->getStructName();
			if (checkConf && Structs.find(vname) == Structs.end()) {
				vname = "";
			} else {
				//std::stringstream ss;
				//ss << gep->getNumIndices();
				//vname += ss.str();
				User::const_op_iterator OI = gep->idx_begin(), OE = gep->idx_end();
				bool first = true;
				for (; OI != OE; ++OI) {
					if (first) {
						first = false;
						continue;
					}
					Value *v = *OI;
					ConstantInt *c = dyn_cast<ConstantInt>(v);
					if (c) {
						std::string s = (c->getValue()).toString(10, true);
						vname += ',' + s;
					}
				}
			}
		}
		return vname;
	}

	std::string getStructVarName(Value *oprand, int checkConf) {
		std::string vname;
		GEPOperator *gep = NULL;

		CastInst *inst = dyn_cast<CastInst>(oprand);
		if (inst)
			oprand = inst->getOperand(0);

		if (ConstantExpr* cexp = dyn_cast<ConstantExpr>(oprand)) {
			gep = dyn_cast<GEPOperator>(cexp);
			if (gep) {
				vname = getStructVarNameFromGEP(gep, checkConf);
			}
		} else {
			gep = dyn_cast<GEPOperator>(oprand);
			if (gep)
				vname = getStructVarNameFromGEP(gep, checkConf);
		}
		if (gep) {
			//Value *arg = gep->getPointerOperand();
			//delete gep;
		} else if (includeGlobalVar) {
			if (GlobalVariable *pGV = dyn_cast<GlobalVariable>(oprand)) {
				vname = pGV->getName();
			}
		}
		return vname;
	}

	std::string getFPName(LoadInst *pLoad) {
		std::list<Instruction *> lu = cfg->get_use_def(pLoad);
		StoreInst *pStore = NULL;
		if (!lu.empty())
			pStore = dyn_cast<StoreInst>(lu.back());
		if (pStore) {
			Value *op = pStore->getValueOperand();
			LoadInst *pLoad2 = dyn_cast<LoadInst>(op);
			if (pLoad2)
				op = pLoad2->getPointerOperand();
			return getStructVarName(op, 0);
		} else {
			return pLoad->getPointerOperand()->getName();
		}
	}

	std::string getVarName(LoadInst *pLoad) {
		Value *var = pLoad->getPointerOperand();
		std::string name = var->getName();
		if (name == "") {
			if (dyn_cast<AllocaInst>(var)) {
				StoreInst *pStore = NULL;
				std::list<Instruction *> lu = cfg->get_use_def(pLoad);
				if (!lu.empty()) {
					pStore = dyn_cast<StoreInst>(lu.back());
					var = pStore->getValueOperand();
					name = var->getName();
				}
			}
		}
		return name;
	}

	/*
	 * Get the line number of the most immediate return following i
	 */
	int getLineOfReturn(Instruction *i) {
		const BasicBlock *bb = i->getParent();
		const Instruction *ins = NULL;
		
		while (1) {
			if (isa<ReturnInst>(bb->getTerminator())) {
				ins = bb->getTerminator();
				break;
			} else if (isa<BranchInst>(bb->getTerminator())) {
				const Instruction *tbb = bb->getTerminator();
				const BranchInst *binst = dyn_cast<BranchInst>(tbb);
				if  (binst->getNumSuccessors() == 1) {
					if (binst->getSuccessor(0) == bb)
						break;
					else {
						ins = binst;
						break;
					}
				} else
					break;
			} else
				break;
		}
		if (ins)
			return getLineNumber(ins);
		else
			return 0;
	}

	int getNumSuccessors(BasicBlock *bb) {
		int count;
		for (succ_iterator I = succ_begin(bb), E = succ_end(bb); I != E; ++I) {
			count++;
		}
		return count;
	}

	int getConstValue(Value *pConst, std::string &ret_value) {
		int err = 0;

		if (ConstantInt *pInt = dyn_cast<ConstantInt>(pConst)) {
			std::stringstream ss;
			ss << pInt->getSExtValue();
			ret_value = ss.str();
		} else if (dyn_cast<ConstantPointerNull>(pConst)) {
			ret_value = "NULL";
		} else if (ConstantExpr *pExp = dyn_cast<ConstantExpr>(pConst)) {
			if (IntToPtrInst *pIntPtr = dyn_cast<IntToPtrInst>(pExp->getAsInstruction())) {
				ConstantInt *pInt = dyn_cast<ConstantInt>(pIntPtr->getOperand(0));
				std::stringstream ss;
				ss << pInt->getSExtValue();
				ret_value = ss.str();
				pIntPtr->dropAllReferences();
				if (pIntPtr->getParent())
					pIntPtr->eraseFromParent();
			}
		} else
			err = -1;
		return err;
	}

	/*
	 * Note that the length of the predicate string must be 2 characters so that
	 * it is easier to separate the operators from operands
	 */
	std::string predicate2String(CmpInst::Predicate pred) {
		switch(pred) {
		case CmpInst::ICMP_EQ:
			return "==";
		case CmpInst::ICMP_NE:
			return "!=";
		case CmpInst::ICMP_UGT:
		case CmpInst::ICMP_SGT:
			return "> ";
		case CmpInst::ICMP_UGE:
		case CmpInst::ICMP_SGE:
			return ">=";
		case CmpInst::ICMP_ULT:
		case CmpInst::ICMP_SLT:
			return "< ";
		case CmpInst::ICMP_ULE:
		case CmpInst::ICMP_SLE:
			return "<=";
		default:
			return "##";
		}
	}

	CmpInst::Predicate reversePredicate(CmpInst::Predicate pred) {
		switch(pred) {
		case CmpInst::ICMP_EQ:
			return CmpInst::ICMP_NE;
		case CmpInst::ICMP_NE:
			return CmpInst::ICMP_EQ;
		case CmpInst::ICMP_UGT:
			return CmpInst::ICMP_SLE;
		case CmpInst::ICMP_SGT:
			return CmpInst::ICMP_SLE;
		case CmpInst::ICMP_UGE:
			return CmpInst::ICMP_ULT;
		case CmpInst::ICMP_SGE:
			return CmpInst::ICMP_SLT;
		case CmpInst::ICMP_ULT:
			return CmpInst::ICMP_UGE;
		case CmpInst::ICMP_SLT:
			return CmpInst::ICMP_SGE;
		case CmpInst::ICMP_ULE:
			return CmpInst::ICMP_UGT;
		case CmpInst::ICMP_SLE:
			return CmpInst::ICMP_SGT;
		default:
			return pred;
		}
	}

	int isSimpleBB(BasicBlock *bb) {
		int line = 0;
		for (BasicBlock::iterator i=bb->begin(), iend=bb->end(); i != iend; ++i){
			if (dyn_cast<LoadInst>(i) || dyn_cast<StoreInst>(i) || dyn_cast<BranchInst>(i) || dyn_cast<ReturnInst>(i)) {
				line = getLineNumber(&(*i));
			} else
				return 0;
		}
		DEBUG(errrawout << "BB ends at line " << line << " is simple BB\n");
		return line;
	}

	BasicBlock *isImmediateReturn(BasicBlock *bb, BasicBlock *bb2) {
		int has_return = 0;
		BasicBlock *last_block = bb;

		while (1) {
			if (bb == bb2)
				return NULL;
			if (!isSimpleBB(bb))
				return NULL;
			if (!bb->empty()) {
				const Instruction *inst = &bb->back();
				if (dyn_cast<ReturnInst>(inst)) {
					has_return = 1;
				}
			}
			if (has_return)
				break;
			last_block = bb;
			bb = *succ_begin(bb);
		}
		if (!has_return)
			last_block = NULL;
		return last_block;
	}

	BasicBlock *getLastBB(BasicBlock *bb, BasicBlock *branch, std::set<BasicBlock *>& visited) {
		int last_line = 0;
		std::vector<BasicBlock *> otherBranches;
		BasicBlock *last_block = bb;

		//DEBUG(errrawout << "getLastBB " << bb << ", " << branch << '\n');
		for (succ_iterator PI = succ_begin(branch), E = succ_end(branch); PI != E; ++PI)
			if (*PI != bb)
					otherBranches.push_back(*PI);

		if (visited.find(bb) != visited.end()) {
			//DEBUG(errrawout << '\t' << "branch at line " << getLineNumber(bb) << '(' << bb << ')' << " already visited\n");
			return NULL;
		}

		while (1) {
			visited.insert(bb);
			for (size_t i = 0; i < otherBranches.size(); i++)
				if (bb == otherBranches[i]) {
					//DEBUG(errrawout << '\t' << "join another branch at line " << getLineNumber(bb) << '(' << bb << ')' << '\n');
					return last_block;
				}
			int line = getLineNumber(bb);
			if (line) {
				if (last_line && (line > last_line + 1 || line <= last_line))
					return last_block;
				last_line = line;
			}
			last_block = bb;
			int n = getNumSuccessors(bb);
			if (n == 1)
				bb = *succ_begin(bb);
			else if (n > 1) {
				for (succ_iterator PI = succ_begin(bb), E = succ_end(bb); PI != E; ++PI) {
					BasicBlock *bb1 = getLastBB(*PI, bb, visited);
					if (bb1 && (getLineNumber(bb1) > last_line)) {
						last_line = getLineNumber(bb1);
						last_block = bb1;
					}
				}
				return last_block;
			} else
				break;
			if (visited.find(bb) != visited.end())
				break;
		}
		return last_block;
	}

	int labelReturnStmt(std::string funcName, BasicBlock *bb, std::string var) {
		int first_line = getLineNumber(bb);
		for (pred_iterator PI = pred_begin(bb), E = pred_end(bb); PI != E; ++PI) {
			BasicBlock *pred = *PI;
			if (getLastLineNumber(pred) == first_line)
				return 0;
		}

		int last_line = getLastLineNumber(bb);
		std::stringstream ss;
		ss << first_line << ',' << last_line << ',' << var;
		dumpCallEx(last_line, funcName, "", ss.str(), -2, 11, NULL, NULL, &bb->back());
		return last_line - first_line + 1;
	}

	int labelGuardingCondition(std::string var, std::string value, LoadInst *pLoad) {
		if (checkedGuardingConditions.find(pLoad) != checkedGuardingConditions.end())
			return 0;

		checkedGuardingConditions.insert(pLoad);
		Value::use_iterator i = pLoad->use_begin();
		if (CmpInst *cmp = dyn_cast<CmpInst>(*i)) {
			Value::use_iterator j = cmp->use_begin();
			if (BranchInst *branch = dyn_cast<BranchInst>(*j)) {
				int count_branch = branch->getNumSuccessors();
				DEBUG(errrawout << "labelGuardingCondition line " << getLineNumber(branch) << " " << count_branch << " branches\n");
				BasicBlock *bb1 = branch->getSuccessor(0);
				BasicBlock *bb2 = branch->getSuccessor(1);
/*
				// nearest common dominator is not the end of if statement

				BasicBlock *CD = postDT->findNearestCommonDominator(bb1, bb2);
				if (CD == NULL) {
					DEBUG(errrawout << '\t' << "No common dominator!\n");
					return 0;
				}
				if (isImmediateReturn(CD, NULL)) {
					DEBUG(errrawout << '\t' << "Common dominator at line " << getLineNumber(CD) << " is immediate return!\n");
					return 0;
				}
*/
				BasicBlock *bb = branch->getParent();
				std::set<BasicBlock *> visited;
				for (succ_iterator PI = succ_begin(bb), E = succ_end(bb); PI != E; ++PI) {
					BasicBlock *last_block = getLastBB(*PI, bb, visited);
					if (last_block)
						DEBUG(errrawout << '\t' << "branch " << getLineNumber(*PI) << " - " << getLastLineNumber(last_block) << '\n');
				}
				if (getLineNumber(bb1) > getLineNumber(bb2)) {
					BasicBlock *bb = bb1;
					bb1 = bb2;
					bb2 = bb;
				}
				BasicBlock *last_block = isImmediateReturn(bb1, bb2);
				if (last_block) {
					int start_line = getLineNumber(pLoad);

					std::list<Instruction *> lu = cfg->get_use_def(pLoad);
					for (std::list<Instruction *>::iterator it = lu.begin(); it != lu.end(); it++) {
						if (StoreInst *pStore = dyn_cast<StoreInst>(*it)) {
							if (CallInst *pCall = dyn_cast<CallInst>(pStore->getValueOperand())) {
								int end_line = getLastLineNumber(last_block);
								CallErrorHandling[pLoad->getPointerOperand()][pCall] = std::make_pair(start_line, end_line);
								DEBUG(errrawout << '\t' << "call error handling " << var << predicate2String(cmp->getPredicate()) << value << ": " << start_line << ", " << end_line << '\n');
								DEBUG(errrawout << "\t\t" << "def var: " << var << " at line " << getLineNumber(*it) << '\n');
							}
						}
						break; // should loop just once
					}
				}
			} /*else if (SwitchInst *branch = dyn_cast<SwitchInst>(*j)) {
			}*/
		}
		return 0;
	}

	void labelConstReturn(int line, std::string funcName, BasicBlock *bb, Instruction *ins, std::string ret_value) {
		const_returns[bb] = std::make_pair(line, ret_value);
		dumpCallEx(line, funcName, "", ret_value, -2, 7, NULL, ins);
	}

	std::set<Instruction*> crcc;
	// function wrapper to prevent infinite recursion
	int CheckReturnConstOrCallEx(std::string funcName, StoreInst *pStore, CallInst *pCall) {
		crcc.clear();
		return CheckReturnConstOrCall(funcName, pStore, pCall);
	}

	int CheckReturnConstOrCall(std::string funcName, StoreInst *pStore, CallInst *pCall) {
		int ret = 0;
		int line = 0;
		Value *arg = NULL;
		std::string var;

		if (crcc.find(pStore) != crcc.end()) {
			DEBUG(errrawout << '\t' << "recursive store detected " << getLineNumber(pStore) << '\n');
			return 0;
		}
		crcc.insert(pStore);
		if (pStore) {
			line = getLineNumber(pStore);
			arg = pStore->getValueOperand();
			var = pStore->getPointerOperand()->getName();
		} else {
			line = getLineNumber(pCall);
			arg = pCall;
		}

		if (CastInst *cast = dyn_cast<CastInst>(arg))
			arg = cast->getOperand(0);

		if (Constant *pConst = dyn_cast<Constant>(arg)) {
			//DEBUG(errrawout << "set const return value at line " <<  getLineNumber(pStore) << '\n');
			//DEBUG(errrawout << "return at line " << getLineOfReturn(pStore) << '\n');
			//int line = getLineOfReturn(pStore);
			// Skip const 0
			std::string ret_value;
			if (getConstValue(pConst, ret_value) == -1) {
				DEBUG(errrawout << '\t' << "cannot identify constant return const at line " << getLineNumber(pStore) << '\n');
				return ret;
			}
			//if (DT->dominates(pStore, loadInst)) {
			//if (line == getLineNumber(pStore)) {
				DEBUG(errrawout << '\t' << "return const value " << ret_value << " at line " <<  getLineNumber(pStore) << '\n');
				BasicBlock *bb = pStore->getParent();
				labelConstReturn(line, funcName, bb, pStore, ret_value);
				if (ret_value == "NULL")
					labelReturnStmt(funcName, bb, var);
				ret = 1;
				if (getNumSuccessors(bb) > 1) {
					cond_const_returns[bb] = line;
					DEBUG(errrawout << '\t' << "return const value has condition\n");
				}
			//} else
			//	DEBUG(errrawout << '\t' << "value assignment does not dominate return" << '\n');
		} else if (CallInst *pCall = dyn_cast<CallInst>(arg)) {
			Function *callee = pCall->getCalledFunction();
			if (callee) {
				std::string callee_name = decorateInternalName(callee);
				DEBUG(errrawout << '\t' << "return call at line " << line << '\n');
				dumpCallEx(line, funcName, callee_name, "", -2, 8, NULL, pCall);
			}
		} else if (LoadInst *pLoad = dyn_cast<LoadInst>(arg)) {
			std::list<Instruction *> lu = cfg->get_use_def(pLoad);
			for (std::list<Instruction *>::iterator it = lu.begin(); it != lu.end(); it++) {
				DEBUG(errrawout << '\t' << "check def at line " << getLineNumber(*it) << '\n');
				if (StoreInst *pStore2 = dyn_cast<StoreInst>(*it)) {
					if (CheckReturnConstOrCall(funcName, pStore2, NULL))
						ret = 1;
				}
			}
		}
		return ret;
	}

	int checkReturn(std::string funcName, ReturnInst *retInst) {
		int count_const_ret = 0;
		DEBUG(errrawout << "check return at line " << getLineNumber(retInst) << '\n');
		Value *retVal = retInst->getReturnValue();
		if (retVal) {
			LoadInst *loadInst = NULL;
			PHINode *phiNode = NULL;
			CallInst *callInst = NULL;

			if (CastInst *cast = dyn_cast<CastInst>(retVal))
				retVal = cast->getOperand(0);

			if ((loadInst = dyn_cast<LoadInst>(retVal))) {
					Value *ptr = loadInst->getPointerOperand();
					//if (ptr->getName().str() == "") {
						DEBUG(errrawout << "return var: " << ptr->getName() << '\n');
						std::list<Instruction *> lu = cfg->get_use_def(loadInst);
						for (std::list<Instruction *>::iterator it = lu.begin(); it != lu.end(); it++) {
							DEBUG(errrawout << '\t' << "check def at line " << getLineNumber(*it) << '\n');
							if (StoreInst *pStore = dyn_cast<StoreInst>(*it)) {
								count_const_ret += CheckReturnConstOrCallEx(funcName, pStore, NULL);
							}
						}
					//}
			} else if ((callInst = dyn_cast<CallInst>(retVal))) {
				CheckReturnConstOrCallEx(funcName, NULL, callInst);
			} else if ((phiNode = dyn_cast<PHINode>(retVal))) {
				for (unsigned i = 0; i < phiNode->getNumIncomingValues(); i++) {
					Value *val = phiNode->getIncomingValue(i);
					BasicBlock *pred = phiNode->getIncomingBlock(i);
					TerminatorInst *branch = pred->getTerminator();
					if (branch == NULL) {
						DEBUG(errrawout << "BB at line " << getLineNumber(pred) << " has no terminator\n");
						continue;
					}
					if (dyn_cast<Constant>(val)) {
#if 0
						if (ConstantInt *pInt = dyn_cast<ConstantInt>(val)) {
							if (pInt->getZExtValue() == 0) {
								DEBUG(errrawout << "ignore return const zero at line " << getLineNumber(pred) << '\n');
								continue;
							}
						}
#endif
						int line = getLineNumber(branch);
						std::string ret_value;
						if (getConstValue(val, ret_value) == -1)
							continue;
						DEBUG(errrawout << "return const value (phi)" << ret_value << " at line " << line << '\n');
						labelConstReturn(line, funcName, pred, &pred->back(), ret_value);
						count_const_ret++;
						if (getNumSuccessors(pred) > 1) {
							cond_const_returns[pred] = line;
							DEBUG(errrawout << "return const value has condition\n");
						}
					}
				}
			}
		} else {
			int line = getLineNumber(retInst);
			labelConstReturn(line, funcName, retInst->getParent(), retInst, "None");
			count_const_ret++;
			DEBUG(errrawout << "return none at line " << line << '\n');
		}
		return count_const_ret;
	}

	int findConstReturn(Function *F) {
		int ret = 0;

		std::string funcName = decorateInternalName(F);
		DEBUG(errrawout << "findConstReturn: " << funcName << '\n');
		const_returns.clear();
	    for (Function::iterator bb=F->begin(), bbEnd=F->end(); bb != bbEnd; ++bb) {
			if (bb->empty())
				continue;
			Instruction *inst = &bb->back();
			if (ReturnInst *retInst = dyn_cast<ReturnInst>(inst)) {
				ret = checkReturn(funcName, retInst);
			}
		}
		return ret;
	}

	void findDependency(Function *F) {
		dependency.clear();

		for (Function::iterator bb=F->begin(), bbEnd=F->end(); bb != bbEnd; ++bb){	
			for (BasicBlock::iterator i=bb->begin(), iend=bb->end(); i != iend; ++i){
				if (BranchInst *branch = dyn_cast<BranchInst>(i)) {
					if (branch->isConditional()) {
						labelDependency(F, &(*bb), branch);
					}
				} else if (SwitchInst *branch = dyn_cast<SwitchInst>(i)) {
					labelDependency(F, &(*bb), branch);
				}
			}
		}
	}

	int labelCheckedCalls(std::string funcName, LoadInst *pLoad, int valIdx, CmpInst *pCmp) {
		int ret = 0;
		Instruction *ins = NULL;
			
		if (pLoad) {
			std::list<Instruction *> lu = cfg->get_use_def(pLoad);
			for (std::list<Instruction *>::iterator it = lu.begin(); it != lu.end(); it++) {
				ins = *it;
				if (StoreInst *pStore = dyn_cast<StoreInst>(ins)) {
					ins = dyn_cast<Instruction>(pStore->getValueOperand());
				}
				break;
			}
		} else {
			ins = dyn_cast<Instruction>(pCmp->getOperand(1 - valIdx));
		}
		if (ins) {
			if (CallInst *pCall = dyn_cast<CallInst>(ins)) {

				checkedCalls[pCall] = pCmp;

				std::string pred = predicate2String(pCmp->getPredicate());
				std::string value = ConvArgToStr(pCmp, pCmp->getOperand(valIdx));
				DEBUG(errrawout << "Found checked call at line " << getLineNumber(pCmp) << ':' << pred << value << '\n');
				Function *callee = pCall->getCalledFunction();
				if (callee) {
					std::string calleeName = decorateInternalName(callee);
					dumpCallEx(getLineNumber(pCmp), funcName, calleeName, value + ',' + pred, -2, 12, NULL, NULL);
				}
				ret = 1;
			}
		}
		return ret;
	}

	std::string getPrototype(Function *F) {
		std::string str;
		raw_string_ostream strout(str);
		bool first = true;

		F->getReturnType()->print(strout);
		strout << '(';
		for (Function::arg_iterator I = F->arg_begin(), E = F->arg_end(); I != E; ++I) {
			Argument* arg = &*I;
			// Check whether it's passed by reference
			const Type* T = arg->getType();
			if (first)
				first = false;
			else
				strout << ',';
			T->print(strout);
		}
		strout << ')';
		return str;
	}

	LoadInst* getCmpVar(CmpInst *cmp, int& varIdx, int& valIdx) {
		if (dyn_cast<Instruction>(cmp->getOperand(0))) {
			varIdx = 0;
			valIdx = 1;
		} else if (dyn_cast<Instruction>(cmp->getOperand(1))) {
			varIdx = 1;
			valIdx = 0;
		} else
			varIdx = -1;
		if (varIdx >= 0)
			return dyn_cast<LoadInst>(cmp->getOperand(varIdx));
		else
			return NULL;
	}

	/*
		findMethod:
			Its output consists of a series of lines, each of which represents a function call.
			Each line contains 10 or more fields, separated by '@'. Each field is explained as below.
			
			# 0: modulename
			# 1: directory
			# 2: filename
			# 3: lineNum 
			# 4: functionName 
			# 5: BBID
			# 6: dominateBBID
			# 7: calleeName
			# 8: key name
			# 9: access type 
			#	'0' - read, '1' - write, when call type is 2
			#	'-1' - function call, when call type is 0 or 1
			#	'-2' - other, when call type is 3, 4, 5, etc.
			#	The BB (line number) in which a key is accessed, that this BB (line) refers to, when call type is 6
			# 	The BB (line number which is dominated by the line, when call type is 7
			# 10: call type '0' - non-API call, '1' - API call, '2' - direct access, '3' - dependency, '4' - FP definition, '5' - FP call, '6' - reference, '7' - const return, '8' - return call, '9' - call with missed check, '10' - simple path, '11' - return NULL, '12' - checked call
			# For function call:
			# 	The remaining fields represents each argument of the function call:
			# 	number - numeric argument
			# 	double-quoted string - string argument
			# 	single-quoted number - formal argument of the function making the call
	*/	
    void findMethod(Function *F) {
	std::string funcName = decorateInternalName(F);
	DEBUG(errrawout << "findMethod: " << funcName << '\n');
	prototypes[funcName] = getPrototype(F);
/*
	for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {
		  	Instruction *pi = dyn_cast<Instruction>(&*I);
			BasicBlock *bb = pi->getParent();
			DEBUG(errrawout << '\t' << bb << ", " << BlockAddress::get(F, bb) << ", " << pi << '\n');
	}

	for (Function::iterator BB = F->begin(), E = F->end(); BB != E; ++BB) {
		BasicBlock *bb = BB;

		for (BasicBlock::iterator i=bb->begin(), iend=bb->end(); i != iend; ++i){
			Instruction *pi = dyn_cast<Instruction>(i);
			DEBUG(errrawout << '\t' << bb << ", " << BlockAddress::get(F, bb) << ", " << pi << '\n');
		}
	}
*/

    for (Function::iterator bb=F->begin(), bbEnd=F->end(); bb != bbEnd; ++bb){	
		for (BasicBlock::iterator i=bb->begin(), iend=bb->end(); i != iend; ++i){
			if (ICmpInst *cmp = dyn_cast<ICmpInst>(i)) {
				int valIdx, varIdx;
				LoadInst *pLoad = getCmpVar(cmp, varIdx, valIdx);
				if (varIdx >= 0) {
					if (pLoad) {
						labelCheckedCalls(funcName, pLoad, valIdx, cmp);
						std::string var = getVarName(pLoad);
						if (var != "") {
							std::string value = ConvArgToStr(cmp, cmp->getOperand(valIdx));
							if (value != "")
								labelGuardingCondition(var, value, pLoad);
						}
					} else
						labelCheckedCalls(funcName, NULL, valIdx, cmp);
				}
			}
		}
	}
	
		//int firstLine = 0;

	// Iterate over all BB
        for (Function::iterator bb=F->begin(), bbEnd=F->end(); bb != bbEnd; ++bb){
		// Loops over all instructions 
		for (BasicBlock::iterator i=bb->begin(), iend=bb->end(); i != iend; ++i){
			// Check each instruction and operate only on CallInst.
			Function *func = NULL;
			Value *arg = NULL;
			std::string fname;
			int Line = 0;
			LoadInst *load = NULL;
			std::string vname;
			CallInst *call = dyn_cast<CallInst>(i);

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 8)
			const DebugLoc& Loc = i->getDebugLoc();
			if (Loc) 
				Line = Loc.getLine();
#else
			if (MDNode *N = i->getMetadata("dbg")) {
			   DILocation Loc(N);
			   Line = Loc.getLineNumber();
			}
#endif

			if (Line > 0) {
				analyzed_lines[funcName].insert(Line);
				if (first_lines.find(funcName) == first_lines.end()) {
					DEBUG(errrawout << "first line: " << Line << '\n');
					first_lines[funcName] = Line;
				}
			}

			// skip llvm dbg calls
			if (call) {
				func = call->getCalledFunction();
				if (func) {
					fname = func->getName().str();
					if (fname == "llvm.dbg.declare")
						continue;
				}
			}
			// may change to use "CallSite" instead CallInst or InvokeInst separately
			if (call) {
				// Identify return call that does not have error handling
				if (call->use_begin() != call->use_end()) {
					Instruction *ins = dyn_cast<Instruction>(*call->use_begin());
					if (ins) {
						if (StoreInst *store = dyn_cast<StoreInst>(ins)) {
							Value *var = store->getPointerOperand();
							Type *type = var->getType();
							type = type->getPointerElementType();
							if (type->isPointerTy()) {
								if (checkedCalls.find(call) == checkedCalls.end()) {
									if (CallErrorHandling.find(var) != CallErrorHandling.end())
										if (CallErrorHandling[var].find(call) == CallErrorHandling[var].end()) {
											Function *callee = call->getCalledFunction();
											if (callee) {
												std::string callee_name = decorateInternalName(callee);
												std::stringstream ss;
												std::map<CallInst *, std::pair<int, int> >::iterator it = CallErrorHandling[var].begin();
												ss << it->second.first << ',' << it->second.second << ',' << getNextLineNumber(&(*bb), i);
												dumpCallEx(Line, funcName, callee_name, ss.str(), -2, 9, NULL, NULL);
												DEBUG(errrawout << '\t' << "call at line " << getLineNumber(call) << " misses error handling\n");
												DEBUG(errrawout << "\t\t" << "add error handling " << it->second.first << " - " << it->second.second << '\n');
											}
										}
								}
							}
						}
					}
				}

				//DEBUG(errrawout << funcName << " make a call at line " << Line << '\n');
				if (func) {
					fname = decorateInternalName(func);
					if ((APIMethods.find(fname) != APIMethods.end()) && (APIMethods[fname].argNum >= 0))
						arg = call->getArgOperand(APIMethods[fname].argNum);
				} else {
					Value *value = call->getCalledValue();
					LoadInst *load = NULL;
					if ((load = dyn_cast<LoadInst>(value))) {
						vname = getLoadStructVarName(load, 0);
						if (vname == "")
							vname =	getFPName(load);
						dumpCall(Line, funcName, "*" + vname, "", -2, 5, i);
					}
				}
			} else if (InvokeInst *invoke = dyn_cast<InvokeInst>(i)) {
				func = invoke->getCalledFunction();
				if (func) {
					fname = decorateInternalName(func);
					if ((APIMethods.find(fname) != APIMethods.end()) && (APIMethods[fname].argNum >= 0))
						arg = invoke->getArgOperand(APIMethods[fname].argNum);
				}
			} else if ((load = dyn_cast<LoadInst>(i))) {
				vname = getLoadStructVarName(load, 0);
			} else if (StoreInst *store = dyn_cast<StoreInst>(i)) {
				GEPOperator *gep = NULL;
				bool erase = false;
				Instruction *inst = NULL;
				if (ConstantExpr* cexp = dyn_cast<ConstantExpr>(store->getPointerOperand())) {
					gep = dyn_cast<GEPOperator>(cexp);
				} else 
					gep = dyn_cast<GEPOperator>(store->getPointerOperand());
				if (gep) {
					//Value *arg = gep->getPointerOperand();
					Type *type = gep->getPointerOperandType()->getPointerElementType();
					if (type->isStructTy()) {
#ifdef DEBUG2
						DEBUG(errrawout << "Store struct " << arg->getName() << ':' << type->getStructName() << " at line " << Line << '\n');
#endif
					}
				}
				if (erase) {
					inst->dropAllReferences();
					if (inst->getParent())
						inst->eraseFromParent();
				}
				// handle reference to function pointer
				Value *arg = store->getValueOperand();
				Type *type = arg->getType();
				while (type->isPointerTy()) {
					type = type->getPointerElementType();
				}
				if (type->isFunctionTy()) {
					DEBUG(errrawout << "Store function pointer " << arg->getName() << " at line " << Line << '\n');
					//dumpCall(Line, funcName, arg->getName() , "", -1, 0, i);
					fp_count ++;
					std::string name;
					ConstantExpr *exp = dyn_cast<ConstantExpr>(arg);
					if (exp) {
						Instruction *inst = exp->getAsInstruction();
						CastInst *cinst = dyn_cast<CastInst>(inst);
						if (cinst) {
							arg = cinst->getOperand(0);
						}
						if (inst) {
							inst->dropAllReferences();
							if (inst->getParent())
								inst->eraseFromParent();
						}
					}
					if (dyn_cast<Function>(arg))
						name = decorateInternalName(dyn_cast<Function>(arg));
					else
						name = arg->getName();
					std::string fp = getStoreStructVarName(store, 0);
					if (fp == "")
						fp = store->getPointerOperand()->getName();
					dumpCallEx(-fp_count, "*" + fp, name, "", -2, 4, NULL, NULL);
				}
			} else	{
#ifdef DEBUG2
				Instruction *inst = dyn_cast<Instruction>(i);
				DEBUG(errrawout << "Instruction " << inst->getOpcodeName() << " at line " << Line << '\n');
#endif
			}
			if (func) {
				if (APIMethods.find(fname) != APIMethods.end()) {
					// Find direct call to an API method
#ifdef DEBUG2
					DEBUG(errrawout << funcName << " calls " << fname << " at line " << Line << '\n');
#endif
					APIMethods[fname].references ++;
#ifdef DEBUG2
					if (arg) {
						DEBUG(errrawout << "args " << APIMethods[fname].argNum << " type: " << arg->getType()->getTypeID() << '\n');
						arg->print(errrawout);
					}
#endif
					std::string parm;
					if (arg)
						parm = ConvArgToStr(&(*i), arg);
					else if (APIMethods[fname].argNum == -1) {
						parm = "\"INT_OPTION\"";
					}
					if (parm != "" && parm[0] == '"') {
						dumpCall(Line, funcName, fname, parm, APIMethods[fname].type, 1, i);
						//output << M.getModuleIdentifier() << FIELD_SEP << Dir.str() << FIELD_SEP << File.str() << FIELD_SEP << Line << FIELD_SEP <<  << FIELD_SEP << bb << FIELD_SEP << pb << FIELD_SEP << fname << FIELD_SEP << parm.c_str() << FIELD_SEP << A << FIELD_SEP << '1';					
					} else {
						if (arg && dyn_cast<LoadInst>(arg))
							errrawout << "Warning: arg is load: " << ModuleName << FIELD_SEP << Dir << FIELD_SEP << File << FIELD_SEP << Line << FIELD_SEP << funcName << FIELD_SEP << arg << FIELD_SEP << fname << FIELD_SEP << FIELD_SEP << FIELD_SEP;
						else
							errrawout << "Error: " << ModuleName << FIELD_SEP << Dir << FIELD_SEP << File << FIELD_SEP << Line << FIELD_SEP << funcName << FIELD_SEP << arg << FIELD_SEP << fname << FIELD_SEP << FIELD_SEP << FIELD_SEP;
						dumpCall(Line, funcName, fname, "", APIMethods[fname].type, 1, i);
						//output << M.getModuleIdentifier() << FIELD_SEP << Dir.str() << FIELD_SEP << File.str() << FIELD_SEP << Line << FIELD_SEP << funcName << FIELD_SEP << bb << FIELD_SEP << pb << FIELD_SEP << fname << FIELD_SEP << FIELD_SEP << FIELD_SEP << '1';
					}
				} else {
#ifdef DEBUG2
					DEBUG(errrawout << funcName << " calls " << fname << " at line " << Line << '\n');
#endif
					// Find a call to another function
					dumpCall(Line, funcName, fname, "", -1, 0, i);
					//output << M.getModuleIdentifier() << FIELD_SEP << Dir.str() << FIELD_SEP << File.str() << FIELD_SEP << Line << FIELD_SEP << funcName << FIELD_SEP << bb << FIELD_SEP << pb << FIELD_SEP << fname << FIELD_SEP << FIELD_SEP << FIELD_SEP << '0';
				}
				
			}else{
			// TODO: handle indirect calls
			}
			if (load && vname != "") {
#ifdef DEBUG2
				DEBUG(errrawout << funcName << " loads " << vname << " at line " << Line << '\n');
#endif
				dumpCall(Line, funcName, "", '"' + vname + '"', 0, 2, i);
			}
			// For dependency
			std::set<std::pair<const Instruction*, int> > dependentInstrs;
			//if (!func && !load && Line && getDependentInstr(i, dependentInstrs))
			
			if (Line) {
			  if (getDependentInstr(&(*i), dependentInstrs)) {
			    //DEBUG(errrawout << "print dependency for " << funcName << ':' << Line << ":yes\n");
				dumpCall(Line, funcName, "", "", -2, 3, i);
			  } //else
			    //DEBUG(errrawout << "print dependency for " << funcName << ':' << Line << ":no\n");
			}
		    }
		}
    }

	// ======================  Helper functions

	// Step 1 Loop over all of the global variables, and copy them to the LSV
	void addGlobalVariables(Module* M, VarMap& LSV){
		for (Module::global_iterator I = M->global_begin(), E = M->global_end(); I != E; ++I) {
			GlobalVariable *GV = &*I;
			LSV[GV] = GV->getName();
			DEBUG(errrawout << "Adding global variable: " << GV->getName() << " to LSV\n");
/*
			for (Value::use_iterator i = GV->use_begin(), e = GV->use_end(); i != e; ++i) {
				if (Instruction *Inst = dyn_cast<Instruction>(*i)) {
					DEBUG(errrawout << *Inst << "\n");
				}
			}
*/
		}
	}

	// Step 2 Add any arguments passed in by reference to the subroutine 
	void addPointerParameters(Function *F, VarMap& LSV){
		for (Function::arg_iterator I = F->arg_begin(), E = F->arg_end(); I != E; ++I) {
			Argument* arg = &*I;
			// Check whether it's passed by reference
			const Type* T = arg->getType();
			if ( T->isPointerTy() || T->isArrayTy() ){
				LSV[arg] = arg->getName();
				DEBUG(errrawout << "Add pointer parameter: " << arg->getName() << " to LSV\n");
			}
		}
	}

	// Step 3 add all pointers returned from subroutines into the LSV
	void addSubroutineReturnValues(Function *F, VarMap& LSV){
		// Iterate over all BB
        for (Function::iterator bb=F->begin(), bbEnd=F->end(); bb != bbEnd; ++bb){
			// Loops over all instructions 
			for (BasicBlock::iterator i=bb->begin(), iend=bb->end(); i != iend; ++i){
				// Check each instruction and operate only on CallInst.
				if (CallInst *call = dyn_cast<CallInst>(i)) {
					Function *func = call->getCalledFunction();
					if (func) {
						const Type* return_type = func->getReturnType();
						if ( return_type -> isPointerTy() ){
							std::string fname = func->getName();
							BasicBlock::iterator in = i;
							++in;
							if (StoreInst *si = dyn_cast<StoreInst>(in)) {
								Value *ptr = si->getPointerOperand();
								LSV[ptr] = ptr->getName();
								DEBUG(errrawout << "Add returned pointer: " << ptr->getName() << " to LSV\n");
							}
						}
					}else{
					// TODO: handle indirect calls
					}
			   }
			}
		}
	}


	// Step 4 Perform DFA to include all variables that are dependent on anything in the LSV 
	void expandLSV(Function *F, VarMap& LSV){
	}

	std::vector<Bitvector>  reachAccAnalysis(Cfg *cfg){
		std::vector<Bitvector> reachAcc;
		if (cfg->get_basicblockcount() > 0) {
			Dataflow *df = new ReachAcc(cfg, cfg->get_access_set(0).size());
			df->analyze();
			reachAcc = df->get_in_sets();
			DEBUG(errrawout << "Reaching Accesses:\n");
			for (unsigned b = 0; b < reachAcc.size(); ++b) {
				DEBUG(errrawout << b << ":" << reachAcc[b].tostring() << '\n');
			}
		}
		return reachAcc;
	}

	void reachDefAnalysis(Function *F){
		VarMap LSV;
		if (cfg)
			delete cfg;
		cfg = new LLVMCfg(F, LSV);
#ifdef DEBUG3
		DEBUG(errrawout << "Reaching Definitions\n");
		cfg->dump();
		cfg->dump_definitions();
#endif

		if (cfg->get_basicblockcount() > 0) {
			if (df)
				delete df;
			df = new ReachDef(cfg, cfg->get_gen_set(0).size());
			df->analyze();
			std::vector<Bitvector> in_sets, out_sets;
			in_sets = df->get_in_sets();
			out_sets = df->get_out_sets();
#ifdef DEBUG3
			DEBUG(errrawout << "Reaching Definitions:\n");
			for (unsigned b = 0; b < cfg->get_basicblockcount(); ++b) {
				DEBUG(errrawout << b << ":" << in_sets[b].tostring() << " -> " << out_sets[b].tostring() << '\n');
			}
#endif
			cfg->gen_use_def(F, df);
		}
#ifdef DEBUG3
		cfg->dump_use_def();
#endif
	}

    // We don't modify the program, so we preserve all analyses
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesAll();
	  AU.setPreservesCFG();
	  //AU.addRequired<LoopInfo>();
	  AU.addRequired<PostDominatorTree>();
	  // LLVM 3.3, 3.8
#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 8)
	  AU.addRequired<DominatorTreeWrapperPass>();
	  // LLVM 3.4.2
#else
	  AU.addRequired<DominatorTree>();
#endif
    }

	void findCalls(Function *F, VarMap& LSV){
		// Iterate over all BB
        for (Function::iterator bb=F->begin(), bbEnd=F->end(); bb != bbEnd; ++bb){
			// Loops over all instructions 
			for (BasicBlock::iterator i=bb->begin(), iend=bb->end(); i != iend; ++i){
				// Check each instruction and operate only on CallInst.
				if (CallInst *call = dyn_cast<CallInst>(i)) {
					Function *func = call->getCalledFunction();
					if (func) {
						const Type* return_type = func->getReturnType();
						if ( return_type -> isPointerTy() ){
							std::string fname = func->getName();
							BasicBlock::iterator in = i;
							++in;
							if (StoreInst *si = dyn_cast<StoreInst>(in)) {
								Value *ptr = si->getPointerOperand();
								LSV[ptr] = ptr->getName();
								DEBUG(errrawout << "Add returned pointer: " << ptr->getName() << " to LSV\n");
							}
						}
					}else{
					// TODO: handle indirect calls
					}
			   }
			}
		}
	}

  };
}


char Analyzer::ID = 0;
static RegisterPass<Analyzer> X("Analyzer", "Analyzer Module Pass", false, false);
