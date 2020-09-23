#!/usr/bin/python

import sys, os
from talos import Talos

class HotSpot:
	def __init__(self):
		allArgs = ['pattern', 'Debug', 'input', 'NameList', 'PathCount', 'ControlPoints', 'EntryFunc', 'InteractiveMode', 'Verbose', 'IgnoreEntryFunc', 'AddSecuritySetting', 'DelSecuritySetting', 'IdentifyWorkarounds', 'IdentifyOneWorkaround', 'SettingsFile', 'CheckOnly', 'AddExecLog', 'CondExecFuncs']
		self.args = {}
		for name in allArgs:
			self.args[name] = None
		os.chdir(os.environ['TALOS_DIR'])
		self.load_sps_funcs()
		self.load_nsps_funcs()

	def load_sps_funcs(self):
		# nsp_sp_funcs: sensitive-partition specific functions
		self.sensitive_funcs = ['pw_lock', 'pw_open', 'spw_lock', 'spw_open', 'pw_update', 'spw_update', 'pw_close', 'spw_close']

	def load_nsps_funcs(self):
		# nsp_sp_funcs: non-sensitive-partition specific functions
		self.nsp_sp_funcs = ['fprintf']

	def run(self, entryFunc, inputFile):
		args = {'EntryFunc':[entryFunc], 'input':[inputFile]}
		for name in args:
			self.args[name] = args[name]
		talos = Talos(self.args)
		countCases = {}
		for f in talos.RetCheckedFunc:
			#print f + ':'
			if f in self.sensitive_funcs:
				for BB in talos.RetCheckedFunc[f]:
					#print '\t', talos.get_name_for_BB(BB)
					if BB not in talos.ControlBBs:
						continue
					for edge in talos.ControlBBs[BB]:
						for B in talos.ControlBBs[BB][edge]:
							if B in talos.Callees:
								#print talos.Callees[B] in self.nsp_sp_funcs:
								if talos.Callees[B] in self.nsp_sp_funcs:
									#print '\t\t', talos.get_name_for_BB(B), talos.BB2CallerName(B), talos.BB2CalleeName(B) 
									caller = talos.BB2CallerName(B)
									if caller in countCases:
										countCases[caller] += 1
									else:
										countCases[caller] = 1
		for f in countCases:
			print f, countCases[f]

if __name__ == '__main__':
	hs = HotSpot()
	hs.run(sys.argv[1], sys.argv[2])
