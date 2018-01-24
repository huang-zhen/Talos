#!/usr/bin/python
# find config options on which a code fragment is control dependent
import sys, os, copy, time, argparse, re
# Import readline to fix a Python bug with raw_input
import readline
# data structures
# FunctionLines: funcName => [line_count, start_line, return_line, path_name, protoType, definedbyMacro]
# ErrorFuncs: funcName => [arg_idx, arg_val, ret, args] 
# 	arguments at arg_idx is compared against the arg_val to determine if indeed
# 	an error handling function is called
#	The SWRR for functions that directly calls error functions contains a call to
# 	the corresponding error function with args
# ErrorReturns: functionName => kind => [((BB, ret_value), (BB, ret_value), ...]
# 	kind: 1 - error logging/handling, 3 - pointer returnning, 4 - propagation

def usage():
	print "Usage: dependency InputFile [Location]"
	sys.exit()

def get_file(dir, file):
	if not (dir, file) in Files:
		#print >>sys.stderr, 'Adding file ', dir, file
		Files[(dir, file)] = len(Files)
		FileRef[Files[(dir, file)]] = (dir, file)
		if Debug:
			print >> sys.stderr, 'Added file',' (', dir, ',', file, ')', '=', Files[(dir, file)]
	return Files[(dir, file)]

def get_function(dir, file, function):
	if not (dir, file, function) in Functions:
		ID = len(Functions)
		Functions[(dir, file, function)] = ID
		FunctionRef[ID] = (dir, file, function)
		if Debug:
			print >> sys.stderr, 'Added function', '(', dir, ',', file, ',', function, ')', '=', ID
	else:
		ID = Functions[(dir, file, function)]
	if not function in FunctionLocation:
		FunctionLocation[function] = set()
	FunctionLocation[function].add(ID)
	return ID

def get_BB(fileID, functionID, line, BB, callee=""):
	if not (fileID, BB, callee) in BBs:
		ID = len(BBs)
		BBs[(fileID, BB, callee)] = ID
		Lines[(fileID, line)] = ID
		if Debug:
			print >> sys.stderr, 'Added BB', ID, '=', fileID, line, BB, callee
	else:
		ID = BBs[(fileID, BB, callee)]
	if line != 0:
		if not ID in BBref:
			BBref[ID] = (fileID, line)
		elif (fileID, line) != BBref[ID]:
			if Debug:
				print >> sys.stderr, 'Warning: BB', ID,  '(', fileID, line, ')', 'already defined in BBref for', BBref[ID]
		if not ID in BBrefFunc:
			BBrefFunc[ID] = functionID
			if Debug:
				print >> sys.stderr, 'BB', ID, 'is defined for', functionID
		elif functionID != BBrefFunc[ID]:
			if Debug:
				print >> sys.stderr, 'Warning: BB', ID, '(', functionID, ')', 'already defined in BBrefFunc for', BBrefFunc[ID]
	return ID

# get BB ID giving priority to BB ID corresponding to function call
def get_BB2(fileID, functionID, line, BB):
	if (fileID, line) in LineOfCall:
		return LineOfCall[(fileID, line)]
	else:
		return get_BB(fileID, functionID, line, BB)

# kind: 1 - error logging/handling, 3 - pointer returnning, 4 - propagation
def add_error_return(kind, func, BB, ret_value):
	#print >>sys.stderr, 'add_error_return', func, BB, ret_value, kind
	if not func in ErrorReturns:
		ErrorReturns[func] = {}
	if not kind in ErrorReturns[func]:
		ErrorReturns[func][kind] = []
	if not (BB, ret_value) in ErrorReturns[func][kind]:
		ErrorReturns[func][kind].insert(0, (BB, ret_value))	

# return the BB for an error return
def get_error_return_BB(func):
	return get_error_return(func)[1][0]

def get_error_return(func):
	for kind in ErrorReturnPriority:
		if kind in ErrorReturns[func]:
			return (kind, ErrorReturns[func][kind][0])
	return None

# return the return value for an error return
def get_error_return_value(func):
	#return get_error_return(func)[1]
	ret = get_error_return(func)
	if ret:
		return ret[0], ret[1][1]
	else:
		return None

def copy_error_return(funcSrc, funcTo):
	kind, errorRet = get_error_return(funcSrc)
	add_error_return(10, funcTo, errorRet[0], errorRet[1])

def get_all_error_return(func):
	return ErrorReturns[func]

def reverse_predicate(pred):
	return PredicateOpps[pred]
	
# pred_satisfiable
#	lhs: name of a function
def pred_satisfiable(lhs, pred, rhs):
	print >>sys.stderr, 'pred_satisfiable', lhs, pred, rhs
	return PredicateFuncs[pred](lhs, rhs)

def is_ret_value_satisfy_pred(funcName, pred, rhs):
	print >>sys.stderr, 'is_ret_value_satisfy_pred', funcName
	for kind in ErrorReturns[funcName]:
		for (BB, value) in ErrorReturns[funcName][kind]:
			if pred_satisfiable(value, pred, rhs):
				return True
	return False

def get_ret_value_to_satisfy_pred(pred, rhs):
	print >>sys.stderr, 'get_ret_value_to_satisfy_pred', pred, rhs
	if rhs == 'None' or rhs == '':
		return None
	elif pred == '==':
		return rhs
	elif rhs == 'NULL':
		return None
	elif rhs[0] == "'":
		return None
	elif pred == '!=':
		return str(1 - int(rhs))
	elif pred == '>' or pred == '>=':
		return str(int(rhs) + 1)
	elif pred == '<' or pred == '<=':
		return str(int(rhs) - 1)
	else:
		return None

# valid_return
# 	return_desc: start_line, end_line, return_var
def valid_return(return_desc):
	parts = return_desc.split(',')
	if parts[0] != '0' and parts[1] != '0':
		return True
	else:
		return False	

# for direct API Calls
# InputFile fields:
# 0. modulename
# 1. directory
# 2. filename
# 3. lineNum 
# 4. functionName 
# 5. BBID
# 6. dominateBBID
# 7. calleeName
# 8. key name
# 9: Access type 
#	'0' - Read, '1' - write, when call type is 2
#	'-1' - function call, when call type is 0 or 1
#	'-2' - other, when call type is 4, or 5, etc.
#	The BB (line number) in which a key is accessed, that this BB (line) refers to, when call type is 6
# 10: call type '0' - non-API call, '1' - API call, '2' - direct Access, '3' - dependency, '4' - FP definition, '5' - FP call, '6' - reference, '7' - return const, '8' - return call, '9' - call with missed check, '10' - simple path, '11' - return NULL
# For function call:
# 	The remaining fields represents each argument of the function call:
# 	number - numeric argument
# 	double-quoted string - string argument
# 	single-quoted number - formal argument of the function making the call

# initialize and identify API wrappers
# load data into various data structures:
#	 Files, FileRef, Functions, FunctionRef, FunctionLocation, BBs, Lines, BBref, BBrefFunc, BBDependency, APIs, References
def pass1(InputFile):
	print "Pass 1...initialize"
	startTime = time.time()
	countWrappers = 0
	lineNo = 0
	input = open(InputFile, 'r')
	for line in input:
		lineNo = lineNo + 1
		if lineNo % 100000 == 0:
			print 'Processed', lineNo, 'lines'
		if Debug:
			print >> sys.stderr, "Processing line", lineNo
		line = line.strip()
		parts = line.split('@')
		if len(parts) < 11:
			print "Invalid number of fields at line", lineNo
		#print parts
		functionName = parts[4]
		if functionName == '*':
			print "Ignoring * as caller at line", lineNo
			continue
		calleeName = parts[7]
		try:
			functionID = get_function(parts[1], parts[2], functionName)
		except IndexError:
			print >> sys.stderr, 'Error in line', lineNo, ',', parts
		fileID = get_file(parts[1], parts[2])
		BB = get_BB(fileID, functionID, parts[3], parts[5], calleeName)
		#if parts[10] == '2' and (not calleeName):
		#	print 'Missing callee in line', lineNo
		#	continue
		if calleeName:
			if not calleeName in RCalls:
				RCalls[calleeName] = set()
			RCalls[calleeName].add(BB)
			if not functionName in Calls:
				Calls[functionName] = set()
			Calls[functionName].add(BB)
			#print >> sys.stderr, lineNo, functionName, 'calls', calleeName, BB
			Callees[BB] = calleeName
			LineOfCall[(fileID, parts[3])] = BB
		#if (calleeName in APIs) and (not functionName in APIs):
		if parts[10].find(',') > 0:
			retInfo = parts[10].split(',')
			callType = int(retInfo[0])
			ret_line = int(retInfo[1])
			ret_value = retInfo[2]
			ret_BB = get_BB(fileID, functionID, str(ret_line), str(ret_line))
			BBFollowByReturn[BB] = (ret_BB, ret_value, fileID);
		
			if ret_value == "NULL":
				#print >> sys.stderr, lineNo, functionName, 'returns NULL'
				if not functionName in FunctionLines:
					FunctionLines[functionName] = [0, 0, -int(parts[3]), None, None, None]
				else:
					FunctionLines[functionName][2] = -int(parts[3])
				add_error_return(3, functionName, BB, ret_value)
		else:
			try:
				callType = int(parts[10])
			except ValueError:
				callType = 0
				print >> sys.stderr, 'Invalid callType in line', lineNo, ',', parts
				continue
		if callType == 10:
			FuncSimplePath[functionName] = parts[8]
			# take out simple path heuristics for now
			#add_error_return(2, functionName, BB, parts[8])
			continue
		if callType == 11:
			if valid_return(parts[8]):
				if not functionName in NullReturns:
					NullReturns[functionName] = []
				NullReturns[functionName].append((BB, parts[8]))
				if not functionName in FunctionLines:
					FunctionLines[functionName] = [0, 0, 0, os.path.join(parts[1], parts[2]), None, None]
				else:
					FunctionLines[functionName][3]  = os.path.join(parts[1], parts[2])
			continue
		if callType == 9:
			error_handle_lines = parts[8].split(',')
			print >> sys.stderr, "Line", lineNo, "unchecked call", calleeName, "is called by", functionName, error_handle_lines
			if not calleeName in UncheckedCalls:
				UncheckedCalls[calleeName] = {}
			UncheckedCalls[calleeName][functionName] = (int(error_handle_lines[2]), int(error_handle_lines[0]), int(error_handle_lines[1]))
			continue
		if callType == 8:
			if not calleeName in RetCalls:
				RetCalls[calleeName] = set()
			RetCalls[calleeName].add((functionName, BB))
			continue
		if callType == 7:
			if not functionName in ConstReturns:
				ConstReturns[functionName] = set()
			ConstReturns[functionName].add((BB, parts[8]))
			if parts[8] == 'NULL':
				add_error_return(3, functionName, BB, 'NULL')
			continue
		if callType == 12:
			if not calleeName in RetCheckedFunc:
				RetCheckedFunc[calleeName] = set()
			RetCheckedFunc[calleeName].add(BB)
			val = parts[8].split(',')[0]
			pred = parts[8].split(',')[1]
			# Only two-way branch is considered
			if not (BB, 0) in CondChecks:
				CondChecks[(BB, 0)] = set()
			CondChecks[(BB, 0)].add((pred, calleeName, val))
			if not (BB, 1) in CondChecks:
				CondChecks[(BB, 1)] = set()
			CondChecks[(BB, 1)].add((reverse_predicate(pred), calleeName, val))
			continue
		#if calleeName:
		#	if callType >= 100:
		#		BBFollowByReturn[BB] = (callType / 1000, (callType % 1000) / 100);
		#		callType %= 100
		if callType == 6: # reference
			rBB = parts[9]
			referBB = get_BB(fileID, functionID, rBB, rBB)
			if not BB in References:
				References[BB] = set()
			References[BB].add(referBB)
			if Debug:
				print >> sys.stderr, BB, "refers", referBB
		if (parts[6] and parts[6] != '0'):
			#dominateBB = get_BB(fileID, functionID, 0, parts[6])
			for dpBB in parts[6].split(','):
				dBB = dpBB.split(';')[0]
				edge = int(dpBB.split(';')[1])
				if not BB in BBDependency:
					BBDependency[BB] = []
				dominateBB = get_BB2(fileID, functionID, dBB, dBB) # BB is lineNum
				#if dominateBB in References:
				#	for rBB in References[dominateBB]:
				#		BBDependency[BB].add(rBB)
				#else:
				#	BBDependency[BB].add(dominateBB)
				BBDependency[BB].append((dominateBB, edge))
				#print >>sys.stderr, "Added dependency", get_name_for_BB(BB), get_name_for_BB(dominateBB)
				if not dominateBB in ControlBBs:
					ControlBBs[dominateBB] = {}
				if not edge in ControlBBs[dominateBB]:
					ControlBBs[dominateBB][edge] = set()
				ControlBBs[dominateBB][edge].add(BB)
				if not functionID in FuncControlBBs:
					FuncControlBBs[functionID] = set()
				FuncControlBBs[functionID].add((dominateBB, edge))
		else:
			dominateBB = -1
		if callType == 6:
			continue
		if calleeName in APIs:
			APIcall = True
		else:
			APIcall = False
		#if lineNo == 199172:
		#	print 'Debug', APIcall, parts[8] #keyarg, len(parts), parts[keyarg]
		# call API with its own argument
		if APIcall and (not parts[8]):
			keyarg = int(APIs[calleeName][2]) + 11
			if (keyarg < len(parts)) and parts[keyarg] and (parts[keyarg][0] == '\''):
				if Debug:
					print >> sys.stderr, 'Identified wrapper', functionName, 'in line', lineNo
				arg = parts[keyarg][1:-1]
				if not functionName in APIs:
					APIs[functionName] = [1, APIs[calleeName][1], arg]
					countWrappers = countWrappers + 1
	print >> sys.stderr, 'Identified', countWrappers, 'wrappres'
	for api in APIs:
		if APIs[api][0] <> 0:
			print >> sys.stderr, '\t', api, APIs[api]
	end_time = time.time()
	print >> sys.stderr, "Pass 1 done -", end_time - startTime, "seconds"
	print "Pass 1 done"

# process direct API Calls
def pass2(InputFile):
	print "Pass 2...process direct API Calls"
	startTime = time.time()
	lineNo = 0
	input = open(InputFile, 'r')
	for line in input:
		lineNo = lineNo + 1
		if lineNo % 100000 == 0:
			print 'Processed', lineNo, 'lines'
		line = line.strip()
		parts = line.split('@')
		if len(parts) < 11:
			print "Invalid number of fields at line", lineNo
		#print parts
		functionName = parts[4]
		if functionName == '*':
			print "Ignoring * as caller at line", lineNo
			continue
		calleeName = parts[7]
		try:
			functionID = get_function(parts[1], parts[2], functionName)
		except IndexError:
			print >> sys.stderr, 'Error in line', lineNo, ',', parts
		fileID = get_file(parts[1], parts[2])
		BB = get_BB(fileID, functionID, parts[3], parts[5], calleeName)
		if parts[10].find(',') > 0:
			retInfo = parts[10].split(',')
			callType = int(retInfo[0])
			ret_line = int(retInfo[1])
			ret_value = retInfo[2]
		else:
			try:
				callType = int(parts[10])
			except ValueError:
				callType = 0
				print >> sys.stderr, 'Invalid callType in line', lineNo, ',', parts
				continue
		if callType >= 7:
			continue
		if (calleeName in APIs) and (not functionName in APIs):
			APIcall = True
		else:
			APIcall = False
		if callType == 2:
			directCall = True
		else:
			directCall = False
		if calleeName in ErrorFuncs:
			print functionName,"calls error func",calleeName
			arg = int(ErrorFuncs[calleeName][0])
			try:
				print "arg:", parts[11 + arg]
				print "expect:", ErrorFuncs[calleeName][1]
				if ErrorFuncs[calleeName][0] == -1 or (parts[11 + arg] and parts[11 + arg] == ErrorFuncs[calleeName][1]):
					if not functionName in FunctionLines:
						FunctionLines[functionName] = [0, 0, int(parts[3]), None, None, None]
					else:
						FunctionLines[functionName][2] = int(parts[3])
					print functionName,"has an error return"
					add_error_return(0, functionName, BB, calleeName)
			except IndexError:
				print 'Invalid calls to', calleeName, 'in line', lineNo
				continue
		dominateBBs = []
		if (parts[6] != '0'):
			for dpBB in parts[6].split(','):
				dBB = dpBB.split(';')[0]
				dominateBBs.append(get_BB2(fileID, functionID, 0, dpBB))
		if APIcall:
			if not functionID in APIcalls:
				APIcalls[functionID] = set()
			APIcalls[functionID].add(BB)
		# callee = get_function(parts[1], parts[2], parts[7])
		# Do we get a key name?
		#if parts[8]:
		if APIcall:
			if (APIs[calleeName][0] == 0) and parts[8]:
				keyname = parts[8]
			elif (APIs[calleeName][0] == 1):
				if len(parts) <= 11 + int(APIs[calleeName][2]):
					print >> sys.stderr, 'Error in line', lineNo, ',', parts, 'key name does not exist for API call', calleeName, APIs[calleeName][2]
					#sys.exit(0)
					keyname = None
				else:
					keyname = parts[11 + int(APIs[calleeName][2])]
			else:
				keyname = None
			#else:
			#	print >> sys.stderr, 'Error in line', lineNo, ',', parts, "key name does not exist for API call!"
			#	sys.exit(0)
		else:
			# direct Access
			if directCall:
				keyname = parts[8]
		acc_type = -1
		if APIcall or directCall:
			if keyname:
				if keyname[0] == '"':
					keyname = keyname.strip('"')
					if keyname[0] == ',':
						print >> sys.stderr, 'Possible error in line', lineNo, 'key name starts with comma!'
					if not keyname in AllKeys:
						AllKeys[keyname] = {}
						AllKeys[keyname]['Functions'] = set()
						AllKeys[keyname]['BBs'] = set()
						AllKeys[keyname]['dominators'] = set()
						AllKeys[keyname]['dominated BBs'] = set()
					if APIcall:
						if APIs[calleeName][1] == '1':
							acc_type = 1
						elif APIs[calleeName][1] == '0':
							acc_type = 0
					else:
						if parts[9] == '1':
							acc_type = 1
						elif parts[9] == '0':
							acc_type = 0
					# for updates
					#if parts[9] == '1':
					if acc_type == 1:
						if not functionID in Update:
							Update[functionID] = {}
							Update[functionID]['keys'] = set()
							Update[functionID]['BBs'] = set()
						Update[functionID]['keys'].add(keyname)
						Update[functionID]['BBs'].add((keyname, BB))
					# for reads
					#elif parts[9] == '0':
					elif acc_type == 0:
						if not functionID in Read:
							Read[functionID] = {}
							Read[functionID]['keys'] = set()
							Read[functionID]['BBs'] = set()
						Read[functionID]['keys'].add(keyname)
						Read[functionID]['BBs'].add((keyname, BB))
						if not BB in BBread:
							BBread[BB] = set()
						BBread[BB].add(keyname)
					AllKeys[keyname]['Functions'].add(functionID)
					AllKeys[keyname]['BBs'].add(BB)
					for dominateBB in dominateBBs:
						AllKeys[keyname]['dominators'].add(dominateBB)
						AllKeys[keyname]['dominated BBs'].add(BB)
					# can have issue if there are duplicate function names (defined in different Files)
					if not functionName in Access:
						Access[functionName] = set()
					Access[functionName].add(keyname)
				else:				
					print >> sys.stderr, 'Error in line', lineNo, ',', parts, 'invalid key name:', keyname, calleeName, APIs[calleeName][2]
					#sys.exit(0)
					#raise Exception('invalid keyname')
	input.close()
	end_time = time.time()
	print >> sys.stderr, "Pass 2 done -", end_time - startTime, "seconds"
	print "Pass 2 done."

# process indirect API Calls
def pass3(InputFile):
	print "Pass 3...process indirect API Calls"
	countIndirectCalls = 0
	lineNo = 0
	input = open(InputFile, 'r')
	for line in input:
		lineNo = lineNo + 1
		line = line.strip()
		parts = line.split('@')
		if len(parts) < 11:
			print "Invalid number of fields at line", lineNo
		#print parts
		functionName = parts[4]
		calleeName = parts[7]
		try:
			functionID = get_function(parts[1], parts[2], parts[4])
		except IndexError:
			print >> sys.stderr, 'Error in line', lineNo, ',', parts
		fileID = get_file(parts[1], parts[2])
		BB = get_BB(fileID, functionID, parts[3], parts[5])
		#if not functionID in Calls:
		#	Calls[functionID] = set()
		#Calls[functionID].add(parts[7])
		callType = int(parts[10])
		if callType >= 1000:
			callType -= 1000
		if callType == 1 and (not parts[4] in APIs):
			APIcall = True
		else:
			APIcall = False
		if (parts[6] != '0'):
			for dpBB in parts[6].split(','):
				dBB = dpBB.split(';')[0]
				dominateBB = get_BB(fileID, functionID, 0, dBB)
		else:
			dominateBB = -1
		if not APIcall:
			if calleeName in Access:
				countIndirectCalls += 1
				for keyname in Access[calleeName]:
					AllKeys[keyname]['Functions'].add(functionID)
					AllKeys[keyname]['BBs'].add(BB)
					if dominateBB >= 0:
						AllKeys[keyname]['dominators'].add(dominateBB)
						AllKeys[keyname]['dominated BBs'].add(BB)
					if not functionID in Read:
						Read[functionID] = {}
						Read[functionID]['keys'] = set()
						Read[functionID]['BBs'] = set()
					Read[functionID]['keys'].add(keyname)
					Read[functionID]['BBs'].add((keyname, BB))
					if not BB in BBread:
						BBread[BB] = set()
					BBread[BB].add(keyname)
	input.close()
	print >> sys.stderr, 'Identified', countIndirectCalls, "indirect Calls."
	print 'Identified', countIndirectCalls, "indirect Calls."
	print "Pass 3 done."

# identify keys used by UI
def pass4(InputFile):
	print "Pass 4...identify keys used by UI"
	countUIKeys = 0
	lineNo = 0
	input = open(InputFile, 'r')
	for line in input:
		lineNo = lineNo + 1
		line = line.strip()
		parts = line.split('@')
		if len(parts) < 11:
			print "Invalid number of fields at line", lineNo
		#print parts
		functionName = parts[4]
		calleeName = parts[7]
		try:
			functionID = get_function(parts[1], parts[2], functionName)
		except IndexError:
			print >> sys.stderr, 'Error in line', lineNo, ',', parts
		#fileID = get_file(parts[1], parts[2])
		#BB = get_BB(fileID, parts[3], parts[5])
		#print >> sys.stderr, lineNo, calleeName
		if calleeName in UI_APIs:
			arg = int(UI_APIs[calleeName][2])
			if parts[11 + arg] and parts[11 + arg][0] == '"':
				countUIKeys = countUIKeys + 1
				UI_Keys[parts[11 + arg].strip('"')] = [functionID, parts[3]]
	input.close()
	print >> sys.stderr, 'Identified', countUIKeys, 'keys used by UI'
	print 'Identified', countUIKeys, 'keys used by UI'
	for key in UI_Keys:
		print '\t', key
	print "Pass 4 done."

def compare(rule1, rule2):
	#print rule1, rule2, correlations[rule1][0], correlations[rule2][0]
	if correlations[rule1][0] < correlations[rule2][0]:
		return -1
	elif correlations[rule1][0] > correlations[rule2][0]:
		return 1
	else:
		return 0

def load_cfg(filename):
	lineNo = 0
	input = open(filename, 'r')
	while input:
		line = input.readline()
		if not line:
			break
		lineNo = lineNo + 1
		line = line.strip()
		if not line:
			continue
		if line[0] == '#':
			continue
		parts = line.split(',')
		method = ''
		for i in range(1, len(parts) - 1):
			if method:
				method = method + ', ' + parts[i].strip()
			else:
				method = parts[i].strip()
		if parts[0] == '0' or parts[0] == '1':
			APIs[method] = [0, parts[0], parts[-1]] # type (0 - API, 1 - wrapper), Access (0 -Read, 1 - write), argument number
		elif parts[0] == '2':
			UI_APIs[method] = [0, parts[0], parts[-1]] # type (0 - API, 1 - wrapper), Access (0 -Read, 1 - write), argument number
		elif parts[0] == '3':
			ConfigKeys.append(parts[1].strip())
		elif parts[0] == '5':
			LoggingFuncs.append(parts[1].strip())
		elif parts[0] == '6':
			name = parts[1].strip()
			idx = parts[2].strip()
			val = parts[3].strip()
			ret = parts[4].strip()
			args = parts[5].strip()
			ErrorFuncs[name] = [int(idx), val, ret, args]
		elif parts[0] == '7':
			name = parts[1].strip()
			ret = parts[2].strip()
			add_error_return(1, name, None, ret)
	input.close()
	#print ConfigKeys


# print prefix + directory + filename + functionname + linenumber + text
def prt_with_location(prefix, functionID, line, text):
	output = prefix
	if functionID != '':
		output = output + FunctionRef[functionID][0] + '/' + FunctionRef[functionID][1] + ':' + FunctionRef[functionID][2]  + ':' 
	if line:
		output = output + line + ':'
	output = output + text
	print output

def get_name_for_BB(BB):
	name = ''
	first = True
	#for entry in FunctionRef[BBref[BB][0]]:
	for entry in FileRef[BBref[BB][0]]:
		if entry:
			if first:
				name = name + entry
				first = False
			else:
				name = name + '/' + entry
	name = name + ':' + str(BBref[BB][1]) + ' ' + str(BB)
	return name

def add_key_dependency(BB, dBB):
	if dBB in BBread:
		if not BB in BBKeyDependency:
			BBKeyDependency[BB] = []
		if not (dBB, BBread[dBB]) in BBKeyDependency[BB]: 
			BBKeyDependency[BB].append((dBB, BBread[dBB]))

def build_BB_key_dependency():
	for BB in BBDependency:
		for (dBB, edge) in BBDependency[BB]:
			add_key_dependency(BB, dBB)
			if dBB in References:
				for rBB in References[dBB]:
					add_key_dependency(BB, rBB)
	
def get_name_for_func(id):
	return FunctionRef[id][2]

def is_config_key(key):
	if key.find('struct.') == 0 or key.find('class.') == 0 or key.find('union.') == 0:
		if key.split(',')[0][7:] in ConfigKeys:
			return True
		else:
			return False  
	elif NamePattern:
		if NamePattern.match(key):
			return True
		else:
			return False
	elif NameList:
		if key in NameList:
			return True
		else:
			return False
	#elif key:
	#	return True
	else:
		return False

def print_path(output, prefix, paths, level):
	spc = '\t' * level
	print >>output, spc + '\t', prefix, 'call chain:'
	level = 0
	for call in paths:
		print >>output, spc + '\t\t', '[' + str(level) + ']', get_name_for_BB(call), get_name_for_func(BBrefFunc[call])
		level += 1
	print >>output
		
def print_key_read(BB, config_key, level, verbose):
	spc = '\t' * level
	keys = set()
	if BB in BBread:
		keystr = ''
		for key in BBread[BB]:
			if is_config_key(key):
				flag = True
			else:
				flag = False
			if flag:
				if not keystr:
					keystr = '"' + key + '"'
				else:
					keystr += ', ' + '"' + key + '"'
			if (not config_key) or flag:
				keys.add(key)
		if keystr:
			if verbose:
				if flag:
					print >>sys.stderr, spc + '\t*', get_name_for_BB(BB), keystr
				elif Debug:
					print >>sys.stderr, spc + '\t#', get_name_for_BB(BB), keystr
	return keys

def find_dependent_key(BB, config_key, level, verbose):
	spc = '-' * level
	keys = {}
	if BB in BBDependency:
		for (dBB, edge) in BBDependency[BB]:
			for key in print_key_read(dBB, config_key, level, verbose):
				if key not in keys:
					keys[key] = set()
				keys[key].add((dBB, dBB, edge))
			if dBB in References:
				if verbose:
					print >>sys.stderr, spc + '-', get_name_for_BB(dBB)
				for rBB in References[dBB]:
					for key in print_key_read(rBB, config_key, level + 1, verbose):
						if key not in keys:
							keys[key] = set()
						keys[key].add((dBB, rBB, edge))
	return keys

def add_callpath(funcName, path, allpaths, verbose, visited, notConnected):
	allpaths.append(copy.deepcopy(path))
	idx = len(allpaths)
	if verbose:
		print_path(sys.stderr, '##' + str(idx), path, 0)
	print >>sys.stderr, "Path", idx, '-', len(path), 'levels'
	print 'Path', idx, '-', len(path), 'levels'
	return True

def find_callpath_ex(funcName, path, allpaths, verbose, visited, notConnected):
	if PathCount and (len(allpaths) >= PathCount):
		return False
	if funcName in notConnected:
		return False
	if funcName == EntryFunc:
		return add_callpath(funcName, path, allpaths, verbose, visited, notConnected)
	visited.add(funcName)
	print >>sys.stderr, 'find_callpath_ex +', funcName
	if (funcName in RCalls):
		connected = False
		for call in RCalls[funcName]:
			if (not get_name_for_func(BBrefFunc[call]) in visited) and (not call in path):
				path.append(call)
				print >>sys.stderr, 'call +', get_name_for_BB(call)
				if find_callpath_ex(get_name_for_func(BBrefFunc[call]), path, allpaths, verbose, visited, notConnected):
					connected = True
				path.pop(-1)
				print >>sys.stderr, 'call -', get_name_for_BB(call)
		if not connected:
			notConnected.add(funcName)
		if funcName in visited:
			visited.remove(funcName)
		print >>sys.stderr, 'find_callpath_ex -', funcName, connected
		return connected
	else:
		if IgnoreEntryFunc:
			if funcName in visited:
				visited.remove(funcName)
			return add_callpath(funcName, path, allpaths, verbose, visited, notConnected)
		else:
			if verbose:
				print_path(sys.stderr, '', path, 0)
				print >>sys.stderr, len(path), 'levels'
			if funcName in visited:
				visited.remove(funcName)
			print >>sys.stderr, 'find_callpath_ex -', funcName, 0
			return False

def find_callpath(BB, funcName, allpaths, verbose=False): 
	path = []
	if BB:
		path.append(BB)
	visited = set()
	notConnected = set()
	try:
		find_callpath_ex(funcName, path, allpaths, verbose, visited, notConnected)
	except KeyboardInterrupt:
		pass
	if verbose:
		print 'Total', len(allpaths), 'call paths.'
	print >>sys.stderr, 'Total', len(allpaths), 'call paths.'
	idx = 1
	minlength = 1000000 # should be large enough
	maxlength = 0
	totlength = 0
	for path in allpaths:
		totlength += len(path)
		if len(path) < minlength:
			minlength = len(path)
		if len(path) > maxlength:
			maxlength = len(path)
		idx += 1
	if len(allpaths) > 0 and verbose:
		print >>sys.stderr, 'Maximum levels:', maxlength
		print >>sys.stderr, 'Minimum levels:', minlength
		print >>sys.stderr, 'Average levels:', 1.0 * totlength / len(allpaths)


def check_callpath(index, path, dependentpaths, verbose, intersect):
	if verbose:
		print >>sys.stderr, '\nPath #' + str(index)
	level = 0
	for call in path:
		spc = '-' * level
		callee = get_name_for_func(BBrefFunc[call])
		if verbose:
			if call in intersect:
				print >>sys.stderr, spc, level, get_name_for_BB(call), callee
			else:
				print >>sys.stderr, spc, str(level) + '*', get_name_for_BB(call), callee
		keys = find_dependent_key(call, True, level, verbose)
		# Call via function pointer is assumed to be controllable
		if len(keys) == 0:
			if isFP(callee):
				key = callee[1:]
				if is_config_key(key):
					keys[key] = set()
					keys[key].add((call, call, 0))
		# Ignore controls that require setting more than one options
		if len(keys) == 1:
			if not index in dependentpaths:
				dependentpaths[index] = {}
			for key in keys:
				dependentpaths[index][key] = keys[key]
				print >>sys.stderr, spc, 'option:', key
			break
		level += 1

def check_all_callpath(allpaths, dependentpaths, verbose):
	if len(allpaths) == 0:
		return
	sets = []
	for path in allpaths:
		sets.append(set(path))
	intersect = set.intersection(*sets)
	idx = 0
	for path in allpaths:
		check_callpath(idx, path, dependentpaths, True, intersect)
		idx += 1

def check_combined_callpath(allpaths, dependentpaths, verbose):
	sets = []
	for path in allpaths:
		sets.append(set(path))
	intersect = set.intersection(*sets)
	check_callpath(0, intersect, dependentpaths, True)

def get_leftmost_bracket_pos(s):
	level=0
	for i in range(len(s)-1, -1, -1):
		if s[i] == ')':
			level+=1
		elif s[i] == '(':
			level-=1
			if level == 0:
				return i

def is_func_return_void(protoType):
	i = get_leftmost_bracket_pos(protoType)
	if protoType[i - 4 : i] == 'void':
		return True
	else:
		return False

def is_func_return_pointer(protoType):
	# try #1
	#parts = protoType.split('(')
	#ret_type = parts[0]
	#if ret_type[-1] == '*':
	#	return True
	#else:
	#	return False
	# try #2
	#i = protoType.rfind('(')
	#if i > 0:
	#	if protoType[i - 1] == '*':
	#		return True
	#return False
	i = get_leftmost_bracket_pos(protoType)
	if protoType[i - 1] == '*':
		return True
	else:
		return False

def load_lines_file(filename):
	file = open(filename, 'r')
	line_id = 0
	totLines = 0
	files = set()
	for line in file:
		line_id += 1
		if line.find('*Analyzed') >= 0:
			parts = line.split(' ')
			if parts[1].find('@') >= 0:
				line_count = parts[1].split('@')[0]
				start_line = parts[1].split('@')[1]
			else:
				line_count = parts[1]
				start_line = 0
			func_name = parts[4]
			path_name = parts[5].strip()
			dir_name = os.path.dirname(path_name)
			file_name = os.path.basename(path_name)
			proto_type = ''
			for ii in parts[6:]:
				proto_type += ii.strip()
			if not proto_type in ProtoTypes:
				ProtoTypes[proto_type] = set()
			ProtoTypes[proto_type].add(func_name)
			if is_func_return_pointer(proto_type):
				FuncRetPointer.append(func_name)
				#add_error_return(3, func_name, None, 'NULL')
			#FunctionLines[get_function(dir_name, file_name, func_name)] = [int(line_count), int(start_line), 0, path_name]
			#print func_name, 'has', line_count, 'Lines'
			# Pass 2 can modify FunctionLines
			if func_name in FunctionLines:
				returnLine = FunctionLines[func_name][2]
				if FunctionLines[func_name][3]:
					path_name = FunctionLines[func_name][3]
			else:
				returnLine = 0
			print >>sys.stderr, 'FunctionLines', func_name, line_count, start_line, returnLine, path_name, proto_type
			FunctionLines[func_name] = [int(line_count), int(start_line), returnLine, path_name, proto_type, None]
			if func_name in ReachableFuncs:
				totLines += int(line_count)
			#else:
			#	print >>sys.stderr, func_name, 'is analyzed but not reachable.'
			files.add(path_name)
		elif line.find('Analyzed') == 0:
			pass
		else:
			print 'Warning: invalid line', line_id, 'in', filename
	file.close()
	print 'Total', len(files), 'files'
	return totLines

def load_nameList(filename):
	file = open(filename, 'r')
	NameList = []
	for line in file:
		NameList.append(line.strip())
	file.close()
	print 'Load', len(NameList), 'setting names from', filename
	return NameList

def location_to_BB(location):
	parts = location.split(':')
	if len(parts) == 2:
		pathName = parts[0]
		line = parts[1]
		try:
			print 'location_to_BB', os.path.dirname(pathName), os.path.basename(pathName)
			fileID = Files[(os.path.dirname(pathName), os.path.basename(pathName))]
			BB = Lines[(fileID, line)]
		except KeyError as err:
			BB = None
			print 'Unable to find', location
		return BB
	else:
		return None

# impact analysis
def remove_disabled_Calls(BBs, remainingCalls):
	for BB in BBs:
		if BB in Callees:
			print >> sys.stderr, '\t', get_name_for_BB(BB), 'Calls', Callees[BB]
			callee = Callees[BB]
			if callee in remainingCalls:
				if BB in remainingCalls[callee]:
					remainingCalls[callee].remove(BB)

def count_disabled_lines_for_BBs(BBs, length, remainingCalls, disabledCallees):
	disabledLines = length
	print >> sys.stderr, '\tdisabled', disabledLines, 'lines'
	remove_disabled_Calls(BBs, remainingCalls)
	newchange = True
	while newchange:
		newchange = False
		to_delete = []
		for callee in remainingCalls:
			if len(remainingCalls[callee]) == 0:
				# for library Functions such as libc Functions
				if callee in FunctionLines:
					Lines = FunctionLines[callee][0]
				else:
					Lines = 0
				print >> sys.stderr, '\tdisabled', Lines, 'lines from function', callee
				disabledLines += Lines
				if callee in Calls:
					remove_disabled_Calls(Calls[callee], remainingCalls)
				to_delete.append(callee)
				newchange = True
		for callee in to_delete:
			del remainingCalls[callee]
			disabledCallees.append(callee)
	return disabledLines

# CB is a pair of (branch, edge)
def count_disabled_lines_for_CB(branch, edge, remainingCalls, disabledCallees):
	print >> sys.stderr, 'count_disabled_lines_for_CB', get_name_for_BB(branch), 'edge', edge
	disabledLines = count_disabled_lines_for_BBs(ControlBBs[branch][edge], len(ControlBBs[branch][edge]), remainingCalls, disabledCallees)
	print >> sys.stderr, 'disabled', disabledLines, 'Lines'
	return disabledLines

def count_disabled_lines_for_func(func_name, remainingCalls, disabledCallees):
	print >> sys.stderr, 'count_disabled_lines_for_func', func_name
	disabledLines = count_disabled_lines_for_BBs(Calls[func_name], FunctionLines[func_name][0], remainingCalls, disabledCallees)
	disabledCallees.append(func_name)
	print >> sys.stderr, 'disabled', disabledLines, 'Lines'
	return disabledLines

def count_disabled_lines(CPs):
	disabledLines = 0
	remainingCalls = copy.deepcopy(RCalls)
	disabledCallees = []
	for (branch, edge) in CPs:
		if edge == -1:
			disabledLines += count_disabled_lines_for_func(branch, remainingCalls, disabledCallees)
		else:
			disabledLines += count_disabled_lines_for_CB(branch, edge, remainingCalls, disabledCallees)
	print 'Totally disabled', disabledLines, 'Lines', str(disabledLines*1.0/TotLines) + '%'
	print 'Totally disabled', len(disabledCallees), 'Functions', str(len(disabledCallees)*1.0/len(ReachableFuncs)) + '%'

def isFP(func_name):
	if func_name[0] == '*':
		return True
	else:
		return False

def isLoggingFunc(func_name):
	if func_name in LoggingFuncs:
		return True
	for func in LoggingFuncs:
		if len(func_name) > len(func):
			if func_name[:len(func)] == func:
				return True
	return False

def BB2CallerName(BB):
	return get_name_for_func(BBrefFunc[BB])

def BB2CalleeName(BB):
	return Callees[BB]

def getCallers(func_name):
	caller_names = set()
	if func_name in RCalls:
		for call in RCalls[func_name]:
			caller = BB2CallerName(call)
			if isFP(caller):
				caller_names = caller_names.union(getCallers(caller))
			else:
				caller_names.add(caller)
	#print callers
	return caller_names

def getCallees(func_name):			
	callee_names = set()
	if func_name in Calls:
		for call in Calls[func_name]:
			callee = Callees[call]
			if isFP(callee):
				callee_names = callee_names.union(getCallees(callee))
			else:
				callee_names.add(callee)
	#print Callees
	return callee_names

def count_disabled_lines_and_dependency(CPs, func_name):
	if not func_name:
		return
	if len(CPs) == 0:
		CPs.append((func_name, -1))
	count_disabled_lines(CPs)
	allpaths = []
	find_callpath(None, func_name, allpaths)
	caller_names = getCallers(func_name)
	print 'Number of direct callers:', len(caller_names)
	print >>sys.stderr, 'Direct callers of', func_name
	for caller in caller_names:
		print >>sys.stderr, '\t', caller
	module_Calls = 0
	non_module_Calls = 0
	all_caller_names = set()
	for path in allpaths:
		is_module_call = False
		for call in path:
			caller = BB2CallerName(call)
			if not isFP(caller):
				all_caller_names.add(caller)
			else:
				is_module_call = True
		if is_module_call:
			module_Calls += 1
		else:
			non_module_Calls += 1
	print 'Number of all callers:', len(all_caller_names)
	print >>sys.stderr, 'All callers of', func_name
	for caller in all_caller_names:
		print >>sys.stderr, '\t', caller
	callee_names = getCallees(func_name)
	print 'Number of direct Callees:', len(callee_names)
	print >>sys.stderr, 'Direct Callees of', func_name
	for callee in callee_names:
		print >>sys.stderr, '\t', callee
	print 'Non Module Calls:', non_module_Calls
	print 'Module Calls:', module_Calls
	print

def count_disabled_lines_file(filename):
	print >> sys.stderr, 'count_disabled_lines_file', filename
	CPs = []
	func_name = None
	file = open(filename, 'r')
	for line in file:
		line = line.strip()
		if not line:
			continue
		if line[0] == '#':
			continue
		if line[0] == '[':
			count_disabled_lines_and_dependency(CPs, func_name)
			CPs = []
			func_name = None
			vulnerability_name = line[1:-1]
			print 'vulnerability name:', vulnerability_name
		elif line.find('function=') == 0:
			line = line[9:]
			func_name = line
			print 'function name:', func_name
		elif line.find('CP=') == 0:
			line = line[3:]
			parts = line.split(' ')
			Location = parts[0]
			taken_edge = parts[1]
			branch = location_to_BB(Location)
			if branch:
				CPs.append((branch, taken_edge))
				print 'cp:', get_name_for_BB(branch), taken_edge
		elif line.find('FP=') == 0:
			line = line[3:]
			parts = line.split(' ')
			FP = parts[0]
			module = parts[1]
			print 'fp:', FP, module
			callee_name = None
			fp_cp_count = 0
			for caller_name in Calls:
				if caller_name.find(FP) == 0:
					callee_names = set()
					for call in Calls[caller_name]:
						callee_name = Callees[call]
						if callee_name.find(module) >= 0:
							callee_names.add(callee_name)
					for callee_name in callee_names:
							print '\tcp:', callee_name
							CPs.append((callee_name, -1))
							fp_cp_count += 1
			print fp_cp_count, 'CPs for FP'
			if not callee_name:
				print 'Error:', FP, 'has no Callees'
	file.close()
	count_disabled_lines_and_dependency(CPs, func_name)
	#print >> sys.stderr, 'The following Functions are not disabled:'
	#for func in remainingCalls:
	#	if func in FunctionLines:
	#		print >> sys.stderr, '\t', func, FunctionLines[func]

def build_call_graph(func):
	if func in ReachableFuncs:
		return
	#print >> sys.stderr, "reaching function", func
	ReachableFuncs.append(func)
	if func in Calls:
		for call in Calls[func]:
			ReachableCalls.add(call)
			build_call_graph(Callees[call])

def remove_unreachable_calls_ex(calls, get_funcname_for_call):
	toDeleteFunc = set()
	for func in calls:
		if not func in ReachableFuncs:
			toDeleteFunc.add(func)
		else:
			toDeleteCall = set()
			for call in calls[func]:
				if not get_funcname_for_call(call) in ReachableFuncs:
					toDeleteCall.add(call)
			for call in toDeleteCall:
				calls[func].remove(call)
			if len(calls[func]) == 0:
				toDeleteFunc.add(func)
	for func in toDeleteFunc:
		del calls[func]

def remove_unreachable_calls():
	remove_unreachable_calls_ex(Calls, BB2CalleeName)
	remove_unreachable_calls_ex(RCalls, BB2CallerName)

def print_totals():
	#if TotLines > 0:
	#	count_dependent = len(BBKeyDependency)
	#	print '1. Source code Lines analyzed:', TotLines
	#	print '2. Control dependent Lines:', count_dependent
	#	print '3. Config dependent Lines:', countConfigDependentLines
	#	print '4. Control dependency ratio (2/1)', 1.0* count_dependent/TotLines
	#	print '5. Config dependency ratio1 (3/1):', 1.0 * countConfigDependentLines/TotLines
	#	print '6. Config dependency ratio2 (3/2):', 1.0 * countConfigDependentLines/len(BBKeyDependency)
	#else:
	#	print linesFilename, 'does not exist'

	count_ConfigKeys = 0
	file = open(InputFile + '.Keys', 'w')
	for key in AllKeys:
		if is_config_key(key):
			print >> file, '*', key
			count_ConfigKeys += 1
		else:
			print >> file, ' ', key
	file.close()
	print '7. Config keys:', count_ConfigKeys
	print '8. Config control keys:', len(countControlKeys)
	print

	#print len(Functions), "Functions:"
	#for function in Functions:
	#	print function, Functions[function]
	file = open(InputFile + '.BBread', 'w')
	print >> file, "BBread:"
	for BB in BBread:
		print >> file, get_name_for_BB(BB)
		for key in BBread[BB]:
			print >> file, '\t', key
	file.close()

	file = open(InputFile + '.BBDependency', 'w')
	print >> file, "BBDependency:"
	for BB in BBDependency:
		print >> file, get_name_for_BB(BB)
		for dBB in BBDependency[BB]:
			print >> file, '\t', get_name_for_BB(dBB)
	file.close()
	
	file = open(InputFile + '.Calls', 'w')
	print >> file, "RCalls:"
	for func in RCalls:
		print >> file, func
		for call in RCalls[func]:
			print >> file, '\t', call, get_name_for_BB(call)
	file.close()
	
	print
	print 'Control_BBs:'
	for dominateBB in ControlBBs:
		print get_name_for_BB(dominateBB)
		for edge in ControlBBs[dominateBB]:
			print '\tedge:', edge
			for BB in ControlBBs[dominateBB][edge]:
				print '\t\t', get_name_for_BB(BB)

def group_dependency(path, group, visited):
	group.append(path)
	if path[0] in BBDependency:
		for p in BBDependency[path[0]]:
			if not p in visited:
				visited.add(p)
				group_dependency(p, group, visited)

def convert_dependency_to_cnf(dependency):
	groups = []
	visited = set()
	if len(dependency) > 0:
		dependency = sorted(dependency, key=lambda x: int(BBref[x[0]][1]), reverse=True)
		for (BB, edge) in dependency:
			if not (BB, edge) in visited:
				visited.add((BB, edge))
				group = []
				group_dependency((BB, edge), group, visited)
				groups.append(group)
	return groups

def contradict_dependency_group(BB, edge, group):
	for (BB1, edge1) in group:
		if BB == BB1 and edge != edge1:
			return True
	return False
		
def contradict_dependency_groups(depGroups1, depGroups2):
	success = False
	minGroupSize = 1000000
	minDepGroup = None
	for dep in depGroups1:
		groups = copy.deepcopy(depGroups2)
		for (BB, edge) in dep:
			toDelete = []
			for group in groups:
				if contradict_dependency_group(BB, edge, group):
					toDelete.append(group)
			for group in toDelete:
				groups.remove(group)
			if len(groups) == 0:
				break
		if len(groups) == 0:
			success = True
			if len(dep) < minGroupSize:
				minGroupSize = len(dep)
				minDepGroup = dep
	return success, dep, minGroupSize

def find_diversion_for_BB(BB):
	minDepGroup = None
	if BB in BBDependency:
		funcID = BBrefFunc[BB]
		minCountDependency = 1000000
		stmtWithMinCountDependency = None
		depGroups = convert_dependency_to_cnf(BBDependency[BB])
		if funcID in FuncControlBBs:
			for (branch, edge) in FuncControlBBs[funcID].difference(BBDependency[BB]):
				for stmt in ControlBBs[branch][edge]:
					if stmt in Callees:
						if isLoggingFunc(Callees[stmt]):
							stmtGroups = convert_dependency_to_cnf(BBDependency[stmt])
							#print 'Checking ', get_name_for_BB(stmt)
							#print_dependency_groups(stmt)
							(success, dep, size) = contradict_dependency_groups(stmtGroups, depGroups) 
							if success and (size < minCountDependency):
								minCountDependency = size
								minDepGroup = dep
								stmtWithMinCountDependency = stmt
		#if stmtWithMinCountDependency:
			#print get_name_for_BB(stmtWithMinCountDependency)
			#for (branch, edge) in minDepGroup:
			#	print '\t', get_name_for_BB(branch), edge
	#if not minDepGroup:
	#	print >> sys.stderr, 'There is no diversion for', get_name_for_BB(BB)
	return minDepGroup

def find_error_return_for_func(func):
	print >> sys.stderr, 'find_error_return_for_func', func
	# ignore workaround that would cause app to exit
	if func == EntryFunc:
		return None
	#if func in ErrorReturns:
	#	print >>sys.stderr, '\t', func, 'has an error return', ErrorReturns[func]
	#	return get_error_return(func)
	earliestReturn = None
	if func in Calls:
		earliestLine = 1000000
		for call in Calls[func]:
			print >> sys.stderr, '\t', get_name_for_BB(call), Callees[call], isLoggingFunc(Callees[call]), call in BBFollowByReturn
			if (isLoggingFunc(Callees[call])) and (call in BBFollowByReturn):
				BB = BBFollowByReturn[call][0]
				line = BBref[BB][1]
				ret_value = BBFollowByReturn[call][1]
				if line > 0 and line < earliestLine:
					earliestLine = line
					earliestReturn = call
					FunctionLines[func][2] = -earliestLine
				add_error_return(1, func, BB, ret_value)
	else:
		print >>sys.stderr, '\t', func, 'has no callees'
	if earliestReturn:
		print >>sys.stderr, '\t', func, 'has an error return', get_name_for_BB(earliestReturn)
	else:
		print >>sys.stderr, '\t', func, 'has no error return'
	return earliestReturn

def find_error_return_for_func_old(func):
	print >> sys.stderr, 'find_error_return_for_func', func
	earliestReturn = None
	if func in Calls:
		for call in Calls[func]:
			funcID = BBrefFunc[call]
			break
		earliestLine = 1000000
		if funcID in FuncControlBBs:
			for (branch, edge) in FuncControlBBs[funcID]:
				print get_name_for_BB(branch), edge, ':'
				for stmt in ControlBBs[branch][edge]:
					print '\t', stmt, get_name_for_BB(stmt), stmt in Callees, stmt in BBFollowByReturn
					if stmt in Callees:
						line = int(BBref[stmt][1])
						print >> sys.stderr, '\t', 'checking call to', Callees[stmt], 'at line', line
						isErrorReturn = False
						if (isLoggingFunc(Callees[stmt])):
							if (stmt in BBFollowByReturn):
								print '\t', BBref[stmt]
								isErrorReturn = True
								line = BBFollowByReturn[stmt][0]
								
								print >> sys.stderr, '\t', 'followed by return at', line
							else:
								print >> sys.stderr, '\t', 'line', line, 'is not followed by return'
						if isErrorReturn:
							if line > 0 and line < earliestLine:
								earliestLine = line
								earliestReturn = stmt
								FunctionLines[func][2] = earliestLine
		else:
			print func, 'has no conditional branches'
	else:
		print func, 'has no callees'
	return earliestReturn

def get_dep_group_for_BB(BB):
	minDepGroup = None
	if BB in BBDependency:
		minCountDependency = 1000000
		depGroups = convert_dependency_to_cnf(BBDependency[BB])
		for group in depGroups:
			if len(group) < minCountDependency:
				minCountDependency = len(group)
				minDepGroup = group
	return minDepGroup
	
def get_error_return_for_BB(BB):
	return find_diversion_for_BB(BB)	

def get_locations_to_add_sec_setting2(func, funcsToDisable, visited, level):
	spc = '\t' * level
	if InteractiveMode:
		print >> sys.stderr, spc, level, "get_locations_to_add_sec_setting2", func, len(funcsToDisable)
	#if FunctionLines[func][2]:
	if func in ErrorReturns:
		funcsToDisable.add(func)
		#if InteractiveMode:
		print >> sys.stderr, spc, level, func, len(funcsToDisable), 'can be protected directly'
		return True
	#if func in FunctionSimplePath:
	#	funcsToDisable.add(func)
	#	if InteractiveMode:
	#		print >> sys.stderr, spc, level, func, len(funcsToDisable), 'can be protected directly'
	#	return True
	callers = getCallers(func)
	if not len(callers):
		if InteractiveMode:
			print >> sys.stderr, spc, level, func, 'cannot be protected'
		return False
	callerProtected = False
	for caller in callers:
		if not caller in visited:
			visited.add(caller)
			if not get_locations_to_add_sec_setting2(caller, funcsToDisable, visited, level + 1):
				if InteractiveMode:
					print >> sys.stderr, spc, level, func, len(funcsToDisable), 'cannot be protected'
				return False
			else:
				callerProtected = True
		elif InteractiveMode:
			print >> sys.stderr, spc, level, caller, "already visited"
	if InteractiveMode:
		if callerProtected:
			print >> sys.stderr, spc, level, func, len(funcsToDisable), 'can be protected'
		else:
			print >> sys.stderr, spc, level, func, len(funcsToDisable), 'cannot be protected'
	return callerProtected

# main entry to get_locations_to_add_sec_settings
def get_locations_to_add_sec_setting3(func, funcsToDisable):
	print >> sys.stderr, "get_locations_to_add_sec_setting3", func
	visited = set()
	if not func in FunctionLines:
		print func, 'is not analyzed'
		return
	if FunctionLines[func][5] == None:
		FunctionLines[func][5] = is_func_defined_by_macro(FunctionLines[func][3], func, FunctionLines[func][1])
	if FunctionLines[func][5]:
		print >>sys.stderr, func, 'is defined by macros'
		return
	if not get_locations_to_add_sec_setting2(func, funcsToDisable, visited, 0):
		funcsToDisable.clear()

def is_func_defined_by_macro(path, func, startLine):
	# restore original function name for static functions
	func = get_orig_func_name(func)
	print >>sys.stderr, 'Checking', func, 'at line', startLine, 'in', path
	inf = open(path, 'r')
	lines = inf.readlines()
	inf.close()
	startLine = get_func_decl_line(path, func, startLine, lines)
	if startLine:
		line = lines[startLine - 1]
		print >>sys.stderr, '----', line
		pos = line.find(func)
		print >>sys.stderr, 'pos:', pos
		if pos < 0:
			return True
		elif pos == 0:
			return False
		elif line[pos - 1] == '(':
			return True
		else:
			return False
	else:
		return True

def get_locations_to_add_sec_setting(func):
	print 'Checking', func
	BB = find_error_return_for_func(func)
	if BB:
		locations = get_dep_group_for_BB(BB)
		#print locations
		if len(locations) > 0:
			return locations
	locations = set()
	if func in RCalls:
		allCalls = copy.deepcopy(RCalls[func])
		processedCalls = set()
		while True:
			print 'allCalls has', len(allCalls), 'calls'
			if len(allCalls) == 0:
				break
			toDelete = set()
			toAdd = set()
			for call in allCalls:
				processedCalls.add(call)
				locationsForBB = get_error_return_for_BB(call)
				if locationsForBB:
					locations = locations.union(locationsForBB)
					toDelete.add(call)
				else:
					toDelete.add(call)
					caller = get_name_for_func(BBrefFunc[call])
					if caller in RCalls:
						toAdd = toAdd.union(RCalls[caller])
					locationToDelete = set()
					for location in locations:
						if BBrefFunc[location[0]] == BBrefFunc[call]:
							locationToDelete.add(location)
					for location in locationToDelete:
						locations.remove(location)
			for call in toDelete:
				allCalls.remove(call)
			for call in toAdd:
				if not call in processedCalls:
					allCalls.add(call)
	else:
		print func, 'has no callers!'
	return locations

def print_dependency_groups(BB):
	idx = 0
	for group in convert_dependency_to_cnf(BBDependency[BB]):
		print 'group', idx
		for path in group:
			print '\t', get_name_for_BB(path[0]), path[1]
		idx += 1

def print_branches(branches):
	for dBB in sorted(branches.keys(), cmp=lambda x, y: get_name_for_BB(x) < get_name_for_BB(y)):
		print '\t', get_name_for_BB(dBB)
		for edge in branches[dBB]:
			print '\t\t', edge

def get_dependency_branches_for_BB(BB):
	branches = {}
	for (dBB, edge) in BBDependency[BB]:
		if not dBB in branches:
			branches[dBB] = set()
		branches[dBB].add(edge)
	return branches

def menu():
	print '1. Find call paths to a function.'
	print '2. Find call paths to a line.'
	print '3. Find callee of a function.'
	print '4. Find caller of a function.'
	print '5. Find dependency of a line.'
	print '6. Find support of a line.'
	print '7. Find diversion of a line.'
	print '8. Add security setting for a function.'
	print '9. Find error return for a function.'
	print '10. Add security setting for all functions.'
	print '11. Find workaround for a function.'
	print '0. Exit.'
	return raw_input('Enter a choice: ')

def interact():
	while True:
		ans = menu();
		if ans == '0':
			break
		elif ans == '1':
			func_name = raw_input('Enter function name: ')
			#findpaths(func_name)
			allpaths = []
			find_callpath(None, func_name, allpaths, True)
		elif ans == '2':
			Location = raw_input('Enter a Location: ')
			#findpaths(func_name)
			allpaths = []
			BB = location_to_BB(Location)
			func_name = get_name_for_func(BBrefFunc[BB])
			print 'Function:', func_name
			find_callpath(BB, func_name, allpaths, True)
		elif ans == '3':
			func_name = raw_input('Enter function name: ')
			if func_name in Calls:
				print >>sys.stderr, 'Callees of', func_name
				for call in Calls[func_name]:
					print >>sys.stderr, call, get_name_for_BB(call), Callees[call]
				print 'Total', len(Calls[func_name]), 'calls.'
			else:
				print func_name, 'does not have any callee.'
		elif ans == '4':
			func_name = raw_input('Enter function name: ')
			if func_name in RCalls:
				callers = set()
				callers2 = set()
				print >>sys.stderr, 'Callers of', func_name
				for call in RCalls[func_name]:
					caller = get_name_for_func(BBrefFunc[call])
					callers.add(caller)
					if call in BBFollowByReturn:
						callers2.add(caller)
						flag = '*'
					else:
						flag = '!'
					print >>sys.stderr, get_name_for_BB(call), caller, flag
				print 'Total', len(RCalls[func_name]), 'calls.'
				print 'Total', len(callers), 'callers.'
				print 'Total', len(callers2), 'callers with calls followed by return.'
			else:
				print func_name, 'does not have any caller.'
		elif ans == '5':
			location = raw_input('Enter a location: ')
			BB = location_to_BB(location)
			if BB:
				if BB in BBDependency:
					print 'This location is satisfied by the following predicates'
					#branches = get_dependency_branches_for_BB(BB)
					#print_branches(branches)
					print_dependency_groups(BB)
				else:
					print 'This location has no dependency.'
			else:
				print 'Invalid location.'
		elif ans == '6':
			location = raw_input('Enter a location: ')
			BB = location_to_BB(location)
			if BB:
				if BB in ControlBBs:
					print 'This location has the following supports.'
					for edge in ControlBBs[BB]:
						print 'Edge:', edge
						for sBB in ControlBBs[BB][edge]:
							print '\t', get_name_for_BB(sBB)
				else:
					print 'This location has no support.'
			else:
				print 'Invalid location.'
		elif ans == '7':
			location = raw_input('Enter a location: ')
			BB = location_to_BB(location)
			if BB:
				find_diversion_for_BB(BB)
			else:
				print 'Invalid location.'
		elif ans == '8':
			funcName = raw_input('Enter a function name: ')
			#for (branch, edge) in get_locations_to_add_sec_setting(funcName):
			#	print '*', get_name_for_BB(branch), edge
			funcsToDisable = set()
			get_locations_to_add_sec_setting3(funcName, funcsToDisable)
			for func in funcsToDisable:
				print func, FunctionLines[func][1:] 
		elif ans == '9':
			funcName = raw_input('Enter a function name: ')
			if funcName in FunctionLines:
				BB = find_error_return_for_func(funcName)
				if BB:
					print get_name_for_BB(BB)
				else:
					print 'No error return for', funcName
			else:
				print funcName, 'is not analyzed'
		elif ans == '10':
			start_time = time.time()
			print >> sys.stderr, 'Running 10@', start_time
			countProtectableFuncs = 0
			protectableFuncs = set()
			totLocations = 0
			minLocations = 1000000
			maxLocations = 0
			countProtectableLines = 0
			for funcName in ReachableFuncs:
				if funcName in FunctionLines: 
					if not isLoggingFunc(funcName):
						print >> sys.stderr, 'Checking', funcName
						locations = get_locations_to_add_sec_setting(funcName)
						if len(locations) > 0:
							countProtectableFuncs += 1
							protectableFuncs.add(funcName)
							print >> sys.stderr, '*', funcName, len(locations)
							for (branch, edge) in locations:
								print >> sys.stderr, '\t', get_name_for_BB(branch), edge
							countLocations = len(locations)
							if countLocations < minLocations:
								minLocations = countLocations
							if countLocations > maxLocations:
								maxLocations = countLocations
							totLocations += countLocations
							countProtectableLines += FunctionLines[funcName][0]
						else:
							print >> sys.stderr, '!', funcName
					else:
						print >> sys.stderr, 'Skipping logging function', funcName
				else:
					print >> sys.stderr, 'Skipping external function', funcName
			print 'Total', countProtectableFuncs, 'of', TotFuncs, 'reachable functions can be protected.'
			print 'Total', countProtectableLines, 'of', TotLines, 'lines can be protected.'
			if countProtectableFuncs:
				print 'Min #locations for protection:', minLocations
				print 'Max #locations for protection:', maxLocations
				print 'Avg #locations for protection:', totLocations / countProtectableFuncs
			end_time = time.time()
			print >> sys.stderr, 'Finish 10@', end_time, 'total', end_time - start_time, 'seconds'
		elif ans == '11':
			func_name = raw_input('Enter function name: ')
			find_workaround(func_name, True)
		else:
			print 'Invalid choice.'
	exit()

def find_workaround(location, verbose):
	find_workaround_ex(location, verbose, "find_workaround", check_combined_callpath)

def find_constraints(location, verbose):
	find_workaround_ex(location, verbose, "find_constraints", check_all_callpath)

def find_workaround_ex(location, verbose, title, check_func):
	print >>sys.stderr, 'find_workaround', location
	ret = False
	allpaths = []
	dependentpaths = {}
	if location.find(':') != -1:
		pathName = location.split(':')[0]
		line = location.split(':')[1]
		try:
			fileID = Files[(os.path.dirname(pathName), os.path.basename(pathName))]
			BB = Lines[(fileID, line)]
			functionName = get_name_for_func(BBrefFunc[BB])
			print >>sys.stderr, pathName, '=>', fileID, BB
			print >>sys.stderr, 'Control dependency of', get_name_for_BB(BB), functionName
			paths = []
			find_callpath(BB, functionName, allpaths, verbose)
			print
		except KeyError as err:
			print 'Unable to find', location
			print 'Try to rerun dependency.py with function name'
			exit()
	else:
		functionName = location
		print >>sys.stderr, 'Control dependency of', functionName
		if functionName in FunctionLocation:
			find_callpath(None, functionName, allpaths, verbose)
		else:
			print >>sys.stderr, 'Function', functionName, 'is undefined'
			return ret

	if verbose:
		print >>sys.stderr
		if PathCount:
			print >>sys.stderr, 'Total', len(allpaths), 'paths - limited to', PathCount
		else:
			print >>sys.stderr, 'Total', len(allpaths), 'paths'

	check_func(allpaths, dependentpaths, verbose)
	if verbose:
		print >>sys.stderr
	CPs = {}
	workaround_keys = {}
	if verbose:
		print >>sys.stderr, 'Dependent paths:'
	multiKeyPath = []
	for path in dependentpaths:
		if len(dependentpaths[path]) > 1:
			multiKeyPath.append(path)
	for path in multiKeyPath:
		del dependentpaths[path]
	for path in dependentpaths:
		if verbose:
			print >>sys.stderr, 'Path', path
		for key in dependentpaths[path]:
			if verbose:
				print >>sys.stderr, key
			for (branch, reference, edge) in dependentpaths[path][key]:
				if not key in workaround_keys:
					workaround_keys[key] = set()
				workaround_keys[key].add(branch)
				if not key in CPs:
					CPs[key] = set()
				#if edge == '0':
				#	CPs[key].add((branch, '1'))
				#for edge2 in ControlBBs[branch]:
				#	if edge2 != edge:
				#		CPs[key].add((branch, edge2))
				CPs[key].add((branch, edge))
			if verbose:
				if branch == reference:
					print >>sys.stderr, edge, get_name_for_BB(branch)
				else:
					print >>sys.stderr, edge, get_name_for_BB(branch), '->', get_name_for_BB(reference)
	print >>sys.stderr, 'Total', len(dependentpaths), 'dependent paths'
	#if len(dependentpaths) == len(allpaths):
	#	print >>sys.stderr, 'All', len(allpaths), 'paths are dependent.'
	#	ret = True
	# we need just one dependentpath since we use check_combined_callpath
	if len(dependentpaths):
		print >>sys.stderr, 'All', len(allpaths), 'paths are dependent.'
		ret = True
	if ret:
		print >>sys.stderr
		print >>sys.stderr, 'Control Points:'
		for key in workaround_keys:
			BBs = AllKeys[key]
			for BB in workaround_keys[key].intersection(AllKeys[key]):
				if BB in ControlBBs:
					print >>sys.stderr, key, ': ', get_name_for_BB(BB)
		for key in CPs:
			for (branch, edge) in CPs[key]:
				print >>sys.stderr, key, get_name_for_BB(branch), edge
			#count_disabled_lines(CPs[key])
	print >>sys.stderr
	return ret

def find_workaround_all(verbose):
	count_func_has_workaround = 0
	funcHasWorkaround = []
	for func in FunctionLines:
		if func in ReachableFuncs:
			if find_workaround(func, verbose):
				count_func_has_workaround += 1
				funcHasWorkaround.append(func)
	print count_func_has_workaround, 'functions has existing workaround'
	return funcHasWorkaround

def find_error_return_for_func_all():
	funcs = []
	for func in FunctionLines:
		if func in ReachableFuncs:
			if find_error_return_for_func(func):
				funcs.append(func)
	print len(funcs), 'functions has error return'
	return funcs

# propagate error handling code upwards the call chain, i.e. from callee to caller
def direct_error_propagation():
	newchange = True
	working_set = set(ErrorReturns)
	count_direct_error_propagation = 0
	while newchange:
		newchange = False
		new_set = []
		# for each function that has an error return
		for func in working_set:
			kind, errorRet = get_error_return(func)
			# we don't propagate the use of error handling functions
			if kind == 0:
				continue
			if func in RetCalls:
				for (caller, call) in RetCalls[func]:
					if caller in ReachableFuncs:
						if not caller in ErrorReturns:
							copy_error_return(func, caller)
							FunctionLines[caller][2] = -int(BBref[call][1])
							newchange = True
							new_set.append(caller)
							count_direct_error_propagation += 1
							print >>sys.stderr, caller, 'has propagated error return from', get_name_for_BB(call)
		working_set = new_set
	print count_direct_error_propagation, 'functions has directly propagated error return'
	return count_direct_error_propagation

def indirect_error_propagation():
	print >>sys.stderr, 'indirect_error_propagation'
	count_indirect_error_propagation = 0
	#print >>sys.stderr, ConstReturns
	#prt_cond_checks()
	print >>sys.stderr, 'ConstReturns:'
	for func in ConstReturns:
		if not func in FunctionLines:
			continue
		if not func in ReachableFuncs:
			continue
		print >>sys.stderr, '\t', func
		for (BB, ret_val) in ConstReturns[func]:
			print >>sys.stderr, '\t\t', get_name_for_BB(BB), ret_val
			done = False
			if BB in BBDependency:
				# use only the most related dependency
				dBB, edge = BBDependency[BB][-1]
				print >>sys.stderr, '\t\t\t', get_name_for_BB(dBB), edge, dBB
				if (dBB, edge) in CondChecks:
					for (pred, funcName, rhs) in CondChecks[(dBB, edge)]:
						print >>sys.stderr, '\t\t\t\t', pred, funcName, rhs			
						if funcName in ErrorReturns:
							if is_ret_value_satisfy_pred(funcName, pred, rhs):
								if not func in ErrorReturns:
									print >>sys.stderr, '\t\t\t\t', 'adding', ret_val, 'as error return value for', func
									add_error_return(11, func, BB, ret_val)
									count_indirect_error_propagation += 1
									done = True
									break
				if done:
					break
	print count_indirect_error_propagation, 'functions has indirectly propagated error return'
	return count_indirect_error_propagation

def reverse_error_propagation():
	print >>sys.stderr, 'reverse_error_propagation'
	countReverseErrorPropagation = 0
	#print >>sys.stderr, ConstReturns
	#prt_cond_checks()
	print >>sys.stderr, 'ErrorReturns:'
	new_errors = []
	for func in ErrorReturns:
		if not func in FunctionLines:
			continue
		if not func in ReachableFuncs:
			continue
		print >>sys.stderr, '\t', func
		for kind in ErrorReturns[func]:
			for (BB, ret_val) in ErrorReturns[func][kind]:
				if BB:
					print >>sys.stderr, '\t\t', get_name_for_BB(BB), ret_val
					if BB in BBDependency:
						# use only the most related dependency
						dBB, edge = BBDependency[BB][-1]
						print >>sys.stderr, '\t\t\t', get_name_for_BB(dBB), edge, dBB
						if (dBB, edge) in CondChecks:
							for (pred, funcName, rhs) in CondChecks[(dBB, edge)]:
								print >>sys.stderr, '\t\t\t\t', pred, funcName, rhs			
								ret_val = get_ret_value_to_satisfy_pred(pred, rhs)
								if ret_val:
									print >>sys.stderr, '\t\t\t\t', 'adding', ret_val, 'as error return value for', funcName
									new_errors.append((kind, funcName, None, ret_val))
	for kind, funcName, BB, ret_val in new_errors:
		if not funcName in ErrorReturns:
			countReverseErrorPropagation += 1
		add_error_return(4, funcName, None, ret_val)

	print countReverseErrorPropagation, 'functions has been reversely propagated error return'
	return countReverseErrorPropagation

def apply_file_change(filename, newfilename, logfilename):
	backupfilename = filename + '.orig'
	if not os.path.exists(backupfilename):
		os.rename(filename, backupfilename)
	os.rename(newfilename, filename)
	log = open(logfilename, 'a')
	print >> log, backupfilename, filename
	log.close()

def get_label(func):
	return 'label_error_return_for_protection'

def get_setting_name_ex(protected):
	name = "FPSW_" + protected.replace('/', '_').replace('-', '_').replace('.', '_')
	return name

def get_setting_name(protected):
	name = get_setting_name_ex(protected)
	if not name in ProtectedName:
		ProtectedName[name] = 0
	else:
		ProtectedName[name] += 1
	return name

def get_setting_number(protected, name):
	FPSW = get_setting_name(protected)
	if not FPSW in ProtectedFuncNumber:
		ProtectedFuncNumber[FPSW] = len(ProtectedFuncNumber)
		ProtectedFuncRef[ProtectedFuncNumber[FPSW]] = name
	return ProtectedFuncNumber[FPSW]

def get_exec_flag_number(func):
	if not func in ExecFuncNumber:
		ExecFuncNumber[func] = len(ExecFuncNumber)
	return ExecFuncNumber[func]

def get_loader_data(name, funcMapping, entry, entryFunc):
	data = 'char *' + name + '[] = {\n'
	funcs = sorted(funcMapping, key=funcMapping.get)
	for func in funcs:
		data += '"' + func + '",\n'
	data += '};\n'
	data += 'char *' + entry + ' = ' + '"' + entryFunc + '";\n'
	return data

def get_loader_code(filename):
	input = open(filename, 'r')
	code = input.readlines()
	input.close()
	return code	

def add_loader_code_to_entry(entryFunc, loaderFile, logfilename):
	filename = FunctionLines[entryFunc][3]
	outfilename = filename + '.protected'
	input = open(filename, 'r')
	output = open(outfilename, 'w')
	print >> output, 'int FPSW_flags[' + str(len(ProtectedFuncNumber)) + '];\n'
	print >> output, get_loader_data('FPSW_flags_names', ProtectedFuncNumber, 'FPSW_entry', entryFunc)
	code = get_loader_code(loaderFile)
	for line in code:
		print >> output, line.strip('\n')
	for line in input:
		line = line.strip('\n')
		print >> output, line
	output.close()
	input.close()
	apply_file_change(filename, outfilename, logfilename)

def add_loader_code(loaderFile, logfilename):
	for funcName in FunctionLines:
		if (funcName.find('main_') == 0) or (funcName == EntryFunc):
			print >>sys.stderr, 'Adding loader to', funcName
			add_loader_code_to_entry(funcName, loaderFile, logfilename)

def add_exec_loader_code_to_entry(entryFunc, loaderFile, logfilename):
	filename = FunctionLines[entryFunc][3]
	outfilename = filename + '.protected'
	input = open(filename, 'r')
	output = open(outfilename, 'w')
	print >> output, 'int EXEC_flags[' + str(len(ExecFuncNumber)) + '];\n'
	print >> output, get_loader_data('EXEC_flags_names', ExecFuncNumber, 'EXEC_entry', entryFunc)
	code = get_loader_code(loaderFile)
	for line in code:
		print >> output, line.strip('\n')
	for line in input:
		line = line.strip('\n')
		print >> output, line
	output.close()
	input.close()
	apply_file_change(filename, outfilename, logfilename)

def add_exec_loader_code(loaderFile, logfilename):
	for funcName in FunctionLines:
		if (funcName.find('main_') == 0) or (funcName == EntryFunc):
			print >>sys.stderr, 'Adding exec loader to', funcName
			add_exec_loader_code_to_entry(funcName, loaderFile, logfilename)

def get_CP_code(func, protected):
	name = protected.replace('/', '_').replace('-', '_').replace('.', '_')
	return "\tif (FPSW_flags[" + str(get_setting_number(protected, name)) + '])\n' + '\t\tgoto ' + get_label(func) + ';\n'

def get_CP_combined_code(func, list_protected):
	cond = ""
	for protected in list_protected:
		name = protected.replace('/', '_').replace('-', '_').replace('.', '_')
		if cond:
			cond += ' || FPSW_flags[' + str(get_setting_number(name, protected)) + '])'
		else:
			cond = 'FPSW_flags[' + str(get_setting_number(name, protected)) + '])'
	return '\tif (' + cond + ')\n' + '\t\tgoto ' + get_label(func) + ';\n'

def get_CP_combined_code_ret(func, list_protected):
	cond = ""
	for protected in list_protected:
		name = protected.replace('/', '_').replace('-', '_').replace('.', '_')
		if cond:
			cond += ' || FPSW_flags[' + str(get_setting_number(name, protected)) + ']'
		else:
			cond = 'FPSW_flags[' + str(get_setting_number(name, protected)) + ']'
	(kind, ret) = get_error_return_value(func)
	ifstmt = 'if (' + cond + ') {\n' + '\tFPSW_log("' + func + '"); //' + str(kind) + '\n'
	if kind == 0:
		ifstmt += '\t' + ret + ErrorFuncs[ret][3] + ';\n'
		if is_func_return_void(FunctionLines[func][4]):
			return ifstmt + '\treturn ;\n' + '}\n'
		elif is_func_return_pointer(FunctionLines[func][4]):
			return ifstmt + '\treturn NULL;\n' + '}\n'
		else:
			return ifstmt + '\treturn -1;\n' + '}\n'
	else:
		if ret != "None":
			return ifstmt + '\treturn ' + str(ret) + ';\n' + '}\n'
		else:
			return ifstmt + '\treturn;\n' + '}\n'

# convert internal function name back
def get_orig_func_name(func):
	pos = func.find('/')
	if pos >= 0:
		return func[:pos - 1]
	else:
		return func

def is_func_def(curLine, lines):
	stmt = lines[curLine - 1]
	not_contains = [';', 'if ', 'switch ', 'while ', 'do ', 'for ']
	contains = ['(']
	for keyword in not_contains:
		if stmt.find(keyword) > 0:
			return False
	for keyword in contains:
		if stmt.find(keyword) < 0:
			return False
	return True

def get_func_decl_line(filename, func, startLine, lines):
	print >>sys.stderr, 'get_func_decl_line', filename, func, startLine
	if startLine >= len(lines):
		print >>sys.stderr, '\tInvalid start_line, file has', len(lines), 'lines'
		#raise IOError
		return
	print >>sys.stderr, '\t', lines[startLine - 1]
	# only do this if the startLine does not contain the function name
	if lines[startLine - 1].find(get_orig_func_name(func)) < 0:
		# ensure we are at the beginning of a function
		curLine = startLine
		while curLine > 0:
			print >>sys.stderr, 'line- ', curLine, lines[curLine - 1]
			if is_func_def(curLine, lines):
				if lines[curLine - 1].find(get_orig_func_name(func)) < 0:
					print >>sys.stderr, '\tIn wrong location?'
					print >>sys.stderr, '\t\t', lines[curLine - 1]
					return 0;
				else:
					break
			curLine -= 1
		startLine = curLine
	return startLine

def get_func_start_line(filename, func, startLine, lines):
	print >>sys.stderr, 'get_func_start_line', filename, func, startLine
	if startLine >= len(lines):
		print >>sys.stderr, '\tInvalid start_line, file has', len(lines), 'lines'
		#raise IOError
		return
	print >>sys.stderr, '\t', lines[startLine - 1]
	# only do this if the startLine does not contain the function name
	if lines[startLine - 1].find(get_orig_func_name(func)) < 0:
		# ensure we are at the beginning of a function
		curLine = startLine
		while curLine > 0:
			print >>sys.stderr, 'line- ', curLine, lines[curLine - 1]
			if is_func_def(curLine, lines):
				if lines[curLine - 1].find(get_orig_func_name(func)) < 0:
					print >>sys.stderr, '\tIn wrong location?'
					print >>sys.stderr, '\t\t', lines[curLine - 1]
					return 0;
				else:
					break
			curLine -= 1
		startLine = curLine

	origStartLine = startLine
	while startLine < len(lines):
		line = lines[startLine - 1].strip()
		print >>sys.stderr, 'line+ ', startLine, line
		if line and line[-1] == '{':
			print >>sys.stderr, func, startLine
			return startLine + 1
		elif line and line[-1] == ';':
			return startLine
		startLine += 1
	print >>sys.stderr, 'Unable to find start line for', func, '@', origStartLine
	return origStartLine
		
def get_call_checks(lines, line1, line2):
	check = "// FPSW: patched call checks\n"
	for line in range(line1, line2 + 1):
		check += lines[line - 1]
	return check.strip()

def get_file_lines(filename):
	try:
		input = open(filename, 'r')
		lines = input.readlines()
		input.close()
		return lines
	except TypeError:
		print 'File', filename, 'cannot be openned!' 
		return []
	except IOError:
		print 'File', filename, 'cannot be openned!' 
		return []

def get_exec_log_code(func):
	stmt = 'EXEC_flags[' + str(get_exec_flag_number(func)) + '] = 1;'
	# use direct logging to avoid loss of cached logging
	stmt = 'EXEC_log("' + func + '");'
	return stmt;

def insert_code(filename, locations, logfilename):
	backupfilename = filename + '.orig'
	outfilename = filename + '.protected'

	if os.path.exists(backupfilename):
		print "File", backupfilename, "already exists!"
		return -1

	input = open(filename, 'r')
	output = open(outfilename, 'w')
	line_no = 0
	for line in input:
		line = line.strip('\n')
		line_no += 1
		if line_no in locations:
			print >> output, locations[line_no]
		print >> output, line
	output.close()
	input.close()
	old_lines = sum(1 for line in open(filename))
	new_lines = sum(1 for line in open(outfilename))
	apply_file_change(filename, outfilename, logfilename)
	print >>sys.stderr, 'Added', new_lines - old_lines, 'lines to', filename
	return new_lines - old_lines

def add_exec_log_code_to_file(filename, funcs, logfilename):
	lines = get_file_lines(filename)
	locations = {}
	if filename != FunctionLines[EntryFunc][3]:
		locations[1] = 'extern int EXEC_flags[];' + '\nextern void EXEC_log(const char *msg);'
	for func in funcs:
		start_line = get_func_start_line(filename, func, FunctionLines[func][1], lines)
		# Something is wrong, can't instrument
		if start_line == 0:
			continue
		if func == EntryFunc:
			locations[start_line] = '\tEXEC_loader();'
			continue
		locations[start_line] = get_exec_log_code(func)
		print >>sys.stderr, 'Adding EXEC for', func, '@', start_line, 'of', filename

	return insert_code(filename, locations, logfilename)

def add_sec_settings_to_file(filename, funcsToDisable, secCP, patchChecks, logfilename):
	lines = get_file_lines(filename)
	locations = {}
	if filename != FunctionLines[EntryFunc][3]:
		locations[1] = 'extern int FPSW_flags[];\nextern void FPSW_log(const char *msg);'
	for func in funcsToDisable:
		start_line = get_func_start_line(filename, func, FunctionLines[func][1], lines)
		# Something is wrong, can't instrument
		if start_line == 0:
			continue
		if func == EntryFunc:
			locations[start_line] = '\tFPSW_loader();'
			continue
		# disable the use of label line for now
		#label_line = FunctionLines[func][2]
		label_line = 0
		if label_line > 0:
			locations[start_line] = get_CP_combined_code(func, secCP[func])
			locations[label_line] = get_label(func) + ':'
		else:
			locations[start_line] = get_CP_combined_code_ret(func, secCP[func])
	#for (line, line1, line2) in patchChecks:
	#	locations[line] = get_call_checks(lines, line1, line2)

	for line in locations:
		print >>sys.stderr, filename, line, ':'
		print >>sys.stderr, '\t', locations[line]

	return insert_code(filename, locations, logfilename)

def lines_of_file(filename):
	return len(get_file_lines(filename))

# secCP: mapping from instrumented functions to protected functions
def identify_protectable_funcs(funcs, secCP, protFuncs):
	#print >>sys.stderr, funcs
	count_disabled_by_callers = 0
	for func in funcs:
		#print >> sys.stderr, '\t', func
		funcsToDisable = set()
		get_locations_to_add_sec_setting3(func, funcsToDisable)
		if len(funcsToDisable):
			protFuncs.append(func)
			for secFunc in funcsToDisable:
				if not secFunc in secCP:
					secCP[secFunc] = []
				secCP[secFunc].append(func)
				print >>sys.stderr, secFunc, "is used to protect", func
			#for f in funcsToDisable:
			#	print >> sys.stderr, '\t\t', f
			if not func in funcsToDisable:
				count_disabled_by_callers += 1
	return count_disabled_by_callers

def print_protected_funcs(title, protFuncs, secCP, flag):
	print len(protFuncs), title
	print >>sys.stderr, len(protFuncs), title
	total_protected_lines = 0
	for func in protFuncs:
		if func in ErrorReturns:
			kind, ret = get_error_return(func)
			if ret[0]:
				print >>sys.stderr, '\t' + flag, func, kind, get_name_for_BB(ret[0]), ret[1]
			else:
				print >>sys.stderr, '\t' + flag, func, kind, None, ret[1]
			all_rets = get_all_error_return(func)
			print >>sys.stderr, '===================================='
			for kind in all_rets:
				for BB, ret in all_rets[kind]:
					if BB:
						print >>sys.stderr, '\t\t', kind, get_name_for_BB(BB), ret
					else:
						print >>sys.stderr, '\t\t', kind, None, ret
		else:
			print >>sys.stderr, '\t' + flag, func, 'is protected by caller'
			ProtectedByCaller.append(get_setting_name_ex(func))
		total_protected_lines += FunctionLines[func][0]
	print total_protected_lines, 'lines can be protected.'
	print len(secCP), 'functions need to be modified.'

def add_sec_settings_all(logfilename, settingsfile, checkOnly=False):
	print >> sys.stderr, "Analyzed reachable functions:"
	secCP = {}
	protFuncs = []
	files = {}
	print >>sys.stderr, "Identify directly-protectable functions..."
	#count_disabled_by_callers = identify_protectable_funcs(set().union(FunctionLines).intersection(ReachableFuncs), secCP, protFuncs)
	count_disabled_by_callers = identify_protectable_funcs(FunctionLines, secCP, protFuncs)
	print_protected_funcs('functions can be protected.', protFuncs, secCP, '+')

	secCP2 = {}
	protFuncs2 = []
	print >>sys.stderr, "Identify indirectly-protectable functions..."
	identify_protectable_funcs(set().union(FunctionLines).difference(protFuncs), secCP2, protFuncs2)
	print_protected_funcs('additional functions can be protected.', protFuncs2, secCP2, '*')

	#print >> sys.stderr, "Protected functions:"
	#for func in protFuncs:
	#	print >> sys.stderr, '\t', func
	print >> sys.stderr, "Modified functions:"
	for func in secCP:
		print >> sys.stderr, '\t', func
	patchChecks = {}
	print >> sys.stderr, "Patched functions:"
	print >>sys.stderr, 'Counting files and lines of code:'
	allfiles = {}
	count_all_lines = 0
	for func in FunctionLines:
		if func in ReachableFuncs:
			filename = FunctionLines[func][3]
			if not filename in allfiles:
				allfiles[filename] = 0
				#count_all_lines += FunctionLines[func][0]
				count =	lines_of_file(filename)
				count_all_lines += count
				print >>sys.stderr, count, filename
	print len(allfiles), 'files.'
	print count_all_lines, 'lines of code.'
	for func in secCP:
		filename = FunctionLines[func][3]
		if not filename in files:
			files[filename] = []
			patchChecks[filename] = []
		files[filename].append(func)
		if func in UncheckedCalls:
			print >> sys.stderr, '\t', "call to", func
			for caller in UncheckedCalls[func]:
				print >> sys.stderr, '\t\t', caller
				filename = FunctionLines[caller][3]
				if not filename in files:
					files[filename] = []
					patchChecks[filename] = []
				patchChecks[filename].append(UncheckedCalls[func][caller])
	print len(files), 'of' , len(allfiles), 'files', '(', len(files) * 100.0 / len(allfiles), '%)', 'need to be modified.'
	if checkOnly:
		return (protFuncs, 0, count_disabled_by_callers)
	count_lines = 0

	# ensure EntryFile is on the list
	entryFile = FunctionLines[EntryFunc][3]
	if not entryFile in files:
		files[entryFile] = []
	files[entryFile].append(EntryFunc)
	if not entryFile in patchChecks:
		patchChecks[entryFile] = []

	for filename in files:
		print >>sys.stderr, "add_sec_settings_to_file for", filename
		count_lines += add_sec_settings_to_file(filename, files[filename], secCP, patchChecks[filename], logfilename)
	print count_lines, 'of', count_all_lines, 'lines of code', count_lines * 100.0 / count_all_lines, '%)', 'need to be added.'
	output = open(settingsfile, 'w')
	#for setting in ProtectedName:
	#	print >> output, setting
	for FPSW in ProtectedFuncNumber:
		ID = ProtectedFuncNumber[FPSW]
		funcName = ProtectedFuncRef[ID]
		if not FPSW in ProtectedByCaller:
			print >>output, FPSW, ID, get_error_return(funcName)[0]
		else:
			print >>output, FPSW, ID, 100
	output.close()
	add_loader_code(TALOS_LOADER_FILE, logfilename)
	return (protFuncs, count_lines, count_disabled_by_callers)

def add_exec_log_code_all(logfilename):
	files = {}
	for func in FunctionLines:
		if func in ReachableFuncs:
			filename = FunctionLines[func][3]
			if not filename in files:
				files[filename] = []
			files[filename].append(func)

	# ensure EntryFile is on the list
	entryFile = FunctionLines[EntryFunc][3]
	if not entryFile in files:
		files[entryFile] = []
	files[entryFile].append(EntryFunc)

	for filename in files:
		add_exec_log_code_to_file(filename, files[filename], logfilename)
	add_exec_loader_code(TALOS_EXEC_FILE, logfilename)

def remove_sec_settings_all(logfilename):
	input = open(logfilename, 'r')
	for line in input:
		line = line.strip()
		if not line:
			continue
		parts = line.split(' ')
		print 'ren', parts[0], parts[1]
		try:
			os.rename(parts[0], parts[1])
		except OSError:
			pass

def find_common_code(lines1, lines2):
	if len(lines1) <= len(lines2):
		count = len(lines1)
	else:
		count = len(lines2)
	if count == 0:
		return []
	for l in range(-1, -count - 1, -1):
		if lines1[l] != lines2[l]:
			break
	return lines1[l+1:]

def strip_lines(lines):
	for l in range(len(lines)):
		lines[l] = lines[l].strip()
	return lines

def find_return_NULL(func):
	lines = []
	first = True
	allLines = get_file_lines(FunctionLines[func][3])
	if allLines:
		print >>sys.stderr, '......', func
		for BB, ret in NullReturns[func]:
			startLine, endLine, var = ret.split(',')
			retLines = strip_lines(allLines[int(startLine) - 1 : int(endLine)])
			if first:
				print >>sys.stderr, '.........', startLine, endLine, lines, retLines
				lines = retLines
				first = False
			else:
				print >>sys.stderr, '.........', startLine, endLine, lines, retLines
				lines = find_common_code(lines, retLines)
	return lines

def generalize_return_NULL():
	#countFuncMulNullReturn = 0
	for func in NullReturns:
		#if len(NullReturns[func]) > 1:
		#	countFuncMulNullReturn += 1
		#	continue
		prototype = FunctionLines[func][4]
		print >>sys.stderr, '...', prototype
		if not prototype in NullReturnPrototype:
			NullReturnPrototype[prototype] = []
			NullReturnPrototype[prototype].append([func])
			NullReturnPrototype[prototype].append(find_return_NULL(func))
		else:
			NullReturnPrototype[prototype][0].append(func)
 			NullReturnPrototype[prototype][1] = find_common_code(NullReturnPrototype[prototype][1], find_return_NULL(func))
	print >>sys.stderr, "return NULL for prototypes:"
	for prototype in NullReturnPrototype:
		print >>sys.stderr, '\t', prototype, NullReturnPrototype[prototype]
		for func in ProtoTypes[prototype]:
			if func in NullReturnPrototype[prototype][0]:
				continue
			if (getCallers(func) == getCallers(NullReturnPrototype[prototype][0][0])):
				print >>sys.stderr, '\t\t', func

def prt_func_list(desc, funcList):
	print >>sys.stderr, desc
	print >>sys.stderr, '========================================'
	for func in funcList:
		print >>sys.stderr, '\t', func
	print >>sys.stderr, '========================================'

def propagate_protectable_functions(funcList):
	propProtFuncs = set()
	funcSet = set()
	funcSet = funcSet.union(funcList)
	funcSet = funcSet.intersection(RetCalls)
	for func in funcSet:
		for (caller, BB) in RetCalls[func]:
			propProtFuncs.add(caller)
	return propProtFuncs

def prt_cond_checks():
	print >>sys.stderr, 'CondChecks:'
	for (BB, edge) in CondChecks:
		print >>sys.stderr, get_name_for_BB(BB), edge, BB
		for (pred, lhs, rhs) in CondChecks[(BB, edge)]:
			print >>sys.stderr, '\t', pred, lhs, rhs
	print >>sys.stderr

def list_cond_exec_funcs(funcList):
	pass

# predicate functions
def equal(lhs, rhs):
	return lhs == rhs

def not_equal(lhs, rhs):
	return lhs != rhs

def greater_than(lhs, rhs):
	return lhs > rhs

def greater_or_equal(lhs, rhs):
	return lhs >= rhs

def less_than(lhs, rhs):
	return lhs < rhs

def less_or_equal(lhs, rhs):
	return lhs <= rhs

# misc functions
def prt_percentage(parms):
	numbers = []
	for (tot, items) in parms:
		for item in items:
			desc = item[0]
			val = item[1]
			print desc, val, '(', val * 100.0 / tot, ')'
			numbers.append(round(val * 100.0 / tot, 1))
	output = ''
	for number in numbers:
		if output:
			output += ' & ' + str(number) + '\%'
		else:
			output += str(number) + '\%'
	print output
	
# main function
start_time = time.time()

parser = argparse.ArgumentParser()
parser.add_argument('-P', dest='pattern', help='Pattern to match setting names', nargs=1)
parser.add_argument('-d', dest='Debug', help='Enable/disable debugging', action='store_true')
parser.add_argument('input', help='input [Location]', nargs='+')
parser.add_argument('-L', dest='NameList', help='Filename of the list of setting names', nargs=1)
parser.add_argument('-N', dest='PathCount', help='Limit number of call paths', default=0, type=int)
parser.add_argument('-C', dest='ControlPoints', help='Filename of the control points', nargs=1)
parser.add_argument('-E', dest='EntryFunc', help='Decorated name of the entry function', nargs=1, required=True)
parser.add_argument('-i', dest='InteractiveMode', help='Runs in interactive mode', action='store_true')
parser.add_argument('-v', dest='Verbose', help='Output in Verbose mode', action='store_true')
parser.add_argument('-I', dest='IgnoreEntryFunc', help='Ignore entry function in finding call paths', action='store_true')
parser.add_argument('-S', dest='AddSecuritySetting', help='Add security settings', nargs=1)
parser.add_argument('-R', dest='DelSecuritySetting', help='Remove security settings', nargs=1)
parser.add_argument('-w', dest='IdentifyWorkarounds', help='Identify All Workarounds', action='store_true')
parser.add_argument('-W', dest='IdentifyOneWorkaround', help='Identify a workaround', action='store_true')
parser.add_argument('-O', dest='SettingsFile', help='Filename of security settings', nargs=1)
parser.add_argument('-K', dest='CheckOnly', help='Do not apply security settings', action='store_true')
parser.add_argument('-G', dest='AddExecLog', help='Add execution logging', nargs=1)
parser.add_argument('-D', dest='CondExecFuncs', help='Identify functions taht are executed conditionaly', action='store_true')

args = vars(parser.parse_args(sys.argv[1:]))
if args['SettingsFile']:
	SettingsFile = args['SettingsFile'][0]
else:
	SettingsFile = None
if args['AddSecuritySetting']:
	AddSecuritySetting = args['AddSecuritySetting'][0]
	if not SettingsFile:
		print "SettingsFile not set!"
		sys.exit()
else:
	AddSecuritySetting = None
if args['DelSecuritySetting']:
	DelSecuritySetting = args['DelSecuritySetting'][0]
else:
	DelSecuritySetting = None
if args['pattern']:
	NamePattern = re.compile(args['pattern'][0])
else:
	NamePattern = None
if args['NameList']:
	NameListFile = args['NameList'][0]
else:
	NameListFile = None
if args['AddExecLog']:
	AddExecLog = args['AddExecLog'][0]
else:
	AddExecLog = None
PathCount = args['PathCount']
EntryFunc = args['EntryFunc'][0]
if len(args['input']) == 2:
	InputFile = args['input'][0]
	Location = args['input'][1]
else:
	InputFile = args['input'][0]
	Location = None

if args['ControlPoints']:
	CPFile = args['ControlPoints'][0]
else:
	CPFile = None

CondExecFuncs = args['CondExecFuncs']

Debug = args['Debug']
InteractiveMode = args['InteractiveMode']
Verbose = args['Verbose']
IgnoreEntryFunc = args['IgnoreEntryFunc']
IdentifyWorkarounds = args['IdentifyWorkarounds']
IdentifyOneWorkaround = args['IdentifyOneWorkaround']
CheckOnly = args['CheckOnly']

if InteractiveMode and (AddSecuritySetting or DelSecuritySetting):
	print "InteractiveMode, AddSecuritySetting, DelSecuritySetting cannot be used together"
	exit()
if AddSecuritySetting and DelSecuritySetting:
	print "AddSecuritySetting and DelSecuritySetting cannot be used together"
	exit()

if DelSecuritySetting:
	remove_sec_settings_all(DelSecuritySetting)
	exit()

print 'InputFile:', InputFile
print 'Location:', Location
print 'NamePattern:', NamePattern
print 'Debug:', Debug
print 'PathCount:', PathCount
if NameListFile:
	NameList = load_nameList(NameListFile)
else:
	NameList = None
print 'EntryFunc:', EntryFunc
print 'CPFile:', CPFile

Functions = {}
BBs = {}
AllKeys = {}
BBref = {}
FunctionRef = {}
APIcalls = {}
APIs = {}
UI_APIs = {}
Calls = {}
Access = {}
Update = {}
Read = {}
UI_Keys = {}
BBread = {}
BBDependency = {}
BBKeyDependency = {}
RCalls = {}
Files = {}
FileRef = {}
Lines = {}
BBrefFunc = {}
FunctionLocation = {}
References = {}
ConfigKeys = []
ControlBBs = {}
FunctionLines = {}
Callees = {}
LoggingFuncs = []
ReturnFuncs = []
FuncControlBBs = {}
BBFollowByReturn = {}
ErrorFuncs = {}
ErrorReturns = {}
RetCalls = {}
UncheckedCalls = {}
ProtectedName = {}
FuncSimplePath = {}
NullReturns = {}
ProtoTypes = {}
FuncRetPointer = []
NullReturnPrototype = {}
ConstReturns = {}
CondChecks = {}
PredicateOpps = {'==':'!=', '!=':'==', '> ':'<=', '>=':'< ', '< ':'>=', '<=':'> '}
PredicateFuncs = {'==':equal, '!=':not_equal, '> ':greater_than, '>=':greater_or_equal, '< ':less_than, '<=':less_or_equal}
LineOfCall = {}
RetCheckedFunc = {}
ErrorReturnPriority = [1, 2, 3, 4, 5, 10, 11, 0]
ProtectedFuncNumber = {}
ProtectedFuncRef = {}
ProtectedByCaller = []
ExecFuncNumber = {}

# Read API rules from configuration file analyzer.cfg
TALOS_DIR=os.path.split(sys.argv[0])[0]
cfgFilename = os.path.join(TALOS_DIR, 'analyzer.cfg')
if not os.path.exists(cfgFilename):
	print 'Error:', cfgFilename, 'does not exist!'
	sys.exit()

load_cfg(cfgFilename)

TALOS_LOADER_FILE = os.path.join(TALOS_DIR, 'Talos_loader.c')
TALOS_EXEC_FILE = os.path.join(TALOS_DIR, 'Talos_exec.c')

INPUT_DIR=os.path.split(InputFile)[0]
linesFilename = os.path.join(INPUT_DIR, os.path.splitext(os.path.basename(InputFile))[0] + '.lines')
if not os.path.exists(linesFilename):
	print 'Error:', linesFilename, 'does not exist!'
	sys.exit()

#input = open(InputFile, 'r')
#inputlines = input.readlines()
#input.close()

pass1(InputFile) # identify API wrappers
inputlines = None # release memory
pass2(InputFile)
#pass3(InputFile)
#pass4(InputFile)
ReachableFuncs = []
ReachableCalls = set()
print 'build_call_graph...'
build_call_graph(EntryFunc)
print 'remove_unreachable_calls...'
remove_unreachable_calls()

print 'build_BB_key_dependency...'
build_BB_key_dependency()
file = open(InputFile + '.BBKeyDependency', 'w')
oldstdout = sys.stdout
sys.stdout = file
countConfigDependentLines = 0
countControlKeys = set()
print "Total", len(BBKeyDependency), "dependent Lines"
for BB in BBKeyDependency:
	print get_name_for_BB(BB)
	keys = find_dependent_key(BB, True, 0, Verbose)
	if len(keys) > 0:
		countControlKeys = countControlKeys.union(keys.keys())
		print keys
		countConfigDependentLines += 1
print 'Total', countConfigDependentLines, 'config dependent Lines'
print 'Total', len(countControlKeys), 'config dependency keys'
for key in countControlKeys:
	print '\t', key
file.close()
sys.stdout = oldstdout

TotLines = load_lines_file(linesFilename)

print 'identify error returns...'
TotFuncRetError = find_error_return_for_func_all()
print 'propagate error returns...'
count_error_propagation = 0
while True:
	old_count = count_error_propagation
	count_error_propagation += direct_error_propagation()
	count_error_propagation += indirect_error_propagation()
	count_error_propagation += reverse_error_propagation()
	if count_error_propagation == old_count:
		break

print 'All Functions:', len(Functions)
print 'Reachable Functions:', len(ReachableFuncs)
#prioritize_heuristics()
TotFuncs = []
TotFuncRetPointer = []
for func in ReachableFuncs:
	if func in FunctionLines:
		TotFuncs.append(func)
		if func in FuncRetPointer:
			TotFuncRetPointer.append(func)

print 'Reachable Lines:', TotLines
print 'Functions that return pointer:', len(TotFuncRetPointer)
prt_func_list('Functions that return pointer:', TotFuncRetPointer)
print >>sys.stderr, 'Functions that return pointer, has no error return, but whose return value is checked:'
for func in TotFuncRetPointer:
	if not func in ErrorReturns:
		if func in RetCheckedFunc:
			print >>sys.stderr, '\t', func
			add_error_return(4, func, None, 'NULL')
print >>sys.stderr, 'Pointer-returnning functions that cannot be protected:'
countPointerFuncNoProt = 0
for func in TotFuncRetPointer:
	if not func in ErrorReturns:
		print >>sys.stderr, '\t', func
		countPointerFuncNoProt += 1
print >>sys.stderr, countPointerFuncNoProt * 100.0 / len(TotFuncRetPointer), '% of all pointer-returning functions'

generalize_return_NULL()

TotDirectProtFuncs = set(ErrorReturns).intersection(ReachableFuncs).intersection(FunctionLines)
print 'Directly protectable functions:', len(TotDirectProtFuncs)
statProtFuncs = {}
for kind in ErrorReturnPriority:
	statProtFuncs[kind] = 0
for func in TotDirectProtFuncs:
	kind, errRet = get_error_return(func)
	statProtFuncs[kind] += 1
print statProtFuncs

print >>sys.stderr, len(FuncSimplePath), 'functions with simple path that is dependent on check of non-local var:'
for func in FuncSimplePath:
	print >>sys.stderr, '\t', func

if Verbose:
	print_totals()

print 'Analyzed Reachable Functions:', len(TotFuncs)

if IdentifyWorkarounds:
	print 'identify existing workarounds...'
	funcsHasWorkaround = find_workaround_all(Verbose)
	print len(funcsHasWorkaround) * 100.0 / len(TotFuncs), 'precent of functions'

if InteractiveMode:
	interact()

if Location:
	if IdentifyOneWorkaround:
		find_workaround(Location, Verbose)
	else:
		find_constraints(Location, Verbose)

#print 'keys:'
#for key in keys:
#	print '\t', key
#print '\t\tcall chain:'
#for call in paths:
#	print '\t\t\t', get_name_for_BB(call)
if CPFile:
	count_disabled_lines_file(CPFile)

if AddSecuritySetting:
	if not os.path.exists(TALOS_LOADER_FILE):
		print 'Error', TALOS_LOADER_FILE, 'does not exist!'
		sys.exit()

	all_prot_funcs = set()
	all_prot_funcs = all_prot_funcs.union(ErrorReturns)
	#all_prot_funcs = all_prot_funcs.union(FuncSimplePath)
	#all_prot_funcs = all_prot_funcs.union(FuncRetPointer)
	count_disabled_by_callers = 0
	(protFuncs, count, count_disabled_by_callers) = add_sec_settings_all(AddSecuritySetting, SettingsFile, CheckOnly)
	all_prot_funcs = all_prot_funcs.union(protFuncs)

	#propProtFuncs = propagate_protectable_functions(all_prot_funcs)
	#all_prot_funcs = all_prot_funcs.union(propProtFuncs)
	all_prot_funcs = all_prot_funcs.intersection(FunctionLines)
	all_prot_funcs = all_prot_funcs.intersection(ReachableFuncs)
	print 'All protectable funcions:', len(all_prot_funcs), '(', len(all_prot_funcs) * 100.0 / len(TotFuncs), ')'
	print 'Indirectly protected functions:', count_disabled_by_callers, '(', count_disabled_by_callers * 100.0 / len(TotFuncs), ')'
	#prt_func_list('All protectable funcions:', all_prot_funcs)
	count_not_protected_funcs = 0
	print >>sys.stderr, "Functions that can not be protected:"
	all_funcs = set()
	all_funcs = all_funcs.union(ReachableFuncs)
	all_funcs = all_funcs.intersection(FunctionLines)
	for func in all_funcs:
		if not func in all_prot_funcs:
			count_not_protected_funcs += 1
			ret_type = FunctionLines[func][4].split('(')[0]
			print >>sys.stderr, '\t', FunctionLines[func][0], ret_type, func, FunctionLines[func][3]
	print >>sys.stderr, count_not_protected_funcs, "functions."
	#all_funcs = set()
	#all_funcs = all_funcs.union(TotFuncs)
	#all_funcs = all_funcs.union(all_prot_funcs)
	#print 'Total funcions:', len(all_funcs)
	# estimate the lines of code that needs to be added
	#lines_to_add = (len(all_prot_funcs) - count_disabled_by_callers) * 3 + count_disabled_by_callers * 2
	#print lines_to_add, 'lines of code need to be added.'
	parms = [[len(TotFuncs), [['Protectable functions:', len(TotDirectProtFuncs) + count_disabled_by_callers]]], [len(TotFuncs), [['\t2 - Functions with simple path:', statProtFuncs[2]], ['\t0 & 1 - Functions with error path:', statProtFuncs[0] + statProtFuncs[1]], ['\t3 & 4 & 5 - Functions that return pointer:', statProtFuncs[3] + statProtFuncs[4] + statProtFuncs[5]], ['\t10 & 11 - Functions that have propagated error return:', statProtFuncs[10] + statProtFuncs[11]], ['\tFunctions that are protected by callers:', count_disabled_by_callers]]]]
	prt_percentage(parms)
	if Verbose:
		print >>sys.stderr, "ID of each protected functions:"
		for FPSW in ProtectedFuncNumber:
			ID = ProtectedFuncNumber[FPSW]
			funcName = ProtectedFuncRef[ID]
			if not FPSW in ProtectedByCaller:
				print >>sys.stderr, '\t', FPSW, ID, get_error_return(funcName)[0], funcName
			else:
				print >>sys.stderr, '\t', FPSW, ID, 100, funcName

if AddExecLog:
	if not os.path.exists(TALOS_EXEC_FILE):
		print 'Error', TALOS_EXEC_FILE, 'does not exist!'
		sys.exit()

	add_exec_log_code_all(AddExecLog)

if CondExecFuncs:
	list_cond_exec_funcs(TotFuncs)

end_time = time.time()
print 'Analyze time:', end_time - start_time

