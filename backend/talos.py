#!/usr/bin/python3
# find config options on which a code fragment is control dependent
import sys, os, copy, time, argparse, re
# Import readline to fix a Python bug with raw_input
import readline
def usage():
	print ("Usage: dependency InputFile [Location]")
	sys.exit()

def get_file(dir, ffile):
	if not (dir, ffile) in Files:
		#print >>sys.stderr, 'Adding file ', dir, file
		Files[(dir, ffile)] = len(Files)
		FileRef[Files[(dir, ffile)]] = (dir, ffile)
		if Debug:
			print ('\tAdded file',' (', dir, ',', ffile, ')', '=', Files[(dir, ffile)], file = sys.stderr)
	return Files[(dir, ffile)]

def get_function(dir, ffile, function):
	if not (dir, ffile, function) in Functions:
		ID = len(Functions)
		Functions[(dir, ffile, function)] = ID
		FunctionRef[ID] = (dir, ffile, function)
		if Debug:
			print ('\tAdded function', '(', dir, ',', ffile, ',', function, ')', '=', ID, file = sys.stderr)
	else:
		ID = Functions[(dir, ffile, function)]
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
			print ('\tAdded BB', ID, '=', fileID, line, BB, callee, file = sys.stderr)
	else:
		ID = BBs[(fileID, BB, callee)]
	if line != 0:
		if not ID in BBref:
			BBref[ID] = (fileID, line)
		elif (fileID, line) != BBref[ID]:
			if Debug:
				print ('Warning: BB', ID,  '(', fileID, line, ')', 'already defined in BBref for', BBref[ID], file = sys.stderr)
		if not ID in BBrefFunc:
			BBrefFunc[ID] = functionID
			if Debug:
                            print ('\tBB', ID, 'is defined for function:', functionID, file = sys.stderr)
		elif functionID != BBrefFunc[ID]:
			if Debug:
				print ('Warning: BB', ID, '(', functionID, ')', 'already defined in BBrefFunc for', BBrefFunc[ID], file = sys.stderr)
	return ID

# get BB ID giving priority to BB ID corresponding to function call
def get_BB2(fileID, functionID, line, BB):
	if (fileID, line) in LineOfCall:
		return LineOfCall[(fileID, line)]
	else:
		return get_BB(fileID, functionID, line, BB)

# kind: 1 - error logging/handling, 3 - pointer returnning, 4 - propagation, 5 - special constant return
def add_error_return(kind, func, BB, ret_value):
	print ('\t', 'add_error_return', func, BB, ret_value, 'kind(', kind, ')', file = sys.stderr)
	if ret_value == '' or ret_value == 'None':
		print('\tError: empty ret_value', file = sys.stderr)
		return
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
	return get_error_return(func)[1][1]

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
	print ('pred_satisfiable', lhs, pred, rhs, file = sys.stderr)
	try:
		l = int(lhs)
		r = int(rhs)
		return PredicateFuncs[pred](int(l), int(r))
	except ValueError:
		return PredicateFuncs[pred](lhs, rhs)

def is_ret_value_satisfy_pred(funcName, pred, rhs):
	print ('is_ret_value_satisfy_pred', funcName, file = sys.stderr)
	for kind in ErrorReturns[funcName]:
		for (BB, value) in ErrorReturns[funcName][kind]:
			if pred_satisfiable(value, pred, rhs):
				return True
	return False

def get_ret_value_to_satisfy_pred(pred, rhs):
	print ('get_ret_value_to_satisfy_pred', pred, rhs, file = sys.stderr)
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
# 0. module name
# 1. directory name
# 2. file name
# 3. line number 
# 4. function name 
# 5. basic block ID (BBID)
# 6. dominator basic block ID (dominateBBID)
# 7. callee name
# 8. call argument, e.g. key name
# 9: Access type 
#	'0' - Read, '1' - write, when call type is 2
#	'-1' - function call, when call type is 0 or 1
#	'-2' - other, when call type is 4, or 5, etc.
#	The BB (line number) in which a key is accessed, that this BB (line) refers to, when call type is 6
# 10: call type '0' - non-API call, '1' - API call, '2' - direct Access, '3' - dependency, '4' - FP definition, '5' - FP call, '6' - reference, '7' - return const, '8' - return call, '9' - call with missed check, '10' - simple path, '11' - return NULL, '12' - return value checked by caller, '13' - return statement line, '14' - function lines info
# For function call:
# 	The remaining fields represents each argument of the function call:
# 	number - numeric argument
# 	double-quoted string - string argument
# 	single-quoted number - formal argument of the function making the call

# initialize and identify API wrappers
# load data into various data structures:
#	 Files, FileRef, Functions, FunctionRef, FunctionLocation, BBs, Lines, BBref, BBrefFunc, BBDependency, APIs, References
def pass1(InputFile):
	print ("Pass 1...initialize")
	startTime = time.time()
	countWrappers = 0
	lineNo = 0
	input = open(InputFile, 'r')
	for line in input:
		lineNo = lineNo + 1
		line = line.strip()
		if lineNo % 100000 == 0:
			print ('Processed', lineNo, 'lines')
		if Debug:
			print ("Processing line", lineNo, file = sys.stderr)
			print('\t', line, file = sys.stderr)
		parts = line.split('@')
		if len(parts) < 11:
			print ("Invalid number of fields", len(parts),"at line", lineNo)
			print ("Invalid number of fields", len(parts),"at line", lineNo, file = sys.stderr)
			print ('\t', parts, file = sys.stderr)
		#print parts
		functionName = parts[4]
		if functionName == '*':
			print ("Ignoring * as caller at line", lineNo)
			continue
		calleeName = parts[7]
		try:
			functionID = get_function(parts[1], parts[2], functionName)
		except IndexError:
			print ('Error in line', lineNo, ',', parts, file = sys.stderr)
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
			if retInfo[1][-1] == 'L':
				retInfo[1] = retInfo[1][:-1]
				ret_line = int(retInfo[1], 16)
			else:
				ret_line = int(retInfo[1], 0)
			ret_value = retInfo[2]
			ret_BB = get_BB(fileID, functionID, str(ret_line), str(ret_line))
			BBFollowByReturn[BB] = (ret_BB, ret_value, fileID);
		
			if ret_value == "NULL":
				#print >> sys.stderr, lineNo, functionName, 'returns NULL'
				if not functionName in FunctionLines:
					FunctionLines[functionName] = [0, 0, -int(parts[3]), None, None]
				else:
					FunctionLines[functionName][2] = -int(parts[3])
				add_error_return(3, functionName, BB, ret_value)
		else:
			try:
				callType = int(parts[10])
			except ValueError:
				callType = 0
				print ('Invalid callType in line', lineNo, ',', parts, file = sys.stderr)
				continue
		print('\tcallType', callType, file=sys.stderr)
		if callType == 14:
			lines_info = parts[8].split(';')
			line_count = int(lines_info[0])
			path_name = lines_info[1]
			proto_type = lines_info[2]
			start_line = int(parts[3])
			add_lines_info(functionName, line_count, start_line, path_name, proto_type)
		elif callType == 13:
			FuncReturnLine[functionName] = parts[3]
		elif callType == 10:
			FuncSimplePath[functionName] = parts[8]
			# take out simple path heuristics for now
			#add_error_return(2, functionName, BB, parts[8])
			continue
		elif callType == 11:
			if valid_return(parts[8]):
				if not functionName in NullReturns:
					NullReturns[functionName] = []
				NullReturns[functionName].append((BB, parts[8]))
				if not functionName in FunctionLines:
					FunctionLines[functionName] = [0, 0, 0, os.path.join(parts[1], parts[2]), None, None]
				else:
					FunctionLines[functionName][3]  = os.path.join(parts[1], parts[2])
			continue
		elif callType == 9:
			error_handle_lines = parts[8].split(',')
			print ("Line", lineNo, "unchecked call", calleeName, "is called by", functionName, error_handle_lines, file = sys.stderr)
			if not calleeName in UncheckedCalls:
				UncheckedCalls[calleeName] = {}
			UncheckedCalls[calleeName][functionName] = (int(error_handle_lines[2]), int(error_handle_lines[0]), int(error_handle_lines[1]))
			continue
		elif callType == 8:
			if not calleeName in RetCalls:
				RetCalls[calleeName] = set()
			print('\tAdding return call', calleeName, 'for', functionName, file=sys.stderr)
			RetCalls[calleeName].add((functionName, BB))
			continue
		elif callType == 7:
			if not functionName in ConstReturns:
				ConstReturns[functionName] = {}
			ConstReturns[functionName][BB] = (parts[8], 0)
			if parts[8] == 'NULL':
				add_error_return(3, functionName, BB, 'NULL')
			if parts[8] == '4294967295':
				add_error_return(5, functionName, BB, 4294967295)
			continue
		elif callType == 12:
			if not calleeName in RetCheckedFunc:
				RetCheckedFunc[calleeName] = set()
			RetCheckedFunc[calleeName].add(BB)
			val = parts[8].split(',')[0]
			pred = parts[8].split(',')[1]
			# Only two-way branch is considered
			if not (BB, 0) in CondChecks:
				CondChecks[(BB, 0)] = set()
			if Debug:
				print('\tCondChecks', get_name_for_BB(BB), 0, pred, calleeName, val, file=sys.stderr)
			CondChecks[(BB, 0)].add((pred, calleeName, val))
			if not (BB, 1) in CondChecks:
				CondChecks[(BB, 1)] = set()
			if Debug:
				print('\tCondChecks', get_name_for_BB(BB), 1, reverse_predicate(pred), calleeName, val, file=sys.stderr)
			CondChecks[(BB, 1)].add((reverse_predicate(pred), calleeName, val))
			continue
		#if calleeName:
		#	if callType >= 100:
		#		BBFollowByReturn[BB] = (callType / 1000, (callType % 1000) / 100);
		#		callType %= 100
		elif callType == 6: # reference
			rBB = parts[9]
			referBB = get_BB(fileID, functionID, rBB, rBB)
			if not BB in References:
				References[BB] = set()
			References[BB].add(referBB)
			if Debug:
				print (BB, "refers", referBB, file = sys.stderr)
		if (parts[6] and parts[6] != '0'):
			#dominateBB = get_BB(fileID, functionID, 0, parts[6])
			for dpBB in parts[6].split(','):
				dBBC = dpBB.split(';')[0]
				dBBSep = dBBC.find('.')
				if dBBSep > 0:
                                    dBB = dBBC[:dBBSep]
                                    dBBCallee = dBBC[dBBSep + 1:]
				else:
                                    dBB = dBBC
                                    dBBCallee = ""
				edge = int(dpBB.split(';')[1])
				if not BB in BBDependency:
					BBDependency[BB] = []
				#dominateBB = get_BB2(fileID, functionID, dBB, dBB) # BB is lineNum
				dominateBB = get_BB(fileID, functionID, dBB, dBB, dBBCallee) # BB is lineNum
				#if dominateBB in References:
				#	for rBB in References[dominateBB]:
				#		BBDependency[BB].add(rBB)
				#else:
				#	BBDependency[BB].add(dominateBB)
				BBDependency[BB].append((dominateBB, edge))
				if Debug:
				    print("\tBBDependency", get_name_for_BB(BB), get_name_for_BB(dominateBB), file=sys.stderr)
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
					print ('Identified wrapper', functionName, 'in line', lineNo, file = sys.stderr)
				arg = parts[keyarg][1:-1]
				if not functionName in APIs:
					APIs[functionName] = [1, APIs[calleeName][1], arg]
					countWrappers = countWrappers + 1
	print ( 'Identified', countWrappers, 'wrappres',file = sys.stderr)
	for api in APIs:
		if APIs[api][0] != 0:
			print ('\t', api, APIs[api], file = sys.stderr)
	end_time = time.time()
	print ("Pass 1 done -", end_time - startTime, "seconds", file = sys.stderr)
	print ("Pass 1 done")

# process direct API Calls
def pass2(InputFile):
	print ("Pass 2...process direct API Calls")
	startTime = time.time()
	lineNo = 0
	input = open(InputFile, 'r')
	for line in input:
		lineNo = lineNo + 1
		if lineNo % 100000 == 0:
			print ('Processed', lineNo, 'lines')
		line = line.strip()
		parts = line.split('@')
		if len(parts) < 11:
			print ("Invalid number of fields at line", lineNo)
		#print parts
		functionName = parts[4]
		if functionName == '*':
			print ("Ignoring * as caller at line", lineNo)
			continue
		calleeName = parts[7]
		try:
			functionID = get_function(parts[1], parts[2], functionName)
		except IndexError:
			print ('Error in line', lineNo, ',', parts, file = sys.stderr)
		fileID = get_file(parts[1], parts[2])
		BB = get_BB(fileID, functionID, parts[3], parts[5], calleeName)
		if parts[10].find(',') > 0:
			retInfo = parts[10].split(',')
			callType = int(retInfo[0])
			if retInfo[1][-1] == 'L':
				retInfo[1] = retInfo[1][:-1]
				ret_line = int(retInfo[1], 16)
			else:
				ret_line = int(retInfo[1], 0)
			ret_value = retInfo[2]
		else:
			try:
				callType = int(parts[10])
			except ValueError:
				callType = 0
				print ('Invalid callType in line', lineNo, ',', parts, file = sys.stderr)
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
			arg = int(ErrorFuncs[calleeName][0])
			try:
				if ErrorFuncs[calleeName][0] == -1 or (parts[11 + arg] and parts[11 + arg][0] == ErrorFuncs[calleeName][1]):
					if not functionName in FunctionLines:
						FunctionLines[functionName] = [0, 0, int(parts[3]), None, None, None]
					else:
						FunctionLines[functionName][2] = int(parts[3])
					add_error_return(0, functionName, BB, ErrorFuncs[calleeName][2])
			except IndexError:
				print ('Invalid calls to', calleeName, 'in line', lineNo)
				continue
		dominateBBs = []
		if (parts[6] != '0'):
			for dpBB in parts[6].split(','):
				dBBC = dpBB.split(';')[0]
				dBBSep = dBBC.find('.')
				if dBBSep > 0:
                                    dBB = dBBC[:dBBSep]
                                    dBBCallee = dBBC[dBBSep + 1:]
				else:
                                    dBB = dBBC
                                    dBBCallee = ""
				#dominateBBs.append(get_BB2(fileID, functionID, 0, dpBB))
				dominateBBs.append(get_BB(fileID, functionID, dBB, dBB, dBBCallee))
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
					print ('Error in line', lineNo, ',', parts, 'key name does not exist for API call', calleeName, APIs[calleeName][2], file = sys.stderr)
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
						print ('Possible error in line', lineNo, 'key name starts with comma!', file = sys.stderr)
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
					print ('Error in line', lineNo, ',', parts, 'invalid key name:', keyname, calleeName, APIs[calleeName][2], file = sys.stderr)
					#sys.exit(0)
					#raise Exception('invalid keyname')
	input.close()
	end_time = time.time()
	print ("Pass 2 done -", end_time - startTime, "seconds", file = sys.stderr)
	print ("Pass 2 done.")

# process indirect API Calls
def pass3(InputFile):
	print ("Pass 3...process indirect API Calls")
	countIndirectCalls = 0
	lineNo = 0
	input = open(InputFile, 'r')
	for line in input:
		lineNo = lineNo + 1
		line = line.strip()
		parts = line.split('@')
		if len(parts) < 11:
			print ("Invalid number of fields at line", lineNo)
		#print parts
		functionName = parts[4]
		calleeName = parts[7]
		try:
			functionID = get_function(parts[1], parts[2], parts[4])
		except IndexError:
			print ('Error in line', lineNo, ',', parts, file = sys.stderr)
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
	print ('Identified', countIndirectCalls, "indirect Calls.", file = sys.stderr)
	print ('Identified', countIndirectCalls, "indirect Calls.")
	print ("Pass 3 done.")

# identify keys used by UI
def pass4(InputFile):
	print ("Pass 4...identify keys used by UI")
	countUIKeys = 0
	lineNo = 0
	input = open(InputFile, 'r')
	for line in input:
		lineNo = lineNo + 1
		line = line.strip()
		parts = line.split('@')
		if len(parts) < 11:
			print ("Invalid number of fields at line", lineNo)
		#print parts
		functionName = parts[4]
		calleeName = parts[7]
		try:
			functionID = get_function(parts[1], parts[2], functionName)
		except IndexError:
			print ('Error in line', lineNo, ',', parts, file = sys.stderr)
		#fileID = get_file(parts[1], parts[2])
		#BB = get_BB(fileID, parts[3], parts[5])
		#print >> sys.stderr, lineNo, calleeName
		if calleeName in UI_APIs:
			arg = int(UI_APIs[calleeName][2])
			if parts[11 + arg] and parts[11 + arg][0] == '"':
				countUIKeys = countUIKeys + 1
				UI_Keys[parts[11 + arg].strip('"')] = [functionID, parts[3]]
	input.close()
	print ('Identified', countUIKeys, 'keys used by UI', file = sys.stderr)
	print ('Identified', countUIKeys, 'keys used by UI')
	for key in UI_Keys:
		print ('\t', key)
	print ("Pass 4 done.")

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
			ErrorFuncs[name] = [idx, val, ret]
		elif parts[0] == '7':
			name = parts[1].strip()
			ret = parts[2].strip()
			add_error_return(0, name, None, ret)
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
	print (output)

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
	print (spc + '\t', prefix, 'call chain:', file = output)
	level = 0
	for call in paths:
		print (spc + '\t\t', '[' + str(level) + ']', get_name_for_BB(call), get_name_for_func(BBrefFunc[call]), file = output)
		level += 1
	print (file = output)
		
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
					print (spc + '\t*', get_name_for_BB(BB), keystr, file = sys.stderr)
				elif Debug:
					print (spc + '\t#', get_name_for_BB(BB), keystr, file = sys.stderr)
	return keys

def find_dependent_key(BB, config_key, level, verbose):
	spc = '\t' * level
	keys = {}
	if BB in BBDependency:
		for (dBB, edge) in BBDependency[BB]:
			for key in print_key_read(dBB, config_key, level, verbose):
				if key not in keys:
					keys[key] = set()
				keys[key].add((dBB, dBB, edge))
			if dBB in References:
				if verbose:
					print (spc + '\t', get_name_for_BB(dBB), file = sys.stderr)
				for rBB in References[dBB]:
					for key in print_key_read(rBB, config_key, level + 1, verbose):
						if key not in keys:
							keys[key] = set()
						keys[key].add((dBB, rBB, edge))
	return keys

def find_callpath_ex(funcName, path, allpaths, verbose, visited):
	if PathCount and (len(allpaths) >= PathCount):
		return
	#print spc + 'find_callpath_ex:', funcName
	if (not funcName in visited) and (funcName in RCalls):
		visited.add(funcName)
		for call in RCalls[funcName]:
			if (not call in path):
				path.append(call)
				find_callpath_ex(get_name_for_func(BBrefFunc[call]), path, allpaths, verbose, visited)	
				path.pop(-1)
	else:
		if IgnoreEntryFunc or funcName == EntryFunc:
			allpaths.append(copy.deepcopy(path))
			idx = len(allpaths)
			if verbose:
				print_path(sys.stderr, '##' + str(idx), path, 0)
				print ("Path", idx, '-', len(path), 'levels', file = sys.stderr)
		else:
			if verbose:
				print_path(sys.stderr, '', path, 0)
				print (len(path), 'levels', file = sys.stderr)

def find_callpath(BB, funcName, allpaths, verbose=False): 
	path = []
	if BB:
		path.append(BB)
	visited = set()
	find_callpath_ex(funcName, path, allpaths, verbose, visited)
	if verbose:
		print ('Total', len(allpaths), 'call paths.')
	print ('Total', len(allpaths), 'call paths.', file = sys.stderr)
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
		print ('Maximum levels:', maxlength, file = sys.stderr)
		print ('Minimum levels:', minlength, file = sys.stderr)
		print ('Average levels:', 1.0 * totlength / len(allpaths), file = sys.stderr)


def check_callpath(index, path, dependentpaths, verbose):
	level = 0
	for call in path:
		spc = '\t' * level
		callee = get_name_for_func(BBrefFunc[call])
		if verbose:
			print (spc, level, get_name_for_BB(call), callee, file = sys.stderr)
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
				print (spc, 'option:', key, file = sys.stderr)
			break
		level += 1

def check_all_callpath(allpaths, dependentpaths, verbose):
	idx = 0
	for path in allpaths:
		check_callpath(idx, path, dependentpaths, verbose)
		idx += 1

def check_combined_callpath(allpaths, dependentpaths, verbose):
	sets = []
	for path in allpaths:
		sets.append(set(path))
	intersect = set.intersection(*sets)
	check_callpath(0, intersect, dependentpaths, True)

def is_func_return_pointer(protoType):
	#parts = protoType.split('(')
	#ret_type = parts[0]
	#if ret_type[-1] == '*':
	#	return True
	#else:
	#	return False
	i = protoType.rfind('(')
	if i > 0:
		if protoType[i - 1] == '*':
			return True
	return False

def add_lines_info(func_name, line_count, start_line, path_name, proto_type):
	if not proto_type in ProtoTypes:
		ProtoTypes[proto_type] = set()
	ProtoTypes[proto_type].add(func_name)
	if is_func_return_pointer(proto_type):
		print(func_name, 'returns a pointer', file=sys.stderr)
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
	print ('FunctionLines', func_name, line_count, start_line, returnLine, path_name, proto_type, file = sys.stderr)
	FunctionLines[func_name] = [int(line_count), int(start_line), returnLine, path_name, proto_type, None]

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
			add_lines_info(func_name, line_count, start_line, path_name, proto_type)
			files.add(path_name)
			if func_name in ReachableFuncs:
				totLines += int(line_count)
		elif line.find('Analyzed') == 0:
			pass
		else:
			print ('Warning: invalid line', line_id, 'in', filename)
	file.close()
	print ('Total', len(files), 'files')
	return totLines

def load_nameList(filename):
	file = open(filename, 'r')
	NameList = []
	for line in file:
		NameList.append(line.strip())
	file.close()
	print ('Load', len(NameList), 'setting names from', filename)
	return NameList

def location_to_BB(location):
	parts = location.split(':')
	if len(parts) == 2:
		pathName = parts[0]
		line = parts[1]
		try:
			print ('location_to_BB', os.path.dirname(pathName), os.path.basename(pathName))
			fileID = Files[(os.path.dirname(pathName), os.path.basename(pathName))]
			BB = Lines[(fileID, line)]
		except KeyError as err:
			BB = None
			print ('Unable to find', location)
		return BB
	else:
		return None

# impact analysis
def remove_disabled_Calls(BBs, remainingCalls):
	for BB in BBs:
		if BB in Callees:
			print ('\t', get_name_for_BB(BB), 'Calls', Callees[BB], file = sys.stderr)
			callee = Callees[BB]
			if callee in remainingCalls:
				if BB in remainingCalls[callee]:
					remainingCalls[callee].remove(BB)

def count_disabled_lines_for_BBs(BBs, length, remainingCalls, disabledCallees):
	disabledLines = length
	print ('\tdisabled', disabledLines, 'lines', file = sys.stderr)
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
				print ('\tdisabled', Lines, 'lines from function', callee, file = sys.stderr)
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
	print ('count_disabled_lines_for_CB', get_name_for_BB(branch), 'edge', edge, file = sys.stderr)
	disabledLines = count_disabled_lines_for_BBs(ControlBBs[branch][edge], len(ControlBBs[branch][edge]), remainingCalls, disabledCallees)
	print ('disabled', disabledLines, 'Lines', file = sys.stderr)
	return disabledLines

def count_disabled_lines_for_func(func_name, remainingCalls, disabledCallees):
	print ('count_disabled_lines_for_func', func_name, file = sys.stderr)
	disabledLines = count_disabled_lines_for_BBs(Calls[func_name], FunctionLines[func_name][0], remainingCalls, disabledCallees)
	disabledCallees.append(func_name)
	print ('disabled', disabledLines, 'Lines', file = sys.stderr)
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
	print ('Totally disabled', disabledLines, 'Lines', str(disabledLines*1.0/TotLines) + '%')
	print ('Totally disabled', len(disabledCallees), 'Functions', str(len(disabledCallees)*1.0/len(ReachableFuncs)) + '%')

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
	print ('Number of direct callers:', len(caller_names))
	print ('Direct callers of', func_name, file = sys.stderr)
	for caller in caller_names:
		print ('\t', caller, file = sys.stderr)
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
	print ('Number of all callers:', len(all_caller_names))
	print ('All callers of', func_name, file = sys.stderr)
	for caller in all_caller_names:
		print ('\t', caller, file = sys.stderr)
	callee_names = getCallees(func_name)
	print ('Number of direct Callees:', len(callee_names))
	print ('Direct Callees of', func_name, file = sys.stderr)
	for callee in callee_names:
		print ('\t', callee, file = sys.stderr)
	print ('Non Module Calls:', non_module_Calls)
	print ('Module Calls:', module_Calls)
	print ()

def count_disabled_lines_file(filename):
	print ('count_disabled_lines_file', filename, file = sys.stderr)
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
			print ('vulnerability name:', vulnerability_name)
		elif line.find('function=') == 0:
			line = line[9:]
			func_name = line
			print ('function name:', func_name)
		elif line.find('CP=') == 0:
			line = line[3:]
			parts = line.split(' ')
			Location = parts[0]
			taken_edge = parts[1]
			branch = location_to_BB(Location)
			if branch:
				CPs.append((branch, taken_edge))
				print ('cp:', get_name_for_BB(branch), taken_edge)
		elif line.find('FP=') == 0:
			line = line[3:]
			parts = line.split(' ')
			FP = parts[0]
			module = parts[1]
			print ('fp:', FP, module)
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
							print ('\tcp:', callee_name)
							CPs.append((callee_name, -1))
							fp_cp_count += 1
			print (fp_cp_count, 'CPs for FP')
			if not callee_name:
				print ('Error:', FP, 'has no Callees')
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
			print ('*', key, file )
			count_ConfigKeys += 1
		else:
			print (' ', key, file )
	file.close()
	print ('7. Config keys:', count_ConfigKeys)
	print ('8. Config control keys:', len(countControlKeys))
	print ()

	#print len(Functions), "Functions:"
	#for function in Functions:
	#	print function, Functions[function]
	file = open(InputFile + '.BBread', 'w')
	print ("BBread:", file )
	for BB in BBread:
		print (get_name_for_BB(BB), file )
		for key in BBread[BB]:
			print ('\t', key, file)
	file.close()

	file = open(InputFile + '.BBDependency', 'w')
	print ("BBDependency:", file)
	for BB in BBDependency:
		print (get_name_for_BB(BB), file)
		for dBB in BBDependency[BB]:
			print ( '\t', get_name_for_BB(dBB), file)
	file.close()
	
	file = open(InputFile + '.Calls', 'w')
	print ("RCalls:", file)
	for func in RCalls:
		print (func, file)
		for call in RCalls[func]:
			print ('\t', call, get_name_for_BB(call), file)
	file.close()
	
	print ()
	print ('Control_BBs:')
	for dominateBB in ControlBBs:
		print (get_name_for_BB(dominateBB))
		for edge in ControlBBs[dominateBB]:
			print ('\tedge:', edge)
			for BB in ControlBBs[dominateBB][edge]:
				print ('\t\t', get_name_for_BB(BB))

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

def find_return_value(lineNo, line):
	retVal = None
	tokens = line.split()
	foundReturn = False
	for idx in range(len(tokens)):
		if tokens[idx] == 'return':
			foundReturn = True
			print('\tFound return at line', lineNo, file=sys.stderr)
			break
	if foundReturn:
		retVal = tokens[idx + 1]
		if retVal == ';':
			retVal = None
			print('\t\treturn statement has no return value', file=sys.stderr)
		else:
			if retVal == '(':
				idx += 1
				retVal = tokens[idx + 1]
			if retVal[0] == '(':
				retVal = retVal[1:]
			if retVal[-1] == ';':
				retVal = retVal[:-1]
				print('\t\treturn value', retVal, file=sys.stderr)
			elif tokens[idx + 2] == ';':
				print('\t\treturn value', retVal, file=sys.stderr)
			else:
				retVal = None
				print('\t\tError: return statement does not end with semi-colon', file=sys.stderr)
	else:
		print('\t\tError: no return statement is found at line', lineNo, file=sys.stderr)
	return retVal

def	identify_const_macro(func, BB, ret_value):
	print('identify_const_macro', func, file=sys.stderr)
	global ConstMacros, FunctionLines
	fileName = FunctionLines[func][3]
	lineNo = int(BBref[BB][1])
	if not FunctionLines[func][5]:
		FunctionLines[func][5] = get_file_lines(fileName)
	lines = FunctionLines[func][5]
	if not lines:
		print("\tError: can't read", fileName, 'for function', func, file=sys.stderr)
		return
	if lineNo >= len(lines):
		print('\tError: line number', lineNo, 'for function', func, 'does not exist in', fileName, file=sys.stderr)
		return
	retVal = find_return_value(lineNo, lines[lineNo - 1])
	if retVal and (retVal[0] not in '0123456789'):
		print("\tIdentified macro", retVal, "as", ret_value, file=sys.stderr)
		print('\tline', lineNo, 'for function', func, 'in file', fileName, file=sys.stderr)
		ConstMacros[retVal] = ret_value
	else:
		print("\tError: can't find return at", lineNo, "in", fileName, file=sys.stderr)

def find_error_return_for_func(func):
	print ('find_error_return_for_func', func, file = sys.stderr)
	# ignore workaround that would cause app to exit
	if func == EntryFunc:
		return None
	#if func in ErrorReturns:
	#	print >>sys.stderr, '\t', func, 'has an error return', ErrorReturns[func]
	#	return get_error_return(func)
	earliestReturn = None
	if func in Calls:
		earliestLine = sys.maxsize
		for call in Calls[func]:
			print ('\t', get_name_for_BB(call), Callees[call], 'logging:', isLoggingFunc(Callees[call]), 'before ret:', call in BBFollowByReturn, file = sys.stderr)
			if (isLoggingFunc(Callees[call])) and (call in BBFollowByReturn):
				BB = BBFollowByReturn[call][0]
				line = int(BBref[BB][1])
				ret_value = BBFollowByReturn[call][1]
				if line > 0 and line < earliestLine:
					earliestLine = line
					earliestReturn = call
					FunctionLines[func][2] = -earliestLine
					print ('\t', 'updated earliestReturn', earliestReturn, file = sys.stderr)
				add_error_return(1, func, BB, ret_value)
				identify_const_macro(func, BB, ret_value)
	else:
		print ('\t', func, 'has no callees', file = sys.stderr)
	if earliestReturn:
		print ('\t', func, 'has an error return', get_name_for_BB(earliestReturn), file = sys.stderr)
	else:
		print ('\t', func, 'has no error return', file = sys.stderr)
	return earliestReturn

def find_error_return_for_func_old(func):
	print ('find_error_return_for_func', func, file = sys.stderr)
	earliestReturn = None
	if func in Calls:
		for call in Calls[func]:
			funcID = BBrefFunc[call]
			break
		earliestLine = 1000000
		if funcID in FuncControlBBs:
			for (branch, edge) in FuncControlBBs[funcID]:
				print (get_name_for_BB(branch), edge, ':')
				for stmt in ControlBBs[branch][edge]:
					print ('\t', stmt, get_name_for_BB(stmt), stmt in Callees, stmt in BBFollowByReturn)
					if stmt in Callees:
						line = int(BBref[stmt][1])
						print ('\t', 'checking call to', Callees[stmt], 'at line', line, file = sys.stderr)
						isErrorReturn = False
						if (isLoggingFunc(Callees[stmt])):
							if (stmt in BBFollowByReturn):
								print ('\t', BBref[stmt])
								isErrorReturn = True
								line = BBFollowByReturn[stmt][0]
								
								print ('\t', 'followed by return at', line, file = sys.stderr)
							else:
								print ('\t', 'line', line, 'is not followed by return', file = sys.stderr)
						if isErrorReturn:
							if line > 0 and line < earliestLine:
								earliestLine = line
								earliestReturn = stmt
								FunctionLines[func][2] = earliestLine
		else:
			print (func, 'has no conditional branches')
	else:
		print (func, 'has no callees')
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
		print (spc, level, "get_locations_to_add_sec_setting2", func, len(funcsToDisable), file = sys.stderr)
	#if FunctionLines[func][2]:
	if func in ErrorReturns:
		funcsToDisable.add(func)
		if InteractiveMode:
			print (spc, level, func, len(funcsToDisable), 'can be protected directly', file = sys.stderr)
		return True
	#if func in FunctionSimplePath:
	#	funcsToDisable.add(func)
	#	if InteractiveMode:
	#		print >> sys.stderr, spc, level, func, len(funcsToDisable), 'can be protected directly'
	#	return True
	callers = getCallers(func)
	if not len(callers):
		if InteractiveMode:
			print (spc, level, func, 'cannot be protected', file = sys.stderr)
		return False
	callerProtected = False
	for caller in callers:
		if not caller in visited:
			visited.add(caller)
			if not get_locations_to_add_sec_setting2(caller, funcsToDisable, visited, level + 1):
				if InteractiveMode:
					print (spc, level, func, len(funcsToDisable), 'cannot be protected', file = sys.stderr)
				return False
			else:
				callerProtected = True
		elif InteractiveMode:
			print (spc, level, caller, "already visited", file = sys.stderr)
	if InteractiveMode:
		if callerProtected:
			print (spc, level, func, len(funcsToDisable), 'can be protected', file = sys.stderr)
		else:
			print ( spc, level, func, len(funcsToDisable), 'cannot be protected', file = sys.stderr)
	return callerProtected

def get_locations_to_add_sec_setting3(func, funcsToDisable):
	print ("get_locations_to_add_sec_setting3", func, file = sys.stderr)
	visited = set()
	if not func in FunctionLines:
		print (func, 'is not analyzed')
		return
	if not get_locations_to_add_sec_setting2(func, funcsToDisable, visited, 0):
		funcsToDisable.clear()

def get_locations_to_add_sec_setting(func):
	print ('Checking', func)
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
			print ('allCalls has', len(allCalls), 'calls')
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
		print (func, 'has no callers!')
	return locations

def print_dependency_groups(BB):
	idx = 0
	for group in convert_dependency_to_cnf(BBDependency[BB]):
		print ('group', idxi)
		for path in group:
			print ('\t', get_name_for_BB(path[0]), path[1])
		idx += 1

def print_branches(branches):
	for dBB in sorted(branches.keys(), cmp=lambda x, y: get_name_for_BB(x) < get_name_for_BB(y)):
		print ('\t', get_name_for_BB(dBB))
		for edge in branches[dBB]:
			print ('\t\t', edge)

def get_dependency_branches_for_BB(BB):
	branches = {}
	for (dBB, edge) in BBDependency[BB]:
		if not dBB in branches:
			branches[dBB] = set()
		branches[dBB].add(edge)
	return branches

def menu():
	print ('1. Find call paths to a function.')
	print ('2. Find call paths to a line.')
	print ('3. Find callee of a function.')
	print ('4. Find caller of a function.')
	print ('5. Find dependency of a line.')
	print ('6. Find support of a line.')
	print ('7. Find diversion of a line.')
	print ('8. Add security setting for a function.')
	print ('9. Find error return for a function.')
	print ('10. Add security setting for all functions.')
	print ('11. Find workaround for a function.')
	print ('0. Exit.')
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
			print ('Function:', func_name)
			find_callpath(BB, func_name, allpaths, True)
		elif ans == '3':
			func_name = raw_input('Enter function name: ')
			if func_name in Calls:
				print ('Callees of', func_name, file = sys.stderr)
				for call in Calls[func_name]:
					print (call, get_name_for_BB(call), Callees[call], file = sys.stderr)
				print ('Total', len(Calls[func_name]), 'calls.')
			else:
				print (func_name, 'does not have any callee.')
		elif ans == '4':
			func_name = raw_input('Enter function name: ')
			if func_name in RCalls:
				callers = set()
				callers2 = set()
				print ('Callers of', func_name, file = sys.stderr)
				for call in RCalls[func_name]:
					caller = get_name_for_func(BBrefFunc[call])
					callers.add(caller)
					if call in BBFollowByReturn:
						callers2.add(caller)
						flag = '*'
					else:
						flag = '!'
					print (get_name_for_BB(call), caller, flag, file = sys.stderr)
				print ('Total', len(RCalls[func_name]), 'calls.')
				print ('Total', len(callers), 'callers.')
				print ('Total', len(callers2), 'callers with calls followed by return.')
			else:
				print (func_name, 'does not have any caller.')
		elif ans == '5':
			location = raw_input('Enter a location: ')
			BB = location_to_BB(location)
			if BB:
				if BB in BBDependency:
					print ('This location is satisfied by the following predicates')
					#branches = get_dependency_branches_for_BB(BB)
					#print_branches(branches)
					print_dependency_groups(BB)
				else:
					print ('This location has no dependency.')
			else:
				print ('Invalid location.')
		elif ans == '6':
			location = raw_input('Enter a location: ')
			BB = location_to_BB(location)
			if BB:
				if BB in ControlBBs:
					print ('This location has the following supports.')
					for edge in ControlBBs[BB]:
						print ('Edge:', edge)
						for sBB in ControlBBs[BB][edge]:
							print ('\t', get_name_for_BB(sBB))
				else:
					print ('This location has no support.')
			else:
				print ('Invalid location.')
		elif ans == '7':
			location = raw_input('Enter a location: ')
			BB = location_to_BB(location)
			if BB:
				find_diversion_for_BB(BB)
			else:
				print ('Invalid location.')
		elif ans == '8':
			funcName = raw_input('Enter a function name: ')
			#for (branch, edge) in get_locations_to_add_sec_setting(funcName):
			#	print '*', get_name_for_BB(branch), edge
			funcsToDisable = set()
			get_locations_to_add_sec_setting3(funcName, funcsToDisable)
			for func in funcsToDisable:
				print (func, FunctionLines[func][1:]) 
		elif ans == '9':
			funcName = raw_input('Enter a function name: ')
			if funcName in FunctionLines:
				BB = find_error_return_for_func(funcName)
				if BB:
					print (get_name_for_BB(BB))
				else:
					print ('No error return for', funcName)
			else:
				print (funcName, 'is not analyzed')
		elif ans == '10':
			start_time = time.time()
			print ('Running 10@', start_time, file = sys.stderr)
			countProtectableFuncs = 0
			protectableFuncs = set()
			totLocations = 0
			minLocations = 1000000
			maxLocations = 0
			countProtectableLines = 0
			for funcName in ReachableFuncs:
				if funcName in FunctionLines: 
					if not isLoggingFunc(funcName):
						print ('Checking', funcName, file = sys.stderr)
						locations = get_locations_to_add_sec_setting(funcName)
						if len(locations) > 0:
							countProtectableFuncs += 1
							protectableFuncs.add(funcName)
							print ('*', funcName, len(locations), file = sys.stderr)
							for (branch, edge) in locations:
								print ('\t', get_name_for_BB(branch), edge, file = sys.stderr)
							countLocations = len(locations)
							if countLocations < minLocations:
								minLocations = countLocations
							if countLocations > maxLocations:
								maxLocations = countLocations
							totLocations += countLocations
							countProtectableLines += FunctionLines[funcName][0]
						else:
							print ( '!', funcName, file = sys.stderr)
					else:
						print ('Skipping logging function', funcName, file = sys.stderr)
				else:
					print ('Skipping external function', funcName, file = sys.stderr)
			print ('Total', countProtectableFuncs, 'of', TotFuncs, 'reachable functions can be protected.')
			print ('Total', countProtectableLines, 'of', TotLines, 'lines can be protected.')
			if countProtectableFuncs:
				print ('Min #locations for protection:', minLocations)
				print ('Max #locations for protection:', maxLocations)
				print ('Avg #locations for protection:', totLocations / countProtectableFuncs)
			end_time = time.time()
			print ('Finish 10@', end_time, 'total', end_time - start_time, 'seconds', file = sys.stderr)
		elif ans == '11':
			func_name = raw_input('Enter function name: ')
			find_workaround(func_name, True)
		else:
			print ('Invalid choice.')
	exit()

def find_workaround(location, verbose):
	print ('find_workaround', location, file = sys.stderr)
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
			print (pathName, '=>', fileID, BB, file = sys.stderr)
			print ('Control dependency of', get_name_for_BB(BB), functionName, file = sys.stderr)
			paths = []
			find_callpath(BB, functionName, allpaths, verbose)
			print ()
		except KeyError as err:
			print ('Unable to find', location)
			print ('Try to rerun dependency.py with function name')
			exit()
	else:
		functionName = location
		print ('Control dependency of', functionName, file = sys.stderr)
		if functionName in FunctionLocation:
			find_callpath(None, functionName, allpaths, verbose)
		else:
			print ('Function', functionName, 'is undefined', file = sys.stderr)
			return ret

	if verbose:
		print (file = sys.stderr)
		if PathCount:
			print ('Total', len(allpaths), 'paths - limited to', PathCount, file = sys.stderr)
		else:
			print ('Total', len(allpaths), 'paths', file = sys.stderr)

	#check_all_callpath(allpaths, dependentpaths, verbose)
	check_combined_callpath(allpaths, dependentpaths, verbose)
	if verbose:
		print (file = sys.stderr)
	CPs = {}
	workaround_keys = {}
	if verbose:
		print ('Dependent paths:', file = sys.stderr)
	multiKeyPath = []
	for path in dependentpaths:
		if len(dependentpaths[path]) > 1:
			multiKeyPath.append(path)
	for path in multiKeyPath:
		del dependentpaths[path]
	for path in dependentpaths:
		if verbose:
			print ('Path', path, file = sys.stderr)
		for key in dependentpaths[path]:
			if verbose:
				print (key, file = sys.stderr)
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
					print (edge, get_name_for_BB(branch), file = sys.stderr)
				else:
					print (edge, get_name_for_BB(branch), '->', get_name_for_BB(reference), file = sys.stderr)
	print ('Total', len(dependentpaths), 'dependent paths', file = sys.stderr)
	#if len(dependentpaths) == len(allpaths):
	#	print >>sys.stderr, 'All', len(allpaths), 'paths are dependent.'
	#	ret = True
	# we need just one dependentpath since we use check_combined_callpath
	if len(dependentpaths):
		print ('All', len(allpaths), 'paths are dependent.', file = sys.stderr)
		ret = True
	if ret:
		print (file = sys.stderr)
		print ('Control Points:', file = sys.stderr)
		for key in workaround_keys:
			BBs = AllKeys[key]
			for BB in workaround_keys[key].intersection(AllKeys[key]):
				if BB in ControlBBs:
					print (key, ': ', get_name_for_BB(BB), file = sys.stderr)
		for key in CPs:
			for (branch, edge) in CPs[key]:
				print (key, get_name_for_BB(branch), edge, file = sys.stderr)
			#count_disabled_lines(CPs[key])
	print (file = sys.stderr)
	return ret

def find_workaround_all(verbose):
	count_func_has_workaround = 0
	funcHasWorkaround = []
	for func in FunctionLines:
		if func in ReachableFuncs:
			if find_workaround(func, verbose):
				count_func_has_workaround += 1
				funcHasWorkaround.append(func)
	print (count_func_has_workaround, 'functions has existing workaround')
	return funcHasWorkaround

def find_error_return_for_func_all():
	funcs = []
	for func in FunctionLines:
	#	if func in ReachableFuncs:
	#		if find_error_return_for_func(func):
	#			funcs.append(func)
		if find_error_return_for_func(func):
			funcs.append(func)
	print (len(funcs), 'functions has error return')
	return funcs

def direct_error_propagation():
	newchange = True
	working_set = set(ErrorReturns)
	count_direct_error_propagation = 0
	while newchange:
		newchange = False
		new_set = []
		for func in working_set:
			#print('checking propagation for', func)
			if func in RetCalls:
				#print(func, 'has return calls')
				for (caller, call) in RetCalls[func]:
					if caller in ReachableFuncs:
						if not caller in ErrorReturns:
							copy_error_return(func, caller)
							FunctionLines[caller][2] = -int(BBref[call][1], 0)
							newchange = True
							new_set.append(caller)
							count_direct_error_propagation += 1
							print (caller, 'has propagated error return from', get_name_for_BB(call), file = sys.stderr)
		working_set = new_set
	print (count_direct_error_propagation, 'functions has directly propagated error return')
	return count_direct_error_propagation

def indirect_error_propagation():
	print ('indirect_error_propagation', file = sys.stderr)
	count_indirect_error_propagation = 0
	#print >>sys.stderr, ConstReturns
	#prt_cond_checks()
	print ('ConstReturns:', file = sys.stderr)
	for func in ConstReturns:
		if not func in FunctionLines:
			continue
		if not func in ReachableFuncs:
			continue
		print ('\t', func, file = sys.stderr)
		for BB in ConstReturns[func]:
			ret_val = ConstReturns[func][BB][0]
			print ('\t\t', get_name_for_BB(BB), ret_val, file = sys.stderr)
			done = False
			if BB in BBDependency:
				# use only the most related dependency
				dBB, edge = BBDependency[BB][-1]
				print ('\t\t\t', get_name_for_BB(dBB), 'edge:', edge, 'dBB:', dBB, file = sys.stderr)
				if (dBB, edge) in CondChecks:
					print('\t\t\t', CondChecks[(dBB, edge)], file = sys.stderr)
					for (pred, funcName, rhs) in CondChecks[(dBB, edge)]:
						print ('\t\t\t\t', pred, funcName, rhs, file = sys.stderr)	
						if funcName in ErrorReturns:
							if is_ret_value_satisfy_pred(funcName, pred, rhs):
								if not func in ErrorReturns:
									if ret_val != '' and ret_val != 'None':
										print ('\t\t\t\t', 'adding', ret_val, 'as error return value for', func, file = sys.stderr)
										#print ('\t', 'adding', ret_val, 'as error return value for', func)
										add_error_return(11, func, BB, ret_val)
										count_indirect_error_propagation += 1
										done = True
										break
				if done:
					break
	print (count_indirect_error_propagation, 'functions has indirectly propagated error return')
	return count_indirect_error_propagation

def reverse_error_propagation():
	print ('reverse_error_propagation', file = sys.stderr)
	countReverseErrorPropagation = 0
	#print >>sys.stderr, ConstReturns
	#prt_cond_checks()
	print ('ErrorReturns:', file = sys.stderr)
	new_errors = []
	for func in ErrorReturns:
		if not func in FunctionLines:
			continue
		if not func in ReachableFuncs:
			continue
		print ('\t', func, file = sys.stderr)
		for kind in ErrorReturns[func]:
			for (BB, ret_val) in ErrorReturns[func][kind]:
				if BB:
					print ('\t\t', get_name_for_BB(BB), ret_val, file = sys.stderr)
					if BB in BBDependency:
						# use only the most related dependency
						dBB, edge = BBDependency[BB][-1]
						print ('\t\t\t', get_name_for_BB(dBB), edge, dBB, file = sys.stderr)
						if (dBB, edge) in CondChecks:
							for (pred, funcName, rhs) in CondChecks[(dBB, edge)]:
								print ('\t\t\t\t', pred, funcName, rhs, file = sys.stderr)		
								ret_val = get_ret_value_to_satisfy_pred(pred, rhs)
								if ret_val:
									print ('\t\t\t\t', 'adding', ret_val, 'as error return value for', funcName, file = sys.stderr)
									new_errors.append((kind, funcName, None, ret_val))
	for kind, funcName, BB, ret_val in new_errors:
		if not funcName in ErrorReturns:
			countReverseErrorPropagation += 1
		add_error_return(kind, funcName, None, ret_val)

	print (countReverseErrorPropagation, 'functions has been reversely propagated error return')
	return countReverseErrorPropagation

def apply_file_change(filename, newfilename, logfilename):
	backupfilename = filename + '.orig'
	if not os.path.exists(backupfilename):
		os.rename(filename, backupfilename)
	os.rename(newfilename, filename)
	log = open(logfilename, 'a')
	print (backupfilename, filename, file = log)
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
	print ('int FPSW_flags[' + str(len(ProtectedFuncNumber)) + '];\n', file = output)
	print ( get_loader_data('FPSW_flags_names', ProtectedFuncNumber, 'FPSW_entry', entryFunc), file = output)
	code = get_loader_code(loaderFile)
	for line in code:
		print (line.strip('\n'), file = output)
	for line in input:
		line = line.strip('\n')
		print (line, file = output)
	output.close()
	input.close()
	apply_file_change(filename, outfilename, logfilename)

def add_loader_code(loaderFile, logfilename):
	for funcName in FunctionLines:
		if (funcName.find('main_') == 0) or (funcName == EntryFunc):
			print ('Adding loader to', funcName, file = sys.stderr)
			add_loader_code_to_entry(funcName, loaderFile, logfilename)

def add_exec_loader_code_to_entry(entryFunc, loaderFile, logfilename):
	filename = FunctionLines[entryFunc][3]
	outfilename = filename + '.protected'
	input = open(filename, 'r')
	output = open(outfilename, 'w')
	print ('int EXEC_flags[' + str(len(ExecFuncNumber)) + '];\n', file = output)
	print (get_loader_data('EXEC_flags_names', ExecFuncNumber, 'EXEC_entry', entryFunc), file = output)
	code = get_loader_code(loaderFile)
	for line in code:
		print (line.strip('\n'), file = output)
	for line in input:
		line = line.strip('\n')
		print (line, file = output)
	output.close()
	input.close()
	apply_file_change(filename, outfilename, logfilename)

def add_exec_loader_code(loaderFile, logfilename):
	for funcName in FunctionLines:
		if (funcName.find('main_') == 0) or (funcName == EntryFunc):
			print ( 'Adding exec loader to', funcName, file = sys.stderr)
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
	ret = get_error_return_value(func)
	if ret != "None":
		return 'if (' + cond + ') {\n' + '\tFPSW_log("' + func + '");\n' + '\treturn ' + str(ret) + ';\n' + '}\n'
	else:
		return 'if (' + cond + ') {\n' + '\tFPSW_log("' + func + '");\n' + '\treturn;\n' + '}\n'

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

def get_func_start_line(filename, func, startLine, lines):
	print ('get_func_start_line', filename, func, startLine, file = sys.stderr)
	if startLine >= len(lines):
		print ('\tInvalid start_line, file has', len(lines), 'lines', file = sys.stderr)
		#raise IOError
		return
	print ('\t', lines[startLine - 1], file = sys.stderr)
	# only do this if the startLine does not contain the function name
	if lines[startLine - 1].find(get_orig_func_name(func)) < 0:
		# ensure we are at the beginning of a function
		curLine = startLine
		while curLine > 0:
			print ('line- ', curLine, lines[curLine - 1], file = sys.stderr)
			if is_func_def(curLine, lines):
				if lines[curLine - 1].find(get_orig_func_name(func)) < 0:
					print ('\tIn wrong location?', file = sys.stderr)
					print ('\t\t', lines[curLine - 1], file = sys.stderr)
					return 0;
				else:
					break
			curLine -= 1
		startLine = curLine

	origStartLine = startLine
	while startLine < len(lines):
		line = lines[startLine - 1].strip()
		print ('line+ ', startLine, line, file = sys.stderr)
		if line and line[-1] == '{':
			print (func, startLine, file = sys.stderr)
			return startLine + 1
		elif line and line[-1] == ';':
			return startLine
		startLine += 1
	print ('Unable to find start line for', func, '@', origStartLine, file = sys.stderr)
	return origStartLine
		
def get_call_checks(lines, line1, line2):
	check = "// FPSW: patched call checks\n"
	for line in range(line1, line2 + 1):
		check += lines[line - 1]
	return check.strip()

def get_file_lines(filename):
	try:
		input = open(filename, 'r', encoding = "ISO-8859-1") #Edited by Xiaowei Yu
		lines = input.readlines()
		input.close()
		return lines
	except TypeError:
		print ('File', filename, 'cannot be openned!') 
		return []
	except IOError:
		print ('File', filename, 'cannot be openned!' )
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
		print ("File", backupfilename, "already exists!")
		return -1

	input = open(filename, 'r')
	output = open(outfilename, 'w')
	line_no = 0
	for line in input:
		line = line.strip('\n')
		line_no += 1
		if line_no in locations:
			print (locations[line_no], file = output)
		print (line, file = output)
	output.close()
	input.close()
	old_lines = sum(1 for line in open(filename))
	new_lines = sum(1 for line in open(outfilename))
	apply_file_change(filename, outfilename, logfilename)
	print ('Added', new_lines - old_lines, 'lines to', filename, file = sys.stderr)
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
		print ('Adding EXEC for', func, '@', start_line, 'of', filename, file = sys.stderr)

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
		print (filename, line, ':', file = sys.stderr)
		print ('\t', locations[line], file = sys.stderr)

	return insert_code(filename, locations, logfilename)

def lines_of_file(filename):
	return len(get_file_lines(filename))

def identify_protectable_funcs(funcs, secCP, protFuncs):
	count_disabled_by_callers = 0
	for func in funcs:
		#print >> sys.stderr, '\t', func
		funcsToDisable = set()
		get_locations_to_add_sec_setting3(func, funcsToDisable)
		if len(funcsToDisable):
			if func not in protFuncs:
				protFuncs[func] = []
			for secFunc in funcsToDisable:
				if not secFunc in secCP:
					secCP[secFunc] = []
				secCP[secFunc].append(func)
				protFuncs[func].append(secFunc)
			#for f in funcsToDisable:
			#	print >> sys.stderr, '\t\t', f
			if not func in funcsToDisable:
				count_disabled_by_callers += 1
	return count_disabled_by_callers

def output_SWRRs(protFuncs, files):
	global InputFile
	print('Writing to SWRRs...')
	SWRRFilename = os.path.splitext(os.path.basename(InputFile))[0] + '.SWRRs'
	#for name in files:
	outp = open(SWRRFilename, 'w')
	for func in protFuncs:
		print (func,end = ' ', file = outp)
		for secFunc in protFuncs[func]:
			#Edit by Xiaowei Yu
			ret_value = get_error_return_value(secFunc)
			if ret_value != 'NULL':
				ret_value = int(ret_value)
				if ret_value < 0:
					ret_value = (2<<15)+ret_value
			if secFunc in FuncReturnLine:
				print (secFunc, str(ret_value) + '(' + FuncReturnLine[secFunc] + ')', file = outp)
			else:
				print (secFunc, ret_value, file = outp)
		print (file = outp)
	outp.close()
	# output to the .SWRRs for the main file only
	#break

def print_protected_funcs(title, protFuncs, secCP):
	print (len(protFuncs), title)
	print (len(protFuncs), title, file = sys.stderr)
	total_protected_lines = 0
	for func in protFuncs:
		if func in ErrorReturns:
			kind, ret = get_error_return(func)
			if ret[0]:
				print ('\t*', func, kind, get_name_for_BB(ret[0]), ret[1], file = sys.stderr)
			else:
				print ('\t*', func, kind, None, ret[1], file = sys.stderr)
			all_rets = get_all_error_return(func)
			print ('====================================', file = sys.stderr)
			for kind in all_rets:
				for BB, ret in all_rets[kind]:
					if BB:
						print ('\t\t', kind, get_name_for_BB(BB), ret, file = sys.stderr)
					else:
						print ('\t\t', kind, None, ret, file = sys.stderr)
		else:
			print ('\t*', func, 'is protected by caller', file = sys.stderr)
			ProtectedByCaller.append(get_setting_name_ex(func))
		total_protected_lines += FunctionLines[func][0]
	print (total_protected_lines, 'lines can be protected.')
	print (len(secCP), 'functions need to be modified.')

def add_sec_settings_all(logfilename, settingsfile, checkOnly=False):
	print ("Analyzed reachable functions:", file = sys.stderr)
	secCP = {}
	protFuncs = {}
	files = {}
	count_disabled_by_callers = identify_protectable_funcs(set().union(FunctionLines).intersection(ReachableFuncs), secCP, protFuncs)
	print_protected_funcs('functions can be protected.', protFuncs, secCP)

	secCP2 = {}
	protFuncs2 = {}
	identify_protectable_funcs(set().union(FunctionLines).difference(protFuncs), secCP2, protFuncs2)
	print_protected_funcs('additional functions can be protected.', protFuncs2, secCP2)

	#print >> sys.stderr, "Protected functions:"
	#for func in protFuncs:
	#	print >> sys.stderr, '\t', func
	print ("Modified functions:", file = sys.stderr)
	for func in secCP:
		print ('\t', func, file = sys.stderr)
	#print "FunctionLines:"
	#print FunctionLines
	#print "ReachableFuncs:"
	#for f in sorted(ReachableFuncs):
	#	print '\t', f
	patchChecks = {}
	print ("Patched functions:", file = sys.stderr)
	print ('Counting files and lines of code:', file = sys.stderr)
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
				print (count, filename, file = sys.stderr)
	if len(allfiles) == 0:
		print ('No protectable function is reachable!', file = sys.stderr)
		return ([], 0, 0)
	print (len(allfiles), 'files.')
	print (count_all_lines, 'lines of code.')
	for func in secCP:
		filename = FunctionLines[func][3]
		if not filename in files:
			files[filename] = []
			patchChecks[filename] = []
		files[filename].append(func)
		if func in UncheckedCalls:
			print ('\t', "call to", func, file = sys.stderr)
			for caller in UncheckedCalls[func]:
				print ('\t\t', caller, file = sys.stderr)
				filename = FunctionLines[caller][3]
				if not filename in files:
					files[filename] = []
					patchChecks[filename] = []
				patchChecks[filename].append(UncheckedCalls[func][caller])
	print (len(files), 'of' , len(allfiles), 'files', '(', len(files) * 100.0 / len(allfiles), '% )', 'need to be modified.')
	if checkOnly:
		output_SWRRs(protFuncs, files)
		return (protFuncs, 0, count_disabled_by_callers)
	count_lines = 0

	# ensure EntryFile is on the list
	entryFile = FunctionLines[EntryFunc][3]
	if not entryFile in files:
		files[entryFile] = []
	files[entryFile].append(EntryFunc)

	for filename in files:
		count_lines += add_sec_settings_to_file(filename, files[filename], secCP, patchChecks[filename], logfilename)
	print (count_lines, 'of', count_all_lines, 'lines of code', count_lines * 100.0 / count_all_lines, '%)', 'need to be added.')
	output = open(settingsfile, 'w')
	for setting in ProtectedName:
		print (setting, file = output)
	output.close()
	add_loader_code('Talos_loader.c', logfilename)
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
	add_exec_loader_code('Talos_exec.c', logfilename)

def remove_sec_settings_all(logfilename):
	input = open(logfilename, 'r')
	for line in input:
		line = line.strip()
		if not line:
			continue
		parts = line.split(' ')
		print ('ren', parts[0], parts[1])
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
		print ( '......', func, file = sys.stderr)
		for BB, ret in NullReturns[func]:
			startLine, endLine, var = ret.split(',')
			retLines = strip_lines(allLines[int(startLine) - 1 : int(endLine)])
			if first:
				print ('.........', startLine, endLine, lines, retLines, file = sys.stderr)
				lines = retLines
				first = False
			else:
				print ('.........', startLine, endLine, lines, retLines, file = sys.stderr)
				lines = find_common_code(lines, retLines)
	return lines

def generalize_return_NULL():
	#countFuncMulNullReturn = 0
	for func in NullReturns:
		#if len(NullReturns[func]) > 1:
		#	countFuncMulNullReturn += 1
		#	continue
		prototype = FunctionLines[func][4]
		print ('...', prototype, file = sys.stderr)
		if not prototype in NullReturnPrototype:
			NullReturnPrototype[prototype] = []
			NullReturnPrototype[prototype].append([func])
			NullReturnPrototype[prototype].append(find_return_NULL(func))
		else:
			NullReturnPrototype[prototype][0].append(func)
			NullReturnPrototype[prototype][1] = find_common_code(NullReturnPrototype[prototype][1], find_return_NULL(func))
	print ("return NULL for prototypes:", file = sys.stderr)
	for prototype in NullReturnPrototype:
		print ('\t', prototype, NullReturnPrototype[prototype], file = sys.stderr)
		if prototype in ProtoTypes:
			for func in ProtoTypes[prototype]:
				if func in NullReturnPrototype[prototype][0]:
					continue
				if (getCallers(func) == getCallers(NullReturnPrototype[prototype][0][0])):
					print ('\t\t', func, file = sys.stderr)

def prt_func_list(desc, funcList):
	print (desc, file = sys.stderr)
	print ('========================================', file = sys.stderr)
	for func in funcList:
		print ('\t', func, file = sys.stderr)
	print ('========================================', file = sys.stderr)

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
	print ('CondChecks:', file = sys.stderr)
	for (BB, edge) in CondChecks:
		print (get_name_for_BB(BB), edge, BB, file = sys.stderr)
		for (pred, lhs, rhs) in CondChecks[(BB, edge)]:
			print ('\t', pred, lhs, rhs, file = sys.stderr)
	print (file = sys.stderr)

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
			print (val, '(', val * 100.0 / tot, ')', desc)
			numbers.append(round(val * 100.0 / tot, 1))
	output = ''
	for number in numbers:
		if output:
			output += ' & ' + str(number) + '\%'
		else:
			output += str(number) + '\%'
	print ('#', output)
	
def load_API_errors(APIErrorSpec):
	inp = open(APIErrorSpec, 'r')
	print('load_API_errors', APIErrorSpec, file=sys.stderr)
	while True:
		line = inp.readline()
		if not line:
			break
		if line[0] == '#':
			continue
		line = line.strip()
		parts = line.split()
		if parts[1] == 'NULL':
			add_error_return(3, parts[0], None, parts[1])
		else:
			add_error_return(0, parts[0], None, int(parts[1], 0))
	inp.close()

# main function
start_time = time.time()

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
# FunctionLines[func_name] = [line_count, start_line, returnLine, path_name, proto_type, lines]
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
ErrorReturnPriority = [0, 1, 2, 3, 4, 5, 10, 11]
ProtectedFuncNumber = {}
ProtectedFuncRef = {}
ProtectedByCaller = []
ExecFuncNumber = {}
ConstMacros = {}

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
parser.add_argument('-w', dest='IdentifyWorkarounds', help='Identify Existing Workarounds', action='store_true')
parser.add_argument('-O', dest='SettingsFile', help='Filename of security settings', nargs=1)
parser.add_argument('-K', dest='CheckOnly', help='Do not apply security settings', action='store_true')
parser.add_argument('-G', dest='AddExecLog', help='Add execution logging', nargs=1)
parser.add_argument('-F', dest='ConfigFile', help='Filename of configuration file', nargs=1, required=True)
parser.add_argument('-a', dest='APIErrorSpec', help='Filename of API error specification', nargs=1)
args = vars(parser.parse_args(sys.argv[1:]))
if args['APIErrorSpec']:
	APIErrorSpec = args['APIErrorSpec'][0]
else:
	APIErrorSpec = None
if args['AddSecuritySetting']:
	AddSecuritySetting = args['AddSecuritySetting'][0]
else:
	AddSecuritySetting = None
if args['SettingsFile']:
	SettingsFile = args['SettingsFile'][0]
else:
	SettingsFile = None
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
Debug = args['Debug']
InteractiveMode = args['InteractiveMode']
Verbose = args['Verbose']
IgnoreEntryFunc = args['IgnoreEntryFunc']
IdentifyWorkarounds = args['IdentifyWorkarounds']
CheckOnly = args['CheckOnly']
CfgFile = args['ConfigFile'][0]

if APIErrorSpec:
	load_API_errors(APIErrorSpec)

if InteractiveMode and (AddSecuritySetting or DelSecuritySetting):
	print ("InteractiveMode, AddSecuritySetting, DelSecuritySetting cannot be used together")
	exit()
if AddSecuritySetting and DelSecuritySetting:
	print ("AddSecuritySetting and DelSecuritySetting cannot be used together")
	exit()

if DelSecuritySetting:
	remove_sec_settings_all(DelSecuritySetting)
	exit()

print ('InputFile:', InputFile)
print ('Location:', Location)
print ('NamePattern:', NamePattern)
print ('Debug:', Debug)
print ('PathCount:', PathCount)
if NameListFile:
	NameList = load_nameList(NameListFile)
else:
	NameList = None
print ('EntryFunc:', EntryFunc)
print ('CPFile:', CPFile)


# Read API rules from configuration file analyzer.cfg
#load_cfg(os.path.join(os.path.split(sys.argv[0])[0], 'analyzer.cfg'))
load_cfg(CfgFile)

#input = open(InputFile, 'r')
#inputlines = input.readlines()
#input.close()
FuncReturnLine = {}

pass1(InputFile) # identify API wrappers
inputlines = None # release memory
pass2(InputFile)
#pass3(InputFile)
#pass4(InputFile)
ReachableFuncs = []
ReachableCalls = set()
print ('build_call_graph...')
build_call_graph(EntryFunc)
for func in Functions:
	print ('Find reachable from', func[2], file = sys.stderr)
	if func != EntryFunc:
		build_call_graph(func[2])
print ('Reachable Functions:', file = sys.stderr)
for func in ReachableFuncs:
	print ('\t', func, file = sys.stderr)
#print 'remove_unreachable_calls...'
#remove_unreachable_calls()

print ('build_BB_key_dependency...')
build_BB_key_dependency()
file = open(InputFile + '.BBKeyDependency', 'w')
oldstdout = sys.stdout
sys.stdout = file
countConfigDependentLines = 0
countControlKeys = set()
print ("Total", len(BBKeyDependency), "dependent Lines")
for BB in BBKeyDependency:
	print (get_name_for_BB(BB))
	keys = find_dependent_key(BB, True, 0, Verbose)
	if len(keys) > 0:
		countControlKeys = countControlKeys.union(keys.keys())
		print (keys)
		countConfigDependentLines += 1
print ('Total', countConfigDependentLines, 'config dependent Lines')
print ('Total', len(countControlKeys), 'config dependency keys')
for key in countControlKeys:
	print ('\t', key)
file.close()
sys.stdout = oldstdout

linesFilename = os.path.splitext(os.path.basename(InputFile))[0] + '.lines'
if os.path.exists(linesFilename):
	load_lines_file(linesFilename)
#else:
    #print('Error:', linesFilename, 'does not exist!', file=sys.stderr)
    #print('Error:', linesFilename, 'does not exist!')
    #if (input('Continue (y/n) ?') == 'n'):
    #    sys.exit()
    #sys.exit()
TotLines = 0
for func in FunctionLines:
	TotLines += FunctionLines[func][0]

print ('identify error returns...')
TotFuncRetError = find_error_return_for_func_all()
print ('propagate error returns...')
count_error_propagation = 0
while True:
	old_count = count_error_propagation
	count_error_propagation += direct_error_propagation()
	count_error_propagation += indirect_error_propagation()
	count_error_propagation += reverse_error_propagation()
	if count_error_propagation == old_count:
		break

print ('All Functions:', len(Functions))
print ('Reachable Functions:', len(ReachableFuncs))
#prioritize_heuristics()
TotFuncs = []
TotFuncRetPointer = []
for func in ReachableFuncs:
	if func in FunctionLines:
		TotFuncs.append(func)
		if func in FuncRetPointer:
			TotFuncRetPointer.append(func)

print ('Reachable Lines:', TotLines)
print ('Functions that return pointer:', len(TotFuncRetPointer))
prt_func_list('Functions that return pointer:', TotFuncRetPointer)
print ('Functions that return pointer, has no error return, but whose return value is checked:', file = sys.stderr)
for func in TotFuncRetPointer:
	if not func in ErrorReturns:
		if func in RetCheckedFunc:
			print ('\t', func, file = sys.stderr)
			add_error_return(4, func, None, 'NULL')
print ('Pointer-returnning functions that cannot be protected:', file = sys.stderr)
countPointerFuncNoProt = 0
for func in TotFuncRetPointer:
	if not func in ErrorReturns:
		print ('\t', func, file = sys.stderr)
		countPointerFuncNoProt += 1
if len(TotFuncRetPointer):
	print (countPointerFuncNoProt * 100.0 / len(TotFuncRetPointer), '% of all pointer-returning functions', file = sys.stderr)

generalize_return_NULL()

TotDirectProtFuncs = set(ErrorReturns).intersection(ReachableFuncs).intersection(FunctionLines)
print ('Directly protectable functions:', len(TotDirectProtFuncs))
statProtFuncs = {}
for kind in ErrorReturnPriority:
	statProtFuncs[kind] = 0
for func in TotDirectProtFuncs:
	kind, errRet = get_error_return(func)
	if kind == 3 or kind == 4 or kind == 5:
		print(func, 'returns a pointer', kind, file=sys.stderr)
	statProtFuncs[kind] += 1
print (statProtFuncs)

#print >>sys.stderr, len(FuncSimplePath), 'functions with simple path that is dependent on check of non-local var:'
#for func in FuncSimplePath:
#	print >>sys.stderr, '\t', func

if Verbose:
	print_totals()

print ('Analyzed Reachable Functions:', len(TotFuncs))

if IdentifyWorkarounds:
	print ('identify existing workarounds...')
	funcsHasWorkaround = find_workaround_all(Verbose)
	print (len(funcsHasWorkaround) * 100.0 / len(TotFuncs), 'precent of functions')

if InteractiveMode:
	interact()

if Location:
	find_workaround(Location)

#print 'keys:'
#for key in keys:
#	print '\t', key
#print '\t\tcall chain:'
#for call in paths:
#	print '\t\t\t', get_name_for_BB(call)
if CPFile:
	count_disabled_lines_file(CPFile)

if AddSecuritySetting:
	all_prot_funcs = set()
	all_prot_funcs = all_prot_funcs.union(ErrorReturns)
	#all_prot_funcs = all_prot_funcs.union(FuncSimplePath)
	#all_prot_funcs = all_prot_funcs.union(FuncRetPointer)
	count_disabled_by_callers = 0
	(protFuncs, count, count_disabled_by_callers) = add_sec_settings_all(AddSecuritySetting, SettingsFile, CheckOnly)
	print ('# Number of "protectable" functions:', len(protFuncs))
	all_prot_funcs = all_prot_funcs.union(protFuncs)

	#propProtFuncs = propagate_protectable_functions(all_prot_funcs)
	#all_prot_funcs = all_prot_funcs.union(propProtFuncs)
	all_prot_funcs = all_prot_funcs.intersection(FunctionLines)
	all_prot_funcs = all_prot_funcs.intersection(ReachableFuncs)
	print ('# Number of defined functions:', len(TotFuncs))
	print ('# Defined functions', '(', len(TotFuncs), ')', file = sys.stderr)
	#print (TotFuncs, file = sys.stderr)
	if len(TotFuncs):
		print ('# All protectable functions:', len(all_prot_funcs), '(', len(all_prot_funcs) * 100.0 / len(TotFuncs), ')')
		print ('Indirectly protected functions:', count_disabled_by_callers, '(', count_disabled_by_callers * 100.0 / len(TotFuncs), ')')
	else:
		print ('All protectable funcions:', len(all_prot_funcs))
		print ('Indirectly protected functions:', count_disabled_by_callers)
	#prt_func_list('All protectable funcions:', all_prot_funcs)
	count_not_protected_funcs = 0
	print ("Functions that can not be protected:", file = sys.stderr)
	all_funcs = set()
	all_funcs = all_funcs.union(ReachableFuncs)
	all_funcs = all_funcs.intersection(FunctionLines)
	for func in all_funcs:
		if not func in all_prot_funcs:
			count_not_protected_funcs += 1
			ret_type = FunctionLines[func][4].split('(')[0]
			print ('\t', FunctionLines[func][0], ret_type, func, FunctionLines[func][3], file = sys.stderr)
	print (count_not_protected_funcs, "functions.", file = sys.stderr)
	#all_funcs = set()
	#all_funcs = all_funcs.union(TotFuncs)
	#all_funcs = all_funcs.union(all_prot_funcs)
	#print 'Total funcions:', len(all_funcs)
	# estimate the lines of code that needs to be added
	#lines_to_add = (len(all_prot_funcs) - count_disabled_by_callers) * 3 + count_disabled_by_callers * 2
	#print lines_to_add, 'lines of code need to be added.'
	#parms = [[len(TotFuncs), [['Protectable functions:', len(TotDirectProtFuncs) + count_disabled_by_callers]]], [len(TotFuncs), [['\t2 - Functions with simple path:', statProtFuncs[2]], ['\t0 & 1 - Functions with error path:', statProtFuncs[0] + statProtFuncs[1]], ['\t3 & 4 & 5 - Functions that return pointer:', statProtFuncs[3] + statProtFuncs[4] + statProtFuncs[5]], ['\t10 & 11 - Functions that have propagated error return:', statProtFuncs[10] + statProtFuncs[11]], ['\tFunctions that are protected by callers:', count_disabled_by_callers]]]]
	# Removed simple path
	parms = [[len(TotFuncs), [['Protectable functions:', len(TotDirectProtFuncs) + count_disabled_by_callers]]], [len(TotFuncs), [['\t0 & 1 - Functions with error path:', statProtFuncs[0] + statProtFuncs[1]], ['\t3 & 4 & 5 - Functions that return pointer:', statProtFuncs[3] + statProtFuncs[4] + statProtFuncs[5]], ['\t10 & 11 - Functions that have propagated error return:', statProtFuncs[10] + statProtFuncs[11]], ['\tFunctions that are protected by callers:', count_disabled_by_callers]]]]
	if len(TotFuncs):
		prt_percentage(parms)
	print ("ID of each protected functions:", file = sys.stderr)
	for FPSW in ProtectedFuncNumber:
		ID = ProtectedFuncNumber[FPSW]
		funcName = ProtectedFuncRef[ID]
		if not FPSW in ProtectedByCaller:
			print ('\t', FPSW, ID, get_error_return(funcName)[0], funcName, file = sys.stderr)
		else:
			print ('\t', FPSW, ID, 100, funcName, file = sys.stderr)

if AddExecLog:
	add_exec_log_code_all(AddExecLog)

end_time = time.time()
print ('Analyze time:', end_time - start_time)

