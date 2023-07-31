#!/usr/bin/python3
import re, sys

access_types = {'0':'ret', '1':'write', '-1':'call', '-2':'other'}

def get_access_type(value):
	if value in access_types:
		return access_types[value]	
	else:
		return ''

call_types = {'0':'non-API call', '1':'API call', '2':'direct access', '3':'dependency', '4':'FP definition', '5':'FP call', '6':'reference', '7':'return const', '8':'return call', '9':'call without check', '10':'simple path', '11':'return NULL'}

def get_call_type(value):
	#print('get_call_type', value)
	if value.find(',') > 0:
		ret = value.split(',')[0]
	else:
		ret = value	
	if ret in call_types:
		return call_types[ret]
	else:
		return ''

fields={0:'module name', 1:'directory', 2:'filename', 3:'line number', 4:'function name', 5:'basic block', 6: 'dominator basic block', 7:'callee name', 8:'key name', 9:get_access_type, 10:get_call_type}
search = sys.argv[1]
filename = sys.argv[2]
pattern = re.compile(search)
callee = input('Callee: ')
inp = open(filename, 'r')
for line in inp:
	if pattern.findall(line):
		parts = line.split('@')
		if (not callee) or (parts[7] == callee):
			print(line)
			i = 0
			for p in parts:
				if i in fields:
					if isinstance(fields[i], str):
						value = fields[i]
					else:
						value = fields[i](p.strip())
				else:
					value = ''
				print(i, '(' + value +')', p)
				i += 1
			input('Press ENTER to Continue')
inp.close()
