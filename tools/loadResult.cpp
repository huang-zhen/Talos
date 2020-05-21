#include <iostream>
#include <fstream>
#include <string>
#include <vector>
#include <list>
#include <map>
#include <sstream>
#include <cstdlib>

using namespace std;

void splitStr(const std::string& s, char delimiter, std::vector<std::string>& tokens)
{
   tokens.clear();
   std::string token;
   std::istringstream tokenStream(s);
   while (std::getline(tokenStream, token, delimiter))
   {
      tokens.push_back(token);
   }
}

std::map<int, std::list<std::string> > controlDep;

bool loadControlDependency(const char *infile, const string& module, const string& function) {
	ifstream ifs;
	ifs.open(infile);
	if (ifs.is_open()) {
		string line;
		while (getline(ifs, line)) {
			vector<string> tokens;
			splitStr(line, '@', tokens);
			const string& mod = tokens[0];
			string& func = tokens[4];
			if (func.find("main_") == 0)
				func = "main";
			const string& accessType = tokens[9];
			const string& callType = tokens[10];
			if ((mod == module) && (func == function) && (accessType == "-2") && (callType == "3")) {
				const string& line = tokens[3];
				const string& dep = tokens[6];
				cout << line << "<-" << dep << '\n';
				stringstream ss(line);
				int l;
				ss >> l;
				if (controlDep.find(l) == controlDep.end()) {
					controlDep[l] = list<string>();
					vector<string> depList;
					splitStr(dep, ',', depList);
					for (unsigned i = 0; i < depList.size(); i++)
						controlDep[l].push_front(depList[i]);
				}
			}
		}
		ifs.close();
	} else
		cerr << "Error: unable to open " << infile << '\n';
}

int main(int argc, const char *argv[]) {
	if (argc < 4) {
		cerr << "Usage: " << argv[0] << " analyzer.out module function\n";
		exit(0);
	}
	const char *infile = argv[1];
	const char *module = argv[2];
	const char *function = argv[3];
	loadControlDependency(infile, module, function);
    for (map<int, list<string> >::iterator it = controlDep.begin(); it != controlDep.end(); it++) {
			cout << it->first << ':';
			for (list<string>::iterator iit = it->second.begin(); iit != it->second.end(); iit++) {
				if (iit == it->second.begin())
					cout << *iit;
				else
					cout << ',' << *iit;
			}
			cout << '\n';
	}
	return 0;
}
