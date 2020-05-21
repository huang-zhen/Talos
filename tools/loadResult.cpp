#include <iostream>
#include <fstream>
#include <string>
#include <vector>
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

bool loadControlDependency(const char *infile, const string& module, const string& function) {
	ifstream ifs;
	ifs.open(infile);
	if (ifs.is_open()) {
		string line;
		while (getline(ifs, line)) {
			vector<string> tokens;
			splitStr(line, '@', tokens);
			//for (unsigned i = 0; i < tokens.size(); i++)
			//	cout << i << ':' << tokens[i] << '\n';
			const string& mod = tokens[0];
			string& func = tokens[4];
			if (func.find("main_") == 0)
				func = "main";
			const string& accessType = tokens[9];
			const string& callType = tokens[10];
			//cout << mod << '@' << func << '@' << accessType << '@' << callType << '\n';
			//if (mod == module && func == function && accessType == "-2" && callType == "3") {
			if ((mod == module) && (func == function) && (accessType == "-2") && (callType == "3")) {
				const string& line = tokens[3];
				const string& dep = tokens[6];
				cout << line << "<-" << dep << '\n';
			}
		}
		ifs.close();
	} else
		cerr << "Error: unable to open " << infile << '\n';
}

int main(int argc, const char *argv[]) {
	if (argc < 4) {
		cerr << "Usage: " << argv[0] << " module function analyzer.out\n";
		exit(0);
	}
	const char *infile = argv[1];
	const char *module = argv[2];
	const char *function = argv[3];
	loadControlDependency(infile, module, function);
	return 0;
}
