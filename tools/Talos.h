#ifndef TALOS_H
#define TALOS_H
#include <map>
#include <list>
#include <string>
#include <vector>

class Talos {
	public:
		Talos() : maxLine(0) {};
		~Talos() {};
		bool init(const char* infile, const char* module);
		// index 0 refers to the outermost control dependency
		// index -1 refers to the innermost control dependency
		const std::string getControlDep(int line, int id);
		unsigned getControlDepCount(int line);
		int getMaxLine() const;
	private:
		int maxLine;
		std::string mod;
		std::map<int, std::vector<std::string> > controlDep;
		// methods
		void splitStr(const std::string& s, char delimiter, std::vector<std::string>& tokens);
		bool loadControlDependency(const char* infile, const char* module);
};
#endif
