#include <iostream>
#include <string>
#include <cstdlib>

#include "Talos.h"

using namespace std;

int main(int argc, const char *argv[]) {
	if (argc < 3) {
		cerr << "Usage: " << argv[0] << " analyzer.out module\n";
		exit(0);
	}
	const char *infile = argv[1];
	const char *module = argv[2];

	Talos t;
    t.init(infile, module);

    for (int line = 1; line < t.getMaxLine(); line ++) { 
			unsigned count = t.getControlDepCount(line);
			if (count > 0) {
				cout << line << ':';
				for (unsigned i = 0; i < count; i++) {
					std::string dep = t.getControlDep(line, i);
					if (i == 0)
						cout << dep;
					else
						cout << ',' << dep;
				}
				cout << '\n';
			}
	}
	return 0;
}
