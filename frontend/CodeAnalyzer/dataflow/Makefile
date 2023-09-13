INSTALLDIR = ~/code/llvm/Debug+Asserts/lib
INSTALLDIR2 = ~/code/llvm/Debug+Asserts/lib

libdataflow.a: dataflow.o reachacc.o bitvector.o reachdef.o
	ar r libdataflow.a dataflow.o reachacc.o bitvector.o reachdef.o
	#cp libdataflow.a $(INSTALLDIR)/
	#cp libdataflow.a $(INSTALLDIR2)/

dataflow.o: dataflow.cc
	g++ -c -g -fPIC dataflow.cc

reachacc.o: reachacc.cc
	g++ -c -g -fPIC reachacc.cc

reachdef.o: reachdef.cc
	g++ -c -g -fPIC reachdef.cc

bitvector.o: bitvector.cc
	g++ -c -g -fPIC bitvector.cc

clean:
	rm *.a *.o

install:
	cp libdataflow.a $(INSTALLDIR)/
	cp libdataflow.a $(INSTALLDIR2)/
