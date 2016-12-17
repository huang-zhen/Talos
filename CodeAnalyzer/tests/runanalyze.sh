~/llvm/bin/clang -g -c -emit-llvm main.c
rm /tmp/analyzer.out
~/llvm/bin/opt -load ~/llvm/lib/libAnalyzer.dylib -Analyzer main.bc > main.new.bc
less /tmp/analyzer.out

