# Note: Z3 was built using C++, so libz3.a has C++ dependencies. 
#       You can use gcc to link the program, but you need tell it 
#       to link the C++ libraries
g++ -fopenmp -I../lib -L../bin/external my_theory.cpp -lz3 -lrt -Wall -o my_theory
gcc -fopenmp -I../lib -L../bin/external test_user_theory.c -lz3 -lrt -o test_user_theory
gcc -fopenmp -I../lib -L../bin/external regex_theory.c -lz3 -lrt -o regex_theory
