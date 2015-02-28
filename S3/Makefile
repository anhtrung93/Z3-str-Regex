default: all

# -------------------------------------------------------------------
# Change the path to Z3 4.1.1 accordingly
# The directory indicated by this path should contain "lib" and "bin"
# e.g. "/home/z3_src_4.1.1"
#      "/home/work/tool/z3/z3_src_4.1.1"
# -------------------------------------------------------------------
Z3_path = /home/lumtics/Z3-str-Regex/z3

JUNK = S3
SOURCE = strTheory.cpp testMain.cpp
INCLUDE = $(Z3_path)/lib
LIB = $(Z3_path)/bin/external

all: $(SOURCE)
	g++-4.9 -std=c++14 -O3 -fopenmp -static -I$(INCLUDE) -L$(LIB) $(SOURCE) -lz3 -lrt -o S3 -Wall
	@echo ""
	
clean:
	rm -f $(JUNK)
