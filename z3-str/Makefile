default: all

# -------------------------------------------------------------------
# Change the path to Z3 4.1.1 accordingly
# The directory indicated by this path should contain "lib" and "bin"
# e.g. "/home/z3_src_4.1.1"
#      "/home/work/tool/z3/z3_src_4.1.1"
# Z3_path = /home/lumtics/Z3-str-Regex/z3
# Boost_path = /home/lumtics/boost_1_57_0
# LIB_BOOST = $(Boost_path)/stage/lib/libboost_regex.a
# -------------------------------------------------------------------
Z3_path = /opt/Workspace/z3-str_ws/z3
Boost_path = /opt/Workspace/boost_1_57_0

JUNK = str
SOURCE = strTheory.cpp regexParser.cpp testMain.cpp
INCLUDE_Z3 = $(Z3_path)/lib
INCLUDE_BOOST = $(Boost_path)
LIB_Z3 = $(Z3_path)/bin/external
LIB_BOOST = $(Boost_path)/lib/libboost_regex.a 

all: $(SOURCE)
	g++ -O3 -fopenmp -g -static -I$(INCLUDE_Z3) -I$(INCLUDE_BOOST) -L$(LIB_Z3) $(SOURCE) -lz3 -lrt -o str -Wall $(LIB_BOOST)
	@echo ""
	
clean:
	rm -f $(JUNK)
