Z3-regex is a string theory plug-in built on the powerful Z3 SMT solver (http://z3.codeplex.com/). 
It was built on-top of Z3-str (https://sites.google.com/site/z3strsolver/). In addition to what Z3-str supports, Z3-regex also supports (see our documentation): 
+ Regular expressions 
+ Membership predicates 
+ High-level string operations that work on regular expressions such as Star(), Matches().

INSTALLATION GUIDE:

1. Download   the   source   code   of   Z3   4.1.1   and   Z3-regex   from: (https://github.com/anhtrung93/Z3-str-Regex)
2. In the top level folder of Z3, build Z3
	•autoconf
	•./configure
	•make
	•make a
3. Download Boost C++ Libraries
	•Go to (http://sourceforge.net/projects/boost/files/boost/1.57.0/) and download Boost Libraries
	•Refer to the "Getting Started Guide"(www.boost.org/doc/libs/1_58_0/more/getting_started/unix-variants.html) of Boost to install and build Boost Libraries. Boost is required when Z3-regex parsing the regular expression constraints.
	•Modify variable "Boost_path" in Z3_regex Makefile to indicate the Boost location
4. Build Z3-regex
	•Modify variable "Z3_path" in the Z3-regex Makefile to indicate the Z3 location.
	•make
5. Setup Z3-regex driver script
	•In "Z3-str.py", change the value of the variable "solver" to point to the Z3-str2binary "str" just built.
6. Run Z3-regex
	•Z3-str.py -f <inputFile>
	•e.g:$./Z3-str.py -f testRegex/Z3-regex/regex-01
