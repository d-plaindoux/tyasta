# ---------------------------------------------------
# Your path should access to F and Z3 solver binaries
# ---------------------------------------------------

.SUFFIXES: .fsti .fst .fsti.checked .fst.checked

all: specs impls

clean:
	rm *.checked

specs: utils.fsti.checked \
	   try.fsti.checked \
	   ast.fsti.checked \
	   checker.fsti.checked \
	   eval.fsti.checked

impls: utils.fst.checked \
	   try.fst.checked \
	   checker.fst.checked \
	   eval.fst.checked

.fsti.fsti.checked: 
	fstar.exe $< --cache_checked_modules 

.fst.fst.checked: 
	fstar.exe $< --cache_checked_modules 
