
# The library requires the delimcc package 
#
# The typical command to use the OCaml top-level:
# $ ocaml 

# $Id$

HANSEI=okmij/hansei
INCLUDES=
OCAMLC=ocamlfind ocamlc -g -package batteries,delimcc -linkpkg
OCAMLOPT=ocamlfind ocamlopt -g -package batteries,delimcc -linkpkg
OCAMLDOC=ocamlfind ocamldoc -g -package batteries,delimcc -linkpkg
OCAML=rlwrap ocaml
OCAML_HANSEI=rlwrap -s 5000 -H .hansei_history ocaml
OCAML_PROB=rlwrap -s 5000 -H .ocaml_history ocaml

OBJECTS=utils.cmo dist.cmo lazydata.cmo monads.cmo treemonads.cmo monadreps.cmo store.cmo prob.cmo inference3.cmo notes.cmo inference2.cmo probimps.cmo inferenceF.cmo grammar.cmo inference1.cmo inference2H.cmo monadst.cmo
SOURCES=utils.ml dist.ml lazydata.ml monads.ml treemonads.ml monadreps.ml store.ml prob.ml inference3.ml notes.ml inference2.ml probimps.ml inferenceF.ml grammar.ml inference1.ml monadst.ml


.SUFFIXES: .ml .mli .cmi .cmo .pdf

%.cmi: %.ml
	$(OCAMLC) -c $(INCLUDES) $<

%.cmo: %.ml 
	$(OCAMLC) -c $(INCLUDES) $<

%.pdf: %.ml 
	a2ps -Eocaml -g -o $*.ps $*.ml
	ps2pdf -sPAPERSIZE=a4 $*.ps
	rm $*.ps


utils.cmo: utils.ml
dist.cmo: dist.ml utils.cmi
lazydata.cmo: lazydata.ml utils.cmi dist.cmi
monads.cmo: monads.ml utils.cmi dist.cmi
monadst.cmo: monadst.ml utils.cmi monads.cmi store.cmi
treemonads.cmo: treemonads.ml monads.cmi lazydata.cmi utils.cmi dist.cmi
monadreps.cmo: monadreps.ml monads.cmi utils.cmi dist.cmi
store.cmo: store.ml utils.cmi
notes.cmo: notes.ml
prob.cmo: prob.ml utils.cmi monads.cmi monadreps.cmi store.cmi dist.cmi

probimps.cmo: probimps.ml prob.cmi utils.cmi monads.cmi store.cmi dist.cmi treemonads.cmi lazydata.cmi
	$(OCAMLC) -c $(INCLUDES) -I $(HANSEI) $<

inference1.cmo: inference1.ml prob.cmi utils.cmi lazydata.cmi monads.cmi dist.cmi store.cmi monadreps.cmi
inference2.cmo: inference2.ml prob.cmi utils.cmi lazydata.cmi monads.cmi dist.cmi store.cmi monadreps.cmi
inference2H.cmo: inference2H.ml utils.cmi lazydata.cmi dist.cmi prob.cmi store.cmi
inference3.cmo: inference3.ml prob.cmi utils.cmi lazydata.cmi monads.cmi dist.cmi store.cmi monadreps.cmi
inference4.cmo: inference4.ml utils.cmi dist.cmi
	$(OCAMLC) -c $(INCLUDES) -I $(HANSEI) $<

inferenceF.cmo: inferenceF.ml prob.cmi utils.cmi lazydata.cmi monads.cmi dist.cmi store.cmi monadreps.cmi
grammar.cmo: grammar.ml utils.cmi prob.cmi monads.cmi monadreps.cmi
johnson.cmo: johnson.ml utils.cmi monads.cmi monadst.cmi store.cmi treemonads.cmi

clean::
	  rm -f *.cm[iox] *.[oa] *~ 

runhans: hanstest
	./hanstest

run: $(OBJECTS)
	$(OCAML_PROB) $(INCLUDES) nums.cma

hanstest: $(OBJECTS) inference2H.cmo inference4.cmo hanstest.ml
	$(OCAMLC) -o hanstest $(INCLUDES) -I $(HANSEI) prob.cma $(OBJECTS) inference4.cmo inference2H.cmo hanstest.ml

delimcc:
	$(OCAML) $(INCLUDES) -I $(HANSEI) pMap.cmo

hansei:
	$(OCAML_HANSEI) $(INCLUDES) -I $(HANSEI) prob.cma nums.cma 

johnson: johnson.ml johnson.cmo dist.cmo dist.cmi
	$(OCAMLC) -o johnson $(OBJECTS) johnson.cmo
