
# The library requires the caml-shift library, delimcc.cma and the
# correspondent .mli files. See caml-shift.tar.gz.
# Please adjust DELIMCC= below to point to the library.
#
# The typical command to use the OCaml top-level:
# $ ocaml -I ../../Continuations/caml-shift/ \
# ../../Continuations/caml-shift/delimcc.cma
# and then do #load "prob.cma";;

# $Id$

HANSEI=$(HOME)/src/okmij/hansei
INCLUDES=-I $(HANSEI)
OCAMLC=ocamlc -g
OCAML=rlwrap ocaml
OCAMLOPT=ocamlopt

.SUFFIXES: .ml .mli .cmi .cmo

%.cmi: %.mli
	$(OCAMLC) -c $(INCLUDES) $<

%.cmo: %.ml 
	$(OCAMLC) -c $(INCLUDES) $<

hansei:
	$(OCAML) $(INCLUDES) delimcc.cma prob.cma

