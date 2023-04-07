OCAMLC=ocamlfind ocamlc -package graphics,lablgtk2,cairo2,cairo2-gtk -linkpkg -thread
OCAMLOPT=ocamlfind ocamlopt -package graphics,lablgtk2,cairo2,cairo2-gtk -linkpkg -thread -p -g

OBJECTS=utils.cmo algebra.cmo gtktools.cmo symbolic.cmo r
SOURCES=utils.ml algebra.ml gtktools.ml symbolic.ml 


.SUFFIXES: .ml .mli .cmi .cmo .pdf

%.cmi: %.mli
	$(OCAMLC) -c $(INCLUDES) $<

%.cmo: %.ml 
	$(OCAMLC) -c $(INCLUDES) $<

%.cmx: %.ml 
	$(OCAMLOPT) -c $(INCLUDES) $<

all: gravity

symbolic.cmo: symbolic.ml utils.ml
symbolic.cmx: symbolic.ml utils.ml
gtktools.cmo: gtktools.ml utils.ml
gtktools.cmx: gtktools.ml utils.ml
algebra.cmo: algebra.ml utils.ml
algebra.cmx: algebra.ml utils.ml
gravity.cmo: gravity.ml utils.ml symbolic.ml algebra.ml gtktools.ml
gravity.cmx: gravity.ml utils.ml symbolic.ml algebra.ml gtktools.ml

gravity: utils.cmo algebra.cmo symbolic.cmo gtktools.cmo gravity.cmo
	$(OCAMLC) -o gravity utils.cmo algebra.cmo symbolic.cmo gtktools.cmo gravity.cmo

gravityo: utils.cmx algebra.cmx symbolic.cmx gtktools.cmx gravity.cmx
	$(OCAMLOPT) -o gravity utils.cmx algebra.cmx symbolic.cmx gtktools.cmx gravity.cmx

clean:
	  rm -f *.cm[iox] *.[oa] *~ gravity.opt gravity

run: 
	sleep 1 && ./gravity 2 0.002 0.0001
