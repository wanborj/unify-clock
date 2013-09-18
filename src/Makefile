FILES=Common.v
FILES+=SingleNode.v
FILES+=ClockUnify.v ClockUnifyProof.v ClockUnifyImpl.v
FILES+=Decidable.v
FILES+=Examples.v

COQC=coqc
COQDEP=coqdep -I .
COQDOC=coqdoc
COQCHK=coqchk --output-context
OCB=ocamlbuild

all:
	@$(MAKE) depend
	@$(MAKE) proof
	@$(MAKE) doc

test: Results.ml Results.mli Printer.ml
	@$(OCB) Printer.byte
	./Printer.byte

depend: $(FILES)
	@echo "COQDEP"
	@$(COQDEP) $^ > .depend

proof: $(FILES:.v=.vo)

clean:
	rm -f .depend
	rm -f *.vo *.glob
	rm -f doc/*.html doc/coqdoc.css
	rm -f Printer.byte Results.ml Results.mli
	rm -rf _build

.SUFFIXES: .v .vo

.v.vo:
	@echo "COQC $*.v"
	@$(COQC) $*.v

-include .depend

.PHONY: all depend proof doc clean chk test

doc: $(FILES:.v=.vo)
	@echo "COQDOC"
	@$(COQDOC) -toc --html -l -d doc --no-index --coqlib http://coq.inria.fr/library/ $(FILES)
	@cp doc/style/coqdoc.css doc/coqdoc.css

chk: $(FILES:.v=.vo)
	@$(COQCHK) $(FILES:.v=)
