default: all
all:     tangrams

CMOS    = numbers.cmo region.cmo geometry.cmo game.cmo
GLFLAGS = -I $(shell ocamlfind query lablgl 2> /dev/null               \
                 || (ocamlfind query lablGL | sed 's/lablgl/lablGL/g') \
              ) lablglut.cma lablgl.cma

clean:
	rm -f *.cmo *.cmi tangrams gltest

top: $(CMOS)
	rlwrap ocaml nums.cma $^

tangrams: $(CMOS) ui.cmo main.ml
	ocamlc -o $@ $(GLFLAGS) nums.cma $^

gltest: gltest.ml
	ocamlc -o gltest $(GLFLAGS) $^

numbers.cmo:  numbers.ml
region.cmo:   numbers.cmo region.mli region.ml
geometry.cmo: numbers.cmo region.cmo geometry.mli geometry.ml
game.cmo:     numbers.cmo region.cmo geometry.cmo game.mli game.ml
ui.cmo:       numbers.cmo region.cmo geometry.cmo game.cmo ui.ml

%.cmo:
	ocamlc -c -o $@ $(GLFLAGS) nums.cma $^

.phony: default all clean top

