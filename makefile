all: miniml expr evaluation

miniml: miniml.ml
	ocamlbuild -use-ocamlfind miniml.byte

expr: expr.ml
	ocamlbuild -use-ocamlfind expr.byte

evaluation: evaluation.ml
	ocamlbuild -use-ocamlfind evaluation.byte

clean:
	rm -rf _build *.byte