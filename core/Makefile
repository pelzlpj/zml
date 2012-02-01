
SRCS := id.ml type.ml syntax.ml typing_unify.ml typing.ml normal.ml function.ml \
	zasm.ml zapf.ml parser.ml lexer.ml main.ml

OBJS := $(SRCS:.ml=.cmx)

all: zml

zml: $(OBJS)
	ocamlopt -o $@ $(OBJS)

parser.cmx: parser.ml parser.cmi
	ocamlopt -c $<

clean:
	rm -f *.cmi *.cmo *.cmx *.o parser.ml lexer.ml zml

%.cmx : %.ml
	ocamlopt -c $<

%.cmi : %.mli
	ocamlc -c $<

%.ml : %.mly
	ocamlyacc -v $<

%.mli : %.mly
	ocamlyacc -v $<

%.ml : %.mll
	ocamllex $<

