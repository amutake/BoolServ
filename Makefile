boolserv: ml/BoolServ.ml
	ocamlbuild -tag safe_string -package verdi-runtime -I ml -cflag -g boolserv.native

proof: Makefile.coq
	$(MAKE) -f Makefile.coq

ml/BoolServ.ml: proof

Makefile.coq:
	./configure

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
