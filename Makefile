
test: main.native mini-c
	./mini-c --debug test.c

main.native: *.ml*
	ocamlbuild -tag bin_annot $@

mini-c:
	ln -s main.native $@

