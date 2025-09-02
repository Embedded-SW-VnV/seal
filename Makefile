OCAMLBUILD=ocamlbuild -use-ocamlfind -classic-display -no-links
OCAMLFIND=ocamlfind

seal:
	$(OCAMLBUILD) seal.cma seal.cmxa seal.cmxs

doc: seal
	$(OCAMLBUILD) seal.docdir/index.html

uninstall:
	$(OCAMLFIND) remove seal

install: seal uninstall
	cd _build && $(OCAMLFIND) install seal ../META seal.a seal.cmx seal.cma seal.cmxa seal.cmxs seal.cmi *.mli

clean:
	ocamlbuild -clean
