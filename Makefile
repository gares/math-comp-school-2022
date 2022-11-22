COQC=eval $$(opam env); coqc
MC=

VS=$(filter-out %tmp.v,$(filter-out %-todo.v,$(wildcard *.v)))
EX=$(filter-out %tmp.v,$(filter-out %-todo.v,$(wildcard exercise*.v)))
FILES=$(VS:%.v=%.html) $(VS) $(EX:%.v=%-todo.v) $(EX:%.v=%-solution.html) demo-support-master.png

OPAMROOT=$(shell pwd)/opam
export OPAMROOT

all: cheat-sheet/cheatsheet.pdf $(FILES)

udoc:
	git clone https://github.com/ejgallego/udoc.git
	cd udoc && touch dune-workspace
	cd udoc && make

cheat-sheet/cheatsheet.pdf: cheat-sheet/cheatsheet.tex
	make -C cheat-sheet

check-ocaml-ver-%:
	@ V=`(echo -n '2 '; ocamlc -version; echo -n '1 '; echo $*) \
	  | sed 's/\./ /g' \
	  | sort -n -k 4 -k 3 -k 2 -k 1 | head -n 1 | cut -d ' ' -f 1`; \
	if `test $$V = 2`; then echo "OCaml must be >= $*"; false; fi

upload: $(FILES) cheat-sheet/cheatsheet.pdf
	scp $(FILES) FileSaver.js Blob.js local.css cheat-sheet/cheatsheet.pdf roquableu.inria.fr:/net/serveurs/www-sop/teams/marelle/MC-2022/

%.html.tmp: %.v Makefile udoc $(OPAMROOT)
	$(COQC) -w -notation-overridden,-undo-batch-mode $< > /dev/null
	./udoc/_build/install/default/bin/udoc -t $* $< --with-header header.html --with-footer footer.html -o $@
	@sed -ix -e 's?<textarea?<textarea class="coq-code"?' $@
	@sed -ix -e 's?^ *<h1>$*tmp</h1>??' $@
	@sed -ix -e 's?^ *<title.*?<title>$*</title>?' $@
	@sed -ix -e 's?^ *<h1>$*</h1>??' $@
	@sed -ix -e 's?jscoq-agent.js?jscoq-loader.js?' $@
	@sed -ix -e 's?</head>?<link rel="stylesheet" href="local.css" /></head>?' $@
	@sed -ix -e 's?</title>?</title><script src="Blob.js" type="text/javascript"></script>?' $@
	@sed -ix -e 's?</title>?</title><script src="FileSaver.js" type="text/javascript"></script>?' $@

validate: $(VS) $(EX) test.v
	for x in $^; do $(COQC) $$x || exit 1; done

$(OPAMROOT):
	(opam init --bare -n -j8;\
	  opam switch create mc2022 4.09.1 -y;\
	  opam repo add coq https://coq.inria.fr/opam/released;\
	  opam repo add overlay file://$$PWD/opam-overlay;\
	  opam update;\
	  opam install coq-mathcomp-algebra-tactics.hierarchy-builder coq-mathcomp-field -y;\
	  (opam install coqide -y || true))\
	|| (rm -rf $(OPAMROOT); exit 1)
# .PHONY: $(OPAMROOT)

# Lessons
lesson%.html: lesson%.html.tmp
	@mv $< $@

# test
test.html: test.html.tmp
	@mv $< $@
	
# Exercises
exercise%.html: exercise%.html.tmp
	@sed -e '/^(\*D\*).*$$/d' -e 's/^(\*A\*).*$$/Admitted./' -e 's/^(\*a\*).*$$/  admit./'  $< > $@
exercise%-solution.html: exercise%.html.tmp
	@cp $< $@
exercise%-todo.v: exercise%.v
	@sed -e '/^(\*D\*).*$$/d' -e 's/^(\*A\*).*$$/Admitted./' -e 's/^(\*a\*).*$$/  admit./'  $< > $@
