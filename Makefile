COQMODULE    := SimComp
COQTHEORIES  := $(shell find . -not -path "./deprecated/*" -not -path "./_opam/*" -iname '*.v')

.PHONY: all proof proof-quick graph

all:
	$(MAKE) proof

graph:
		sh make_graph.sh

### Quick
# proof-quick: Makefile.coq $(COQTHEORIES)
# 	$(MAKE) -f Makefile.coq quick

proof-quick: Makefile.coq $(COQTHEORIES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vio,$(COQTHEORIES))

proof: Makefile.coq $(COQTHEORIES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(COQTHEORIES))

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R lib $(COQMODULE)"; \
         echo "-R ems $(COQMODULE)"; \
         echo "-R spc $(COQMODULE)"; \
         echo "-R proofmode $(COQMODULE)"; \
         echo "-R imp $(COQMODULE)"; \
         echo "-R mem $(COQMODULE)"; \
         echo "-R examples $(COQMODULE)"; \
         echo "-R extract $(COQMODULE)"; \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	$(MAKE) -f Makefile.coq clean || true
	find . -name "*.vio" -type f -delete -not -path "./_opam/*"
	find . -name "*.v.d" -type f -delete -not -path "./_opam/*"
	find . -name "*.vo" -type f -delete -not -path "./_opam/*"
	find . -name "*.vok" -type f -delete -not -path "./_opam/*"
	find . -name "*.vos" -type f -delete -not -path "./_opam/*"
	find . -name "*.glob" -type f -delete -not -path "./_opam/*"
	git clean -Xf .
	rm -f _CoqProject Makefile.coq Makefile.coq.conf #Makefile.coq-rsync Makefile.coq-rsync.conf


### copied from iris-examples by YJ
# Install build-dependencies
OPAMFILES=$(wildcard *.opam)
BUILDDEPFILES=$(addsuffix -builddep.opam, $(addprefix builddep/,$(basename $(OPAMFILES))))

builddep/%-builddep.opam: %.opam Makefile
	@echo "# Creating builddep package for $<."
	@mkdir -p builddep
	@sed <$< -E 's/^(build|install|remove):.*/\1: []/; s/"(.*)"(.*= *version.*)$$/"\1-builddep"\2/;' >$@

builddep-opamfiles: $(BUILDDEPFILES)
.PHONY: builddep-opamfiles

builddep: builddep-opamfiles
	@# We want opam to not just install the build-deps now, but to also keep satisfying these
	@# constraints.  Otherwise, `opam upgrade` may well update some packages to versions
	@# that are incompatible with our build requirements.
	@# To achieve this, we create a fake opam package that has our build-dependencies as
	@# dependencies, but does not actually install anything itself.
	@echo "# Installing builddep packages."
	@opam install $(OPAMFLAGS) $(BUILDDEPFILES)
.PHONY: builddep
