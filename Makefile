COQMODULE    := SimComp
COQTHEORIES  := $(shell find . -not -path "./deprecated/*" -iname '*.v')

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
         echo "-R . $(COQMODULE)"; \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

clean:
	$(MAKE) -f Makefile.coq clean || true
	find . -name "*.vio" -type f -delete
	find . -name "*.v.d" -type f -delete
	find . -name "*.vo" -type f -delete
	find . -name "*.vok" -type f -delete
	find . -name "*.vos" -type f -delete
	find . -name "*.glob" -type f -delete
	git clean -Xf .
	rm -f _CoqProject Makefile.coq Makefile.coq.conf #Makefile.coq-rsync Makefile.coq-rsync.conf
