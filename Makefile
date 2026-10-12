# Build the Fresco mechanization.
#
#   make coq      full kernel check of every file (the bar for a release)
#   make quick    .vos/.vok mode, skipping opaque proof replay
#   make clean    remove build products
#
# `def_ott.v` and `prop_ln.v` are generated from `fresco/language.ott` by
# Ott and LNgen; the generated files are committed, so neither tool is
# needed for `make coq`.  `make -B ott lngen` regenerates them
# (`make -B LNGEN=<binary> ott lngen` if LNgen is installed elsewhere).

COQ_PROJECT  := _CoqProject
COQ_MAKEFILE := CoqMakefile
NJOBS        ?= 4

OTT_FLAGS := -coq_lngen true -signal_parse_errors true
LNGEN     ?= lngen
SYSTEMS   := fresco

ifeq ($(shell uname -s), Darwin)
	SED_FLAG := -i ""
else
	SED_FLAG := -i
endif

# The extraction driver writes its OCaml here.
EXTRACT_DIR := fresco/ext_algo/extraction/extracted

.PHONY: coq quick clean ott lngen

$(COQ_MAKEFILE): $(COQ_PROJECT) $(shell find . -name '*.v' | sort)
	find . -name '*.v' | sed 's|^\./||' | sort | xargs coq_makefile -o $@ -f $(COQ_PROJECT)

coq: $(COQ_MAKEFILE)
	mkdir -p $(EXTRACT_DIR)
	$(MAKE) -j $(NJOBS) -f $(COQ_MAKEFILE)

quick: $(COQ_MAKEFILE)
	mkdir -p $(EXTRACT_DIR)
	$(MAKE) -j $(NJOBS) -f $(COQ_MAKEFILE) vos

clean: clean-frontend
	-$(MAKE) -f $(COQ_MAKEFILE) clean
	rm -f $(COQ_MAKEFILE) $(COQ_MAKEFILE).conf
	find . -name '.*.aux' -delete
	rm -rf $(EXTRACT_DIR)

# Metavariable stems from the Ott grammar are renamed to the paper's Greek
# letters, and the per-colour variable sorts are aliased to one atom type.
define GREEK_SED
	sed -e "/Ott.ott_list_core/d" $(SED_FLAG) $@
	sed -e "s/dE/Γ/g" -e "s/dD/Δ/g" -e "s/dP/Ψ/g" -e "s/eps/ε/g" $(SED_FLAG) $@
	sed -e "s/Xpt/α/g" -e "s/Xbt/α/g" -e "s/Xut/α/g" \
	    -e "s/Xps/α/g" -e "s/Xbs/α/g" -e "s/Xus/α/g" $(SED_FLAG) $@
endef

# Regeneration is opt-in: ordinary builds use the committed syntax.
ifneq ($(filter ott lngen,$(MAKECMDGOALS)),)
ott: $(addsuffix /def_ott.v,$(SYSTEMS))

%/def_ott.v: %/language.ott
	ott -i $^ -o $@ $(OTT_FLAGS)
	$(GREEK_SED)
	sed -e "s/Definition ctypvar : Set := var\./Notation ctypvar := typvar./g" $(SED_FLAG) $@
	sed -e "s/Definition btypvar : Set := var\./Notation btypvar := ptypvar./g" \
	    -e "s/Definition utypvar : Set := var\./Notation utypvar := ptypvar./g" \
	    -e "s/Definition gutypvar : Set := var\./Notation gutypvar := ptypvar./g" \
	    -e "s/Definition psklvar : Set := var\./Notation psklvar := ptypvar./g" \
	    -e "s/Definition bsklvar : Set := var\./Notation bsklvar := ptypvar./g" \
	    -e "s/Definition usklvar : Set := var\./Notation usklvar := ptypvar./g" $(SED_FLAG) $@

lngen: $(addsuffix /prop_ln.v,$(SYSTEMS))

%/prop_ln.v: %/def_ott.v
	$(LNGEN) --coq $@ --coq-ott $*.ott $*/language.ott
	sed -e "s/.ott./.def_ott./" $(SED_FLAG) $@
	$(GREEK_SED)

endif

# The frontend uses only the OCaml standard library. Keep compiler products
# separate from both hand-written sources and Coq's generated extraction.
# Syntax, paper examples, and invocation examples: README.md.
OCAMLC ?= ocamlc
FRONTEND_BUILD := _build/frontend
FRONTEND_SOURCES := frontend/parser.ml frontend/printer.ml frontend/main.ml
EXAMPLES := $(sort $(wildcard examples/*.fresco))

.PHONY: extract frontend examples test-frontend clean-frontend
extract : ${COQ_MAKEFILE}
	mkdir -p ${EXTRACT_DIR}
	${MAKE} -j ${NJOBS} -f ${COQ_MAKEFILE} fresco/ext_algo/extraction/Extract.vo
	@test -f ${EXTRACT_DIR}/fresco_guess.ml -a -f ${EXTRACT_DIR}/fresco_guess.mli || \
	  coqc -R . src fresco/ext_algo/extraction/Extract.v

frontend : extract
	mkdir -p ${FRONTEND_BUILD}
	cp ${EXTRACT_DIR}/fresco_guess.ml ${EXTRACT_DIR}/fresco_guess.mli $(FRONTEND_SOURCES) ${FRONTEND_BUILD}/
	cd ${FRONTEND_BUILD} && $(OCAMLC) -w -a -c fresco_guess.mli && \
	  $(OCAMLC) -w -a -c fresco_guess.ml && \
	  $(OCAMLC) -o fresco fresco_guess.cmo parser.ml printer.ml main.ml

examples : frontend
	${FRONTEND_BUILD}/fresco $(EXAMPLES)

test-frontend : frontend
	python3 frontend/test_frontend.py ${FRONTEND_BUILD}/fresco

clean-frontend :
	rm -rf ${FRONTEND_BUILD}
