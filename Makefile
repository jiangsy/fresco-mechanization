COQ_PROJECT  := _CoqProject
COQ_MAKEFILE := CoqMakefile

OTT_FLAGS := -coq_lngen true -signal_parse_errors true

SYSTEMS := fresco
IGNORE_DIRS := ""
OTT_OUTS   := $(addsuffix /def_ott.v,${SYSTEMS})
LNGEN_OUTS := $(addsuffix /prop_ln.v,${SYSTEMS})

ifeq ($(OS), Windows_NT)
	UNAME_S := Windows
else
	UNAME_S := $(shell uname -s)
endif

ifeq ($(UNAME_S), Darwin)
	SED_FLAG := -i ""
else
	SED_FLAG := -i
endif

PAPER_DIR ?= ../impredicative/paper
PAPER_AUX := $(PAPER_DIR)/frost.aux

# Use `make NJOBS=N coq` (or quick) for parallel compilation. Default 4.
NJOBS ?= 4

.PHONY: coq quick clean tidy sync-paper-refs sync-paper-refs-md

%/def_ott.v : %/language.ott
	ott -i $^ -o $@ ${OTT_FLAGS}
	sed -e "/Ott.ott_list_core/d" ${SED_FLAG} $@
	sed -e "s/dE/Γ/g" ${SED_FLAG} $@
	sed -e "s/dD/Δ/g" ${SED_FLAG} $@
	sed -e "s/dP/Ψ/g" ${SED_FLAG} $@
	sed -e "s/eps/ε/g" ${SED_FLAG} $@
	# Type/skeleton variables uniformly greek: the ott metavar stems
	# (Xpt/Xbt/Xut = type vars in the 3 colours, Xps/Xbs/Xus = skeleton
	# vars) all become α. The numeric suffix lngen appends keeps distinct
	# vars distinct (α1, α2, …); no generated lemma mixes two stems, so
	# this is collision-free. Hand-written lemmas that referenced a stem
	# name are fixed manually (one-shot).
	sed -e "s/Xpt/α/g" -e "s/Xbt/α/g" -e "s/Xut/α/g" \
	    -e "s/Xps/α/g" -e "s/Xbs/α/g" -e "s/Xus/α/g" ${SED_FLAG} $@
	# ctypvar = ptypvar (both are atom). Use a Notation so Coq's
	# type-class resolution sees ctypvar and typvar as the same
	# syntactic head — Definition aliases don't unify for typeclasses,
	# but Notation does (parse-time substitution).
	sed -e "s/Definition ctypvar : Set := var\./Notation ctypvar := typvar./g" ${SED_FLAG} $@
	# Phase A refactor: btypvar / utypvar / skelvar also alias typvar.
	sed -e "s/Definition btypvar : Set := var\./Notation btypvar := ptypvar./g" ${SED_FLAG} $@
	sed -e "s/Definition utypvar : Set := var\./Notation utypvar := ptypvar./g" ${SED_FLAG} $@
	sed -e "s/Definition gutypvar : Set := var\./Notation gutypvar := ptypvar./g" ${SED_FLAG} $@
	sed -e "s/Definition psklvar : Set := var\./Notation psklvar := ptypvar./g" ${SED_FLAG} $@
	sed -e "s/Definition bsklvar : Set := var\./Notation bsklvar := ptypvar./g" ${SED_FLAG} $@
	sed -e "s/Definition usklvar : Set := var\./Notation usklvar := ptypvar./g" ${SED_FLAG} $@

ott : ${OTT_OUTS}

%/prop_ln.v : %/def_ott.v
	lngen-new --coq $@ --coq-ott $*.ott $*/language.ott
	sed -e "s/.ott./.def_ott./" ${SED_FLAG} $@
	sed -e "s/dE/Γ/g" ${SED_FLAG} $@
	sed -e "s/dD/Δ/g" ${SED_FLAG} $@
	sed -e "s/dP/Ψ/g" ${SED_FLAG} $@
	sed -e "s/eps/ε/g" ${SED_FLAG} $@
	# Type/skeleton variables uniformly greek (see the def_ott.v recipe).
	sed -e "s/Xpt/α/g" -e "s/Xbt/α/g" -e "s/Xut/α/g" \
	    -e "s/Xps/α/g" -e "s/Xbs/α/g" -e "s/Xus/α/g" ${SED_FLAG} $@

lngen : ${LNGEN_OUTS}

# The CoqMakefile is regenerated whenever the set of .v files changes.
VFILES := $(shell find . -name '*.v' | sed 's|^\./||' | sort)

${COQ_MAKEFILE} : ${COQ_PROJECT} ${LNGEN_OUTS} $(VFILES)
	printf '%s\n' $(VFILES) | xargs coq_makefile -o $@ -f ${COQ_PROJECT}

# The extraction driver (fresco/ext_algo/extraction/Extract.v) writes its OCaml
# into a fixed directory, and `Set Extraction Output Directory` does NOT create
# it — a fresh clone would fail there.  Make it unconditionally; it is one
# mkdir and it keeps the build self-contained.
EXTRACT_DIR := fresco/ext_algo/extraction/extracted

# The frontend uses only the OCaml standard library. Keep compiler products
# separate from both hand-written sources and Coq's generated extraction.
# Syntax, paper row mappings, and invocation examples: frontend/README.md.
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

coq : ${COQ_MAKEFILE}
	mkdir -p ${EXTRACT_DIR}
	${MAKE} -j ${NJOBS} -f ${COQ_MAKEFILE}

# `quick` skips Qed-proof checking via `vos`/`vok` mode (much faster for
# development iteration on prop_typing.v). Files compile to .vos rather
# than .vo; opaque proofs aren't replayed. Use plain `make coq` before
# committing to verify the full kernel acceptance.
quick : ${COQ_MAKEFILE}
	mkdir -p ${EXTRACT_DIR}
	${MAKE} -j ${NJOBS} -f ${COQ_MAKEFILE} vos

clean : tidy clean-frontend
	${MAKE} -f ${COQ_MAKEFILE} clean
	rm -f */prop_ln.v */def_ott.v ${COQ_MAKEFILE} ${COQ_MAKEFILE}.conf .FILE_LIST
	# Litter coq_makefile's own `clean` does not know about: the .aux
	# per-proof timing files, and .DS_Store.  `find` rather than a glob
	# list, because the tree is three levels deep (algo/completeness_look/)
	# and the old `*/.*.aux */*/.*.aux` pair silently missed level three.
	find . -name '.*.aux' -delete
	find . -name '.DS_Store' -delete
	rm -f .lia.cache
	# The extracted OCaml is a BUILD PRODUCT, regenerated on every `make coq`.
	rm -rf ${EXTRACT_DIR}

# `tidy` removes ONLY orphaned build artifacts — a .glob/.vo/.vok/.vos/.aux
# whose companion .v no longer exists.  Safe to run at any time, and unlike
# `clean` it PRESERVES the live .aux files, which record proof_build_time per
# proof and are the starting point of every performance pass (see CLAUDE.md).
#
# Orphans accumulate silently: every deleted scratch buffer, every renamed
# file (the 2026-08-09 audit renamed six) leaves its artifacts behind, and
# they are a grep hazard — a stale .glob still names lemmas that are gone.
# Detection is by companion-file existence, not by a `scratch_*`/`probe_*`
# name pattern, so it needs no maintenance as new prefixes get invented.
.PHONY: tidy
tidy :
	@find . \( -name '*.glob' -o -name '*.vo' -o -name '*.vok' -o -name '*.vos' \) \
	  | while read f; do [ -f "$${f%.*}.v" ] || { echo "  tidy: $$f"; rm -f "$$f"; }; done
	@find . -name '.*.aux' \
	  | while read a; do b=`basename "$$a"`; d=`dirname "$$a"`; v="$$d/$${b#.}"; \
	      [ -f "$${v%.aux}.v" ] || { echo "  tidy: $$a"; rm -f "$$a"; }; done

# Sync paper Lemma/Theorem numbers from the compiled paper into:
#   - `[paper-ref: ...]`-marked comments in .v files
#   - the auto-managed `<!-- BEGIN paper-refs -->`..`END` block in
#     PROGRESS.md (label → file:line reference-link definitions)
# Requires paper to be built first (`make -C $(PAPER_DIR)` or similar; PAPER_DIR defaults to the sibling `impredicative/paper` checkout).
sync-paper-refs : ${PAPER_AUX}
	FRESCO_PAPER_DIR=$(PAPER_DIR) python3 scripts/sync_paper_refs.py

# Same, but only the Markdown block (no .v file edits) — fast.
sync-paper-refs-md : ${PAPER_AUX}
	FRESCO_PAPER_DIR=$(PAPER_DIR) python3 scripts/sync_paper_refs.py --md
