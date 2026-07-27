COQ_PROJECT  := _CoqProject
COQ_MAKEFILE := CoqMakefile

OTT_FLAGS := -coq_lngen true -signal_parse_errors true

SYSTEMS := frost
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

PAPER_AUX := ../paper/frost.aux

# Use `make NJOBS=N coq` (or quick) for parallel compilation. Default 4.
NJOBS ?= 4

.PHONY: coq quick clean sync-paper-refs sync-paper-refs-md

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

# a hack to force makefile to detect source file changes
.FILE_LIST : ${LNGEN_OUTS} FORCE
	tree . -if -I ${IGNORE_DIRS} | grep -E "v$$" | cut -c3- | sort -s > .FILE_LIST.tmp
	diff $@ .FILE_LIST.tmp || cp .FILE_LIST.tmp $@
	rm .FILE_LIST.tmp

FORCE:

${COQ_MAKEFILE} : ${COQ_PROJECT} .FILE_LIST ${LNGEN_OUTS}
	tree . -if -I ${IGNORE_DIRS} | grep -E "v$$" | cut -c3- | xargs coq_makefile -o $@ -f ${COQ_PROJECT}

coq : ${COQ_MAKEFILE}
	${MAKE} -j ${NJOBS} -f ${COQ_MAKEFILE}

# `quick` skips Qed-proof checking via `vos`/`vok` mode (much faster for
# development iteration on prop_typing.v). Files compile to .vos rather
# than .vo; opaque proofs aren't replayed. Use plain `make coq` before
# committing to verify the full kernel acceptance.
quick : ${COQ_MAKEFILE}
	${MAKE} -j ${NJOBS} -f ${COQ_MAKEFILE} vos

clean :
	${MAKE} -f ${COQ_MAKEFILE} clean
	rm */prop_ln.v */def_ott.v ${COQ_MAKEFILE} ${COQ_MAKEFILE}.conf .FILE_LIST

# Sync paper Lemma/Theorem numbers from the compiled paper into:
#   - `[paper-ref: ...]`-marked comments in .v files
#   - the auto-managed `<!-- BEGIN paper-refs -->`..`END` block in
#     PROGRESS.md (label → file:line reference-link definitions)
# Requires paper to be built first (`make -C ../paper` or similar).
sync-paper-refs : ${PAPER_AUX}
	python3 scripts/sync_paper_refs.py

# Same, but only the Markdown block (no .v file edits) — fast.
sync-paper-refs-md : ${PAPER_AUX}
	python3 scripts/sync_paper_refs.py --md
