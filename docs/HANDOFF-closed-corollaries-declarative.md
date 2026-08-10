Handover — Frost mechanization: state the CLOSED-PROGRAM COROLLARIES against
the PURELY DECLARATIVE system (`d_sd_typing` / `d_typing`), in BOTH
directions.

## STATE (2026-08-10, second pass)

⭐ **SOUNDNESS IS DONE.**  `a_typing_sound_infer` / `a_typing_sound_check`
(`frost/algo/typing/prop_closed.v`) now read the paper's own §declarative
system on the declarative side — `· ⊢ˢ[M] e ⦂ B` AND `· ⊢[M] e ⦂ B` — over a
declarative context.  `make coq` exit 0, admit-free, axiom-free, README.v
24/24 `Print Assumptions` closed.

⛔ **COMPLETENESS IS NOT DONE**, and the two things blocking it are recorded
below and in `frost/algo/typing/prop_conserv.v` §12.  ⚠️ One of them (B) was
NOT known when the first pass wrote this hand-off.

## WHAT LANDED

**`frost/algo/typing/prop_conserv.v`** (new, ~1300 lines) — the conservativity
bridge the paper asserts and never states (`app:decl-in-algo-context`: *"it is
easy to extend them to algorithmic contexts Θ"*).  Registered in
`docs/PAPER-GAPS.md`.

| § | what |
|---|---|
| 0 | `denv_to_aenv` — a declarative context IS a flexible-free algorithmic one; `denv_to_aenv_no_flex_def` is what makes every FlexL/FlexR/FlexMono row vacuous |
| 0b | Δ is `atoms` on the `ad` side, `list atom` on the `d` side: related by membership (`delta_agree`), not converted |
| 1 | `a_tyequiv_denv_eq` — the appendix's four `Θ ⊢ A ≡ B` premises collapse to `=` |
| 2 | `a_wf_ptyp` / `a_wf_pskl` ⇄ `d_wf_ptyp` / `d_wf_pskl` |
| 3–4 | `ad_pat_consis` ⇄ `d_pat_consis` (SK) and ⇄ `d_consis` (TY) |
| 5 | `ad_refine_syn` ⇄ `d_refine_syn` |
| 6 | the ForallL instantiation across the sorts (`d_wf_uskl_of_a_wf_pskl`, the ghost-free retraction `uskl_to_utyp`, `d_tags_uskl_to_utyp`, `d_wf_utyp_of_d_wf_uskl`) |
| 7–8 | `ad_pat_sub` ⇄ `d_pat_sub` (SK) and → `d_sub` (TY) |
| 9–10 | `ad_pat` → `d_pat`, `ad_sd_typing` → `d_sd_typing` |
| 11 | ⭐ CLOSING the run's output context: `ad_sd_typing_close_suffix` |
| 12 | the completeness direction: how far it reaches and where it stops |

Two conversions were added to `frost/coercions.v` (`utyp_to_uskl` — the sort
inclusion — and its retraction `uskl_to_utyp`), with their facts in
`frost/prop_coercions.v`.  The `msubst_btyp` facts §11 needs are in
prop_conserv.v: `msubst_btyp` was DEFINED in `algo/def_meta.v` and used by no
proof anywhere, so that section is its only home.

**The closing (§11) is the step the paper does not mention.**  Soundness
delivers its declarative derivation at the run's OUTPUT context Θ₁, which
normally still holds flexibles (`fun x -> x` at `·` gives `Θ₁ = α̂` and answer
`α̂ → α̂`), and the bridge needs a flexible-FREE context.  Since the run starts
at `·`, Θ₁ is a pure suffix, so every entry is solvable into its own tail
(`solves_flex_of_wf_head`); peeling it with `ad_sd_typing_subst_mid` and
accumulating the solutions BUILDS a `ζ ∷ Θ₁ ⊑ ·` together with the derivation
at `·`.  Building it (rather than quantifying over one) is what keeps the
corollary non-vacuous.

The corollaries also lost their existential `Bt`: at `TI` the answer's
colouring is forced to `syn{A}` and at `TC` to `inh{A}`, so the statement now
names the type directly.

## WHAT BLOCKS COMPLETENESS

Completeness needs the OTHER direction, `d_sd_typing · e B → ad_sd_typing · e B`.

### (A) The leaf-valid datum — ⭕ R0 IS NOW SETTLED, and the answer is "no"

`ad_pat` / `ad_sd_typing` embed `ad_pat_sub_v`, whose consistency leaves carry
`Θ ⨟ ∅ ⊢ᵣₚᵃᵈ ⌊R⌋ˢ ⊳ ⌊Q⌋`; `d_pat` / `d_sd_typing` embed the plain join.
`cex/cex_ad_pat_join_not_leaf_valid.v` machine-checks that the datum is not
recoverable at the capture configuration (subject `∀X.◇`, counterpart `∀ˢX.X`).

⭐ **The open half is now proved** — `d_pat_consis_subject_refine_ghost_free`
(prop_conserv.v §12): **at a ghost-free subject the leaf datum IS derivable
from consistency alone.**  The ∀ rows line up (consistency pushes the bound
rigid into Γ, refinement into Δ — the `tvars_denv Δd ++ Γ0` split in the
statement is exactly that correspondence) and every rule that could fill a
ghost with a binder-bound variable is excluded by the subject.

So the previous session's question — *"is the capture configuration reachable
for `ad_sd_typing` at a closed program?"* — resolves as follows:

- **`ad_sd_typing`'s OWN base rows can never be the problem.**  They join
  `ptyp_to_uskl_syn A` for a `ptyp` `A`, which has no ghosts.
- **`ad_pat`'s P-Var can.**  Its subject is `syn{P}` for a `P` read out of the
  context, and `ad_pat__abs` may push `x : P` for ANY well-formed `P`,
  including `∀ˢ.◇`.  `d_sd_typing`'s App rule has a `d_pat` premise, so
  skeleton inference is reachable from typing; inside it, `d_pat__abs`
  requires `M ≠ TC` and is reached from the App premise's `TC` through
  `d_pat__app`'s function premise (`mode_fn M`) or `d_pat__freeze` (`TI`).

⚠️ Note what this does NOT establish: a *reachable configuration* is not yet a
*counterexample to the bridge*.  Refuting `d_sd_typing · e B → ad_sd_typing ·
e B` needs a closed `e`, `B` with the `ad` side FALSE — i.e. ruling out every
`ad` derivation, not just the one the `d` derivation mirrors.  The App rule
existentially quantifies its skeleton `P`, so a refutation has to close over
all choices of `P`.  That is the remaining piece of work on (A).

### (B) Tag hygiene — ⚠️ NEW, and it bites at the TYPE sort too

`ad_pat_sub_gv`'s two ForallL rows carry, beyond the paper's `Ψ' ∩ Ψ = ∅`,

```coq
Ψ' ∩ (ftag_in_uskl (uskl_all_etag ε R)) [=] empty
```

— the instantiation's tags fresh from the SUBJECT's syntactic tags.  That is
the mech's rendering of the paper's prose `fresh Ψ'` as GLOBAL freshness, and
it is load-bearing: `lemma:precision-substitution` is FALSE without it
(`docs/DESIGN-completeness-subtyping.md` §5.2, and the 2026-07-24
PROSE-COMPLETION entry in `docs/PAPER-GAPS.md`).

`d_sub` / `d_pat_sub` render the same prose as freshness from the TAG CONTEXT
only.  Along a ForallL CHAIN the two agree (the tag context accumulates
`Ψ ∪ Ψ'`), but they come apart at **Arrow**, where the tag context splits into
`Ψ₁ ∪ Ψ₂` and the recursive call keeps only `Ψ₂` while the subject keeps all
of its tags.  Bridging them needs an ε-tag FRESHENING lemma over `d_sub` /
`d_pat_sub` — the `_n → _g` renaming the development explicitly deferred.

⚠️ Unlike (A) this is not confined to the skeleton sort: `ad_sd_typing`'s base
rows go through `ad_pat_sub_gv` at `N = TY`, whose ForallL rows carry the same
condition.  So (B) blocks completeness even if (A) is resolved.

## ROUTES, RE-SCORED

- **R1 (restricted bridge)** — needs (A)'s reachability question closed in the
  *negative sense* described above AND all of (B).  The (A) half now has its
  positive lemma; the missing invariant would have to say that the ghosty
  skeleton entries `d_pat__abs` may introduce never reach a capture at a
  closed program, over ALL choices of the App rule's existential `P`.
- **R2 (leaf-validity as a side condition)** — still the cheapest way to keep
  the paper's system untouched, but the side condition is a property of the
  DERIVATION, not of the conclusion, so it does not state well; and it does
  nothing about (B).
- **R3 (a leaf-valid declarative twin)** — would absorb (A) and (B) together
  (define the twin with both the leaf data and the hygiene), at the cost of a
  judgement whose relation to `d_sd_typing` is then the open question.  ⭐ This
  is now the most promising route, because it is the only one that addresses
  (B) without a freshening lemma.
- **R4 (strengthen the paper's declarative system)** — unchanged: it forces
  the standalone `Sub` rule too and re-opens Phase 2 plus the paper's
  §declarative figure.  Author-facing decision; ASK first.
- **NEW prerequisite for R1/R2**: the ε-tag freshening lemma for `d_sub` /
  `d_pat_sub`.  Whatever route is taken, (B) has to be paid for.

## ACCEPTANCE — where it stands

- ✅ `a_typing_sound_infer` / `a_typing_sound_check` read `⊢ˢ` and `⊢` on the
  declarative side
- ⛔ `a_typing_complete_infer` / `a_typing_complete_check` still read `⊢ᵃᵈ`
- ✅ `make coq` exit 0, every `Print Assumptions` "Closed under the global
  context", zero Axioms/Parameters/Variables/Admitted
- ✅ README.v's `Check`s updated for the two soundness corollaries
- ✅ the bridge is registered in `docs/PAPER-GAPS.md` as the prose-completion
  of `app:decl-in-algo-context`'s "it is easy to extend"
- ⚠️ no route was taken that requires changing `d_sd_typing` / `d_typing` —
  that decision is still the user's
