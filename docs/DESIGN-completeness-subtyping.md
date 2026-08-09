# Mechanizing Completeness + Optimality of Subtyping

Companion to `DESIGN-subtyping.md` (which covers both halves at the map
level and whose §2.2 / §4 / §5 this doc refines).  Soundness
(`a_sub_sound`) is **DONE, Qed, axiom-free**
(`prop_decorate_key.v:3406`).  This doc is the concrete plan for the
completeness half (paper `thm:complete-subtyping`), written **after**
finishing soundness so the two hard lessons of that effort are baked in.

Paper: `paper/sections/algorithmic.tex:1446` (statement),
`paper/sections/appendices/subtyping-proofs.tex:1526-3536` (proofs).

---

## 0. The two lessons from soundness (READ FIRST)

Soundness detoured twice and each detour cost sessions.  Both are
avoidable here by a decision made *before* the first proof.

1. **Statement drift — do not invent a mech-only strengthening; do not
   leave the motive too weak.**  Soundness burned time on a
   `ghost_free P0` condition that was *stronger* than the paper and not
   derivable at the SK/fn call sites.  The dual failure mode on
   *completeness* is a motive that is too *weak*: the paper's 2-condition
   solution notion makes `thm:complete-subtyping` **FALSE** (the
   `(P0=◇, P=∀X.◇, Q=∀X.X)` capture — see `PAPER-GAPS.md` and
   `DESIGN-subtyping.md §3.1`).  The consistency completeness theorem
   already carries the fix: a **third** solution premise beyond join +
   fill, namely subject refinement `ad_refine_pskl_f ∅ Θ ∅ (κP) Q`.  Our
   subtyping motive carries the analog **from the start** (see §1), and
   its shape is copied *verbatim* from `a_consis_complete`
   (`prop_consis_complete.v:8648`) — every deviation costs a transport
   lemma later.

2. **Follow the paper's proof structure; do not invent an intermediate
   relation.**  Soundness's L-A wasted sessions on a bespoke `dec_ext`
   bridge with a per-step Ψ-growth identity that turned out FALSE at the
   ∀ node; the paper's actual device was monolithic set-membership
   coverage.  Completeness has *no* such temptation **provided we honour
   the paper's two big honest inductions** — one on the **declarative
   `ad_pat_sub` derivation height** (main thm + `-solving-var`), one on
   the **context list** (complete-flex) — and reuse the *existing* Qed
   recipes (`guess_join_witness`, the assign/unify walk) instead of
   rebuilding them.  The only new *infrastructure* is the fuel index
   (§2), which is forced, not invented.

---

## 1. The generalized motive (LOCK THIS)

Paper generalized statement, `subtyping-proofs.tex:3054-3074`: prove not
`thm:complete-subtyping` directly but its Ψ-general, `S`-general form,
then instantiate `S=P`, `Ψ=∅`.

```
Given problem (Θ0;N;M;P0;P), tag ctx Ψ, unresolved S with ⌊S⌋=P,
and (κ:Θ0⇒Θ ; Q), IF
  (join/subtyping)  typsub^N_M[Ψ] Θ ⊢ syn(κS) ⊑ bid Q          ← height/fuel lives here
  (P0-fill)         Θ ⊢ inh(κP0) ⤳syn bid Q
THEN ∃ P1 Θ1 κ1:
  a_sub^N_M[P0] Θ0 ⊢ P ⊑ P1 ⊣ Θ1        (algo run)
  κ1:Θ1⇒Θ  ∧  Θ ⊢ κ1 P1 ⊑ Q (precision)  ∧  κ ≡ κ1 : Θ0⇒Θ.
```

**Mech motive** — copy `a_consis_complete`'s shape (the id-witness
`ρ1`/`ζ` factoring), swap consistency's judgment for `ad_pat_sub`, and
add the *third* solution premise (lesson 1).  Skeleton:

```coq
Lemma a_sub_complete_gen : forall n,          (* fuel; strong induction *)
  forall NM M Θ0 P0 P S Ψ Θ ρ Q,
    a_wf_aenv Θ0 ->  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
    ⌊S⌋ˢ = P ->                               (* erasure of the unresolved subject *)
    ρ ∷ Θ0 ⊑ Θ ->  a_wf_aenv Θ ->
    (* solution, 3 conditions — matching a_consis_complete: *)
    ad_pat_sub_n n NM M Ψ Θ (msubst_uskl ρ S) Q ->                       (* join, fuel n *)
    ad_refine_syn_f empty Θ empty (pskl_to_bskl_inh (msubst_pskl ρ P0)) Q ->  (* P0-fill *)
    ad_refine_pskl_f empty Θ empty (msubst_pskl ρ ⌊S⌋ˢ) (bskl_to_pskl Q) ->   (* SUBJECT refinement — lesson 1 *)
    exists P1 Θ1,
      a_sub NM M P0 Θ0 P P1 Θ1 /\
      (forall ρ1, is_id_msubst ρ1 -> ρ1 ∷ Θ0 ⊑ Θ1 ->
         exists ζ, ζ ∷ Θ1 ⊑ Θ /\
                   a_inc_equiv Θ0 ρ (msubst_compose ζ ρ1) Θ /\
                   Θ ⨟ empty ⊢ₚᵣᵃ (msubst_pskl ζ P1) ⊑ (bskl_to_pskl Q)).
```

✅ **LOCKED 2026-07-30 — `frost/algo/prop_sub_complete_thm.v`** carries the two
motives as `sub_complete_concl` / `sub_flex_complete_concl` (+ the bundle
statement `a_sub_complete_bundle`, named after `a_sub_decorate_bundle`), and
they typecheck.  ⚠️ The unresolved subject is spelled `R`, not the paper's `S`:
it is a `uskl`, and the metavariable convention spells that sort `R` (P6-L
calls the same thing `R'`).  Writing them out corrected the skeleton above in two places:

- ⚠️ **The fuel judgment is `ad_pat_sub_g`, not `ad_pat_sub_n`.**  The
  development settled on the TAG-HYGIENIC fuel mirror, because
  precision-substitution — which ForallL applies to its premise to get the
  derivation it hands the IH — is FALSE over `_n` (§5.4).  P5 and ALL FIVE P6
  lemmas are stated over `_g`, so P7 must be.
- ⚠️ **The factored conclusion is FORCED, not stylistic.**  `a_inc_equiv` is
  POSITIONAL (def_meta.v:268 pairs the two metasubstitutions' entries key-by-key
  against `Θ0`'s entries), so the paper's flat `inc[θ≡θ1]{Θ0}{Θ}` rendered as
  `a_inc_equiv Θ0 κ ζ Θ` with `ζ ∷ Θ1 ⊑ Θ` is not even the right SHAPE: ζ is
  keyed by `Θ1`, which has entries `Θ0` does not — and at Flex-Solve in the
  MIDDLE rather than at the end.  Keeping `a_consis_complete`'s
  `forall κ1, is_id_msubst κ1 → … → exists ζ` wrapper says the same thing while
  staying well-formed, and the four consistency cases then pass their conclusion
  straight through.

Also fixed while writing: P7a's context split.  `a_sub_flex NM M P0 Θ0 Ξ α P1 Θ1`
keeps the walked-past entries in `Ξ` and the rest in `Θ0`; the FULL context is
`Ξ ++ Θ0` (`a_sub_flex__depend`'s conclusion is at `(β~flex) ++ Θ0` with suffix
`Ξ`, its premise at `Θ0` with suffix `Ξ ++ (β~flex)` — the same list), and
`a_sub__flex_mono` enters at `Ξ = ·`.  So P7a's premises and its `a_inc_equiv`
are stated at `Ξ ++ Θ0`, and the measure is lex(n, |Θ0|).

Notes on shape (verify each against `a_consis_complete` when writing):
- `κ` is the mech's `ρ ∷ Θ0 ⊑ Θ` (an `a_inc` metasubstitution).
- `bid Q` target: `ad_pat_sub`'s target sort is **`bskl`** (`Q : bskl`),
  matching `a_consis`'s `Qb`.  Precision conclusion compares `pskl` to
  `pskl` via `ad_precise` (`⊑ₚᵣᵃ`, `prop_precise.v:47`
  = `⊢ᵣᵃ inh{·} ⊳ inh{·}`); erase `Q` with `bskl_to_pskl`.
- The **third premise** `ad_refine_pskl_f ∅ Θ ∅ (msubst ρ ⌊S⌋ˢ) (bskl_to_pskl Q)`
  is the repair.  It is exactly what `a_consis_sound`'s `⊢ᵣₚᵃ` conjunct
  *produces* for every algorithmic output, so the sound/complete pair
  still characterizes the algorithm exactly (it succeeds iff a
  refinement-valid solution exists and is ⊑-optimal among them).  Thread
  it through every case just as consistency threads its subject
  refinement.

  ⚠️ **REFUTED AS STATED (2026-07-30) — the root-level third premise is a
  LOCKSTEP condition and truncates the theorem far beyond a ghost corner.**
  Two machine-checked findings (`cex/cex_p7_univ_ghost_r_vacuous.v`,
  `cex/cex_p7_third_premise_forall.v`, both Qed + axiom-free):
  (i) the justification above is wrong for subtyping — `a_sub_sound`
  exports NO subject-refinement conjunct (algorithmic `UnivGhostR` outputs
  `∀◇.P` from input `P`, which refinement cannot mirror), so the premise is
  not the sound/complete mirror it is for consistency; (ii) because
  `ad_refine_pskl` descends both sides together while `ForallL` / `ForallR`
  / `UnivGhostR` break head correspondence, the premise excludes
  `Sub-UnivGhostR` entirely AND every head-disagreeing solution of
  `ForallL` / `ForallR` — including `∀a.a ⩽ unit` and `unit ⩽ ∀a.unit`.
  Consistency's own third premise is harmless only because `ad_pat_consis`
  is itself lockstep (its ∀-inh rows demand ∀-or-ghost subjects).  The
  REPAIR is to move the condition to the CONSISTENCY LEAVES of the
  declarative derivation (`__infer` / `__check` / `__univ_ghost_r`, the
  latter at the STRIPPED counterpart) — exactly the data the
  `a_consis_complete` invocations consume; the closed rows survive
  (Ghost / GhostG never use the premise; Infer / Check use it only to feed
  consistency).  Full analysis + author options in `PAPER-GAPS.md`
  ("MECH-PREMISE … third solution condition").

  ✅ **REPAIR LANDED (2026-07-30, same day).**  The join is now the
  LEAF-VALID mirror `ad_pat_sub_gv` (def_decl_algo_sub_hyg.v; three
  augmented leaf rows + `ad_pat_sub_gv_forget` back to `_g` for every
  P5/P6 invocation), and `sub_complete_concl` / `sub_flex_complete_concl`
  have NO root-level third premise.  All five closed rows re-closed, and
  `a_sub_complete_univ_ghost_r` is now a REAL proof: algorithmic
  `UnivGhostR`, the shared `□`-P0 precision core at the STRIPPED
  counterpart (`ad_refine_syn_f_hole_tophole_inv` strips the fill), and an
  `ad_refine_syn__tophole_keep` wrap (`guarded_bskl_inh_repaint` supplies
  the guard).  New plumbing: `ad_refine_pskl_f_empty_intro` (plain ⊳ →
  `_f` at `F = ∅`) and `ad_pat_sub_gv_ti_refine` (every TI row yields the
  subject refinement — `__infer` on the rule, the ghost subjects from
  their own wf premises).  ⚠️ REMAINING OBLIGATION for ForallL / ForallR:
  the P5 precision-substitution (`ad_pat_sub_precise_upre`) and the
  `_n→_g` freshening/renaming kits must be transported to `_gv`; the one
  genuinely new fact is that precision-substitution preserves the leaves'
  subject refinement (the substituted subject is GHOSTIER, so its erasure
  refines further — but the new holes' fills must stay Δ-clean; state it
  with the same care as the `uskl_precise` wf side conditions).
- **Corollary** `a_sub_complete` (paper-facing): `S:=` a decoration
  with `⌊S⌋=P` (any `is_tskl` witness, e.g. via `pskl_decorate_exists`,
  or just `S = pskl_to_uskl P` if the subject can be the plain skeleton),
  `Ψ:=∅`, `n` from `ad_pat_sub_to_n`.

**Mutual partner** — `a_sub_flex_complete` (`complete-flex-subtyping`,
`subtyping-proofs.tex:2835`): same conclusion shape but subject `α̂`,
context split `Θ0 ∣ Ξ` (`Ξ` all-flexible), and it recurses into
`a_sub_complete_gen`'s IH.  Combined measure §2.

---

## 2. The measure (LOCK THIS — the μ lesson: get it right before the bundle)

Paper: **lex(derivation height of the `typsub` premise, |Ψ|)**, main thm
mutual with complete-flex (induction on contexts `Θ0∣Ξ`).

**Why a fuel index is forced.**  `ad_pat_sub` is in `Prop`; we cannot
extract a structural `nat` size from a `Prop` derivation for well-founded
induction, and plain structural induction on the derivation gives **no
IH** for the ForallL case — there the IH is applied to `refi`, a
derivation *produced by* `precision-substitution`
(`subtyping-proofs.tex:3416-3429`), which is not a structural
sub-derivation of the ForallL conclusion.  So we index by fuel.

**Decision: a separate fuel-indexed mirror `ad_pat_sub_n : nat -> …`**,
NOT a re-indexing of `ad_pat_sub` itself (that would cascade into the
finished, Qed soundness proofs that consume `ad_pat_sub`).  Bridges:
- `ad_pat_sub_of_n : ad_pat_sub_n n … -> ad_pat_sub …`
- `ad_pat_sub_to_n : ad_pat_sub … -> exists n, ad_pat_sub_n n …`
- `ad_pat_sub_n_mono : ad_pat_sub_n n … -> n <= m -> ad_pat_sub_n m …`
  (fuel weakening; each rule at `S n` with premises at `n`, so equal-fuel
  siblings need `mono` to line up — the arrow rule especially).

**How the two IH applications stay well-founded** (the whole point):
- *structural premises* → strictly smaller fuel (built into `ad_pat_sub_n`).
- *ForallL* → IH on `refi = precision-substitution(refb)`.  `refb` is the
  ForallL premise (fuel `< n`); **`precision-substitution` preserves fuel
  exactly** (it reconstructs the *same* derivation rule-for-rule with
  `Pa` in place of `ψa` — paper: "would not result in any type
  mismatch"), so `refi` has fuel `= refb`'s `< n`.  Primary component
  decreases; `|Ψ|` is only the paper's belt-and-suspenders and is not
  strictly needed here (record but don't over-engineer).
- *complete-flex (mutual)* → induction on the context list `Ξ`; its
  Flex-Solve/Flex-Assign recurse into `a_sub_complete_gen`'s IH at fuel
  `≤ n` (the subtyping premise is obtained by **Arrow-inversion** of a
  premise, so its fuel is `< n`).  Combined measure: `lex(n, |Ξ|)` — the
  flex walk shrinks `Ξ` at fixed-or-smaller `n`.

**`precision-substitution` must therefore be stated fuel-preserving**
(`ad_pat_sub_precise_subst`, P5):
```
ad_pat_sub_n n NM M (Ψ ∪ Ψa) Θ (S[ψa/α]) Q ->
Θ ⊢ₚᵣᵃ Pa ⊑ ⌊ψa⌋ˢ ->  a_tags_sort NM Ψ' ψa ->  fresh Ψ' ->  Ψa ⊆ Ψ' ->
(NM = ty -> «Pa is a type») ->
ad_pat_sub_n n NM M Ψ Θ (S[Pa/α]) Q.       (* SAME n *)
```
(`S[ψa/α]`, `S[Pa/α]` = opening/substituting the `uskl` subject; `Pa` is
a `pskl` painted into the `uskl` subject — check the exact subst/paint
form against how ForallL builds `refi`.)

---

## 3. Phase / dependency order (concrete)

| phase | lemma (mech name) | paper | measure? | reuse |
|---|---|---|---|---|
| **P5a** | `ad_pat_sub_n` + `_of_n`/`_to_n`/`_n_mono` | — | defines fuel | new inductive in `def_decl_algo_sub.v` (append; no cascade) |
| **P5b** | `ad_partial_precise_complete` | partial-precision-complete (1639) | none | induction on `ad_partial_precise`; see §5.1 worked case-plan |
| **P5c** | `ad_pat_sub_precise_subst` | precision-substitution (1664) | **fuel-preserving** | induction on `ad_pat_sub_n`; uses P5b's precision to rule out mismatch |
| **P6a** | `a_solve_complete_var` | complete-cc-solving-var (1697) | height IH | induction on `ad_pat_sub_n` deriv; assign-walk / increment-transformer |
| **P6b** | `a_looksolve_complete` | complete-cc-solving (2203) | via P6a | wraps P6a at `Pi=Hole`, `Ψi=∅` |
| **P6c** | `a_extract_complete_gen` | complete-look (2730) | — | P6b + P5b + guess^TY sub-induction = `guess_join_witness` pattern |
| **P7a** | `a_sub_flex_complete` | complete-flex (2835) | `lex(n,|Ξ|)` mutual | assign/unify walk recipes (mid-strip/insert) |
| **P7b** | `a_sub_complete_gen` | thm generalized (3050) | `lex(n,|Ψ|)` | mutual w/ P7a; cases → `a_consis_complete` [Qed], P6c, P7a |
| **P7c** | `a_sub_complete` | thm (algorithmic.tex:1446) | — | instantiate `S=P`, `Ψ=∅`, `n` via `_to_n` |

Greenfield support still needed alongside (from `DESIGN-subtyping.md
§3.3`, mostly for P6): `a_looksub`/`a_solve_*`/`a_extract` wf+ftv+decls
basics; `a_solvetag*` concat.  Some already exist (`prop_looksub.v`,
`prop_solve_sub.v`) — audit before writing.

**Independence:** P5–P7 do **not** depend on soundness's L-A decoration
machinery; completeness is a separate track that only reuses the Qed
consistency black box + kits.  P5b (partial-precision-complete) is the
cleanest self-contained first Qed — start there to validate the
`ad_partial_precise` def and warm up, in parallel with standing up P5a.

---

## 4. Black boxes / kits (invoke, don't reprove)

- `a_consis_complete` (`prop_consis_complete.v:8648`, Qed,
  axiom-free) — the motive-shape template AND the Infer/Check/UnivGhostR/
  Arrow cases.  Its 3-premise form (join + P0-fill + **subject
  refinement**) is why our motive has the third premise.
- `guess_join_witness` increment-transformer (join file) — the
  guess^TY construction in `a_extract_complete_gen`.
- assign/unify walk recipes (closed unify/assign cases,
  `remech-complete-mu-bundle`) — the Flex-Solve/Assign/Depend/Skip cases
  of `a_sub_flex_complete`.
- msubst / a_inc / a_inc_equiv / mono-bridge / refinement-transport kits
  — `DESIGN-subtyping.md §3.2`.
- Existing subtyping infra (all Qed, `prop_pat_sub.v`):
  `ad_pat_sub_{isub,weaken,strip_suffix,rename_tvar,subst_flex,subst_flex_def}`,
  `ad_partial_precise_{isub,weaken}`.

---

## 5. Hazards specific to completeness

- **H1 (measure).** §2.  Nail `ad_pat_sub_n` + fuel-preserving
  precision-substitution before P6/P7.  This is the μ lesson.
- **H2 (paper-gap solution).** §1 lesson 1.  Third premise in the motive
  from the start; do not attempt to *derive* it from join+fill (FALSE).
- **H3 (WLOG-by-congruence, `subtyping-proofs.tex:155-173`).**
  `DESIGN-subtyping.md §4.1`.  The constraint-collection judgments are
  not syntax-directed; the paper reorders by fiat.  Lands in P6.  Budget
  real time; check `type.ml` as third witness for rule ordering.
- **H4 (freshness prose-completion / F-set).** The `a_sub` walk re-enters
  under `Ξ ++ …`; `a_subtag__forall_l_*` picks fresh tags.  Soundness
  already threaded the relevant `uniq (Ξ ++ Θ0)` prose-completions on the
  ForallL rules — reuse, don't re-derive.  Audit whether completeness's
  guess^TY needs more.
- **H5 (partial precision Δ generality).** `partial-precision-complete`
  is paper-stated at `Δ=∅` but its ∀-case extends `Δ`; state at general
  `Δ` (mirrors how `ad_refine_pskl` proofs generalize Δ).

---

## 5.1 P5b `ad_partial_precise_complete` — worked case-plan (execute next)

Statement (target is COLOURED precision `ad_precise`, matching the paper's
`⊑` and complete-look's `precise{κa Pa}{⌊ψa⌋}` output, tex:2764):

```coq
Lemma ad_partial_precise_complete : forall NM Θ Δ Ψ P ψ,
  a_tags_sort NM Ψ ψ ->
  Θ ⨟ Δ ⊢ₚₛᵃ ⌊ ψ ⌋ˢ ->            (* wf premise — the paper's "by wf of ψ"; needed by the hole case *)
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  Θ ⨟ Δ ⊢ₚᵣᵃ P ⊑ ⌊ ψ ⌋ˢ.          (* = ad_refine_syn Θ Δ (inh P) (inh ⌊ψ⌋) *)
```

Induction on `ad_partial_precise` (revert `a_tags_sort`/wf first, re-derive
per case).  `ad_precise` has NO tag index, so the IH only needs SOME
`a_tags_sort` for the sub-ψ (read straight off `d_tags_skl` inversion) —
**no `Ψ1 = tags ψ1` disjointness argument is needed** (key simplification).
Painting facts: `pskl_to_bskl_inh (pskl_all_syn P) = bskl_all_inh (inh P)`;
`pskl_to_bskl_inh_open` (exists, prop_basic.v:93).  Cases:

- **unit / var** → `ad_refine_syn__unit` / `__var` (var carries the same
  `X∈Δ ∨ tvar` disjunct).
- **arrow** → `__arrow`; invert `d_tags_skl__arrow` + `is_tskl` for the two
  sub-`a_tags_sort`; invert wf-arrow for the two sub-wf; two IHs.
- **forall (ε)** `pskl_all_syn P ⊑ᵖ[add ε Ψ0] all_etag ε ψ0` → `__all`
  (extends Δ — matches ppre's Δ-extension); sub-`a_tags_sort` from
  `d_tags_skl__all_etag` inversion at the fresh X; opens commute with
  `inh` painting.
- **hole** `pskl_hole ⊑ᵖ[∅] ψ` → `__hole`.  `a_tags_sort NM ∅ ψ` ⇒
  `d_tags_skl ∅ ψ` ⇒ ψ has NO `all_etag` (any `all_etag` forces a tag) ⇒
  `⌊ψ⌋` is ∀-free ⇒ **`inh ⌊ψ⌋ = syn ⌊ψ⌋`** (NEEDS helper
  `pskl_no_forall → pskl_to_bskl_inh = pskl_to_bskl_syn`; cf.
  `no_forall_bskl` (was predicates.v:97; DELETED 2026-08-06 as an unused
  duplicate — re-add if this route is taken), `ptyp_to_bskl_inh_syn_eq`
  prop_mono_bridge.v:78 — build the pskl analog).  Then `__hole` needs
  `Θ ⨟ ∅ ⊢ₚₛᵃ ⌊ψ⌋`: strip Δ from the wf premise via `Δ ∩ ftv ⌊ψ⌋ = ∅`
  (the ppre__hole side condition) + a wf Δ-strip lemma.
- **tophole_remove** `pskl_tophole P ⊑ᵖ[Ψ] ψ` → `__tophole_remove` + IH
  (same ψ, same Ψ; wf/tags unchanged).
- **tophole_fill** `pskl_tophole P ⊑ᵖ[Ψ] all_etag ε ψ0` → **VACUOUS**.
  `inh(all_etag ε ψ0)` erases to `bskl_all_inh(...)` but no `⊢ᵣᵃ`
  rule gives `∀◇· ⊳ all_INH ·` (tophole_fill of `ad_refine_syn` outputs
  `all_SYN`).  Exclude via NEW helper
  `ad_partial_precise_tags_sub : ad_partial_precise Θ Δ Ψ P ψ ->
   d_tags_skl Ψt ψ -> Ψ [<=] Ψt` applied to the RECURSIVE premise
  `∀◇P ⊑ᵖ[Ψ] open ψ0 X`: gives `Ψ ⊆ d_tags(open ψ0 X) = Ψt0`, but
  `a_tags_sort` gives `Ψ = add ε Ψt0` with `ε ∉ Ψt0` ⇒ `ε ∈ Ψ ⊆ Ψt0`,
  contradiction.  (`tags_sub` = ~40-line induction; flex_r case needs
  `d_tags_skl ∅ (ptyp_to_uskl_syn τ)` — painted monotypes are tag-free.)
- **tophole_keep** `pskl_tophole P ⊑ᵖ[Ψ] topholeg ψ0` → `__tophole_keep`
  (⌊topholeg ψ0⌋ = pskl_tophole ⌊ψ0⌋; needs `guarded_bskl (inh ⌊ψ0⌋)` +
  IH); `d_tags_skl__topholeg` passes tags through.
- **flex_l / flex_r** → `ad_refine_syn__flex_l` / `__flex_r`; sub-`a_tags_sort`
  on the def body's painting (tag-free for flex_r's monotype target).

Helpers to build first: (1) `ad_partial_precise_tags_sub` (Ψ⊆tags); (2)
`pskl_to_bskl_inh = pskl_to_bskl_syn` on a ∀-free pskl; (3) wf Δ-strip
under `Δ ∩ ftv = ∅` (check WF-SIDE-CONDITIONS.md / prop for an existing
`a_wf_pskl_strip`-style lemma before writing).

## 5.2 P5b-ii `ad_pat_sub_precise_subst` — statement + tag-flow (execute next)

Term-level substitution encoding (confirmed against `subst_uskl_in_uskl`,
def_ott.v:487 — replacement is a `uskl`, var is the `usklvar` α):
`S[ψa/α] = subst_uskl_in_uskl ψa α S`;
`S[Pa/α] = subst_uskl_in_uskl (pskl_to_uskl Pa) α S`.

```coq
Lemma ad_pat_sub_precise_subst : forall n NM M Ψ Ψa Ψ' Θ S α ψa Pa Q,
  ad_pat_sub_n n NM M (Ψ `union` Ψa) Θ (subst_uskl_in_uskl ψa α S) Q ->
  Θ ⨟ empty ⊢ₚᵣᵃ Pa ⊑ ⌊ ψa ⌋ˢ ->          (* precision Pa ⊑ ⌊ψa⌋ *)
  a_tags_sort NM Ψ' ψa ->                    (* Ψ' = ψa's tags *)
  Ψa [<=] Ψ' ->
  (* possibly: (NM = ty -> «Pa is a type») — add iff a case needs it *)
  ad_pat_sub_n n NM M Ψ Θ (subst_uskl_in_uskl (pskl_to_uskl Pa) α S) Q.
```

**Tag flow (RESOLVED — the paper elides it).**  In `ad_pat_sub`/`ad_pat_sub_n`
the tag context `Ψ` is *consumed into the consistency premises*: leaves
(Infer/UnivGhostR/Ghost/GhostG) force `Ψ = ∅`; **Arrow SPLITS**
`Ψ = Ψ1 ∪ Ψ2` (Ψ1 → the `∼` consistency premise, Ψ2 → the recursive
subtyping premise); Check sends all of `Ψ` to its `∼` premise; ForallL
GROWS the premise to `Ψ ∪ Ψ'` (the chosen instantiation's tags, `Ψ'`
fresh from `Ψ`).  So `Ψa` in `[Ψ,Ψa]` = **ψa's own tags**, sitting in the
subject and flowing to whichever consistency premise reads the ψa part.
`pskl_to_uskl Pa` is tag-free (no `all_etag`), so those `Ψa` tags vanish →
context drops to `[Ψ]`.  The paper's premises are correct as stated.

**Proof shape.**  Induction on the `ad_pat_sub_n` derivation, generalizing
`S`, `Ψ`, `Ψa` (`remember (subst_uskl_in_uskl ψa α S)`).  In each rule,
`destruct S`: the *structural* sub-case reconstructs the same rule with
`subst … (pskl_to_uskl Pa) α …` and recurses (fuel preserved); the **`S =
uskl_var α` sub-case is the crux** — the subject becomes `ψa` (resp.
`pskl_to_uskl Pa`), and the goal reduces to a **consistency/subtyping-side
precision fact**: a derivation on `ψa` (with tags `Ψa`) transfers to one on
`Pa` (tags ∅) using `Pa ⊑ ⌊ψa⌋`.  That crux likely needs a consistency
analog (reuse the `a_consis` theory / the sound-decorated-consistency
machinery) — budget it as a real sub-lemma, not a one-liner.  NB fuel is
preserved because the reconstruction is rule-for-rule; the crux case must
also preserve `n` (the ψa-derivation and the Pa-derivation have the same
height by precision — verify).

Finalize the exact form (esp. whether the `(NM=ty → Pa is a type)`
condition and empty-vs-general `Δ` on the precision premise are needed)
against how P6/complete-look actually invokes it (it feeds the ForallL
`refi` step, subtyping-proofs.tex:3416).

**Full decomposition (the "straightforward" hides a ~4-lemma metatheory
subtask — on the scale of the whole P5b-i effort).**  Traced by following
the actual induction; each substitution lemma's `S = uskl_var α` sub-case
is where the subject *becomes* `ψa`, and that is not an IH — it needs a
subject-precision lemma one level down:

1. **`ad_pat_consis_subject_precise`** (the base crux): `Ψt ⨟ Θ ⊢ₛᵃ ψa ∼ Q`
   + `Θ ⨟ ∅ ⊢ₚᵣᵃ Pa ⊑ ⌊ψa⌋ˢ` ⇒ `∅ ⨟ Θ ⊢ₛᵃ (pskl_to_uskl Pa) ∼ Q`.
   Output tags `∅` because `pskl_to_uskl Pa` has NO `all_etag` (tag-free);
   `Pa` is the *ghostier* skeleton (`⊳` = refine-toward-filled, so `Pa` has
   holes where `⌊ψa⌋` is concrete), and a ghostier subject is *more*
   consistent (holes ∼ anything).  Proof: induction on the consistency
   `ψa ∼ Q`, inverting the precision `inh Pa ⊳ inh ⌊ψa⌋` by its known RHS
   shape per case.  REAL WORK: the ∀◇ / hole / ∀ interplay (≈ the L-A
   soundness flavour); the hole sub-case needs `Q` to be an inh-painting,
   which `ψa ∼ Q` supplies.  NOT among existing lemmas
   (`ad_pat_consis_refine_syn_mono` etc. go consis→refinement with mono Q,
   the wrong direction).  ~150-250 lines.  BINDER DEVICE: the ∀-cases hit
   the Θ↔Δ tension (consis extends `Θ` with rigid `X`; precision's
   `refine_syn__all` extends `Δ`) — generalize over `Δ` and reuse the
   fill-hygienic refinement scaffolding (`prop_consis_sound.v:330`,
   `ad_pat_consis_refine_inh_gen`) that already moves an opened binder from
   the algo context into the refinement `Δ`.
   **TEMPLATE (KEY): `ad_pat_consis_refine_inh_gen` (prop_sub_sound.v:280,
   Qed) is the TARGET-side mirror of (1)** — `T ∼ Qt` + `Bsrc` refines to
   `Qt` ⇒ `T ∼ inh Bsrc`.  (1) is the SUBJECT-side version: same induction
   skeleton (`induction` on the refinement `inh Pa ⊳ inh ⌊ψa⌋`, `destruct`
   the painted skeleton, `try discriminate`), reusing `consis_transport_arrow`
   / `consis_transport_all` / `consis_unfold_def_join`, with the Θ'/Hmon/Hrig
   binder-monotonicity carriage — transporting the LHS subject instead of the
   RHS, and the subject's tags collapsing to ∅ (`pskl_to_uskl Pa` is
   tag-free).  So (1) is a template-follow (~150 lines), not greenfield.
   Output tag ctx is `∅`.  Also verify: consistency's ∀ has 4 variants
   (forall_inh/syn × tagged/untagged) vs the refinement's 1 `__all` — the
   precision inversion per consis-case selects the matching one.
2. **`ad_pat_consis_precise_subst`**: the general subject substitution on
   `ad_pat_consis` — induction on the deriv, `destruct S`; structural
   sub-cases recurse, `S = α` sub-case invokes (1).
3. **`ad_pat_sub_precise_subst`** (the P5b-ii target): induction on
   `ad_pat_sub_n`, `destruct S`; the `∼` premises (Infer/Check/Arrow-dom)
   invoke (2), the recursive `⩽` premises use the IH, `S = α` invokes a
   subtyping analog of (1).  Fuel `n` preserved (rule-for-rule).
4. (Possibly) a **subtyping subject-precise** base analog of (1) for the
   `S = α` sub-case of (3), if it doesn't reduce to (2).

RECOMMENDATION: execute (1) → (2) → (3) as its own focused pass (it is a
self-contained metatheory block), OR defer until P6 pins the exact form
`complete-look` needs — P6 may only require a restricted instance (e.g.
hole-free `S`, or `Δ = ∅`), which could collapse (1)'s hard cases.

## 5.3 P5b-ii crux — build status (2026-07-22)

Decomposed crux (1) into two steps; (1a) DONE.

- **(1a) `ad_pat_consis_strip_tags` — DONE** (prop_sub_complete.v, Qed,
  axiom-free): `Ψt ⨟ Θ ⊢ₛᵃ ψa ∼ Q → ∅ ⨟ Θ ⊢ₛᵃ (pskl_to_uskl ⌊ψa⌋ˢ) ∼ Q`.
  Strips the decorated subject to plain (`all_etag→all_syn`,
  `holeg→hole`, `topholeg→tophole`); tag ctx drops to ∅.  Helper
  `strip_uskl_open` (open-commute).  GOTCHA: `strip(topholeg R) =
  uskl_tophole(strip R)` (a plain tophole, use `__tophole`, not
  `__topholeg`); `strip(holeg) = uskl_hole` (use `__hole` with
  `pskl_hole`).
- **(1b) TODO `ad_pat_consis_subject_refine`**: `∅ ⨟ Θ' ⊢ₛᵃ
  (pskl_to_uskl Ptgt) ∼ Q` + `inh Psrc ⊳ inh Ptgt` (Psrc ghostier,
  i.e. `Pa ⊑ ⌊ψa⌋`) → `∅ ⨟ Θ' ⊢ₛᵃ (pskl_to_uskl Psrc) ∼ Q`.  KEY
  INSIGHT: ghost-free `Psrc` makes this trivial (`Psrc = Ptgt`), so the
  REAL content is **holey `Psrc`** — the hole/∀◇ cases are the point,
  not excludable.  Structure = outer induction on the refinement
  `inh Psrc ⊳ inh Ptgt` (destruct `Psrc`), with the Θ'/Hmon/Hrig binder
  carriage of `ad_pat_consis_refine_inh_gen`.  BUT the existing
  `consis_transport_arrow`/`consis_transport_all` transport the TARGET
  (subject fixed) — (1b) needs SUBJECT-analog transport helpers (inner
  induction on the consistency, `remember` the SUBJECT).  So ~3 new
  subject-transport helpers + the main lemma, ≈150 lines.  Hole case:
  `Psrc = hole` ⇒ `uskl_hole ∼ Q` needs `Q` inh-shaped OR a flex-var
  `Q` handled by `flex_r` + `consis_unfold_def_join` (the flex def
  unfolds to a wf paint).
- Then crux (1) `= (1a) ; (1b)` at `Ptgt := ⌊ψa⌋`; then the general
  subst (2) and the `ad_pat_sub` version (3) per §5.2.

**⛔ RETRACTED (2026-07-23): the "PIVOTAL FINDING" that (1b) /
precision-substitution is FALSE was WRONG — machine-refuted.**  The
claimed counterexample was `uskl_hole ∼ bskl_arrow (bskl_var α) Q2` with
`α` a defined flex, argued to be underivable because "`pskl_var α` is NOT
wf for a flex `α` (flex ≠ tvar)".  **That premise is false in this
codebase.**  `a_binds_tvar` (algo/def_extra.v:88-91) is a *disjunction*
that INCLUDES defined flex vars: `binds X abind_tvar ∨ binds X
abind_flex_mono ∨ ∃τ, binds X (abind_flex_mono_def τ)`.  So
`a_wf_pskl__var` accepts `pskl_var α` for a flex `α`, and therefore
`uskl_hole ∼ bskl_var α` (and `∼ bskl_arrow (bskl_var α) bskl_unit`) IS
derivable via `__hole` with `P = pskl_var α` (resp. `pskl_arrow (pskl_var
α) pskl_unit`).  Both machine-checked (`coqc` rc=0, scratchpad
`cex_check.v`).  The general principle: `κ`-defined flex vars are
monotype-defined ⇒ `a_wf_pskl`-able ⇒ `uskl_hole` stays consistent with
them.  So the hole sub-case of (1b) is fine for flex-var targets.

CONSEQUENCES of the retraction:
- Precision-substitution is a **genuine paper lemma**
  (`lemma:precision-substitution`, subtyping-proofs.tex:1664), stated
  exactly in the (1b)/§5.2 form — NOT a mech-only decomposition.  It is
  **not refuted**; status returns to "believed true, proof unfinished".
- **This is NOT a paper gap** (nothing goes in PAPER-GAPS.md): the error
  was a self-inflicted misreading of `a_binds_tvar`, not a paper problem.
- P6-first is no longer *forced* by any falsity argument.  It remains a
  reasonable engineering choice (P6 pins the exact `Q`-shapes (1b) is
  invoked at, which can still collapse (1b)'s hard cases), but ordering is
  now open — (1b) may well be provable in the general form after all.

- DONE toward (1b) (committed, Qed, axiom-free): `consis_subj_transport_arrow`,
  `consis_subj_transport_all` (subject-side transport helpers — still
  reusable).  The `tophole` helper needs a context-polymorphic transporter
  (its `tophole_inh` sub-case extends the context without opening the body)
  — a real binder issue, independent of the retracted finding.

## 5.4 Step (3) architecture — tag hygiene + the ⊑ᵤ subject-precision relation
   (worked out 2026-07-23; steps (1)+(2) are DONE and Qed)

Two structural findings, both discovered by tracing step (3)'s ForallL case
concretely.  READ BEFORE writing any step-(3) code.

**Finding A — the paper's `fresh Ψ'` is GLOBAL freshness, and the plain
fuel mirror cannot express it (hazard H4 materialized).**  In
`ad_pat_sub_n`, ForallL's freshness is only `inter Ψ' Ψctx = ∅`.  That is
too weak for precision-substitution: if a tag ε is shared between an
`all_etag` node of `S` (or of a LATER instantiation `ψ''` chosen inside
the derivation) and a tag of `ψa`, one can build a derivation where ε is
bookkept as solved-by-`ψa` (`ε ∈ Ψa`) but the `S`/`ψ''`-node with target
`all_inh` is FORCED to re-record ε after the substitution removes the
`ψa` copy — the conclusion is underivable and the lemma is FALSE without
freshness of `Ψ'` from BOTH the residual context `Ψ` and all other tags
in the subject/derivation.  Consequences:
- The consistency level is safe with a SYNTACTIC premise
  `inter Ψ' (ftag_in_uskl S) = ∅` — consistency has no ForallL, so no new
  tags appear inside a derivation.  (`ftag_in_uskl` = hand-written
  syntactic tag collector, `frost/def_extra.v` — a LEAF module over the
  generated syntax, so it can be used by def-files without a rebuild
  cascade.  It lived in its own `frost/def_tags.v` until 2026-08-06.)  This is how step (2) is stated and proved.
- The subtyping level ALSO introduces tags inside the derivation
  (ForallL's `ψ''`), whose freshness from `Ψ'` no premise about `S`/`ψa`
  can supply ⇒ step (3) must run over a **TAG-HYGIENIC fuel mirror**
  `ad_pat_sub_g`: same rules as `ad_pat_sub_n` plus, on both ForallL
  rules, `inter Ψ'' (ftag_in_uskl (subject)) = ∅` (instantiation tags
  fresh from the subject's own tags; freshness vs the ctx is already a
  rule premise).  Bridges: `_g → _n` trivial (drop premise); the reverse
  `ad_pat_sub_n → ad_pat_sub_g` is a TAG-FRESHENING lemma requiring a
  tag-renaming kit (rename ε→δ in uskl subjects + `d_tags_skl` /
  `a_tags_sort` / `ad_pat_consis` / `ad_pat_sub_n` rename lemmas; targets
  are `bskl` = tag-free, so targets are untouched; fuel rides along as in
  `ad_pat_sub_n_rename_tvar`).  DEFER the freshening bridge to a
  standalone final task: P6/P7 can run entirely over `_g`, and only the
  paper-facing corollary P7c consumes the bridge.

**Finding B — the subst-form of precision-substitution is too weak for
its own ForallL crux; use a subject-precision RELATION ⊑ᵤ instead.**  In
the crux (subject = `ψa` wholly) with last rule ForallL on `ψa`'s own ∀:
the premise subject is `open ψbody ψ''` and the reconstruction (for
`Pa = ∀.Pa0`) needs `open (paint Pa0) ψ'' ⩽ Q` — the changing part is
the WHOLE skeleton around `ψ''`, not the positions of a substituted
variable, so the `S[ψa/α] → S[Pa/α]` induction hypothesis does not
apply.  (Keeping `ψ''` decorated is forced: `is_tskl` forbids `all_syn`,
so re-instantiating with the stripped `⌊ψ''⌋` painting is not a legal
ForallL instantiation.)  Fix: define

```
uskl_precise (⊑ᵤ) : NM -> aenv -> atoms -> atoms(*Ψrep*) -> uskl -> uskl -> Prop
```

**REFINEMENT (traced 2026-07-23, late):** a monolithic leaf rule
`paint Pa ⊑ᵤ[Ψ'] ψ` does NOT survive the subst-compatibility proof —
substituting `[ψ''/X]` into a leaf whose precision mentions `X`
(`paint(open Pa0 X) ⊑ᵤ open ψbody X`, the exact crux instance) yields a
pair that is no longer painting-vs-ψ (decorated `ψ''` fragments appear
INSIDE the erstwhile painting), and re-deriving its precision is
precision-substitution itself — circular.  So ⊑ᵤ is a first-class
DECORATED-precision judgment mirroring `ad_refine_syn`/`ad_partial_precise`
on uskl pairs:
- an explicit REFL rule for identical (lc) decorated fragments — this is
  what the substituted `ψ''`-copies land on (var-X-vs-var-X → refl);
- congruence rules (arrow, all_syn/all_syn, all_etag/all_etag same tag,
  tophole, topholeg; cofinite binders extend Δ);
- the asymmetric ghostier-LHS rules mirroring the refinement: hole-vs-R
  (⌊R⌋ ∀-free + wf at ∅ — hence X-free, so subst-invariant ✓),
  tophole_remove / tophole_keep / tophole_fill-mirror (RHS `all_etag`,
  Ψrep passes through, as in `ad_ppre__tophole_fill`),
  all_syn-vs-all_etag (THE ∀-leaf: contributes ε + body tags to Ψrep),
  flex_l / flex_r def-unfoldings.
- Ψrep accounting: union at congruences (NO cross-copy disjointness —
  multiple `ψa` copies share tags), the RHS-decoration tags at the
  asymmetric rules.

Kit: reflexivity (Ψrep=∅), **subst-compatibility**
`⊑ᵤ at (add X Δ) → [ψ''/X] both sides → ⊑ᵤ at Δ` (the ForallL crux
enabler; provable rule-by-rule given the hole rule's X-freeness), and the
**embedding** `a_tags_sort NM Ψ' ψ → Θ ⨟ Δ ⊢ₚᵣᵃ Pa ⊑ ⌊ψ⌋ →
paint Pa ⊑ᵤ[Ψ'] ψ` (induction on the precision derivation, re-matching
erasure structure to decorated structure — all_syn↔all_etag,
tophole↔topholeg; ~150 lines).  `S[Pa/α] ⊑ᵤ[Ψ'] S[ψa/α]` then falls out
(congruence + embedding at each α position, refl elsewhere).

Then:
- **(2')** restate/reprove step (2) over ⊑ᵤ (same 15-case induction,
  inverting ⊑ᵤ per case instead of destructing `S`; leaf case = crux
  (1)).  Step (2) as proved (subst-form) stays as a corollary/template.
- **(3)** `ad_pat_sub_precise_subst` over `ad_pat_sub_g` + ⊑ᵤ, premises
  `Ψfull [=] Ψ ∪ Ψa`, `Ψa ⊆ Ψrep`, `inter Ψrep Ψ = ∅`,
  `inter Ψrep (ftag R') = ∅`, wf of the target threaded (as in (2)).
  Induction on the fuel-indexed derivation; congruence cases mirror (2);
  the leaf-ForallL case reconstructs with the SAME `ψ''` and recurses
  via subst-compat.  Two verified sub-points:
  - the subject's own root tag ε cannot lurk in `Ψa`:
    `ftag`-invariant on the PREMISE (`Ψfull∪Ψ'' ⊆ ftag ψbody ∪ Ψ''`)
    + `d_tags` uniqueness (`ε ∉ tags ψbody`) + hygiene (`ε ∉ Ψ''`)
    give `ε ∉ Ψfull ⊇ Ψa`.
  - `Ψa∖{ε} ⊆ tags ψbody` from `Ψa ⊆ Ψ' = {ε} ∪ tags ψbody`.
  Also needed: `ad_pat_sub_g_ftag_sub` (ctx ⊆ subject tags; ForallL case
  needs the general-opening upper bound
  `ftag(open R ψ) ⊆ ftag R ∪ ftag ψ`), and the TY side condition
  `(NM = TY → Pa is a type)` for the Check/guardedness reconstruction —
  exactly the paper's premise.

**Effort estimate:** ⊑ᵤ + kit ≈ 150 lines; (2') ≈ port of (2); `_g` def +
`g_of_n` + `g_ftag_sub` ≈ 150; (3) ≈ 400+ (leaf sub-analysis: ∀ / arrow /
hole / ∀◇-chains / flex / TY-type conditions); freshening bridge ≈ 300
(deferred).  2–3 focused sessions.

## 6. Status log

- 2026-07-29 (a2): **P6-Sv induction at 11/12 — only ARROW and
  ForallL-tagged remain, and NEITHER needs new infrastructure.**  Closed
  since (a1): the ρ-EXTENSION `uskl_rho_subst` (the paper's
  `ρ_b = ρ ∘ [ψ_b/β]`) together with `uskl_rho_subst_refl`, `uskl_rho_rename`
  and `uskl_rho_is_tskl`; and the CHECK case in full, including the sub-row
  where hazard H3 materialised.
  - The H3 sub-row (Pi = ∀◇Pi' with a FLEXIBLE body): `SolEq-Var` keeps the
    BODY's flexible rather than the payload's, so the output is ∀◇Pi' and
    its precision IS the input premise — modulo Ψa = ∅, which holds by the
    flexible-payload argument (κP0 mono ⇒ Q mono-ish ⇒ the consistency
    solves no tag), exactly P6-Cv's own FLEX row reused.
  - **Method note that keeps paying off**: every binder-family mismatch in
    this development dissolves the same way — instantiate at ONE fresh
    binder, then rename.  It is now used by `flex_shield_rename_l/_r`,
    `a_solve_sub_eq_rename` (ForallR's SolS-ForallR family),
    `uskl_rho_rename` (the ρ-extension's ∀ rows).  See (z5).
  - **Arrow** (next): `arrow_tag_split` (Qed) does the tag algebra; the LEFT
    premise goes to P6-Cv as in Check, the RIGHT to the IH.  Pi grid: arrow
    / □ (SolS-GhostLF) / ∀◇ / flexible / unit and ∀ impossible.  NOTE: the
    ∀◇ row needs NO inner induction — wf makes the ∀◇-body GUARDED, so it is
    unit/var/arrow and reduces to the other rows.  (P6-Cv needed a size
    induction there for unrelated reasons.)
  - **ForallL-tagged**: `uskl_rho_subst` + `flex_shield_descend_r` + the
    `fastep_all_r` prepend; Pi grid ∀ / ∀◇ / □, the last two as in
    UnivGhostLG.

- 2026-07-29 (a1): **P6-Sv induction at 10/12 — ForallR, Check (bar one
  sub-row), FlexMono and UnivGhostLG all closed.**  Kit added since (z4),
  all Qed: `a_solve_sub_complete_rho_var` (the ρ-leaf closer every case
  uses), `ad_ppre_guarded_topholeg_absurd`, `ad_ppre_hole_subject_tags`,
  `ad_ppre_tophole_strip`, `ad_ppre_lift_topholeg`,
  `a_solve_sub_hole_output`, `uskl_rho_guarded_erase`,
  **`ad_partial_precise_src_ftv_avoid`** (the ∀-cases' binder-stripping
  bound — note it must avoid `def_ftv Θ` and Θ's DEFINED flexibles, not
  merely `dom Θ`: P-FlexL puts a defined flexible into the subject and
  P-FlexR unfolds a definition), `a_non_flex_guarded_dec`, and the
  walk-indexed `flex_apart_walk` + `_here` / `_step` / `_weaken_tvar`.
  REMAINING: **Arrow** (delegates to P6-Cv exactly like Check, plus
  `flex_shield_arrow_inv` and the tag split Ψa_i := Ψa ∩ Ψ'_i, with
  `ad_partial_precise_tags_sub` giving Ψi_i ⊆ Ψ'_i) and **ForallL-tagged**
  (the ρ-EXTENSION case).  Plus one sub-row of Check — the WLOG hazard H3,
  see below.
  **ForallL needs the only piece of new infrastructure left**: a `uskl_rho`
  SUBSTITUTION lemma, since Sub-ForallL turns the guess's binder into a
  ρ-replaced variable and the instantiation into its image (the paper's
  `ρ_b = ρ ∘ [ψ_b/β]`).  Its `ρ = id` component `uskl_rho_subst_refl` is in
  the file with all non-binder rows proved; the two ∀ rows want a `uskl_rho`
  rigid-renaming lemma (per (z5): instantiate at one fresh binder, rename to
  build the family).  Tag bookkeeping is a BOUND, not an equation —
  `Ψρ' ⊆ Ψρ ∪ Ψb`, with `Ψb ⊆ Ψρ'` only when β actually occurs; the missing
  case is harmless because `ad_pat_sub_g_ftag_sub` plus ForallL's hygiene
  premise force `Ψb = ∅` when β is unused.
  **HAZARD H3 MATERIALISED (Check, Pi = ∀◇Pi').**  The paper writes "by
  congruence of constraint solving, we ASSUME refb is derived by
  SolEq-GhostGuarded" (subtyping-proofs.tex:1810).  Mechanically P6-Cv
  returns whichever derivation it built, so SolEq-FlexR must be handled too;
  `a_non_flex_guarded_dec` splits it, and only the sub-row where the
  ∀◇-body is ITSELF a flexible is still open (SolEq-Var then keeps the
  body's flexible, so the precision must come from the INPUT premise, which
  needs Ψa = ∅ by the flexible-payload argument plus `is_tskl`-preservation
  along `uskl_rho`).

- 2026-07-28 (z5): **METHOD RULE — "cofinite quantification prevents X" is
  never a valid argument in this development; the answer is always a
  RENAMING lemma.**  Recorded after (z4) stated one such claim and it was
  wrong.  Whenever two cofinite families must be crossed — a one-sided
  binder descent meeting a two-sided one, an existential-L conclusion whose
  inner set depends on an outer binder, a rule family offering a binder
  different from the one the induction picked — instantiate the family at a
  FRESH binder (making the nesting harmless) and rename it to the binder you
  need.  The rename is sound exactly when the fresh name does not occur in
  the parts you are not renaming, which is what freshness gives.  Instances
  already in the tree: `flex_shield_rename_l` / `_rename_r` (this is how
  `flex_shield_descend_l` / `_descend_r` cross the one-sided ∀ rows),
  `a_looksub_lookeq_rename_tvar` (P6-Cs's LE-ForallInh family from one
  instance), `ad_partial_precise_rename_tvar` (P6-Cv's tophole_fill
  family).  If a case looks blocked by binder bookkeeping, write the rename.

- 2026-07-28 (z4): **P6-Sv induction at 8/12; the last 4 are blocked on ONE
  structural question — the apartness invariant must be indexed by the WALK,
  not by syntax.**  Closed since (z3): Infer, UnivGhostR, GhostG (skmod
  forces P0 = □ ⇒ SolS-Vacuous), Ghost, UnivGhostL, ForallL-untagged (subject
  shape not `is_tskl` ⇒ vacuous), **UnivGhostLG** (full, incl. the `Pi = □`
  row the paper omits — see PAPER-GAPS) and **FlexMono** (unfold the
  definition on both sides, rebuild with P-FlexR).  New reusable kit, all
  Qed: `a_solve_sub_complete_rho_var` (the ρ-leaf closer used by EVERY
  case), `ad_ppre_guarded_topholeg_absurd`, `ad_ppre_hole_subject_tags`,
  `ad_ppre_tophole_strip`, `ad_ppre_lift_topholeg`,
  `a_solve_sub_hole_output`, `uskl_rho_guarded_erase`.
  **THE BLOCKER (found by starting ForallR; the experiment was made and
  REVERTED).**  The two ∀ cases must hand `flex_apart` — P6-Cv's premise,
  which P6-Sv only threads — to the recursive call across a ONE-SIDED
  descent (ForallR opens P0 and keeps the guess; ForallL instantiates the
  guess and keeps P0).  `flex_apart`'s ∀ rows are TWO-SIDED, and its clean
  row dies on the ForallL descent exactly as `fsh_clean` does.  Adding the
  one-sided rows + a `fa_flexfree` base to `flex_apart` was tried: the three
  new rows are absorbed by `flex_apart_topholeg_target_inv`,
  `flex_apart_tophole_p0_inv`, `flex_apart_arrow_inv` and
  `flex_apart_weaken` (the last needs "no new flexibles", free at the tvar
  extensions it is used at, plus a `flex_apart_weaken_tvar` wrapper) — but
  it leaves `flex_apart_all_etag_forall_inv` — P6-Cv's own TWO-sided descent
  — unprovable BY INVERSION, since its `fa_all_l` row offers a one-sided
  family where a two-sided one is wanted.  Experiment reverted (the tree is
  green); `prop_look_complete.v` is untouched pending the fix below.
  **THE FIX (settled 2026-07-28, after one false start).**  The two-sided
  descent IS available for `flex_shield`: `flex_shield_descend_both` is
  literally `_descend_r ; _descend_l` (Qed, six lines) — the guess's binder
  joins Δρ (from the subtyping side it IS ρ-replaced) and the payload's is a
  fresh rigid.  That suggested RETIRING `flex_apart` and re-stating P6-Cv
  over `flex_shield`.  ⚠️ **That is wrong, and the reason matters: P6-Cv has
  a SECOND caller.**  P6-Cs discharges P6-Cv's `flex_apart` with `fa_clean`
  at Δρ = ∅ (prop_look_complete_cstr.v:1750) against an arbitrary, possibly
  TAGGED guess; `fsh_clean` also demands tag-freeness, so the strengthening
  would break the CLOSED P6-Cs.  Rightly so: the tag half is a
  SUBTYPING-only concern — it exists because Sub-ForallL turns a tag into
  ρ-dirt, and consistency has no ForallL.
  **What was done instead** (in `prop_look_complete_sub_var.v`, no closed
  file touched): P6-Cv keeps `flex_apart`, P6-Sv keeps `flex_shield` for the
  tag half, and the Δρ half travels as **`flex_apart_walk`** — `flex_apart`
  at every state reachable by `fa_step`, which has one constructor per
  descent this induction performs (arrow-both, ForallR, ForallL with Δρ
  growing, ∀◇/∀◈, flexible unfolding).  Closure under a descent is
  `flex_apart_walk_step` (prepend), the P6-Cv delegation is
  `flex_apart_walk_here` (reflexivity).  `flex_apart` still cannot be
  DESCENDED — its two-sided ∀ rows tie both binders to one variable, and no
  rename fixes that (renaming aligns a pair; it does not manufacture a
  family) — but the walk-indexing never needs to descend it.

- 2026-07-28 (z3): **PREMISE WEAKENED — `flex_shield` as first built was TOO
  STRONG; new row `fsh_rho_var` added (all Qed, still axiom-free).**  Prompted
  by the "is the restriction too strong?" check.  Concrete instance the old
  form wrongly rejected: `ψa = ∀^ε β.β`, `P0 = α̂` (raw flex), `Pi = ∀β.β` —
  the algorithm SUCCEEDS there (precision forces `Pi = ∀β.β`; SolS-ForallL
  then **SolS-Var**, since the body is a VARIABLE, returns `Pa = ∀β.β`, whose
  precision against `∀^ε β.β` holds), yet no rule of the old relation
  applied.  Only a COMPOUND body (the counterexample's `β→β`) sends the solve
  to SolE-FlexR and destroys the information.
  FIX: `fsh_rho_var : α ∈ Δρ -> flex_shield Θ0 Ψ' Δρ P0 (uskl_var_f α)` — a
  ρ-replaced rigid variable is safe opposite ANY payload, because that is
  exactly P6-Cv's LEAF (the precision premise forces Pi to be that variable
  via `ad_ppre_delta_var_inv` + `msubst_pskl_var_inv`, SolS-Var/SolE-Var keep
  it, and the conclusion's precision is the var rule).  Consequences:
  `flex_shield` is congruent but NO LONGER ANTITONE in Δρ (`delta_anti`
  replaced by a direct `delta_cong`); `flex_shield_flex_leaf`'s conclusion
  becomes a DISJUNCTION (clean+tag-free ∨ ψa is a Δρ-var, the second
  disjunct routing to the leaf closer).  Both tests are now in the file:
  `flex_shield_excludes_cex` (the counterexample stays excluded) and
  `flex_shield_admits_var_body` (the succeeding shape is admitted).
  METHOD NOTE: check every mech-only side condition BOTH ways — that it
  excludes the known failure AND that it admits a known success.

- 2026-07-28 (z2b): **the three "impossible" cases are PAPER-CONFIRMED.**
  The decorated subtyping judgment of the paper (`decorated-algosub.tex`,
  rules `Var / ForallL / UnivGhostLG / Vacuous / Check / ForallR / Arrow /
  Flex`) has NO plain-□ row, NO plain-∀◇ row and NO untagged-∀ row: its
  ForallL subject is `∀^ε α.ψ` (tagged) and its ghost row is the DOTTED
  `UnivGhostLG`.  The P6-Sv proof text says so for the first of them
  verbatim ("The Ghost case cannot occur because ψa cannot contain □",
  subtyping-proofs.tex:1757).  The mech's `ad_pat_sub_g` carries all three
  extra rows because its `uskl` grammar also serves the UNRESOLVED skeleton
  R; against a decorated subject they are vacuous, discharged by `is_tskl`
  on all three `uskl_rho` disjuncts (refl / ρ-leaf image / congruence).

- 2026-07-28 (z2): **REPAIR BUILT — `frost/algo/prop_look_complete_sub_var.v`
  (new): `flex_shield` + its full descent kit, ALL Qed and axiom-free (0
  admits); the P6-Sv statement is restated with it and type-checks (main
  induction `Admitted`, case map in the file).**  Two corrections to (z)
  came out of building it:
  1. **A SECOND failure shape** (hand-verified, not yet machine-checked):
     `Pi = ∀β.((β→β)→⟨⟩)`, `P0 = α̂→⟨⟩`, `ψa = ∀^ε β.((β→β)→⟨⟩)`, `M = FN TC`,
     `κα̂ = ⟨⟩→⟨⟩`.  SolS-ForallL, SolS-Arrow, then SolE-FlexR on the
     ARROW-LEFT — a CONSISTENCY position — gives `Pa = ∀β.(α̂→⟨⟩)` and again
     `⟨⟩ ⊑ᵖ β`.  Pi's left component is an arrow, so SolE-Var does not
     shield it.  ⇒ the (z) "spine-only" reading is TOO WEAK (it guards only
     the result spine of P0), and a global "P0 flex-free ∨ ψa tag-free" is
     TOO STRONG (it rejects the legitimate `α̂→⟨⟩` vs `⟨⟩→∀^ε β.…`).
  2. So the premise is POSITIONAL with a tag-aware non-aligned base case:
     `flex_shield Θ0 Ψ' Δρ P0 ψa` — rules `fsh_clean` (ψa Δρ-clean AND
     Ψ'-tag-free; the ONLY rule for a non-aligned pair), `fsh_flexfree`
     (P0 has no raw Θ0-flexible), `fsh_arrow` (both sides), `fsh_all_l`
     (Sub-ForallR: P0 only), `fsh_all_r` (Sub-ForallL: ψa only, and it
     BAKES IN the ρ-growth `add α Δρ`), `fsh_tophole_l`, `fsh_topholeg_r`.
     It subsumes both halves of the invariant, so it replaces the (z)
     `flex_tags_apart` draft; `flex_apart` stays as-is for the P6-Cv
     delegation.
  **Proved (Qed, axiom-free):** `flex_shield_delta_anti/_cong`,
  `_weaken_tvar`, `_rename_l`, `_rename_r(_gen)`, `_arrow_inv`,
  `_topholeg_r_inv`, `_tophole_l_inv`, **`_descend_l`** (Sub-ForallR),
  **`_descend_r`** (Sub-ForallL), `_flex_leaf`, and **`flex_shield_excludes_cex`
  — the regression test that the premise rules the machine-checked
  counterexample out**.  KEY structural point: the two one-sided ∀ rules do
  NOT commute rule-by-rule, but each descent lemma's opposite-sided case
  goes through because the IH re-derives the other rule — that is why
  `flex_shield` is an inductive relation with both one-sided rows rather
  than a definition.  Ltac notes: the descents need `eapply` (ε/ψ are not
  determined by the conclusion), explicit `Δρ0 := add α Δρ0` instantiation
  (evar-fsetdec otherwise), and pick-fresh unions must be split with
  `solve_notin` FIRST — the 4-way-union `fsetdec` hangs (>600 s).
  NEXT: the main induction, per the case map in the file header.

- 2026-07-28 (z): **AUTHOR DECISIONS on (y): the `broom_flex_poly` program is
  REJECT-by-design (robustness bug only — declarative rejection verified,
  see the PAPER-GAPS entry), and the (y) premise is STRENGTHENED to the
  Ψ'-form: `flex_tags_apart Θ0 Ψ' P0 ψa` — flexible payload parts face
  TAG-FREE regions of ψa (Ψ' = `a_tags_sort`'s index = ALL of ψa's tags).**
  Call-site analysis (the "is it satisfied at call sites?" question):
  1. **Kills the cex, even more directly**: flex P0 admits only `fta_clean`
     ⇒ `ftag(ψa) ∩ Ψ' = ∅`; but for a TAGGED ψa, `d_tags_skl_ftag` gives
     `Ψ' ⊆ ftag(ψa)`, so Ψ' = ∅ — contradiction with ForallL's ε.  The
     ForallL flex-P0 row is vacuous without touching Ψi/Ψa bookkeeping.
  2. **No per-constraint rethreading**: unlike the Ψi-form, Ψ' is a
     PER-LOOK constant, so P6-Ss's constraint chain passes the same
     relation to every -Sv call; the a_solve_cstr threading does not
     change it.  The descent kit is the same congruence + all_etag-open
     lemmas as `flex_apart`'s.
  3. **Supplied at P6-L/P7**: at each flexible position of the counterpart
     P', the solution's own refinement premise pins the κ-image mono ⇒ the
     facing ψa-region is consistent with a mono-ish fill ⇒ mono-paint ⇒
     tag-free — the EXISTING monoish kit (`ad_refine_mono_paint_rhs_monoish`
     + `ad_pat_consis_monoish_counterpart`, plus a small `ad_pat_sub_g`
     analog) derives exactly this, positionally.  The backstop for the
     remaining shapes (rigid-∀-spine skeleton facing a bare flexible) is
     the flex-mono wall: by the author decision above, such programs are
     REJECTED (declaratively and algorithmically), so solutions with a
     tagged ψa-region facing a flexible payload simply do not exist at the
     theorem's call sites.
  4. Paper form of the side condition: "wherever P0 has a flexible
     variable, the corresponding position of ψa carries NO TAG" —
     mirroring the positional ρ side condition already on the lemma.

- 2026-07-28 (y): **IMPL EXPERIMENTS RUN — the (x) flip proposal is WITHDRAWN;
  the fix is STATEMENT-SIDE; P6-Sv restated with a `flex_tags_apart` premise
  (draft below).**  Built the artifact (`opam switch 5.4.0` + bindlib/
  multicont; `paper/artifact/implementation`) and tested the end-to-end
  claims.  Outcomes (full record: PAPER-GAPS.md "Correction" +
  "IMPLEMENTATION BUG" entries):
  1. `(fun x y -> y x) (id0 ids) useMono` — ACCEPTED.  Two errors in the (x)
     reachability story: I-App pre-shapes applied-λ binders via
     `guess_mono(skel(arg))` (never a bare flexible), and the PI pass
     ghost-erases top-level ∀s of argument skeletons to `∀◇(□→□)` — so the
     eq-payload never carries a rigid `∀β.β→β` and the mono route suffices.
  2. `h id0 3` (`h : ∀c.((∀b.b→b)→c)→c`) — rejected CORRECTLY: a TC-check
     against a guarded type is LS-Check = pure consistency (SHALLOW
     subtyping); declaratively rejected too.
  3. NEW impl crash (`broom_flex_poly`, separate PAPER-GAPS entry): a rigid
     ∀ kept under a constructor meets an inference-mode bare-flex binder and
     dies BEFORE any look — evidence the flex-mono wall guards the
     rigid-∀-spine + flex-payload combination upstream.
  **Conclusion:** the composed pipeline maintains invariants that keep the
  cex configuration out of real runs; the -Sv lemma is repaired by a premise,
  not by changing the algorithm.  **Draft statement** (mech shape; the NEW
  premise is `flex_tags_apart`):

  ```coq
  (* Flexible payload positions of P0 face TAG-UNSOLVED regions of ψa.
     Mirrors [flex_apart] (prop_look_complete.v:2603) with Ψi/ftag_in_uskl
     in place of Δρ/ftvar_in_uskl: same congruence rows (unit / rigid-var /
     hole / ∀◇ source / ∀◈ target / arrow / ∀-descents), and the ONLY rule
     admitting a FLEXIBLE P0-leaf is the clean one: *)
  Inductive flex_tags_apart (Θ0 : aenv) (Ψi : atoms) : pskl -> uskl -> Prop :=
  | fta_clean : forall P0 ψa,
      (ftag_in_uskl ψa) ∩ Ψi [=] empty ->
      flex_tags_apart Θ0 Ψi P0 ψa
  | fta_unit | fta_var_rigid (binds α abind_tvar Θ0) | fta_hole
  | fta_tophole | fta_topholeg_t | fta_arrow | fta_all_etag | fta_all_syn
    (* … verbatim the flex_apart congruence shapes … *).

  Theorem a_solve_sub_complete_var :   (* P6-Sv, subtyping-proofs.tex:1696 *)
    forall n NM M Θ0 Θ κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0,
    a_wf_aenv Θ -> a_wf_aenv Θ0 ->
    Θ0 ⨟ empty ⊢ₚₛᵃ Pi -> Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
    (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->   (* skmod[N]{P0}{M} *)
    (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
    κ ∷ Θ0 ⊑ Θ ->
    uskl_rho NM Θ Δρ Ψρ ψsub ψa ->
    a_tags_sort NM Ψ' ψa ->
    Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψsub ⌋ˢ ->            (* subject wf — the P6-Cs lesson *)
    Ψi `union` Ψa [=] Ψ' ->                (* the paper's Ψi,Ψa = Ψ' (EQUATION) *)
    Ψρ ∩ Ψ' [=] empty ->
    rho_fresh Δρ Θ κ -> Δρ [<=] Δ ->
    (forall α, α `in` Δρ ->
       α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
    delta_def_fresh Δ Θ ->
    flex_apart Θ0 Δρ P0 ψa ->              (* P6-Cv's invariant, unchanged *)
    flex_tags_apart Θ0 Ψ' P0 ψa ->         (* NEW: the reachability premise —
       STRENGTHENED 2026-07-28 (z) to index by Ψ' (ALL of ψa's tags), not Ψi:
       flexible payload parts face TAG-FREE regions of ψa.  See the (z)
       call-site analysis below for why this form is both supplied and
       simpler to thread. *)
    Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa ->
    Ψsub [<=] Ψρ `union` Ψa -> Ψa [<=] Ψsub ->
    ad_pat_sub_g n NM M Ψsub Θ ψsub Q ->
    Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
    exists Pa, Θ0 ⊢ₛ Pi ≼[ M ] P0 ⤳ Pa /\
      Θ ⨟ Δ ⊢ (msubst_pskl κ Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa.
  ```

  Why this premise is exactly right:
  - **Kills the cex** (`cex_p6sv_forall_flex.v`): there `P0 = α̂` (flexible)
    and `ψa = ∀^ε β.β→β` with `Ψi = {ε}`; the only `flex_tags_apart` rule
    matching a flexible P0 is `fta_clean`, which demands
    `{ε} ∩ {ε} = ∅` — unsatisfiable.  The cex file becomes the regression
    test that the premise excludes the configuration.
  - **Makes the ForallL flex-P0 case VACUOUS**: `fta_clean` gives
    `ε ∉ Ψi`; the paper's own argument (`ε ∉ Ψa` since ForallL discards
    ε + the equation `Ψi,Ψa = Ψ'`) gives `ε ∈ Ψi` — contradiction.  The
    non-flex-P0 rows proceed exactly per the paper (refinement inversion
    forces P0's shape; the P6-Cs strip kit).  KEY mech fact backing the
    vacuity: in `ad_partial_precise`, tags enter Ψ ONLY via `ad_ppre__forall`
    (rigid-∀ match); `ad_ppre__tophole_fill` adds NO tag — so `Ψi ≠ ∅`
    forces a rigid-∀ in κPi at a tagged position, which is what real runs
    never pair with a flexible payload.
  - **Positional, not global**: the arrow case splits it per component
    (a flex P02 with tag-solved ψ1 on the OTHER side is fine), matching
    how `flex_apart` splits; the ∀-descents need `fta` open-descent lemmas
    mirroring `flex_apart_guarded_all_etag_descent`.
  - **Paper form**: one more positional side condition on the -Sv lemma,
    mirroring the existing ρ one: "wherever P0 has a flexible variable, the
    corresponding position of ψa carries no tag of Ψi."
  Obligations to discharge later (registered): (i) `fta` congruence +
  descent + weakening kit; (ii) P6-Ss threads it per-constraint (whether
  the CONCLUSION must return an `fta`-maintenance fact — decide when
  drafting P6-Ss); (iii) **P7 must SUPPLY it** — the pipeline argument:
  sub-payload flexibles sit on the result spine; pipeline Pi-spines are
  ghost-erased (∀◇), so spine tags never enter Ψi via `ad_ppre__forall`;
  the rigid-∀-spine + flex-payload combination is stopped upstream by the
  flex-mono wall (the `broom_flex_poly` shape) — the LAST part depends on
  how WT resolves the impl crash, so P7's supply proof is the place this
  gets tested.

- 2026-07-28 (x): **⛔ P6-Sv IS BLOCKED — the paper's
  `lemma:complete-constraint-collection-solving-var` (subtyping-proofs.tex
  :1696) is FALSE as an isolated statement, machine-checked in
  `frost/algo/cex/cex_p6sv_forall_flex.v`
  (`p6sv_with_p6cv_premises_is_false`, Qed, axiom-free).**  Work on P6-Sv is
  STOPPED pending an authors' decision; P5 / P6-Cv / P6-Cs are unaffected
  (no ForallL ⇒ ρ never grows there).
  - Witness (ρ = IDENTITY, `Δρ = ∅`): `Θ0 = α̂`, `Θ = α̂ := ⟨⟩→⟨⟩`,
    `κ = [α̂ ↦ ⟨⟩→⟨⟩]`, `N = TY`, `M = TC`, `Pi = ∀β.β→β`, `P0 = α̂`,
    `ψa = ψsub = ∀^ε β.β→β`, `Q = inh{⟨⟩→⟨⟩}`, `Ψ' = Ψi = {ε}`,
    `Ψa = Ψsub = Ψρ = ∅`, `Δ = ∅`.  All premises hold — including every
    premise of the CLOSED consistency twin (`flex_apart`, the subject-wf
    premise, and the tag EQUATION `Ψi,Ψa = Ψ'`).  The algorithm is forced to
    `Pa = ∀β.α̂` (a `∀` is not `guarded`, so only SolS-ForallL applies; the
    body goes SolS-Check + SolE-FlexR), whose precision obligation reduces to
    `⟨⟩ ⊑ᵖ β`.  Refuted for EVERY `κa : Θ0 ⊑ Θ` via the file's general lemma
    `mono_paint_ppre_target_ftv` (a mono-paint subject is never precise to a
    target mentioning a variable outside Θ).
  - **Why §7's plan cannot be patched:** `flex_apart` (and any invariant
    stated at the CURRENT `ψa`) is destroyed by the ForallL descent — it adds
    `β` to `Δρ` while `P0` is NOT decomposed, so a raw-flex `P0` that was
    legitimately `fa_clean` before the descent faces a Δρ-dirty `ψa` after
    it.  A stable invariant would have to forbid a raw Θ0-flex `P0` facing
    ANY *tagged* `ψa` (a tagged `ψa` becomes dirty one ForallL step later),
    and that is not derivable at the P6-Ss call sites.
  - **Why the 2026-07-25 "unreachable" resolution
    (`cex_p6_flex_freshened.v`) does not cover it:** (i) here ρ is created by
    the completeness proof's OWN ForallL (`ρb = ρ ∘ [ψb/β]`), not by
    constraint collection; (ii) the raw flexible payload arrives from
    **LS-Var**, and `a_looksub` has no FlexR rule at all, so nothing
    freshens it on the subtyping route; (iii) the paper's positional side
    condition ("Pi has the same rigid variable in the same position") HOLDS
    all the way down (`Pi = β→β` vs `ψa = β→β`).
  - Registered in docs/PAPER-GAPS.md (final entry).  **RESOLUTION PROPOSED
    (2026-07-28, same day, after re-reading the paper's fig:constraint-solving,
    the consistency -var Arrow case, and type.ml): flip `SolE-FlexR`'s output
    to keep the NON-flexible side** — `nonflex{P} ⊢ solveeq{P}{α̂} ⤳ P`.  It
    is the only solve rule where the payload replaces a structured subject;
    under a SolS-ForallL descent that discards binder-local rigid info no
    α̂-solution can express.  With the flip every flex-payload completeness
    case closes from the PRECISION PREMISE (`Ψa = ∅` is forced since a mono
    payload solves no tags), P6-Cv's mech-only `flex_apart` premise becomes
    droppable, and the earlier "unreachable-configuration" machinery
    (cex_p6_flex_counterpart / cex_p6_flex_freshened) is retired.  Freshening
    the payload instead does NOT work (a fresh γ̂ ∈ Ξ is equally out of the
    binder's scope); a statement-side premise cannot exclude the reachable,
    declaratively-solvable top-level instance.  Full argument + impact plan in
    PAPER-GAPS.md.  AWAITING coauthor sign-off (algorithm change).

- 2026-07-27 (v): **TASK A DONE — accumulated-skeleton invariant PROVED,
  axiom-free, in `algo/prop_accum_no_hole.v`.**  *(SUPERSEDED: the
  `pskl_no_hole P0` premise was removed later the same day, so the
  invariant became obsolete and its file was DELETED 2026-07-27; entry
  kept as the record of what was proved.)*  Discharges the P6-Cs
  disjunctive premise `P0 = □ ∨ pskl_no_hole P0`; deep-mixed `P0` is NOT
  reachable.  A1 `a_guess_hnh`, A2 `a_look_payload_hnh` (mutual), A3
  `a_solve_cstr_hnh` (+ `_hole_start`; generalises `a_solve_eq_no_hole_p0`
  to the sub/eq/cstr block), A4 `a_sub_a_sub_flex_no_hole_p0`.  **Key design
  point on A4:** stated SUBJECT-FREE (`nh P0 → nh Q`) — output holes come
  only from the counterpart, so `a_sub__forall_l` merely threads `P0` and the
  ∀-body instantiation `open P P1` (possibly `□`-deep-mixed in `sk` mode) is
  irrelevant to the output; `Infer`/`UnivGhostR` (`P0 = □`) fall out by
  `pskl_no_hole □ = False`.  The disjunctive `hnh` form is needed only at the
  solve layer (accumulator starts `□`, `SE-GhostL`/`SE-VacuousR` pass the
  □-disjunct); a_sub/a_consis use the strict counterpart-only form.  See
  WF-SIDE-CONDITIONS.md §"pskl_no_hole P0", item 2.  **Next: Task B (P6-Cs).**

- 2026-07-27 (u): **P6-Cv CLOSED — `a_solve_eq_complete_var` is axiom-free
  ("Closed under the global context"), zero admits.**  The three ForallSyn
  Pi-rows all landed; `a_solve_eq_complete_var_gen` is `Qed`.  Home:
  `frost/algo/prop_look_complete_var.v` (renamed from the cex scratch).
  The kit that closed it:
  - **`ad_partial_precise_rename_tvar`** (aenv-tvar Z↦W rename for
    `ad_partial_precise`, ~60-line induction; flex cases need `Z,W∉ftv τ`,
    supplied via `a_wf_aenv_def_ftv_dom`).  This is what builds the
    `ad_ppre__tophole_fill` cofinite family (binder in the AENV) from the
    SINGLE IHX instance — the missing lemma §6(t) flagged.
  - **`pskl_no_hole P0` premise** added to `_gen` + corollary (a genuine
    wf/scoping side-condition, consistent with the pre-existing
    `a_solve_eq_no_hole_p0` invariant).  It gives `bskl_no_hole` for the
    `ad_refine_syn_aenv_to_delta` transport (`inh(□)=bskl_hole`, so a
    guarded-but-holey P0' would otherwise block moving X into Δr).  Threaded
    through every recursive `IHHconsis`/`IHn`/`CORE`/IHX site.
  - **∀◇ row** (UnivGhost): wrapped IHX (Pi0:=∀◇.Pi', P0i:=∀◇.P0'); solve =
    IHX output via `tophole_both` (strengthen_tvar; 3-subgoal inversion, the
    2 extra guarded-tophole cases killed by `inversion Hg`); precision =
    `ad_ppre__tophole_fill` + rename_tvar family (X-freshness of the fixed
    subject via `a_solve_sub_eq_ftv` + `a_wf_pskl_ftv_dom` +
    `msubst_pskl_ftv_avoid`).
  - **□ row** (GhostL): solve = `a_solve_eq__hole_l` (Pa:=∀◇.P0'); IHX with
    Pi0:=□ (Hpre0x = `ad_ppre__hole`); same tophole_fill + rename closure.
  - **∀ row** (ForallGhost): solve = `a_solve_eq__all_l_tophole` (RHS ∀◇.P0'
    KEPT & X-free ⇒ `subst_fresh_eq` on the RHS in the rename); IHX at
    Δx:=add X Δ (X∈Δ ⇒ the Δ-var **FOLD** applies, NOT rename_tvar);
    precision conclusion = `ad_ppre__forall` (Pa = ∀.close).
  One ε-metavariable from a tophole_fill family member is genuinely
  unconstrained (any ε inhabits the same family); discharged with `Unshelve;
  exact ε` at KEYF-close.  The abandoned split-B permute lemmas
  (`a_wf_aenv_insert_mid_tvar`, `a_inc_*_tvar_prefix`) were deleted as dead.
  NEXT: fold into `prop_look_complete.v` proper / add to README.v index;
  register the `pskl_no_hole P0` side-condition.

- 2026-07-26 (t): **CORRECTION to §6(s): NO exchange lemmas — split-A is the
  right recipe; ForallSyn IHX REBUILT & compiling (3 clean admits, ~20s).**
  §6(s)'s split-B (`Θtv_ih:=Θtv`, `Θr_ih:=(X~tvar)++Θr`) is IMPOSSIBLE: H0's
  aenv is FIXED at `(X~tvar)++Θ = (X~tvar)++Θtv++Θr` (X at FRONT), and the
  split equation `(X~tvar)++Θ = Θtv_ih ++ Θr_ih` forces `Θtv_ih` to be a
  PREFIX starting with X — so `Θtv_ih := Θtv` (starts with a non-X binder)
  can never satisfy it.  The 3 exchange lemmas were built (`a_wf_aenv_
  insert_mid_tvar`, `a_inc_{strip,build,insert}_tvar_prefix`, all Qed) but
  are UNUSED — kept as harmless kit.
  **Split-A (CORRECT): `Θtv_ih := (X~tvar)++Θtv`, `Θr_ih := Θr`,
  `Θ0r_ih := Θ0r`, `Δr_ih := add X Δr`.**  The split eq `(X~tvar)++Θ =
  ((X~tvar)++Θtv)++Θr` is VALID (X stays at front), gives the TIGHT family
  premise `dom Θr` DIRECTLY (no `add X`, no `dom Θtv` gap), and feeds every
  fixed-aenv premise (wf/inc/rho/precision) at `(X~tvar)++Θ` exactly as the
  nil-approach did.  DECISIVE CONFIRMATION: the already-CLOSED
  `forall_inh_tagged` IHX uses split-A verbatim (`((X~tvar)++Θtv) Θr Θ0r`,
  `Δr:=add X Δr`, refinement `apply Hreff`) — ForallSyn now mirrors it.
  The ONLY ForallSyn-specific twist is the refinement: P0=∀◇.P0' makes
  `Hrefine` a `tophole_fill`, so `Hrefb` = its inverted body at
  `(X~tvar)++Θr ⨟ Δr ⊢ᵣᵃ bskl_tophole(paint P0') ⊳ open Q X`, and each row
  moves X into Δr by `ad_refine_syn_aenv_to_delta` — which WORKS on the
  tophole subject because `bskl_no_hole (bskl_tophole A) = bskl_no_hole A`
  (guarded body ⇒ no hole).  Rows use the WRAPPED IHX (Pi0:=∀◇.Pi',
  P0i:=∀◇.P0'): the IHX solve output IS the outer solve (strengthen_tvar,
  no SE-rule), and the precision fill matches HF directly (no strip).
  **THE SOLE REMAINING BLOCKER (all 3 rows): the ForallSyn precision
  conclusion is `∀◇.PaX ⊑ᵖ uskl_all_etag ε ψR`, closed by
  `ad_ppre__tophole_fill` — whose cofinite premise binds X' in the AENV
  (`(X'~tvar)++Θ`), keeps Ψ, adds NO ε (so "ε is Ψ'-only" holds).  But IHX
  yields ONE instance at `(X~tvar)++Θ`; building the X'-family needs an
  AENV-tvar rename of `ad_partial_precise`.  `ad_partial_precise_rename`
  renames only Δ-vars (needs `Xr ∈ Δ`); `strengthen_tvar_mid` removes an
  aenv-tvar only when it is ALSO in Δ; no `delta_to_tvar` promotion exists.
  NEXT: build `ad_partial_precise_rename_tvar` (aenv-tvar Z→W rename, ~60-
  line induction mirroring `ad_partial_precise_rename` but with the aenv as
  `Θ1 ++ (Z~tvar) ++ Θ0`; flex cases need `Z,W ∉ ftv τ` side-conditions;
  tophole_fill/forall push the binder with `Θ1':=(X~tvar)++Θ1`).  Then a
  FOLD-tvar (strengthen-free: subject `msubst κ PaX` is X-free, so rename
  only re-points the aenv-tvar + opens the target) closes the tophole_fill
  family — the SAME kit unblocks □ (hole_l, Pa:=∀◇.P0') and ∀
  (all_l_tophole, P0i:=∀◇.P0' KEPT + FOLD).  Backups: p6cv_working8_
  splitA_rows_admit.v (clean 3-admit).

- 2026-07-26 (s): **CORRECTION to §6(q)/(r): the `Θtv_ih := []` recipe is
  WRONG for the family premise — the permutation IS needed after all.**
  `Θtv_ih := []` makes `Θr_ih = (X~tvar)++Θ`, so `dom Θr_ih = dom Θ` and
  the IH's family premise is `S ∩ add X (dom Θ)`.  Discharging that from
  the outer family needs `S ∩ dom Θtv = ∅`, which forced strengthening
  the `_gen` conclusion family premise from `S ∩ dom Θr` to `S ∩ dom Θ`
  — and that CASCADE-BREAKS the already-proven ForallInh ROW B, whose
  per-X' fold provides `S_arg := add X' S` to the IH assuming its family
  premise is `dom Θr` (X'-free); with `dom Θ` the premise contains X'
  (`(add X' S) ∩ add X' (dom Θ) ⊇ {X'} ≠ ∅`).  Machine-verified: the
  `dom Θ` change compiled through the base/absurd/flex/□ cases but died
  at ForallInh ROW B.
  **CORRECT fix (revert to permutation):** ForallSyn's IHX must use
  `Θtv_ih := Θtv`, `Θr_ih := (X~tvar)++Θr`, so `dom Θr_ih = add X (dom Θr)`
  — X'-free of Θtv, matching the outer `dom Θr` family premise with
  `X ∉ S`; NO `dom Θ`, NO ForallInh breakage.  The cost is the
  consistency aenv is `(X~tvar)++Θtv++Θr` (rule prepends X) while the IH
  needs it at `Θtv++(X~tvar)++Θr` (X adjacent to Θr), same `binds` — so
  3 exchange lemmas for a fresh mid-inserted tvar: `ad_pat_consis` (via
  the existing binds-monotone `ad_pat_consis_weaken`, both directions),
  `a_wf_aenv` (fresh-mid-insert), and `a_inc` (fresh-mid-insert — the
  trickiest).  All LOCAL to forall_syn_tagged.  NEXT SESSION: prove the
  3 exchange lemmas, redo the ForallSyn IHX with `Θtv_ih := Θtv`, then
  the 3 Pi-rows (the □-row is already written and worked against the
  `dom Θ` variant — re-point its IHX family plumbing to `add X (dom Θr)`).
  State is reverted to the clean 3-admit `p6cv_working4.v` (compiles 20s).

- 2026-07-26 (r): **`forall_syn_tagged` built DOWN TO its 3 Pi-rows; full
  scratch compiles (20s, 3 clean admits).**  Done + verified (backup
  `p6cv_working4.v`): the two `flex_apart` target-descent lemmas
  (guarded ∀◇-body excludes the all_syn source that blocks descent); the
  KEYF preamble + tag algebra (simpler than ForallInh — `ε ∉ Ψ`, so
  `Ψa ⊆ Ψ0'` is direct, no ε-split); `HψaB` from the reconstructed ρ;
  the P0-grid absurd columns (`allsyn_rhs_absurd` + rigid K17) and the
  `P0 = □` VacuousR column; and the `P0 = ∀◇` column INFRASTRUCTURE — the
  refinement transport `Hreff` (tophole_fill inversion yields BOTH the
  `tophole_remove` goal [absurd — a guarded body cannot refine to
  `all_syn`, killed per-shape after `inversion HgP0'`] and the
  `tophole_fill` goal, transported by `ad_refine_syn_weaken` +
  `ad_refine_syn_delta_absorb`) and the IHX wrapper (`Θtv_ih := nil`,
  `Θr_ih := (X~tvar)++Θ`, `Δr_ih := empty`, `Δx` a parameter, refinement
  passed explicitly).  Ltac gotcha: after `inversion Hrefine`, the
  cofinite premise must be referenced by its assigned name (`H5`/`L0`),
  not via a `_ ⨟ _ ⊢ᵣᵃ _ ⊳ _` match pattern under the binder — that
  pattern silently fails to bind.
  **THE REMAINING OBSTACLE (fix before the 3 rows): the family premise
  must strengthen from `S ∩ dom Θr = ∅` to `S ∩ dom Θ = ∅`.**  The IHX's
  `Θtv_ih := nil` makes `dom Θr_ih = dom Θ`, so the IH's family premise is
  `S ∩ add X (dom Θ)`; the outer family only provides `S ∩ dom Θr`, gap
  `S ∩ dom Θtv`.  Strengthening the `_gen` conclusion family premise to
  `S ∩ dom Θ` closes it uniformly: producers still discharge it
  (`weaken_fresh` needs only `S ∩ ftv ⊆ S ∩ (dom Θr ∪ Δρ) ⊆ S ∩
  (dom Θ ∪ Δρ)`), ForallInh's IH provides the stronger `S ∩ add X dom Θ`
  from its own `HS2` + `X ∉ S`, and the corollary is unaffected
  (`Θtv = [] ⇒ dom Θ = dom Θr`).  It is an 8-site coordinated edit
  (statement + every case's nested KEYF/IHX/FOLD family premise) + the
  `HS2`-use re-thread.  (NOT a `dom Θtv ⊆ Δ` premise — that FAILS for
  ForallInh's □/∀◇ rows, where the binder enters `Θtv` but not `Δ`.)
  Then the 3 Pi-rows: □ (GhostL, per-X' IHX rerun, `ad_ppre__tophole_fill`
  conclusion), ∀ (ForallGhost `a_solve_eq__all_l_tophole` +
  `a_solve_sub_eq_rename`, Δ-grow `ad_ppre__forall`), ∀◇ (UnivGhost
  `a_solve_eq__tophole_both`, refinement ∀◇-strip, `ad_ppre__tophole_keep`).

- 2026-07-26 (q): **`forall_syn_tagged` UNBLOCKED — the §6(o) open question
  resolved WITHOUT a statement change.**  The fear was that ForallSyn's
  `P0 = ∀◇.P0'` refinement uses `tophole_fill`, which grows the
  refinement's aenv to `(Z~tvar)++Θr`, breaking the split's "refinement
  at Θr" invariant.  RESOLUTION: **put the ForallSyn binder Z into the
  Θr side of the split, not Θtv.**  The split's real invariant is
  *"Θtv = binders the refinement does NOT see (ForallInh binders, which
  grow Δ/precision but never the refinement); Θr = the original context
  PLUS binders the refinement DOES see (ForallSyn binders, introduced by
  the refinement's own tophole_fill)."*  Consequences (all checked):
  - The IH call for ForallSyn uses `Θtv_ih := Θtv` (unchanged),
    `Θr_ih := (Z~tvar)++Θr`, `Θ0r_ih := (Z~tvar)++Θ0r`.  Then the _gen
    refinement premise `Θr_ih ⨟ Δr ⊢ᵣᵃ …` is literally `refb` (Z in the
    aenv via tophole_fill; Δr = dom Θtv unchanged since tophole_fill
    doesn't touch Δ).  NO statement change.
  - The family premise `S ∩ dom Θr = ∅` auto-covers Z once Z ∈ dom Θr,
    so no new freshness premise is needed.
  - The already-proven ForallInh case still holds with a Θr that
    contains ancestor-ForallSyn binders: `refine_primary_to_plain`
    weakens `Θr ⊆ Θ` regardless, and the □-row's
    `ftv ψa ⊆ dom Θr ∪ Δρ` weaken-fresh uses exactly `S ∩ dom Θr = ∅`.
  - **Cleaner still — NO permutation needed.**  Take
    `Θtv_ih := []`, `Θr_ih := (Z~tvar)++Θ` (= `(Z~tvar)++Θtv++Θr`),
    `Θ0r_ih := (Z~tvar)++Θ0`, `Δr_ih := empty`.  Then
    `Θ_ih = Θtv_ih ++ Θr_ih = (Z~tvar)++Θ` is exactly the consistency
    rule's prepended aenv — Z stays at the FRONT, so `Hconsis`,
    `HwfΘ_ih` (via `a_wf_aenv__tvar`), and `Hκ_ih` (via `a_inc__tvar`,
    Ξ=[]) all hold with NO exchange lemmas.  `Htvs_ih` is vacuous (empty
    Θtv), `Δr_ih [=] dom [] = empty`, `inter Δρ (dom []) = empty`.  The
    refinement premise is at `Θr_ih ⨟ Δr_ih = ((Z~tvar)++Θ) ⨟ empty`:
    obtain it from `refb` (at `(Z~tvar)++Θr ⨟ Δr`) by
    `ad_refine_syn_weaken` (`(Z~tvar)++Θr ⊆ (Z~tvar)++Θtv++Θr` by
    append-binds) then `ad_refine_syn_delta_absorb` to drop `Δr = dom Θtv`
    into the aenv (its binders are the Θtv-tvars, now present in Θr_ih).
    Both lemmas already exist.  Trade-off: the IH's tight-Θr is "given
    up" (dom Θr_ih = add Z (dom Θ)), but the family premise correspondingly
    tightens to `S ∩ add Z (dom Θ) = ∅`, and ForallSyn's conclusion is
    built by aenv-grow (`ad_ppre__tophole_fill`), not Δ-transfer, so it
    never needed the tight Θr.  Entirely LOCAL to forall_syn_tagged.
  Remaining to implement: the case body (mirrors ForallInh's KEYF/IHX/
  FOLD but with ForallSyn's solve rules — SS-ForallGhost
  `a_solve_eq__all_l_tophole`, SS-GhostL, SS-UnivGhost — and P0 grid
  `{∀◇.P0' (tophole_fill), □ (□-fills-to-∀), flex-chain}`); the Z-into-Θr
  permutation lemmas; the ForallSyn conclusion precision via
  `ad_ppre__tophole_fill` (grows the aenv, NOT Δ — so NO ∀S-family
  Δ-transfer issue here, unlike ForallInh).

- 2026-07-26 (p): **REPAIR PHASE 3b — `forall_inh_tagged` (case 1) CLOSED;
  `_gen` now 14/15 (only `forall_syn_tagged` admit); dev scratch compiles
  in 19.6s.**  Built per the §6(o) recipes: KEYF continuation, ε as a
  Ψ'-solved tag (`Ψa' := remove ε Ψa`), the P0-grid (only P0=∀.P0b
  survives), the shared IHX (body-IH wrapper) + FOLD (per-instance
  strengthen→rename→rewrite fold), and rows A (Pi=∀), B (Pi=□), C
  (Pi=∀◇-fill).  Two engineering findings worth keeping:
  - **Row B (Pi=□) cannot use FOLD.**  The □-rule's target
    `open ψR (var X)` contains X, so its precision premise is only
    derivable at Δ (not `add X Δ`); the body-IH therefore runs with X ∉
    its Δ-set, so `ad_partial_precise_rename` (needs `Xr ∈ Δ`) does not
    apply.  Row B keeps the PER-X' IH rerun instead; its solve is a
    single `a_solve_eq__hole_l` (Pa := ∀.P0b, no cofinite reassembly).
  - **Running the giant IH under a binder hangs `destruct`.**  The same
    `destruct (IHX …)` is instant at a row's top level but hangs inside
    the ∀-fold body (bloated context).  Fix: `clear FOLD` (the unused
    giant) before Row B's destruct; rows A/C run IHX at the top and FOLD.
  New kit (Qed, scratch): `a_wf_pskl_delta_to_tvar(_mid)`,
  `a_inc_image_ftv_dom`.  **Slowness (was >4min → 19.6s):** the case was a
  chain of ~6 hung/slow sentences, each an instance of four patterns —
  fsetdec-on-a-giant-union-∉ (→ `solve_notin` for notin goals,
  `destruct_notin; fsetdec` for the rest; NEVER `first [ solve_notin |
  fsetdec ]`), fsetdec-on-an-evar-set-goal (→ pin the `∀S` arg,
  `apply (HqX (remove X S))`), giant-IH-`destruct`-under-binder (→ clear
  giants), and `Set Implicit Arguments` arg-slot bugs (→ `@lemma` + supply
  the substituend before the freshness proof).  The profiling method:
  tight `timeout` + `coqc -time`, read the last-logged byte offset (the
  stuck sentence is the next one), fix, iterate.
  REMAINING: **`forall_syn_tagged`** — its P0=∀◇.P0' refinement is
  `tophole_fill`, which grows the REFINEMENT's aenv to `(X~tvar)++Θr`; the
  (Θtv, Θr) split cannot absorb that binder into Δr, so it needs handling
  distinct from case 1 (candidates: let Θr grow there and relax the
  S-conditions per row, or a case-3-specific fill analysis).  Then migrate
  `_gen` + the corollary to prop_look_complete.v, Print Assumptions, and
  retire the scratch.

- 2026-07-26 (o): **REPAIR PHASE 3a — rename machinery Qed + the tagged-∀
  case plan COLLAPSED (no inner induction needed).**
  - Landed Qed (dev scratch; migrate with the cases):
    `msubst_pskl_subst_var` (msubst/subst-var commutation) and
    `ad_partial_precise_rename` (renames a Δ-only variable Xr→Yr through
    subject+target+Δ; premises: Xr ∈ Δ, Xr ∉ dom Θ, Yr globally fresh,
    Xr/Yr avoid def-images; the □-rule survives because its own
    Δ-disjointness already excludes Xr from the local target).  Proof
    gotcha: ott's `eq_var`-ifs are NOT abstracted by `destruct (x == y)`
    after `simpl` — destruct the goal's own scrutinee via
    `match goal with |- context [if ?c then _ else _] => destruct c end`.
  - **KEY DISCOVERY — the ∀-cases need NO CORE size-induction.**
    `a_wf_pskl__tophole` demands GUARDED bodies, so `∀◇.∀…` subjects are
    not wf: the precision tophole_remove branch dies (guarded body vs
    all_etag target: unit/arrow by inversion, var by the
    mono-subject-tags-empty ε-contradiction), and the P0 = ∀◇.P0' rows
    die the same way on the refinement side.  (Sanity check that forced
    this: `∀◇.∀Z.Z ∼ ∀β.β` has NO solve derivation — GhostForall's body
    keeps the ∀◇ and the inner `∀Z.Z ∼ β'` is stuck — so wf-exclusion is
    load-bearing, not a convenience.)  Surviving grid per case:
    Pi ∈ {∀ (A), □ (B), ∀◇-FILL (C)} × P0 ∈ {∀ (case 1) / ∀◇-fill, □
    (case 3)}; everything else absurd with existing kit
    (mono-subject-tags-empty + ε ∈ Ψ'; K17 rigid-var;
    allinh/allsyn_rhs_absurd for flex P0; paint-shape discriminations).
  - Row recipes (all machinery now exists):
    * Tag algebra at the case top: `Ψa' := remove ε Ψa`;
      `Ψ0sub ⊆ Ψρ ∪ Ψ0'` via the ftag-flow at one fresh X; body-Hsubeq1
      needs `ε ∈ Ψ0sub ⇒ ε ∈ Ψρ` from that flow + the target's
      `ε ∉ Ψ0'` (a_tags_sort_all_etag_inv).
    * Row B (Pi=□): solve = SE-GhostL directly; the ∀-fold's body
      obligations are built PER (X', S) by RE-RUNNING the cofinite IH at
      X' (legal: `a_solve_eq_hole_subject_inv` pins every run's output
      to P0b^X', so no cross-run coherence is needed); each run's family
      at S' := {X'} ∪ S then `strengthen_tvar` (X' ∈ Δ∪S∪{X'}) +
      `delta_cong`.  NO rename.
    * Rows A (Pi=∀) and C (Pi=∀◇ via tophole_fill): ONE fresh-X IH run;
      solve reassembled with close_pskl + `a_solve_eq_strengthen_tvar` +
      `a_solve_sub_eq_rename` + `subst_pskl_in_pskl_spec/intro`;
      precision bodies per (X', S): take the X-run's family at
      S' := {X} ∪ S (allowed: X ∉ Δ, X ∉ dom Θr — THE point of the
      repair), `strengthen_tvar` (X now in the Δ-side), then
      `ad_partial_precise_rename` X→X' (Xr := X ∈ Δ∪S∪{X} ✓) +
      `msubst_pskl_subst_var` + open/close-spec rewrites + `delta_cong`.
    * The primary refinement's ∀-descent: `ad_refine_syn__all` grows Δr
      (aenv stays Θr) — enters the IH's (Θr, add X Δr) slot directly;
      body terms need `pskl_to_bskl_inh_open` + `msubst_pskl_open_lc_local`
      (msubst_lc via `a_inc_msubst_lc`).
  - OPEN QUESTION for case 3 (forall_syn_tagged) ONLY: its P0=∀◇ row is
    REAL via the refinement's tophole_fill, which grows the REFINEMENT's
    aenv ((X~tvar)++Θr) — there the fills may legitimately mention the
    binder, so the (Θtv,Θr) split cannot absorb it into Δr.  Resolve
    when building case 3 (candidates: let the IH's Θr grow there and
    weaken the S-conds per-row, or a case-3-specific fill analysis);
    case 1 is unaffected.

- 2026-07-26 (n): **REPAIR PHASE 2 COMPLETE — `a_solve_eq_complete_var_gen`
  is proven for all 13 previously-closed cases IN THE REPAIRED STATEMENT,
  and the paper-form statement is derived as its corollary (Qed).**  The
  scratch now holds only: `_gen` with the two tagged-∀ admits + the
  corollary (`Θtv := []`, `Δr := ∅`, `S := ∅` — the instantiation
  type-checks and Qeds, validating the design end-to-end).  Rethread
  facts learned (for the ∀-case builder):
  - The split equations `Θ = Θtv ++ Θr` / `Θ0 = Θtv ++ Θ0r` are consumed
    by ANY `inversion …; subst` — post-subst text must write
    `(Θtv ++ Θr)`/`(Θtv ++ Θ0r)` and pass `eq_refl eq_refl` to IH calls.
  - Per-case preamble: `HwfΘr` via `a_wf_aenv_app_r`; the plain
    refinement `Hrefine'` via `refine_primary_to_plain` ONLY where a
    delegation (cv_*, Bridge B2 inside FLEX) needs `(Θ, ∅)`; all
    structural inversions and recursion slots run on the PRIMARY form
    directly (same rule shapes).
  - Family discharges used per row: no_hole-Δ-monotonicity (Pi=var rows,
    the var-case binder-side via `a_solve_eq_no_hole_p0` +
    `ad_refine_inh_deltar_var_rhs_no_hole` + msubst-no_hole transport —
    the mini-grid was avoided entirely); target-fresh weaken (P0=□ rows,
    via `ad_refine_syn_ftv_rhs_bound` at the hole-LHS +
    `consis_subject_ftv_split_bound` + `uskl_rho_ftv_target_bound`,
    packaged per-case as `HψaB`); FLEX made Δ-UNIVERSAL (B2's conclusion
    is ∀Δ, so the flex rows instantiate the family at `Δ ∪ S` directly);
    recursion rows pass families through the ∀◇/arrow folds unchanged;
    the rigid-var absurdity at the primary uses the new
    `ad_refine_syn_rigid_var_nonvar_absurd_sub` (binds-inclusion into Θ
    + uniq).
  - New kit this phase (Qed, committed): `binds_def_split`,
    `refine_primary_to_plain`, `pskl_no_hole_open_rec_inv/_open_inv`,
    `msubst_pskl_no_hole(_inv)`, `a_solve_eq_no_hole_p0`,
    `ad_refine_inh_deltar_var_rhs_no_hole`,
    `consis_subject_ftv_split_bound`,
    `ad_refine_syn_rigid_var_nonvar_absurd_sub`, `p6cv_close_leaf_mono`
    (Δ-monotone leaf closer).
  REMAINING (Phase 3): the two tagged-∀ cases of `_gen`, now actually
  provable: the ∀-row per §6(h) (aenv-weaken into the IH at
  `Δx = add X Δ`, strengthen_tvar back); the □-row via the IH at `Δ`
  plus its FAMILY at `S := {X}` (X ∉ Δ, X ∉ dom Θr — the whole point of
  the repair); the fill-row likewise at the extended aenv; plus the
  `ad_partial_precise_rename` lemma (solve non-determinism forces
  rename-based cofinite reassembly), the SE-Forall/GhostForall solve
  close/rename plumbing, and the `Ψa \\ {ε}` tag algebra — all specified
  in §6(m).

- 2026-07-26 (m): **REPAIR OF THE §6(l) BLOCKER STARTED (user-approved
  "make the repair") — architecture LOCKED, support kit Qed+committed,
  generalized statement TYPE-CHECKED; proof rethread = next session.**
  The repair keeps the paper's statement intact: prove
  `a_solve_eq_complete_var_gen` (drafted, type-checked, in the dev
  scratch) and derive the paper form as the `Θtv := []`/`S := ∅`
  corollary.  The generalization has two coupled parts:
  1. **Split-context refinement premise.**  `Θ = Θtv ++ Θr` (`Θtv` =
     the ∀-descent binders, all `abind_tvar`; `Θr` = the original
     context; similarly `Θ0 = Θtv ++ Θ0r`), and the refinement premise
     is `Θr ⨟ Δr ⊢ᵣᵃ inh{κP0} ⊳ Q` with `Δr [=] dom Θtv` and
     `inter Δρ (dom Θtv) = ∅`.  Binders never enter the refinement's
     aenv, so its □-rule keeps fills wf at the ORIGINAL context — the
     load-bearing invariant (`ad_refine_syn_ftv_rhs_bound` then bounds
     every counterpart piece by `ftv(source) ∪ dom Θr`).  The ForallInh
     descent extends `Θtv`/`Δr` in lockstep and the all-rule inversion
     of the primary refinement re-enters the statement with NO
     transfer.  Where a case needs the OLD `(Θ, ∅)` form (cv_* /
     bridge / monoish delegations), derive it per case via
     `ad_refine_syn_weaken` + `ad_refine_syn_delta_absorb`
     (Δr-entries are Θ-tvars).
  2. **Fresh-extension conclusion family.**  Conclusion:
     `exists Pa, solve ∧ ∀S, inter S Δ = ∅ → inter S (dom Θr) = ∅ →
     delta_def_fresh S Θ → Θ ⨟ (Δ∪S) ⊢ msubst κ Pa ⊑ᵖ[Ψi∪Ψa] ψa`.
     The premise `Hpre` STAYS single-Δ (a ∀S-premise breaks
     derivation-shape dispatch: different S-instances may invert by
     different rules — verified dead end).  The □/∀◇-fill rows fold
     their ad_ppre__forall bodies by taking the body-IH's family at
     `S := {X}` (X allowed: X ∉ Δ, X ∉ dom Θr) + `strengthen_tvar`
     (X ∈ (add-X-side) Δ) + `delta_cong`.
  **Discharge table for the family (per row of the 13 closed cases):**
  - Pi=var rows / any row echoing a mono-paint-subject Hpre:
    `ad_ppre_no_hole_subject_delta_mono` (paints are `pskl_no_hole`;
    for hole-free subjects precision is fully Δ-monotone — Qed).
  - P0=□ (VacuousR) rows: `Q` is the □-fill's syn-paint ⇒
    `ftv Q ⊆ dom Θr` (rhs-bound at LHS `bskl_hole`) ⇒ via
    `ad_pat_consis_ftv_bound` (tight: counterpart vars ∪ DEFINED-FLEX
    data only — rigid tvar entries never pollute it) +
    `uskl_rho_ftv_target_bound` ⇒ `ftv ψa ⊆ dom Θr ∪ Δρ` ⇒
    `S ∩ ftv ψa = ∅` ⇒ `ad_partial_precise_delta_weaken_fresh`.
  - unit/ghostg delegation rows: target ftv = ∅ ⇒ weaken_fresh.
  - arrow rows: componentwise (branch families at the same S).
  - FLEX/B2 rows: B2's conclusion is already ∀Δ — instantiate at Δ∪S.
  - **var case, target `var X0` with `X0 ∈ dom Θtv` (the one NEW
    sub-proof, reachable from the folds when ψR uses its binder):**
    cv_var's output is opaque, so this branch must be proven directly:
    the PRIMARY refinement forces P0's core to be `∀◇ⁿ.(var X0)`
    (hole-fill `var X0` is not Θr-wf; flex-chases are Θr-scoped and
    X0-free — use rhs-bound), Hpre forces Pi's core ∈ {var X0, □}, and
    every reachable output Pa is `∀◇ⁿ.(var X0)`-shaped, hence
    `pskl_no_hole` ⇒ Δ-monotone.  Budget ~100-150 lines.
  **Remaining plumbing to write (all standard):**
  `ad_partial_precise_rename` (X→Y on subject+target+Δ-entry; model:
  `ad_refine_syn_f_rename`) — REQUIRED because a_solve_eq is not
  deterministic, so the family's per-X' ∀-rule bodies must come from
  renaming the single X-run's output precision (per-X' IH re-runs would
  return unrelated Pa's); `rho_fresh`/`delta_def_fresh` cons-tvar
  weakenings (inline-able); the SE-Forall/GhostForall cofinite solve
  reassembly (close_pskl + `a_solve_eq_strengthen_tvar` +
  `a_solve_sub_eq_rename` + `subst_pskl_in_pskl_spec`); msubst/open
  commutation via `msubst_pskl_open_lc_local` + `a_inc_msubst_lc`
  (both exist); the `Ψa' := Ψa \ {ε}` tag algebra (body-Hsubeq1 needs
  `ε ∈ Ψ0sub ⇒ ε ∈ Ψρ`, from the ftag-flow fact + the target's
  `ε ∉ Ψ0'` d_tags disjointness); the ForallSyn-case analogue of
  `flex_apart_all_etag_forall_inv` for ∀◇-sources (the deleted
  `..._target_clean_inv` draft had the wrong shape — its fa_tophole
  case meets diagonal families; re-derive from the actual grid).
  **Landed this session (Qed, axiom-free, committed in
  prop_look_complete.v):** `ad_partial_precise_delta_cong`,
  `ad_partial_precise_delta_weaken_fresh`,
  `ad_refine_syn_delta_to_tvar(_mid)`, `ad_refine_syn_delta_absorb`,
  `ad_pat_consis_ftv_bound`, `uskl_rho_ftv_target_bound`,
  `is_tskl/uskl_ghost_free/a_tags_sort_all_etag_inv`,
  `flex_apart_weaken`, `flex_apart_all_etag_forall_inv`,
  `pskl_no_hole` kit + `ad_ppre_no_hole_subject_delta_mono`,
  `ad_refine_syn_ftv_rhs_bound`.

- 2026-07-25 (l): **P6-Cv at 13/15 — Hsubeq weakened to the inclusion pair,
  ARROW CASE CLOSED, both untagged-∀ cases closed (absurd); the two
  TAGGED-∀ cases are TRUE but BLOCKED on a Δ-transfer PAPER-GAP that
  needs a repair decision.**
  - **Hsubeq weakening (STEP 1) done**: the statement's
    `Ψsub [=] Ψρ ∪ Ψa` is now the pair `Ψsub ⊆ Ψρ ∪ Ψa` ∧ `Ψa ⊆ Ψsub`
    (`Hsubeq1`/`Hsubeq2`); all 10 previously closed cases re-threaded
    (topholeg P0=□ rows use only `Hsubeq2`, flex_l passes the pair with
    the second component trivial).
  - **Arrow case CLOSED** (dev scratch; kit Qed in prop_look_complete.v).
    Structure: `uskl_rho_arrow_l_inv` → leaf (`p6cv_close_leaf`) / refl
    (recast as congruence via `urho__refl`, lc from `is_tskl_lc`,
    Ψρ := ∅∪∅) / congruence — both non-leaf branches funnel into an
    inline KEY continuation.  KEY level (fixed for the whole grid):
    `a_tags_sort_arrow_inv` branch decomposition; the branch tag-flow
    facts `Ψ_k ⊆ Ψρ_k ∪ Ψ'_k` (`ad_pat_consis_ftag_sub` +
    `uskl_rho_ftag_sub` + `d_tags_skl_ftag`); the solved-tag split
    `Ψa_k := Ψ_k ∩ Ψ'_k` with `Ψa [=] Ψa1 ∪ Ψa2` (one scoped fsetdec
    from Hsubeq1/2 + H + Hsub + Hinter + the flow facts); VACR (P0 = □ ⇒
    `ad_refine_syn_hole_sskl` + `ad_pat_consis_sskl_tags` per branch ⇒
    Ψa = ∅); FLEX — the repaired flexible-P0 discharge chain as one
    assert (apart-inversion: only `fa_clean` survives, `fa_var_rigid`
    dies by wf-uniq; `uskl_rho_clean_eq` per branch ⇒ subject = target,
    Ψρ_k = ∅; `ad_refine_mono_paint_rhs_monoish` ⇒ monoish Q_k;
    `ad_pat_consis_monoish_counterpart` per branch ⇒ Ψ_k = ∅ and
    ψa_k = mono paint; rebuild `ad_pat_consis__arrow`; B2
    `mono_paint_paint_refine_consis_ppre` closes the κβ̂-image precision).
    CORE = inner strong induction on `size Pi + size P0` at the fixed
    arrow target: Pi ∈ {unit, arrow-vs-∅-rules absurd, var (SE-Var +
    NEW `ad_ppre_mono_subject_target_tags_empty` ⇒ Ψ' = ∅ ⇒ Ψa = ∅),
    arrow (P0-grid: flex = FLEX + SE-FlexR; rigid var absurd; arrow =
    branch main IHs with the tag split; □ = VACR + SE-VacuousR; ∀◇ =
    `flex_apart_tophole_p0_inv` + SE-GuardedGhost + CORE), □ (P0-grid:
    flex = FLEX + SE-GhostL; arrow = □-precisions per branch + branch
    main IHs + `a_solve_eq_hole_subject_inv` pins; ∀◇ = CORE(□,P0') +
    SE-GhostL), ∀◇ (tophole_remove inversion only — target is an arrow —
    then the cv_mono-style P0 grid with SE-GhostGuarded/UnivGhost/
    VacuousR)}.  New kit (Qed, committed): `ad_ppre_arrow_arrow_inv`,
    `ad_refine_arrow_arrow_inv` (caller-named component inversions),
    `ad_ppre_mono_subject_target_tags_empty`, `flex_apart_arrow_inv`.
  - **forall_inh_untagged + forall_syn CLOSED — ABSURD**: the subject
    `uskl_all_syn` is neither tag-sorted (no `is_tskl`/`d_tags_skl`
    all_syn constructor) nor a legal ρ-leaf image; all three ρ-inversion
    branches die by `a_tags_sort_d_tags` inversion (same pattern as the
    plain-ghost cases).  [The paper runs these under its ForallInh/
    ForallSyn cases; in the mech's tag-sorted reading only the TAGGED
    subjects survive.]
  - **BLOCKER (needs decision) — forall_inh_tagged / forall_syn_tagged:
    the Pi = □ and Pi = ∀◇(tophole_fill-branch) rows.**  The ∀-row
    (Pi = ∀.Pib) follows §6(h): precision-body from `ad_ppre__forall`
    inversion at `Θ ⨟ add X Δ`, aenv-weaken into the IH at
    Θx = (X~tvar)++Θ, `ad_partial_precise_strengthen_tvar` back out
    (legal: X ∈ add X Δ), solve out via `a_solve_eq_strengthen_tvar` +
    `a_solve_sub_eq_rename` cofinite reassembly.  But in the □/∀◇-fill
    rows the IH's precision PREMISE can only be built at Δ (the □-rule's
    side condition `Δx ∩ ftv(ψR^X) = ∅` fails at Δx = add X Δ since
    X ∈ ftv(ψR^X) in general), so the IH's OUTPUT lives at Δ (resp. at
    (X~tvar)++Θ ⨟ Δ for the fill-branch) — and the conclusion's
    `ad_ppre__forall` body must sit at `Θ ⨟ (add X Δ)`.  The transfer is
    blocked precisely at `ad_ppre__hole`: its Δ-disjointness is NOT
    Δ-monotone.  **This is a PAPER-GAP, not a falsity**: the paper's own
    Subcases Pi=□ / Pi=∀◇.Pi' (consistency-proofs.tex ForallInh/
    ForallSyn) silently move the IH output from Δ to Δ,β.  The statement
    survives because the configurations that would break the transfer
    are premise-unreachable: a refinement □-fill is `Θ ⨟ ∅`-wf, hence
    X-free (X ∉ dom Θ), and consistency + ρ transfer that X-freeness to
    the □-opposite TARGET subtrees (verified concretely: ψR = β→1,
    P0b = □→1 forces the □-fill's syn-paint to be `var X`, whose wf
    premise fails — the bad configuration cannot arise).  Candidate
    repairs (decide before building the two cases):
    1. **(prefer to explore first) Δr-generalized refinement premise**:
       change the statement's refinement slot to `Θ ⨟ Δr ⊢ᵣᵃ … ⊳ Q` with
       Δr collecting the ∀-descent binders (side conditions
       Δr ∩ dom Θ = ∅, Δr ⊆ Δ-ish); the binder then stays in Δr — never
       enters Θ — so the refinement's own □-rule wf keeps fills X-free,
       and the □-row recursion re-enters the statement without any
       transfer.  Cost: `a_solve_eq_cv_{unit,mono,ghostg}`, Bridges A/B
       and B2 pin `Δr [=] empty` — they need Δr-generalization or
       call-site strengthening lemmas.
    2. **Standalone □-column lemma**: prove the Pi = □ instance of the
       theorem as its own consistency induction with a Δr-INDEXED
       refinement premise, plus two new ftv-bound lemmas
       (`ad_pat_consis`: ftv(S) ⊆ ftv(Q) ∪ dom Θ; `uskl_rho`:
       ftv(ψa) ⊆ ftv(ψsub) ∪ Δρ) discharging each □-leaf's
       (add X Δ)-disjointness pointwise; the main induction's □-rows and
       the ∀◇-fill rows call it.  No statement change, but a second
       □-column copy of the induction.
    3. **hole_apart positional premise** (flex_apart-style statement
       change): dispreferred — the call sites would need to derive it
       from cleanliness, which breaks at exactly the binder descent.
    Plumbing needed regardless of the choice (all standard):
    `ad_refine_syn` Δr→tvar transfer (mid-general), an
    `ad_partial_precise` rename lemma, `a_tags_sort_all_etag_inv`,
    `flex_apart` binder inversion + aenv-weakening + open/rename,
    `pskl_shielded_ftv_open_upper` threading, and the
    `Ψa' := Ψa \ {ε}` tag algebra (body-Hsubeq1 needs `ε ∈ Ψ0sub ⇒
    ε ∈ Ψρ`, which follows from the flow fact + the target's
    `ε ∉ Ψ0'` d_tags disjointness).

- 2026-07-25 (k): **Arrow repair option (i) EXECUTED through the discharge
  kit — `flex_apart` premise added (user-approved direction), all 10 closed
  cases re-threaded, flex-subcase machinery Qed.**  User question answered:
  the premise does NOT escape the P6 cluster — vacuous (`fa_clean`) at every
  ρ = id call site; threaded through Cs/Sv/Ss statements internally; the one
  real obligation is Sv-ForallL maintenance, to be discharged by the
  collection-time freshening lemmas.  Landed (Qed, axiom-free, migrated):
  - `flex_apart Θ0 Δρ P0 ψa` (leaf constructors for □/unit/rigid-var,
    `fa_clean` for Δρ-clean targets, congruences incl. ∀◇/∀◈ strips and
    cofinite ∀-pairs) + `flex_apart_{topholeg_target,tophole_p0}_inv`.
    The cex config now VIOLATES the premise (P0 = β̂ flexible, ψa carries
    the replaced rigid `c`); statement drafted accordingly.
  - `uskl_rho_clean_eq` — on a Δρ-clean target the ρ-relation degenerates
    to syntactic equality with Ψρ = ∅ (pick-fresh + `open_uskl_wrt_uskl_inj`
    in the binder cases).
  - `ad_refine_mono_paint_{allinh,allsyn}_rhs_absurd` (completing the
    mono-paint RHS absurdity family), `bskl_monoish` + 
    `ad_refine_mono_paint_rhs_monoish` (the counterpart shapes reachable
    from a mono paint), `ad_pat_consis_monoish_counterpart` (against a
    mono-ish counterpart a tag-sorted subject IS a mono paint and the
    derivation solves no tags — gives Ψsub = ∅ hence Ψa = ∅, and turns
    ψa into `ptyp_to_uskl_syn τa` so `ad_ppre_mono_tags_empty` kills Ψi).
  - LHS flex_l-spine chases `ppre_paint_{arrow,flexvar}_chase`
    (continuation-passing over the component obligations) and the bridge
    **`mono_paint_paint_refine_consis_ppre`** (B2): a mono paint refining
    the counterpart of a MONO-PAINT consistency subject is ⊑ᵖ[∅] against
    that subject — outer induction on the consistency, Bridge A at the
    leaves, the chases at arrow/flex_r.
  **Remaining for the Arrow case (next): the CORE inner size-induction**
  (∀◇-strip recursion on `size Pi + size P0` at a fixed arrow target, with
  the two branch main-IHs in scope), the branch TAG-SPLIT algebra
  (Ψa_k := Ψ_k ∩ Ψ'_k; needs `ad_partial_precise_tags_sub`,
  `ad_pat_consis_ftag_sub`, `d_tags_skl_ftag`, a new rho-tags-lower lemma),
  and — DISCOVERED during the split analysis — **the `Hsubeq` premise must
  weaken from the equality `Ψsub [=] Ψρ ∪ Ψa` to the inclusion pair
  `Ψsub ⊆ Ψρ ∪ Ψa` ∧ `Ψa ⊆ Ψsub`**: cross-copy shared replacement tags
  (one ρ-image at two leaves, consumed in one branch only) satisfy the
  global equality but break the branch equalities; the inclusion pair is
  branch-derivable (Ψ_k ⊆ Ψρ_k ∪ Ψ'_k via ftag_sub + rho-ftag-upper +
  d_tags_skl_ftag) and callers derive it from the paper's ⊎ — premise
  weakening = lemma strengthening, no caller cost.  All 10 closed cases'
  Hsubeq uses survive the inclusion form (checked: topholeg P0=□, flex_l
  transport, arrow-flex Ψa ⊆ Ψsub).  Then the four ∀ cases.

- 2026-07-25 (j): **P6-Cv main induction at 10/15 cases; GhostG + topholeg +
  flex + plain-ghost cases CLOSED; ARROW CASE BLOCKED — the drafted
  statement's arrow/flex-P0 subcase is refuted by the standing cex.**
  New Qed, axiom-free (migrated to `prop_look_complete.v`):
  - `a_solve_eq_cv_ghostg` — the GhostG case as a standalone lemma with NO
    size induction: a `holeg` target admits only a `□` subject and a
    `bskl_hole` refinement RHS only a `□` source (mono paints and guarded
    ∀◇-bodies have no rule into them) — both sides forced to `□`, all other
    shapes premise-absurd.  Kit: `d_tags_skl_holeg_inv`,
    `ad_ppre_mono_paint_holeg_absurd`, `ad_refine_mono_paint_hole_rhs_absurd`.
    Uniformity trick: `msubst κ (var v)` is ALWAYS a mono paint
    (`a_inc_lookup_mono` covers rigid v too) — no rigid/flex split anywhere.
  - Flex kit: `is_tskl/d_tags_skl/uskl_ghost_free/a_tags_sort_mono_paint`
    (a mono paint is an empty-tag tag-sorted decorated skeleton).
  - Topholeg kit: `a_tags_sort_topholeg_inv` (TY-mode vacuous via
    ghost-free), `ad_ppre_mono_paint_topholeg_absurd`,
    `ad_refine_mono_paint_tophole_rhs_absurd`.
  Main-induction cases wired in the dev scratch (beyond unit/var):
  - **ghostg** via `a_solve_eq_cv_ghostg` (+ leaf via `p6cv_close_leaf`).
  - **hole / tophole / tophole_inh / tophole_drop** — ABSURD: ψa (and a
    leaf's replacement image) is tag-sorted, and `is_tskl`/`d_tags_skl`
    have no plain `hole`/`tophole` constructor; every branch of the ρ
    inversion dies by `a_tags_sort_d_tags` inversion.  [The paper's
    UnivGhost1/UnivGhost2 cases are vacuous in the mech's tag-sorted
    reading; Ghost matches the paper's own "Impossible".]
  - **flex_l** — target-switch: ψa = var α (α defined in Θ): transport the
    precision via `ad_ppre_flexdef_target_unfold` (uses `delta_def_fresh`),
    switch the WHOLE problem to the definition's mono paint (rho := refl,
    tags := `a_tags_sort_mono_paint`, all tag sets ∅ since
    `ad_ppre_mono_tags_empty` + `d_tags_skl_var_inv`), recurse via the MAIN
    IH, fold the conclusion back with `ad_ppre__flex_r`.
  - **flex_r** — one-liner: transport the refinement via
    `ad_refine_flexdef_target_unfold`, main IH at the unchanged ψa.
  - **topholeg** — the ∀◈ congruence via an inline KEY continuation shared
    by the refl and congruence ρ-branches (refl recast with `urho__refl`,
    lc from `is_tskl_lc`).  Grid: Pi ∈ {□, ∀◇.Pi'} (paints/guarded die);
    P0 = □ ⇒ SE-VacuousR with Ψa=∅ from the `is_sskl` kit
    (`ad_refine_syn_hole_sskl` + `ad_pat_consis_sskl_tags` — the paper's
    "P0 = □ ⇒ Q synthesized ⇒ Ψa = ·" special case); P0 = ∀◇.P0' ⇒
    keep-inversion (remove-branch dies on guarded bodies) then main IH —
    at (Pi', P0') with SE-UnivGhost, or at (□, P0') with
    `a_solve_eq_hole_subject_inv` pinning the sub-output and SE-GhostL;
    shielded-pack transported via `pskl_shielded_ftv_sub_ftv`.
  **REMAINING 5 cases: arrow + the four ∀ cases.  ARROW IS BLOCKED on a
  statement-level decision:** the drafted `a_solve_eq_complete_var` admits
  `cex_p6_flex_counterpart.v`'s configuration VERBATIM (re-verified against
  every premise incl. the new `delta_def_fresh`) — the flexible-P0-opposite-
  a-ρ-leaf collision sits exactly in the arrow case's SE-FlexR subcase, so
  the isolated statement is FALSE and no premise currently encodes the
  LE-FlexR freshening that makes it unreachable (§6(g) resolved the
  COMPLETENESS question but left the standalone-statement repair
  unspecified).  Candidate repairs to decide: (i) a P0-side positional
  premise ("no Θ0-flex in P0 opposite a ψa-subtree containing a ρ-leaf") —
  the resurrected-but-reachability-flavoured dominates predicate; its Cv-
  internal maintenance is structural, and the killer maintenance step of
  the reverted attempt lived at Sv-ForallL/Cs, where the freshening facts
  (`cex_p6_flex_freshened.v`) are exactly what discharges it; (ii) inline
  Cv into Cs's induction (no standalone -var lemma; the paper's own -var
  statement is the refuted one — already a PAPER-GAPS item); (iii) a
  Ξ-extension conclusion — REFUTED already (the cex kills arbitrary κa).
  The four ∀ cases are deferred until the decision, since a new premise
  must thread through exactly their binder bookkeeping.

- 2026-07-25 (i): **P6-Cv Var case CLOSED — `a_solve_eq_cv_var` Qed,
  axiom-free, via the MONO-TARGET generalization `a_solve_eq_cv_mono`**
  (both `Print Assumptions` = Closed under the global context; in
  `prop_look_complete.v`).  The Unit/Var/GhostG paper case's grid at a
  variable target is richer than unit: a DEFINED-FLEX target `var X`
  unfolds through Θ's definition chains in both premises.  Design:
  - `a_solve_eq_cv_mono`: target = `ptyp_to_uskl_syn τ` for MONO `τ`
    (subsumes unit `τ=1` — delegated to `a_solve_eq_cv_unit` — and var
    `τ=X`; arrow components recurse inside).  Strong induction on
    `size Pi + size P0` only; the target's def-chain unfolding rides the
    PREMISE DERIVATIONS via `a_def_chain Θ τ τe` + chain-based
    inversions, NOT the size (a size-only induction cannot step
    flex_r-target unfolds — that was the structural crux).
  - Kit (all Qed): paint compute/shape inversions (uskl+bskl);
    `a_inc_lookup_mono` (κ-images mono); `a_def_chain` + mono/trans;
    `mono_ptyp_wf_to_pskl_wf`, `ad_ppre_mono_paint_refl`,
    `ad_refine_mono_paint_refl`; `ad_ppre_mono_tags_empty` (mono targets
    carry no tags — replaces per-target `_tags_empty` lemmas);
    defined-flex TARGET unfolds `ad_ppre/ad_refine_flexdef_target_unfold`
    + chain transports (`*_chain_unfold`, `ad_ppre_chain_fold` — fold =
    iterated `flex_r`, used to bring conclusions back to the original
    target); chain-based SUBJECT inversions
    (`ad_ppre_{unit,arrow,tophole}_subject_chain_inv`,
    `ad_ppre_allsyn_subject_mono_absurd`,
    `ad_refine_tophole_lhs_chain_inv`, `ad_refine_allinh_lhs_mono_absurd`,
    `ad_refine_syn_rigid_var_nonvar_absurd`); Bridge A
    `ad_refine_mono_paint_lhs_ppre` (mono-paint LHS — the κ-image of a
    flexible counterpart — precise at ANY Δ: paints have no ghosts, so no
    Δ-sensitive rule fires); Bridge B `ad_refine_inh_hole_ppre` (arbitrary
    inh-painting LHS for the `Pi = □`/SE-GhostL case, threading the given
    □-precision to ghost leaves and Δ-def-freshness to chain hops).
  - **NEW WF-SIDE-CONDITION (statement change, registered
    WF-SIDE-CONDITIONS §7): `delta_def_fresh Δ Θ`** — every `Y ∈ Δ`
    avoids every definition image's ftvs.  NECESSARY: the Δ-free
    statement is FALSE — with `X` def-flex `:= (var Y)→1`, `Y ∈ Δ` rigid,
    `Pi = □` (precision by the □-rule at `var X`, X ∉ Δ), `P0 = (□→□)`,
    all premises hold but the conclusion precision must pass the □-rule
    at the definition's paint, whose Δ-disjointness fails.  Semantically
    it is the paper's implicit wf of the Δ-extended precision context
    (Δ's binders postdate Θ's definitions).  Maintenance is free at every
    growth point: ForallInh binders are fresh w.r.t. `dom Θ ⊇` def-ftvs
    (`a_wf_aenv_def_ftv_dom`); Δρ carries it inside `rho_fresh`; the
    initial Δ at the P6-Cs call site obeys the same discipline.
  - Main induction (`a_solve_eq_complete_var`, dev scratch): **Unit and
    Var cases WIRED and closed** — refl branch of `uskl_rho` via
    `a_solve_eq_cv_unit`/`_cv_var` + `d_tags_skl_{unit,var}_inv` (Ψ'=∅ ⇒
    Ψa=∅ ⇒ psi_cong), leaf branch via `p6cv_close_leaf`.  13 cases
    remain.  The statement gained the `delta_def_fresh Δ Θ` hypothesis.
  - PERF gotchas (all hit, all fixed; add to the checklist): (1)
    `fsetdec` on an EVAR set-goal AGAIN — the bridges' `Δr [=] empty`
    subgoal ran before `?Δr` was pinned by the refinement arg ⇒
    minutes-long unification hang; fix `eapply … with (Δr := empty)`.
    (2) `ltac:(lia)` as an argument in a named-arg application elaborates
    BEFORE `(n := …)` pins the evar ⇒ "Cannot find witness"; use a prior
    `assert (Hsz : …) by lia`.  (3) a wrong-orientation `symmetry` before
    `apply`ing a painting equation sends unification into deep conversion
    between two reducible paintings — apply in the lemma's own
    orientation.
  NEXT: GhostG case (`a_solve_eq_cv_ghostg` — target `uskl_holeg`/
  `bskl_hole`; NB `bskl_hole` is NOT a mono paint, so it is a sibling of
  cv_unit, not a cv_mono instance), then Arrow (first case recursing into
  the MAIN consistency IH), then flex/∀◇/∀ cases per the build order.

- 2026-07-25 (h): **P6-Cv INDUCTION STARTED — reusable kit landed, Qed,
  axiom-free (commits 47947e3, a793581 on `remech`).**  The statement
  (`a_solve_eq_complete_var`) is set up in `prop_look_complete.v` with the
  uniform 15-case induction on the consistency derivation (dev file
  `algo/cex/p6cv_dev_tmp.v`, UNTRACKED scratch — migrate finished pieces).
  Committed reusable helpers (all in `prop_look_complete.v`):
  - `p6cv_close_leaf` — closes the `rho_leaf` disjunct of EVERY case
    uniformly (target = replaced rigid var ⇒ `Pi = var X` by the freshness
    pack ⇒ SE-Var, `Pa := Pi`).
  - `pskl_to_bskl_inh_{all_inh,arrow,tophole}_inv` — painting inversions;
    the `all_inh` one forces a `pskl_all_syn` source (excludes flexible
    `P0` in the ∀ cases — κ maps flexibles to monotypes).
  - `ad_refine_inh_unit_ppre` — refinement→precision bridge for the `unit`
    target (follows `flex_l` def-chains, strips ∀◇); discharges `Pi=□` and
    ∀◇-`P0` unit subcases.
  - `msubst_lookup_notin_dom`, `a_inc_dom_flex`, `msubst_pskl_tvar_id` —
    the metasubst-domain facts (dom ρ ⊆ source flexibles; a rigid source
    var is msubst-fixed), for the `P0 = var` FlexR/rigid split.
  - `ad_refine_syn_rigid_var_unit_absurd` — a rigid var cannot refine into
    unit; kills the rigid-`P0` unit subcase.
  Kept in dev (Qed): `ad_ppre_unit_tags_empty` (unit target ⇒ Ψi=∅).
  **STRUCTURE learned:** each of the 15 cases carries a 2-D Pi×P0 grid; the
  ∀◇-stripping (both Pi and P0 sides) recurses on skeleton SIZE, so each
  leaf/structural case is cleanest as a STANDALONE size-induction lemma
  (`a_solve_eq_cv_<shape>`) that the main consistency-induction dispatches
  to — the main IH is on the consistency derivation and gives NO handle on
  a smaller Pi/P0.  **UNIT CASE CLOSED** (commit 68c48eb): `a_solve_eq_cv_unit` Qed,
  axiom-free — the full Pi×P0 grid as a standalone size-induction lemma
  (strong induction on `size Pi + size P0` so ∀◇-stripping on both sides
  recurses).  This is the TEMPLATE for the other leaf cases (Var/GhostG:
  same shape, target `var X` / `holeg` instead of `unit`, needing the
  analog of `ad_refine_inh_unit_ppre` per target).  Validated: the empty-Δ
  statement + the standalone-case-lemma factoring both work.
  **P0/Pi WF CONTEXT (FINAL — both at `Θ0 ⨟ empty`, no side-condition).**
  Change both wf premises to `Θ0 ⨟ empty ⊢ₚₛᵃ Pi` and
  `Θ0 ⨟ empty ⊢ₚₛᵃ P0` — the faithful rendering of the paper's `Θ0 ⊢ Pi`,
  `Θ0 ⊢ P0`.  This is symmetric AND at empty Δ, because the mech's
  `a_wf_pskl__all` handles a ∀-binder by growing the AENV `Θ0`
  (`(X~tvar)++Θ0`), NOT Δ — so `Θ0 ⨟ empty` with `Θ0` growing under binders
  covers all binder vars, exactly as the paper's growing `Θ0` does.
  BOTH `Θ0` and the precision `Δ` grow in ForallInh, via DIFFERENT premises:
  `Θ0`/Γ via the wf (`a_wf_pskl__all`) and inc (`a_inc__tvar`, to keep
  `κ ∷ Θ0 ⊑ Θ`); the precision `Δ` via `ad_ppre__forall`.  The `a_solve_eq`
  judgment does not grow (binder stays opened/free).  Reconciled: weaken the
  precision aenv `Θ → (X~tvar)++Θ` going into the IH, and
  `a_solve_eq_strengthen_tvar` drops the rigid `X` from the solve output
  coming out (mirror `ad_partial_precise_strengthen_tvar` for precision).
  **No side-condition:** at empty Δ, `P0 = var α` forces `α ∈ Θ0`
  (`a_wf_pskl__var` gives `α ∈ ∅ ∨ a_binds_tvar α Θ0`), so the P0=var case
  closes by the ordinary 3-way (rigid ⇒ `ad_refine_syn_rigid_var_unit_absurd`
  after `msubst_pskl_tvar_id` + `a_inc_binds_tvar`; flex ⇒ SE-FlexR) — no
  `α ∈ Δ`-only branch to worry about.  [History: this note flip-flopped —
  P0-only-empty (asymmetric, wrong) → both-at-Δ (wrong) → both-at-Δ +
  side-condition (wrong, forgot a_wf_pskl grows Θ0 not Δ).  THIS is the
  correct one: both at empty Δ, Θ0 grows, no side-condition.]

- 2026-07-25 (g): **RESOLVED — the -var cex is NOT a completeness problem;
  the whole P0-side-condition line of (d)–(f) is SUPERSEDED and REVERTED.**
  Re-reading the paper's Arrow case ("We assume `P0 = P0,1→P0,2`",
  subtyping-proofs.tex:1940 / consistency-proofs.tex:1408) plus the solve
  rules (fig:selected-look) settled it:
  - **Only the Arrow case can even have a flexible P0.** κ maps flexibles to
    MONOTYPES (unit / mono-or-rigid var / arrow); refinement `inh{κP0} ⊳ Q`
    into a ∀/∀◇ needs a ∀/∀◇/defined-flex source, which a monotype never is.
    So ForallInh/ForallSyn/ghost provably have non-flex P0, and leaves are
    handled directly (SolE-Flex / the SolE-Var ρ-var special case).
    Machine-checked shape: `ad_refine_syn` into `bskl_all_inh` forces the
    source to be ∀/∀◇/defined-flex.
  - **No flex-SPLIT rule exists in constraint solving, and none is needed.**
    SolE-Arrow needs both sides arrows; SolE-FlexR solves the flexible
    counterpart directly to `β̂` (kept whole). `split[α̂][β̂→γ̂]` lives only in
    the inference/`⤳ᵐ` layer (which can introduce fresh flexibles via a
    context move).
  - **The cex's κ is FORCED BY ρ, not free, and the config is UNREACHABLE.**
    ρ substitutes the rigid `c` away, so `ρ(ψa)=unit→unit ∼ Q` and
    `inh{κβ̂} ⊳ Q` (same Q) pin `κβ̂ = unit→unit`; a run never produces this
    because a flexible counterpart at a COMPOUND subject is FRESHENED by
    LE-FlexR to a fresh `γ ∈ Ξ` (the non-var lemma then extends κ over Ξ and
    assigns γ the rigid `c`). Machine-checked, Qed axiom-free, in NEW file
    `algo/cex/cex_p6_flex_freshened.v`:
    `a_lookeq_arrow_subject_flex_target_freshened` (arrow subject ⇒
    freshened) and `a_lookeq_flex_target_raw_subject_not_arrow` (a raw flex
    payload's subject is never an arrow).
  - **REVERTED:** the `pskl_dominates_rho` relation + inversion kit + the
    ForallL maintenance experiment (the maintenance-from-solve lemma was
    itself false — SolE-Check bridges into SolE-FlexR). `prop_look_complete.v`
    is back to its committed state.
  - **P6-Cv/Sv plan (now):** ∀/∀◇/ghost cases prove non-flex P0 from the
    monotype→refinement fact (no premise); leaf cases as the paper; Arrow
    case handles flexible P0 via SolE-FlexR like the leaf case, relying on
    the freshening so a raw Θ0-flex opposite a ρ-rigid-var cannot occur.
  The cex header (cex_p6_flex_counterpart.v) STATUS block is updated to
  match; the `\shengyi{}` paper note (remech-paper) is updated likewise.

- 2026-07-25 (f) [SUPERSEDED by (g)]: **the nonflex{P0} repair REFUTED at depth (mech-first
  experiment); repair REDIRECTED to a P0-side positional condition.**
  `cex_p6_var_nonflex_insufficient` (cex_p6_flex_counterpart.v, Qed
  axiom-free): with `P0 = 1 → β̂` the head-shape premise holds, but the
  -var Arrow case recurses on P0's PIECES and the flexible piece opposite
  the ρ-leaf reproduces the (d) refutation one level down — no head-shape
  premise survives the structural recursion.  Naming: the cex now uses
  rigid `c` / flexible `β̂` (user rule: never reuse the lemma's α; keep
  mech and paper letters aligned).  KEY INSIGHT for the repair: at
  ρ = id — the `P = α` crux, the only direct paper invocation of the -var
  lemma — the bad configuration is premise-UNSATISFIABLE (the subject is
  ψa itself and rigid-vs-flex-image consistency fails), so the falsity is
  an artifact of the ρ-GENERALIZATION forgetting that flexibles cannot
  cover ρ-positions in premise sets arising from real runs.  REDIRECTED
  REPAIR (to validate BEFORE building P6-Cv): extend the positional side
  condition symmetrically to the counterpart — "P0 has no flexible
  variable at or covering any ρ-substituted position" — mechanized as a
  second leaf-freshness component alongside the existing pack (e.g.
  `∀X ∈ Δρ, ∀β̂ ∈ flex(Θ0): β̂'s P0-position does not cover X's
  ψa-position", concretely: a P0-side analogue of `ad_ppre_delta_var_inv`
  giving "at a ρ-leaf, the refinement-exposed P0-piece is X, a rigid var,
  or □" — killing the FlexR-subcase), maintained at Sv-ForallL by
  X-postdating-P0 freshness.  Validation plan: (1) state the P0-side
  condition relationally (couple it to uskl_rho or thread it as a
  freshness fact like the pack); (2) re-run the two cex configurations
  against it (both must violate it); (3) check the Cs→Cv call site (ρ=id:
  vacuously true) and the Sv-ForallL extension step.  The implementation
  (type.ml solve_eq) confirms context-free FlexR — the solve side cannot
  be tightened; the invariant must exclude the configuration.  Paper notes
  updated on remech-paper (retraction + redirected proposal).
- 2026-07-24 (e): **SE-FlexR widened to `a_flex_tvar` (paper's
  context-free FlexR)** — the undefined-only encoding was an
  INDEPENDENT completeness falsifier (defined flexible nested in a
  structural counterpart: solve stuck in mech, fine on paper; survives
  any repair of the (d) gap).  Fallout: prop_look_complete.v transport
  helpers only; soundness stack untouched (a_sub_sound still
  Closed under the global context); make coq green.  The (d)
  counterexample is unaffected (it uses an undefined flexible — the
  widening does not repair it; the failure is in the conclusion
  precision, not solve-stuckness).
- 2026-07-24 (d): **P6 BLOCKED — the -var lemmas (P6-Cv/Sv) are FALSE AS
  STATED; machine-checked counterexample committed**
  (`algo/cex/cex_p6_flex_counterpart.v`, Qed axiom-free; PAPER-GAPS
  entry "FALSE — the -var completeness lemmas of the constraint
  cluster").  While drafting P6-Cv's statement, the case grid (Pi × P0
  shapes exposed by precision/refinement inversion) surfaced a subcase
  every paper case analysis skips: `P0` = FLEXIBLE VARIABLE, whose
  κ-image supplies the constructor the refinement inversion "exposes".
  Configuration `Θ0 = X,α̂; κ = [α̂ ↦ unit→unit]; ψa = X→unit;
  ρ = [X ↦ unit]; Pi = X→unit; P0 = α̂; Q = unit→unit` satisfies EVERY
  premise (incl. the positional side condition / the §7 freshness pack);
  solve is forced to `Pa = α̂` (FlexR — note the mech's SE-FlexR already
  fires: α̂ is undefined-flex in Θ0), and the conclusion precision
  `κa(α̂) ⊑ᵖ (X→unit)` fails for every `κa ≡ κ` (pinned image
  `unit→unit`; `unit ⊑ᵖ X` underivable, X rigid) — refutation
  machine-checked for arbitrary `Pa`, `κa`, Δ, and tag set.  LE-FlexR
  (the algorithm's own fresh-`γ̂` rule for flexible counterparts) is
  never used in either completeness appendix; at the NON-var lemmas it
  can repair the subcase (κa extends to Ξc), at the -var lemmas it
  cannot (Ξc = ∅, κa pinned).  STOPPED per the ground rules (never
  mechanize a refuted statement; repairs to statements need sign-off).
  Candidate repairs for discussion: (i) add the premise "P0 is not a
  flexible variable" to the -var lemmas and handle flexible payloads at
  the callers via LE-FlexR + Ξc-extension (requires proving the
  mono-paintable/vacuity dichotomy for the flexible subcase of the
  non-var lemmas); (ii) rephrase the -var conclusion up to a
  Ξ-extension.  ALSO delivered this session (all Qed, statement-neutral,
  in prop_look_complete.v): `a_solve_eq_hole_subject_inv` (subject-□
  solve returns the target — the paper's silent `Pi = □` determinism),
  `uskl_rho_weaken` (Θ-binds-monotone), `binds_mid_drop`,
  `ad_partial_precise_strengthen_tvar(_mid)` (the binder cases' Θ-tvar
  strengthening), and `a_solve_eq_wf` (Δ-uniform wf preservation for
  a_solve_eq — discharges the paper's `Θ0 ⊢ Pa` conclusion outside the
  -var inductions).  Related audit observation to settle WITH the
  repair: `a_solve_eq__flex_r` demands `binds α abind_flex_mono Θ`
  (undefined only) where the paper's context-free FlexR fires on ANY
  hatted α̂ (full-algo-spec.tex:1374) — a defined-flex target with
  non-var/non-□ subject is solve-stuck in the mech but not on paper.
- 2026-07-24 (c): **P6 STARTED — ρ-representation DECIDED (+ corrected)
  and the full leaf/freshness infrastructure Qed, axiom-free** (new file
  `algo/prop_look_complete.v`; `p6_leaf_var` = Closed under the global
  context).  (1) ρ = the RELATION `uskl_rho` (refl + congruences + one
  replace-leaf; Δρ = replaced vars, Ψρ = replacement tags, union without
  cross-copy disjointness) — see the §7 DECISION block.  (2) **DESIGN
  CORRECTION discovered while drafting the leaf case:** the paper's
  positional side condition is LOAD-BEARING and not derivable from
  Δ-membership + precision (concrete counterexamples v4/v5 in §7:
  ∀◇-wrapped or definition-chained leaf positions force SE-GhostForall's
  `all_syn` output, which has no precision rule against a rigid var); it
  is instead RECOVERED as a lemma from FRESHNESS of the replaced
  variables (X ∈ Δ, `binds X abind_tvar Θ`, X ∉ κ-image-ftvs, X ∉
  Θ-definition-ftvs, X ∉ `pskl_shielded_ftv` of the subject) — all of
  which hold at the single leaf-creating call site (P6-Sv ForallL's fresh
  binder; the `a_wf_pskl__tophole` empty-Δ-body discipline supplies the
  shielded component).  Qed kit: `uskl_rho` + psi_cong/delta_mono/
  ftag_sub; `pskl_shielded_ftv` + open/msubst/painting bounds;
  `rho_fresh`; `ad_ppre_var_target_absent` + `ad_ppre_delta_var_inv` (the
  leaf inversion: subject IS `var X`, Ψ = ∅); `msubst_lookup_ftv_avoid` /
  `msubst_pskl_ftv_avoid` / `msubst_pskl_shielded_avoid` /
  `msubst_pskl_var_inv`; solve-cluster `a_solve_sub_eq_ctx_change` (+
  tvar strengthen/weaken) and `a_solve_sub_eq_rename` (rigid rename, for
  the cofinite SE/SS-Forall reassembly from one fresh witness);
  `a_solve_sub_eq_shielded` (output-shielded bound, for chaining the
  pack); `is_sskl_pskl_to_bskl_syn` / `ad_refine_syn_hole_sskl` /
  `ad_pat_consis_sskl_tags` (the P0 = □ special case).  P6-Cv STATEMENT
  DECISION: conclude with κ ITSELF (no κa existential — every -var case
  chooses κa := κ; the paper-shaped corollary is immediate); only
  P6-Cs/Ss/L extend κ (over Ξc / guess-Ξ').  NEXT: the 9 per-constructor
  `uskl_rho` inversion helpers, then P6-Cv's main induction
  (consistency-derivation outer, relation-inversion per case, paper's
  Pi-subcase analyses), with the ≡ˢ-precision transport NOT needed until
  a case actually produces κa ≠ κ (expected: never, in the -var pair).
- 2026-07-24 (b): **P5b-ii step (3) DONE — `ad_pat_sub_precise_upre`
  Qed, axiom-free** (commit f5b3e72; `Print Assumptions` = Closed under
  the global context; `make coq` green).  Precision-substitution
  (`lemma:precision-substitution`) in ⊑ᵤ-form over the hygienic mirror,
  FUEL-PRESERVING: all nine per-rule ⊑ᵤ-transports + the 12-case
  assembly.  The ForallL crux went exactly as scripted (fresh
  X ∉ dom Θb, body-⊑ᵤ, `uskl_precise_subst`, `subst_uskl_in_uskl_intro`
  both sides, recursion at `Ψsup ∖ Ψ'`); `all_inst` rebuilds the
  untagged ForallL with no ε-bookkeeping (sub-level ForallL does not
  consume its tag).  PAPER-GAPS entries written (global-freshness
  prose-completion + the two non-straightforward steps of the
  "straightforward induction").  **P5 is now COMPLETE except two
  deferred bridges:** (i) the subst-form corollary
  `S[Pa/α] ⊑ᵤ S[ψa/α]` (congruence walk + embedding at α-positions —
  build when P7b's ForallL constructs its pair); (ii) the `_n → _g`
  tag-renaming freshening bridge (only P7c consumes it).  NEXT: **P6**
  (`a_solve_complete_var` / `a_looksolve_complete` /
  `a_extract_complete_gen`) — remember the Infer/Check cases must re-route
  through `consis_complete`/`a_consis_complete` (the paper's
  consistency-side `-var` lemma was never mechanized; the μ-bundle
  route replaced it).
- 2026-07-24: **§5.4 EXECUTED through (2') and most of (3)'s
  infrastructure — all Qed, axiom-free** (commits b925723, 0eb95ff,
  a3da6b7).  DONE: ⊑ᵤ (`uskl_precise`) + full kit (psi_cong, ftag_sub,
  ftag_rep, lc_l, subst-compatibility, embedding
  `uskl_precise_of_precise`); **(2')** `ad_pat_consis_precise_upre` via
  `consis_split_transport` + 7 per-shape transporters; the hygienic
  mirror `ad_pat_sub_g` (`def_decl_algo_sub_hyg.v` — NB the REVISED fuel
  discipline: leaves at ANY fuel, UnivGhostL/LG/FlexMono NON-incrementing,
  only Arrow/ForallR/ForallL increment, so (3) is fuel-preserving even
  when the ghostier subject adds ∀◇-wraps or folds flex defs; P7b's
  measure is then lex(fuel, derivation-structure), which its
  non-incrementing cases support since they recurse structurally);
  `_g` helpers (g_of, g_psi_cong, g_ftag_sub, g_wrap_tophole,
  g_fold_flex, g_concrete_target, refl_transport, hole_intro,
  uskl_ghost_free_subst, mono_paint_guarded, uskl_precise_guarded); and
  per-rule ⊑ᵤ-transports for **UnivGhostR / Ghost / GhostG**
  (`ad_pat_sub_g_{ughost_r,ghost,ghostg}_transport`) — these validate the
  whole inner-⊑ᵤ-induction pattern: congruence roots rebuild via (2') on
  the reassembled pair, ∀◇/flex peels recurse at the SAME fuel via
  wrap_tophole/fold_flex, flex_r roots unfold the subject definition
  (consis_unfold_def_subject), hole roots go through
  hole_intro/concrete_target, refl roots through refl_transport.
  **REMAINING for (3)** (mechanical from the validated pattern):
  per-rule transports for **Arrow** (left premise via
  `ad_pat_consis_precise_upre` on the sub-⊑ᵤ, right premise via the main
  IH passed as a functional argument, per-branch splits by
  `diff/inter Ψsup` exactly as in (2')'s arrow transporter),
  **ForallL ×2** (the crux: pick a fresh X ∉ dom Θb, take the cofinite
  body-⊑ᵤ at X, `uskl_precise_subst` with ψ (lc via `is_tskl_lc`),
  rewrite both sides with `subst_uskl_in_uskl_intro`, recurse the main IH
  at Ψsup' := Ψsup ∖ Ψ' — all six side conditions verified in §5.4's
  worked notes; TY threads ghost-freeness via `uskl_ghost_free_subst` +
  the tags_sort-TY ghost-free component; all_inst rebuilds the UNTAGGED
  ForallL, cong rebuilds the same flavour; the sub-level ForallL does NOT
  consume ε so no ε-bookkeeping), **UnivGhostL/LG** (premise-pair via
  main-IH functional; keepg root maps LG→L), **FlexMono** (flex_r root =
  main-IH on the premise-pair against paint τ after binds_unique), then
  the 12-case **main assembly** `ad_pat_sub_precise_upre` (statement
  drafted in session notes: derivation-outer induction, Infer/Check
  direct via (2') + uskl_precise_guarded, ForallR direct via IH at the
  same ⊑ᵤ).  PROOF-ENGINEERING RULES learned: (i) per-rule transports
  MUST be standalone lemmas (clean contexts make Coq's auto-generated
  hypothesis names predictable: premises H/H0/…, sub-derivations
  Hup1/Hup2, IHs IHHup/IHHD); (ii) never let a ForallL bracket's
  `inter Ψ' …` goal reach fsetdec with Ψ' an evar — instantiate
  `with (Ψ' := Ψ')` (10-min hang otherwise); (iii) `repeat split` enters
  `[=]` — use explicit `split; [ | split ]`; (iv) `destruct (x == y)`
  may not match the `if` in a `subst`-reduced goal — use the
  `match goal |- context [if ?e then _ else _]` destruct.  THEN: P7c-side
  freshening bridge `_n → _g` (tag renaming, deferred), P6, P7,
  PAPER-GAPS entries (freshness prose-completion + the ForallL
  "straightforward induction" gap) once (3) is Qed.
- 2026-07-23: **P5b-ii steps (1)+(2) DONE, Qed, axiom-free; consis
  metatheory refactored out.**  New file `algo/prop_consis_precise.v`
  (the consistency subject-precision metatheory: general tag/wf helpers,
  crux (1a)/(1b)/(1), and NEW step (2) `ad_pat_consis_precise_subst` +
  its kit `ftag_in_uskl_open{_rec}_var`, painting-tag-free lemmas,
  `d_tags_skl_ftag`, `ad_pat_consis_ftag_sub` (ctx ⊆ subject tags),
  `ad_pat_consis_precise_var_case` (the packaged crux)); moved there
  from `prop_sub_complete.v`, which now holds only P5a + P5b-i (+ P5b-ii
  step (3) to come).  New leaf module `frost/def_tags.v`
  (`ftag_in_uskl`; folded into `frost/def_extra.v` 2026-08-06).  `make coq` green; `Print Assumptions` on
  `ad_pat_consis_precise_subst` / `ad_partial_precise_complete` /
  `ad_pat_sub_to_n` = Closed under the global context.  §5.4 written:
  step (3) needs the tag-HYGIENIC mirror `ad_pat_sub_g` (paper's
  `fresh Ψ'` is global — plain `_n` precision-substitution is FALSE
  under tag collisions) and the ⊑ᵤ subject-precision relation (the
  subst-form is too weak for its own ForallL crux).  NEXT: execute §5.4
  ((⊑ᵤ + kit) → (2') → `ad_pat_sub_g` + `g_ftag_sub` → (3)), defer the
  `_n → _g` tag-freshening bridge; THEN P6 (NB: the paper's P6a leans on
  `complete-consistency-cc-solving-var`, consistency-proofs.tex:1182,
  which the mech never built — consistency completeness went through the
  μ-bundle — so P6a's Infer/Check cases must re-route through
  `consis_complete` / `a_consis_complete` or grow a `-var` wrapper).
- 2026-07-22: doc written.  Soundness done.  Completeness = greenfield
  (inventory: no `a_sub_complete*`, no `ad_pat_sub_n`, no
  `precision_subst`; `a_consis_complete` Qed; build green, 0 admits
  in `frost/algo/`).
- 2026-07-22: **P5b-i DONE** — `ad_partial_precise_complete` **Qed, axiom-free**
  (`Print Assumptions` = Closed under the global context; `make coq` green).
  Target confirmed COLOURED `ad_precise`; needs `a_wf_aenv Θ` + `a_tags_sort`
  + wf `⌊ψ⌋` premises.  Supporting lemmas built (all in `prop_sub_complete.v`):
  `pskl_no_forall`(+`_inh_eq_syn`), `d_tags_empty_no_forall`,
  `a_wf_pskl_delta_narrow`/`_strip`, `ad_partial_precise_tags_sub` (the
  Ψ⊆tags invariant), `d_tags_skl_{unit,var,arrow,all_etag,topholeg}_inv`,
  `d_tags_skl_recong`, `a_tags_sort_{d_tags,psi_cong,arrow_inv,all_etag_inv}`,
  `a_wf_pskl_{all,tophole}_inv`.  LESSONS confirmed vs the design guess: the
  arrow/forall cases DO need the disjointness argument (`tags_sub` + set
  algebra pins `Ψ1 = d_tags ψ1` via `psi_cong`) — the "no disjointness" note
  in §5.1 was wrong.  tophole_fill vacuous via `tags_sub` as planned.  flex
  cases: `a_wf_ptyp` is tvar-only ⇒ def bodies are flex-free ⇒ wf of the mono
  paint holds (`a_scope_pskl_of_ptyp_vis`).  COQ GOTCHA (cost a 9-min hang):
  never `fsetdec` a psi_cong EVAR goal — build `a_tags_sort NM empty` concretely
  first, THEN `psi_cong; [exact … | fsetdec]` (memory rule).  NEXT P5b-ii:
  `ad_pat_sub_precise_subst` (fuel-preserving; state the subject-subst form
  `S[ψa/α]` vs `S[Pa/α]` against how P6/ForallL build it — finalize when P6
  consumes it).
- 2026-07-22: **P5a DONE** (axiom-free, full `make coq` green).
  `ad_pat_sub_n` (fuel mirror, `def_decl_algo_sub.v`, appended — no
  cascade into soundness) + `prop_sub_complete.v` with
  `ad_pat_sub_of_n`, `ad_pat_sub_n_succ`, `ad_pat_sub_n_mono`,
  `ad_pat_sub_n_rename_tvar` (fuel-preserving tvar rename, mechanical
  mirror of the non-fuel `ad_pat_sub_rename_tvar`), and `ad_pat_sub_to_n`
  (needs `a_wf_aenv Θ` — the consumer has it — to discharge the rename's
  def-freshness via `a_wf_aenv_def_ftv_dom`; binder cases pick a fresh
  witness and transport its fuel by rename).  `Print Assumptions` on
  `of_n`/`to_n`/`n_mono` = Closed under the global context.  NEXT: P5b
  (`ad_partial_precise_complete`, then fuel-preserving
  `ad_pat_sub_precise_subst`).  NB the single non-paper hypothesis added
  so far is `a_wf_aenv Θ` on `to_n` — standard, available downstream, not
  a statement weakening.

### (a3) P6-Sv CLOSED (2026-07-29) — the two remaining cases, and a SECOND statement change

`a_solve_sub_complete_var` is `Qed` and axiom-free.  Two things beyond the
`flex_shield` repair of (z)–(a2) were needed.

**1. Arrow — `arrow_grid`.**  The branch algebra (tag split, P6-Cv on the
left premise, IH on the right) is packed into a `KEY` hypothesis, so the
lemma itself is only the case analysis on the input skeleton `Pi`: arrow /
□ (SolS-GhostLF) / ∀◇ / variable, with unit and ∀ refuted by the precision
against an arrow guess.  The variable row needs no solving at all — the
κ-image of a variable is a MONOTYPE, so `ad_ppre_mono_subject_target_tags_
empty` makes the guess tag-free and `Ψa = ∅`.  The ∀◇ row recurses
STRUCTURALLY on `Pi`, no measure: well-formedness makes the ghost's body
guarded, so the FILL/KEEP rows cannot fire.

**2. Sub-ForallL — ρ absorbs the instantiation, and the CONTEXT must
generalize.**  The rule's instantiation becomes the paper's
`ρ_b = ρ ∘ [ψ_b/β]` (`uskl_rho_subst`), so the recursive call runs at
`Δρ,β`.  Two consequences:

- `rho_fresh` insists every ρ-replaced variable be a RIGID OF THE CONTEXT,
  and the opened `Pi`-body must be well-formed, so the IH has to run at
  `Θ0,β / Θ,β`.  But `ad_pat_sub_g`'s context is an INDEX, so `induction`
  freezes it — the IH is only ever available at the original `Θ`.  FIX: the
  derivation now lives in a smaller `Θs`, and every other premise in a `Θ`
  related to it only by `binds`-monotonicity (`forall x b, binds x b Θs ->
  binds x b Θ`).  At the top level `Θs = Θ` and the premise is the identity;
  inside, each rule premise stated in the small context is weakened on the
  spot, so all previously closed cases read unchanged.  This is the mech's
  reading of the paper's "by weakening \refn[9] to Θ,β"
  (subtyping-proofs.tex:2153).
- β joins Δρ, so `Hshield` must hold for it: `β ∉ pskl_shielded_ftv (κ Pi)`.
  That is exactly the ∀◇-body discipline DESIGN §7 names in prose, and it is
  now a LEMMA — `a_wf_pskl_shielded_dom`: since `a_wf_pskl__tophole` types
  the ghost's body at the EMPTY Δ, a well-formed skeleton's shielded
  variables all live in `dom Θ`, never in Δ.

**The `Pi` grid has ONE live row** (`Pi = ∀β.P1`, the paper's).  Every other
shape would have to solve the top-level tag ε, and ε is already in `Ψi` —
proved, not assumed: `ε ∉ ftag R` (ρ only ADDS tags,
`uskl_rho_ftag_target_sub`, together with `Ψρ ∩ Ψ' = ∅` and sortedness of
ψa) and `ε ∉ ftag ψ_b` (the rule's own freshness) bound the premise's solved
tags via `ad_pat_sub_g_ftag_sub`, giving `ε ∉ Ψsub ⊇ Ψa`, hence `ε ∈ Ψi` by
`Ψi,Ψa = Ψ'`.  So □ (`Ψi = ∅`), ∀◇ (both its rules), the variable row and
the structural rows are all IMPOSSIBLE.

**Rebuilding the ∀.**  The output is re-abstracted with
`close_pskl_wrt_pskl β`, and the single instance becomes SolS-ForallL's
cofinite family by rigid renaming (`a_solve_sub_eq_rename`), as in ForallR.
The PRECISION needs the converse of `a_wf_pskl_delta_to_tvar_mid`, which did
not exist: `ad_partial_precise_tvar_to_delta_mid` — a rigid binder ALREADY
in Δ may be dropped from the aenv.  (`ad_partial_precise_strip_tvar_mid`
cannot be used: it wants β free in NEITHER side, and here β is free in
both.)  Then `ad_partial_precise_rename` moves β to the family's α.

**Gotchas.**  `a_wf_aenv__tvar` takes the FRESHNESS first — a wrong bullet
order surfaces as "No matching clauses for match", because `match goal`
backtracks when its BODY fails, not its pattern.  `Ψ0` must be PINNED with
`with (Ψ0 := …)` on `ad_ppre__forall`, or the tag side condition's `fsetdec`
runs forever on an evar.  And Ltac cannot resolve a `rename`-introduced name
inside a `match goal` PATTERN — match on the weakening hypothesis and bind
the context as `?S`.


## 7. P6 plan (audited 2026-07-24; execute next)

> **UPDATE 2026-07-25 (read with §6 (g)).**  This plan STANDS: `uskl_rho`
> (the ρ relation) and the Pi-side positional condition recovered via the
> freshness pack (`ad_ppre_delta_var_inv` / `shielded_ftv`) are the committed
> P6 infrastructure and are NOT affected by the revert — only the LATER
> `pskl_dominates_rho` P0-side experiment (§6 (d)–(f)) was reverted.  What
> this section did not yet account for is the flexible-`P0` subcase of the
> Arrow case; per §6 (g) it needs NO P0-side condition. (a) ForallInh/
> ForallSyn/ghost cases prove `P0` non-flexible for free (κ maps flexibles to
> monotypes; refinement into a ∀/∀◇ needs a ∀/∀◇/defined-flex source). (b)
> Leaf cases handle a flexible `P0` directly (SolE-Flex / SolE-Var). (c) The
> Arrow case handles a flexible `P0` via SolE-FlexR like the leaf case,
> relying on LE-FlexR FRESHENING (a raw Θ0-flex opposite a ρ-substituted rigid
> var is not producible — `algo/cex/cex_p6_flex_freshened.v`). So the P6-Cv/Sv
> statements need only the ρ/Pi machinery below, plus these flex-case
> observations — no symmetric P0-side predicate.

**Correction to the earlier P6 note.**  The paper's consistency-side
lemmas (complete-consistency-cc-solving(-var), consistency-proofs.tex:921
/1182) are about the **constraint cluster** `a_lookeq`/`a_solve_eq` —
defined MUTUALLY with `a_looksub`/`a_solve_sub` in algo/def_extra.v
(299-469) — NOT about the μ-bundle's `a_consis` join.  The μ-bundle
cannot stand in for them; they must be mechanized as their own
inductions.  P6 therefore has FIVE lemmas, in dependency order:

| # | lemma | paper | conclusion judgments | induction on |
|---|---|---|---|---|
| P6-Cv | `a_solve_eq_complete_var` | consistency-proofs 1182 | `a_solve_eq` | the `ad_pat_consis` derivation of the ρ(ψa)-subject |
| P6-Cs | `a_lookeq_solve_complete` | consistency-proofs 921 | `a_lookeq` + `a_solve_cstr`-per-constraint | ad_pat_consis of `(κS)[ψa/α]` |
| P6-Sv | `a_solve_sub_complete_var` | subtyping-proofs 1697 | `a_solve_sub` | `ad_pat_sub_g` of ρ(ψa) (fuel rides) |
| P6-Ss | `a_looksub_solve_complete` | subtyping-proofs 2203 | `a_looksub` + `a_solve_cstr` | `ad_pat_sub_g` of `(κS)[ψa/α]` |
| P6-L | `a_extract_complete_gen` | subtyping-proofs 2730 | `a_extract` + plain precision | wraps P6-Ss; `ad_partial_precise_complete` upgrades ⊑ᵖ to ⊑; the TY guess needs a NEW sub-induction — see §7.3 |

Existing support (audited, all Qed): prop_looksub.v has decls/ftv/
absent-nil/subst-stable/rename-var for `a_looksub`/`a_lookeq` +
`a_extract_decls` + `a_extract_output_fresh`; prop_solve_sub.v has
lc/guarded/ftv preservation for `a_solve_sub`/`a_solve_eq`.  No
completeness lemmas exist for any of them.  `guess_join_witness`
(prop_consis_complete.v:4627, Qed) provides exactly the P6-L TY-witness.

**THE design decision to make first: representing the paper's ρ**
("capture-avoiding substitution from rigid type variables to decorated
skeletons", with the side condition that Pi has the SAME rigid variable
at every ρ-substituted position).  ρ accumulates as P6-Ss's induction
walks under ψa's own ForallLs (each declarative instantiation β ↦ ψ''
extends ρ), while the algorithm's Pi keeps β rigid at that position.
Candidates:
  (a) explicit multi-substitution `list (atom * uskl)` + a subst
      function + the position side condition as a separate predicate;
  (b) a RELATION in the ⊑ᵤ style (the P5 lesson: relations beat
      substitutions for these inductions): `ψsub ⊒ρ[Ψρ] ψa` — decorated
      congruences + one replace-leaf `β ↦ ψ''` (β rigid,
      `a_tags_sort NM Ψ'' ψ''`, wf ⌊ψ''⌋), Ψρ collecting replacement
      tags; the Pi-position condition then couples this relation with
      the partial-precision derivation `κPi ⊑ᵖ[Ψi] ψa` (whose var-rule
      must be what fires at replace-leaf positions).
Start by DRAFTING P6-Cv's statement both ways against the paper's
Check-case usage (subtyping-proofs.tex:1770-1785, which instantiates
ρ := ρ|premise) and pick whichever discharges that call site with less
glue.  Expect (b).

**DECISION (locked 2026-07-24): (b), the relation `uskl_rho`.**  Both
drafts pass the Check call site verbatim (sub/consis premises share the
subject), so the discriminators are elsewhere, and all favour (b):
1. Arrow: the paper's ρ1/ρ2 restriction exists only to make "Ψ introduced
   by ρ" positional; a shared variable in both branches makes the
   list-form tag set NON-positional (copies share tags — the same
   cross-copy phenomenon P5's ⊑ᵤ met).  The relation localizes Ψρ per
   branch by inversion; per-branch (Ψn_i, Ψna_i) are recovered
   set-algebraically as Ψf_i∖Ψ' / Ψf_i∩Ψ' using `inter Ψρ Ψ' = ∅` +
   `ad_pat_consis_ftag_sub` + tags-uniqueness of ψa.
2. ForallL (P6-Sv): relation extension = one subst lemma
   (`uskl_rho_subst`, mirror of `uskl_precise_subst`); list form = a
   hand-rolled capture-avoiding multi-subst kit + commutation lemmas.
3. The positional side condition ("Pi has the same rigid variable at
   every ρ-position") is replaced by FRESHNESS facts about the replaced
   variables — NOT by mere Δ-membership.  **Counterexample analysis
   (2026-07-24, do not re-derive):** Δ-membership alone is INSUFFICIENT.
   With X ∈ Δ ∩ dom Θ, precision still admits a ∀◇-wrapped leaf position
   via `tophole_remove` (v4: `Pi`-pos `∀◇.ŵ`, ŵ ∈ Θ0 flex, κŵ = X — wf,
   since the ∀◇-body is ŵ, not X) or via def-chains (v5: κŵ = β̂,
   `β̂ := X ∈ Θ`); then target-pos `all_syn` (P0-pos `∀γ.γ`, image
   ψ'' = `∀^ε'γ.γ`, refinement satisfied through `all_inh`) forces
   SE-GhostForall, whose `all_syn`-output has NO precision rule against
   the rigid `var X` — conclusion underivable, all premises satisfied.
   What kills v4/v5 at the REAL call site (P6-Sv ForallL, X freshly
   opened from `Pi = ∀β.P1`): (i) X cannot occur under any ∀◇ of P1 —
   `a_wf_pskl__tophole` demands empty-Δ bodies (the "no binder under a
   ∀◇-body" discipline recorded on `a_sub__forall_l`); (ii) X postdates
   every flex-image of κ (κ ∷ Θ0 ⊑ Θ is fixed before X is picked); (iii)
   X postdates every definition in Θ (aenv order: `(X~tvar)++Θ`, wf
   scopes defs to their tails).  MECHANIZATION: carry a freshness pack
   `∀X ∈ Δρ`: `X ∈ Δ` (blocks the hole rule), `binds X abind_tvar Θ`
   (blocks flex_r, via wf-uniq), `X ∉ msubst-image-ftv of κ`,
   `X ∉ def-image-ftv of Θ`, `X ∉ shielded_ftv (msubst κ Pi)` — where
   `shielded_ftv : pskl → atoms` is a NEW syntactic collector of the
   ftvars of all ∀◇-bodies.  The LEAF INVERSION lemma then holds:
   `⊑ᵖ (P, var X)` + the pack ⇒ `P = pskl_var_f v` (v = X or a flex) ∧
   `Ψ = ∅` — so `Pi`-pos is a var and SE-Var fires with κa := κ.
   For CHAINING (a_solve_cstr threads outputs into the next constraint's
   Pi; the arrow case threads κ1 into branch 2), the CONCLUSIONS must
   return the pack for (κa, Pa): add `∀X∈Δρ, X ∉ msubst-ftv κa ∧
   X ∉ shielded_ftv (msubst κa Pa)`.  Supporting kit:
   `shielded_ftv(out) ⊆ shielded_ftv(subject) ∪ ftvar(target)` for
   a_solve_eq/a_solve_sub (mutual, alongside the existing
   `a_solve_sub_eq_ftv`), plus msubst/constructor distribution lemmas.
   ⇒ [paper-gap] entries: (1) the prose side condition must be read as
   these freshness facts — its ForallL-maintenance ("Guaranteed by the
   fact that ρ comes from instantiation") is a genuine argument needing
   (i)-(iii), not an observation; (2) v4/v5 document why weaker readings
   are false.

Shape of `uskl_rho` (in the new algo/prop_look_complete.v):
`uskl_rho (NM : a_sub_mode) (Θ : aenv) : atoms(*Δρ*) -> atoms(*Ψρ*) ->
uskl -> uskl -> Prop` — REFL (lc, Ψρ=∅; identity-ρ call sites),
same-constructor congruences (arrow, all_syn, all_etag same-tag,
tophole, topholeg; cofinite binders; Ψρ = union, NO cross-copy
disjointness), and the LEAF `ψ'' ⊒ var X` with `X ∈ Δρ`,
`a_tags_sort NM Ψ'' ψ''`, wf `⌊ψ''⌋`, `Ψρ [=] Ψ''`.  No functionality
(same X may map to different images at different leaves — no proof step
needs sameness).  Kit: psi_cong, ftag_sub (`ftag ψsub ⊆ Ψρ ∪ ftag ψa`
-ish), lc, and `uskl_rho_subst` (one-sided: `[ψb/X]` on the LHS turns
X-refl/congruence-var occurrences into leaves; RHS unchanged).
Tag premises in the lemma statements (replacing the paper's "Ψ
introduced by ρ" prose): `Ψfull [=] Ψn ∪ Ψna`, `Ψna ⊆ Ψ'`,
`inter Ψn Ψ' [=] ∅`, `inter Ψρ Ψ' [=] ∅` (the paper's global
`fresh Ψ'`), precision premise at `Ψi ⊆ Ψ'`, conclusion precision at
`Ψi ∪ Ψna`.  a_solve_eq/a_solve_sub conclusions at Θ0 (tvar-entry
strengthening lemma needed for the ForallInh/ForallR cases).

Other observations for the statements:
- `solveeq{Pi}{P0}{Pa}` = `Θ? ⊢ₑ Pi ∼ P0 ⤳ Pa`: pick the aenv index
  against a_solve_eq's flex_r rule (binds α abind_flex_mono) — the -var
  lemmas run at Θ0 (the algorithm's context).
- `solve{C}{Pi}{Pa}` in P6-Cs/Ss is per-constraint discharge —
  `a_solve_cstr Ξc C Pi Pa` (note the CONTEXT of a_solve_cstr in
  a_extract is Ξ, the collected fresh flexibles).
- The `Ψi,Ψa = Ψ'` (subtyping) vs `Ψi,Ψa ⊆ Ψ'` (consistency) asymmetry
  is real (WT's comment) — keep it.
- P6-Sv's Check and Arrow-left cases invoke P6-Cv; P6-Ss's crux
  (subject = the looked-for α's position) invokes P6-Sv; P6-Cs's crux
  invokes P6-Cv.  So build order: P6-Cv → P6-Cs → P6-Sv → P6-Ss → P6-L.
- The declarative-side judgments to induct on: `ad_pat_consis` for
  P6-Cv/Cs (no fuel needed — no ForallL inside consistency), and
  `ad_pat_sub_g` for P6-Sv/Ss (hygiene needed for the same reason as
  P5b-ii: the subject carries ψa/ρ-copies whose tags must stay disjoint
  from inner instantiations; fuel rides inertly and is what P7b's
  measure consumes).
- P6-L additionally needs: `a_extract`'s Ξ-freshness prose-completion
  (already a premise on `a_sub__forall_l` — mirror it), and the
  `⊑ᵖ → ⊑` upgrade at the END via `ad_partial_precise_complete`
  (P5b-i, Qed) exactly as complete-look's proof does at tex:2764.

### 7.1 P6-Cs execution note (drafted 2026-07-27, after Task A)

Reconnaissance (signatures verified in-tree):
- Induct on **`ad_pat_consis`** (`Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q`, def_decl_algo.v:52-120;
  ctors unit/var/arrow/forall_inh_{tagged,untagged}/forall_syn{_tagged,}/
  ghostg/topholeg/hole/tophole/tophole_inh/tophole_drop/flex_{l,r}).  NO fuel.
- Conclusion judgments: **`a_lookeq α P P0 C Ξc`** (def_extra.v:330) and
  **`a_solve_cstr Ξc C Pi Pa`** (def_extra.v:482).  NB: the accumulated-
  □-or-hole-free side condition is **no longer needed** — the
  `pskl_no_hole P0` premise was removed (see §6, 2026-07-27), so P6-Cs
  mirrors the paper directly with no `P0 = □ ∨ pskl_no_hole P0` thread.
  (Task A's `prop_accum_no_hole.v`, which would have discharged it, was
  deleted accordingly.)
- Model the STATEMENT on `a_solve_eq_complete_var` / `_gen`
  (prop_look_complete_var.v:3047 / :480), NOT on the P5 `consis_complete`
  driver (prop_consis_complete.v:8611, which uses `a_inc_equiv`+`msubst_compose`
  optimality — the wrong shape here).  Reuse verbatim: `⊑ᵖ`
  (`ad_partial_precise`, def_decl_algo_sub.v:221), `a_inc` (`∷⊑`,
  def_meta.v:184), `a_inc_equiv` (`κ≡κa`, def_meta.v:245), `a_tags_sort`
  (def_decorated.v:96), `ad_refine_syn` (`⊢ᵣᵃ`, def_decl_algo.v:126).

**Open DESIGN DECISION to make FIRST — how to encode the subject
`(κ S)[ψa/α]`.**  Unlike P6-Cv (whose subject `ψsub` is `uskl_rho`-related to
a single `ψa`), the P6-Cs paper subject is `κ` painted over the DECORATED
skeleton `S` (erase S = P) with the single flex `α ↦ ψa`.  No `erase : uskl →
pskl` and no separate `S` currently exist.  Two candidate encodings:
  (a) carry `S : uskl` with a NEW `uskl_erase S = P` premise and subject
      `subst_uskl_in_uskl ψa α (msubst_uskl κ S)` — most paper-faithful but
      needs the erase relation + its interaction lemmas with msubst/subst;
  (b) reuse `uskl_rho` with `Δρ := {α}` and the `urho__leaf` rule mapping
      `α ↦ ψa` (α∈Δρ, treated as the "replaced variable"), subject the
      `uskl_rho`-image of the painted `P` — leverages ALL of P6-Cv's kit
      (`urho__*` inversions, flex_apart, precision transport) at the cost of
      re-reading `[ψa/α]` as a one-leaf ρ.
  RECOMMEND (b): the P=α special case then IS `urho__leaf` at the single α,
  and the P6-Cv call there degenerates to `urho__refl` on ψa exactly as the
  paper says ("identity substitution, empty tag context").  Decide by drafting
  the P=α and Arrow cases both ways against the P6-Cv corollary call site.
- Special cases (paper order, all BEFORE the induction split): `P0=□` →
  LE-Vacuous, `C=·`, `Pa=Pi`, `κa=κ` (uses Task-A: refinement inversion gives
  Q synthesised ⇒ Ψa=∅); `P=α` (so S=α) → LE-Var + invoke `a_solve_eq_complete_var`
  with identity ρ (`urho__refl`, `Δρ:=∅` ⇒ `flex_apart` via `fa_clean`,
  `rho_fresh` trivial); `α∉ftv P` → LE-Absent, `C=·`.  Induction cases:
  ForallInh (LE-ForallInh, β-weakening + `β∉ftv Pa`), ForallSyn (LE-ForallSyn,
  P0=∀◇P0' by refinement inversion since P0≠□), Arrow (LE-Arrow + sequential
  `a_solve_cstr`, mirror `consis_complete`'s `Ψ[=]Ψ1∪Ψ2` split), UnivGhost*
  (UnivGhost / UnivGhost1 / UnivGhost2-with-P0-case-analysis).
- P6-Cs omits `Θ0 ⊢ Pa`-style solve-output wf that its own conclusion needs;
  add a solve-output wf-preservation lemma (`a_solve_cstr`/`a_solve_eq`
  preserve `Θ0,Ξc ⊢ₚₛᵃ`) when the conclusion requires it.
- STATUS (2026-07-27, updated): encoding LOCKED to (a-lite) — see §7.2;
  statement DRAFTED + type-checks in `frost/algo/cex/p6cs_dev_tmp.v`; the THREE
  special cases (P0=□, P=α via the P6-Cv corollary, α∉ftv P) are PROVEN, plus
  the reusable helpers `ad_partial_precise_psi_cong` (Qed, migrate to
  prop_precise.v) and `pskl_hole_dec`/`pskl_var_dec`; `a_solve_eq_wf` (existing)
  discharges the solve-output wf.  ONE admit left = the MAIN INDUCTION (P0≠□,
  P≠α, α∈ftv P).  Reused: `a_solve_eq_complete_var` (P6-Cv corollary) at the
  P=α leaf with `urho__refl`/Δρ:=∅/`fa_clean`; `ad_pat_consis_sskl_tags` +
  `ad_refine_syn_hole_sskl` (P0=□); `ad_pat_consis_ftag_sub` +
  `subst_uskl_in_uskl_fresh_eq` + `msubst_pskl_ftv_avoid` +
  `a_inc_image_ftv_dom` (α∉ftv P).  **Main-induction plan:** `induction
  Hconsis` on the GENERAL statement (do NOT dispatch special cases at top —
  the IH must stay general; the current scratch's top-level dispatch is a
  scaffold to be folded per-case).  In each consistency case: (i) invert
  `subst_uskl_in_uskl ψa α R` on R's shape (R=`uskl_var α` → the P=α leaf,
  delegate to P6-Cv; congruence → structural); (ii) dispatch P0=□ (LE-Vacuous)
  and α∉ftv P (LE-Absent); (iii) structural: build `a_lookeq` via the matching
  LE-rule + thread `a_solve_cstr` (Arrow = sequential `a_solve_cstr__eq`/
  `__sub`, Ψ split like `consis_complete`), applying the IH to sub-derivations;
  ForallInh/ForallSyn extend Θ,β with front-weakening (β∉ψa,β∉Pa so precision
  conclusion drops β; ForallSyn's refinement is tophole_fill — align its
  cofinite binder with the consistency binder X).  Tag bookkeeping mirrors
  P6-Cv's arrow-split (`ftag_in_uskl R` in place of Ψρ).

### 7.2 P6-Cs ENCODING DECISION — CORRECTED to (a-lite), locked 2026-07-27

**⚠️ (b) as first drafted is WRONG — `uskl_rho` is TOO LOOSE.**  Its
`urho__leaf` allows an ARBITRARY tags-sorted image `ψ''` at each α-position,
but the P6-Cs subject `[ψa/α]` substitutes the SAME single `ψa` at every
occurrence, and that `ψa` is also the single precision target
(`κPi ⊑ᵖ ψa`) fed to P6-Cv at the leaf.  With per-leaf-arbitrary images the
delegation to P6-Cv cannot type: P6-Cv's `ψa` would have to equal both the
leaf image AND the global precision target.  So the images must be pinned to
`ψa`, which `uskl_rho` does not express.

**Decision: encoding (a-lite) — `subst_uskl_in_uskl ψa α R`.**  The
uskl-for-var substitution `subst_uskl_in_uskl : uskl → usklvar → uskl → uskl`
ALREADY EXISTS (def_ott.v:487, full lngen kit: open/subst commutation, spec,
fresh_eq, lc, degree) — `S[ψa/α] = subst_uskl_in_uskl ψa α S` (the P5b-ii
convention).  So:

1. Carry `R : uskl` (playing `syn κS`) tied to P by
   **`⌊ R ⌋ˢ = msubst_pskl κ P`** — erasure commutes with the monotype
   substitution κ, so `erase(κS) = κ(erase S) = κP`.  `msubst_uskl` is NOT
   needed: R is posited, not built.
2. **The consistency subject is `subst_uskl_in_uskl ψa α R`** — this PINS
   every α-image to the one `ψa`, exactly `(κS)[ψa/α]`.  Inverting it against
   the consistency derivation is the same leaf/congruence split as `uskl_rho`
   but via the Fixpoint's computation: `subst_uskl_in_uskl ψa α R = arrow …`
   forces R = `uskl_var α` (leaf, subject = ψa, the P=α case) or R = arrow
   (congruence).  At each node `⌊R⌋ˢ = msubst_pskl κ P` recovers P's shape
   (msubst_pskl is structural on non-var P; the bare-var P cases are the
   `P=α` / `α∉ftv P` special cases).
3. **`uskl_rho` is used only at the P6-Cv DELEGATION** (P=α leaf): the P6-Cv
   corollary takes a `uskl_rho` premise, discharged by `urho__refl` on ψa
   (Δρ:=∅, ρ=id) — "the identity substitution, empty tag context" the paper
   names.  So P6-Cv's own kit is reused wholesale at the leaf; P6-Cs's own
   induction uses `subst_uskl_in_uskl`, not `uskl_rho`.

3. **P6-Cs is SIMPLER than P6-Cv — NO `flex_apart`, NO freshness pack, NO
   aenv-split `_gen`.**  P6-Cs's induction recurses via ITSELF (the paper's
   Arrow case applies IH twice + LE-Arrow + sequential solving; ForallInh/Syn
   apply IH under Θ,β), and reaches the α-leaf ONLY through the `P=α` special
   case, which invokes the `a_solve_eq_complete_var` COROLLARY with the
   identity ρ (`urho__refl` on ψa, `Δρ := ∅` ⇒ `flex_apart` discharged by
   `fa_clean`, `rho_fresh`/shielded trivial).  The freshness pack and
   flex_apart were needed in P6-Cv only for the rigid-var leaf inversion of
   the PRECISION premise against ρ(ψa); in P6-Cs the precision premise is on
   ψa directly (unchanged by the [ψa/α] substitution) and the leaf is
   delegated, so none of that machinery threads into P6-Cs's own statement.
   The ForallSyn tophole_fill aenv-extension (P6-Cv's old blocker) is benign
   here: the consistency ForallSyn binder X and the refinement tophole_fill
   binder align (instantiate the refinement's cofinite family at X), and the
   precision conclusion `κa Pa ⊑ᵖ ψa` never sees X (X∉ψa, X∉Pa), so no
   aenv→Δ transport is required — plain front-extension weakening suffices.

4. **Tag bookkeeping.**  ψa's tags = Ψ' (`a_tags_sort NM Ψ' ψa`).  The
   consistency index `Ψsub` decomposes as `Ψ ∪ Ψa`: Ψ = R's own decoration
   tags (S's ∀^δ tags = `ftag R`, disjoint from Ψ' since S's binders are not
   ψa's instantiation tags), Ψa ⊆ Ψ' = the ψa-leaves' contribution
   (= `uskl_rho`'s Ψρ role).  This mirrors P6-Cv's arrow-split tag algebra
   (`ad_pat_consis_ftag_sub` + `uskl_rho_ftag_sub` + d_tags uniqueness);
   exact premise shapes to be finalized against the Arrow-case proof.

5. **a_solve_cstr context = `Ξc ++ Θ0`** (Ξc = fresh flexibles from LE-FlexR,
   at the front).  Degenerate at the P=α leaf: Ξc = [] ⇒ `Θ0 ⊩ eq(P0) :: · ⨾
   Pi ⤳ Pa` unfolds to `a_solve_eq Θ0 Pi P0 Pa` = the P6-Cv corollary output.

Scratch: `frost/algo/cex/p6cs_dev_tmp.v`.

- **STATUS (2026-07-28): CLOSED.**  `a_lookeq_solve_complete` is `Qed` and
  axiom-free in `frost/algo/prop_look_complete_cstr.v` (0 admits); the scratch
  `cex/p6cs_dev_tmp.v` is gone.  Two deviations from the plan above are worth
  recording:
  1. the main induction is on `size_uskl S + size_pskl P0`, NOT on the
     consistency derivation — a measure induction keeps the three special-case
     proofs verbatim (they need the whole `Hconsis`, which `induction Hconsis`
     would have destructed) and hands back a GENERAL `IHn`;
  2. the statement carries one extra premise, well-formedness of the
     CONSISTENCY SUBJECT.  It is load-bearing, not cosmetic: without it the
     lemma is false (machine-checked counterexample in
     `cex/cex_p6cs_subject_wf.v`, registered in docs/WF-SIDE-CONDITIONS.md).
  The ∀-binder kit, the two ftv transports behind "Pi and 𝒞 cannot contain β",
  and `a_looksub_lookeq_rename_tvar` are all in the same file and are what
  P6-Ss should reuse.

## 8. P6-Ss plan (drafted 2026-07-29, after P6-Sv closed)

`lemma:complete-constraint-collection-solving` (subtyping-proofs.tex:2202),
the subtyping twin of the CLOSED P6-Cs (`a_lookeq_solve_complete`).  Target
file `frost/algo/prop_look_complete_sub_cstr.v`.

### (a) The paper's P6-Ss INHERITS P6-Sv's falsity — same witness

Its first special case ("If `P = α`, then `S = α`") applies P6-Sv **with the
identity substitution**, i.e. at `Δρ = ∅`, `Ψρ = ∅`.  That is EXACTLY the
configuration of `cex/cex_p6sv_forall_flex.v`, and the witness transports:
take the LOOKED-FOR variable `α'` — the one the lookup judgment
`looksub α' P P0 ⤳ Ξ ⨾ 𝒞` searches for, which P6-Ss requires to satisfy
`α' ∉ dom Θ` — and set `S = R' = α'`.  Since κ substitutes FLEXIBLES only
and `α'` is fresh for Θ hence for `dom κ`, we get `κ S = κ α' = α'`, so the
subject `(κ S)[ψa/α']` IS `ψa = ∀^ε β.β→β`.  κ does its work on the other
side of the witness: `P0 = α̂` with `κ = [α̂ ↦ ⟨⟩→⟨⟩]`, so
`κ P0 = ⟨⟩→⟨⟩`, which is what the refinement premise
`Θ ⊢ inh(κ P0) ⊳ Q` uses to reach `Q = inh{⟨⟩→⟨⟩}`; and `Pi = ∀β.β→β`.  `a_looksub` has NO FlexR rule, so LS-Var is FORCED and
`𝒞 = [ ≼[M] P0 ]`; solving it is the P6-Sv leaf, which the cex refutes.  So
P6-Ss must carry the SAME repair, and the mechanized statement does.

### (b) The repair premise — a P0-ONLY walk

P6-Sv's `flex_shield Θ0 Ψ' Δρ P0 ψa` pairs P0 and ψa *positionally*, both
descending together.  P6-Ss's recursion is different: **ψa is FIXED** (it is
the single guess for α) while P0 descends, so the pairing at a leaf is
(P0-subterm, the WHOLE ψa).  Only two of P6-Ss's cases move P0:

- Sub-Arrow takes the RIGHT component (the left one goes to P6-Cs, which
  needs no shield — consistency has no ForallL, so tags never become dirt);
- Sub-ForallR opens the body.

`flex_shield` supports the second (`fsh_all_l`) but NOT the first: `fsh_arrow`
descends both sides at once.  So P6-Ss threads the walk-closure, exactly as
P6-Sv threads `flex_apart_walk`:

```
Inductive ss_step : pskl -> pskl -> Prop :=      (* P0-only descents *)
| sss_arrow_r : ss_step (P1 → P2) P2
| sss_all     : ss_step (∀.P0)    (open P0 γ).

Definition sub_shield Θ0 Ψ' P0 ψa : Prop :=
  forall P0', ss_walk P0 P0' ->
    flex_apart_walk Θ0 empty P0' ψa /\ flex_shield Θ0 Ψ' empty P0' ψa.
```

It descends for free (`ss_walk` is transitive) and hands P6-Sv both of its
premises at the leaf, via the reflexive step.  NB `flex_apart_walk` must be
carried too: P6-Cs discharges P6-Cv's `flex_apart` with `fa_clean` at
Δρ = ∅, but `fsh_clean` additionally demands TAG-freeness, which a tagged ψa
does not have — so the two cannot be merged (see §6 (a3) and the note at
`flex_apart_walk`).

### (c) The measure — NOT P6-Cs's

P6-Cs induces on `size_uskl R' + size_pskl P0`, which works because
consistency's ∀ rules open with a VARIABLE (size-preserving).  Subtyping's
**Sub-ForallL opens with the GUESS** `ψ_b`, so `size (open R ψ_b)` can be
arbitrarily larger — the P6-Cs measure is unusable.  Use the
`ad_pat_sub_g` DERIVATION instead, as P6-Sv does; its fuel decreases on
ForallL / Arrow / ForallR, and the fuel-preserving rows (UnivGhostL/LG,
FlexMono) shrink the subject.  Since the subject is the compound
`(κ R')[ψa/α]`, the derivation has to be `remember`ed and the shape equation
inverted per rule — the same bookkeeping P6-Sv's Θs-generalization needed.

### (d) Reuse from P6-Cs (`prop_look_complete_cstr.v`)

The ∀-binder kit (β-strip lemmas, Δ→Θ refinement transport,
`a_looksub_lookeq_rename_tvar`), the two ftv transports behind "Pi and 𝒞
cannot contain β", the `*_refine_unify` chain-walkers, and the
`κc ++ κ` syntactic-extension treatment of the paper's `κ ≡ κa`.  The
conclusion shape (𝒞, Ξc, Pa, κc with the `keys`/`Forall`/`ftvar_in_cstrs`
side conditions) carries over verbatim; only `a_lookeq` becomes `a_looksub`
and the mode/`skmod` premises are added.


### (e) P6-Ss status 2026-07-29 (second session) — ForallL prerequisite closed, ForallL row BLOCKED

**Done.**

- `a_looksub_subst_stable_rev` + `a_lookeq` twin + the two
  `a_{looksub,lookeq}_subst_var` helpers, in `prop_looksub.v` §4b (`Qed`,
  axiom-free).  This is the REVERSE of
  `lemma:constraint-collection-stable-substitution`, the lemma the paper's
  ForallL case ends with.  Proof shape: mutual induction on the derivation
  with the SUBSTITUTED subject `remember`ed (stated as
  `Ps = subst Pg βg Pu -> …` so the equation survives), then `destruct Pu`
  per row.  The `Pu = var βg` branch is uniform — the derivation ran wholly
  inside the α-free guess, so `a_looksub_lookeq_absent_nil` empties it and
  LS/LE-Absent rebuilds — and needs the rule's own conclusion rebuilt from
  its premises (`apply <ctor>; eassumption`) to feed the helper.
  ⚠️ Two Coq traps paid for: `inversion HlcPu; subst` CONSUMES the
  `injection` equation if `injection` runs first, so do the `inversion`
  FIRST and then `injection … ; subst`; and `guarded_pskl` covers only
  `unit`/`var_f`/`arrow`, which is what kills the `all_syn`/`hole`/`tophole`
  branches of LS-Check and LE-UnivGhostR.
- The SCOPE premise `ftv R' ⊆ add α (dom Θ0)` is relaxed to
  `add α (dom Θ0 ∪ dom Θ)` and the dual κc-freshness conclusion
  strengthened to match — in BOTH `prop_look_complete_cstr.v` (P6-Cs,
  re-`Qed`ed unchanged otherwise) and `prop_look_complete_sub_cstr.v`.
  Five textual sites in P6-Cs, six in P6-Ss.  Needed because ForallL's IH
  subject `open R0 ψ_b` is Θ-scoped, never Θ0-scoped.
- The duplicate `a_looksub_lookeq_absent` in `prop_look_complete_sub_cstr.v`
  is deleted; `prop_looksub.v`'s `a_looksub_lookeq_absent_nil` is the one.

**ForallL repair DECIDED (see docs/PAPER-GAPS.md, last entry — reclassified
as a PROOF-STEP gap; evidence `frost/algo/cex/cex_p6ss_inc_compat.v`).**
The paper's ForallL IH instance needs `θψ_b = ψ_b`, and NO side condition
on θ rescues that step: Barendregt disjointness is unsatisfiable at ι
(`id_inc_dom_overlap`); syntactic survivor-compat excludes the legitimate
definition-substituting θ, which is inc-equivalent to ι
(`def_subst_theta_is_legit`); and the strongest defensible invariant — the
SEMANTIC `α̂ ∈ dom Θ ⟹ Θ ⊢ θα̂ ≡ᵗ α̂`, which also kills the junk θ moving
an UNDEFINED survivor (`inc_moves_survivor`) — still leaves `θψ_b ≠ ψ_b`
on that legitimate θ.  So: NO premise.  The repair is the ρ-GENERALIZED
INDUCTION, statement UNCHANGED — an aux lemma whose motive carries an
accumulated rigid substitution ρ (each ForallL opens with a FRESH RIGID β,
guess absorbed as `ρ ∘ [ψ_b/β]`; subject `ρ((κR'')[ψa/α])`; β ∉ dom κ ∪
dom Θ0 and κ's images β-free, so the κ/ψ commutation never arises), with
the theorem as the ρ = identity instance.  The looksub side stays on
var-opened subjects (LS-ForallL rebuilds via its cofinite family +
`a_looksub_lookeq_rename_tvar`; `a_looksub_subst_stable_rev` is NOT needed
on this route), and the `P = α` leaf calls P6-Sv at the ACCUMULATED ρ —
the general-ρ interface it was built with.  Cost: the aux lemma carries
P6-Sv's ρ premise kit (`uskl_rho`, `rho_fresh` via the binds-monotone
Θs-generalization, `flex_apart_walk`/`flex_shield` at Δρ — `sub_shield`
generalizes to carry Δρ), and the eight closed rows re-dispatch under the
generalized motive (mechanical).  The ε-tag bookkeeping is expected to
follow P6-Sv's Ψρ treatment (guesses' tags accumulate in Ψρ; `Ψρ ∩ Ψ' = ∅`
from the rule's freshness premises); verify when executing.

**ρ-generalization: KIT AUDIT (2026-07-29) — nothing is missing.**  Checked
before starting, because the P6-Cs half is the expensive part:

- The `uskl_rho_*_l_inv` family is COMPLETE — all nine subject shapes
  (`unit`, `var`, `arrow`, `hole`, `holeg`, `tophole`, `topholeg`,
  `all_syn`, `all_etag`), prop_look_complete.v:199-300 — and it inverts on
  the LEFT (the ρ-IMAGE), which is the direction both generalizations need:
  the derivation runs on the image, and the rule fixes the image's shape.
  Each returns exactly three cases: `refl` (image = ideal, Ψρ = ∅),
  `rho_leaf` (the ideal is a Δρ-variable and the image is its guess), and
  the congruence.
- ⚠️ **The `rho_leaf` case is IMPOSSIBLE in the main induction of both
  P6-Cs and P6-Ss** — it needs the IDEAL subject to be a bare variable,
  i.e. `(κR')[ψa/α] = uskl_var_f α0`, which forces `R'` to be a variable;
  and the main induction runs under `P ≠ α` and `α ∈ ftv P`, so `R'` is
  never a variable (that is exactly what `HRnv` records).  So every row
  inverts to just two cases — refl and congruence — and the refl case is
  the CURRENT proof text verbatim.  This is what makes the P6-Cs half
  threading rather than a rewrite.
- P6-Cv (`a_solve_eq_complete_var_gen`, prop_look_complete_var.v:505)
  already takes `uskl_rho NM Θ Δρ Ψρ ψsub ψa`, so P6-Cs's leaf passes the
  real ρ down instead of `urho__refl`; and `uskl_rho_subst`
  (prop_look_complete_sub_var.v:1111) is the ρ-extension `ρ_b = ρ ∘ [ψ_b/β]`
  that Sub-ForallL needs.
- P6-Cs's measure (`size_uskl R' + size_pskl P0`) is on the ρ-FREE ideal
  subject, so it is untouched; and P6-Cs's own ∀ rows open with fresh
  VARIABLES, so ρ never grows inside P6-Cs.
- ⚠️ **One thing WAS missing, and is now built** (2026-07-29, `Qed`,
  prop_look_complete.v, right before `uskl_rho_weaken`): the MIRROR family
  `uskl_rho_*_r_inv`.  P6-Cs dispatches on `R'` — the IDEAL subject — not on
  the derivation, so at each row the TARGET's shape is what is known and the
  ρ-IMAGE's has to be read off; `_l_inv` reads the other way.  The mirror
  direction is strictly simpler: for every NON-VARIABLE target only
  `urho__refl` and the matching congruence apply (`urho__leaf` demands a
  variable target), and the two COLLAPSE, because `urho__refl` carries
  `lc_uskl` so its components are themselves reflexive ρ-images at `Ψρ = ∅`.
  So `unit` / `hole` / `holeg` return an equation, `arrow` / `tophole` /
  `topholeg` / `all_syn` / `all_etag` return a SINGLE congruence with no
  disjunct to dispatch, and only `var` keeps the leaf disjunct — which is
  exactly right, since the variable target is the only place ρ does
  anything.

**P6-Cs ρ-generalization — EXECUTABLE RECIPE (derived 2026-07-29; the
structure was checked against the proof, not guessed).**

Three facts make this much smaller than feared:

1. **P6-Cs calls P6-Cv exactly ONCE** — at the `P = α` special case
   (prop_look_complete_cstr.v:1741), before the induction.  Every other row
   recurses into P6-Cs itself.
2. **ψa NEVER moves in P6-Cs** (it is the fixed guess for α; the Arrow row
   passes `ψa` unchanged to both recursive calls).  Only `P0` descends —
   arrow components, `open P0'`, `∀◇`-strip.
3. **Δρ is CONSTANT in P6-Cs.**  Consistency has no ForallL, so nothing ever
   extends ρ inside it; ρ only ARRIVES from a Sub-ForallL above.

⇒ The only new *structural* premise is `flex_apart_walk Θ0 Δρ P0 ψa` (P6-Cv
wants plain `flex_apart`; the walk is closed under exactly the P0-only steps
P6-Cs makes — `fastep_arrow_l/_r`, `fastep_all_l`, `fastep_tophole_l` — via
`flex_apart_walk_step`, read off at the leaf by `flex_apart_walk_here`, and
carried across the ∀ rows' context growth by `flex_apart_walk_weaken_tvar`).
No `flex_shield`: that is P6-Sv's premise, not P6-Cv's.

STATEMENT DELTA (mirrors what P6-Cv already takes):
```
  + params Δρ Ψρ Rsub
  + uskl_rho NM Θ Δρ Ψρ Rsub (subst_uskl_in_uskl ψa α (msubst_uskl_syn κ R'))
  ~ Ψsub ⨟ Θ ⊢ₛᵃ Rsub ∼ Q                         (was: on the ideal)
  ~ Θ ⨟ empty ⊢ₚₛᵃ (uskl_to_pskl Rsub)             (was: on the ideal)
  + Ψρ ∩ Ψ' [=] empty
  + rho_fresh Δρ Θ κ
  + Δρ [<=] Δ
  + (forall α0, α0 `in` Δρ -> α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi))
  + flex_apart_walk Θ0 Δρ P0 ψa
  ~ Ψsub [<=] ftag_in_uskl R' `union` Ψρ `union` Ψa
```

ROWS.  The induction dispatches on `R'`, so use the `_r_inv` family (built
2026-07-29).  Only FIVE rows are live and need an inversion — `arrow`,
`all_syn`, `all_etag`, `tophole`, `topholeg`; `unit` / `var_b` / `hole` /
`holeg` are already dead by `α ∈ ∅`, and `var_f` by the special cases.  Each
inversion returns a SINGLE congruence (no disjunct — see the audit above),
so the row's existing text survives with `Rsub`'s components in place of the
ideal's and the sub-ρ threaded into the recursive call.

The `P = α` leaf: STOP rewriting the subject to `ψa` (lines 1730-1737) and
pass `Rsub` + `Hrho` straight through as P6-Cv's `ψsub` — the `urho__refl` /
`fa_clean` / `Δρ := empty` arguments at 1744-1752 become the real ρ premises.
`ftag_in_uskl R' = ∅` there, so `Ψsub ⊆ Ψρ ∪ Ψa` matches P6-Cv verbatim.

TAG ALGEBRA is the one place to go slowly: rows currently read
`Ψ1 ⊆ ftag <ideal component>` off `ad_pat_consis_ftag_sub`, which now yields
`Ψ1 ⊆ ftag <Rsub component>`; convert with `uskl_rho_ftag_sub`
(`ftag Rsub ⊆ Ψρ ∪ ftag ideal`), which is why `Ψρ` joins the `Ψsub` bound.

⚠️ **AMENDMENT (2026-07-29, found by executing the statement change): the
recipe above is INCOMPLETE — P6-Cs also needs the Θs GENERALIZATION, and its
`ftvar_in_cstrs` conclusion has to be relaxed.**  What breaks:

- The `P = α` leaf establishes the ψa-relative conclusion
  `ftv 𝒞 ⊆ ftv ψa ∪ dom Ξc ∪ dom κ ∪ def_ftv Θ` through
  `ad_pat_consis_target_ftv Hconsis`, which bounds `ftv Q` by the
  CONSISTENCY SUBJECT.  Under ρ that subject is `Rsub`, not ψa, so the leaf
  now yields `ftv 𝒞 ⊆ ftv Rsub ∪ …` and `uskl_rho_ftv_subject_bound` only
  gets from there to `ftv ψa ∪ dom Θ`.
- `dom Θ` is FATAL as stated: P6-Cs's ∀ rows run the IH at `Θ,β` and must
  then strip β from 𝒞 (`HβC`, prop_look_complete_cstr.v:2395), and
  `β ∈ dom (Θ,β)`.  So the relaxed conclusion must name the ρ-images' OWN
  scope, not the current context.
- FIX: ρ's images are fixed when ρ is built — by a Sub-ForallL OUTSIDE
  P6-Cs — and P6-Cs never extends ρ.  So carry the ρ premise at a FIXED
  context `Θs` with a binds-monotonicity `forall x b, binds x b Θs -> binds
  x b Θ` (exactly P6-Sv's Θs device, prop_look_complete_sub_var.v:1756), and
  relax the conclusion to
  `ftv 𝒞 ⊆ ftv ψa ∪ dom Θs ∪ dom Ξc ∪ dom κ ∪ def_ftv Θ`.
  Then `uskl_rho_ftv_subject_bound` on the (unweakened) sub-ρ gives
  `dom Θs` uniformly at every depth, the ∀ rows pick β fresh for `dom Θs`
  (free: `Θs ⊆ Θ` by monotonicity and β is already fresh for `dom Θ`), and
  `HβC` survives.  P6-Cv is called at the current Θ, so weaken a COPY of the
  ρ premise there via `uskl_rho_weaken`.
- NB the second ∀ row (line 2602) does NOT use the ψa-relative bound at all
  — it re-derives `β ∉ ftv 𝒞` from the STRUCTURAL `a_looksub_lookeq_ftv`
  plus `ftv P0 ⊆ dom Θ0` — so only the rows whose TARGET gains β depend on
  the relaxed conclusion.

DONE towards this (2026-07-29, `make coq` green, committed):
`fa_step` / `fa_walk` / `flex_apart_walk` + its three lemmas, and
`uskl_rho_is_tskl`, MOVED from prop_look_complete_sub_var.v into
prop_look_complete.v — P6-Cs needs all of them and was UPSTREAM of the file
they lived in.  That circularity would have blocked the statement change
outright; it is now cleared.

⚠️ **SECOND AMENDMENT (2026-07-29, from a second execution attempt — the
statement, the leaf and the Absent case are now VERIFIED to work; the
flexible-P0 row is where it stops).**

VERIFIED by compiling: the statement delta above type-checks as written
(with `Θs` added), the `P = α` leaf goes through — rewrite the ideal side of
`Hrho` instead of `Hconsis`, weaken a COPY out of Θs for P6-Cv
(`uskl_rho_weaken`), and close the ftv-𝒞 conjunct with
`uskl_rho_is_tskl` + `uskl_rho_ftv_subject_bound` — and the `α ∉ ftv P`
Absent case goes through with `uskl_rho_ftag_sub` replacing the direct
`ad_pat_consis_ftag_sub` bound (which is what makes Ψρ join the Ψsub
premise).  The Arrow row's ρ-inversion (`uskl_rho_arrow_r_inv`, then
`subst Rsub`) also works, and `Hcons0` simply restates on `uskl_arrow Ra' Rb'`.

WHERE IT STOPS — the **flexible-P0 row** (`P0 = var β0`,
prop_look_complete_cstr.v:~1948).  It applies
`ad_pat_consis_subst_psia_mono` to a subject of the shape
`subst_uskl_in_uskl ψa α X`, concluding that ψa is a MONO PAINT.  Under ρ
the subject is `Rsub`, which is not syntactically of that shape.  It IS, up
to a commutation: α ∉ dom Θs (α ∉ dom Θ and Θs ⊆ Θ) so α ∉ Δρ, hence

    Rsub = ρ(subst ψa α (κR'))  =  subst (ρψa) α (ρ(κR')).

So the row needs (a) a COMMUTATION lemma putting `Rsub` in that form, and
(b) a small "reflect the mono paint back through ρ" step: the lemma then
gives `ρψa` a mono paint, and since ρ replaces rigid VARIABLES by
tags-sorted images, ψa is a mono paint too (a variable is itself a mono
paint, so the ρ-leaf positions are unproblematic).  Neither is deep, but
both are new lemmas — budget them before restarting the row.

A WIP diff of everything verified above (statement + leaf + Absent + Arrow
inversion) was produced and discarded with the revert; it is ~60 lines and
re-derivable from this recipe in minutes.

✅ **DONE 2026-07-29 (third session) — P6-Cs IS ρ-GENERALIZED AND `Qed`.**
`a_lookeq_solve_complete` is axiom-free, `make coq` is green, and the ρ =
identity instance is machine-checked to still FIRE (the non-vacuity witness
`p6cs_fires_when_the_subject_is_wf` in `cex/cex_p6cs_subject_wf.v`).  What the
recipe above got right, and the four places it did not:

1. ⚠️ **The COMMUTATION is FALSE, and no repair of it is needed.**  `uskl_rho`
   is a RELATION, not a substitution: `urho__leaf` may send two occurrences of
   the SAME Δρ-variable to DIFFERENT images, so `ρ((κR)[ψa/α]) =
   (ρψa)[ρ(κR)/α]` fails already at `R = α→α`, `ψa = β ∈ Δρ`.  The
   "mono-paint reflection" step is likewise unnecessary.  What replaces both:
   at a FLEXIBLE P0 the only `flex_apart` constructor that can hold is
   `fa_clean` (`fa_var_rigid` wants that same variable RIGID; `fa_topholeg_t`
   does not move free variables), so the guess is Δρ-CLEAN there and
   `uskl_rho_clean_eq` collapses ρ on it.  Landed lemmas:
   `flex_apart_flex_var_clean`, `psia_rho_leaf_step`,
   `psia_rho_leaf_impossible`, `ad_pat_consis_rho_subst_psia_mono`.  The last
   inducts on the CONSISTENCY (not on ρ), so `bskl_monoish Q` kills every
   binder case and no cofinite bookkeeping arises; each live row inverts ρ by
   the SUBJECT shape, delegates `urho__refl` to the ρ-free lemma verbatim, and
   threads the sub-ρ into the recursive call.
2. **Two premises beyond the recipe**, both forced by the Arrow row's RIGHT
   recursion (its `Pi` becomes the LEFT branch's `Pa1` under `κc1 ++ κ`):
   `Δρ ∩ dom Θ0 = ∅` and a new OUTPUT conjunct
   `Forall (fun p => ftv (snd p) ∩ Δρ = ∅) κc`.  Together they re-derive the
   shielded-ftv condition at `Pa1`: `Ξc1` is fresh for Θ ⊇ Δρ so `Pa1` avoids
   Δρ, and κ's images avoid it by `rho_fresh` while κc1's do by the new
   `Forall` (whose only witness source is the flexible-P0 row, where the guess
   is Δρ-clean).
3. ⚠️ **`flex_apart_walk` did NOT cover P6-Cs's Arrow row.**  `fastep_arrow_l`
   / `_r` descend P0 and ψa TOGETHER, but P6-Cs keeps ψa FIXED (it is the
   single guess for α and never splits).  `fa_step` therefore gains
   `fastep_p0_arrow_l` / `_r`; `fastep_all_l` and `fastep_tophole_l` already
   had the right shape.  Adding constructors only STRENGTHENS the premise, so
   P6-Sv (which merely threads the walk via `_here` / `_step`) is unaffected.
   Also added: `flex_apart_walk_weaken` (the tvar-only version does not cover
   the Arrow row's `Ξc1 ++ Θ0` growth).
4. **The ∀ and ∀◇ rows got SIMPLER, not harder.**  Consistency and subject-wf
   are now stated on the IMAGE, which opens directly, so `p6cs_subject_open`
   survives only in the ρ premise — the one hypothesis still ideal-side.
5. The Θs generalization and the relaxed ftv-𝒞 bound (first amendment) are
   confirmed exactly as written; `HβC` survives, and the ∀ rows get
   `β ∉ dom Θs` free from `dom Θs ⊆ dom Θ` (a two-line consequence of the
   binds-monotone premise, hoisted once after `intros`).
6. **The paper's statement is back as a corollary.**  The generalized theorem
   is `a_lookeq_solve_complete_gen`; `a_lookeq_solve_complete` is its
   ρ = identity instance and is LITERALLY the pre-generalization statement,
   with no residue.  Making it premise-free is why P6-Cs takes the P0-ONLY
   walk `flex_apart_deep` (`p0_step` / `p0_walk`, prop_look_complete.v) instead
   of `flex_apart_walk`: P6-Cs descends P0 alone at a CONSTANT Δρ, so at
   Δρ = ∅ every reachable state is `fa_clean`, whereas `flex_apart_walk`'s
   `fastep_all_r` can grow Δρ and would leave a real premise behind.  P6-Ss
   threads the full walk and converts via `flex_apart_walk_p0` — which is
   what `fastep_p0_arrow_l/_r` exist for.  Use the corollary unless you are
   threading a ρ down from a Sub-ForallL.

⚠️ NAMING: the ρ-image subject is `Rsub`, not `Ssub` — a `uskl` is `R` in
this corpus (`S` is not a metavariable here at all).  NB there is
pre-existing drift to clean up separately: `prop_consis_precise.v` uses
`Ssub` as a local `remember` name in ~10 proof bodies.

⚠️ This is ONE atomic change — the file does not compile part-way through, so
budget it as a single sitting.

**Order for the next session** (Arrow and ForallR do NOT depend on the
decision above, so start there):

1. Arrow — the assembly is a near-copy of P6-Cs's Arrow row
   (`prop_look_complete_cstr.v:2007-2160`): LEFT premise to
   `a_lookeq_solve_complete`, RIGHT to the derivation IH with
   `sss_arrow_r` + `sub_shield_step`, then the same `a_solve_cstr_app` /
   `a_wf_pskl_swap_app` / `a_inc_flex_prefix_split` kit.  New relative to
   P6-Cs: `skmod` forcing `P0 = P01→P02`, and the `Ψa1`/`Ψa2` split.
2. ForallR — the `β ∉ ftv 𝒞` obligation is a MECH-ENCODING artefact, not a
   paper gap (WT, 2026-07-29: `look` is scoping-agnostic; the extract use
   site's separate `Θ0,Ξ ⊢ P1` premise does the scope check).  DECIDED:
   KEEP the cofinite rule — completeness of a narrower algorithm is a
   stronger theorem.  ⚠️ but do NOT justify it by "the wf check catches a
   β-mentioning 𝒞 anyway": `a_solve_sub__var` is `α̂ ≼[m] Q ⤳ α̂` and
   DISCARDS the target, so a β-mentioning 𝒞 can solve to a β-free `P1` that
   passes `Θ0,Ξ ⊢ P1`; the encodings are not literally equivalent.  What
   the row needs is to re-acquire the ψa-relative bound
   `ftv 𝒞 ⊆ ftv ψa ∪ dom Ξc ∪ dom κ ∪ def_ftv Θ` that P6-Cs carries and this
   statement dropped — available once the ρ-generalization lands, since
   under ρ the lookup side never sees a guess.  **ForallL and ForallR are
   fixed by the SAME change**, so do (3) first and this row falls out.
3. ForallL — the ρ-generalized aux lemma above.  ⚠️ SCOPE MEASURED
   (2026-07-29): the Check row hands its whole subject to P6-Cs and a
   ForallL can sit above a Check, so **P6-Cs must be ρ-generalized too**.
   Threading, not new theory — P6-Cv (`a_solve_eq_complete_var_gen`)
   already takes `uskl_rho`, the `uskl_rho_*_l_inv` kit exists, P6-Cs's
   measure is on the ρ-free ideal subject so it is unaffected, its ∀ rows
   open with fresh VARIABLES so ρ never grows inside it, and its leaf
   passes the real ρ down instead of `urho__refl`.  ALREADY LANDED for
   this step (file compiles, statement unmoved): `sub_shield` carries Δρ
   (instantiated at `empty` for now) with `sub_shield_add_fresh` /
   `_weaken_tvar`, and `ad_partial_precise_delta_shrink_fresh` is `Qed`.
   P6-Sv's ForallL row (prop_look_complete_sub_var.v:2308) is the
   line-by-line template, simplified: P6-Ss's ∀ comes from the SUBJECT, so
   ψa/P0/Pi/Ψi/Ψa do not move and only Θ0/Θ/Δ/Δρ grow by β.
   ✅ **The P6-Cs half is DONE (2026-07-29) — see the DONE block above.**
   What P6-Ss must now supply at its Check/Arrow calls, on top of what
   `sub_shield_here` already gives (`flex_apart_walk`): the ρ premise at a
   FIXED `Θs` with binds-monotonicity into Θ, `Ψρ ∩ Ψ' = ∅`,
   `rho_fresh Δρ Θ κ`, `Δρ ⊆ Δ`, `Δρ ∩ dom Θ0 = ∅`, and the Pi-shielded-ftv
   condition; and it gains one output conjunct (`κc`'s images avoid Δρ).
   ⚠️ `sub_shield` will have to carry the P0-ONLY arrow steps that P6-Cs
   added to `fa_step` (`fastep_p0_arrow_l/_r`) — the Check row's call is
   already discharged by `sub_shield_here`, but only because the walk is
   threaded rather than constructed.  Constructing one from scratch at
   Δρ = ∅ is NOT free (a `fa_walk` can grow Δρ via `fastep_all_r`); see
   `cex_flex_apart_walk_unit` in `cex/cex_p6cs_subject_wf.v` for the shape
   of the induction a from-scratch construction needs.

### (f) P6-Ss status 2026-07-29 (fourth session) — Arrow CLOSED, leaf ρ-ready, the rest SPLIT IN TWO

`make coq` green; admits = P6-Ss's THREE (ForallR, ForallL×2).

**Closed.**

- **Arrow.**  LEFT premise (a consistency judgment) → the ρ-free P6-Cs
  corollary; RIGHT → the derivation IH; LS-Arrow pairs the prefixes and
  `a_solve_cstr_app` composes the solves — legal because `C1`, a LOOKEQ's
  output, holds no subtyping constraint.  The assembly is line-for-line
  P6-Cs's Arrow assembly minus its ftv-𝒞 conjunct.  Three prerequisites it
  forced, all landed:
  1. the induction now GENERALIZES `Θ0` and `κ` — the right branch runs at
     `Ξc1 ++ Θ0` / `κc1 ++ κ` because the solves are SEQUENTIAL.  All eight
     previously closed rows survived untouched.
  2. `sub_shield` transports across a FLEXIBLE prefix.  `flex_shield` is NOT
     context-monotone: `fsh_flexfree` says no variable of P0 is a
     Θ0-FLEXIBLE, and a flex prefix can make one so, so the transport needs
     `ftv P0 ∩ dom Ξ = ∅`.  The call site has that, but `sub_shield`
     quantifies over every `ss_walk`-reachable `P0'` and `sss_all` opened
     with an ARBITRARY γ — so `ss_step` / `ss_walk` now carry an AVOID SET
     (`sss_all` needs `γ ∉ A`), instantiated at `dom Θ0`.  New:
     `ss_walk_mono`, `ss_walk_ftv`, `flex_shield_weaken_flex_prefix`,
     `sub_shield_weaken_flex_prefix`.
  3. `a_looksub_all_flex_mono` — looksub collects flexibles only through
     LS-Check and LS-Arrow's left premise, both of which are lookeq.
- **The leaf is ρ-generalized.**  `a_looksub_solve_complete_leaf` carries the
  ρ pack, `sub_shield` at Δρ, and its `P = α` case hands P6-Sv the REAL ρ.
  `a_looksub_solve_complete_leaf_id` is the ρ = identity wrapper, so the
  theorem's call sites are untouched for now.
  NB P6-Sv's ρ interface was never idle — its OWN Sub-ForallL row grows ρ
  (`uskl_rho_subst`, then the IH at `add β Δρ`), and `fsh_all_r` bakes the
  growth into `flex_shield`.  Only the EXTERNAL entry point was
  identity-instantiated; the leaf simply stops passing the identity.

**Split the rest in two.**  ForallL needs only the ρ params; ForallR needs
only the ψa-relative ftv-𝒞 conclusion.  So:

- **Phase A** — ρ params + threading ⇒ ForallL×2.  Needs NO `Θs`: P6-Sv's
  leaf call wants `uskl_rho` at plain `Θ`.  Delta mirrors P6-Cs's:
  `+ Δρ Ψρ Rsub`, `uskl_rho … Rsub ((κR')[ψa/α])`, `Ψρ ∩ Ψ' = ∅`,
  `rho_fresh`, `Δρ ⊆ Δ`, `Δρ ∩ dom Θ0 = ∅`, the Pi-shielded-ftv condition;
  `sub_shield` at Δρ; subtyping + wf premises on `Rsub`; the `Ψsub` bound
  gains Ψρ; the conclusion gains `Forall (images ⊥ Δρ)`.
- **Phase B** — the ψa-relative ftv-𝒞 conclusion ⇒ ForallR.  This is the
  part that needs `Θs` (same reason as P6-Cs: the ∀ rows strip β from 𝒞).

**Phase A is NOT incremental — budget a fresh sitting.**  P6-Ss `remember`s
its subject as `Sub0` with `HeqSub : Sub0 = (κR')[ψa/α]`, and every row reads
R''s shape off that equation by `destruct R'` + `discriminate`.  Under ρ the
derivation runs on the VARIABLE `Rsub`, which `induction` abstracts directly
— so the `remember` / `HeqSub` device is DROPPED and each row inverts `Hrho`
with the `uskl_rho_*_r_inv` family instead, exactly as P6-Cs does.  That
rewrites all nine closed rows' shape-derivations at once; there is no
compiling half-way state, and the `_id` leaf wrapper dies with it (the rows
move to the general leaf).

### (g) P6-Ss Phase A DONE (2026-07-29, fifth session) — ρ-generalized, BOTH ForallL rows CLOSED

`make coq` green; the mechanization's ONLY admit is P6-Ss's **Sub-ForallR**.

⚠️ **The plan in (f) had a hole, and it was in P6-Cs, not P6-Ss.**  P6-Cs's ρ
premise `forall α0 ∈ Δρ, α0 ∉ dom Θ0` makes the ρ-generalization VACUOUS —
machine-checked, `frost/algo/cex/cex_p6cs_rho_delta_vacuous.v`.  Beside
`κ ∷ Θ0 ⊑ Θ` and `rho_fresh Δρ Θ κ` it forces `Δρ = ∅`, because **an increase
never invents a rigid**: `a_suffix` admits only flexible entries, so every rigid
of the target is a rigid of the source (`a_inc_binds_tvar_rev`, the converse of
`a_inc_binds_tvar`).  Hence a fresh ρ-binder MUST enter Θ0 and Θ together
(`a_inc_cons_tvar`), and the premise (f) told P6-Ss to adopt would have made
P6-Ss vacuous too.  **Repair, landed:** the ftv-level premise
`forall α0 ∈ Δρ, α0 ∉ ftv P0 ∪ ftv Pi`, which is all the old one was ever used
for (via `a_wf_pskl_ftv_dom`) and is preserved by every descent
(`rho_ftv_apart_mono`; the Arrow row's RIGHT recursion earns it for `Pi := Pa1`
through `a_solve_cstr_ftv` + `a_looksub_lookeq_ftv`).  Both P6-Cs and P6-Ss now
take it; keep this in mind for any future ρ-style generalization over `a_inc`.

**Θs — TWO different devices with the same name.**  P6-Ss Phase A does need one,
just not P6-Cs's: the DERIVATION's context (P6-Sv's device), because Sub-ForallL
runs the recursion at `Θ,β` while the derivation's context is an INDEX.  Rule
premises are weakened on the spot right after `induction`, exactly as P6-Sv does
(the `all: match goal` block).  ⚠️ that block does NOT catch the ForallL rule's
`Θ ⨟ empty ⊢ₚₛᵃ ⌊ψ⌋ˢ` premise (reason not chased) — weaken it by hand.
P6-Cs's `Θs` (the ρ premise at a FIXED context, for the ftv-𝒞 bound) is still
NOT taken here; that is Phase B.

**Sub-ForallL, as executed.**  Fresh rigid β; guess absorbed by `uskl_rho_subst`;
recursion at `Θ0,β / Θ,β / add β Δ / add β Δρ`; β stripped from every output by
P6-Cs's ∀-binder kit (`a_solve_cstr_strip_tvar_mid`, `a_wf_pskl_strip_tvar`,
`a_inc_strip_tvar_mid`, `ad_partial_precise_strip_tvar_mid`, then
`ad_partial_precise_delta_shrink_fresh` for the Δ side); LS-ForallL's cofinite
family from the single β-instance by `a_looksub_lookeq_rename_tvar`, legal
because the TARGET P0 does not move so `a_looksub_ftv` keeps β out of 𝒞.

**The tag bookkeeping (f) left to "verify when executing" — it works, with one
observation.**  `ad_pat_sub_g` records the paper's GLOBAL freshness of an
instantiation's tags as only two conjuncts (fresh from the tag index and from
the SUBJECT's syntactic tags).  Sub-ForallL needs a third, freshness from ψa's
tags Ψ', to keep `Ψρ ∩ Ψ' = ∅`.  It is not a new side condition: the induction
runs under `α ∈ ftv R'`, so ψa sits INSIDE the ideal `(κR')[ψa/α]`, and
`uskl_rho` only ADDS tags going to the image (`uskl_rho_ftag_target_sub`) —
hence `Ψ' ⊆ ftag Rsub`, where the rule's own subject-freshness excludes them.
New (both `Qed`): `ftag_in_uskl_subst_lower`, `msubst_uskl_syn_ftv_keep`.
The IH's `Ψsub`-bound obligation also needs the binder's own ε ruled out of Ψ;
`Hdisj` (`ftag R' ∩ Ψ' = ∅`) does it, since the only route by which ε could
have to land in Ψ' is closed.

**Traps paid for this session** (both are the evar-fsetdec one):
`eapply ad_partial_precise_delta_cong; [ | fsetdec ]` HANGS — the Δ is an evar
when the `[=]` goal runs; pin it with a named `assert` first.  And
`rewrite <set equality>` in a judgment's Δ position fails outright (no `Proper`
instance) — use the congruence lemma, not `rewrite`.

**Phase B (Sub-ForallR), unchanged in shape:** re-acquire
`ftv 𝒞 ⊆ ftv ψa ∪ dom Θs ∪ dom Ξc ∪ dom κ ∪ def_ftv Θ` as an output conjunct,
with P6-Cs's fixed-`Θs` ρ premise; the ρ-generalization landed here is exactly
what makes it available (under ρ the lookup side never sees a guess).

**Phase B — one prerequisite MEASURED (2026-07-29, after (g)).**  The ftv-𝒞
conclusion's leaf case needs the SUB-SIDE analogue of
`ad_pat_consis_target_ftv` (prop_look_complete_cstr.v:1481,
`ftv Q ⊆ ftv ψ ∪ def_ftv Θ` from a consistency derivation) — call it
`ad_pat_sub_g_target_ftv`.  It does NOT exist (only the TAG version
`ad_pat_sub_g_ftag_sub` does), and the `P = α` leaf cannot establish
`ftv 𝒞 = ftv P0 ⊆ ftv ψa ∪ dom Θρ ∪ …` without it: the chain is
P0 → κP0 → Q (refinement) → subject (this lemma) → ψa ∪ dom Θρ
(`uskl_rho_ftv_subject_bound`).  Budget it before starting Phase B.  NB the ρ
premise's fixed context needs a THIRD context parameter here (`Θρ`), since
`Θs` is already taken by the derivation's.

### (h) P6-Ss Phase B — the planned route is REFUTED; the route that works (2026-07-29, sixth session)

`make coq` green; the mechanization's ONLY admit is still P6-Ss's **Sub-ForallR**.

⚠️ **Phase B's prerequisite is FALSE, and `is_tskl` does not repair it.**
Machine-checked: `frost/algo/cex/cex_p6ss_sub_target_ftv.v`
(`p6ss_sub_target_ftv_is_false`, axiom-free, plus a non-vacuity witness).
The sub-side analogue of `ad_pat_consis_target_ftv`,

    ad_pat_sub_g n NM M Ψ Θ R Q -> a_wf_aenv Θ -> is_tskl R ->
      ftv Q ⊆ ftv R ∪ def_ftv Θ

fails at **`ad_pat_sub_g__forall_l_tagged`**, not only at the `__ghost` row
(g) anticipated.  `is_tskl` DOES exclude `__ghost` (it admits the dotted ◈
`uskl_holeg` but not the plain ◇ `uskl_hole`), `__ghostg`, `__univ_ghost_l/lg`
and `__forall_l_untagged` (whose subject is the tag-elided `uskl_all_syn`) —
but `uskl_all_etag` IS `is_tskl`, and ForallL instantiates it with a guess
bounded only by `Θ ⨟ empty ⊢ₚₛᵃ ⌊ψ⌋ˢ`, i.e. by **`dom Θ`, not `def_ftv Θ`**.
Witness: Θ = β, subject `∀^ε α. α`, guess β, leaf `β ∼ β` ⇒ target `β`.

`dom Θ` is therefore the strongest sound bound — and it is exactly the wrong
one, because `ad_pat_sub_g__forall_r` runs its premise at `Θ,β`, so the bound
readmits the very binder Sub-ForallR must strip.  There is no shape premise to
add: ForallL is the essential subtyping rule, and consistency escapes the
problem only because it HAS no ForallL.

**The theorem is NOT refuted — only the route.**  In every configuration the
lemma fails on, the algorithm still collects a β-free 𝒞, by taking
LS-ForallL / LS-UnivGhostL *before* LS-ForallR: LS-Var then fires at the
UNDESCENDED `∀β.P0`.  (E.g. `∀γ.α ≼[α,tc] ∀β.β ⤳ · ⨾ [α ≼ ∀β.β]`, where
descending first gives the β-mentioning `[α ≼ β]`.)

**THE MODE RESTRICTION IS WHAT MAKES THIS DECIDABLE-BY-CASES.**
`ad_pat_sub_g__forall_r` forces `NM = a_sub_mode_ty` and `M = mode_tc`, and NM
is invariant along a derivation.  At `(ty, tc)` the ONLY applicable rows are

    __check      (leaf; its subtree is pure CONSISTENCY — no guesses)
    __forall_r   (descends the target, subject fixed)
    __forall_l_* (descends the subject; the only guess source)

— `__infer` needs `mode_ti`; `__arrow` and `__flex_mono` need `mode_fn _`;
`__ghost`, `__ghostg`, `__univ_ghost_l/lg/r` need `a_sub_mode_sk`.  Two
consequences:

1. On the lookup side the mirror rows are LS-Check (⇒ P6-Cs), LS-ForallR,
   LS-ForallL and LS-UnivGhostL.  So under a Sub-ForallR the **P6-Ss leaf
   (`P = α`) is reachable only when P is a ∀/⊤◇-STACK over α** — every other
   α-leaf sits under LS-Check, i.e. inside P6-Cs, whose ftv-𝒞 bound is
   already ψa-relative.
2. In that stack case every ∀-body is CONSTANT, so every ForallL guess is
   discarded and the derivation permutes: `__forall_l` can be pulled above
   `__forall_r`.  (∀L/∀R do NOT permute in general — that is precisely why
   the general route dies — but they do when the guess is dropped.)

**The Phase B statement that works.**  Carry the ftv-𝒞 conclusion as a
MODE-GUARDED DISJUNCTION:

    M = mode_tc ->
      ftv 𝒞 ⊆ ftv ψa ∪ dom Ξc ∪ dom κ ∪ def_ftv Θ   \/   α_stack α P

where `α_stack α P` is the inductive "P is α under ∀/⊤◇ binders".  Row by row:

- **Sub-Arrow** — conclusion mode is `mode_fn M ≠ mode_tc`: VACUOUS.  This is
  what kills the obvious objection (Arrow cannot concatenate a left disjunct
  with a right one).
- **Check** — P6-Cs's own ftv-𝒞 output, left disjunct.
- **Sub-ForallL / UnivGhostL/LG** — target unmoved; IH's disjunct passes
  through (a right disjunct lifts: `P''^β` an α-stack ⇒ `∀P''` is one).
- **leaf, LS-Absent** — 𝒞 = nil, left.  **leaf, `P = α`** — right.
- **Sub-ForallR** — left ⇒ `β ∉ ftv 𝒞` (β is fresh for ψa, Ξc, κ, and is a
  rigid so not in `def_ftv Θ`) ⇒ rebuild LS-ForallR from the single instance.
  right ⇒ P is an α-stack: build LS-ForallL*/LS-UnivGhostL* + LS-Var directly
  at the UNDESCENDED P0, and get the leaf's other conjuncts by first
  stripping the constant-body `__forall_l`s off the derivation.
- Infer / UnivGhostR / Ghost / GhostG / FlexMono — 𝒞 = nil or mode ≠ tc.

**One change to P6-Cs is required, and it is small.**  Its ftv-𝒞 conclusion
must DROP the `dom Θs` term — under a Sub-ForallR a nested Sub-ForallL's guess
mentions β, so ρ's images are scoped at `Θs,β` and `dom Θs` readmits β.  The
replacement is an apartness premise

    Δρ ∩ ftv ψa [=] empty

plus a new `uskl_rho_ftv_apart : uskl_rho NM Θ Δρ Ψρ R' R -> ftv R ∩ Δρ [=]
empty -> ftv R' [<=] ftv R` (routine induction; the `urho__leaf` row is
vacuous under the premise, the binder rows pick α fresh for Δρ).  P6-Cs keeps
Δρ CONSTANT and never moves ψa, so the premise is preserved by every descent;
P6-Ss maintains it because ψa is fixed in the main induction and every
Sub-ForallL binder is picked fresh.  Note this makes P6-Cs's `Θs` slot
irrelevant to the ftv bound, so Phase B needs NO third context parameter —
the `Θρ` of (g)'s plan is not needed.

**Build order, with what is DONE.**
1. ✅ `uskl_rho_ftv_apart` (prop_look_complete.v), `Qed`.
2. ✅ P6-Cs takes the apartness premise and its ftv-𝒞 conclusion DROPS
   `dom Θs`; both P6-Cs theorems re-`Qed`, axiom-free.  P6-Ss takes the same
   premise and maintains it at both Sub-ForallL rows (β is already known
   fresh for ψa as `Hβψa`); both `ρ = identity` corollaries discharge it at
   `Δρ = ∅`.
3. ✅ `alpha_stack` + `alpha_stack_subst_var` + `alpha_stack_all_of_one`
   (lifts a SINGLE β-instance to the cofinite `ast_all`, via
   `subst_pskl_in_pskl_intro`) + **`alpha_stack_looksub`**: an α-stack
   collects `nil ⨾ [a_cstr_sub m P0]` at ANY undescended P0.  All `Qed`, in
   the P6-Ss file just above the leaf lemma.
4. ✅ (a) `ad_pat_sub_g_ty_tc_subject` — the mode restriction, machine-checked:
   at `(ty, tc)` the subject is GUARDED or ∀-headed, so a ⊤◇/◇/◈ subject is
   impossible there (stripping those needs `a_sub_mode_sk`).  This is what
   lets the stack branch assume the stack is ∀s alone.
   ❌ (b) `ad_pat_sub_g_strip_const_all` — **NOT NEEDED, dropped.**  It was to
   let the stack branch hand P6-Sv a derivation against the UNDESCENDED target,
   but STRENGTHENING the right disjunct (step 5) makes the IH hand back the
   solve directly, so no derivation surgery is required.  It would also have
   hit the cofinite-existential wall at `__forall_r` (one `n'`/`Ψ'` for
   cofinitely many binders).
5. ✅ The mode-guarded disjunction is threaded through all twelve rows, both
   P6-Ss statements, the corollary and the five inner `REC` restatements.  The
   right disjunct is STRENGTHENED to
   `alpha_stack α P /\ Ξc = nil /\ κc = nil /\ 𝒞 = a_cstr_sub M P0 :: nil`,
   which is what removes 4(b): in the stack case the IH already yields the
   solve, at the descended target.
6. ✅ Sub-ForallR, executed as planned.  The refinement inversion block is
   P6-Sv's verbatim (`skmod{TY}` makes P0 a TYPE, so the inherited-∀ target
   forces P0 = ∀.P0' — every other type shape is guarded, and a guarded
   source refines only to a guarded target).  Then ONE fresh rigid β, the
   usual transports, the IH at Θ,β / Θ0,β, and **the IH's own ftv-𝒞 disjunct
   decides the branch** — no decidability of `alpha_stack` is needed:
   - LEFT: `β ∉ ftv 𝒞` (β fresh for ψa/Ξc/κ, and a rigid so not in
     `def_ftv Θ`); strip β from every output with P6-Cs's ∀-binder kit and
     rebuild with `a_looksub__forall_r` + `a_looksub_lookeq_rename_tvar`.
     Same shape as the Sub-ForallL rows with the renamed side swapped: there
     the SUBJECT moves and the target is fixed, here the reverse.  Δ does not
     grow, so unlike Sub-ForallL there is no `delta_shrink` step.
   - RIGHT: `alpha_stack_looksub` gives the whole `a_looksub` conjunct at the
     UNDESCENDED P0; the IH's one-constraint solve inverts to
     `Θ0,β ⊢ₛ Pi ≼[tc] P0'^β ⤳ Pa`, and
     `a_solve_sub_strengthen_tvar` + `a_solve_sub__forall_r` +
     `a_solve_sub_eq_rename` lift it over the ∀ (P6-Sv's recipe,
     prop_look_complete_sub_var.v:2036).

**P6-Ss IS CLOSED (2026-07-30).**  `a_looksub_solve_complete_gen` and the
paper's premise-free `a_looksub_solve_complete` are both `Qed` and
`Closed under the global context`; `make coq` is green from clean and the
whole mechanization is admit-free again.

**Two traps this row paid for, both worth remembering.**
- `β ∉ ftv Pa` in the RIGHT branch does NOT come from `a_solve_sub_ftv`: the
  target there legitimately mentions β (that is the branch's whole point), so
  that bound is useless.  It comes from PRECISION —
  `ad_partial_precise_src_ftv_avoid` bounds the source by
  `ftv ψa ∪ Δ ∪ def_ftv Θ`, all β-free — then `msubst_pskl_ftv_dom_lower`.
  P6-Sv's ForallR row does exactly this.
- `repeat split` CLOSES `keys nil = keys nil` by itself: `split` on a
  convertible equality is `eq_refl`, since `eq` is single-constructor.  So the
  RIGHT branch's bullet list has no `keys` bullet, while the LEFT branch's
  does (there `keys κc = keys Ξc` is not convertible).  A stray bullet shifts
  the whole list and the error surfaces far away.

**On "𝒞 may mention β, but the later wf check makes it transparent."**
Half true, and worth keeping in view for step 6.  It is NOT a licence to skip
the obligation: `a_looksub__forall_r` is COFINITE in β with one `Ξ ⨾ 𝒞`, so it
is the RULE that blocks, not the extract-site `Θ0,Ξ ⊢ P1` check — and that
check is not a filter either, since `a_solve_sub__var` (`α̂ ≼[m] Q ⤳ α̂`)
DISCARDS the target, so a β-mentioning 𝒞 can solve to a β-free P1 the check
accepts (the 2026-07-29 author resolution recorded at the `admit`).  But the
same fact is a genuine SIMPLIFICATION inside the α-stack branch: there Pi
faces the undescended `∀β.P0`, and whenever Pi is a flexible variable
SS-Var/SS-Flex returns Pi whatever the target is, so the descended and
undescended solves agree.  `a_solve_sub__forall_r` is itself cofinite with a
β-free output P', i.e. the solve side already made this same encoding choice.

**The alternative the mode analysis rules IN but does not recommend:** adopt
the paper-faithful LAX `a_looksub__forall_r` (exists-fresh; the paper's
constraint collection is scoping-agnostic and defers scoping to the extract
site).  Sub-ForallR then becomes trivial and Phase B disappears.  The cost is
that `a_looksub_ftv` (`ftv 𝒞 ⊆ ftv P' ∪ dom Ξ`) becomes FALSE — and BOTH
Sub-ForallL rows use it to strip their binder (prop_look_complete_sub_cstr.v:
1724, 2086) — so it would have to be replaced by an avoid-set threaded through
the theorem's conclusion, and subtyping SOUNDNESS re-checked against a rule
that admits strictly more.  The α-stack route above touches no rule and no
closed soundness proof.

### 7.3 P6-L sizing (measured 2026-07-30, after P6-Ss closed)

**P6-L is NOT a thin wrapper — it is a small half plus a real sub-induction.**
`a_extract` has ONE rule, so the shape is fixed:

    P ≼[α,m] P' ⤳ Ξ ⨾ 𝒞  →  Ξ ⊩ 𝒞 ⨾ □ ⤳ Q  →  a_guess NM Q Ξ' Q'
      →  P ⊳[NM,α,m] P' ⤳ (Ξ ++ Ξ') ↪ Q'

- Premises 1–2: **P6-Ss at `Pi := pskl_hole`, `Ψi := ∅`, `Ψ' := Ψa`** (the
  ρ = identity corollary — nothing threads a ρ in from outside).  Its
  precision premise `Θ ⨟ Δ ⊢ κ□ ⊑ᵖ[∅] ψa` is the precision hole rule.
- Then `ad_partial_precise_complete` (P5b-i, Qed) upgrades `⊑ᵖ[Ψa]` to plain
  `⊑ ⌊ψa⌋ˢ`, exactly as complete-look does at tex:2764.
- **`N = SK`: trivial.**  `a_guess__sk` gives `Ξ' = nil`, `Q' = Q`, so
  `θa := θs` and all four outputs are P6-Ss's verbatim.
- **`N = TY`: the real work.**  The paper's "by induction on the definition
  of `guess^N(P_s)`" is a sub-induction over `a_guess_mono`'s six
  constructors producing FOUR conclusions at once — wf, `a_inc`,
  `a_inc_equiv`, and precision — with `θa` built POSITIONALLY by extending
  `θs` to map each flexible of `Ξ'` to the corresponding type in `⌊ψa⌋ˢ`.
  It also needs the paper's own side observation that no quantifier of
  `⌊ψa⌋ˢ` faces a universal ghost in `P_s` (because all tags are in `Ψa`).

⚠️ **CORRECTION to §7's table: `guess_join_witness` does NOT "provide exactly
the P6-L TY-witness".**  It is CONSISTENCY-driven — its premise is
`Ψ ⨟ Θ ⊢ₛᵃ pskl_to_uskl (msubst κm P) ∼ ptyp_to_bskl_syn A` with `A` a
monotype (prop_consis_complete.v:4624) — whereas P6-L has PRECISION against
`⌊ψa⌋ˢ`, which at TY is a general ghost-free skeleton, not a monotype
painting.  Either a precision-driven analogue must be built, or a bridge
found; `a_guess_mono_consis` (prop_flex.v:352) goes the OTHER way (guess ⇒
consistency).  The five existing `a_guess_mono` lemmas are all structural
support (ftv / flex_binds / decls / consis / head) — there is no witness
lemma among them.

**Estimate: a focused session, maybe two** — much smaller than P6-Ss, but not
an add-on.  P7 opens only after it.

✅ **CLOSED 2026-07-30** — see §7.5.  The estimate held; the sizing above was
accurate except that the ⚠️ on `guess_join_witness` (below) turned out to be the
smaller of the two surprises: the bigger one was the `__flex_r` CHASE.

### 7.4 ⚠️ P6-L IS BLOCKED ON AN ENCODING MISMATCH (found 2026-07-30, before writing any proof)

`a_extract`'s solve premise runs at the WRONG CONTEXT for P6-Ss's output, and
the gap is not a weakening.

    a_extract__solve : P ≼[α,m] P' ⤳ Ξ ⨾ 𝒞  ->  Ξ ⊩ 𝒞 ⨾ □ ⤳ Q  -> …
                                                 ^^^ Ξ ALONE

but P6-Ss delivers `(Ξc ++ Θ0) ⊩ 𝒞 ⨾ Pi ⤳ Pa`.  Going from `Ξc ++ Θ0` down to
`Ξc` DROPS Θ0's flexibles, and that is unsound for the one context-sensitive
rule in the whole solve cluster:

    a_solve_eq__flex_r :  a_flex_tvar Θ α -> a_non_flex Θ P ->
                          Θ ⊢ₑ P ∼ (pskl_var_f α) ⤳ (pskl_var_f α)

`a_flex_tvar Θ α` gets HARDER in the smaller context (while `a_non_flex Θ P`
gets easier), so neither direction is monotone.  Every other rule of
`a_solve_sub` / `a_solve_eq` / `a_solve_cstr` ignores Θ entirely — this one
rule is the whole issue.  Existing lemmas only WEAKEN
(`a_solve_eq_weaken_tvar` adds a rigid; `a_solve_cstr_weaken_mid_flex` inserts
flexibles); there is no strengthening lemma, and there should not be.

**The configuration is reachable.**  `skmod{TY}` at TC makes P0 a TYPE, and a
type may be a FLEXIBLE variable of Θ0 (flexibility is a context property, not
a syntactic one), so \lslab{Var} / \lelab{Var} can emit `eq α̂` with α̂ ∈ Θ0.
The FIRST constraint is safe — `Pi = □` and `a_solve_eq__hole_l` (`□ ∼ Q ⤳ Q`)
has no flex check — but with `𝒞 = [eq Q1, eq α̂]` the second constraint faces a
non-hole subject and needs SE-FlexR, which `Ξc` alone cannot supply.

**This is a MECH-ENCODING artefact, not a paper gap.**  The paper's solve
judgment is CONTEXT-FREE — `\boxed{\solve{\mC}{P}{Q}}`, full-algo-spec.tex:1216
— because there `α̂` is syntactically distinct.  The mech added Θ only to
decide hattedness (def_extra.v:377), and `a_extract` then had no context to
pass but `Ξ`.  So the mech is free to choose; the current choice is just the
narrow one, and it is narrow in a way that breaks completeness rather than
strengthening it.

**✅ FIXED (2026-07-30).**  `a_extract` now carries the context and solves at
`Ξ ++ Θ0`:

    Inductive a_extract : aenv -> a_sub_mode -> atom -> mode -> pskl -> pskl
                          -> aenv -> pskl -> Prop
    a_extract__solve : P ≼[α,m] P' ⤳ Ξ ⨾ 𝒞 -> (Ξ ++ Θ0) ⊩ 𝒞 ⨾ □ ⤳ Q
                       -> a_guess NM Q Ξ' Q' -> Θ0 ⊢ P ⊳[NM,α,m] P' ⤳ (Ξ++Ξ') ↪ Q'

with notation `Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q`.  Both use sites
(`a_sub__forall_l`, and the two decorated `a_subtag__forall_l_*` rows) already
had Θ0 in scope.

**THE PAPER SETTLES IT — this is a faithfulness FIX, not a design change.**
`\soleqlab{FlexR}` (full-algo-spec.tex:1370) is

    nonflex(P)  ⟹  solveeq{P}{α̂}{α̂}

with NO context and NO flexibility premise: hattedness is purely SYNTACTIC
there, `α̂` being a distinct metavariable class.  The mech has one atom class,
so it must consult a context — and handing the solve `Ξ` alone hid Θ0's
flexibles.  That is the SAME unfaithful narrowing already corrected once at
this very rule (see `a_solve_eq__flex_r`'s own comment: the undefined-only
`binds α abind_flex_mono` reading, widened 2026-07-24).

**Soundness was unaffected, as predicted.**  Its only two consumers are
`a_extract_decls` (reads Ξ, never the solve) and `a_extract_decorate`, whose
solve lemmas `solve_cstr_top_guarded_tg` / `solve_cstr_decorate` quantify Θ
universally and never mention it in their conclusions.  Clean `make coq` is
green with 0 admits and all 31 `Print Assumptions` closed; the whole diff is
six files of arity threading and no proof-script changes beyond `intros`.

(Option (b) — a reachability invariant making the narrow reading provable —
is moot and was not pursued.)

**NB this is the same SHAPE of question as P6-Ss's `a_looksub__forall_r`
(§8 (h))** — a mech scoping choice made on a judgment the paper leaves
scope-free.  There the narrow choice turned out to be provable (via the
α-stack split) and was KEPT; here the narrow choice looks unprovable.
### 7.5 P6-L CLOSED (2026-07-30) — **P6 IS COMPLETE**

`a_extract_complete_gen` is `Qed` and axiom-free in
`frost/algo/prop_look_complete_extract.v`; `make coq` green from clean, 35
`Print Assumptions` all closed, zero admits.  All five P6 lemmas are done:
`P6-Cv → P6-Cs → P6-Sv → P6-Ss → P6-L`.  **P7 is now the front.**

**The file's shape**, §1–§10:

| § | content |
|---|---|
| §1 | `pskl_all_free`, `pskl_inh_eq_syn_inv`, `pskl_all_ghost_free_mono` — the two paintings agree EXACTLY on ∀-free skeletons, and ∀-free + ghost-free + lc IS a monotype painting |
| §2 | `a_guess_mono_rename_tvar`, `a_guess_mono_all_of_one` — one instance at a fresh β becomes `a_guess_mono__forall`'s cofinite family |
| §3 | `ad_refine_syn_hole_l_inv`, `ad_precise_hole_inv_mono` — a ◇ facing the counterpart pins a Θ-scoped MONOTYPE there; this is what makes the θ-extension well-defined |
| §4 | `ad_refine_syn_all_l_not_mono` — a ∀-headed source never refines to a monotype painting |
| §5 | ghost-freeness is open-invariant; `uskl_ghost_free_to_pskl`; `a_wf_ptyp_of_wf_pskl_mono`; `ad_refine_syn_rename_delta` / `ad_precise_rename_delta` |
| §6 | `ad_precise_{arrow,tophole,all}_l_inv` — inversion WITH A REPLAY (the `__flex_r` chase) |
| §7 | `msubst_pskl_{lookup_congr_ftv,mid_skip}`, `ad_precise_delta_mono`, `a_wf_pskl_rename_delta` |
| §8 | `a_inc_lookup_ftv`, `msubst_{lc,ftv}_app_wf`, `msubst_pskl_ftv_fresh`, `{a_wf_pskl,ad_precise}_all_of_one` |
| §9 | `a_guess_ty_witness` — the witness induction |
| §10 | `a_extract_complete_gen` |

**What the paper's one-line third premise actually costs.**  *"By induction on
the definition of guess^N(P_s)"* is §9, and it is an induction the OTHER way
round: P6-L's conclusion is existential in Ξ and the extract output, so nothing
hands us a guess — `a_guess_ty_witness` BUILDS `a_guess_mono` and the
metasubstitution extension κ′ at the same time, descending `P_s` on
`size_pskl`, reading the counterpart's matching piece off the precision premise
at each node.  Three things that are invisible in the paper:

1. **The `__flex_r` CHASE.**  Precision at a composite source can be concluded
   by the structural rule OR by `ad_refine_syn__flex_r`, which fires whenever
   the counterpart is a DEFINED flexible: it swaps the target for that
   definition's monotype painting and leaves the source untouched.  At the ∀
   that refutes (§4).  ⚠️ At the ARROW and the ∀◇ **it does not** — κs can turn
   a flexible into an arrow, so the source's shape does not clash with a
   monotype painting.  So §6's arrow and ∀◇ lemmas chase the chain and return a
   REPLAY function that re-applies the chased steps to whatever the caller
   builds.  This is one-step re-application, NOT transitivity of refinement,
   which is FALSE (`cex/cex_refine_not_transitive.v`).  The chase terminates on
   the DERIVATION, so §6's lemmas are inductions on it, not on a size.
2. **Why the extension is legal.**  `ad_refine_syn__hole`'s fill premise is
   `Θ ⨟ empty ⊢ₚₛᵃ P` — CLOSED.  So a hole under a binder can never be filled
   with the bound variable, and κ′'s images are Θ-well-formed monotypes however
   deep the ∀-nesting goes.  That is the mechanical content of the paper's side
   remark at tex:2812 ("no quantifier of `⌊ψa⌋ˢ` faces a universal ghost in
   `P_s`, since all tags are in Ψa").
3. **Both Δ's move, independently.**  `Δ0` carries `P_s`'s binders (wf), `Δ` the
   counterpart's (precision).  `a_wf_pskl__all` and `ad_refine_syn__all` each
   grow their own; the ∀◇ case RESETS `Δ0` to ∅ (`a_wf_pskl__tophole`'s body is
   wf CLOSED).  Pin them as separate parameters, not one.

**One-instance→cofinite-family, three times.**  The ∀ case runs the IH at ONE
fresh β and owes cofinite families: guess (§2, with the payload CLOSED over β
via `close_ptyp_wrt_ptyp`), wf (`a_wf_pskl_all_of_one` + `a_wf_pskl_rename_delta`)
and precision (`ad_precise_all_of_one` + `ad_precise_rename_delta`).  The
refinement rename routes through the fill-hygiene `_f` kit:
`ad_refine_syn_f_rename` wants the renamed name in `F`, and
`ad_refine_syn_f_fextend_dom` puts it there for free because it is outside
`dom Θ`.  ⚠️ The ftv-keyed `ad_refine_syn_f_fextend_ftv` would NOT do: β occurs
in the target `X0^β`, which is the whole point.  Keeping the rename honest also
needs `β ∉ ftv (κ P)`, which is why the witness statement carries
`a_inc_lookup_ftv`'s scoping property of the incoming κ as a premise.

**Assembly reused the HOMOGENEOUS-FLEX REORDER KIT** of
`prop_look_complete_cstr.v` and needed nothing new: `a_extract` emits `Ξc,Ξ'`
where the natural build order is `Ξ',Ξc`, and both blocks are undefined
flexibles, so `a_inc_flex_prefix_build`/`_split`, `msubst_pskl_app_swap` and
`a_wf_pskl_swap_app` cover all four conclusions.  `a_extract`'s emission order
was deliberately left alone (audit F4's "reversed Ξ orders" is immaterial here,
and changing it would have churned `test_examples.v`).

**Statement deltas vs the paper — both are the paper's own prose, restored:**
`Θ ⨟ Δ ⊢ₚₛᵃ ⌊ψa⌋ˢ` (the "ψa is a valid instantiation" premise, which
`ad_partial_precise_complete` needs) and `Δ ∩ ftv ψa = ∅` (the precision HOLE
rule's side condition).  As in P6-Ss, the paper's `inc[θ≡θa]{Θ0}{Θ}` is the
reflexive `a_inc_equiv Θ0 κ κ Θ`: the mech's `a_inc_equiv` is POSITIONAL, so
"θa agrees with θ on Θ0" is carried instead by the a_inc conclusion exhibiting
θa as the EXTENSION `κa ++ κ`.

**Housekeeping.**  §1's locally-declared `pskl_ghost_free` Inductive duplicated
`prop_pat_sub.v`'s Fixpoint of the same name and is gone; the file uses the
existing one (which also supplies `ptyp_to_pskl_ghost_free` and
`pskl_ghost_free_open_rec`).

---

## 9. P7 plan (drafted 2026-07-30, right after P6-L closed)

P7 is the LAST front of subtyping completeness, and unlike P6 it is a **mutual
induction**, per §3's rows:

| | mech name | paper | measure |
|---|---|---|---|
| **P7a** | `a_sub_flex_complete` | lemma:complete-flex-subtyping (:2836) | induction on the contexts `Θ0 ∣ Ξ` |
| **P7b** | `a_sub_complete_gen` | generalised thm:complete-subtyping (:3050) | `lex(decl height, |Ψ|)`, after a case split on "P is a flexible in FN mode" |
| **P7c** | `a_sub_complete` | thm (algorithmic.tex:1446) | instantiate `S := P`, `Ψ := ∅` |

P7a's proof says *"by induction on the contexts of the subtyping judgement,
**mutually** with the generalised version of thm:complete-subtyping below"*, and
P7b's `P = α̂ ∧ M = FN M'` case calls P7a at `Ξ = ·`.  So the two are one bundle;
`a_consis_complete`'s 3-way mutual block is the shape precedent.

### 9.0 ⚠️ TASK 0 — SUPPLY `sub_shield` AT P7b's ForallL.  SETTLE THIS FIRST

P7b's Sub-ForallL case is the sole consumer of **P6-L**, and P6-L's statement
carries the P6-Sv/P6-Ss REPAIR premise `sub_shield Θ0 Ψa empty P0 ψa`.  That
premise cannot be dropped — the paper's P6-Sv without it is machine-checked
FALSE (`cex/cex_p6sv_forall_flex.v`) — so **P7 must SUPPLY it**, exactly as §6
(z) item 3 and §6's obligation (iii) registered.  This is the P6-L §7.4 lesson
again: settle the premise story before writing the induction.

What has to be produced, unfolding `sub_shield` at Δρ = ∅: for every P0-subterm
`P0'` reachable by `ss_walk (dom Θ0) P0` and every `Δρ'` with
`Δρ' ∩ ftv ψa = ∅`, both `flex_apart_walk Θ0 Δρ' P0' ψa` and
`flex_shield Θ0 Ψa Δρ' P0' ψa`.  The rules available for the hard leaf (P0' a
RAW Θ0-FLEXIBLE) are only:

- `fsh_clean` — needs `ftag ψa ∩ Ψa = ∅`, i.e. **ψa TAG-FREE**.  Note
  `d_tags_skl_ftag` gives `Ψa ⊆ ftag ψa`, so at a tagged ψa this rule is
  unavailable and forces Ψa = ∅.
- `fsh_flexfree` — needs `pskl_flex_free Θ0 P0'`.  ⚠️ The paper's ForallL WLOG
  (`guarded(P0) ∨ P0 = □`) does NOT give this: `guarded_pskl__var` holds for
  EVERY variable, flexible included (def_extra.v:124).
- `fsh_rho_var` — only when the facing ψa-part is a Δρ-member variable.

**The intended route (§6 (z) item 3), and it is available:** at each flexible
position of the counterpart the solution's own REFINEMENT premise pins the
κ-image to a monotype, so the facing ψa-region is consistent with a mono-ish
fill, hence a mono PAINT, hence tag-free — which is `fsh_clean`.  The kit is
already Qed in `prop_look_complete.v:3022-3100`:

    bskl_monoish  /  bskl_monoish_paint
    ad_refine_mono_paint_rhs_monoish        (refining FROM a mono paint lands mono-ish)
    ad_pat_consis_monoish_counterpart       (a tag-sorted subject against a mono-ish
                                             counterpart IS a mono paint, and Ψs = ∅)

The plan therefore said **the missing piece is one `ad_pat_sub_g` analogue of
`ad_pat_consis_monoish_counterpart`** — "against a mono-ish counterpart, a
tag-sorted subject is a mono paint and solves no tags".

⚠️ **THAT ANALOGUE IS FALSE — machine-checked, `cex/cex_p7_sub_monoish.v`
(`p7_sub_monoish_counterpart_is_false`, Qed, axiom-free).  So this route does NOT
work as sketched, and P7 TASK 0 must be restated.**  The culprit is
`ad_pat_sub_g__forall_l_tagged` — the same row that already broke P6-Ss Phase B's
planned bound (`cex/cex_p6ss_sub_target_ftv.v`), and it is literally the same
witness derivation.  Consistency's ∀ rules all require the COUNTERPART to be a
quantifier too, which is exactly why a mono-ish counterpart forces the subject
mono there.  Subtyping's ForallL does not: it INSTANTIATES.  So `∀^ε α. α` —
`is_tskl` and ghost-free, hence legal at TY — instantiated with a rigid `β` lands
on the target `β`, which is `bskl_monoish` by `bmi_var`, while the subject is not
a mono paint at all.

**What the leaf actually needs, stated directly.**  Unfold `sub_shield` at
Δρ = ∅ and look at the flexible-P0 leaf again: the only applicable rule is
`fsh_clean`, and its `ftag ψa ∩ Ψa = ∅` together with `d_tags_skl`'s
`Ψa ⊆ ftag ψa` forces **Ψa = ∅** — the ForallL guess must be TAG-FREE, i.e.
(with `a_tags_sort`'s ghost-freeness at TY) a MONOTYPE.  So the obligation is the
flex-mono WALL itself:

> a raw-Θ0-flexible position of `P0` forces the ForallL guess facing it to be a
> monotype

and NOT any statement about the subject facing a mono-ish counterpart.  Note also
that weakening the analogue to just `Ψ = ∅` would survive the witness but is
USELESS here: `__forall_l_tagged` drops its own ε (conclusion `Ψ`, premise
`Ψ ∪ Ψ'`), so a small conclusion-Ψ says nothing about `ftag ψa`.

**Restated TASK 0:** prove the wall, over `ad_pat_sub_g` + the refinement
premise, positionally.

✅ **ITS LEAF IS PROVED (2026-07-30), so the wall is NOT a blocker after all —
the earlier "P7 is blocked" reading was wrong.**  What the leaf needs is TAG
ACCOUNTING, not a shape bound, and that is `ad_pat_sub_g_monoish_tag_free` in
`frost/algo/prop_sub_shield_supply.v` (Qed, axiom-free):

    ad_pat_sub_g n NM M Ψ Θ ψ Q  →  a_wf_aenv Θ  →  is_tskl ψ
      →  bskl_monoish Q  →  Ψ [=] ∅

i.e. it is exactly the conjunct of the refuted statement that SURVIVES
`cex_p7_sub_monoish.v` — and it is the conjunct the shield wants, since
`fsh_clean`'s `ftag ψa ∩ Ψa = ∅` plus `Ψa ⊆ ftag ψa` IS "Ψa = ∅".  The proof is
one induction and it went through unchanged: a tag reaches the conclusion's Ψ
only by being SOLVED, i.e. by a rule MATCHING a tagged quantifier of the subject
against a quantifier of the counterpart; every other row either carries `Ψ = ∅`
on the rule, delegates to `ad_pat_consis_monoish_counterpart`, or is
`is_tskl`-impossible.  ⚠️ In particular `__forall_l_tagged` — the row that killed
the shape half — is harmless here: it DROPS its own ε and hands the IH `Ψ ∪ Ψ'`,
so a collapse below collapses Ψ too.  A `bskl_monoish` counterpart has no
quantifier, so nothing can be solved.

And the counterpart IS mono-ish exactly where `P0` is flexible: a
metasubstitution's images are monotypes, so `κP0` is a mono PAINT there, and
`ad_refine_mono_paint_rhs_monoish` (Qed) carries that through the refinement
premise.

✅ **AND THE SUPPLY ITSELF IS CLOSED ON THE BRANCH THAT WAS BLOCKING.**
`sub_shield_supply_mono_counterpart` / `sub_shield_supply_mono_p0`
(`prop_sub_shield_supply.v`, Qed, axiom-free):

    a_wf_aenv Θ  →  a_tags_sort NM Ψa ψa  →  is_tskl ψsubj
      →  ad_pat_sub_g n NM M Ψa Θ ψsubj Q  →  bskl_monoish Q
      →  sub_shield Θ0 Ψa ∅ P0 ψa                      (UNIFORMLY in P0)

with the corollary taking the refinement premise directly, for `κP0` a mono
PAINT — which is what a raw Θ0-flexible `P0` gives, since every image of a
metasubstitution is a monotype.  **That is exactly the configuration
`cex_p6sv_forall_flex.v` uses to refute the paper's P6-Sv, so the premise P6-L
had to carry is discharged where P7b's Sub-ForallL needs it.**

No positional decomposition is needed on this branch after all: once `Ψa = ∅`,
`fsh_clean` does not look at the payload, so it shields every `ss_walk` residue
of `P0` at once.  The work is all in the OTHER conjunct, `flex_apart_walk`,
which quantifies over the ρ-walk — and there the invariant is that a TAG-FREE
guess can never take `fastep_all_r` (the only step that grows Δρ), while every
other step preserves tag-freeness (subterms, or a mono PAINTING).  So Δρ stays
put and `fa_clean` closes every walked point (`fa_walk_tag_free`,
`flex_apart_walk_tag_free`, `sub_shield_tag_free`).

⚠️ **ONE RULE HAD TO BE NARROWED, and the earlier note here was wrong about
why.**  `fastep_flexdef_r` (`prop_look_complete.v:3798`) installed
`ptyp_to_uskl_syn τ` for an UNCONSTRAINED τ, which makes `flex_apart_walk`
underivable from cleanliness of ψa — the walk admits garbage no context
justifies.  It now carries `ftv (paint τ) ∩ Δρ = ∅`, exactly the fact its own
comment said a call site would discharge.  Cost: ZERO — its single builder
(P6-Sv's FlexMono row, `prop_look_complete_sub_var.v:2863`) already had it in
scope as `Hclean` for its own `fsh_clean`, and the full rebuild was green
first time.  ⚠️ The previously-recorded fix — "the Δρ' generality is slack, make
`sub_shield` Δρ'-monomorphic" — was WRONG: `sub_shield_add_fresh` (Sub-ForallL's
Δρ growth in P6-Ss) genuinely uses that quantifier.

✅ **AND THE NON-COMPOSITE SHAPES OF `P0` ARE DONE TOO** — `sub_shield_atomic`
(same file, Qed): at `unit` / `◇` / a RIGID variable NEITHER walk moves `P0`
(`ss_step`'s two rows need an arrow or a ∀; of `fa_step`'s nine only the three
ψ-side ones can fire, and they all leave `P0` alone), so the shield is one
`flex_apart` constructor plus `fsh_flexfree`, uniformly in ψa and with no tag
reasoning at all.

**So TASK 0's RESIDUAL IS EXACTLY ONE SHAPE.**  P7b's Sub-ForallL comes with the
paper's WLOG `guarded(P0) ∨ P0 = □`, and `guarded_pskl` is `unit | var | arrow`
(def_extra.v:122) — so a ∀ or ∀◇ `P0` never reaches the call at all.  Of what
remains:

| `P0` | covered by |
|---|---|
| `□`, `unit`, rigid var | §5 `sub_shield_atomic` |
| FLEXIBLE var | §4 — `κP0` IS that variable's monotype image, so `Q` is mono-ish |
| *any* `P0` with a mono-ish `Q` | §4 |
| **arrow, with a non-mono-ish `Q`** | ⚠️ **OPEN** — but see §9.0.1 / §9.0.2, which close all of it except a `P0` carrying a ∀ BELOW its head |

⚠️ **AND THAT LAST ROW IS NOT MERELY UNPROVED — THE PREMISE IS UNSATISFIABLE
THERE.**  Machine-checked: `cex/cex_p7_shield_arrow.v` (two witnesses, Qed,
axiom-free).  `sub_shield`'s `flex_apart_walk` conjunct quantifies over the
ρ-walk, and Sub-ForallL's step `fastep_all_r` — which P6-Sv's own ForallL row
builds (`prop_look_complete_sub_var.v:2470`) — opens a tagged quantifier of the
guess at a fresh β, adds β to Δρ, and LEAVES `P0` ALONE.  So the walk reaches
`flex_apart Θ0 {β} P0 (var β)`, and at an ARROW `P0` no rule applies:
`fa_clean` wants `{β} ∩ {β} = ∅` and every congruence row wants another shape.
Hence `sub_shield Θ0 Ψa ∅ (P1 → P2) (∀^ε b. b)` is **unsatisfiable**: P6-L is
vacuous there and P7b's Sub-ForallL cannot use it.

**The repair is identified and it is a MISSING MIRROR.**  `flex_shield` carries
`fsh_rho_var` (`α ∈ Δρ ⟹ shield against `var α`, whatever the payload), added
precisely because "WITHOUT this rule the premise is TOO STRONG" — see its own
comment.  `flex_apart` never got it, and the stuck state is exactly its shape.
Adding `fa_rho_var` kills both witnesses.

⚠️ **HELD PENDING THE AUTHORS' DECISION**, because `flex_apart` is P6-Cv's
REPAIR PREMISE — reshaping it changes a side condition the PAPER must adopt.
Cost measured before backing the change out: the ~8 `flex_apart` inversion
lemmas each gain a case, all but one closing with `apply fa_rho_var;
assumption` (only `flex_apart_tophole_p0_inv` actually needed a bullet); and
`flex_apart_flex_var_clean` (`prop_look_complete.v:2907`) genuinely BREAKS —
"a flexible P0 forces the guess Δρ-CLEAN" gains a second way to hold, so it must
weaken to a disjunction whose right arm is "the guess is a Δρ-variable under a
∀◈ stack".  Its single consumer (P6-Cs's Arrow row,
`prop_look_complete_cstr.v:2199`) still reaches its "ψa is a mono paint, hence
tag-free" conclusion — a Δρ-variable IS one — but only after peeling that stack,
which at `SK` is not free.  Registered in docs/PAPER-GAPS.md.

**The backstop, and the one genuinely open dependency.**  For the remaining
shape — a rigid-∀-spine skeleton facing a bare flexible payload — the argument
is the flex-mono WALL: the authors decided (§6 (z)) that `broom_flex_poly`-shaped
programs are REJECT-by-design, so such solutions do not exist at the theorem's
call sites.  ⚠️ That decision was recorded against an IMPLEMENTATION CRASH
(docs/PAPER-GAPS.md, "broom_flex_poly: should not happen"), not against a proof.
**If Task 0 cannot discharge the flexible-P0 leaf, P7b is BLOCKED and the
authors must be told** — do not weaken P6-L's statement to get past it, and do
not thread `sub_shield` outward as a P7b premise without first checking it
survives P7c (where `Ψ = ∅` but `Ψa` at a ForallL is NOT empty, so the
threading does NOT become vacuous at the top).

### 9.0.1 TASK 0 (a) LANDED (2026-07-30) — the FLEX-FREE branch

`prop_sub_shield_supply.v` §6, all Qed and axiom-free.  §10.6 gave `flex_apart`
the base row `flex_shield` already had (`fa_flexfree`), so the two guards now
agree on "nothing to keep apart", and the shield follows for ANY flex-free `P0`
— uniformly in ψa **and in Δρ** (§5's `sub_shield_atomic` is the Δρ = ∅
special case, and it is subsumed: `unit` / `◇` have no free variable and a
RIGID variable is not a flexible one).

The only content is that flex-freedom SURVIVES both walks
(`ss_walk_flex_free`, `fa_walk_flex_free`).  Every `P0`-moving step takes a
SUBTERM or opens a ∀ at a binder the AVOID SET keeps out of `dom Θ0` — and a
variable outside the context is bound nowhere, hence flexible nowhere
(`pskl_flex_free_open_fresh`; contrast `pskl_flex_free_open_tvar`, which puts
the binder INTO the context and is what the ForallR *descent* uses).  This is
the second payoff of the avoid set §10.6 added to all three walks.

### 9.0.2 TASK 0 (b) — the residual is MUCH smaller than "arrow with a non-mono-ish Q"

⚠️ **The plan's positional route (decompose along `fsh_arrow` / `fsh_all_l` /
`fsh_all_r` and apply the mono lemma at each flexible leaf) is NOT what the
case needs, and reading the rules again shows why.**  `bskl_monoish` was never
the load-bearing hypothesis.  A tag LEAVES the index at exactly ONE rule in
the whole system — `ad_pat_consis__forall_inh_tagged` (`Ψ = ε ∪ Ψ0`) — whose
counterpart is a `bskl_all_inh`.  Every other row of consistency AND of
subtyping either forces `Ψ = ∅` on the rule or passes Ψ down unchanged (or, at
`__arrow`, splits it into two branches that do the same).  In particular
`__forall_l_tagged` DROPS its own ε rather than solving it, and
`__forall_syn_tagged` — a tagged ∀ facing a SYNTHESISED ∀ — passes Ψ through
untouched.

So the real hypothesis is **the counterpart carries no INHERITED quantifier**,
`bskl_inh_free`.  That is strictly weaker than `bskl_monoish`: it admits
ghosts (`◇`, `∀◇`) and synthesised ∀s, all three of which a refinement really
does produce (`ad_refine_syn__hole` paints its fill SYNTHESISED,
`__tophole_fill` emits `bskl_all_syn`, `__tophole_keep` emits `bskl_tophole`).
It also drops the `is_tskl` and `a_wf_aenv` premises §2/§4 needed — the
flexible-lookup rows land on `ptyp_to_bskl_syn`, a SYN painting, which is
inh-free whatever the monotype is.

LANDED in `prop_sub_shield_supply.v` §7/§8, all Qed and axiom-free:

    ad_pat_consis_inh_free_tag_free   Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q → inh_free Q → Ψ = ∅
    ad_pat_sub_g_inh_free_tag_free    ad_pat_sub_g … Ψ … Q → inh_free Q → Ψ = ∅
    ad_refine_syn_inh_free            refinement never CREATES an inherited ∀
    sub_shield_supply_inh_free_counterpart
    sub_shield_supply_all_free_p0     P0 has no ∀ ⟹ the shield, whatever ψa is

The chain is `P0` has no ∀ ⟹ `κP0` has no ∀ (κ's images are MONOTYPES,
`a_inc_lookup_mono`) ⟹ `inh{κP0}` is inh-free ⟹ `Q` is inh-free
(`ad_refine_syn__all` is the only row that emits an inherited ∀ and it demands
one on the left) ⟹ `Ψa = ∅` ⟹ `sub_shield_tag_free`.

**The residual is therefore no longer "an ARROW `P0` with a non-mono-ish
counterpart" but the much narrower "a `P0` carrying a ∀ BELOW its head"** —
the head itself is `unit | var | arrow | □` by the WLOG, so the open shape is
`P1' → P2'` with a `pskl_all_syn` strictly inside.  For that shape the
positional argument really is needed, and the alignment it needs is NOT
structural between `P0` and ψa (they are related only through the derivation:
ψa sits at the α-positions of the subject `(κS)[ψa/α]`, and `P0` faces the
subject through `Q`).  Sketch of where the work goes, for whoever picks it up:

- Peel ψa: `fsh_all_r` takes tagged ∀s (growing Δρ), `fsh_topholeg_r` takes
  ∀◈; `fsh_arrow` matches an arrow ψa against the arrow `P0`; `fsh_all_l` /
  `fsh_tophole_l` descend `P0`.  `unit` / `◈` / any variable close by
  `fsh_clean` or `fsh_rho_var`.
- The ONLY stuck configuration left is a RAW FLEXIBLE `P0`-leaf facing an
  ARROW payload that mentions a peeled binder — which is exactly the
  `cex_p6sv_forall_flex.v` shape (`ψa = ∀^ε β. β→β` against `P0 = α̂`).
- Ruling it out needs "the tag ε is SOLVED, hence faces an inherited ∀ of `Q`,
  hence the aligned `Q`-part is not mono-ish — but a flexible `P0`-leaf forces
  it mono-ish".  Making "aligned" precise is a POSITIONAL refinement of
  `ad_pat_sub_g_inh_free_tag_free`, and that is a new lemma of P6 size.

### 9.1 Case map for P7b (paper :3050-3420 and on)

Read the paper's cases in this order; the first four are cheap because their
content is already a Qed black box.

| declarative rule | route | note |
|---|---|---|
| `P = α̂`, `M = FN M'` | **P7a at Ξ = ·**, then algorithmic `FlexMono` | the mutual edge |
| Sub-Infer | `a_consis_complete` | `M = TI ⇒ Ψ = ∅` and `skmod` forces `P0 = □` |
| Sub-Check | `a_consis_complete` | needs "`P0` concrete ⇒ the consistency output is equivalent to `P0`" |
| Sub-UnivGhostR | `a_consis_complete` | `N = SK`, `M = TC`, `P0 = □` |
| Sub-Arrow | `a_consis_complete` on the domain + IH on the codomain | ⚠️ threads `Θ0 → Θ1 → Θ2` and composes THREE `a_inc_equiv`s |
| Sub-ForallR | IH at `Θ0,α` | ⚠️ output context is `Θ1,α,Ξ` — the Ξ-suffix strip is the work |
| Sub-ForallL | **P6-L** then **P5c** (`ad_pat_sub_precise_subst`) | Task 0 lives here; also the WLOG-by-congruence hazard H3 |

⚠️ Two of these lean on a property the paper asserts in passing and marks with
its own TODO (`subtyping-proofs.tex:3243`: *"we may have the property that, in
algo subtyping, when input `P_0` is a concrete type, RHS of subtyping is always
`P_0`"*): Sub-Check needs it for `P'_0 ≡ P_0`, Sub-ForallR for `P_1 ≡ P_0'`.
The plan said: mechanize it as a standalone lemma before the two cases,
because if it is FALSE both cases need rewriting.

⚠️ **IT IS FALSE — machine-checked, `cex/cex_p7_concrete_rhs.v`
(`p7_concrete_rhs_is_false`, Qed, axiom-free), and it is false for a reason
that does not go away by strengthening the premises.**  At `N = TY` the mode
constraint `skmod[TY]{P0}{TC}` forces `P0 = ptyp_to_pskl A` — that IS the
paper's "concrete type", and it is the only place the concreteness comes
from.  But consistency's `FlexL` row returns the SUBJECT:

    Θ ⊢ₐ[ P0 ] α̂ ∼ α̂ ⊣ Θ'          (a_consis__flex_l, via a_assign)

and algorithmic `Arrow` copies that output into its own.  So already at
`P0 = unit → unit` (concrete, and entirely flexible-FREE), subject `α̂ → unit`,
the RHS is `α̂ → unit`, not `P0`.  The witness carries `a_wf_aenv Θ0` and
`skmod[TY]` as premises, so no missing side condition explains it away, and
reading "concrete" as also excluding flexibles does not help — the flexible is
on the SUBJECT side, which the property does not constrain.

**What this does and does not settle.**  It refutes the SIMPLIFICATION the
TODO proposes; it does NOT refute Sub-Check or Sub-ForallR, whose written
arguments already go through the EQUIVALENCE ("`P'_0` is equivalent to `P_0`",
:3181; "`P'_0` and `P_1` are equivalent through `Q`", :3238) — and the
equivalence is exactly what the run's output context supplies (`α̂ ≔ unit`
here).  So the mechanization must keep the equivalence route, and the real
obligation for both cases is

    msubst_pskl κ1 (output)  =  msubst_pskl κ1 P0                    (†)

— equality only AFTER the metasubstitution, which absorbs the definition the
witness exploits.

✅ **AND THE CONSISTENCY HALF OF (†) IS NOW PROVED** —
`frost/algo/prop_sub_concrete_rhs.v`, all Qed and axiom-free.  The right
relation was already in the development: `a_pskl_tyequiv` (`≡ˢ`,
def_meta.v:172) is "the `a_tyequiv` equational theory lifted to skeletons:
definitions of flexible variables unfold, ghosts are inert", introduced for
`a_inc`'s GMM-style SEMANTIC middles.  And the proof is NOT on consistency —
`a_consis_sound` already exports `Θ1 ⨟ ∅ ⊢ᵣᵃ inh{P0} ⊳ Qt` with `⌊Qt⌋ = P'`,
so all that is left is:

    ad_refine_syn_ghost_free_equiv   refinement out of a GHOST-FREE source
                                     only ever UNFOLDS DEFINITIONS
    a_consis_concrete_output_equiv   Θ1 ⊢ P0 ≡ˢ P'          (the paper's :3181)

One induction, no context threading — refinement keeps its context fixed (the
one row that extends it, `__tophole_fill`, needs a ghost on the left and is
excluded), `__unit`/`__var` are identities, `__arrow`/`__all` congruences, and
the only surviving rows are the two flexible lookups, which are
`a_pskl_tyequiv__flex_def` verbatim, one on each side.

✅ **AND THE `a_sub` HALF TOO** (Sub-ForallR's ":3238"), `a_sub_concrete_output_equiv`.
It was planned as a MUTUAL induction with `a_sub_flex`; that induction is NOT
needed.  `a_sub_sound` (prop_decorate_key.v:3326) already exports the
output's refinement FROM the input skeleton — the very same conjunct
`a_consis_sound` exports, in the very same shape — so the same
`ad_refine_syn_ghost_free_equiv` applies verbatim and the whole half collapses
to one `destruct`.

**So BOTH cases the `:3243` TODO was meant to simplify now get their step from
the SOUNDNESS theorems**, not from any new induction.  That is the honest form
of the authors' intuition: not "the RHS is `P_0`" (false) but "the RHS is `P_0`
up to the definitions the run recorded".

§4 of the same file additionally has the three ≡ˢ transports that MOVE an
equivalence once you have it, all Qed — `a_pskl_tyequiv_isub_mono` (Sub-Arrow
reads its domain equivalence off at Θ1 and must state it at Θ2; `a_isub`'s "a
definition, once made, is never rewritten" is exactly and only what it uses),
`a_pskl_tyequiv_weaken`, and `a_pskl_tyequiv_subst_flex_def`.

⚠️ Note `a_sub__check` itself already OUTPUTS `P0` (`a_consis_chk` hides the
consistency output existentially), so the mech's Sub-Check does not need (†)
to build the derivation — only to transport the PRECISION conclusion from
`a_consis_complete`'s output `P1` to `P0`.

### 9.1.1 The remaining IH-free rows — FOLLOW THE PAPER; a shortcut around it is false

⚠️ **RETRACTION.**  Earlier versions of this section built an elaborate route for
Sub-Infer / Sub-UnivGhostR — a shared lemma, then a threaded induction, then a
transport kit for reconciling Θ- and Δ-binders.  That whole line came from
MISREADING the paper.  It writes, at :3134,

> The consistency premise, together with `⌊S⌋ = P` and
> \Cref{thm:complete-consistency}, gives `Θ ⊢ precise{θP}{Q}`.

which is not "read a precision off the consistency premise" but "invoke
**thm:complete-consistency**" — a theorem, already mechanized as
`a_consis_complete` — on the consistency problem `(Θ_0; □; P)`, and take the
precision from its conclusion.  `skmod` forces `P_0 = □` in both rows, so the
problem is exactly the one the theorem is about.

✅ **All the route needs beyond the black box is one small lemma, now proved**
(`a_consis_hole_p0_output`, Qed): at `P_0 = □` the algorithmic consistency
OUTPUT is the SUBJECT, so the theorem's precision — stated about the run's
output — IS a precision about `P`.  Of the fifteen `a_consis` rows only three
admit `P_0 = □` (`__ghost`, whose subject IS the ghost; `__ghost_r`; `__flex_l`)
and each returns its own subject; `__univ_ghost2` is the only row that does not
fix `P_0`'s shape and its `guarded_pskl P_0` premise excludes the ghost.

**So write these two cases the paper's way.**  Sub-Check is the same shape one
level up: `a_consis_complete` for the run and the precision, then
`a_consis_concrete_output_equiv` (§9.1) to move that precision from the
consistency output to `P_0`.

#### The assembled route, and the ONE piece still missing

1. `skmod` forces `P_0 = □` (both mode-compat relations pin `TI` to the ghost).
2. `a_sub__infer` gives the run, output `P` at context `Θ_0` — so the two
   increase conjuncts are `ζ := κ` + `opt_axiom_factor`, as in
   `a_sub_complete_ghost`.
3. The DECORATED consistency premise undecorates: `ad_pat_consis_strip_tags`
   (prop_consis_precise.v:275) turns `Ψ ⨟ Θ ⊢ₛᵃ κR ∼ Q` into
   `∅ ⨟ Θ ⊢ₛᵃ pskl_to_uskl ⌊κR⌋ˢ ∼ Q`, and `⌊κR⌋ˢ = κ⌊R⌋ˢ = κP` by a one-line
   commutation.
4. `a_consis_complete` on `(Θ_0; □; P)` — its other two premises ARE this
   motive's refinement premises at `P_0 = □`.
5. `a_consis_hole_p0_output` says the run's output is `P`, so the theorem's
   precision IS a precision about `P`.

⚠️ **Step 5 lands the precision under the theorem's own `ζ`, not under `κ`**, and
that is the one piece still missing.  `msubst_compose_id_pskl` collapses the
package's composite on a Θ0-scoped skeleton, so what is wanted is

    Θ ⨟ Δ ⊢ₚᵣᵃ (msubst_pskl κ P) ⊑ (msubst_pskl σ P)
      given  a_inc_equiv Θ0 κ σ Θ  and  Θ0 ⨟ Δ0 ⊢ₚₛᵃ P

— *precision is stable under equivalent metasubstitutions* — after which
`ad_refine_syn_trans` composes it with the theorem's own precision.

**This is NOT the general `≡ˢ` transport**, which an earlier reading of the gap
called for.  That form is awkward: `≡ˢ` is an equivalence CLOSURE, so the
induction has to carry both directions at once and its `trans` row needs wf of a
MIDDLE skeleton nobody supplies.  The statement above sidesteps all of it by
inducting on **the wf of `P`**, because the equivalence actually in play is not a
general `≡ˢ` but congruence over `P`'s own structure with `≡ᵗ`-**monotypes** at
the leaves — a metasubstitution's images are monotypes.

Row by row: `unit` / `hole` are constructors; `arrow` / `all` / `tophole` are
congruences (the last by `__tophole_keep`, whose guard wf supplies and `msubst`
preserves); a Δ-bound or RIGID variable is missed by both metasubstitutions
(`msubst_lookup_notin`), so both sides are the same variable; and a FLEXIBLE
variable is the only real case — `a_inc_equiv_lookup` gives `Θ ⊢ κα ≡ᵗ σα`,
`a_inc_lookup_mono` gives both monotypes, and **`tyequiv_mono_refine_syn`
(prop_precise_recover.v:90) IS that case, already Qed**.

Side conditions, both standard and both available at the call site: `Δ0 ⊆ Δ`, and
Δ-binders fresh for the context (the same condition `ad_refine_syn_trans` itself
carries).

#### What the detour did produce, and is worth keeping

- `cex/cex_p7_sskl_precise.v` — the SHORTCUT (precision directly from the
  consistency premise, without completeness) is FALSE, and structurally so:
  consistency opens a ∀ into Θ while refinement opens it into Δ, so a
  consistency derivation may fill a ghost with a binder precision cannot see.
  Witness `∀◇.` against `∀α. α`.  A standing warning, since the shortcut looks
  available.
- The Θ↔Δ transport kit — `a_wf_pskl_reassoc_mid`,
  `ad_refine_pskl_f_reassoc_mid` / `_reassoc`, `ad_refine_pskl_f_fgrow`,
  `ad_refine_pskl_f_weaken_tvar`, `a_wf_pskl_weaken_tvar` — all Qed.  Not needed
  for these two cases, but they are general facts about refinement's hygiene
  index (`_fgrow` in particular: `_fmono` only SHRINKS `F`, and growing it is
  sound for a binder the context does not know) and Sub-ForallR's Ξ-suffix strip
  is the next likely consumer.
- `ad_pat_consis_ghost_subject_no_forall`, `is_sskl_inh_no_forall` — context-free
  facts about ghost subjects, cheap and reusable.

**Lesson, and it is the expensive one from this session:** when the paper cites
one of its own theorems, follow the citation before inventing a lemma.  Three
successive "the step is false / holds / is false again" records here all came
from arguing about a statement the paper never made.

### 9.1.2 CLOSED (2026-07-30) — the missing piece landed, and THREE cases with it

✅ **`a_inc_equiv_precise_msubst` is Qed and axiom-free**
(`prop_sub_complete_thm.v`), and it came out with ONE side condition instead of
the two the plan guessed at.  The route §9.1.1 sketched was right: induct on the
**wf of `P`**; `unit` / `hole` are constructors, `arrow` / `all` / `tophole` are
congruences (the last by `__tophole_keep`, whose guard wf supplies and `msubst`
preserves), and the flexible leaf is `tyequiv_mono_refine_syn` verbatim.

Two things the writing-out corrected:

- **`Δ`-freshness is NOT needed.**  The plan expected `Δ0 ⊆ Δ` plus "Δ-binders
  fresh for the context".  Only `Δ0 ⊆ Δ` survives: the variable row splits on
  whether the metasubstitutions SEE α (`α ∈ dom κ` / `α ∈ dom σ`) rather than on
  where α is bound, and BOTH answers are usable — `a_inc_dom_flex` turns a hit
  into `a_binds_tvar α Θ0` (the ≡ᵗ route), and a double miss makes both sides
  the SAME variable, closed by `__var` from `α ∈ Δ0 ⊆ Δ`.
- **The hypothesis is stated POINTWISE**, `∀α, a_binds_tvar α Θ0 → Θ ⊢ κα ≡ᵗ σα`
  (`a_inc_equiv_precise_msubst_gen`), with `a_inc_equiv` supplying it via
  `prop_normal.a_inc_equiv_lookup`.  That is what makes the FLIPPED direction
  free (`a_inc_equiv_precise_msubst_flip`, one `a_tyequiv__sym`) — and Sub-Check
  needs the flip, while Sub-Infer needs the forward one.  `a_inc_equiv` itself
  is not obviously symmetric: `a_inc_equiv__flex_def`'s third premise mentions κ.

✅ **Sub-Infer** (`a_sub_complete_infer`) and ✅ **Sub-Check**
(`a_sub_complete_check`) are Qed, both by the paper's route.  The shared core is
`a_sub_complete_hole_p0_precision`: at `P0 = □` the motive's three solution
premises ARE `a_consis_complete`'s, `a_consis_hole_p0_output` says the run
returns the SUBJECT, and the stability lemma + `ad_refine_syn_trans` move the
result from the theorem's ζ to κ.  Supporting facts, all Qed:
`uskl_to_pskl_msubst_uskl_syn` (the one-line commutation), `ad_pat_sub_g_ti_consis`
(at `M = TI` only `__infer` / `__ghost` / `__ghostg` fire, and all three carry a
tag-free consistency), and `ad_refine_syn_hole_l_target_wf`.

⚠️ **Sub-Check does NOT need `a_consis_concrete_output_equiv`.**  The plan routed
its precision through the consistency OUTPUT, but the algorithm never returns
that output: `a_sub__check` hides it existentially inside `a_consis_chk` and
returns `P0`.  So the precision goal is `ζP0 ⊑ ⌊Q⌋`, and at `Q = inh{B}` the
motive's **P0-fill premise IS `κP0 ⊑ B` by definition of `ad_precise`** — the
goal closes outright, modulo the κ→ζ move.  What `a_consis_complete`
supplies at Sub-Check is the RUN and the two increase conjuncts, not the
precision.  (§9.1's closing note already observed that `a_sub__check` outputs
`P0`; what it did not observe is that the fill premise then finishes the job.)
`a_consis_concrete_output_equiv` remains Qed and is presumably Sub-ForallR's.

Sub-Check takes two hypotheses beyond the motive, both to be supplied by the
bundle and both registered in docs/WF-SIDE-CONDITIONS.md: `guarded_pskl P0`
(the algorithm's Check-vs-ForallR dispatch — the paper's own case split) and
`Θ ⨟ ∅ ⊢ₚₛᵃ ⌊Q⌋` (external wf of the counterpart, which `ad_refine_syn_trans`
needs and which the `P0 = □` rows get for free).

### 9.1.3 ⚠️ Sub-UnivGhostR IS VACUOUS UNDER THE MOTIVE'S THIRD PREMISE

Machine-checked: `cex/cex_p7_univ_ghost_r_vacuous.v` (Qed, axiom-free) plus
`ad_refine_pskl_f_tophole_r_shape` in `prop_sub_complete_thm.v`.

The row's subject is `guarded_uskl` and its counterpart is `∀◇.Q0`, so the
motive's THIRD solution premise reads `κ⌊R⌋ˢ ⊳ ∀◇.⌊Q0⌋` with a guarded
left-hand side — and refinement has no rule putting a `∀◇` on the RIGHT of a
non-ghost left: `__tophole_keep` / `__tophole_remove` want a `∀◇` on the LEFT,
`__hole` wants a `◇` there, and `__flex_l` only unfolds a definition into
another `ptyp` painting, which is a ghost nowhere.  So the case closes by
CONTRADICTION (`a_sub_complete_univ_ghost_r`, Qed) — the row is proved, and the
theorem says nothing about the solutions it describes.

⚠️ **The third premise is the MECH's, not the paper's**, and §1's justification
for it does not survive contact.  §1 said it "is exactly what `a_consis_sound` /
`a_sub_sound` PRODUCE for every algorithmic output".  `a_consis_sound` does.
**`a_sub_sound` (prop_decorate_key.v:3326) does NOT** — its conclusion has
`Θ0 ⊴ Θ1`, wf, the decorated subtyping judgment and the P0-fill, and no subject
refinement.  It could not have one: algorithmic `UnivGhostR` outputs `∀◇.P` from
the input `P`.  So for subtyping the third premise is not the sound/complete
mirror it is for consistency.

§2 of the cex file exhibits the smallest configuration where the paper's TWO
conditions hold and the third fails (`Θ0 = Θ = ·`, `κ = ι`, subject `unit`,
counterpart `∀◇.unit`), so this is a real loss of coverage, not a vacuity that
was there anyway.  Registered in docs/PAPER-GAPS.md; the authors must choose
between (a) dropping the third condition — NOT free, since it is literally
`thm:complete-consistency`'s own third premise at the subproblem `(Θ0; □; P)`
that Sub-Infer and Sub-Check invoke — (b) keeping it and stating the theorem as
not covering `∀◇`-counterpart solutions, or (c) weakening it modulo the `∀◇`s
that UnivGhostR / UnivGhostL insert.

### 9.2 P7a's two interesting cases (paper :2861-3040)

`Flex-Solve` and `Flex-Assign`; the paper omits the rest as "routine IH".

- **Flex-Solve** splits `θα̂0` into `τ1 → τ2` by inversion of declarative
  Sub-Arrow on the equivalence `θα̂0 ≡ τ1→τ2`, then BUILDS `θs` mapping the two
  fresh flexibles.  The construction is the assign/unify walk recipe
  (mid-strip / mid-insert) from `remech-complete-mu-bundle`; `a_inc__flex_def`'s
  `≡ᵗ` middle is what absorbs `α̂0 := α̂→β̂`.
- **Flex-Assign** substitutes `τ/β̂` in BOTH the subject and `P0`, so it needs
  `ad_pat_sub_{subst_flex,subst_flex_def}` (already Qed, `prop_pat_sub.v`) plus
  `a_inc`'s "extend the source with `β̂ := τ`" step, which is `a_inc__flex_def`
  read backwards — check `a_inc_mid_strip_flex_def` /
  `a_inc_equiv_mid_insert_flex_def` (`prop_consis_complete.v:2059`, :2100) cover
  it before writing anything new.

### 9.3 What NOT to redo

- The homogeneous-flex reorder kit (`prop_look_complete_cstr.v`) — see §7.5.
- The `_f` fill-hygiene transports for renaming a Δ-bound variable — §7.5.
- `a_consis_complete` and `complete_mu` are Qed black boxes; four of P7b's
  seven cases are just their application.

---

## 10. `flex_apart` and `flex_shield`, rethought as a whole (2026-07-30)

✅ **CLOSED — read §10.6 for the settled version and what landed.**  §10.5's
"one predicate" reading is retracted in turn: see §10.6.

⚠️ **§10.5 was the previous attempt at settling this.**  §10.3 said "delete
`flex_apart`"; §10.4 said "no, the descents must differ"; §10.5 VALIDATES §10.3
against the existing `flex_shield` kit and RETRACTS §10.4.  The intuition in
§10.1-§10.2 was stable throughout.

Written after `cex_p7_shield_arrow.v` showed a `fa_rho_var`-shaped hole, and
instead of patching it.

### 10.1 The intuition — one hazard, one position, two ways to fail

Both premises guard exactly one thing.  The solve's `SolEq-FlexR` / `SolS-Flex`
rules **discard the accumulated skeleton `Pi` and output the bare flexible `α̂`**.
Completeness must then show that output is precise to the guess — but `θ(α̂)` is a
**monotype fixed by the SOLUTION, before the run starts**.  So it can only be
precise to a guess-part that a pre-fixed Θ-monotype can reach, and exactly two
things put a part out of reach:

1. **a TAG** — a tagged ∀ is a polytype and no monotype is precise to one;
2. **a RUN-INTRODUCED BINDER** — the algorithm's own ∀ binders (tracked by `Δρ`)
   are local, while `θ(α̂)` is Θ-scoped and was chosen before they existed.

`flex_shield` was built for (1), `flex_apart` for (2).  They are the same
statement about the same object at the same position:

> at every raw-Θ0-flexible position of `P0`, the facing guess must be within
> reach of a pre-fixed Θ-monotype — no `Δρ` binder, no `Ψ'` tag.

**And `fsh_clean` already says both** (prop_look_complete_sub_var.v:190): it
carries `ftv ψa ∩ Δρ = ∅` AND `ftag ψa ∩ Ψ' = ∅`.  So `flex_shield` is not a
sibling of `flex_apart` — it is a strictly more permissive REPLACEMENT.

### 10.2 Why the asymmetries exist, once you say it that way

| `flex_apart` | `flex_shield` | reading |
|---|---|---|
| `fa_unit`, `fa_var_rigid`, `fa_hole` | `fsh_flexfree` | three special cases of "no flexible here"; `flex_apart` never got the general rule |
| — | `fsh_rho_var` | "a `Δρ`-variable is safe opposite anything" — added to `flex_shield` because "WITHOUT this rule the premise is TOO STRONG"; the hole `cex_p7_shield_arrow.v` falls through |
| `fa_all_etag` / `fa_all_syn` (lockstep) | `fsh_all_l` / `fsh_all_r` (independent) | the algorithm descends the two sides SEPARATELY — Sub-ForallR moves `P0`, Sub-ForallL moves the guess and grows `Δρ` |
| `Δρ` a PARAMETER | `Δρ` an INDEX | `flex_apart` predates the ForallL descent that grows `Δρ` |

`flex_apart` is an earlier draft written for P6-Cv, where the ∀ descents happen
in lockstep and `Δρ` never grows.  It was never revisited when P6-Sv taught the
development that the two sides move independently.

### 10.3 The refactor

**Delete `flex_apart`, `fa_step`, `fa_walk`, `flex_apart_walk`,
`flex_apart_deep` and their ~15 lemmas; use `flex_shield` everywhere, at
`Ψ' = ∅` on the consistency side (where the tag conjunct is vacuous).**
`sub_shield`'s two conjuncts collapse to one.

- ⚠️ **Ordering constraint:** `flex_shield` currently lives in
  `prop_look_complete_sub_var.v`, which is DOWNSTREAM of `prop_look_complete_cstr.v`
  (P6-Cs) and `prop_look_complete_var.v` (P6-Cv).  It must move UP to
  `prop_look_complete.v`, where `flex_apart` lives now.
- Most consumers already have a `flex_shield_*` counterpart:
  `flex_shield_{arrow,topholeg_r,tophole_l}_inv`, `_weaken_tvar`, `_descend_r`,
  `_psi_anti`.
- ⚠️ The one that needs care is the FLEXIBLE-P0 READ-OFF
  (`flex_apart_flex_var_clean`, consumed by P6-Cs's Arrow row at
  `prop_look_complete_cstr.v:2199`).  `flex_shield` has three more ways to hold
  at a flexible `P0`: `fsh_flexfree` is IMPOSSIBLE there (a flexible variable is
  not flex-free) and costs nothing; `fsh_rho_var` gives a `Δρ`-VARIABLE guess,
  which is already a mono paint — exactly what the consumer wanted the
  cleanliness FOR; and `fsh_all_r` can fire at a variable `P0`, so the read-off
  gains a tagged-∀ arm that recurses at `add α Δρ`.  **Drafted and backed out:
  the first two arms are easy, the `fsh_all_r` arm is what makes the read-off a
  three-way disjunction rather than a two-way one.  Settle its statement before
  starting the rewiring.**
- Sanity check that must keep holding: `flex_shield Θ0 {ε} ∅ α̂ (∀^ε β. β→β)` is
  still NOT derivable — `fsh_all_r` descends to `flex_shield Θ0 {ε} {α} α̂ (α→α)`
  where `fsh_clean` fails on `α ∈ Δρ`, `fsh_rho_var` wants a bare variable and
  `fsh_arrow` wants an arrow `P0`.  That is `cex_p6sv_forall_flex.v`, and the
  merged predicate must keep excluding it.

### 10.4 CORRECTION — the merge is wrong; the BASE rows must agree, the DESCENTS must not

Attempting §10.3 immediately hit the reason the two predicates differ, and it is
a real one.  **P6-Cv descends CONSISTENCY, which matches ∀s in LOCKSTEP**
(`fa_all_etag` / `fa_all_syn`, Δρ FIXED); **P6-Sv descends SUBTYPING, which
INSTANTIATES** (`fsh_all_r`, Δρ GROWS).  `flex_apart_all_etag_forall_inv` reads
the lockstep child off at the SAME Δρ, and only `fa_clean` and `fa_all_etag` can
conclude at a ∀/∀ node — an `fsh_all_r`-style row would also conclude there, give
the child at `add α Δρ` with `P0` UNOPENED, and the inversion would break.  That
inversion is load-bearing for P6-Cv.  **So the descent disciplines genuinely
differ, mirroring how the two judgments descend, and must stay different.**
`Δρ` being a PARAMETER of one and an INDEX of the other is that same fact, not an
oversight.

**What must agree is the BASE rows** — they say the same thing about the same
hazard (§10.1) — and `flex_apart` is missing two:

- **`fa_flexfree`** — nothing to keep apart when the payload has no raw
  Θ0-flexible.  `fa_unit` / `fa_var_rigid` / `fa_hole` are three special cases;
  the general rule was never written.
- **`fa_rho_var`** — a ρ-replaced rigid variable is safe opposite ANY payload.
  This is P6-Cv's own leaf, and `flex_shield` states it as `fsh_rho_var`.

Neither disturbs the lockstep inversions: `fa_flexfree` re-applies at any
sub-payload (flex-freedom is inherited), and `fa_rho_var`'s target is a bare
variable, which every ∀ / arrow inversion discriminates away.  Together they kill
both witnesses of `cex_p7_shield_arrow.v`.

**Status: branch `flexapart-baserules`, WIP, does not compile.**
`prop_look_complete.v` and P6-Cv are green there: `pskl_flex_free` + kit moved up
(the new row needs it in scope before P6-Cv), the two rows added, the ~6
inversions extended, `flex_apart_weaken` split into a flex-preserving form (⚠️
`fa_flexfree` reads the context NEGATIVELY, so a context weakening must also
create no new flexibles — true of every RIGID extension, which is what all five
callers do) plus a flex-prefix twin mirroring `flex_shield_weaken_flex_prefix`,
and `a_flex_tvar_strip_tvar` added.

⚠️ **BLOCKED ON** `flex_apart_flex_var_clean`, which now returns a DISJUNCTION
whose right arm is "the guess is a Δρ-variable under a ∀◈ STACK".  P6-Cs's Arrow
row (`prop_look_complete_cstr.v:2198`) consumes the old equation to obtain a MONO
PAINT `τψ`, which it needs both to build the metasubstitution entry `(α1, τψ)`
and to close precision via `ad_ppre_mono_paint_refl`.  The UN-STACKED arm is fine
(`τψ := ptyp_var_f α0`, well-formed by `rho_fresh`), but under a ∀◈ stack `ψa` is
not a mono paint and there is no precision rule for `var ⊑ᵖ topholeg`.  So
either that combination is unreachable at this call site — `a_tags_sort` at TY
forces ghost-freeness, which excludes `topholeg`, but SK does not — or the
read-off needs a different right arm.  **Settle that before continuing.**

### 10.5 VALIDATED (2026-07-30) — §10.4 was an over-correction; the merge is on

Two checks, both against code rather than reasoning.

**(a) The `guarded(P0)` side condition on the instantiating ∀ row is free.**
All EIGHT `fsh_all_r` producer sites (`prop_look_complete_sub_var.v` lines 246,
266, 283, 322, 349, 384, 482, 521) sit inside inductions over `flex_shield` —
`_delta_cong`, `_psi_anti`, `_weaken_tvar`, `_weaken_flex_prefix`, `_rename`,
`_rename_r_gen`, `_tophole_l_inv`, `_topholeg_r_inv`.  Every one RE-APPLIES the
rule while rebuilding a transported derivation, so a new side condition would
ride along from the instance being transported.  **No site builds an
`fsh_all_r` from scratch**, and the suppliers (P7's
`prop_sub_shield_supply.v`) use only `fsh_clean` / `fsh_flexfree`.  So the
condition would cost nothing.

**(b) …but it is not needed, because §10.4's objection is FALSE.**
§10.4 claimed the merge dies on `flex_apart_all_etag_forall_inv`, the LOCKSTEP
∀/∀ descent at a FIXED Δρ.  `flex_shield` already has that descent:

    flex_shield_descend_both   (prop_look_complete_sub_var.v:581, Qed)

and its own comment settles the disagreement — *"the two-sided row is not a
separate obligation: the guess's binder joins Δρ (it IS ρ-replaced from the
subtyping side's point of view) and the payload's binder is a fresh rigid of
the context"*.  It lands at `add α Δρ` and `(α ~ abind_tvar) ++ Θ0`, not at Δρ.
So `flex_apart`'s `fa_all_etag` — which holds Δρ FIXED across a matched ∀ — is
the rule that is out of step, and `flex_shield`'s reading is both stronger as a
premise and compositional.  **§10.3's conclusion stands: one predicate,
`flex_shield`.**

**And the blocker recorded in §10.4 is already solved on the `flex_shield`
side.**  `flex_shield_flex_leaf` (:603, Qed) IS the flexible-P0 read-off, and it
resolves the ∀◈-stack arm the way P6-Sv does — by carrying SHAPE side conditions
(`ψa` is neither a `uskl_all_etag` nor a `uskl_topholeg`) and handling those two
targets in their own rows of the induction.  P6-Cs would do the same.

**Coverage check — every `flex_apart` consumer already has its twin:**

| `flex_apart` | `flex_shield` |
|---|---|
| `_topholeg_target_inv` | `_topholeg_r_inv` |
| `_tophole_p0_inv` | `_tophole_l_inv` |
| `_flex_var_clean` | `_flex_leaf` (shape side conditions) |
| `_arrow_inv` | `_arrow_inv` |
| `_weaken` | `_weaken_tvar` / `_weaken_flex_prefix` |
| `_all_etag_forall_inv` | `_descend_both` (at `add α Δρ`) |
| `_guarded_all_etag_descent` | `_descend_r` |
| `_tophole_all_etag_descent` | `_descend_r` ∘ `_tophole_l_inv` |

**Remaining work, in order:** (1) move `flex_shield` + `pskl_flex_free` + kit up
to `prop_look_complete.v` (P6-Cv/P6-Cs are upstream of where they live);
(2) rewire P6-Cv and P6-Cs to `flex_shield Θ0 ∅ Δρ P0 ψa` — ⚠️ **the one
non-mechanical part is that their ∀ rows must now land at `add α Δρ` and a Θ0
extended by the rigid**, which the ρ-machinery already tolerates elsewhere
(`a_inc_cons_tvar`); (3) delete `flex_apart`, `fa_step`, `fa_walk`,
`flex_apart_walk`, `flex_apart_deep`; (4) collapse `sub_shield` to one conjunct,
which is what `cex_p7_shield_arrow.v` demands.  Branch `flexapart-baserules` is
then superseded — its base-row patch is subsumed.

### 10.6 CLOSED (2026-07-30) — the BASE rows merged, the DESCENTS kept apart

The oscillation across §10.3-§10.5 came from conflating **same notion** (true)
with **same inductive definition** (false).  Executing the merge settled it in
one line of evidence: `flex_apart`'s `fa_all_etag` descends a matched ∀ at a
**fixed** Δρ, while `flex_shield_descend_both` descends it at **`add α Δρ`**.
Neither implies the other, so a merge means reproving P6-Cv's whole ∀/ρ
threading.  They are two sound approximations of one condition, each closed
under a different recursion — consistency MATCHES ∀s, subtyping INSTANTIATES
them — and that difference is real.

**What must agree is the BASE rows, and `flex_apart` was missing two.**  Landed:

- **`fa_flexfree`** — nothing to keep apart when the payload has no raw
  Θ0-flexible.  `fa_unit` / `fa_var_rigid` / `fa_hole` were three special cases.
- **`fa_rho_var`** — a ρ-replaced rigid variable is safe opposite ANY payload;
  P6-Cv's own leaf, which `flex_shield` had stated as `fsh_rho_var` all along.
- **`fa_topholeg_t` DELETED.**  With `fa_rho_var` present it was the only way a
  guard could hold at a ∀◈ that is neither clean nor flex-free, and it produced
  a "∀◈-stack over a Δρ-variable" that no consumer can use.  Every producer was
  a transport re-applying it, never a consumer building one, and the direction
  that IS used (`flex_apart_topholeg_target_inv`, stripping a ∀◈ off the target)
  still holds.

**Three knock-ons, each with the same shape and the same fix.**

1. `fa_flexfree` reads the context NEGATIVELY, so **context weakening must also
   create no new flexibles** — true of every RIGID extension, which is what all
   the callers do (`a_flex_tvar_strip_tvar`).  A FLEXIBLE prefix needs the
   ftv-scoped twin instead.
2. That twin needs the walk's endpoint to miss `dom Ξ`, so **`p0_walk` and
   `fa_walk` both gained an AVOID SET**, exactly as `ss_walk` already had —
   `ss_step`'s own comment had diagnosed this ("without that the walk reaches
   states mentioning an ARBITRARY γ, and the transport could then not be done at
   all").  New: `p0_walk_mono` / `p0_walk_ftv` / `fa_walk_mono` / `fa_walk_ftv`
   and the two `*_weaken_flex_prefix` transports.
3. `flex_apart_flex_var_clean` is now a **two-way read-off** (clean, or the
   guess IS a Δρ-variable), mirroring `flex_shield_flex_leaf`.  P6-Cs's Arrow
   row consumes the new arm by the route `fsh_rho_var`'s comment describes: the
   precision premise **forces `Pi` to be that very variable**
   (`ad_ppre_delta_var_inv` + `msubst_pskl_var_inv`), so SolE-Var keeps it, the
   output is `Pa = α0` rather than the fresh `α1`, and `α1`'s image is then
   unconstrained — `⟨⟩` serves, and `⟨⟩` IS Δρ-clean where `α0` would not have
   been.

**`cex/cex_p7_shield_arrow.v` is now REFUTED, as intended,** and has become
`cex/regr_p7_shield_arrow.v`: both witnesses are shielded, one by each new row.
`make coq` green from clean, 41 `Print Assumptions` closed, zero admits.

---

## §12 P7c — the DISPATCHER, scoped (2026-08-02)

P7b's seven row lemmas are all `Qed` and axiom-free; what is missing is the
bundle that assembles them, `a_sub_complete` (algorithmic.tex:1446),
referenced in prop_sub_complete_thm.v's roadmap but never written — the file
ends after the seventh row.  This is the scoping, done against the tree.

### The dispatch is on the JOIN, and it has TWELVE cases, not seven

Every row lemma has the same interface:

```coq
Lemma a_sub_complete_<row> : forall n <row args>,
  (forall NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q',
     sub_complete_concl n NM' M' Θ0' P0' P' R'' T'' Ψ' Θ' κ' Q') ->  (* IH at fuel n *)
  <premises read off the join's last rule> ->
  sub_complete_concl (S n) …
```

so the dispatcher inverts `ad_pat_sub_gv` and delegates.  `ad_pat_sub_gv`
(def_decl_algo_sub_hyg.v:143) has **twelve** constructors:

| join constructor | dispatch |
|---|---|
| `__infer`, `__check`, `__univ_ghost_r`, `__ghost`, `__ghostg` | leaf rows, `Qed` |
| `__arrow`, `__forall_r`, `__forall_l_tagged`, `__forall_l_untagged` | recursive rows, `Qed` |
| `__univ_ghost_l`, `__univ_ghost_lg` | **no row lemma exists** — short inline IH applications wrapping `a_sub__univ_ghost_l` / `_lg` |
| `__flex_mono` | **P7a**, the flex half |

### ⚠️ The induction cannot be a plain one on the fuel

`__univ_ghost_l`, `__univ_ghost_lg` and `__flex_mono` conclude at fuel `n`, not
`S n` — they do not consume fuel, and they do not shrink `Ψ` either, so
lex(fuel, |Ψ|) does not decrease on them.  What does decrease is the JOIN
DERIVATION.  So the dispatcher is two nested inductions:

- outer: strong induction on the fuel `n` (`lt_wf_ind`), which is what feeds the
  row lemmas their `sub_complete_concl n` argument at a conclusion of `S n`;
- inner: structural induction on `ad_pat_sub_gv n …`, which handles the three
  fuel-preserving rules.

At fuel 0 only the leaves and the three fuel-preserving rules can fire, so the
inner induction covers it with no separate base case.

### What the dispatcher must RECOVER, and what it must be GIVEN

The join fixes `R'` and `Q`; the row lemmas are stated at the *subject* `R` too,
related only by the ≡ᵘ slack `Θ ⊢ R' ≡ᵘ msubst_uskl_syn κ R`.  So each case owes
a shape transfer from `R'` to `R`.  The kit is partial
(prop_sub_msubst_equiv.v): `a_uskl_tyequiv_arrow_arrow_inv`, `_all_syn_inv`,
`_all_etag_inv`, `_hole_l_inv`, `_holeg_l_inv`, `_mono_r_inv` exist and are
stated in the direction the rows already use; the dispatcher needs the
complementary "`R'` has shape X ⟹ `κR` has shape X" direction, which is where
the flexible case splits off (`κα̂` may be an arrow while `R` is a bare `α̂` —
that is exactly `__flex_mono` ⇒ P7a).

⛔ **THE BLOCKER, and it is pre-existing.**  Both ForallL rows demand
`sub_shield Θ0 Ψa empty P0 ψa` as a premise, and the join does NOT supply it.
`sub_shield` is TASK 0, and prop_sub_shield_supply.v closes it only for a
RESTRICTED `P0` — `sub_shield_flex_free`, `sub_shield_atomic`,
`sub_shield_supply_mono_counterpart`, and the inh-free counterpart — leaving
open exactly the case of a `P0` carrying a `∀` below its head.  So P7c cannot
be closed unconditionally today: the dispatcher can be written and every other
case discharged, but the two ForallL cases must either take the shield as a
hypothesis or wait for TASK 0's residual.  The two ForallL rows also need
`(guarded_pskl P0 \/ P0 = pskl_hole)` and, at `NM = TY`, the subject's
ghost-freeness — both of which have to be derived from the mode-compatibility
premises and the fill rather than read off the join.

### ⚠️ §12.1 CORRECTION (2026-08-03): the induction above is WRONG, and the
### case map, measured against the tree

`prop_sub_complete_dispatch.v` §1 (Qed, axiom-free) is the SHAPE TRANSFER the
dispatcher owes, and §2 records the scoping below.

**The case map.**  What the join does not fix is the motive's unresolved
subject `R` — only the ≡ᵘ slack `Θ ⊢ R' ≡ᵘ κR` ties them.  `msubst_uskl_syn` is
structural except at a free variable, where it installs a MONOTYPE PAINTING,
and a painting is `unit` / a variable / an arrow — never a ∀, never a ghost.
So the transfer is TOTAL at every row except `__arrow`:

| join row | subject `R` | dispatch |
|---|---|---|
| `__infer` `__check` `__univ_ghost_r` `__forall_r` | arbitrary | the row lemma does its own transfer |
| `__ghost` `__ghostg` | `◇` / `◈` | the row lemma takes `R'` directly |
| `__arrow` | an ARROW **or a VARIABLE** | arrow ⟹ `a_sub_complete_arrow`; variable ⟹ **the only entry into P7a** |
| `__forall_l_{tagged,untagged}` | the same ∀ | the two ForallL rows (each owes `sub_shield`) |
| `__univ_ghost_l` `__univ_ghost_lg` | the same ghost | **no row lemma** — strip with `a_sub__univ_ghost_l`, recurse |
| `__flex_mono` | unchanged | a pure PEEL (chase the Θ-definition; re-establish the slack by `flex_def_paint_tyequiv` + trans) |

The arrow row's variable escape needs `unit` excluded, and that is not
syntactic: `Θ ⊢ arrow ≡ᵘ unit` dies only through ⇓ (`a_tyequiv_downarrow` is a
congruence and `⇓(A→B)` is an arrow).  `a_uskl_tyequiv_arrow_l_inv` is that
argument.

**⚠️⚠️ THE TERMINATION IS NOT lex(fuel, |Θ0|).**  The two halves call each other
at the SAME fuel: `a_sub__flex_mono` enters P7a at the same context, and P7a's
`Flex-Solve` re-enters P7b at the same fuel with a context TWO ENTRIES LARGER —
it deposits `α̂0 ≔ α̂→β̂` plus the two fresh flexibles
(prop_sub_complete_thm.v:4586).  So on that cycle neither component decreases.
(`Flex-Assign` is fine: it consumes the definition, so the context shrinks by
one.)

⭐ **What breaks the cycle is the SUBJECT.**  Flex-Solve re-enters at the
subject `α̂ → β̂` — an ARROW — and a main call at an arrow subject can never come
back into P7a: the escape needs a VARIABLE subject, and no join row shrinks an
arrow to a variable (`__univ_ghost_l` needs a ∀◇ subject; `__flex_mono` leaves
`R` alone).  The layering that works is

1. `main_arrow_subject` — the main half at an ARROW subject, from the fuel IH
   ALONE: no P7a, no context induction;
2. the flex half at `|Ξ ++ Θ0| = k`, by an inner induction on `|Θ0|`
   (Flex-Depend keeps the total and shrinks Θ0), using (1) for Flex-Solve and
   the main half at `k-1` for Flex-Assign;
3. the main half at `k`, using (2) for the R-variable escape and the fuel IH
   for the fuel-consuming rows; its inner induction on the join handles the
   three fuel-preserving ones;
4. strong induction on `k`, then on the fuel.

**⭕ THE STUCK-CHECK IS NOT CONSISTENCY'S, AND IT IS THE PIECE TO BUILD FIRST.**
A rigid head `β` with `β ∈ ftv P0` matches no `a_sub_flex` rule (it cannot enter
Ξ — `a_decls` holds only flexible declarations — and `Flex-SkipRigid` needs
`β ∉ ftv P0`), so the dispatcher must refute it from the solution.
Consistency's twin (`assign_complete_step`'s rigid-head case,
prop_consis_complete.v:5000-5090) runs `rigid_survives_solution` then
`ad_pat_consis_rigid_ftv_rev_scoped`, because THERE the pattern IS the join's
subject.  ⚠️ Here `P0` sits on the FILL side (`Θ ⊢ᵣ inh{κP0} ⊳ Q`) and the
join's subject is `κα̂`, so the chain is

    β ∈ ftv P0 ⟹ β ∈ ftv (κP0) ⟹ β ∈ ftv Q ⟹ β ∈ ftv (κα̂)

whose last step is "the SUBJECT confines the TARGET" — FALSE for the join in
general (`ad_pat_sub_gv__ghost` gives a ◇ subject an arbitrary target).  It has
to be re-derived for the MONOTYPE subject the walk actually has, where every
row carries a refinement premise off the subject's HOLE-FREE erasure and the
target therefore cannot invent free variables.

### Recommended order

1. the ten non-ForallL cases (nine delegations + the two inline univ-ghost-l
   rows), with P7a taken as a hypothesis — this is self-contained and closes
   most of the dispatcher;
2. the ≡ᵘ shape-transfer lemmas each case needs, added to
   prop_sub_msubst_equiv.v;
3. the ForallL cases, gated on TASK 0's residual;
4. P7a itself, which needs the `a_sub` / `a_sub_flex` run-renaming kit (K1–K4)
   to discharge the walk's three `β ∉ dom Θ1` premises (algo/def_extra.v
   :1100/:1116/:1123).

## §13 P7a — what the walk rows actually cost (measured 2026-08-02, against the tree)

§12's item 4 ("P7a itself, which needs the run-renaming kit K1–K4") is now
half-executed and half-corrected.  The swap kit was sufficient for the half it
was built for; the other half is a different problem.

### The rows split THREE ways, not two

| row | where its IH lives | status |
|---|---|---|
| `Flex-Depend` | this motive, same context up to `++`-assoc | **Qed** |
| `Flex-Skip` | this motive, at the stripped context, SAME target Θ | **Qed** |
| `Flex-SkipRigid` | this motive, at the stripped context, TRUNCATED target Θ' | blocked, see below |
| `Flex-Assign` | **the P7b motive** (`sub_complete_concl`) at fuel ≤ n | open |
| `Flex-Solve` | **the P7b motive** at fuel ≤ n | open |

`Flex-Assign` re-enters the MAIN judgment with the substituted subject
`α̂[τ/β̂]` — for `β̂ = α̂` that is the bare monotype τ, not a variable — so it is a
cross-half row exactly like `Flex-Solve`, and neither takes
`sub_flex_complete_concl` as its IH.  Only the three walk-internal rows do.

### Why `Flex-Skip` works and `Flex-SkipRigid` does not: `a_inc` is POSITIONAL

`a_inc__flex` / `a_inc__flex_def` hold the target FIXED
(`κ ∷ Θ ⊑ Θ'  ⟹  ((α,τ)::κ) ∷ ((α ~ flex) ++ Θ) ⊑ Θ'`), so stripping a flexible
entry out of the middle of the source leaves `κ' ∷ (Ξ ++ Θ0) ⊑ Θ` at the SAME Θ
— and every other premise of the motive (the join, the fill, wf of Θ, the ≡ᵘ
slack) is stated at Θ and therefore transports verbatim.  That is the whole
reason the discharge pattern is short:

1. peel around the mid entry (`a_inc_strip_flex_mid`);
2. feed the IH;
3. pick β1 fresh;
4. junk-swap the IH's run (`a_sub_flex_swap_junk`) and re-attach with
   `swap_junk_dom_out` — this is the Barendregt premise, discharged;
5. rebuild the package as `(β, κ's β-image) :: kswap_msubst β β1 ζ`, via
   `a_inc_kswap` / `msubst_compose_kswap_id` + `msubst_compose_head_id` /
   `msubst_bskl_head_notin` + `msubst_bskl_kswap_paint`.

`a_inc__tvar` breaks step 1.  `κ ∷ (Ξ ++ (β ~ tvar) ++ Θ0) ⊑ Θ` forces
`Θ = Ξv ++ (β ~ tvar) ++ Θ'` with `a_suffix Ξv` and `κ' ∷ Θ0 ⊑ Θ'`
(`a_inc_tvar_inv`).  The IH's target is therefore Θ', and `κ' ∷ Θ0 ⊑ Θ` is
FALSE — not merely unproved — as soon as Θ0 carries a rigid or a term entry,
since `a_inc__tvar` / `a_inc__var` admit only an `a_suffix` above the matching
target entry and Θ has `β ~ tvar` sitting there.  So the row needs the
⇓-truncation apparatus, which is precisely what the consistency walk's own
`Assign-SkipRigid` already pays (`a_inc_self_downarrow`,
`join_pskl_downarrow_mono_scoped`, prop_consis_complete.v:4930-5153) — lifted
from `ad_pat_consis` to `ad_pat_sub_gv`.

### `sub_flex_complete_concl` is missing `dom Ξ [<=] ftvar_in_pskl P0`

The consistency motive has it (`assign_complete_at`,
prop_consis_complete.v:2249); the subtyping one does not.  It is load-bearing at
`Flex-SkipRigid` and only there: Ξ sits ABOVE β in the source, so a solution may
map a Ξ-flexible `γ̂` to the skipped rigid β, and the rule re-attaches β at the
TOP of the output (`Θ1, β`), where Θ1's flexibles are scoped BELOW it — so no ζ
over the output can reproduce `γ̂ ↦ β`.  With the invariant, `γ̂ ∈ ftv P0`, and
the chain "β ∈ ftv (κ P0) ⟹ β ∈ ftv Q (fill) ⟹ β ∈ ftv (κ α̂) (join, monotype
subject) ⟹ contradiction with `κ α̂` scoped below β" closes the hole — the last
step being the subtyping twin of `ad_pat_consis_rigid_ftv_rev_scoped`.  The
invariant is supplied at `a_sub__flex_mono` (Ξ = ·) and preserved by every walk
row, so the dispatcher can pay for it.

The same place owes a STUCK-CHECK: with a rigid head and `β ∈ ftvar_in_pskl P0`
NO rule applies, so the row must refute that configuration from the solution
(`rigid_survives_solution`'s twin).

### Order for the rest of P7a

1. add `dom Ξ [<=] ftvar_in_pskl P0` to `sub_flex_complete_concl` and re-close
   the two Qed rows (they do not use it, so this is mechanical);
2. lift `ad_pat_consis_rigid_ftv_rev_scoped` / `join_pskl_downarrow_mono_scoped`
   to `ad_pat_sub_gv`; then `Flex-SkipRigid` and its stuck-check;
3. the two cross-half rows, against the P7b motive;
4. the dispatcher (§12).

## §14 TASK 0's residual — the falsity half is SETTLED (2026-08-02)

`cex/cex_p7_shield_forall_flex.v` (Qed, axiom-free) machine-checks the half of
the probe that does not depend on realizability:

    flex_shield Θ0 Ψ' Δρ α̂ (∀^ε β. β→β)             is UNDERIVABLE   (α̂ flexible, ε ∈ Ψ')
    sub_shield  Θ0 Ψ' ∅ ((∀γ.γ) → α̂) (∀^ε β. β→β)   is UNDERIVABLE

The leaf is stuck structurally: `fsh_clean` is blocked by the tag,
`fsh_flexfree` by the flexible, and `fsh_all_r` only descends into `α → α` at
`add α Δρ`, where `fsh_clean` is blocked by α itself and every congruence by a
shape mismatch (P0 is a variable, ψa an arrow).  The second statement follows
because `ss_walk` reaches the codomain in one `sss_arrow_r` step and
`sub_shield` demands the shield at EVERY walk-reachable `P0`-part against the
WHOLE fixed `ψa`.

So the residual `P0` (a ∀ below the head) is not merely unproved — where it also
carries a walk-reachable raw flexible, the shield is **false**, and the ∀-free
supply route cannot be stretched to cover it: with a ∀ inside `P0`, `κP0` carries
a ∀, the fill may emit a `bskl_all_inh`, `Q` stops being `bskl_inh_free`, and
`ad_pat_sub_g_inh_free_tag_free` no longer collapses `Ψa` to ∅.

**What is still open is REALIZABILITY**: whether P7b's Sub-ForallL rows can be
reached with that `(P0, ψa)` pair and `ε ∈ Ψa` — i.e. whether the ambient join
`ad_pat_sub_gv n NM M (Ψ ∪ Ψa) Θ (open Rj ψa) Q` and fill
`Θ ⊢ᵣ inh{κP0} ⊳ Q` are jointly inhabited there.  That is the next step, and it
is now a bounded question with a named witness rather than an open search.

If it IS realizable, the conclusion is **not** that P6-Ss is false but that
`sub_shield` is over-strong.  It is indexed NON-POSITIONALLY — every
walk-reachable `P0`-part against the whole guess — while the derivation aligns
`ψa` with ONE position (here the domain, facing the inherited ∀ of `Q`, where its
tag is legitimately solved).  The repair is a positional re-indexing, replayed
through P6-Ss and P7b's two ForallL rows, which consume the current shape.
Nothing goes to PAPER-GAPS.md: `sub_shield` is a mech-invented repair premise,
not a paper statement.

⚠️ **There is no cheap escape by trimming the definition.**  The `ss_walk`
closure is not gratuitous: P6-Ss's Sub-Arrow row consumes it directly —
`prop_look_complete_sub_cstr.v:1546-1548` builds `sub_shield (Ξc1 ++ Θ0) Ψ' Δρ
P02 ψa` for the codomain via `sub_shield_step … sss_arrow_r`, because P6-Ss
solves ONE flexible against a FIXED guess while walking `P0`.  So weakening the
definition breaks the Qed consumer, and the repair really is a re-indexing
(pairing each walk position with the part of ψa the derivation aligns there),
replayed through P6-Ss and P7b's two ForallL rows.  That is why settling
REALIZABILITY first is worth it: it is one bounded instance, and it decides
whether any of that work is needed at all.

### §14.1 SETTLED (2026-08-03): the residual IS REALIZABLE — `sub_shield` is over-strong

`cex/cex_p7_shield_realizable.v` (Qed, axiom-free) exhibits the configuration
and machine-checks every part of it.  The witness is

    Θ0 = α̂ ,  κ = α̂ ↦ unit ,  Θ = Θ0
    P0 = (∀γ. γ→γ) → α̂        a ∀ BELOW the head AND a walk-reachable raw flexible
    R  = ∀^t. (□₀ → unit)      the subject: one tagged ∀
    ψa = ∀^e β. β→β            the guess — TAGGED, with a COMPOUND body
    Q  = (∀ᵢ. β→β) → unit      the counterpart

and the file proves, at that configuration: the whole completeness input
(wf of `Θ0` / `P0` / `P` / `⌊Q⌋`, `skmod[TY]{P0}{FN TC}`, `guarded P0`,
`ghost-free R`, `⌊R⌋ˢ = P`, `κ ∷ Θ0 ⊑ Θ`, the `≡ᵘ` slack), the JOIN
(`ad_pat_sub_gv 2` ending at `__forall_l_tagged` with exactly this `ψa`, its
`a_tags_sort` / disjointness / wf side conditions, and the sub-join), the FILL
(`ad_refine_syn_f ∅ Θ ∅ inh{κP0} Q`) — and `~ sub_shield Θ0 {e} ∅ P0 ψa`.

**Why it goes through, and why the obvious probe does not.**  The tag `e` has
exactly ONE way to be discharged — `ad_pat_consis__forall_inh_tagged`, a
tagged ∀ in the subject facing an INHERITED ∀ in the counterpart — and the
counterpart is pinned by the FILL, so `Q`'s inherited ∀ can only come from a ∀
in `P0` (κ's images are monotypes; `__hole` / `__tophole_fill` emit
`bskl_all_syn`, not `_inh`).  Its BODY is therefore whatever `P0`'s ∀-body
refines to.  With `P0 ⊇ ∀γ.γ` that body is a bare variable and a compound
guess is stuck; with `P0 ⊇ ∀γ.γ→γ` it is an arrow and the guess goes through.
So the residual is realized by the SAME shape that makes the shield false.

**And the dispatcher has no way around it**: `join_at_Rw_is_forall_l` shows the
join at that node can only have ended with `__forall_l_tagged` (`__infer` wants
`mode_ti`; `__check` / `__univ_ghost_r` want a GUARDED subject and a ∀ is not;
`__forall_r` / `__univ_ghost_r` want a ∀-inh / tophole counterpart and this one
is an arrow; every other row wants another subject shape).  So P7c must apply
the ForallL row there, and its `sub_shield` premise is false.

**Conclusion.**  `sub_shield` is over-strong, exactly as §14 predicted: it is
indexed NON-POSITIONALLY.  The repair is a positional re-indexing — pair each
`ss_walk` position with the part of `ψa` the derivation aligns there — replayed
through P6-Ss and P7b's two ForallL rows.  Nothing goes to PAPER-GAPS.md
(`sub_shield` is a mech-invented repair premise, not a paper statement), and
neither P6-Sv nor P6-Ss is refuted: both remain `Qed` at the current premise,
which is merely stronger than it needs to be.

⚠️ Trimming the `ss_walk` closure is still not an option (§14): P6-Ss's
Sub-Arrow row consumes it directly (prop_look_complete_sub_cstr.v:1546-1548).

### §14.2 SCOPING THE REPAIR (2026-08-03): it is NOT local to `flex_shield`

`sub_shield` bundles TWO closures, and the same witness kills BOTH — so a
positional re-indexing of `flex_shield` alone does not unblock P7c.

- **the `flex_shield` half** fails at the CODOMAIN (`sss_arrow_r` pairs the raw
  flexible `α̂` with the WHOLE guess).  ⭐ At the ROOT it is DERIVABLE —
  `fsh_all_r` opens the guess into `α→α` at `add α Δρ`, `fsh_arrow` splits it
  against `P0 = (∀γ.γ→γ) → α̂`, and both sides close by `fsh_rho_var`.  So the
  defect really is the pairing, not the shape.
- **the `flex_apart_walk` half** (`apart_w_fails`, Qed) fails already at the
  ROOT, because `fa_walk` MIXES a P0-only descent (`fastep_p0_arrow_r` — the
  step P6-Cs needs, since it walks `P0` with the guess FIXED) with a step that
  GROWS Δρ (`fastep_all_r`, Sub-ForallL opening the guess).  Two steps reach
  `(α̂, β→β)` at `β ∈ Δρ`, where `fa_clean` is blocked by β, `fa_flexfree` and
  `fa_var_rigid` by the flexible, and every congruence by a shape mismatch.

⚙ **What keeps this from spreading further.**  What P6-Ss actually hands P6-Cs
is `flex_apart_deep` — the P0-only `p0_walk` closure at a FIXED Δρ — and that one
is TRUE here (at Δρ = ∅ with a closed guess, `fa_clean` discharges every
position).  So P6-Cv / P6-Cs are NOT themselves implicated; the defect is
exactly `fa_walk`'s mixing of a Δρ-growing step with a guess-fixed P0 descent.

**The shape of the repair.**  Index both closures by the SUBJECT and the
looked-for variable — data P6-L and P6-Ss already carry (`R'`, `α`) — and demand
the premise only at positions the guess can actually reach:

    Definition sub_shield Θ0 Ψ' Δρ α P0 R ψa : Prop :=
      forall P0' R' Δρ', ss_walk (dom Θ0) P0 R P0' R' ->
        Δρ [<=] Δρ' -> Δρ' ∩ ftvar_in_uskl ψa [<=] Δρ ->
        α `in` ftvar_in_uskl R' ->              (* ⇐ THE POSITIONAL GUARD *)
        flex_apart_walk Θ0 Δρ' P0' ψa /\ flex_shield Θ0 Ψ' Δρ' P0' ψa

with `ss_step` stepping `(P0, R)` in lockstep — six forms, one per P6-Ss row
that moves either component: `sss_arrow_r` (both), `sss_all` (P0 only,
Sub-ForallR), `sss_forall_l_{syn,etag}` (R only), `sss_univ_ghost_l{,g}` (R
only).  ⭐ The guard is FREE at the only place the shield half is consumed:
P6-Ss's LS-Var row, where `R' = uskl_var_f α` (prop_look_complete_sub_cstr.v
:661-684 — the ONLY `sub_shield_here` that takes the `flex_shield` conjunct;
:994 and :1482 take the apart half alone).  And it kills the witness exactly:
after `sss_arrow_r` the subject is `unit`, so no obligation is raised at `α̂`.

The `sub_shield'` prototype (definition + `ss_step'` / `ss_walk'` +
`ss_walk'_mono` / `_ftv` + all five transports `_here` / `_step` / `_add_fresh`
/ `_weaken_tvar` / `_weaken_flex_prefix`) is written and compiles clean, so the
re-indexing itself is mechanically routine.

### ⚠️ §14.3 CORRECTION (same day): the guard alone is NOT enough — `fa_walk` is implicated

§14.2's blast-radius claim above ("`prop_look_complete.v` is NOT touched") is
**WRONG**, and `apart_w_fails` is what refutes it.  The positional guard is
SATISFIED at the root (`α ∈ ftvar_in_uskl (α → unit)`), so the root obligation
is still raised — and its `flex_apart_walk` conjunct is exactly what
`apart_w_fails` shows to be FALSE.  Guarding `sub_shield` therefore fixes the
`flex_shield` conjunct and leaves the `flex_apart_walk` one broken.

The culprit is inside `fa_walk` itself: `fastep_p0_arrow_l` / `fastep_p0_arrow_r`
descend `P0` with the guess FIXED — they exist for P6-Cs, which walks `P0`
against a fixed guess — and composing one of them with `fastep_all_r` (Sub-ForallL
opening the guess, which GROWS Δρ) reaches `(α̂, β→β)` at `β ∈ Δρ`, where nothing
applies.  P6-Sv demands `flex_apart_walk Θ0 Δρ P0 ψa` in that full closure
(prop_look_complete_sub_var.v, the premise marked "P6-Cv's invariant, ALONG THE
WALK"), so the closure cannot simply be weakened at the `sub_shield` end.

**Hand-verified (NOT yet machine-checked), and the next thing to settle:**
without `fastep_p0_arrow_{l,r}` the witness IS satisfiable — with the guess a ∀,
`fap_arrow_r` cannot fire at the root (it needs BOTH sides to be arrows), so
`(Δρ, α̂, ψa)` is never reached and neither is `(Δρ, α̂, β→β)`; every reachable
triple is discharged by `fa_clean` (closed guess) or `fa_rho_var` (the guess is a
Δρ-variable).  If that holds, the repair splits `fa_walk` in two — the
POSITIONAL closure P6-Sv demands (no guess-fixed P0 descent) and the P0-only
`flex_apart_deep` P6-Cs already uses separately (and which is TRUE at the
witness) — and `prop_look_complete.v` IS in the blast radius after all.

**Corrected blast radius**: `prop_look_complete.v` (`fa_step` / `fa_walk` split
+ their transports — this is the deep one, it rebuilds the algo tail),
`prop_look_complete_sub_var.v` (P6-Sv's premise), `prop_look_complete_sub_cstr.v`
(`sub_shield` + 6 transports + P6-Ss's two statements + ~14 call sites),
`prop_look_complete_extract.v` (P6-L ×2), `prop_sub_shield_supply.v`,
`prop_sub_complete_thm.v` (P7b's two ForallL rows), and three cex files.

### §14.4 The Part-A prototype, verbatim (compiles clean, 2026-08-03)

Developed against the installed `.vo`s, so it needs no tree rebuild; NOT
committed as Coq source because it is dead code until §14.3's Part B is
settled.  Drop it into a scratch file with the header
`Require Import`s of `prop_look_complete`, `prop_look_complete_sub_var`,
`prop_look_complete_sub_cstr` (plus the usual `notations` / `def_extra` /
`coercions` / `predicates` / `decl.def_extra` / `algo.def_extra` /
`algo.def_meta` / `def_tags`) and `Set Implicit Arguments`.

⚙ Two things the prototype had to get right, both recorded at their sites:
`sub_shield'` is a `Definition`, so `apply H` does NOT unfold it — apply it to
its three explicit arguments (`apply (H P1 R1 Δρ')`); and every `ss_walk'_mono`
instance must be PINNED by a named `assert`, because inline its `A'` is still an
evar when the `[<=]` side goal runs and an evar-`fsetdec` does not terminate.

```coq
(* ===================================================================== *)
(*  THE POSITIONAL RE-INDEXING (DESIGN §14.2)                             *)
(*                                                                        *)
(*  The walk steps [P0] and the SUBJECT in lockstep, and the premise is    *)
(*  demanded only where the looked-for [α] — hence the guess [ψa] that     *)
(*  replaces it — actually reaches.                                       *)
(* ===================================================================== *)

Inductive ss_step' (A : atoms) (α : atom) : pskl -> uskl -> pskl -> uskl -> Prop :=
| sss'_arrow_r : forall P1 P2 R1 R2,                (* Sub-Arrow : both move *)
    ss_step' A α (pskl_arrow P1 P2) (uskl_arrow R1 R2) P2 R2
| sss'_all : forall P0 R γ,                         (* Sub-ForallR : P0 only *)
    γ `notin` A ->
    ss_step' A α (pskl_all_syn P0) R (open_pskl_wrt_pskl P0 (pskl_var_f γ)) R
| sss'_forall_l_syn : forall P0 R β,                (* Sub-ForallL : R only *)
    β <> α ->
    ss_step' A α P0 (uskl_all_syn R) P0 (open_uskl_wrt_uskl R (uskl_var_f β))
| sss'_forall_l_etag : forall P0 ε R β,             (* Sub-ForallL, tagged *)
    β <> α ->
    ss_step' A α P0 (uskl_all_etag ε R) P0 (open_uskl_wrt_uskl R (uskl_var_f β))
| sss'_univ_ghost_l : forall P0 R,                  (* Sub-UnivGhostL *)
    ss_step' A α P0 (uskl_tophole R) P0 R
| sss'_univ_ghost_lg : forall P0 R,                 (* Sub-UnivGhostLG *)
    ss_step' A α P0 (uskl_topholeg R) P0 R.

Inductive ss_walk' (A : atoms) (α : atom) : pskl -> uskl -> pskl -> uskl -> Prop :=
| ssw'_refl : forall P0 R, ss_walk' A α P0 R P0 R
| ssw'_step : forall P0 R P1 R1 P2 R2,
    ss_step' A α P0 R P1 R1 -> ss_walk' A α P1 R1 P2 R2 ->
    ss_walk' A α P0 R P2 R2.

(** Shrinking the avoid set admits MORE walks (only [sss'_all] reads it). *)
Lemma ss_walk'_mono : forall A A' α P0 R P1 R1,
  ss_walk' A α P0 R P1 R1 -> A' [<=] A -> ss_walk' A' α P0 R P1 R1.
Proof.
  intros A A' α P0 R P1 R1 H; induction H; intros Hsub; [ apply ssw'_refl | ].
  eapply ssw'_step; [ | apply IHss_walk'; exact Hsub ].
  destruct H;
    [ apply sss'_arrow_r
    | apply sss'_all; clear - H Hsub; fsetdec
    | apply sss'_forall_l_syn; assumption
    | apply sss'_forall_l_etag; assumption
    | apply sss'_univ_ghost_l
    | apply sss'_univ_ghost_lg ].
Qed.

Definition sub_shield' (Θ0 : aenv) (Ψ' : atoms) (Δρ : atoms) (α : atom)
  (P0 : pskl) (R : uskl) (ψa : uskl) : Prop :=
  forall P0' R' Δρ',
    ss_walk' (dom Θ0) α P0 R P0' R' ->
    Δρ [<=] Δρ' -> Δρ' ∩ ftvar_in_uskl ψa [<=] Δρ ->
    α `in` ftvar_in_uskl R' ->            (* ⇐ THE POSITIONAL GUARD *)
    flex_apart_walk Θ0 Δρ' P0' ψa /\ flex_shield Θ0 Ψ' Δρ' P0' ψa.

(* --------------------------------------------------------------------- *)
(*  The five transports, exactly the old ones plus the guard              *)
(* --------------------------------------------------------------------- *)

Lemma sub_shield'_here : forall Θ0 Ψ' Δρ α P0 R ψa,
  sub_shield' Θ0 Ψ' Δρ α P0 R ψa ->
  α `in` ftvar_in_uskl R ->
  flex_apart_walk Θ0 Δρ P0 ψa /\ flex_shield Θ0 Ψ' Δρ P0 ψa.
Proof.
  intros Θ0 Ψ' Δρ α P0 R ψa H Hα.
  apply (H P0 R Δρ);
    [ apply ssw'_refl | clear; fsetdec | clear; fsetdec | exact Hα ].
Qed.

Lemma sub_shield'_step : forall Θ0 Ψ' Δρ α P0 R P0' R' ψa,
  sub_shield' Θ0 Ψ' Δρ α P0 R ψa ->
  ss_step' (dom Θ0) α P0 R P0' R' ->
  sub_shield' Θ0 Ψ' Δρ α P0' R' ψa.
Proof.
  intros Θ0 Ψ' Δρ α P0 R P0' R' ψa H Hs P1 R1 Δρ' Hw Hle Hcl Hα.
  apply (H P1 R1 Δρ');
    [ eapply ssw'_step; [ exact Hs | exact Hw ] | exact Hle | exact Hcl
    | exact Hα ].
Qed.

Lemma sub_shield'_add_fresh : forall Θ0 Ψ' Δρ α P0 R ψa β,
  sub_shield' Θ0 Ψ' Δρ α P0 R ψa ->
  β `notin` ftvar_in_uskl ψa ->
  sub_shield' Θ0 Ψ' (add β Δρ) α P0 R ψa.
Proof.
  intros Θ0 Ψ' Δρ α P0 R ψa β H Hβ P1 R1 Δρ' Hw Hle Hcl Hα.
  apply (H P1 R1 Δρ');
    [ exact Hw | clear - Hle; fsetdec | clear - Hcl Hβ; fsetdec | exact Hα ].
Qed.

(** …and the P0-component's free variables still miss the avoid set: the
    R-only steps leave P0 alone, and the two P0 steps are the old ones. *)
Lemma ss_walk'_ftv : forall A α P0 R P1 R1,
  ss_walk' A α P0 R P1 R1 -> (ftvar_in_pskl P0) ∩ A [=] empty ->
  (ftvar_in_pskl P1) ∩ A [=] empty.
Proof.
  intros A α P0 R P1 R1 H; induction H; intros Hfr; [ exact Hfr | ].
  apply IHss_walk'. destruct H.
  - simpl in Hfr; clear - Hfr; fsetdec.
  - pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0 (pskl_var_f γ)) as Hup.
    simpl in Hup, Hfr. clear - Hup Hfr H; fsetdec.
  - exact Hfr.
  - exact Hfr.
  - exact Hfr.
  - exact Hfr.
Qed.

Lemma sub_shield'_weaken_tvar : forall Θ0 Ψ' Δρ α P0 R ψa β,
  sub_shield' Θ0 Ψ' Δρ α P0 R ψa ->
  sub_shield' ((β ~ abind_tvar) ++ Θ0) Ψ' Δρ α P0 R ψa.
Proof.
  intros Θ0 Ψ' Δρ α P0 R ψa β H P1 R1 Δρ' Hw Hle Hcl Hα.
  (* ⚙ PIN the avoid set with a named [assert]: inline, [ss_walk'_mono]'s [A']
     is still an evar when the [⊆] side goal runs, and an evar-[fsetdec] does
     not terminate. *)
  assert (Hw0 : ss_walk' (dom Θ0) α P0 R P1 R1)
    by (eapply ss_walk'_mono; [ exact Hw | simpl; clear; fsetdec ]).
  destruct (H P1 R1 Δρ' Hw0 Hle Hcl Hα) as [Hap Hfs].
  split;
    [ apply flex_apart_walk_weaken_tvar; exact Hap
    | apply flex_shield_weaken_tvar; exact Hfs ].
Qed.

Lemma sub_shield'_weaken_flex_prefix : forall Θ0 Ψ' Δρ α P0 R ψa Ξ,
  sub_shield' Θ0 Ψ' Δρ α P0 R ψa ->
  (ftvar_in_pskl P0) ∩ (dom Ξ) [=] empty ->
  sub_shield' (Ξ ++ Θ0) Ψ' Δρ α P0 R ψa.
Proof.
  intros Θ0 Ψ' Δρ α P0 R ψa Ξ H HfrP0 P1 R1 Δρ' Hw Hle Hcl Hα.
  assert (HwΞ : ss_walk' (dom Ξ) α P0 R P1 R1)
    by (eapply ss_walk'_mono; [ exact Hw | rewrite dom_app; clear; fsetdec ]).
  assert (Hw0 : ss_walk' (dom Θ0) α P0 R P1 R1)
    by (eapply ss_walk'_mono; [ exact Hw | rewrite dom_app; clear; fsetdec ]).
  assert (HfrP1 : (ftvar_in_pskl P1) ∩ (dom Ξ) [=] empty)
    by (eapply ss_walk'_ftv; [ exact HwΞ | exact HfrP0 ]).
  destruct (H P1 R1 Δρ' Hw0 Hle Hcl Hα) as [Hap Hfs].
  split;
    [ eapply flex_apart_walk_weaken_flex_prefix; [ exact Hap | exact HfrP1 ]
    | eapply flex_shield_weaken_flex_prefix; [ exact Hfs | exact HfrP1 ] ].
Qed.
```

### ⭐⭐ §14.5 LANDED (2026-08-03): Part B settled, and the repair is in the tree

`make coq` green, admit-free, axiom-free.  §14.2's prototype and §14.3's
hand-verified claim are now both machine-checked and committed; the two
sections above are kept as the reasoning record, with the corrections below.

**PART B HOLDS.**  With `fastep_p0_arrow_{l,r}` removed, `flex_apart_walk`
holds at the §14.1 witness — and the proof is a *general* closure argument, not
a witness-specific enumeration.  The invariant is

    INV Δρ P0 ψa  :=  etag_free ψa
                      ∧ ( ψa is Δρ-clean  ∨  rho_shape Δρ P0 ψa )

where `rho_shape` is the `fa_arrow`/`fa_rho_var` skeleton (arrow spine matching
P0's, every leaf a Δρ-variable).  It is closed under every surviving step:
`fastep_all_r` is VACUOUS on it (an ε-tagged ∀ is not `etag_free`), and
`fastep_flexdef_r` re-enters the clean branch because a monotype PAINTING
carries no tag (`bskl` has no ε-∀ constructor, so `ptyp_to_uskl_syn` cannot
produce one).  Only the ROOT is witness-specific: the sole step from
`(∅, P0w, ψw)` is `fastep_all_r`, landing in `rho_shape`.

**THE SPLIT.**  `fastep_p0_arrow_{l,r}` and `flex_apart_walk_p0` are deleted.
`flex_apart_deep` is now an independent `sub_shield` conjunct.

⚠️ **§14.2's guard sketch was too coarse — the guard applies to exactly TWO of
the three closures.**  `flex_apart_deep` never descends the guess, so it is
harmless at any position, and it **must stay unguarded**: P6-Ss's Check and
Arrow-left rows hand it to P6-Cs at positions where `α` does not occur at all
(P6-Ss's own premise is `α ∉ ftv P ∨ P = α`, so `α` occurs only at the LS-Var
leaf, and a guarded `flex_apart_deep` would leave those two rows with nothing).
The two closures that DO descend the guess are exactly the ones the witness
refutes, and for them the guard is free where they are consumed.  The landed
definition is

    sub_shield Θ0 Ψ' Δρ α P0 R ψa :=
      forall P0' R' Δρ', ss_walk (dom Θ0) α P0 R P0' R' ->
        Δρ [<=] Δρ' -> Δρ' ∩ ftv ψa [<=] Δρ ->
        flex_apart_deep Θ0 Δρ' P0' ψa
        /\ (α ∈ ftv R' -> flex_apart_walk Θ0 Δρ' P0' ψa
                          /\ flex_shield Θ0 Ψ' Δρ' P0' ψa)

with `ss_step` exactly §14.4's `ss_step'` (six rows, lockstep) and the five
transports as prototyped, each threading the guard through the implication.

**THE ROW MAP, as landed** (`prop_look_complete_sub_cstr.v`): LS-Var takes both
guarded conjuncts, guard discharged by `simpl; fsetdec` (`R' = α` there);
Check and Arrow-left take `flex_apart_deep` through the new `sub_shield_here_p0`;
Sub-ForallR steps by `sss_all`; Sub-Arrow-right by `sss_arrow_r` +
`_weaken_flex_prefix`; the two Sub-ForallL rows step the SUBJECT as well
(`sss_forall_l_etag` / `sss_forall_l_syn`, whose `β <> α` premise is already on
hand as `Hβα`) before `_add_fresh` + `_weaken_tvar`; the two UnivGhostL rows
gained one `sub_shield_step` each.  P6-Ss compiled first try, in 16 s.

**P7b's ForallL premise** is `forall α, sub_shield Θ0 Ψa ∅ α P0 (open Rb α) ψa`
— the subject the row hands P6-L, with the marker quantified because it is
picked inside the proof.  ⚠️ The `forall R` form is NOT available: it is
over-strong at the same witness (take `R = unit → α`, which walks the guess onto
a raw flexible it never meets).  `sub_shield_forall_flex_p0_fails` is now stated
in exactly that form and is the BOUNDARY the guard exists to respect.  Every
route in `prop_sub_shield_supply.v` is uniform in `α` and `R`, so all of them
still discharge it, with `flex_apart_deep` free from `flex_apart_deep_clean` at
Δρ = ∅.

**⭐⭐ THE DECISIVE CHECK** — `p7_sub_shield_repaired_holds`
(cex/cex_p7_shield_realizable.v, Qed, axiom-free): the repaired premise, in
exactly the form P7b's rows take, HOLDS at the configuration that refutes the
old one.  Part A kills the codomain obligation (subject `unit`, guard unmet);
Part B makes the root one true.  The same file keeps the negative evidence,
restated in terms that survive the re-indexing: the configuration is inhabited
AND both guess-descending closures fail at the CODOMAIN, one `ss_walk` step from
the root, which is precisely what the old P0-only indexing demanded.

⭕ **P7c's two ForallL cases are UNBLOCKED — but read this precisely.**  What
is removed is the FALSITY: the premise is no longer refutable, and it is
machine-checked TRUE at the node that refuted it.  What is NOT yet in the tree
is a GENERAL supply route for §9.0.2's residual shape (a `P0` carrying a ∀ below
its head).  `prop_sub_shield_supply.v` still covers only flex-free / atomic /
mono-counterpart / inh-free-counterpart / ∀-free `P0`, all now uniform in `α`
and `R`.  So the dispatcher can be written and its ForallL cases can take the
shield as a hypothesis exactly as §12 item 3 planned — the difference is that
the hypothesis is now known to be SATISFIABLE, and the positional index is the
handle a general supply proof gets to use (it need only shield positions the
guess actually reaches).  The dispatcher (§12) is next.

### ⚠️⚠️ §14.6 REFUTED AGAIN (2026-08-03, later): the positional index is STILL over-strong — the DOUBLE-OCCURRENCE witness

`cex/cex_p7_shield_double_occ.v`, all Qed, axiom-free.  §14.5's "known
SATISFIABLE" claim was true but did not settle the general supply, and the
supply question is now settled in the NEGATIVE.

**The witness is §14.1's with the marker DUPLICATED.**  Take the SAME
`Θ0 = α̂`, `P0 = (∀γ.γ→γ) → α̂`, `ψa = ∀^e β.β→β` (tagged, compound body), and
change only

    R = ∀^t.(□₀ → □₀)          the ∀-binder occurs at BOTH arrow positions
    κ = α̂ ↦ unit→unit           (so the codomain counterpart is an arrow)
    Q = (∀ᵢ.β→β) → (unit→unit)

Every hypothesis of `a_sub_complete_forall_l_tagged` other than the shield is
machine-checked inhabited (`p7_sub_shield_positional_over_strong`): the JOIN
holds because the tag `e` is still discharged at the arrow's DOMAIN — exactly
as in §14.1 — while the CODOMAIN copy of the guess is merely
ForallL-INSTANTIATED (with `unit`) against the mono-ish counterpart the fill
pins at the raw flexible, which costs NO tag (`join_cod_d`: an inner
`__forall_l_tagged` with guess `unit`, then `__check`).  And the join can only
have ended in ForallL there (`join_at_Rd_is_forall_l`).  But the shield's
subject is now `open (□₀ → □₀) α = α → α`: one `sss_arrow_r` step reaches
`(α̂, α)`, **the guard `α ∈ ftv α` is MET**, and the leaf is
`cex_p7_shield_forall_flex.v`'s stuck shape — so the premise is FALSE at every
marker (`p7_sub_shield_double_fails`), fresh ones included.

**What the guard cannot see.**  The positional index localised the demand to
the positions the guess REACHES; what it cannot express is WHAT THE DERIVATION
DOES there.  With the marker at two positions the derivation treats the two
copies of the guess DIFFERENTLY — the domain copy is MATCHED against the
inherited ∀ of `Q` (its tag solved by `__forall_inh_tagged`), the codomain
copy is INSTANTIATED against an inh-free counterpart (no tag solved) — while
`flex_shield` demands, at every guarded position, protection of the WHOLE
guess, tag included.  The failure is precisely a raw flexible paired with a
guess copy the derivation instantiates.

**Consequence for P7c.**  NO general supply of the CURRENT `sub_shield`
exists: `main_forall n` cannot be discharged through
`a_sub_complete_forall_l_tagged` as stated.  ⚠️⚠️ **Superseded by §14.7**:
`main_forall` is not merely undischargeable — it is FALSE (machine-checked,
`cex/probe_double_occ_run.v`), because at this very configuration the
algorithm has NO run at all while the join + fill are Qed-inhabited.  The
"KNOWN-TRUE `main_forall`" line below reflected the paper's claim and is
RETRACTED there.

**The repair direction the witness dictates.**  The next index must
distinguish positions by what the join does at them — MATCH vs INSTANTIATE —
and the FILL is the handle that pins it: at a raw Θ0-flexible of `P0` the
counterpart is the refinement of a monotype painting, hence `bskl_inh_free`
(`ad_refine_mono_paint_rhs_monoish` / `ad_refine_syn_inh_free`), and an
inh-free counterpart solves NO tags (`ad_pat_sub_g_inh_free_tag_free`).  So at
exactly the positions where `flex_shield`'s stuck leaf bites, the guess copy
is provably instantiated.  The open research question is what P6-Sv's LS-Var
leaf needs at an INSTANTIATED position — the current `fsh_clean`/`fsh_flexfree`
dichotomy is what must be relaxed there, and the relaxation has to be replayed
through P6-Sv → P6-Ss → P6-L → both P7b ForallL rows.  ⚠️ Note the counterpart
index cannot be bolted onto `sub_shield` alone: `flex_shield` is CONSUMED by
P6-Sv, whose statement has no fill in scope — threading the counterpart (or an
inh-free bit) through the P6 tower is the actual cost to estimate first.

### ⚠️⚠️ §14.7 THE PROBE, MACHINE-CHECKED (2026-08-03, end): `main_forall` is FALSE — the theorem over-quantifies `P0`

`cex/probe_double_occ_run.v`, all Qed, axiom-free (three `Print Assumptions`
closed).  §14.6 refuted the shield PREMISE at the double-occ node; this
settles the stronger question the premise was standing in for: **does the
algorithm run at all there?**  It does not.

**The forced trace, now a Qed lemma per step.**  At the §14.6 configuration
(`Θ0 = f̂`, `P0 = (∀γ.γ→γ) → f̂`, subject `∀.(□₀→□₀)`, `NM = TY`,
`M = fn tc`; join + fill Qed-inhabited):

1. ForallL is the only `a_sub` entry at a ∀ subject with an arrow `P0` at
   `FN(TC)` (one inversion).
2. The extract is DETERMINISTIC (`probe_extract_det`), uniformly in the
   marker and every fresh name: looksub is LS-Arrow = LE-Var + LS-Var
   (`probe_look_det`), the solve THREADS the accumulated pattern — the eq's
   yield `∀γ.γ→γ` is fed into the sub-constraint, where SS-ForallL /
   SS-Check / SE-FlexR OVERWRITE it with the flexible (`a_solve_eq__flex_r`'s
   output IS `α̂`), so the close re-binds a VACUOUS binder
   (`probe_solve_det`: output `∀_.f̂`), and the TY guess passes it through
   (`probe_guess_det`).  The vacuous binder swallows every fresh name, which
   is why determinism is name-free.
3. The continuation `(∀_.f̂) → (∀_.f̂)` vs `(∀γ.γ→γ) → f̂` forces Arrow,
   whose domain CONSISTENCY forces ForallInh; at the freshly pushed rigid
   the subject's body is the bare `f̂` facing `β1→β1` — FlexL's assignment
   walk meets the context head `β1 ~ tvar` with `β1 ∈ ftv`, where the only
   matching rule Assign-SkipRigid refuses
   (`a_assign_rigid_head_occurs_stuck`, one inversion).  Fully general:
   `a_consis_forall_arrow_vs_vacuous_var_stuck` holds for ANY context, ANY
   subject variable, ANY names.

So `probe_no_run : forall Q Θ1, ~ a_sub TY (fn tc) P0d Θ0d (∀.(□₀→□₀)) Q Θ1`.
Wiring in the motive premises (all Qed in
`p7_sub_shield_positional_over_strong`) gives `probe_motive_instance_false`,
hence `probe_main_forall_false : ~ main_forall 3` and
`probe_main_forall_hyp_false : ~ (forall n, main_forall n)`.

**What this means — SUPERSEDED SAME DAY by §14.8.**  The first reading was
that thm:complete-subtyping merely quantifies `P0` beyond the payloads the
TYPING produces (met.exe accepts `id2 idc`,
`docs/repros/thm_complete_subtyping_fn_tc_passes.mle`, because there the
collection DETERMINES the instantiation).  §14.8 shows the failing class is
REACHABLE: a payload with a raw ∀ below the head of a spine-domain AND a
fresh flexible at the codomain is built by the typing itself, and a source
program separates the systems.  The repair is NOT a fourth shield
re-indexing, and NOT a payload side condition either — see §14.8.

### ⚠️⚠️ §14.8 ~~TASK 2's VERDICT: the failing payload class is TYPING-REACHABLE~~ — **RETRACTED SAME DAY (see §14.9)**

⚠️⚠️ **The conclusion of this subsection is WRONG and is retracted in §14.9:
the declarative system REJECTS the program below too, so it is not a
separation.**  The producer analysis (facts 1 and 2) is accurate and worth
keeping; what fails is the inference from it.  Read §14.9 first.

Reading the payload invariant off the producers (HANDOFF TASK 2) appeared to
refute the premise of the planned repair instead of supplying it.

**The producers.**  Every `a_sub` payload is the ambient `a_typing`/`a_pat`
payload.  FN payloads are `arrow(P_arg, Q_amb)` built by AT-App/AP-App,
where `P_arg` is the SPINE COLLECTION's output on the argument at TC/◇ —
and the collection ghosts only the HEAD quantifiers: `a_pat` on an argument
typed `(∀c.c→c) → unit` goes SK-ForallL only at a ∀ HEAD, then
`a_sub__univ_ghost_r` keeps the guarded arrow VERBATIM under ⫯ — output
`⫯((∀c.c→c) → unit)`, the raw ∀ surviving BELOW the head (the
implementation's SI-UnivGhostR is verbatim the same, type.ml:1002).
`Q_amb` at TC can be a FRESH FLEXIBLE: when the body's collected skeleton
has ◇ at the result (a lambda-bound function applied in the body —
LE-Vacuous emits no constraint), the look's guess invents `r̂`, and the
re-check runs the body at `[tc; r̂]`, so the inner application's FN payload
is `arrow(⫯((∀c.c→c)→unit), r̂)` — the cex shape, typing-built.

**The separation.**  `pipe (fun g -> g arg)` with
`pipe : ∀r.(( ∀b.[](b→b)) → r) → r`, `arg : []((∀c.[](c→c)) → unit)`:
met.exe REJECTS (`this expression has type ˆx1 but expected
👻.(∀c.[](c→c)) → unit` — the FlexR-collapsed guess), while the
declarative side accepts (`r := (∀c.[](c→c)) → unit`, impredicatively).
CONTROL: the same program with `r` pre-instantiated concretely PASSES
(so by soundness the body's declarative check exists; decl ForallL
supplies the instantiation).  ABLATION: `arg : [](unit→unit)` PASSES —
the collapse still happens but the collapsed guess is MONO and
Assign-SolveM succeeds; the ∀ below the argument type's head is the exact
discriminator.  Repros: `docs/repros/thm_complete_subtyping_reachable_*`.

**~~Consequence for the roadmap~~ — RETRACTED, see §14.9.**

### ⚠️⚠️ §14.9 THE RETRACTION (2026-08-03, same day, co-author caught it): the declarative system REJECTS that program too — §14.8 is NOT a separation

The §14.8 program is not a counterexample: **`pipe (λg. g arg)` is
ill-typed DECLARATIVELY as well**, so met.exe's rejection is correct
behaviour and nothing goes to the authors.

**The error.**  I read `d_sub__forall_l_untagged` for a `mono_ptyp`
restriction, found none, and concluded that impredicative instantiation is
unconstrained.  The operative constraint is not monotype-ness but the TAG
obligation — the paper's *"never guess polymorphism out of thin air"*:

* `d_sub__forall_l_untagged` runs its premise at `Ψ ∪ Ψ'` with
  `d_tags Ψ' ph`, so an instantiation containing a ∀ contributes a tag ε
  the premise's derivation must PRODUCE;
* `d_consis__forall_inh_tagged` is the ONLY `d_consis` rule that puts a tag
  into Ψ, and its counterpart must be `btyp_all_inh` — an INHERITED ∀;
* `d_sub__infer` demands `Ψ [=] empty` at TI.

⟹ **a polytype instantiation must be PAID FOR by an inherited ∀ at that
position of the counterpart**, and the counterpart is what the SKELETON
supplies.  In §14.8's program the argument's skeleton is `⫯(◇ → ◇)` — no ∀
at `r`'s position — so `r := (∀c. c → c) → 1` is unpayable.  (`is_ttyp`
excludes ghosts, so no ghost-carrying instantiation evades this; and no
MONOTYPE instantiation of `b` can accept `arg` either.)  `pipe`'s `r` and
`g`'s `b` need each other's information — mutually dependent.

**The paper documents exactly this, twice (§2.9).**  *"Only flowing back and
forth once"* (third limitation) is the program structurally — `f`'s `c` is
guided by `g`'s skeleton, but `b` needs the information to flow BACK, which
\Calc allows only once; the co-author's remark is that the program becomes
typeable if `pipe`'s skeleton first flows INTO `λg. g arg`, i.e. under that
very extension.  *"Ghosts are nameless"* (second limitation) is the same
defect in `⫯(◇ → ◇)`: the ghosts lose the argument/result connection, so
the inherited information is "too coarse" to license the instantiation.

**What survives, and what reopens.**  §14.7's rule-level result is
untouched (`probe_no_run`, `probe_main_forall_false`), and that
configuration's declarative side genuinely pays its tag — `consis_d`
discharges ε against a `bskl_all_inh` counterpart at the DOMAIN — so
`join_d` is a legitimate solution and `main_forall` is really false.  What
reopens is REACHABILITY, now sharply stated: the cex needs BOTH (1) a raw
`Θ0`-flexible at the payload's codomain (algorithm has NO inherited
information there) and (2) a concrete counterpart at that codomain with the
tag paid at the domain (declarative side HAS information).  These pull in
opposite directions — the flexible arises exactly where information is
absent — and §14.8's program is the instructive near-miss: it achieves (1)
and loses (2), whereupon the declarative side rejects with the algorithm.
If the conjunction is unreachable the theorem is merely OVER-QUANTIFIED and
HANDOFF TASKS 2–3 (the payload side condition) are back ON.

**Lesson.**  Before any "decl accepts" claim, enumerate ALL the declarative
side conditions rather than the first plausible one, and consult §2.9's
limitation list — it is the authoritative catalogue of what the declarative
system deliberately rejects.  Same species as the MODE confusion of
§14.6's episode.  Full entry: docs/PAPER-GAPS.md (2026-08-03).

### ⭐⭐ §12.2 LANDED (2026-08-03): all three layers, and the two obstacles that remain

`frost/algo/prop_sub_complete_dispatch.v` is now §1–§10, 1093 lines, every
lemma `Qed` and axiom-free, <1 s to compile.  §12.1's layering is in the tree:

| layer | lemma | how it terminates |
|---|---|---|
| (a) | `sub_complete_arrow_holds` | the FUEL IH alone — no P7a, no context induction |
| (b) | `sub_flex_complete_holds` | structural on `Θ0`, `Ξ` generalized, total length bounded |
| (c) | `sub_complete_assemble` | induction on the JOIN (twelve rows) |

**THE ONE DESIGN IDEA THAT MADE (a) AND (c) ONE PROOF.**  §12.1 planned them
as separate developments.  They are not: `sub_complete_assemble` carries the P7a escape as
an ABSTRACT predicate `ESC : uskl -> Prop` on the *motive's* subject, with
three closure conditions —

```coq
(forall R0, ESC (uskl_tophole R0) -> ESC R0) ->
(forall R0, ESC (uskl_topholeg R0) -> ESC R0) ->
(forall α, ESC (uskl_var_f α) -> sub_flex_complete n Θ0) ->
```

The two tophole conditions are needed because `__univ_ghost_l` / `_lg` STRIP
the subject and can therefore EXPOSE a variable that the conclusion's subject
hid; that is why the escape cannot be phrased as a bare `R = uskl_var_f α ->
…`.  Instantiate `PIH` with a constant and you get the general dispatch;
instantiate it with `fun R => exists Rx Ry, R = uskl_arrow Rx Ry` and all
three conditions are closed by `discriminate` — an arrow is neither `∀◇` nor
`∀◈` nor a variable — so P7a is unreachable and layer (a) falls out of layer
(c) with the fuel IH alone.  **Reuse this whenever two layers of one induction
differ only in which escapes are reachable.**

**FIVE ROW-LEMMA HYPOTHESES MOVED** (prop_sub_complete_thm.v; the proofs are
otherwise untouched — each used its IH exactly once, at the guarded instance):

* `depend` / `skip` / `skip_rigid` — the walk IH gains `length Ξ' <= S (length Ξ)`.
  An unguarded `forall Ξ'` is NOT derivable under a structural induction on
  `Θ0` with `Ξ` generalized: the IH is available only at suffixes the walk can
  reach, and Flex-Depend reaches exactly one, `Ξ,β̂`.
* `assign` — the cross-half IH gains `length Θ0' <= length Ξ + length Θ0`.
* `solve` — the cross-half IH is **restricted to an ARROW subject**.  This is
  §12.1's whole point, made mechanical.

**THE STUCK-CHECK COST NOTHING NEW.**  §12.1 called it "the one research
step".  It is `a_sub_flex_complete_skip_rigid`'s steps 0–4 re-read as a
refutation: `sub_gv_bskl_downarrow_mono_scoped` (the JOIN's ⇓-confinement at a
monotype subject) composed with `refine_syn_f_downarrow_source_ftv` (the
FILL's source below its target) bounds `ftv (⇓ˢ κP0)` by `dom Θ'`, while
`rigid_survives_solution` puts `β` in it and `β ∉ dom Θ'`.  ⭐ The ⇓-FORM is
also what absorbs the motive's ≡ᵘ slack — `≡ᵗ` does not preserve ftv-scoping,
but it does preserve ⇓.  **Whenever a confinement has to survive the motive's
slack, state it on `⇓` and not on the term.**

**THE CHECK ROW's `guarded_pskl P0`** is the SOURCE-side mirror of
`ad_refine_syn_f_all_inh_r_shape`: `ad_refine_syn_f_all_inh_l_shape` says a
`bskl_all_inh` SOURCE refines only to a `bskl_all_inh` TARGET (only `__all`
and `__flex_r` have such a source, and `__flex_r`'s chain cannot bottom out —
a monotype painting is never ∀-inh).  With the Check row's guarded
counterpart that refutes a ∀-headed `P0`.

#### ⭕ The two obstacles, and why neither is mechanical

**(A2) ⚠️ THE JOIN'S LAST RULE DOES NOT DETERMINE THE ALGORITHM'S RULE.**  The
whole dispatcher is built on "invert the join, delegate to the matching row
lemma".  That correspondence FAILS at ForallL.  `a_sub__forall_l` fires on a
∀ SUBJECT and carries `(guarded_pskl P0 \/ P0 = ◇)`; `a_sub__forall_r` fires
on a ∀ INPUT.  At `NM = TY`, `M = TC` with BOTH a ∀ subject and a ∀-headed
`P0`, the join may end in ForallL while the algorithm has no choice but
ForallR — and `a_ty_mode_compat mode_tc P0` does not exclude a ∀-headed `P0`.
§8's refutation does not transfer, because it consumes the Check row's
GUARDED counterpart and ForallL's counterpart is arbitrary.  A repair needs a
JOIN-PERMUTATION lemma: from a ForallL-rooted join with a `bskl_all_inh`
target, extract the ForallR family `a_sub_complete_forall_r` consumes.
**⭐ CLOSED 2026-08-03 — see §12.4.**  It is NOT a paper defect: the paper
covers it with a one-sentence WLOG (subtyping-proofs.tex:3385).

**(B) ⛔ THE TERM-VARIABLE GAP.**  See docs/PAPER-GAPS.md.  **⭐ CLOSED
2026-08-03 — see §12.4.**  What matters for
the DESIGN is the shape of the workaround and why it does not scale: the
premise `a_sub_flex_walkable Θ0` sits on `sub_flex_complete_holds` only.  It cannot be
carried to the bundle, because the row lemmas' fuel IH is the UNRESTRICTED
`sub_complete_concl` — the restriction would have to move INTO the motive, and
then every row would owe walkability of the contexts it recurses at (Sub-Arrow
at the domain run's output, Sub-ForallL at `Ξ ++ Θ0`, Flex-Solve at the
deposited block).  Adding `Flex-SkipTmVar` is strictly the smaller change.

#### The assembly, once A and B are discharged

```coq
Theorem a_sub_complete_bundle_holds : a_sub_complete_bundle.
(* strong induction on the fuel n; inside, strong induction on |Θ0|:
     sub_complete_arrow_holds  (fuel IH)
   → sub_flex_complete_holds         (sub_complete_arrow + main at shorter contexts)
   → sub_complete_assemble         (fuel IH + sub_flex_complete_holds at Ξ = ·) *)
```

### ⭐ §12.3 Flex-SkipTmVar LANDED (2026-08-03), and what the two P7a rows cost

The authors' call was to add the missing rule, so `a_sub_flex__skip_tm_var` /
`__skip_tm_skl` are in `algo/def_extra.v` with decorated mirrors, and the three
mutual inductions over the `a_sub` / `a_sub_flex` pair carry their new cases
(prop_sub_sound.v, prop_decorate_key.v, prop_swap.v).  `make coq` green,
admit-free, axiom-free.  Each of those cases is Flex-SkipRigid's, with
`a_isub_cons_var_typ` / `_var_skl` for the increase and `a_wf_ptyp_isub` /
`a_scope_pskl_isub` for the re-attached entry's wf.

⭐ **The one thing that is NOT a premise.**  Neither the new rules nor the twin
walk's `Assign-SkipTmVar` carries `x ∉ ftv P0`, and none is needed: a term
entry is never `a_binds_tvar`, so under `uniq` no free variable of a
well-formed `P0` can be it.  Every consumer derives it in four lines
(`a_wf_pskl_ftv_tvarish` + `binds_unique`).  Do not add it to the rules.

⭕ **The two P7a completeness rows, scoped exactly.**  `a_inc__var` /
`a_inc__var_skl` shrink the `a_inc` TARGET exactly as `a_inc__tvar` does, so
each row is `a_sub_flex_complete_skip_rigid`'s ⇓-truncation apparatus
(prop_sub_complete_thm.v:6211-6576) with the tvar pieces swapped:

| SkipRigid | SkipTmVar |
|---|---|
| `a_inc_tvar_inv` | `a_inc_var_inv` (one more output, `A'`, and the `≡ᵗ`) |
| `a_inc__tvar` | `a_inc__var` (one more premise) |
| `a_inc_tvar_mid_strip_id` | `a_inc_var_mid_strip_id` |
| `a_inc_equiv_mid_insert_tvar` | `a_inc_equiv_mid_insert_var` (one more premise) |
| `a_wf_aenv__tvar` | `a_wf_aenv__var_typ` (one more premise) |
| premises `α ≠ β`, `β ∉ ftv P0` | both DERIVED (see above) |

⚠️ **The one genuinely new obligation is the SEMANTIC MIDDLE.**  A rigid entry
has no payload; a term entry does, and both `a_inc__var` and
`a_inc_equiv_mid_insert_var` demand `Θ' ⊢ A' ≡ᵗ κ A` at the re-attachment.
The consistency twin's `Assign-SkipTmVar` case proves precisely that
(prop_consis_complete.v:5595-5690, `Hmiddle`), through
`a_inc_equiv_msubst_ptyp` + `msubst_compose_id_ptyp` + `msubst_ptyp_agree` +
`msubst_compose_downarrow_tyequiv`.  ⚙ One extra step the consistency proof
does not need: the subtyping row re-attaches through the JUNK SWAP, so the
increase's witness is `kswap_msubst β β1 ζ` rather than `msubst_compose ζ κf` —
close the gap with `msubst_ptyp_kswap` (prop_swap.v:1983), whose hypotheses are
free because `β`/`β1` are fresh for the payload (it is scoped in `Θ0`).

With both rows, `sub_flex_complete_holds`'s `a_sub_flex_walkable Θ0` premise is deleted and
its two `exfalso` branches become ordinary delegations.

### ⭐⭐⭐ §12.4 THE BUNDLE IS ASSEMBLED (2026-08-03) — one hypothesis left

`make coq` green, admit-free, axiom-free.  Three things landed, in dependency
order.

**(1) The two P7a term-variable rows are `Qed`.**
`a_sub_flex_complete_skip_tm_var` / `_skip_tm_skl`
(prop_sub_complete_thm.v §(N)/§(O)) came out of §12.3's substitution table
with no surprises — the recipe was right, including the two DERIVED premises
and the semantic middle.  The one place to be careful when transcribing is the
**two sides of the entry**: occurrences inside `Ξv ++ …` are the `a_inc`
TARGET and become `(β ~ abind_var_typ A')`; every other occurrence is the
SOURCE and stays `(β ~ abind_var_typ Qv)`.  `a_sub_flex_walkable` and its two
lemmas are DELETED; `sub_flex_complete_holds` takes no side condition on `Θ0`; obstacle (B)
is closed.

**(2) Obstacle (A2) is closed, and the paper was right all along.**
subtyping-proofs.tex:3385 already covers it — *"Since declarative subtyping is
congruent, we assume WLOG that guarded(P0) ∨ P0 = □; otherwise we apply
ForallR first."*  ⚠️ **Do not report the ForallL/ForallR overlap as a paper
defect.**  Its mechanical content is two lemmas in dispatch.v §11:

- `sub_gv_all_inh_forall_r_family` — from ANY TY/TC join onto a
  `bskl_all_inh` target, extract the cofinite ForallR family.  Induction on
  the join; the ForallL chain must bottom out in `__forall_r` because
  `__check` is the only other TY/TC row that can carry the target and its
  `guarded_pskl` premise refutes a ∀-inh counterpart (§8's step, read
  backwards).  Each ForallL step is re-applied under the new binder, its only
  context-sensitive premise (`Θ ⊢ ⌊ψ⌋ˢ`) weakened along the added rigid.
- `ad_pat_sub_gv_fuel_weaken` — needed because the extraction returns the
  family at whatever height it finds, while `a_sub_complete_forall_r` wants it
  at exactly `n` for a conclusion at `S n`.  A 20-line induction: only the four
  rules whose conclusion fuel is `S n` need `destruct m`.

`sub_complete_all_inh_counterpart` composes them: **whenever the counterpart is ∀-inh
the row goes through ForallR, whatever the join's last rule and whatever
`P0`** — so the ForallL rows' `guarded_pskl P0 ∨ P0 = ◇` premise costs
nothing, because a ∀-headed `P0` forces a ∀-inh counterpart through the FILL.

⭐ **And A2 is now DISCHARGED INSIDE the dispatch, not just closable.**
`p0_wlog_trichotomy` reads the WLOG straight off mode compatibility: at
`NM = SK` every compatible `P0` is a hole or an arrow; at `NM = TY` the only
non-guarded, non-hole shape is a `∀`, and only at `M = TC` (`__ti` forces the
hole, `__fn` forces an arrow).  `sub_complete_assemble`'s two ForallL cases now split on
that trichotomy and send the escaping shape to `sub_complete_all_inh_counterpart`,
so **`main_forall` TAKES `guarded_pskl P0 ∨ P0 = ◇` as a hypothesis** instead
of owing it.  The bundle's residual is strictly narrower than before.

**(3) `a_sub_complete_bundle_holds` (dispatch.v §12).**  Exactly the shape
§12.2 predicted:

```coq
Theorem a_sub_complete_bundle_holds :
  (forall n, main_forall n) -> a_sub_complete_bundle.
(* lt_wf_ind on the fuel; inside, lt_wf_ind on the CONTEXT LENGTH:
     sub_complete_arrow_holds (fuel IH)
   → sub_complete_ctx_lt n k   (length IH)
   → sub_flex_complete_holds        (sub_complete_arrow + sub_complete_ctx_lt)
   → sub_complete_assemble        (fuel IH + sub_flex_complete_holds at Ξ = nil, via `sub_flex_complete`) *)
```

`sub_complete_assemble`'s `PIH` is instantiated with `fun _ => True`: the two tophole
closures are `exact I` and the third hands back `sub_flex_complete n Θ0`, i.e.
`sub_flex_complete_holds` at `Ξ = nil`.  `a_sub_complete` (algorithmic.tex:1446) follows
as the `Ψ := ∅`, `R := ⌈P⌉ᵘ` instance.

⭕ **THE RESIDUAL is `main_forall n`, and (2026-08-03, later) it is down to
ONE component** — the count's history matters, because §12.2 listed only one
of the two and the P7c hand-off listed only the other:

1. **TASK 0's `sub_shield`** for a `P0` carrying a `∀` below its head.
   ⚠️⚠️ **Now known UNSUPPLIABLE as stated** — the double-occurrence witness
   (§14.6, cex/cex_p7_shield_double_occ.v) refutes the premise at a reachable
   ForallL node.  ⚠️⚠️ **And §14.7 settles WHY: `main_forall` itself is FALSE
   there (`cex/probe_double_occ_run.v`) — the residual does not close by any
   shield re-indexing; the MOTIVE must gain the typing's payload side
   condition (HANDOFF-completeness-repair.md TASKS 2–3).**
2. ⭐ **CLOSED (2026-08-03): `NM = TY -> uskl_ghost_free R'`** is ON THE
   MOTIVE — `sub_complete_concl`'s last premise, on the JOIN-side subject,
   with `a_sub_complete` carrying it as the external side condition
   (WF-SIDE-CONDITIONS.md).  The suppliers were exactly the predicted six and
   all cheap: Sub-Arrow inverts, Sub-ForallR passes through, both ForallL
   rows' construction became the shared `Hgfswap` assert (their own `Hgfj`
   hypothesis DELETED — the motive supplies it), Flex-Assign derives it from
   the walk's ≡ᵘ-to-a-painting slack (`tyequiv_mono_paint_ghost_free`),
   Flex-Solve from the deposited painting, and the dispatcher's
   `__univ_ghost_l/lg` / `__flex_mono` cases by `discriminate` /
   `mono_ptyp_to_uskl_syn_ghost_free`.

⚠️ **Why the hypothesis is `main_forall` and not a "shield
supply".**  It is tempting to state the residual as the thing actually
missing — some `forall α, sub_shield Θ0 Ψa ∅ α P0 (open Rb α) ψa` under side
conditions.  Do NOT: the side conditions are precisely the open question,
`sub_shield_forall_flex_p0_fails` (cex/cex_p7_shield_forall_flex.v) shows the
unguarded form is FALSE, and §14.6 now shows the guarded form is false TOO at
a reachable node.  A false hypothesis makes the conditional theorem
vacuously true and worthless.  ⚠️⚠️ **UPDATE (2026-08-03, §14.7): the
"`main_forall n` is KNOWN-TRUE — it is an instance of the very theorem being
proved" reasoning is RETRACTED — it was CIRCULAR exactly at the paper
theorem's over-quantification of `P0`, and `main_forall 3` is now REFUTED
(`cex/probe_double_occ_run.v`, `probe_main_forall_false`).  So the bundle IS
vacuous as stated.**  The discipline still paid off, in the opposite
direction to the one intended: because the hypothesis was the paper-shaped
`main_forall` and not a guessed supply, its falsity was DETECTABLE by one
closed instance — and detecting it is what turned the shield saga into a
statement about the THEOREM's quantifier.  The repair is a payload side
condition on the motive (HANDOFF-completeness-repair.md TASKS 2–3), not a
fourth shield re-indexing.

### ⭕ §14.10 TASK A (reachability), the POSITIVE half machine-checked (2026-08-04): the refuting payload needs a FROZEN argument

`frost/algo/cex/probe_payload_reachability.v`, all `Qed`, three
`Print Assumptions` closed.  §14.9 left reachability open and sharply stated;
this settles one of its two conjuncts at the RULE level and pins the search.

**What the refuting payload needs.**  Re-read §14.7's configuration as a
demand on `P0 = (∀γ.γ→γ) → f̂`:

1. a raw `Θ0`-flexible at the CODOMAIN — the algorithm has no inherited
   information there; and
2. a **bare ∀** at the DOMAIN.  It must be BARE, not `⫯`-wrapped: the domain
   is the position that feeds CONSISTENCY, and a guess's tag is payable only
   against a `bskl_all_inh` of the counterpart, which `pskl_to_bskl_inh`
   produces exactly at a `pskl_all_syn` of `P0`.

**(2) IS SETTLED: freeze is the only producer.**  A payload's arrow-LEFT is
the ARGUMENT'S COLLECTION — an `a_pat` output at `(TC, ◇)`, i.e. at the SK
sort.  The theorem is

    a_sub_sk_no_spine_all :
      a_sub SK M P0 Θ0 P Q Θ1 -> skmod[SK]{P0}{M} -> ~ spine_all_out M Q

where `spine_all_out M Q` says the output's MODE-SPINE (peel one arrow per
`FN`) ends in a bare `pskl_all_syn`.  Reading the rows: `__infer` is the only
one that returns the subject verbatim and it runs at **TI**, which
`spine_all_out` has no row for; `__check`/`__forall_r` are TY-only;
`__univ_ghost_r` wraps in `⫯`; `__arrow` hands the spine to its codomain
premise; `__ghost` returns the PAYLOAD, which `skmod[SK]` forbids (its spine
ends in ◇); and `__flex_mono`/`__forall_l`/`__univ_ghost_l` plus the whole
flexible walk merely relay (Flex-Assign substitutes a monotype into `P0`,
which leaves the arrow spine alone — `a_sk_mode_compat_subst`).

Lifting it through `a_pat` gives

    a_pat_spine_all_out_freeze :
      a_pat m Θ0 P0 e Q Θ1 -> skmod[SK]{P0}{m} -> spine_all_out m Q
      -> exp_freeze_inside e

with `exp_freeze_inside` the spine of head positions a freeze can occupy
(application function, lambda body, the expression itself).  The four
`a_sub`-delegating rows die by the theorem, the two Check rows emit a `⫯`,
and Abs/App relay.  The corollary
`app_payload_domain_all_needs_freeze` is the form the question uses.

⭐ So the hand-off's warning is now a THEOREM in the positive direction: do
not try to prove "payload domains are never ∀-headed" (false — `{|e|}`
collects at TI where `a_sub__infer` is verbatim), but DO use "only `{|e|}`
makes them so".  **A refuting source program must freeze a polymorphic
argument.**

**The other half of the tension, also at the rule level.**
`a_guess_mono_all_free : a_guess_mono Θ P Ξ A -> mono_ptyp A ->
pskl_all_free P` — `a_guess_mono`'s ∀ row returns a `ptyp_all`, never a
monotype.  Since `a_assign__solve_m` is the ONLY rule that solves a flexible
against an inherited skeleton and it demands `mono_ptyp τ`, **a flexible can
never absorb a ∀**.  That is simultaneously the mechanism of §14.7's collapse
(SolE-FlexR overwrites the eq-constraint's polytype yield, and SolveM cannot
recover it) and the obstruction to checking a frozen polymorphic argument at
a raw-flexible payload.

**⭕ WHAT REMAINS OPEN — conjunct (1), and it is one crisp statement.**  The
ambient payload of an application is the OUTER function's domain, i.e. the
output of a consistency guided by the collection of THAT SAME application
(`a_consis__ghost_r` — payload ◇, output = subject — is what leaves a
ForallL-guessed flexible RAW; `__flex_l`'s assignment otherwise defines it,
and `a_typing__abs`'s `a_split__flex` only propagates one).  But that
collection is computed by the SAME `a_sub` run, at the same subject and the
same payload domain, differing only in the SORT — SK guesses ghosts, TY
guesses flexibles.  So when the marker's domain position carries the ∀ that
(2) demands, the marker's instantiation IS that ∀ and the run's codomain
output is a `⫯`-wrapped skeleton rather than a plain ◇ — whereupon the
enclosing look has information and the ambient is not raw.  **That
co-determination is why (1) and (2) pull in opposite directions**, and
closing it needs one further EXTRACT-level fact:

> the extract's output is ghost-ish only if the look collected nothing at the
> marker.

That is P6-level machinery and is NOT proved here.  Until it is, TASK A's
verdict is: **no reachable witness, and the obstruction is identified and
half machine-checked** — every probe to date (`docs/repros/…`) lands on one
horn or the other, and the two known near-misses (`_reject_pipe`, which gets
(1) and loses (2); `_probe_frozen_arg`, which gets (2) via the freeze) are
now explained by the same fact rather than by two separate accidents.

#### ⭐⭐⭐ §14.10a USER DIRECTIVE (2026-08-04): the SUBTYPING half must be settled WITHOUT typing

The reachability framing above (and TASK A of the hand-off) appeals to what
`a_typing`/`a_pat` can BUILD.  ⚠️ That is the wrong lens for
`thm:complete-subtyping`: **the paper's proof never mentions typing**, so the
obligation is that DECLARATIVE SUBTYPING and the ALGORITHMIC CONSTRAINT
COLLECTION match on their own terms.  §14.10's lemmas stay valid and useful
(they are rule-level facts about `a_sub` / `a_pat` / `a_guess_mono`), but the
open question is NOT "can the typing reach this payload".

**Where decl and algo actually diverge, at the subtyping layer.**  At the
double-occ configuration the look collects `[eq(∀γ.γ→γ); sub_tc(f̂)]` and the
solve THREADS them (`a_solve_cstr__eq` feeds the eq's yield into the rest).
The eq yields `∀γ.γ→γ`; the sub-constraint then solves ON that pattern and
reaches

    a_solve_eq__flex_r  (SE-FlexR) :  Θ ⊢ₑ P ∼ α̂ ⤳ α̂

which DISCARDS the accumulated pattern `P` and returns the flexible.  Compare
its ghost twin

    a_solve_eq__hole_r  (SE-VacuousR) :  Θ ⊢ₑ P ∼ ◇ ⤳ P

which KEEPS it.  ⭐ Both a ghost and a raw flexible carry NO information at
that position, and the two rules disagree about what to do with the
information already accumulated — that asymmetry is the whole divergence.
Declaratively the flexible's image is a MONOTYPE (`κ f̂ = 1→1`) and ForallL
instantiates the guess down into it; algorithmically the eq's polytype yield
is thrown away and cannot be recovered, because `a_assign__solve_m` demands
`mono_ptyp τ` and `a_guess_mono_all_free` (§14.10) says a monotype guess
exists only for a ∀-free skeleton — **a flexible can never absorb a ∀**.

**So the repair is one of these two, and both are subtyping-level:**

* SE-FlexR is too destructive — it should behave like SE-VacuousR (yield the
  accumulated pattern) when the pattern is not ◇, the flexible being recorded
  in the context rather than in the output.  ⚠️ This CHANGES a paper rule
  (full-algo-spec.tex:1374); it must be flagged, not made silently.
* or `lemma:complete-look` / `thm:complete-subtyping` need a side condition on
  the LOOK's constraint list — e.g. no `eq` constraint with a ∀-carrying yield
  may be followed by a `sub` constraint against a raw flexible — stated where
  the paper's proof invokes look completeness.

Next step is to decide between them by reading what the solve is FOR: whether
returning `α̂` is load-bearing anywhere (the assignment that follows already
records the flexible in Θ), and whether the repaired rule keeps P6-Sv/P6-Ss
sound.  No `a_typing` argument is needed for either.
