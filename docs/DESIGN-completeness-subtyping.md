# Mechanizing Completeness + Optimality of Subtyping

Companion to `DESIGN-subtyping.md` (which covers both halves at the map
level and whose §2.2 / §4 / §5 this doc refines).  Soundness
(`a_sub_sound_thm`) is **DONE, Qed, axiom-free**
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
   its shape is copied *verbatim* from `a_consis_complete_thm`
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

**Mech motive** — copy `a_consis_complete_thm`'s shape (the id-witness
`ρ1`/`ζ` factoring), swap consistency's judgment for `ad_pat_sub`, and
add the *third* solution premise (lesson 1).  Skeleton:

```coq
Lemma a_sub_complete_gen : forall n,          (* fuel; strong induction *)
  forall NM M Θ0 P0 P S Ψ Θ ρ Q,
    a_wf_aenv Θ0 ->  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
    ⌊S⌋ˢ = P ->                               (* erasure of the unresolved subject *)
    ρ ∷ Θ0 ⊑ Θ ->  a_wf_aenv Θ ->
    (* solution, 3 conditions — matching a_consis_complete_thm: *)
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

Notes on shape (verify each against `a_consis_complete_thm` when writing):
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
- **Corollary** `a_sub_complete_thm` (paper-facing): `S:=` a decoration
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
| **P6c** | `a_extract_complete` | complete-look (2730) | — | P6b + P5b + guess^TY sub-induction = `guess_join_witness` pattern |
| **P7a** | `a_sub_flex_complete` | complete-flex (2835) | `lex(n,|Ξ|)` mutual | assign/unify walk recipes (mid-strip/insert) |
| **P7b** | `a_sub_complete_gen` | thm generalized (3050) | `lex(n,|Ψ|)` | mutual w/ P7a; cases → `a_consis_complete_thm` [Qed], P6c, P7a |
| **P7c** | `a_sub_complete_thm` | thm (algorithmic.tex:1446) | — | instantiate `S=P`, `Ψ=∅`, `n` via `_to_n` |

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

- `a_consis_complete_thm` (`prop_consis_complete.v:8648`, Qed,
  axiom-free) — the motive-shape template AND the Infer/Check/UnivGhostR/
  Arrow cases.  Its 3-premise form (join + P0-fill + **subject
  refinement**) is why our motive has the third premise.
- `guess_join_witness` increment-transformer (join file) — the
  guess^TY construction in `a_extract_complete`.
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
  `no_forall_bskl` predicates.v:97, `ptyp_to_bskl_inh_syn_eq`
  prop_mono_bridge.v:78 — build the pskl analog).  Then `__hole` needs
  `Θ ⨟ ∅ ⊢ₚₛᵃ ⌊ψ⌋`: strip Δ from the wf premise via `Δ ∩ ftv ⌊ψ⌋ = ∅`
  (the ppre__hole side condition) + a wf Δ-strip lemma.
- **tophole_remove** `pskl_tophole P ⊑ᵖ[Ψ] ψ` → `__tophole_remove` + IH
  (same ψ, same Ψ; wf/tags unchanged).
- **tophole_fill** `pskl_tophole P ⊑ᵖ[Ψ] all_etag ε ψ0` → **VACUOUS**.
  `inh(all_etag ε ψ0)` erases to `bskl_all_inh(...)` but no `⊢ᵣᵃ`
  rule gives `⊤◇· ⊳ all_INH ·` (tophole_fill of `ad_refine_syn` outputs
  `all_SYN`).  Exclude via NEW helper
  `ad_partial_precise_tags_sub : ad_partial_precise Θ Δ Ψ P ψ ->
   d_tags_skl Ψt ψ -> Ψ [<=] Ψt` applied to the RECURSIVE premise
  `⊤◇P ⊑ᵖ[Ψ] open ψ0 X`: gives `Ψ ⊆ d_tags(open ψ0 X) = Ψt0`, but
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

Term-level substitution encoding (confirmed against `subst_bskl_in_uskl`,
def_ott.v:487 — replacement is a `uskl`, var is the `usklvar` α):
`S[ψa/α] = subst_bskl_in_uskl ψa α S`;
`S[Pa/α] = subst_bskl_in_uskl (pskl_to_uskl Pa) α S`.

```coq
Lemma ad_pat_sub_precise_subst : forall n NM M Ψ Ψa Ψ' Θ S α ψa Pa Q,
  ad_pat_sub_n n NM M (Ψ `union` Ψa) Θ (subst_bskl_in_uskl ψa α S) Q ->
  Θ ⨟ empty ⊢ₚᵣᵃ Pa ⊑ ⌊ ψa ⌋ˢ ->          (* precision Pa ⊑ ⌊ψa⌋ *)
  a_tags_sort NM Ψ' ψa ->                    (* Ψ' = ψa's tags *)
  Ψa [<=] Ψ' ->
  (* possibly: (NM = ty -> «Pa is a type») — add iff a case needs it *)
  ad_pat_sub_n n NM M Ψ Θ (subst_bskl_in_uskl (pskl_to_uskl Pa) α S) Q.
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
`S`, `Ψ`, `Ψa` (`remember (subst_bskl_in_uskl ψa α S)`).  In each rule,
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
   shape per case.  REAL WORK: the ⊤◇ / hole / ∀ interplay (≈ the L-A
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
  REAL content is **holey `Psrc`** — the hole/⊤◇ cases are the point,
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
  syntactic tag collector, `frost/def_tags.v` — a LEAF module, imports
  only `def_ott`, so it can be used by def-files without a rebuild
  cascade.)  This is how step (2) is stated and proved.
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
hole / ⊤◇-chains / flex / TY-type conditions); freshening bridge ≈ 300
(deferred).  2–3 focused sessions.

## 6. Status log

- 2026-07-29 (a2): **P6-Sv induction at 11/12 — only ARROW and
  ForallL-tagged remain, and NEITHER needs new infrastructure.**  Closed
  since (a1): the ρ-EXTENSION `uskl_rho_subst` (the paper's
  `ρ_b = ρ ∘ [ψ_b/β]`) together with `uskl_rho_subst_refl`, `uskl_rho_rename`
  and `uskl_rho_is_tskl`; and the CHECK case in full, including the sub-row
  where hazard H3 materialised.
  - The H3 sub-row (Pi = ⊤◇Pi' with a FLEXIBLE body): `SolEq-Var` keeps the
    BODY's flexible rather than the payload's, so the output is ⊤◇Pi' and
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
    / □ (SolS-GhostLF) / ⊤◇ / flexible / unit and ∀ impossible.  NOTE: the
    ⊤◇ row needs NO inner induction — wf makes the ⊤◇-body GUARDED, so it is
    unit/var/arrow and reduces to the other rows.  (P6-Cv needed a size
    induction there for unrelated reasons.)
  - **ForallL-tagged**: `uskl_rho_subst` + `flex_shield_descend_r` + the
    `fastep_all_r` prepend; Pi grid ∀ / ⊤◇ / □, the last two as in
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
  **HAZARD H3 MATERIALISED (Check, Pi = ⊤◇Pi').**  The paper writes "by
  congruence of constraint solving, we ASSUME refb is derived by
  SolEq-GhostGuarded" (subtyping-proofs.tex:1810).  Mechanically P6-Cv
  returns whichever derivation it built, so SolEq-FlexR must be handled too;
  `a_non_flex_guarded_dec` splits it, and only the sub-row where the
  ⊤◇-body is ITSELF a flexible is still open (SolEq-Var then keeps the
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
  growing, ⊤◇/⊤̇◇, flexible unfolding).  Closure under a descent is
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
  Flex`) has NO plain-□ row, NO plain-⊤◇ row and NO untagged-∀ row: its
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
     ghost-erases top-level ∀s of argument skeletons to `⊤◇(□→□)` — so the
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
     hole / ⊤◇ source / ⊤̇◇ target / arrow / ∀-descents), and the ONLY rule
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
  ghost-erased (⊤◇), so spine tags never enter Ψi via `ad_ppre__forall`;
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
  - **⊤◇ row** (UnivGhost): wrapped IHX (Pi0:=⊤◇.Pi', P0i:=⊤◇.P0'); solve =
    IHX output via `tophole_both` (strengthen_tvar; 3-subgoal inversion, the
    2 extra guarded-tophole cases killed by `inversion Hg`); precision =
    `ad_ppre__tophole_fill` + rename_tvar family (X-freshness of the fixed
    subject via `a_solve_sub_eq_ftv` + `a_wf_pskl_ftv_dom` +
    `msubst_pskl_ftv_avoid`).
  - **□ row** (GhostL): solve = `a_solve_eq__hole_l` (Pa:=⊤◇.P0'); IHX with
    Pi0:=□ (Hpre0x = `ad_ppre__hole`); same tophole_fill + rename closure.
  - **∀ row** (ForallGhost): solve = `a_solve_eq__all_l_tophole` (RHS ⊤◇.P0'
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
  The ONLY ForallSyn-specific twist is the refinement: P0=⊤◇.P0' makes
  `Hrefine` a `tophole_fill`, so `Hrefb` = its inverted body at
  `(X~tvar)++Θr ⨟ Δr ⊢ᵣᵃ bskl_tophole(paint P0') ⊳ open Q X`, and each row
  moves X into Δr by `ad_refine_syn_aenv_to_delta` — which WORKS on the
  tophole subject because `bskl_no_hole (bskl_tophole A) = bskl_no_hole A`
  (guarded body ⇒ no hole).  Rows use the WRAPPED IHX (Pi0:=⊤◇.Pi',
  P0i:=⊤◇.P0'): the IHX solve output IS the outer solve (strengthen_tvar,
  no SE-rule), and the precision fill matches HF directly (no strip).
  **THE SOLE REMAINING BLOCKER (all 3 rows): the ForallSyn precision
  conclusion is `⊤◇.PaX ⊑ᵖ uskl_all_etag ε ψR`, closed by
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
  family — the SAME kit unblocks □ (hole_l, Pa:=⊤◇.P0') and ∀
  (all_l_tophole, P0i:=⊤◇.P0' KEPT + FOLD).  Backups: p6cv_working8_
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
  (guarded ⊤◇-body excludes the all_syn source that blocks descent); the
  KEYF preamble + tag algebra (simpler than ForallInh — `ε ∉ Ψ`, so
  `Ψa ⊆ Ψ0'` is direct, no ε-split); `HψaB` from the reconstructed ρ;
  the P0-grid absurd columns (`allsyn_rhs_absurd` + rigid K17) and the
  `P0 = □` VacuousR column; and the `P0 = ⊤◇` column INFRASTRUCTURE — the
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
  ForallInh's □/⊤◇ rows, where the binder enters `Θtv` but not `Δ`.)
  Then the 3 Pi-rows: □ (GhostL, per-X' IHX rerun, `ad_ppre__tophole_fill`
  conclusion), ∀ (ForallGhost `a_solve_eq__all_l_tophole` +
  `a_solve_sub_eq_rename`, Δ-grow `ad_ppre__forall`), ⊤◇ (UnivGhost
  `a_solve_eq__tophole_both`, refinement ⊤◇-strip, `ad_ppre__tophole_keep`).

- 2026-07-26 (q): **`forall_syn_tagged` UNBLOCKED — the §6(o) open question
  resolved WITHOUT a statement change.**  The fear was that ForallSyn's
  `P0 = ⊤◇.P0'` refinement uses `tophole_fill`, which grows the
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
  `{⊤◇.P0' (tophole_fill), □ (□-fills-to-∀), flex-chain}`); the Z-into-Θr
  permutation lemmas; the ForallSyn conclusion precision via
  `ad_ppre__tophole_fill` (grows the aenv, NOT Δ — so NO ∀S-family
  Δ-transfer issue here, unlike ForallInh).

- 2026-07-26 (p): **REPAIR PHASE 3b — `forall_inh_tagged` (case 1) CLOSED;
  `_gen` now 14/15 (only `forall_syn_tagged` admit); dev scratch compiles
  in 19.6s.**  Built per the §6(o) recipes: KEYF continuation, ε as a
  Ψ'-solved tag (`Ψa' := remove ε Ψa`), the P0-grid (only P0=∀.P0b
  survives), the shared IHX (body-IH wrapper) + FOLD (per-instance
  strengthen→rename→rewrite fold), and rows A (Pi=∀), B (Pi=□), C
  (Pi=⊤◇-fill).  Two engineering findings worth keeping:
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
  REMAINING: **`forall_syn_tagged`** — its P0=⊤◇.P0' refinement is
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
    `a_wf_pskl__tophole` demands GUARDED bodies, so `⊤◇.∀…` subjects are
    not wf: the precision tophole_remove branch dies (guarded body vs
    all_etag target: unit/arrow by inversion, var by the
    mono-subject-tags-empty ε-contradiction), and the P0 = ⊤◇.P0' rows
    die the same way on the refinement side.  (Sanity check that forced
    this: `⊤◇.∀Z.Z ∼ ∀β.β` has NO solve derivation — GhostForall's body
    keeps the ⊤◇ and the inner `∀Z.Z ∼ β'` is stuck — so wf-exclusion is
    load-bearing, not a convenience.)  Surviving grid per case:
    Pi ∈ {∀ (A), □ (B), ⊤◇-FILL (C)} × P0 ∈ {∀ (case 1) / ⊤◇-fill, □
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
    * Rows A (Pi=∀) and C (Pi=⊤◇ via tophole_fill): ONE fresh-X IH run;
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
  - OPEN QUESTION for case 3 (forall_syn_tagged) ONLY: its P0=⊤◇ row is
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
    recursion rows pass families through the ⊤◇/arrow folds unchanged;
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
     different rules — verified dead end).  The □/⊤◇-fill rows fold
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
    the PRIMARY refinement forces P0's core to be `⊤◇ⁿ.(var X0)`
    (hole-fill `var X0` is not Θr-wf; flex-chases are Θr-scoped and
    X0-free — use rhs-bound), Hpre forces Pi's core ∈ {var X0, □}, and
    every reachable output Pa is `⊤◇ⁿ.(var X0)`-shaped, hence
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
  `flex_apart_all_etag_forall_inv` for ⊤◇-sources (the deleted
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
    branch main IHs with the tag split; □ = VACR + SE-VacuousR; ⊤◇ =
    `flex_apart_tophole_p0_inv` + SE-GuardedGhost + CORE), □ (P0-grid:
    flex = FLEX + SE-GhostL; arrow = □-precisions per branch + branch
    main IHs + `a_solve_eq_hole_subject_inv` pins; ⊤◇ = CORE(□,P0') +
    SE-GhostL), ⊤◇ (tophole_remove inversion only — target is an arrow —
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
    the Pi = □ and Pi = ⊤◇(tophole_fill-branch) rows.**  The ∀-row
    (Pi = ∀.Pib) follows §6(h): precision-body from `ad_ppre__forall`
    inversion at `Θ ⨟ add X Δ`, aenv-weaken into the IH at
    Θx = (X~tvar)++Θ, `ad_partial_precise_strengthen_tvar` back out
    (legal: X ∈ add X Δ), solve out via `a_solve_eq_strengthen_tvar` +
    `a_solve_sub_eq_rename` cofinite reassembly.  But in the □/⊤◇-fill
    rows the IH's precision PREMISE can only be built at Δ (the □-rule's
    side condition `Δx ∩ ftv(ψR^X) = ∅` fails at Δx = add X Δ since
    X ∈ ftv(ψR^X) in general), so the IH's OUTPUT lives at Δ (resp. at
    (X~tvar)++Θ ⨟ Δ for the fill-branch) — and the conclusion's
    `ad_ppre__forall` body must sit at `Θ ⨟ (add X Δ)`.  The transfer is
    blocked precisely at `ad_ppre__hole`: its Δ-disjointness is NOT
    Δ-monotone.  **This is a PAPER-GAP, not a falsity**: the paper's own
    Subcases Pi=□ / Pi=⊤◇.Pi' (consistency-proofs.tex ForallInh/
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
       the ⊤◇-fill rows call it.  No statement change, but a second
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
    `fa_clean` for Δρ-clean targets, congruences incl. ⊤◇/⊤̇◇ strips and
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
  (⊤◇-strip recursion on `size Pi + size P0` at a fixed arrow target, with
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
    ⊤◇-bodies have no rule into them) — both sides forced to `□`, all other
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
  - **topholeg** — the ⊤̇◇ congruence via an inline KEY continuation shared
    by the refl and congruence ρ-branches (refl recast with `urho__refl`,
    lc from `is_tskl_lc`).  Grid: Pi ∈ {□, ⊤◇.Pi'} (paints/guarded die);
    P0 = □ ⇒ SE-VacuousR with Ψa=∅ from the `is_sskl` kit
    (`ad_refine_syn_hole_sskl` + `ad_pat_consis_sskl_tags` — the paper's
    "P0 = □ ⇒ Q synthesized ⇒ Ψa = ·" special case); P0 = ⊤◇.P0' ⇒
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
  the MAIN consistency IH), then flex/⊤◇/∀ cases per the build order.

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
    target (follows `flex_l` def-chains, strips ⊤◇); discharges `Pi=□` and
    ⊤◇-`P0` unit subcases.
  - `msubst_lookup_notin_dom`, `a_inc_dom_flex`, `msubst_pskl_tvar_id` —
    the metasubst-domain facts (dom ρ ⊆ source flexibles; a rigid source
    var is msubst-fixed), for the `P0 = var` FlexR/rigid split.
  - `ad_refine_syn_rigid_var_unit_absurd` — a rigid var cannot refine into
    unit; kills the rigid-`P0` unit subcase.
  Kept in dev (Qed): `ad_ppre_unit_tags_empty` (unit target ⇒ Ψi=∅).
  **STRUCTURE learned:** each of the 15 cases carries a 2-D Pi×P0 grid; the
  ⊤◇-stripping (both Pi and P0 sides) recurses on skeleton SIZE, so each
  leaf/structural case is cleanest as a STANDALONE size-induction lemma
  (`a_solve_eq_cv_<shape>`) that the main consistency-induction dispatches
  to — the main IH is on the consistency derivation and gives NO handle on
  a smaller Pi/P0.  **UNIT CASE CLOSED** (commit 68c48eb): `a_solve_eq_cv_unit` Qed,
  axiom-free — the full Pi×P0 grid as a standalone size-induction lemma
  (strong induction on `size Pi + size P0` so ⊤◇-stripping on both sides
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
    into a ∀/⊤◇ needs a ∀/⊤◇/defined-flex source, which a monotype never is.
    So ForallInh/ForallSyn/ghost provably have non-flex P0, and leaves are
    handled directly (SolE-Flex / the SolE-Var ρ-var special case).
    Machine-checked shape: `ad_refine_syn` into `bskl_all_inh` forces the
    source to be ∀/⊤◇/defined-flex.
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
  - **P6-Cv/Sv plan (now):** ∀/⊤◇/ghost cases prove non-flex P0 from the
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
  helpers only; soundness stack untouched (a_sub_sound_thm still
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
  ⊤◇-wrapped or definition-chained leaf positions force SE-GhostForall's
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
  X ∉ dom Θb, body-⊑ᵤ, `uskl_precise_subst`, `subst_bskl_in_uskl_intro`
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
  `a_extract_complete`) — remember the Infer/Check cases must re-route
  through `consis_complete`/`a_consis_complete_thm` (the paper's
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
  when the ghostier subject adds ⊤◇-wraps or folds flex defs; P7b's
  measure is then lex(fuel, derivation-structure), which its
  non-incrementing cases support since they recurse structurally);
  `_g` helpers (g_of, g_psi_cong, g_ftag_sub, g_wrap_tophole,
  g_fold_flex, g_concrete_target, refl_transport, hole_intro,
  uskl_ghost_free_subst, mono_paint_guarded, uskl_precise_guarded); and
  per-rule ⊑ᵤ-transports for **UnivGhostR / Ghost / GhostG**
  (`ad_pat_sub_g_{ughost_r,ghost,ghostg}_transport`) — these validate the
  whole inner-⊑ᵤ-induction pattern: congruence roots rebuild via (2') on
  the reassembled pair, ⊤◇/flex peels recurse at the SAME fuel via
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
  rewrite both sides with `subst_bskl_in_uskl_intro`, recurse the main IH
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
  (`ftag_in_uskl`).  `make coq` green; `Print Assumptions` on
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
  `consis_complete` / `a_consis_complete_thm` or grow a `-var` wrapper).
- 2026-07-22: doc written.  Soundness done.  Completeness = greenfield
  (inventory: no `a_sub_complete*`, no `ad_pat_sub_n`, no
  `precision_subst`; `a_consis_complete_thm` Qed; build green, 0 admits
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
□ (SolS-GhostLF) / ⊤◇ / variable, with unit and ∀ refuted by the precision
against an arrow guess.  The variable row needs no solving at all — the
κ-image of a variable is a MONOTYPE, so `ad_ppre_mono_subject_target_tags_
empty` makes the guess tag-free and `Ψa = ∅`.  The ⊤◇ row recurses
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
  That is exactly the ⊤◇-body discipline DESIGN §7 names in prose, and it is
  now a LEMMA — `a_wf_pskl_shielded_dom`: since `a_wf_pskl__tophole` types
  the ghost's body at the EMPTY Δ, a well-formed skeleton's shielded
  variables all live in `dom Θ`, never in Δ.

**The `Pi` grid has ONE live row** (`Pi = ∀β.P1`, the paper's).  Every other
shape would have to solve the top-level tag ε, and ε is already in `Ψi` —
proved, not assumed: `ε ∉ ftag R` (ρ only ADDS tags,
`uskl_rho_ftag_target_sub`, together with `Ψρ ∩ Ψ' = ∅` and sortedness of
ψa) and `ε ∉ ftag ψ_b` (the rule's own freshness) bound the premise's solved
tags via `ad_pat_sub_g_ftag_sub`, giving `ε ∉ Ψsub ⊇ Ψa`, hence `ε ∈ Ψi` by
`Ψi,Ψa = Ψ'`.  So □ (`Ψi = ∅`), ⊤◇ (both its rules), the variable row and
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
> monotypes; refinement into a ∀/⊤◇ needs a ∀/⊤◇/defined-flex source). (b)
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
| P6-L | `a_extract_complete` | subtyping-proofs 2730 | `a_extract` + plain precision | wraps P6-Ss; `guess_join_witness` for TY; `ad_partial_precise_complete` upgrades ⊑ᵖ to ⊑ |

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
   With X ∈ Δ ∩ dom Θ, precision still admits a ⊤◇-wrapped leaf position
   via `tophole_remove` (v4: `Pi`-pos `⊤◇.ŵ`, ŵ ∈ Θ0 flex, κŵ = X — wf,
   since the ⊤◇-body is ŵ, not X) or via def-chains (v5: κŵ = β̂,
   `β̂ := X ∈ Θ`); then target-pos `all_syn` (P0-pos `∀γ.γ`, image
   ψ'' = `∀^ε'γ.γ`, refinement satisfied through `all_inh`) forces
   SE-GhostForall, whose `all_syn`-output has NO precision rule against
   the rigid `var X` — conclusion underivable, all premises satisfied.
   What kills v4/v5 at the REAL call site (P6-Sv ForallL, X freshly
   opened from `Pi = ∀β.P1`): (i) X cannot occur under any ⊤◇ of P1 —
   `a_wf_pskl__tophole` demands empty-Δ bodies (the "no binder under a
   ⊤◇-body" discipline recorded on `a_sub__forall_l`); (ii) X postdates
   every flex-image of κ (κ ∷ Θ0 ⊑ Θ is fixed before X is picked); (iii)
   X postdates every definition in Θ (aenv order: `(X~tvar)++Θ`, wf
   scopes defs to their tails).  MECHANIZATION: carry a freshness pack
   `∀X ∈ Δρ`: `X ∈ Δ` (blocks the hole rule), `binds X abind_tvar Θ`
   (blocks flex_r, via wf-uniq), `X ∉ msubst-image-ftv of κ`,
   `X ∉ def-image-ftv of Θ`, `X ∉ shielded_ftv (msubst κ Pi)` — where
   `shielded_ftv : pskl → atoms` is a NEW syntactic collector of the
   ftvars of all ⊤◇-bodies.  The LEAF INVERSION lemma then holds:
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
  P0=⊤◇P0' by refinement inversion since P0≠□), Arrow (LE-Arrow + sequential
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
  `subst_bskl_in_uskl_fresh_eq` + `msubst_pskl_ftv_avoid` +
  `a_inc_image_ftv_dom` (α∉ftv P).  **Main-induction plan:** `induction
  Hconsis` on the GENERAL statement (do NOT dispatch special cases at top —
  the IH must stay general; the current scratch's top-level dispatch is a
  scaffold to be folded per-case).  In each consistency case: (i) invert
  `subst_bskl_in_uskl ψa α R` on R's shape (R=`uskl_var α` → the P=α leaf,
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

**Decision: encoding (a-lite) — `subst_bskl_in_uskl ψa α R`.**  The
uskl-for-var substitution `subst_bskl_in_uskl : uskl → usklvar → uskl → uskl`
ALREADY EXISTS (def_ott.v:487, full lngen kit: open/subst commutation, spec,
fresh_eq, lc, degree) — `S[ψa/α] = subst_bskl_in_uskl ψa α S` (the P5b-ii
convention).  So:

1. Carry `R : uskl` (playing `syn κS`) tied to P by
   **`⌊ R ⌋ˢ = msubst_pskl κ P`** — erasure commutes with the monotype
   substitution κ, so `erase(κS) = κ(erase S) = κP`.  `msubst_uskl` is NOT
   needed: R is posited, not built.
2. **The consistency subject is `subst_bskl_in_uskl ψa α R`** — this PINS
   every α-image to the one `ψa`, exactly `(κS)[ψa/α]`.  Inverting it against
   the consistency derivation is the same leaf/congruence split as `uskl_rho`
   but via the Fixpoint's computation: `subst_bskl_in_uskl ψa α R = arrow …`
   forces R = `uskl_var α` (leaf, subject = ψa, the P=α case) or R = arrow
   (congruence).  At each node `⌊R⌋ˢ = msubst_pskl κ P` recovers P's shape
   (msubst_pskl is structural on non-var P; the bare-var P cases are the
   `P=α` / `α∉ftv P` special cases).
3. **`uskl_rho` is used only at the P6-Cv DELEGATION** (P=α leaf): the P6-Cv
   corollary takes a `uskl_rho` premise, discharged by `urho__refl` on ψa
   (Δρ:=∅, ρ=id) — "the identity substitution, empty tag context" the paper
   names.  So P6-Cv's own kit is reused wholesale at the leaf; P6-Cs's own
   induction uses `subst_bskl_in_uskl`, not `uskl_rho`.

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
