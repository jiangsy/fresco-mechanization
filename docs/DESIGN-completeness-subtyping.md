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
   fill, namely subject refinement `ad_refine_pskl_f ∅ Θ ∅ (θP) Q`.  Our
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
and (θ:Θ0⇒Θ ; Q), IF
  (join/subtyping)  typsub^N_M[Ψ] Θ ⊢ syn(θS) ⊑ bid Q          ← height/fuel lives here
  (P0-fill)         Θ ⊢ inh(θP0) ⤳syn bid Q
THEN ∃ P1 Θ1 θ1:
  a_sub^N_M[P0] Θ0 ⊢ P ⊑ P1 ⊣ Θ1        (algo run)
  θ1:Θ1⇒Θ  ∧  Θ ⊢ θ1 P1 ⊑ Q (precision)  ∧  θ ≡ θ1 : Θ0⇒Θ.
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
- `θ` is the mech's `ρ ∷ Θ0 ⊑ Θ` (an `a_inc` metasubstitution).
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
`⊑` and complete-look's `precise{θa Pa}{⌊ψa⌋}` output, tex:2764):

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

## 6. Status log

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
