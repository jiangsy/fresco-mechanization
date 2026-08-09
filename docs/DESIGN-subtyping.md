# Mechanizing Subtyping (soundness + completeness/optimality) — the full map

*2026-07-18, post-`complete_mu` (consistency completeness closed, 37a84b7).
Source of truth: `paper/sections/appendices/subtyping-proofs.tex` (3536 lines),
`decorated-algosub.tex`, `full-algo-spec.tex`, `full-decl-spec.tex`
(fig:decl-subtyping-all).  Mech state: branch `re-mech`.*

This is the plan for the two remaining flagship theorems of the algorithmic
metatheory:

- **thm:sound-subtyping** — an `a_sub` run yields a solution to its subtyping
  problem (algorithmic.tex:1439).
- **thm:complete-subtyping** — if a subtyping problem has a solution, `a_sub`
  succeeds and its solution is optimal (algorithmic.tex:1446).

A subtyping problem is `(Θ0; N; M; P0; P)` with `Θ0 ⊢ P0`, `Θ0 ⊢ P`,
`skmod^N(P0, M)`; a solution is `(Θ0 ≤[κ1] Θ1; P1)` with
`typsub^N_M[·] Θ1 ⊢ syn(κ1 P) ⊑ bid(P1)` and `Θ1 ⊢ inh(κ1 P0) ⋈syn bid(P1)`;
optimality is the usual ζ-factoring + `Θ ⊢ ζP1 ⊑ Q` precision
(algorithmic.tex:1423-1437).

---

## 0. Executive summary

The consistency stack absorbs most of the mathematical difficulty: **both
subtyping proofs consume the consistency theorems as black boxes** at every
`Infer`/`Check`/`UnivGhostR`/`Arrow`-premise node, and those black boxes are
now fully Qed (`a_consis_sound`, `a_consistag_sound_aux`,
`a_consis_complete`/`complete_mu`, `a_consis_decorate`).  The genuinely
new content is:

1. the **constraint-collection/solving layer** (`a_looksub`, `a_solve_sub`,
   `a_solve_cstr`, `a_extract`, `a_guess`) — *zero* lemmas exist about any of
   these;
2. the **decorated tag layer** (`a_subtag`, `a_solvetag`, `a_solvetag_sub`,
   `a_solvetag_eq`, `a_tags_sort`) — defined, *zero* lemmas;
3. three **missing definitions**: `ad_pat_sub` (declarative subtyping in
   algorithmic contexts), the algorithmic tag-well-formedness
   `Θ ⊢^N Ψ ψ`, and **partial precision** `Θ ⨟ Δ ⊢ P ⊑[Ψ] ψ`;
4. the **flex-variable walk** (`a_sub_flex`) — new cases, but a direct
   transplant of the closed unify/assign walk recipes.

Unlike consistency, **no new μ-measure is needed**: the paper's completeness
induction is lexicographic on (height of the declarative derivation, |Ψ|),
mutually with a context-structural induction for the flex walk.  The one
measure-theoretic obligation is that `precision-substitution` is
height-non-increasing (§4.3).

---

## 1. Judgment inventory

### 1.1 Exists (defined, unproved)

| judgment | file:line | paper |
|---|---|---|
| `a_sub` / `a_sub_flex` (mutual) | algo/def_extra.v:780/838 | `atypsub`, fig:alg-subtyping |
| `a_looksub` (+ `a_cstr`/`a_cstrs`) | algo/def_extra.v:270/258 | `looksub` constraint collection |
| `a_solve_sub` | algo/def_extra.v:359 | single-constraint solving |
| `a_solve_cstr` | algo/def_extra.v:445 | constraint-list solving |
| `a_extract` | algo/def_extra.v:463 | look ∘ solve ∘ guess (`\looksub^N`) |
| `a_guess` / `a_guess_mono` | algo/def_extra.v:244/222 | `guess^SK` / `guess^TY` |
| `a_subtag` | algo/def_decorated.v:229 | `asubtag`, decorated subtyping |
| `a_solvetag_sub` / `a_solvetag_eq` | algo/def_decorated.v:312/341 | decorated single-constraint tag solving |
| `a_solvetag` | algo/def_decorated.v:381 | `solvetag` over constraint lists |
| `a_tags_sort` | algo/def_decorated.v:96 | `⊢^N tags{Ψ}{ψ}` (see §5.4) |

Declarative side (all with weakening/renaming/subst/trans Qed in `decl/`):
`d_sub` (decl/def_extra.v:301), `d_pat_sub` (:479), `d_tags`/`d_tags_skl`
(:198/:225).

### 1.2 Missing (must be defined first)

**(D1) `ad_pat_sub`** — fig:decl-subtyping-all's `typsub^N_M[Ψ] Γ ⊢ syn S ⊑
bid P` transplanted to algorithmic contexts `Θ`, exactly as `ad_pat_consis`
(def_decl_algo.v:77) transplants `d_pat_consis`: same rules
(Infer/Check/ForallR/UnivGhostR/Arrow/ForallL/Ghost/GhostG/UnivGhostL(G)) plus
the flexible-variable *lookup* rules.  Notes:
- Signature `a_sub_mode -> mode -> atoms(Ψ) -> aenv -> uskl -> bskl -> Prop`.
- Its `Infer`/`Check` premises are `ad_pat_consis` (already defined ✓).
- The completeness proof's Flex-Solve case reads a subtyping premise off a
  *defined* flexible (`sublab{FlexMono}` "when `Θ ∋ α̂:=τ`",
  subtyping-proofs.tex:2904) — so the transplant needs `flex_l`/`flex_r`-style
  lookup rules mirroring `ad_pat_consis__flex_l/_r` and
  `ad_refine_syn__flex_l/_r`.
- ForallL's instantiation premise uses (D3) tag-wf and substitution
  `S[ψ/α]` at the `uskl` level — check `subst_uskl_in_uskl` exists in
  prop_ln (it should; grep before hand-rolling).

**(D2) subtyping problems/solutions** — inline the solution conditions in the
theorem statements, as `a_consis_complete` does (the old standalone
problem/solution definitions were deleted with the OPT-bundle file — inline
conditions are what the proofs actually consume).  The fill condition
`Θ1 ⊢ inh(κ1 P0) ⋈syn bid(P1)` is `ad_refine_syn` with an inherited-painted
source — the same shape as consistency's solution, so `ad_refine_syn_f_of_plain`
(join file) converts to the hygienic `_f` form where needed.

**(D3) algorithmic tag-wf `Θ ⊢^N tags{Ψ}{ψ}`** — `a_tags_sort` (def_decorated)
is *context-free* (no `Θ`): it checks sort/tag-uniqueness only, per the
external-wf discipline (docs/WF-SIDE-CONDITIONS.md).  Decide early whether the
subtyping lemmas need a Θ-carrying version (wf of ⌊ψ⌋ in Θ) or whether
`a_tags_sort ψ ∧ a_wf_pskl Θ ⌊ψ⌋` suffices — the latter matches the mech's
established style and composes with the existing `a_wf_pskl` kit.  Register
the choice in WF-SIDE-CONDITIONS.md.

**(D4) partial precision `Θ ⨟ Δ ⊢ P ⊑[Ψ] ψ`** — the completeness-only
judgment (rules at subtyping-proofs.tex:1561-1637).  The paper says it
"corresponds one to one to the definition of refinement in algorithmic
contexts": its rules are `ad_refine_pskl`'s with (a) a tag context Ψ collected
at tagged quantifiers, (b) hole matches any Δ-avoiding ψ, (c) tophole
remove/fill/keep trio, (d) `flex_l`/`flex_r` lookup rules.  Crib the
`ad_refine_pskl` metatheory proofs (weaken/Δ-mono/isub/rename) nearly verbatim.

---

## 2. Proof architecture

### 2.1 Soundness (subtyping-proofs.tex §"Soundness of Subtyping")

```
thm:sound-subtyping
 ├─ L-A  decorating-algorithmic-subtyping   a_sub → a_subtag at Ψ=∅   [HARD]
 │    ├─ look-decoration                    (Q ↦ fresh-tagged ψ, Ψ)
 │    ├─ decorate-constraint-solving        (looksub^N inverted into looksub + solvetag)
 │    ├─ solvetag-concat                    (solvetag splits/joins over ++)
 │    ├─ subtyping-decoration-var           [the ~150-line core, tex:176-483]
 │    ├─ subtyping-decoration               [the ~420-line core, tex:542-962]
 │    ├─ vacuous-subtyping-decoration, look-output-fresh,
 │    │  constraint-collection-stable-substitution, look-decoration-replacement
 │    └─ (mirrors of the consistency decoration lemmas, which exist:
 │        a_consis_decorate_gen — use as the template)
 └─ L-B  sound-decorated-subtyping          a_subtag → ⊴ + fill(P0) + ad_pat_sub
      ├─ mutual with sound-decorated-flex-subtyping (a_sub_flex walk)
      └─ every consistency premise = a_consistag_sound_aux   [Qed ✓]
```

L-B is a straightforward induction *given* (D1) and the ⊴-stability kit; its
Check/Infer/Arrow cases feed `a_consistag_sound_aux`'s conclusions
(`⊴`, wf, `ad_pat_consis`, `ad_refine_*_f`) into the `ad_pat_sub`
constructors; the `_f`-hygiene conjuncts discharge by `*_f_forget`.  The
ForallR case re-attaches a rigid head — the L8-style head-preservation lemma
pattern from `prop_consis_rename.v` applies.

**Definition fix (2026-07-18): the decorated flex walk.**  `a_subtag`'s
FlexMono premise originally re-entered the *plain* `a_sub_flex` (whose
premises re-enter plain `a_sub`), which leaves L-B's flex case without a
decorated subderivation to recurse on.  The paper's decorated system is
self-contained — `lemma:sound-decorated-flex-subtyping`'s Flex-Solve premise
is an `asubtag` (tex:1119-1135); the figure merely omits the walk as
"trivial".  Fixed: `a_subtag_flex` is now mutual with `a_subtag`
(def_decorated.v), mirroring `a_sub_flex` with the Flex-Solve re-entry at
decorated `Ψ = ∅`.  It stays a SEPARATE mutual judgment (not extra
`a_subtag` cases): the walk carries the `Θ0 ∣ Ξ` split and an atom subject,
and folding it into the main judgment would let the walk's recursive
occurrences re-match the FlexMono entry and discard `Ξ` (the documented
`a_sub_flex` hazard).

**L-B statement shape** (mirror `a_consistag_sound_aux`):
```
a_subtag_sound_aux :  Θ0 ⊢ᵗ[NM|M|P0|Ψ] S ⊑ Q ⊣ Θ1 ->
  a_wf_aenv Θ0 -> lc_uskl S -> Θ0 ⨟ ∅ ⊢ₚₛᵃ P0 -> Θ0 ⨟ ∅ ⊢ₚₛᵃ ⌊S⌋ ->
  Θ0 ⊴ Θ1 /\ a_wf_aenv Θ1 /\
  (exists Qt, bskl_to_pskl Qt = Q /\
     Ψ ⨟ Θ1 ⊢ᵃᵈ[NM|M] S ⊑ Qt /\
     ad_refine_syn_f ∅ Θ1 ∅ (pskl_to_bskl_inh P0) Qt)
```
mutual (via `Scheme`) with the flex conclusion at `(Ξ ++ Θ0) ⊴ Θ1` and
subject `uskl_var_f α`.  Case notes: Flex-Solve builds the ⊴ for the
deposited `α̂0 := α̂→β̂` exactly as plain `a_assign_sound`'s SolveM case does
(`a_isub_prepend_decls_src` + target-weaken, prop_consis_sound.v:2588-2610),
and its `ad_pat_sub` conclusion is `ad_pat_sub__flex_mono` off the IH's
arrow subtyping (`ptyp_to_uskl_syn (α→β)` is definitionally the premise
subject).  Flex-Assign needs a fold-def transport on the fill conclusion
(the `[τ/β̂]`-fold family; `ad_refine_syn_f_unfold_def_source` is the
unfold direction — the fold direction may need writing).

L-A is the hard half of soundness and is ~all-greenfield: it needs the first
real metatheory of `a_looksub`/`a_solve_*`/`a_extract` (§3 gap list) plus the
tag-solving accounting (`a_solvetag_sub`, `a_solvetag`).  The paper's own
account of the crux: "when we do instantiation, all tags introduced by the
type used for instantiation are solved."

### 2.2 Completeness (subtyping-proofs.tex §"Completeness of Subtyping")

Generalized statement (tex:3050-3074): given the problem, a tag context Ψ, an
unresolved `S` with `⌊S⌋ = P`, and a solution `(Θ0 ≤[κ] Θ; Q)`:

```
⌊S⌋ = P    ad_pat_sub^N_M[Ψ] Θ ⊢ syn(κS) ⊑ bid Q    Θ ⊢ inh(κP0) ⋈syn bid Q
⇒ ∃ P1 Θ1 κ1,  a_sub^N_M[P0] Θ0 ⊢ P ⊑ P1 ⊣ Θ1  ∧  Θ1 ≤[κ1] Θ
               ∧  Θ ⊢ κ1P1 ⊑ Q (precision)  ∧  a_inc_equiv Θ0 κ (κ1) Θ
```

(Note the mech statement will phrase `κ ≡ ζ∘ρ1`-style factoring through the
id-witness exactly as `a_consis_complete` does — reuse that statement
shape verbatim, replacing the `ad_precise_f` conjunct with plain precision.)

```
thm:complete-subtyping (generalized)
 │  induction: lex (height of the ad_pat_sub derivation, |Ψ|),
 │  mutual with complete-flex-subtyping (induction on contexts Θ0∣Ξ)
 ├─ case P = α̂ flexible, M = FN M'  → complete-flex-subtyping
 ├─ Infer / Check / UnivGhostR      → a_consis_complete   [Qed ✓]
 ├─ ForallR                         → IH + fill-inversion + rigid-head re-attach
 ├─ Arrow                           → a_consis_complete (premise 1)
 │                                    + a_inc_equiv transport + IH (premise 2)
 ├─ ForallL                         → complete-look → complete-constraint-
 │                                    collection-solving(-var)  [THE core]
 │                                    + partial-precision-complete
 │                                    + precision-substitution
 └─ Ghost / GhostG / UnivGhostL(G)  → routine
```

- **complete-constraint-collection-solving** (tex:2203): induction on the
  declarative derivation of `(syn κS)[syn ψa/α] ⊑ bid Q`, producing the
  `a_looksub` run, the `a_solve_cstr` result `Pa`, `κa`, and *partial
  precision* `Θ ⨟ Δ ⊢ κaPa ⊑[Ψi,Ψa] ψa`.  Its `-var` variant (tex:1697)
  additionally threads a rigid-variable substitution ρ.  These are the
  subtyping analog of the assign walk — sized like `assign_complete_step`.
- **complete-look** (tex:2730): assembles look = collect ∘ solve ∘ guess.  The
  `guess^TY` sub-induction ("construct κa by extending κs to map each flexible
  in Ξ' to the corresponding type in ⌊ψa⌋ based on its position") is
  *exactly* the `guess_join_witness` pattern already Qed in the join file —
  same increment-transformer trick, same freshness bookkeeping.
- **complete-flex-subtyping** (tex:2835): the `a_sub_flex` walk.  Flex-Solve
  deposits `α̂0 := α̂→β̂` — the analog of consistency's Flex-Solve, closed via
  the mono bridge (`consis_mono_join`-style inversion gives `κα̂0 ≡ᵗ τ1→τ2`);
  Flex-Assign is the `[τ/β̂]`-substitution back-edge (analog of Assign-Assign,
  closed recipe: `a_inc_mid_strip_flex_def` + `msubst_pskl_subst` +
  `a_inc_equiv_msubst_pskl` transport); Depend/Skip/SkipRigid are the
  Ξ-reassociation / mid-strip cases (closed recipes; **no V-measure needed**
  since the induction is on the context list, not a size).

---

## 3. Reuse map (what is already Qed, by consumer)

### 3.1 Black boxes (invoke, don't reprove)

| paper use | mech lemma | file |
|---|---|---|
| thm:complete-consistency (4 case families) | `a_consis_complete`, `consis_complete`, `complete_mu` | prop_consis_complete.v |
| sound-decorated-consistency | `a_consistag_sound_aux` (decorated), `a_consis_sound(_aux)` | prop_consis_sound.v |
| decorating-algorithmic-consistency | `a_consis_decorate(_gen)` — the *template* for L-A | prop_decorate.v |

**Interface friction — RESOLVED (2026-07-18): the third premise is the
PAPER'S OWN, and the subtyping solution notion needs the same repair.**
The mech consistency-completeness demands `ad_refine_pskl_f ∅ Θ ∅ (κP) Qb`
(subject-side refinement).  This is *not* a mech artifact: the paper's proof
opens by **augmenting the definition of a solution** to require three
conditions — the join, the `P0`-fill at Δ₁, **and**
`skctx[Δ2]{Θ} κ⌊S⌋ ⋈ Q` (consistency-proofs.tex:2230-2242) — and the
standalone 2-condition Definition of consistency solutions is *commented
out* in algorithmic.tex.  So `a_consis_complete` is faithful to the
paper's proof-level statement.

Deriving the third condition from the other two is **FALSE**:
`(P0 = ∀X.X, P = ∀X.◇, Q = ∀X.X)` satisfies join + fill (the join's hole
rule checks the fill's wf over the *binder-extended* Θ, and the fill's `X`
sits at a concrete — not hole — position of `P0`), but the subject
refinement fails (`ad_refine_pskl`'s hole rule demands
`Θ ⨟ ∅ ⊢ₚₛᵃ fill`), and the algorithm is stuck on it (`a_consis__ghost`
carries `Δ2 ∩ ftv(fill) = ∅`, and the ∀-step puts the binder in both Δs) —
so completeness against the 2-condition notion is genuinely false.

**Consequence for the assembled subtyping theorem ([paper-gap], flag to
WT):** the ACTIVE subtyping-solution Definition (algorithmic.tex:1423-1437)
has only two conditions, and the same capture transplants to it: at `TI`,
`(P0=◇, P=∀X.◇, Q=syn ∀X.X)` passes `typsub`-Infer + the `P0`-fill, yet the
required optimality conclusion `κ(∀X.◇) ⊑ ∀X.X` is underivable (⊑'s hole
rule forbids capture) — thm:complete-subtyping as literally stated is
false on it (hand-derivation in docs/PAPER-GAPS.md — no cex file needed:
the mech follows the paper's proof-level statements here, so nothing rests
on the refutation being formal).  Repair: state the subtyping theorems against
refinement-valid solutions (add `Θ ⊢ κ⌊S⌋ ⋈ Q`-style subject data to the
solution/motive, threading it through the induction exactly as
consistency's augmented statement does); soundness already yields the
condition for every algorithmic output (`a_consis_sound`'s
`⊢ᵣₚᵃᵈ` conjunct), so the pair still characterizes the algorithm exactly:
it succeeds iff a valid solution exists and is ⊑-optimal among valid
solutions.  A restricted derivation lemma (join ⇒ subject refinement for
**hole-free** subjects — the TY-mode call sites) is true and avoids
threading at Check.

### 3.2 Kits (used pervasively; all Qed)

- **msubst algebra** (prop_metasubst/prop_compose):
  `msubst_{ptyp,pskl,bskl}_*`, `msubst_lookup_{app_in,app_notin,mid_drop,notin}`,
  `msubst_ptyp_agree(_inv)`, `msubst_compose_{app,cons_l_id,is_id_r,is_id_r_ext}`,
  `msubst_compose_agree_id`, `dom_msubst_compose`.
- **increments**: `a_inc_{refl_gen,trans,dom_sub,dom_flex,lookup_wf,lookup_mono,
  binds_*, tvar_inv,var_inv,var_skl_inv}`, `a_inc_strip_decls_prefix`,
  `a_inc_mid_strip_flex(_def)`, `a_inc_{tvar,var_skl}_mid_strip_id`.
- **equivalence of increments**: `a_inc_equiv_{refl,trans,glue,lookup,
  msubst_mono,msubst_ptyp,msubst_pskl,self_downarrow}`,
  `a_inc_equiv_mid_insert_{flex,flex_def,var,var_skl,tvar}`,
  `is_id_inc_unique`, `is_id_msubst_mid`, `opt_axiom_factor`.
- **⊴-stability**: `ad_wf_pskl_isub`, `ad_pat_consis_isub`,
  `ad_refine_{syn,pskl}_isub` (prop_stability) — `ad_pat_sub_isub` will join
  this family (same proof skeleton).
- **⇓ / normal forms** (prop_normal): `a_tyequiv_downarrow(_size)`,
  `downarrow_subst_*`, `aenv_msubst_*` — for any ≡ᵗ-invariance argument
  (likely lighter use than in consistency since there is no V-measure here).
- **mono bridge** (prop_mono_bridge): `consis_mono_join`, `refine_mono_join`,
  `tyequiv_mono_consis(_transport)`, `ptyp_to_bskl_syn_inj`,
  `ptyp_to_{uskl,bskl_inh}_syn_eq`, `join_var_tyequiv` (join file) — the
  Flex-Solve arrow-inversion and every "κα̂ is a mono" step.
- **refinement/precision transports** (prop_consis_sound + join file):
  `ad_refine_{syn,pskl}_f_{forget,strip,rename,rename_ctx,isub,delta_mono,
  fmono,weaken_ctx,ctx_to_delta,of_plain,…}`, `ad_precise_f_forget`,
  `skl_tyequiv_{consis,refine_syn_f,refine_pskl_f}_transport`,
  `consis_downarrow_subject`, `consis_precise_via_{join,refine}`.
- **walk-case recipes** (from the closed unify/assign cases; see memory
  [[remech-complete-mu-bundle]] + [[remech-optimality-bundle-progress]]):
  mid-strip → IH/build → mid-insert re-cons; id-witness identification by
  `is_id_inc_unique`; `msubst_compose_cons_l_id` /
  `msubst_compose_is_id_r_ext` collapses.
- **a_guess**: `a_guess_mono_{ftv,decls,flex_binds,consis}` and the
  *increment-transformer* construction pattern of `guess_join_witness`
  (join file §2i) — the model for complete-look's guess induction.
- **decl side**: `d_sub`/`d_pat_sub` weakening/renaming/subst/trans if the
  bridge to the declarative-context statement is ever needed (the appendix
  works entirely in Θ-contexts, so probably only for the final paper-facing
  corollary, mirroring how consistency stayed inside `ad_*`).

### 3.3 Greenfield (no support exists — write from scratch)

1. `a_looksub` basics: output `Ξ` is `a_decls`, wf/ftv of collected
   constraints, determinism/congruence facts as needed (see hazard §4.1).
2. `a_solve_sub` / `a_solve_cstr` basics: wf of outputs, concat behavior
   (paper lemma solvetag-concat's undecorated shadow), interaction with
   substitution.
3. `a_extract` = look ∘ solve ∘ guess: wf of `P1`, freshness of `Ξ`,
   `⌊ψg⌋ = P1` decorations.
4. All `a_solvetag*` metatheory (concat, decoration, replacement).
5. `ad_pat_sub` structural kit: weaken, Δ/Ψ-congruence, isub-stability,
   rename (mirror `ad_pat_consis`'s; ~1 day of mechanical transplant).
6. Partial-precision kit: `partial-precision-complete`
   (⊑[Ψ] + tags-wf ⇒ plain precision) and `precision-substitution`
   (with the height guarantee, §4.3).

---

## 4. Hazards (know before starting)

### 4.1 The paper's "WLOG by congruence" (tex:155-173)
The constraint-collection and decorated-constraint-solving judgments are NOT
syntax-directed; the paper reorders overlapping rule applications by fiat
("WLOG … we use the congruence of these judgements").  In Coq this must become
either (a) explicit commutation lemmas ("if a derivation applies rule X after
Y, there is one applying X first"), or (b) a reformulated, syntax-directed
presentation proved equivalent, or (c) an induction restructured to avoid the
reordering.  This is flagged in the tex itself ("We may want to make the above
more formal").  **Treat as a [paper-gap]: budget real time, and check the
reference implementation (`paper/artifact/implementation/lib/type.ml`) as the
third witness for rule-ordering questions.**

### 4.2 Freshness prose-completion (the F-set lesson)
`a_sub` carries no used-name set `F`, but `a_extract`'s `a_guess` picks fresh
names and `a_subtag__forall_l_*` demands `Ψg ∩ Ψ = ∅` with *chosen* tags.
Consistency needed the F prose-completion (def_extra.v:506-514) because solve
fires below walked-past entries.  Audit early whether the subtyping walk
(`a_sub_flex` re-entering `a_sub` under `Ξ ++ …`) creates the same
name-capture hazard for guessed `Ξ'` names and, if so, add the F index to
`a_sub`/`a_subtag` *before* proving anything (changing it later cascades).

### 4.3 Height-indexed induction
The completeness induction is lex(derivation height, |Ψ|), and the ForallL
case applies the IH to a derivation *produced by* `precision-substitution` —
so that lemma must be proved height-non-increasing.  Concretely: define
`ad_pat_sub_size : … -> nat` (or an inductive `ad_pat_sub_n` with a fuel
index) and prove `precision-substitution` as
`ad_pat_sub_n n … S[ψa/α] … -> ad_pat_sub_n n … S[Pa/α] …`.  Mini design doc
first (the μ-measure experience: get the measure right before the bundle).
Alternative worth 30 minutes of thought: |Ψ| strictly decreases in that step
(Ψ,Ψa → Ψ), so plain lex (height, |Ψ|) with height-*equality* may suffice —
but only if ForallL's premise height is preserved *exactly*, which still
requires the fuel-indexed statement.

### 4.4 External wf side conditions
Several paper statements will look false without the prose wf conditions
(memory [[frost-wf-external-side-conditions]], docs/WF-SIDE-CONDITIONS.md).
E.g. `subtyping-decoration`'s tag accounting silently assumes tag-uniqueness
from wf of ψ; ForallR's fill-inversion needs `P0`'s wf.  Registry discipline:
put transportable conditions on rules, the rest in statements; update the
registry as each is placed.

### 4.5 Statement-shape drift
Follow the consistency statements' shapes exactly where analogous
(`a_consis_complete` for the completeness motive;
`a_consistag_sound_aux`'s conjunct list for L-B): every deviation costs a
transport lemma later.  In particular keep the hygienic `_f` discipline — the
∀-cases of consistency completeness only closed after the precision conjunct
was strengthened to `_f` with `F = Δ1∪Δ2` (memory
[[remech-forall-enablers-and-hygiene]]); expect the same for partial precision
if ForallR/ForallL interact with fills.

---

## 5. Phasing (dependency-ordered)

| phase | content | size feel |
|---|---|---|
| **P1** | Defs: `ad_pat_sub` (+notation), partial precision, subtyping-solution shape; decide D3 (tag-wf) and the §3.1 interface friction; register wf conditions | small, but decisions locked here |
| **P2** | Structural kits: `ad_pat_sub_{weaken,isub,psi_cong,rename}`; partial-precision kit incl. `partial-precision-complete`; `a_looksub`/`a_solve_*`/`a_extract` wf+ftv+decls basics | mechanical, medium |
| **P3** | Soundness L-B: `sound-decorated-flex-subtyping` + `sound-decorated-subtyping` (consumes `a_consistag_sound_aux`) | medium |
| **P4** | Soundness L-A: solvetag metatheory (concat, look-decoration, decorate-constraint-solving) then the two `subtyping-decoration` cores; §4.1 hazard lives here | LARGE |
| **P5** | `precision-substitution` with the height index (§4.3 mini-design first) | medium |
| **P6** | Completeness cores: `complete-constraint-collection-solving(-var)`, `complete-look` (reuse `guess_join_witness` pattern) | LARGE |
| **P7** | `complete-flex-subtyping` (walk recipes transplant) + the generalized theorem assembly + paper-shaped corollaries | medium |

P3 can proceed in parallel with P4 (only shares P1/P2).  P5-P7 are
independent of P4 (completeness does not use decoration), so completeness can
be attacked before soundness's L-A if desired — the reverse of the usual
order, and worth considering since P6 reuses the freshest machinery (the
assign-walk and guess-witness recipes).

---

## 6. Paper-lemma checklist (tex label → planned mech name)

| tex label | mech target | phase |
|---|---|---|
| decorating-algorithmic-subtyping | `a_sub_decorate` | P4 |
| look-decoration | `a_looksub_decorate_output` | P4 |
| decorate-constraint-solving | `a_solve_cstr_decorate` | P4 |
| solvetag-concat | `a_solvetag_app(_inv)` | P4 |
| subtyping-decoration-var | `a_solvetag_sub_decoration_var` | P4 |
| subtyping-decoration | `a_solvetag_sub_decoration` | P4 |
| vacuous-subtyping-decoration | `a_solvetag_sub_vacuous` | P4 |
| constraint-collection-stable-substitution | `a_looksub_subst_stable` | P4 |
| look-output-fresh | `a_looksub_output_fresh` | P2 |
| look-decoration-replacement | `a_looksub_decorate_replace` | P4 |
| sound-decorated-flex-subtyping | `a_sub_flex_tag_sound` | P3 |
| sound-decorated-subtyping | `a_subtag_sound` | P3 |
| partial-precision-complete | `ad_partial_precise_complete` | P2 |
| precision-substitution | `ad_pat_sub_precise_subst` (height-indexed) | P5 |
| complete-constraint-collection-solving-var | `a_solve_complete_var` | P6 |
| complete-constraint-collection-solving | `a_looksolve_complete` | P6 |
| complete-look | `a_extract_complete_gen` | P6 |
| complete-flex-subtyping | `a_sub_flex_complete` | P7 |
| thm:sound-subtyping | `a_sub_sound` | P3+P4 |
| thm:complete-subtyping | `a_sub_complete` | P7 |
