# Frost — High-Level Design Notes

A single-page mental model for the mechanization. Two parts:

- **[Part 1 — Frost calculus design](#part-1--frost-calculus-design)** — the
  paper-level design: what problem Frost solves, the four mechanisms,
  the judgment families. Read this if you want to understand the
  *calculus*.
- **[Part 2 — Mechanization design](#part-2--mechanization-design)** — the
  encoding decisions, methodology, and rationale for known gaps. Read
  this if you want to understand the *Coq files*.

Lives alongside [`AGENTS.md`](AGENTS.md) (ground rules + dirs) and
[`PROGRESS.md`](PROGRESS.md) (per-lemma status). Status numbers
(per-lemma admit lists, daily progress) live in PROGRESS.md and are
NOT duplicated here.

---

# Part 1 — Frost calculus design

## 1. What problem does Frost solve?

Type inference for **first-class polymorphism (FCP)** with both
directions of information flow between functions and arguments,
without backtracking and without ad-hoc heuristics.

Concretely, Frost wants all four of the following in one system:

1. *Function → argument* — `poly (λx. x)` where `poly : (∀a. a→a) → Int`
   propagates `∀a. a→a` inward to type-check `λx. x`.
2. *Argument → function* — `head ids` where `ids : List (∀a. a→a)`
   needs the type of `ids` to instantiate `head : ∀a. List a → a` at
   the polytype `∀a. a→a`.
3. *Argument → function → other arguments* — `choose ~id (λx. x)`
   funnels information through the function as a bridge.
4. *Polymorphic instantiation* without guessing polytypes out of thin
   air — every guessed quantifier must be *justified by inherited
   information*.

Bidirectional typing alone handles (1). Local type inference handles
parts of (2). Frost handles all four uniformly via **skeletons +
colours + tags + modes**, with a term-level **freezing** operator as
an escape hatch.

## 2. The four mechanisms

### 2.1 Modes (`mode`, `m`)

```text
M ::= TI | TC | FN M
```

- `TI` (synthesis), `TC` (check) — bidirectional typing's two modes.
- `FN M` — "this position is a function applied to one more argument,
  whose continuation runs in mode `M`". `FN (FN TI)` is a function
  applied to two arguments. So `FN^k M` tracks the depth of curried
  applications.

Mode decrement `M-` strips one `FN`: `TI- = TI`, `TC- = TC`, `(FN M)- = M`.

Modes track **program structure** (depth in function position), not
information flow directly. They tell subtyping / refinement *when*
instantiation is allowed (`M ≠ TI` in `forall_l`).

### 2.2 Colours (`colour`, `c`)

```text
c ::= S | I
```

Quantifiers in *bidirectional* types carry a colour:

- `∀^S α. A` — **synthesised** quantifier (came from a term we typed)
- `∀^I α. A` — **inherited** quantifier (came from the context)
- `∀α. A` — **plain** (used in non-bidirectional positions)

Only quantifiers are coloured; monotypes are uncoloured. Colours are a
*reasoning aid* — programmers never write them. The compatibility
predicate `is_syn_typ` / `is_inh_typ` says all ∀'s in a type are S /
all I respectively.

The mode-colour invariant `mode_typ_compat M A`:

- `TI` requires `is_syn_typ A`
- `TC` requires `is_inh_typ A`
- `FN M` requires arrow shape with bidirectional argument and
  recursive constraint on the result.

So the type's colour profile is determined by the mode it sits under.

> The mechanization's encoding of "the same `A` in two different
> colours" (the paper's `syn{A}` / `inh{A}` overload) is documented
> in [Part 2 §4.4](#44-the-colourless-base-ctyp--syn_color--inh_color-paintings).

### 2.3 Tags (`epsvar`, `eps`; ranges via `dD : tagctx`)

Tags `ε` are atoms tracking provenance during instantiation. When
subtyping `∀ε α. T ≤ A` triggers via `sub__forall_l`, Frost picks a
**tagged** instantiation `φ` (a synthesised type whose every ∀ carries
a fresh tag). The tag context `Δ` collects every tag the derivation
binds. This is how "no guessing out of thin air" gets enforced: every
quantifier the algorithm conjures up must be tagged, and the typing
context provides its tags.

In the current mechanization the paper categories are separate generated
syntax categories rather than predicates over one AST:

| Paper | Coq category | Allowed ∀'s / ghosts |
|-------|--------------|----------------------|
| `A`   | `ptyp`       | plain `∀`; no holes |
| `B`   | `btyp`       | bidirectional `∀^S` / `∀^I`; no holes |
| `C`   | `utyp`       | unresolved `∀^S` / `∀^ε`; no inherited ∀ |
| `G`   | `gutyp`      | generalized unresolved `∀^S` / `∀^I` / `∀^ε` |
| `P`   | `pskl`       | plain skeletons with holes / topholes |
| `Q`   | `bskl`       | bidirectional skeletons |
| `R`   | `uskl`       | unresolved skeletons |

The rule statements use these categories directly.  Predicates such as
`is_styp`, `is_ityp`, `is_ttyp`, `mono_ptyp`, and the guarded predicates
are now refinements of already-split categories, not substitutes for the
categories themselves.

### 2.4 Skeletons & ghosts

```text
Skeletons P, Q ::= □ | α | P → Q | ∀α.P | TopHole.P
```

Skeletons are types extended with two ghosts:

- **`HOLE`** (paper `□`) — an unknown atomic type.
- **`TOPHOLE.P`** (paper `□̇.P`) — an unknown prefix of universal
  quantifiers followed by a guarded `P`.

A skeleton is a **shape extracted from a term, independent of the
context**. The pattern of `λx.x` is `TopHole.□→□`: any function type,
modulo unknown top-level quantifiers. The pattern of `ids` is
`TopHole.List (∀a.a→a)`: a `List (∀a.a→a)` possibly with implicit
top-level quantification.

Skeleton **refinement** `P ⟶ Q` fills ghosts in `P` to get `Q`. The
two-level context `Ψ | Γ` tracks variables: `Ψ` is the scope inside
the *current* `TopHole`-block; `Γ` is the outer term context. `TopHole`
clears `Ψ` (universal-ghost contents cannot mention `Ψ`-vars).

**Coloured refinement** `inh{P} ⟶ bid{Q}` fills inherited skeletons
with synthesised continuations — the bridge from skeleton inference's
output to typing's input in the `App` rule.

### 2.5 Freezing

`freeze e` forces `e`'s type to be exactly what synthesis produces —
no implicit instantiation, no implicit ∀-introduction. It switches
mode from `TI` to `TC` and uses the synthesised type as the *inherited*
type. Used to disambiguate `single id` (returns `∀a. a→a List`) vs
`single ~id` (returns `List (∀a. a→a)`).

## 3. The judgment families

### 3.1 Declarative judgments (in `frost/decl/def_extra.v`)

Roughly the dependency DAG:

```text
d_wf_typ ⊆ {d_wf_ttyp, d_wf_utyp} ⊆ d_wf_pskl ⊆ {d_wf_tskel, d_wf_uskel}
                      │
                      ▼
                 d_consis  ── d_sub  ── d_shallow_sub
                      │         │
                      ▼         ▼
                 d_pat_consis ── d_pat_sub
                      │
                      ▼
                 d_refine_syn
                      │
                      ▼
                          d_typing  ⇄  d_pat       (mutual)
```

Modes appear in `d_sub`, `d_pat_sub`, `d_refine_syn`, `d_typing`, `d_pat`.
Tag contexts `Δ` thread through `d_consis`, `d_sub`, `d_pat_consis`,
`d_pat_sub` (in a "linear use" discipline — disjoint at arrows,
singleton at tagged ∀, empty at unit/var).

The two-context split `Ψ ⨟ Γ` shows up in the skeleton well-formedness
judgments (`d_wf_pskl`, `d_wf_uskl`); `d_refine_syn` is now
**three-context** (`Γ ⨟ Δs ⨟ Δi`). Term-typing
judgments use only `Γ`. `Ψ` tracks variables bound *inside* the
current skeleton; arrow rules thread `Ψ` to both branches; `TopHole`
rules **clear** `Ψ`.

The mutual `d_typing ⇄ d_pat` block exists because:

- `d_typing__app` fires `d_pat` on the argument to grab its skeleton,
  then refines that into the inherited side of the function's arrow.
- `d_pat__app` mirrors the same shape on the skeleton-inference side.

So neither can be defined alone.

### 3.2 Algorithmic judgments (in `frost/algo/def_extra.v`)

The current algorithmic files are **split-syntax placeholders**, not a
faithful mechanization of the algorithmic rules in
`paper/sections/algorithmic.tex`.  They keep the high-level shape of an
algorithmic context and input/output judgments so the repository can
compile while the declarative split-syntax port proceeds, but most rules
are permissive one-constructor stubs.

Algorithmic contexts `Θ` (`aenv`) are ordered lists of `abind`:

```text
abind ::= tvar               -- rigid type variable
        | var_typ A          -- term-variable typing, A : ptyp
        | flex_mono          -- declared α̂
        | flex_mono_def A    -- solved α̂ := A, A : ptyp
        | flex_poly_def P    -- declared α̌ ≜ P, P : pskl
        | marker             -- ⫶, scope delimiter for flex-poly
```

The intended paper-faithful algorithm still needs to restore the
non-trivial information-increase relation, flex-variable solving,
subtyping broom, unification, splitting, algorithmic typing, and
algorithmic skeleton inference.  Consequently the current
`a_*_sound` / `a_*_complete` theorem statements are audit targets, not
validated paper matches; see `PROGRESS.md` for the exact mismatch list.

---

# Part 2 — Mechanization design

## 4. Encoding choices

The mechanization makes four load-bearing encoding choices that
diverge from the paper's notation. Each is documented here with the
*why*.

### 4.1 Split syntax categories

The current `language.ott` generates separate categories for the paper's
type/skeleton strata:

```text
ptyp, btyp, utyp, pskl, bskl, uskl
```

This is the canonical encoding going forward.  Do not add aliases such
as `typ := ...` or old compatibility constructors; rule statements
should be rewritten against the split categories directly.  Where the
paper writes a painted occurrence of a plain type or skeleton, the
mechanization uses explicit conversions from `frost/coercions.v`:

- `ptyp_to_btyp_syn`, `ptyp_to_btyp_inh`
- `ptyp_to_utyp_syn`
- `ptyp_to_pskl`, `pskl_to_bskl_syn`
- erasing/subset embeddings `utyp_to_btyp`, `btyp_to_ptyp`,
  `bskl_to_pskl`, `uskl_to_bskl`

Metavariable convention in comments and statements: `A` for `ptyp`,
`B` for `btyp`, `C` for `utyp`; `P` for `pskl`, `Q` for `bskl`,
`R` for `uskl`.

### 4.2 Predicative contexts (`list atom`)

Tag contexts `Δ` and skeleton-scope contexts `Ψ` are plain `list
atom`. Disjoint-union `Δ₁ ⊎ Δ₂` is encoded as `list_disjoint Δ₁ Δ₂`
plus `++`. Avoids the multiset machinery the paper's prose hints at.

The cost: arrow cases of transitivity-style lemmas like
`d_consis_compose` (paper Lemma B.2) interleave segments
`(Δ₁ ++ Δb1) ++ (Δ₂ ++ Δb2)` vs the natural `Δa ++ Δb`. Worked
around with a `Permutation`-quantified conclusion plus the
`list_swap_middle` helper. Switching to multiset would simplify
this; deferred decision.

**Set semantics for `d_consis` (2026-05-23).** The paper's `Δ` is a *set*
(`declarative.tex:818`): consistency `[Arrow]` combines tags by **set union**
(no disjointness side-condition) and `[ForallInh]` by **idempotent** union (no
freshness side-condition). The mechanized `d_consis` rules had been *stricter*
— `list_disjoint Δ1 Δ2` on `d_consis__arrow` and `~ List.In ε Δ` on
`d_consis__forall_inh_tagged` — which is exactly what made B.2 (consistency
transitivity) un-provable: composing two derivations can legitimately reuse a
tag, which a set absorbs but disjoint-`++` cannot. Both premises were
**dropped** (paper-faithful set semantics). B.2 then closes with a **superset**
conclusion `∃ Δc, incl (Δa ++ Δb) Δc ∧ …`: the superset is *not* slack but
necessary — the **tagged→syn→inh** path (an etag-∀ syn-matched against the
synthesised middle, then inh-matched against the target) mints a tag that is in
the output but neither input. Conversely the middle MUST stay syn (an inh
middle drops a recorded tag, breaking the superset) — and this is faithful,
since the consistency-transitivity middle is always the LHS of the second
consistency, hence synthesised. Proof uses an explicit witness *function*
`compose_tags : utyp → btyp → list atom` (the output Δ as a function of the
endpoints, invariant under the opening variable), which sidesteps the cofinite
"different Δc per opening X" obstruction. The same superset shape now applies
to B.4 (`d_sub_gen_trans{,_ti_lhs}`); `d_sub_gen_trans_btyp_nil` recovers the
nil output for the etag-free `btyp_to_gutyp` LHS that the gen-typing `__sub`
consumes.

### 4.3 Binder freshness: cofinite in `decl/`, EXISTS-FRESH in `algo/`

Standard locally-nameless mechanization. lngen generates `prop_ln.v`
with the free-variable lemmas, opening / substitution operators, etc.

**The canon (decided 2026-07-31, the uniform-encoding campaign).  There
is ONE freshness discipline per layer:**

| layer | discipline |
|---|---|
| `frost/decl/` (declarative judgments, incl. the `decl_algo` mirrors) | **cofinite** — `forall α, α ∉ L → …` |
| `frost/algo/` (the ALGORITHM's own judgments, `a_*`) | **exists-fresh** — one binder α + explicit freshness side conditions |

#### Why the algorithmic layer cannot be cofinite

A cofinite premise demands that ONE choice of the rule's OUTPUTS work
for EVERY fresh binder.  That is fine for a declarative rule, whose
premise has no outputs, and fine for an algorithmic rule that re-binds
the binder in its output (`SS-ForallL`: `∀α.P ⤳ ∀α.P'`, output opened
at the same α).  It is WRONG for an algorithmic rule whose outputs
ESCAPE the binder, because the paper's rule lets them mention it:

```text
\solsublab{ForallR}   solvesub A TC B P'  ⟹  solvesub A TC (∀β.B) P'
\lelab{ForallInh}     lookeq α P P' 𝒞[Ξ] ⟹  lookeq α (∀β.P) (∀β.P') 𝒞[Ξ]
```

Here `P'` / `𝒞` / `Ξ` are produced UNDER the binder and are not re-bound,
so they may carry β.  Rendered cofinitely, the shared output has to be
β-free, and the rule silently degenerates to "fires only when the binder
is vacuous".  This is the bug already found and fixed once at
`a_sub__forall_r` / `a_subtag__forall_r` (PROGRESS 2026-07-31, the junk
suffix Ξ): it broke COMPLETENESS while soundness never noticed, because
soundness only ever CONSUMES the rule.  The same defect is present
throughout the look / solve / guess clusters, which is what the campaign
converts.

#### The shape

```coq
| a_<judgment>__<rule> : forall … β,
    β `notin` <everything in the CONCLUSION that must stay clean> ->
    <premise at β> ->
    <conclusion>
```

The side condition lists the rule's own inputs (`dom Θ`, the input
skeletons' `ftvar_in_*`) and those outputs the judgment's invariants
require to stay well-scoped.  Outputs the paper treats as junk or as
carriers of freshly-generated names — `a_sub__forall_r`'s discarded
suffix `Ξ`, the look's `Ξ ⨾ 𝒞` — are deliberately NOT constrained; that
permissiveness is what makes the encoding as wide as the paper's rule.
Ill-scoped results are filtered downstream by the wf side conditions
that already exist (`a_sub__forall_l`'s `(Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P1`),
not by narrowing the rule.

**No function-valued rule arguments.**  A cofinite family whose output
varies with the binder (`Ξf : atom -> aenv`) was built and rejected
during the ForallR fix: it admits exotic name-dependent outputs and is
unusable in inversions.  Exists-fresh is the decided replacement.

#### The cost, and the staging rule that pays it

Exists-fresh takes binder choice AWAY from consumers: a proof that needs
the binder somewhere specific must MOVE it.  So every cluster is
converted **rename-lemma-first** — the rename must be Qed before the
rule changes, and the tree stays green at every step.  The four assets
that make the campaign executable already exist:

| cluster | rename lemma |
|---|---|
| guess | `a_guess_mono_rename_tvar` (prop_look_complete_extract.v) |
| look | `a_looksub_lookeq_rename_tvar` (prop_looksub.v) — needs `β ∉ ftv 𝒞` |
| solve | `a_solve_sub_eq_rename` (prop_look_complete.v) — fully general, renames the escaping output too |
| consis mutual | `a_assign_unify_consis_rename_tvar` (prop_consis_rename.v) |

The standing recipe for a consumer that pushes a substitution through a
derivation (it needs every binder ≠ the substituted variable, which
exists-fresh does not give) is to RE-FRESHEN ITS OWN variable away from
the rule's α — see `a_subtag_decoration`'s ForallR case, the worked
precedent.

#### What else the campaign folds in

Two further disciplines are being retired into the canon:

- **The `F` avoidance set** — an `atoms` index threaded through the
  whole `a_assign` / `a_unify` / `a_consis` mutual and consumed in
  exactly ONE rule (`a_assign__solve_m`, where the guessed `βs` avoid
  `F ∪ {α} ∪ dom (Ξ ++ Θ0)`), pure pass-through everywhere else.  It is
  deprecated; Solve-M's freshness moves to the canonical side-condition
  form.
- **The walk's prose-Barendregt OUTPUT premises** (`β ∉ dom Θ1` on
  `a_sub_flex__assign` / `__skip` / `__skip_rigid`) — these stay as
  genuine side conditions, and COMPLETENESS discharges them with the
  `a_sub` / `a_sub_flex` run-renaming kit (K1–K4) rather than the rules
  being weakened.  This is the P7a blocker.

### 4.4 Paintings and erasures between split categories

The paper writes `syn{A}` / `inh{A}` as if painting were notation over a
single meta-object.  In the split mechanization, those paintings are
explicit functions from plain syntax:

```coq
ptyp_to_btyp_syn : ptyp -> btyp
ptyp_to_btyp_inh : ptyp -> btyp
ptyp_to_utyp_syn : ptyp -> utyp
ptyp_to_pskl     : ptyp -> pskl
```

Erasure is also explicit:

```coq
btyp_to_ptyp : btyp -> ptyp
bskl_to_pskl : bskl -> pskl
```

The key audit consequence is that paper-facing theorems should not start
from an arbitrary inferred `B : btyp` and then erase/repaint it as a
synthesized unresolved type.  If the paper premise is `syn{A}`, the
native statement should quantify `A : ptyp` and use
`ptyp_to_btyp_syn A` / `ptyp_to_utyp_syn A` directly.  Where a theorem
really must accept an arbitrary `B : btyp`, it needs an explicit
synthesized-shape premise instead of silent erasure.

### 4.5 The δ-encoding (potential tags `δ ∈ {·, ε}`)

The paper writes a `\sublab{ForallL}`-family of rules with a "potential tag"
`δ ∈ {·, ε}` on the bound quantifier (declarative.tex:778–783):

```text
Potential tags δ ::= · | ε
```

A `syn{∀^δ α.T}` is either **tagged-syn** (`δ = ε`, paper writes
`syn{∀^ε α.T}`) or **untagged-syn** (`δ = ·`, paper writes `syn{∀α.T}`).
The split mechanization maps these to two distinct constructors:

- `δ = ε ↦ utyp_all_etag ε C` / `uskl_all_etag ε R`
- `δ = ·  ↦ utyp_all_syn C` / `uskl_all_syn R`

The corresponding bidirectional outputs are `btyp_all_syn`,
`btyp_all_inh`, `bskl_all_syn`, and `bskl_all_inh`.

**Each paper rule with `δ` therefore splits into TWO Coq constructors**
— one per encoding of `δ`. The judgments affected (paper rule ↔ Coq
constructors):

| Paper rule | δ=ε | δ=· |
|---|---|---|
| `\sublab{ForallL}` (Fig 6) | `d_sub__forall_l_tagged` | `d_sub__forall_l_untagged` |
| `\eqlab{ForallInh}` (Fig 6) | `d_consis__forall_inh_tagged` | `d_consis__forall_inh_untagged` |
| `\eqlab{ForallSyn}` (Fig 6) | `d_consis__forall_syn_tagged` | `d_consis__forall_syn` |
| `\sublab{ForallL}` (Fig 12) | `d_pat_sub__forall_l_tagged` | `d_pat_sub__forall_l_untagged` |
| `\textsc{Forall}` (Fig 12) | `d_pat_consis__forall_inh_tagged` | `d_pat_consis__forall_inh_untagged` |
| `\textsc{Forall'}` (Fig 12) | `d_pat_consis__forall_syn_tagged` | `d_pat_consis__forall_syn_untagged` |

The same δ split is now built into the `utyp` / `uskl` grammar rather
than represented as `is_utyp` / `is_uskel` predicate cases.

**History note.** Older docs discuss `typ_all_plain` and a unified
`typ` encoding.  That history is obsolete after the split-syntax port;
new code should use `utyp_all_syn` / `utyp_all_etag` and the skeleton
counterparts directly.

**Rule ordering preference.** In `decl/def_extra.v` the tagged and
untagged constructors of the same paper rule are kept ADJACENT (e.g.
`d_consis__forall_inh_tagged` immediately followed by
`d_consis__forall_inh_untagged`), grouped by paper rule rather than
appended-last. This makes the audit "does Coq cover the paper's δ
spread for rule X?" a one-glance check.

**Rule-body notation.** Notations for the 7 main judgments
(`d_wf_pskl`, `d_wf_ttyp`, `d_wf_tskel`, `d_consis`, `d_sub`,
`d_pat_consis`, `d_pat_sub`) are declared as `Reserved Notation` at
the top of `decl/def_extra.v` and bound via `where` clauses on each
`Inductive`. Rule bodies use the notations directly — same reason:
audit-against-paper without translating `d_consis Δ Γ T A` ↔
`Δ ⨟ Γ ⊨ T ≈ A` in your head.

**Consequences for downstream lemmas.** Invariants must be stated over
the split categories.  In particular, do not prove facts by first
pretending a `btyp` is a `utyp`; when an unresolved synthesized LHS is
needed, either quantify the underlying `A : ptyp` and use
`ptyp_to_utyp_syn A`, or add an explicit synthesized-shape premise on the
`btyp`.

### 4.6 Generalized subtyping (`d_sub_gen`)

The paper's generalized subsumption proof uses a generalized subtyping
judgment whose outer LHS is written as `bid{T}` in
`syntax-directed.tex`; this is a generalized unresolved type, not plain
`btyp`.  The mechanization represents it as `gutyp`, which preserves
ε-tagged quantifiers and also admits inherited quantifiers.

- `Infer`, `Check`, and `ForallR` consume a synthesized/unresolved LHS;
  in Coq these constructors use `utyp_to_gutyp C`.
- `Arg` is the place where generalized bidirectional components appear:
  its domain consistency premise and codomain subtyping premise are over
  `gutyp` components, while the result type remains `btyp`.
- `ForallL` is native to the generalized relation over
  `gutyp_all_etag`; the split syntax also carries the corresponding
  untagged `gutyp_all_syn` case, matching the ordinary δ-erasure split.

The maps `utyp_to_gutyp` and `btyp_to_gutyp` are explicit injections,
not global Coq coercions.  This keeps the existing erasure coercions
(`utyp >-> btyp`, `btyp >-> ptyp`) from competing with the generalized
syntax embedding.

There are no embedding or reflexivity shortcut constructors in
`d_consis_gen` / `d_sub_gen`.  Ordinary cases must be reconstructed by
the native generalized rules, not by an ad-hoc compatibility layer.

This distinction matters.  An earlier scaffold allowed
`gutyp_all_inh ...` as a top-level generalized LHS for `Check`, which
produced a false counterexample to the intended collapse/transitivity
story.  The current mechanization has the checked lemma
`d_sub_gen_top_inherited_lhs_impossible`, so that counterexample is now
classified as a translation bug, not a core issue.  The remaining hard
proof obligation is generalized composition through `Arg`'s
bidirectional arrow components.

## 5. Cross-check vs current defs

(Audit performed 2026-05-12 against `mech` HEAD; spot-refreshed
2026-05-17.)

### 5.1 Consistencies

- **Modes**: `mode_ti`, `mode_tc`, `mode_fn` match paper's `TI / TC /
  FN M`; `decr_mode` matches `M-`. ✓
- **Split categories**: `ptyp`, `btyp`, `utyp`, `pskl`, `bskl`,
  `uskl` are native categories matching the paper strata. ✓
- **Colour/tag distinction**: `btyp`/`bskl` carry synthesized vs
  inherited quantifiers; `utyp`/`uskl` carry synthesized vs tagged
  quantifiers. ✓
- **Mutual block**: only `d_typing ↔ d_pat` are mutual; everything
  else stands alone. ✓
- **Algorithmic flex-poly with skeleton assignment**:
  `abind_flex_poly_def P` carries a `pskl`, matching the paper's
  skeleton-assigned flexible polymorphic variables. ✓

### 5.1.1 Current audit verdict for flagship statements

As of 2026-05-20, the repository builds, but several flagship theorem
statements are **not faithful enough to be claimed as mechanizations of
the paper theorem without qualification**:

| Flagship | Current Coq statement | Paper-faithfulness verdict |
|---|---|---|
| D1 General subsumption | `d_typing_general_subsumption` quantifies `A : ptyp`, assumes `Γ ⊢[TI] e ⦂ ptyp_to_btyp_syn A`, and subtypes from `ptyp_to_utyp_syn A` to `B`. | **Faithful statement shape, proof admitted.** This matches the paper's shared `syn{A}` premise without erasing an arbitrary `btyp`. |
| D12 Generalised general subsumption | `d_typing_general_subsumption_gen` uses `d_typing_gen` and `d_sub_gen` over `btyp`, with `is_fn_n_ti` encoding `FN^n TI`. | **Close in shape, proof admitted.** Missing explicit counterpart of the paper premise `skmod[TY] (FN^n TI) bid{A}`; current `d_sub_gen` is also a compact scaffold, not the full syntax-directed relation. |
| Algorithmic soundness | `a_typing_sound`, `a_pat_sound`, `a_sub_sound`. | **Not faithful.** Current algorithmic judgments are permissive placeholders and `a_transfers` relates any `Θ` to any `Γ`; the theorems are admitted and do not express paper questions/solutions/minimality. |
| Algorithmic completeness | `a_typing_complete`, `a_pat_complete`, `a_sub_complete`. | **Not faithful.** Current statements are declarative-to-algorithmic existence lemmas, not the paper's question/solution minimality theorem. |

### 5.2 Encoding-induced premises (paper-implicit, mech-explicit)

- **`mode_typ_compat` / `mode_skel_compat` are NOT threaded as
  premises through `d_typing` / `d_pat` rules**. The paper says
  (declarative.tex:435–436) these are "implicitly required as a
  well-formedness condition" — meta-level invariants the typing rules
  preserve, not premises. The mechanization mirrors this slack. As a
  consequence, the lemma `d_typing m Γ e A → mode_typ_compat m A`
  doesn't follow from rule shapes alone; the invariant must be
  established at the toplevel and shown to be preserved (likely via a
  separate regularity lemma if needed).
- **Wf premises on intro rules.** `d_typing__abs` / `_abs_anno` /
  `d_pat__anno` / `d_pat__abs` carry explicit `d_wf_typ Γ A` /
  `d_wf_pskl nil Γ P`. The paper does not state these — they're
  regularity strengthenings the mechanization needs to close
  `d_typing_pat_preserves_wf`. Worth a paper footnote. (After the
  2026-05-15 re-encoding, `d_typing__abs` / `_abs_anno` wf premise is
  on `inh_color A` / `syn_color A` for the `ctyp` base `A`.)
- **`d_consis__var` carries a `binds X dbind_tvar Γ` premise**
  (paper-faithful: the paper assumes the wf invariant implicitly).
  Without it, `d_consis_preserves_wf`'s var case is open.
- **Linearity of tag contexts** is encoded as `list_disjoint` +
  append, not multiset. This is a prosaic reading of the paper
  (`Δ₁ ⊎ Δ₂` = disjoint union) but readers expecting linear logic
  might want a stronger statement. Out of scope.

### 5.3 Status of paper claims

[`PROGRESS.md` Part 1](PROGRESS.md#part-1-paper--mechanization-mapping)
is the single source of truth for which paper Lemma / Theorem is in
which Coq file at which status. Don't track per-lemma status here —
it WILL go stale.

Top-line: D1 (`d_typing_general_subsumption`) and D12
(`d_typing_general_subsumption_gen`) were **Qed and "Closed under the
global context"** as of commit `8701b4a` (2026-05-17, pre-δ-refactor).
The in-progress δ-encoding refactor (commit `0bf2815`, §4.5 above)
wholesale-admits `d_consis_gen_trans`, which is transitively used by
the flagship theorems; the closure property therefore needs
re-verification once the refactor's cascade is patched. Phase 3 (algo
soundness / completeness) has scaffolding with HEADLINE admits.

## 6. Proof debugging methodology — read through the colour/mode lens

A general lesson from successive admit-closures: **when a metatheory
lemma in Frost looks "almost-but-not-quite true" structurally, the
right question is rarely "how do I patch the wf rules" and almost
always "which call-site predicate, induced by the calculus's
colour/mode discipline, makes the bad case unreachable?"**

### The discipline, restated

Frost factors "what polymorphic type information can flow where" along
two orthogonal axes:

- **Mode** (TI / TC / Fn m) — *direction* of type-info flow. Standard
  bidirectional skeleton, with `Fn m` being "we're at a function
  position; the next thing is an arrow whose result mode is m".
- **Colour** (inh / syn) — *provenance* of quantifiers. An `inh` ∀ was
  introduced from a checking type flowing *down*; a `syn` ∀ was
  introduced bottom-up by an inference step. Two ∀'s that look
  identical at the AST mean very different things to the system:
  `inh` is committed-against and can't be decomposed freely; `syn` is
  still flexible.

Together these encode the **decidability frontier** of impredicative
polymorphism: checked-against quantifiers are fixed, synthesised ones
are open. Bidirectional information flow is then not just "left ↔
right" but tracks *which* polymorphic types are already-decided vs.
still-open. Frost decides more programs than naive bidirectional
systems because it has finer-grained info per ∀.

### Concretely, how this shows up in proof script gaps

Many rules in this system have *implicit* shape constraints baked
into the colour discipline. A few patterns to watch for:

| structural gap | look for this call-site predicate | example |
|---|---|---|
| consistency RHS appears non-wf | `is_syn_skel P` on the calling `d_pat_sub` rule | Lemma 3.7 (`d_pat_preserves_skel_wf`) |
| `d_typing__sub` takes arbitrary B | `is_base_term e` (paper restricts to base terms) | general-subsumption (D1) |
| ∀-introduction in TI mode | `is_value e` (value restriction) | `d_typing__forall` |
| arrow-position pattern coerces freely | `mode_fn m` (function-position mode) | `d_pat_sub__arg` |
| skeleton input to a refinement rule | `is_inh_skel` / `is_syn_skel` matching colour expectation | `d_refine_*` family |
| `d_consis` LHS shape "looks too permissive" | `d_wf_typ Γ T` to rule out `typ_all_etag` LHS | `d_consis_sub_trans` (D10 / paper B.3) |

A standalone helper lemma that drops one of these contextual
predicates is almost always provably false on isolated derivations,
but provably true when used from within the typing system — because
the typing system's colour/mode discipline forecloses the bad path
at the call site.

### Proof recipe when a wf-style helper "doesn't seem to hold"

1. **Build the smallest counter-example** at the rule level. Don't
   trust narrative arguments — write down concrete SS, P, derivation
   tree, and check whether the conclusion wf-judgement actually
   accepts the output.
2. **Trace upward.** Find every rule that *invokes* the lemma in the
   metatheory. List their explicit and implicit premises. The
   premise that rules out your counter-example is the missing
   precondition.
3. **Surface that premise on the helper**, leaving the top-level
   paper-facing lemma's signature unchanged. The paper's informal
   proof was relying on this premise implicitly.
4. If the top-level lemma's signature itself doesn't admit the
   restriction, the *mode discipline* might. Check whether the
   problematic call site is reachable only at certain modes; an
   internal `m ∈ {tc, ti}` conditioning is fair game (project it
   out as a paper-faithful corollary at the paper's stated mode).

### Concrete payoffs already realised

- **Lemma 3.7** (`d_pat_preserves_skel_wf`) — closed by reading the
  colour discipline at the `d_pat_consis` call sites (worked example
  written up in [PROGRESS.md Part 2](PROGRESS.md#part-2-daily-progress)).
- **Lemma D.3** / suffix-moving — closed via `d_typing_pat_ctx_morph`
  because the structural reordering preserves *all* bindings, which
  the morph captures uniformly.
- **The 9 stability lemmas** — closed via tvar-morph helpers + the
  binding-preservation invariant of `aenv_extends`.
- **D10 / paper B.3** (`d_consis_sub_trans`) — closed via a
  `d_wf_typ Γ T` premise that lets the new helper
  `d_consis_RHS_syn_color_eq` pin the LHS syn-shape (post the
  2026-05-15 `__forall_syn` rule addition).
- **D12** — closed by adding an `Hbody_at_tc` parameter on the SPLIT
  helpers so D12 can construct it from its own IHbody — breaking the
  `lift_mono ↔ D12` cycle without restructuring the inductive.

### Where this lens is likely to pay off next

- **Validity / Safety of skeleton inference (D6 / D7)** — the
  refinement reflexivity on *guarded* skeletons is exactly the kind
  of side-condition that the colour discipline supplies; look at the
  `d_refine_syn` rules' guardedness premises.
- **Algorithmic stability lemma chain** — colours and modes survive
  algorithmically; many "obvious" stability claims should reduce to
  the same morph + discipline trick.
- **Phase 3 soundness / completeness HEADLINES** — these are gated on
  five auxiliary `a_*_sound` / `a_*_complete` lemmas. Each is
  expected to follow the same morph + discipline pattern.
