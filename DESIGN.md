# Frost — High-Level Design Notes

A single-page mental model for the mechanization. Lives alongside
[`AGENTS.md`](AGENTS.md) and [`PROGRESS.md`](PROGRESS.md); read this
before touching defs.

## 1. What problem does Frost solve?

Type inference for **first-class polymorphism (FCP)** with both
directions of information flow between functions and arguments,
without backtracking and without ad-hoc heuristics.

Concretely, Frost wants the following all in one system:

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

```
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

```
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

### 2.3 Tags (`epsvar`, `eps`; ranges via `dD : tagctx`)

Tags `ε` are atoms tracking provenance during instantiation. When
subtyping `∀ε α. T ≤ A` triggers via `sub__forall_l`, Frost picks a
**tagged** instantiation `φ` (a synthesised type whose every ∀ carries
a fresh tag). The tag context `Δ` collects every tag the derivation
binds. This is how "no guessing out of thin air" gets enforced: every
quantifier the algorithm conjures up must be tagged, and the typing
context provides its tags.

In the syntax:
- `typ_all_etag eps X. A` — ε-tagged ∀
- `typ_all_col c X. A` — bidirectional ∀ (synthesised or inherited)
- `typ_all_plain X. A` — plain ∀ (e.g., inside skeletons before
  colouring)

The mechanization uses a **single unified `typ` AST** (the language.ott
choice). The six paper "categories" — plain types, tagged types `φ`,
unresolved types `T`, skeletons `P`, tagged skeletons `ψ`, unresolved
skeletons `S` — are **predicates** over `typ`:

| Paper | Predicate          | Allowed ∀'s | Holes? |
|-------|--------------------|-------------|--------|
| `A`   | `is_typ`           | `_plain`    | no     |
| `φ`   | `is_ttyp`          | `_etag`     | no     |
| `T`   | `is_utyp`          | `_etag,_plain` | no  |
| `P`   | `is_skel`          | `_col,_plain` | yes  |
| `ψ`   | `is_tskel`         | `_etag`     | yes    |
| `S`   | `is_uskel`         | `_etag,_plain` | yes  |

Inhabitation predicates: `is_inh_typ`, `is_syn_typ`, `is_inh_skel`,
`is_syn_skel` narrow further by colour.

### 2.4 Skeletons & ghosts

```
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

```
d_wf_typ ⊆ {d_wf_ttyp, d_wf_utyp} ⊆ d_wf_skel ⊆ {d_wf_tskel, d_wf_uskel}
                      │
                      ▼
                 d_consis  ── d_sub  ── d_shallow_sub
                      │         │
                      ▼         ▼
                 d_pat_consis ── d_pat_sub
                      │              │
                      ▼              ▼
                 d_refine_syn    d_refine
                      │              │
                      └──────────────┘
                              │
                              ▼
                          d_typing  ⇄  d_pat       (mutual)
```

Modes appear in `d_sub`, `d_pat_sub`, `d_refine`, `d_typing`, `d_pat`.
Tag contexts `Δ` thread through `d_consis`, `d_sub`, `d_pat_consis`,
`d_pat_sub` (in a "linear use" discipline — disjoint at arrows, singleton
at tagged ∀, empty at unit/var).

The two-context split `Ψ | Γ` shows up only in skeleton-related
judgments (`d_wf_skel`, `d_refine`, `d_refine_syn`). Term-typing
judgments use only `Γ`. `Ψ` tracks variables bound *inside* the
current skeleton; arrow rules thread `Ψ` to both branches; `TopHole`
rules **clear** `Ψ`.

The mutual `d_typing ⇄ d_pat` block exists because:
- `d_typing__app` fires `d_pat` on the argument to grab its skeleton,
  then refines that into the inherited side of the function's arrow.
- `d_pat__app` mirrors the same shape on the skeleton-inference side.

So neither can be defined alone.

### 3.2 Algorithmic judgments (in `frost/algo/def_extra.v`)

Algorithmic syntax extends `typ` with:
- `typ_var_flex_mono monvar` — `α̂`, a unification variable for
  monotypes.
- `typ_var_flex_poly polvar` — `α̌`, a *polymorphic* flex var carrying
  a skeleton assignment.

Algorithmic contexts `Θ` (`aenv`) are ordered lists of `abind`:

```
abind ::= tvar               -- rigid type variable
        | var_typ A          -- term-variable typing
        | flex_mono          -- declared α̂
        | flex_mono_def τ    -- solved α̂ := τ
        | flex_poly_def P    -- declared α̌ ≜ P (skeleton)
        | marker             -- ⫶, scope delimiter for flex-poly
```

The flex-poly assignment is the algorithm's novelty: every `α̌` is
born with skeleton `□` and is refined as constraints arrive.

**Information increase** `Θ₀ ⊑ Θ₁` (paper `Θ₀ → Θ₁` with the
metasubst) preserves variable dependency: `α̂` can become `α̂ := τ`;
`α̌ ≜ P` can become `α̌ ≜ Q` with `P ⟶ Q`; markers and rigid vars are
preserved; suffixes can be appended.

The algorithmic judgments (`a_sub`, `a_pat`, `a_typing`, etc.) take
`Θ₀` as input and produce `Θ₁` as output — they monotonically
*augment* information. **Transfer** `a_transfers Θ Γ` projects an
algorithmic context to its declarative shadow by erasing flex vars
(only feasible when every flex-mono is solved).

The declarative and algorithmic systems are connected by:

- **Soundness** (paper §Type Inference) — every algorithmic judgment
  has a declarative shadow under `a_transfers`.
- **Completeness** (paper §"Subtyping is complete") — every
  declarative derivation can be matched algorithmically (modulo
  flex-var choices).
- **Stability** (paper proofs.tex §1) — declarative judgments are
  preserved under `Θ₀ ⊑ Θ₁` after transfer.

## 4. Why these design choices in the mechanization

The mechanization makes three encoding choices that diverge from the
paper's notation:

1. **One `typ` inductive** (instead of six). Pre-rejected approach:
   six mutually defined inductives. lngen rejected it with "Ambiguous
   type for X". Fix: predicates over a single `typ`. Category-preservation
   under substitution becomes a structural lemma instead of being
   built into the type system.

2. **Predicative contexts** (`list atom` in Set, not `vars : Type`).
   Tag contexts `Δ` and skeleton-scope contexts `Ψ` are plain `list
   atom`. Disjoint-union `Δ₁ ⊎ Δ₂` is encoded as `list_disjoint Δ₁ Δ₂
   ∧ append`. Avoids the multiset machinery the paper's prose hints
   at.

3. **Cofinite-quantification binders via lngen**. Standard for
   locally-nameless mechanization; familiar to anyone who's done
   Metalib proofs.

These are documented in [`language.ott`](frost/language.ott)'s header
comment.

## 5. Cross-check vs current defs

(Audit performed 2026-05-12 against `mech` HEAD.)

### 5.1 Consistencies

- **Modes**: `mode_ti`, `mode_tc`, `mode_fn` match paper's `TI / TC /
  FN M`; `decr_mode` matches `M-`. [`frost/def_extra.v`](frost/def_extra.v):
  ✓
- **Colour-mode compatibility**: `is_syn_typ` / `is_inh_typ` /
  `mode_typ_compat` / `mode_skel_compat` match the paper's `M ⊢ A : TY
  / SK`. ✓
- **Six categories** as predicates: `is_typ`, `is_ttyp`, `is_utyp`,
  `is_skel`, `is_tskel`, `is_uskel`. ✓
- **`guarded_typ` / `guarded_skel`**: a top-level non-∀ check;
  skeleton version additionally rejects `HOLE` and `TOPHOLE` at the
  top. ✓ (matches paper line 220 + 1168)
- **Mutual block**: only `d_typing ↔ d_pat` are mutual; everything
  else stands alone. ✓ (`d_pat` does NOT depend on `d_refine`/`d_pat_sub`
  mutually — paper's typing rules force `d_pat` to inherit the
  refinement/subtyping output from outside, but the proof reading of
  the rules supports a non-mutual `d_refine` etc.)
- **Algorithmic flex-poly with skeleton assignment**:
  `abind_flex_poly_def P` carries a skeleton (paper's novelty
  preserved). ✓
- **`a_transfers` as a relation** (not partial Fixpoint): correct
  choice — flex-mono `Θ`s without definitions have no shadow, so the
  Prop form is cleaner than `option`. ✓

### 5.2 Known tensions (documented in PROGRESS.md, repeated here)

- **`d_pat__abs_check` produces `typ_tophole typ_hole`** which the
  paper's own `d_wf_skel` rejects (paper line 1191). This is a
  paper-level inconsistency, not a mechanization bug. Flagged.

- **Γ↔Ψ "move" lemma**: closing `d_wf_typ → d_wf_skel` (a typ→skel
  bridge) requires rebalancing variables between `Γ` and `Ψ`. The
  paper sketches no proof of this; not attempted.

- **`d_sub_no_guess_uniqueness` (paper line 1102)** sketch: the
  paper itself flags it as "a bit sketchy". A counter-example shape
  is documented inline in [`prop_subtyping.v`](frost/decl/prop_subtyping.v).
  Flagged for paper revision.

### 5.3 Spotted inconsistencies in current defs (FOLLOW-UP)

None of the following are bugs — they're places where the def could
be slightly cleaner without changing semantics:

- **`mode_typ_compat` / `mode_skel_compat` are NOT threaded as
  premises through `d_typing` / `d_pat` rules**. The paper says
  (declarative.tex:435–436) these are "implicitly required as a
  well-formedness condition" — meta-level invariants the typing rules
  preserve, not premises. The mechanization mirrors this slack. As a
  consequence, the lemma `d_typing m Γ e A → mode_typ_compat m A`
  doesn't follow from rule shapes alone; the invariant must be
  established at the toplevel and shown to be preserved (likely via a
  separate regularity lemma if needed).

- **`d_typing__anno` carries `is_inh_typ A`** as a premise (for the
  TC-mode body) but produces `d_typing mode_ti` on the conclusion. By
  `mode_typ_compat`-implicit, the result type ought to be syn-coloured.
  This is consistent IFF the annotation type has no coloured ∀'s
  (i.e. `is_typ A` in our predicate hierarchy — annotation types are
  programmer-written and colour-free). The paper's typing rule reads
  the same `A` in different colours via meta-notation `\inh{A}` /
  `\syn{A}`; the mechanization captures one direction (`is_inh_typ`)
  but relies on the unstated invariant that annotation types are plain
  for the other direction. Not a soundness issue.

- **Wf premises on intro rules** (added in commit `1932f03`):
  `d_typing__abs` / `_abs_anno` / `d_pat__anno` / `d_pat__abs` now
  carry explicit `d_wf_typ Γ A` / `d_wf_skel nil Γ P`. The paper does
  not state these — they're regularity strengthenings the
  mechanization needs to close `d_typing_pat_preserves_wf`. Worth a
  paper footnote.

- **`d_consis__var` lacks a `binds` premise**: paper-flagged. The
  var-case admit in `d_consis_preserves_wf` is direct evidence;
  closing it requires either a `binds X dbind_tvar Γ` premise on
  `d_consis__var` or a side-hypothesis precondition on the lemma.

- **Linearity of tag contexts** is encoded as `list_disjoint` +
  append, not multiset. This is a faithful prosaic reading of the
  paper (`Δ₁ ⊎ Δ₂` = disjoint union) but readers expecting linear
  logic might want a stronger statement. Out of scope for the
  current mechanization.

## 6. Paper Lemma 3.7 — root-cause of the one remaining open admit

Originally three admits, but two were due to a parsing mistake on my
part — see §6.1.

### P1 — `d_pat__sub` case: type/predicate problem (paper omits wf premise)

The rule:
```coq
| d_pat__sub : ... -> d_pat_sub m nil Γ P Q -> d_pat m Γ e Q
```

To derive `d_wf_skel nil Γ Q` we need `d_pat_sub_preserves_wf` (P → Q
preserves wf). That lemma is currently tautological (takes the
conclusion as a side hypothesis). The structural lemma is blocked at
**`d_pat_consis__ghost`**:

```coq
| d_pat_consis__ghost : forall Γ P, no_forall_typ P -> d_pat_consis nil Γ typ_hole P
```

`no_forall_typ P` does NOT imply `d_wf_skel nil Γ P` — it accepts free
variables. The paper's rule (eqlab{Ghost}, declarative.tex:1847)
requires `\syn{∀α} ∉ P` (a syntactic condition on quantifiers) and
**silently assumes P is wf** via the paper's ambient wf invariant.

**Classification:** missing rule premise / type-predicate mismatch.
`no_forall_typ` is the wrong predicate for the wf side. Closing
requires adding `d_wf_skel nil Γ P` to `d_pat_consis__ghost`. Pure
rule strengthening, no semantic change in well-formed scenarios.

### 6.1 Originally-flagged "P2/P3 paper inconsistency" — RESOLVED (was a parsing bug)

I originally read the paper rules at declarative.tex:1620 and 1635 as
producing `(typ_tophole typ_hole) → Q` and `(typ_tophole A) → Q`
respectively, concluding the rules produced shapes that fail wf.

That was a **precedence misreading**. In math notation, `TopHole.X → Y`
parses as `TopHole.(X → Y)` (binder right-associative, like
`∀x. P → Q ≡ ∀x.(P → Q)`). The actual rules produce:

- `\plab{AbsCheck}` (paper:1620): `TopHole.(Hole → Q)`, i.e.
  `typ_tophole (typ_arrow typ_hole Q)`.
- `\plab{AbsAnnoCheck}` (paper:1635): `TopHole.(A → Q)`, i.e.
  `typ_tophole (typ_arrow A Q)`.

The body of each `TopHole` is now an arrow, which IS guarded
(`guarded_skel` accepts arrows). Both wf cases close cleanly via the
existing `d_wf_skel__tophole` rule + bridge lemmas. Fixed in commit
that re-parses the rules. **No paper inconsistency.**

## 7. Metatheory landmarks (current status; admits ≠ done)

| Paper claim | Mechanization | Status |
|---|---|---|
| Subtyping soundness (paper:1095) | `d_sub_sound` | Qed |
| Refinement preserves wf (paper:1380) | `d_refine_preserves_wf`, `d_refine_syn_preserves_wf` | Qed |
| Skeleton wf preservation (paper:1970) | `d_pat_preserves_skel_wf` | Qed (projection) |
| General subsumption (paper:574) | `d_typing_general_subsumption` | base-term cases Qed, others admitted |
| No guessing of polytypes (paper:1102) | `d_sub_no_guess_uniqueness` | admitted (paper-flagged) |
| Validity of skel inference (paper:1981) | `d_pat_validity` | admitted |
| Safety of skel inference (paper:1986) | `d_pat_safety` | admitted |
| Stability (paper proofs.tex §1) | `stability_d_wf_typ`, `stability_d_*` | partial / admitted |
| Algorithmic soundness | `a_sub_sound`, `a_pat_sound`, `a_typing_sound` | admitted (research-grade) |
| Algorithmic completeness | `a_sub_complete`, `a_pat_complete`, `a_typing_complete` | admitted (research-grade) |
| Decidability of `a_sub` | `a_sub_decidable_existential` | narrowed (vacuous-disjunct) |

Honest accounting: only fully Qed-ed lemmas count as done.
PROGRESS.md tracks which lemmas are at which stage.
