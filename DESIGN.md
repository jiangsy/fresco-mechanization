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

In the syntax:

- `typ_all_etag ε X. A` — ε-tagged ∀
- `typ_all_col c X. A` — bidirectional ∀ (synthesised or inherited)

The mechanization uses a **single unified `typ` AST**. The six paper
"categories" — plain types, tagged types `φ`, unresolved types `T`,
skeletons `P`, tagged skeletons `ψ`, unresolved skeletons `S` — are
**predicates** over `typ`:

| Paper | Predicate | Allowed ∀'s | Holes? |
|-------|-----------|-------------|--------|
| `A`   | `is_typ`   | `_col` only | no |
| `φ`   | `is_ttyp`  | `_etag`     | no |
| `T`   | `is_utyp`  | `_etag,_col` | no |
| `P`   | `is_skel`  | `_col`      | yes |
| `ψ`   | `is_tskel` | `_etag`     | yes |
| `S`   | `is_uskel` | `_etag,_col` | yes |

Inhabitation predicates: `is_inh_typ`, `is_syn_typ`, `is_inh_skel`,
`is_syn_skel` narrow further by colour.

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
`d_pat_sub` (in a "linear use" discipline — disjoint at arrows,
singleton at tagged ∀, empty at unit/var).

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

Algorithmic syntax does **not** extend `typ`. A flex variable is an
ordinary type variable (`typ_var_f X`); whether `X` is rigid,
flex-mono (`α̂`), or flex-poly (`α̌`) is recorded **solely by its
binding** in the algorithmic context `Θ`. (Pre-2026-05-15, `typ` had
`typ_var_flex_mono` / `typ_var_flex_poly` constructors — removed for
the same reason `ctyp` has no flex case, see Part 2 §4.4.)

Algorithmic contexts `Θ` (`aenv`) are ordered lists of `abind`:

```text
abind ::= tvar               -- rigid type variable
        | var_typ A          -- term-variable typing
        | flex_mono          -- declared α̂  (X bound here ⟹ X is flex-mono)
        | flex_mono_def τ    -- solved α̂ := τ
        | flex_poly_def P    -- declared α̌ ≜ P (skeleton)
        | marker             -- ⫶, scope delimiter for flex-poly
```

So `α̂` / `α̌` are `typ_var_f X` entries whose `Θ`-binding is
`flex_mono` / `flex_poly_def _`; rigid vars bind `tvar`. The flex-poly
assignment is the algorithm's novelty: every `α̌` is born with
skeleton `□` and is refined as constraints arrive.

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

---

# Part 2 — Mechanization design

## 4. Encoding choices

The mechanization makes four load-bearing encoding choices that
diverge from the paper's notation. Each is documented here with the
*why*.

### 4.1 One `typ` inductive (instead of six)

The paper's six categories (`A`, `φ`, `T`, `P`, `ψ`, `S`) are encoded
as **predicates** over a single `typ` AST (see the table in §2.3).

Pre-rejected: six mutually-defined inductives — lngen rejected it
with "Ambiguous type for X". Fix: single `typ`, predicates layer on
top. Category-preservation under substitution becomes a structural
lemma instead of being built into the type system.

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

### 4.3 Cofinite-quantification binders via lngen

Standard locally-nameless mechanization. lngen generates `prop_ln.v`
with the free-variable lemmas, opening / substitution operators, etc.
Cofinite premises on binder rules (i.e. `forall X, X ∉ L → ...`) are
the norm.

### 4.4 The colourless base `ctyp` + `syn_color` / `inh_color` paintings

The paper writes `syn{A}` / `inh{A}` ambiguously — sometimes as a
*predicate* ("`A` is all-synthesised"), sometimes as a
*transformation* ("paint `A`'s skeleton all-synthesised"). The
mechanization fixes **one uniform rule** built on a genuine
**colourless type** `ctyp`:

```text
ctyp ::= unit | α | ctyp → ctyp | ∀.ctyp | □ | □̇.ctyp
```

`ctyp` is `typ`'s shape with the **two** colour-bearing `forall`
flavours (`typ_all_col`, `typ_all_etag`) collapsed to **one** neutral
binder `ctyp_all`, and **no** flex-var constructors (an algorithmic
flex var is morally a variable, distinguished by its binding in `Θ`,
not by a type former). It is the *free equivalence class* of coloured
types — two coloured `typ`s are *convertible* exactly when they
`erase` to the same `ctyp`. Three functions
([`decl/def_extra.v`](frost/decl/def_extra.v)):

- `syn_color, inh_color : ctyp -> typ` — paint a colourless `ctyp`
  all-synthesised / all-inherited (`ctyp_all` → `typ_all_col
  colour_syn` / `typ_all_col colour_inh`);
- `erase : typ -> ctyp` — forget all colour/tag, projecting onto the
  equivalence class. Round-trips: `erase (syn_color C) = C =
  erase (inh_color C)`.

> Where the paper writes `syn{A}` / `inh{A}` over a meta-symbol `A`,
> the mechanization quantifies **one base `C : ctyp`** and writes
> `syn_color C` / `inh_color C`. Different-colour occurrences thus
> share their shape (the base `C`), painted independently;
> same-colour occurrences are literally the same term. **No**
> `is_syn_typ` / `is_inh_typ` predicates and **no** `syn_color X =
> syn_color Y` equalities — the shared base *is* the shape constraint.

`ctyp` is **never used** as a term annotation, context binding, or
judgement index — those stay `typ`. It appears only as a rule's
shared base variable and as `erase`'s codomain. When a coloured `typ`
`P'` (not a `ctyp` base — e.g. a refinement output) needs an
opposite-colour reading, it goes through `erase`:
`inh_color (erase P')` in `d_typing__app`.

Three situations sit outside the base device, consistently: (1)
**input read-back** — `d_typing__var` reads a `typ` straight out of
`Γ` (already a `syn`-painting, by the invariant that `__abs` /
`__abs_anno` bind `syn_color _`); (2) **`bid` / mode-dependent**
positions (`B` in `__abs` / `__app`) are plain `typ` variables; (3)
**literal tagged-forall constructors** — `d_sub__forall_l_tagged` etc.
match a literal `typ_all_etag ε T`, a structural type former, not a
coloured meta-symbol occurrence.

**`ctyp`'s locally-nameless layer.** `ctyp` is hand-written (it stays
out of `language.ott` / lngen), but it *is* a binder (`ctyp_all`) and
the proof layer does open / substitute it — so `decl/def_extra.v`
carries a hand-written locally-nameless layer for it
(`open_ctyp_wrt_ctyp`, `ftvar_in_ctyp`, `subst_ctyp_in_ctyp`),
mirroring lngen's `typ` operations definitionally so the
`syn_color` / `inh_color` / `erase` commutation lemmas
(`syn_color_open_ctyp`, `erase_open_typ`, `*_subst_ctyp`, …) and the
round-trips (`erase_syn_color`, `erase_inh_color`) line up. So "no
lngen" means "no generated `.v` file for `ctyp`", not "no binder
infrastructure".

The declarative rule definitions were re-encoded to this scheme on
2026-05-15 (see [PROGRESS.md Part 2](PROGRESS.md#part-2-daily-progress)
for the closure log).

### 4.5 The δ-encoding (potential tags `δ ∈ {·, ε}`)

The paper writes a `\sublab{ForallL}`-family of rules with a "potential tag"
`δ ∈ {·, ε}` on the bound quantifier (declarative.tex:778–783):

```text
Potential tags δ ::= · | ε
```

A `syn{∀^δ α.T}` is either **tagged-syn** (`δ = ε`, paper writes
`syn{∀^ε α.T}`) or **untagged-syn** (`δ = ·`, paper writes `syn{∀α.T}`).
The mechanization maps these to two distinct AST shapes:

- `δ = ε ↦ typ_all_etag ε T` (the ε-tagged ∀)
- `δ = ·  ↦ typ_all_col colour_syn T` (the untagged syn-painted ∀;
  post `typ_all_plain` removal this colour-paint is the encoding home
  for "untagged syn ∀", since `typ_all_plain` no longer exists)

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

The same δ split also propagates into the **unresolved-type / unresolved-skel
predicate grammars** (utyp / uskel), since paper's
`utyp T ::= unit | α | T → T | syn{∀^δα.T}` covers both `δ` cases:

- `is_utyp__tall` (tagged) + `is_utyp__pall` (untagged-syn)
- `is_uskel__tall` (tagged) + `is_uskel__pall` (untagged-syn)

**History note.** The 2026-05-15 `typ_all_plain` removal pass mistakenly
dropped the `δ = ·` cases from `d_sub`, `d_consis` (partially),
`d_pat_sub`, `d_pat_consis`, `is_utyp`, and `is_uskel` with the note
"the colour-painted shape isn't `is_utyp`" / "ForallL for that shape
is not paper-faithful". The note was incorrect — the paper IS faithful
to having both `δ` cases. Restoration was done 2026-05-17 (commit
`0bf2815`, WIP); see [PROGRESS.md](PROGRESS.md) for cascade details.

**Rule ordering preference.** In `decl/def_extra.v` the tagged and
untagged constructors of the same paper rule are kept ADJACENT (e.g.
`d_consis__forall_inh_tagged` immediately followed by
`d_consis__forall_inh_untagged`), grouped by paper rule rather than
appended-last. This makes the audit "does Coq cover the paper's δ
spread for rule X?" a one-glance check.

**Rule-body notation.** Notations for the 7 main judgments
(`d_wf_skel`, `d_wf_ttyp`, `d_wf_tskel`, `d_consis`, `d_sub`,
`d_pat_consis`, `d_pat_sub`) are declared as `Reserved Notation` at
the top of `decl/def_extra.v` and bound via `where` clauses on each
`Inductive`. Rule bodies use the notations directly — same reason:
audit-against-paper without translating `d_consis Δ Γ T A` ↔
`Δ ⨟ Γ ⊨ T ≈ A` in your head.

**Consequences for downstream lemmas.** A bunch of `d_consis` /
`d_consis_gen` / `is_utyp` invariants used to ride on the absence of
the δ=· case (typically: "if LHS is syn-paint shape S, then RHS is
also S" or "if X is is_utyp then no typ_all_col"). Adding the δ=·
rules invalidates those invariants. Several lemmas become **provably
false** under the restored encoding — they need precondition
strengthening, not just proof patching. Tracked in
[PROGRESS.md](PROGRESS.md)'s δ-refactor entry.

## 5. Cross-check vs current defs

(Audit performed 2026-05-12 against `mech` HEAD; spot-refreshed
2026-05-17.)

### 5.1 Consistencies

- **Modes**: `mode_ti`, `mode_tc`, `mode_fn` match paper's `TI / TC /
  FN M`; `decr_mode` matches `M-`. ✓
- **Colour-mode compatibility**: `is_syn_typ` / `is_inh_typ` /
  `mode_typ_compat` / `mode_skel_compat` match the paper's `M ⊢ A : TY
  / SK`. ✓
- **Six categories** as predicates: `is_typ`, `is_ttyp`, `is_utyp`,
  `is_skel`, `is_tskel`, `is_uskel`. ✓
- **`guarded_typ` / `guarded_skel`**: a top-level non-∀ check;
  skeleton version additionally rejects `HOLE` and `TOPHOLE` at the
  top. ✓ (matches paper line 220 + 1168)
- **Mutual block**: only `d_typing ↔ d_pat` are mutual; everything
  else stands alone. ✓
- **Algorithmic flex-poly with skeleton assignment**:
  `abind_flex_poly_def P` carries a skeleton (paper's novelty
  preserved). ✓
- **`a_transfers` as a relation** (not a partial Fixpoint): the
  Prop form is cleaner than `option` for flex-mono `Θ`s without
  definitions. ✓

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
  `d_wf_skel nil Γ P`. The paper does not state these — they're
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

Top-line: D1 (`d_typing_general_subsumption_via_gen`) and D12
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
