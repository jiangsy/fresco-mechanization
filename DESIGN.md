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

#### The colour-encoding principle: `ctyp` + the `syn_color` / `inh_color` paintings

The paper writes `syn{A}` / `inh{A}` ambiguously — sometimes as a
*predicate* ("`A` is all-synthesised"), sometimes as a
*transformation* ("paint `A`'s skeleton all-synthesised"). The
mechanization fixes **one uniform rule** built on a genuine
**colourless type** `ctyp`:

```text
ctyp ::= unit | α | ctyp → ctyp | ∀.ctyp | □ | □̇.ctyp
```

`ctyp` is `typ`'s shape with the **three** `forall` flavours
(`typ_all_col`, `typ_all_etag`, `typ_all_plain`) collapsed to **one**
neutral binder `ctyp_all`, and **no** flex-var constructors (an
algorithmic flex var is morally a variable, distinguished by its
binding in `Θ`, not by a type former). It is the *free equivalence class* of
coloured types — two coloured `typ`s are *convertible* exactly when
they `erase` to the same `ctyp`. Three functions (`def_extra.v`):

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
2026-05-15 — see [PROGRESS.md](PROGRESS.md) "colour re-encoding" for
the per-rule table and the proof-repair status.

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

Algorithmic syntax does **not** extend `typ`. A flex variable is an
ordinary type variable (`typ_var_f X`); whether `X` is rigid,
flex-mono (`α̂`), or flex-poly (`α̌`) is recorded **solely by its
binding** in the algorithmic context `Θ`. (Pre-2026-05-15, `typ` had
`typ_var_flex_mono` / `typ_var_flex_poly` constructors — removed for
the same reason `ctyp` has no flex case, §2.2 / §4.4.)

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

4. **Colour disambiguation via a colourless `ctyp`** (§2.2). The
   paper's `syn{A}` / `inh{A}` notation is overloaded (predicate
   vs. transformation); the mechanization fixes one uniform reading —
   a genuine colourless type `ctyp` (the *free equivalence class* of
   coloured types), with `syn_color` / `inh_color : ctyp -> typ`
   painting a shared base and `erase : typ -> ctyp` projecting onto
   the class. Every coloured occurrence of a meta-symbol is
   `syn_color C` / `inh_color C` over one shared base `C : ctyp`. No
   `is_c` predicates, no shape-equality premises. `ctyp` is the *one*
   place the mechanization adds a second type-like inductive — kept
   out of `language.ott` / lngen, but with a small **hand-written**
   locally-nameless layer in `decl/def_extra.v` (`open_ctyp_wrt_ctyp`,
   `ftvar_in_ctyp`, `subst_ctyp_in_ctyp` + commutation lemmas) because
   the proof layer opens and substitutes it. Rule definitions were
   re-encoded to this on 2026-05-15 (see PROGRESS.md).

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

- **`d_typing__anno` colour mismatch — RESOLVED 2026-05-15.** The rule
  used one variable `A` (`is_inh_typ`) for the premise, term annotation
  *and* the conclusion, where the paper concludes `syn{A}` not
  `inh{A}`. Re-encoded per §2.2: one colourless base `A : ctyp`,
  premise + term annotation at `inh_color A`, conclusion at
  `syn_color A`. (Part of the colour re-encoding — see PROGRESS.md;
  proofs not yet repaired.)

- **Wf premises on intro rules** (added in commit `1932f03`):
  `d_typing__abs` / `_abs_anno` / `d_pat__anno` / `d_pat__abs` carry
  explicit `d_wf_typ Γ A` / `d_wf_skel nil Γ P`. The paper does
  not state these — they're regularity strengthenings the
  mechanization needs to close `d_typing_pat_preserves_wf`. Worth a
  paper footnote. (After the 2026-05-15 re-encoding the `d_typing__abs`
  / `_abs_anno` wf premise is on `inh_color A` / `syn_color A` for the
  `ctyp` base `A`.)

- **`d_consis__var` lacks a `binds` premise**: paper-flagged. The
  var-case admit in `d_consis_preserves_wf` is direct evidence;
  closing it requires either a `binds X dbind_tvar Γ` premise on
  `d_consis__var` or a side-hypothesis precondition on the lemma.

- **Linearity of tag contexts** is encoded as `list_disjoint` +
  append, not multiset. This is a faithful prosaic reading of the
  paper (`Δ₁ ⊎ Δ₂` = disjoint union) but readers expecting linear
  logic might want a stronger statement. Out of scope for the
  current mechanization.

## 6. Paper Lemma 3.7 — closed via the colour discipline (was open)

**Status: Qed-closed** at the paper-faithful signature
([`d_pat_preserves_skel_wf`](frost/decl/prop_skeleton.v):
`d_pat mode_tc Γ e P → d_wf_denv Γ → d_wf_skel nil Γ P` — no extra
premises). Closure took several iterations and bottomed out at a
*methodological* insight rather than a structural patch — see §8.

### What looked like the obstacle (it wasn't)

The `d_pat_consis__univ_ghost_inh1` rule recurses on Γ-extension while
`d_wf_skel__all_col` recurses on Ψ-extension. At a `typ_tophole`
boundary, Ψ gets stripped while Γ survives. So a derivation that
introduces α into Γ during d_pat_consis can produce an output ∀α.P
where the wf-check (which rebinds α in Ψ) fails because α is under a
tophole. A concrete counter-example exists at the standalone-rule
level: input `TopHole.(Hole → Unit)`, output
`∀α. TopHole.(α → Unit)` — d_pat_consis derives it, wf rejects it.

I diagnosed this as a "paper-level Γ↔Ψ tension" needing rule changes.

### What the actual obstacle was

The d_pat_consis rule *can* derive the bad shape **in isolation**, but
the *only* contexts in the typing system that invoke d_pat_consis are
`d_pat_sub__infer` and `d_pat_sub__univ_ghost_r`, both of which carry
`is_syn_skel P` as an explicit rule premise. `is_syn_skel` rejects
`typ_all_col colour_inh` at the top — exactly the shape the
counter-example produces. So the bad derivation can be *built*, but
it **can never be plugged into a typing-context use of d_pat_consis.**

The paper's informal proof of Lemma 3.7 implicitly relied on this
contextual constraint. Mechanically, the fix is to surface it on the
helper lemma:

```coq
Lemma d_pat_consis_preserves_wf :
    d_pat_consis Δ Γ SS P -> is_skel SS -> wf(SS) ->
    is_syn_skel P ->                                    (* the call-site contract *)
    wf(P).
```

The previously-admitted `__univ_ghost_inh1` case is now closed by
inversion of `is_syn_skel` on the output.

### The shape of the fix

1. `d_pat_consis_preserves_wf` and `d_pat_sub_preserves_wf` strengthened
   with `is_syn_skel P` (call-site contract surfaced).
2. `d_wf_denv__skel` strengthened with `is_skel P` (already true of every
   constructor of dbind_skel-entries; we made it explicit).
3. Auxiliary lemmas: `d_pat_sub_implies_is_syn_skel` (mode_tc / mode_ti),
   `d_pat_base_mode_ti_is_skel` (d_pat output for base terms at mode_ti).
4. Mutual `d_typing_pat_preserves_wf` conditions its d_pat side on
   `(m = mode_tc ∨ m = mode_ti)` — implementation detail.
5. **`d_pat_preserves_skel_wf` corollary at mode_tc, no extra premises** —
   matches the paper's signature exactly.

The top-level paper-facing lemma carries no new premises. The premises
appear only on internal helpers, where they reflect the colour
discipline the paper proof's narration was already using.

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

> ⚠️ **As of 2026-05-15 the build is RED** — the colour re-encoding
> (`ctyp`) and the `typ` flex-var removal changed core rule shapes, so
> the proof layer is mid-repair (`def_extra.v`, `prop_basic.v`,
> `prop_wellformed.v` compile; `prop_subtyping.v` partway;
> `prop_typing.v` / `prop_skeleton.v` / `algo/prop_*` not yet). The
> "Status" column below reflects the **pre-re-encoding** state and is
> the *target* the repair restores, not the current build. See
> PROGRESS.md "colour re-encoding".

| Paper claim | Mechanization | Status (pre-re-encoding target) |
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

## 8. Proof debugging methodology — read through the colour/mode lens

A general lesson from the Lemma 3.7 closure (§6): **when a metatheory
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
| consistency RHS appears non-wf | `is_syn_skel P` on the calling d_pat_sub rule | Lemma 3.7 (§6) |
| d_typing__sub takes arbitrary B | `is_base_term e` (paper restricts to base terms) | general-subsumption (§7) |
| forall-introduction in TI mode | `is_value e` (value restriction) | d_typing__forall |
| arrow-position pattern coerces freely | `mode_fn m` (function-position mode) | d_pat_sub__arg |
| skeleton input to a refinement rule | `is_inh_skel` / `is_syn_skel` matching colour expectation | d_refine_* family |

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

- Lemma 3.7 (§6) — closed by reading the colour discipline at the
  d_pat_consis call sites.
- Lemma D.3 / suffix-moving — closed via `d_typing_pat_ctx_morph`
  because the structural reordering preserves *all* bindings, which
  the morph captures uniformly.
- The 9 stability lemmas — closed via tvar-morph helpers + the
  binding-preservation invariant of `aenv_extends`.

### Where this lens is likely to pay off next

- **General subsumption (paper Lemma 3.1)** non-base cases: the
  `is_base_term e` premise on `d_typing__sub` is the analogue of
  `is_syn_skel P` in §6. The non-base cases need either restructuring
  through the rule that introduced the non-base term, or a paper-level
  generalisation of `d_typing__sub`.
- **Validity / Safety of skeleton inference (3.8 / 3.9)** — the
  refinement reflexivity on *guarded* skeletons is exactly the kind
  of side-condition that the colour discipline supplies; look at
  the d_refine_syn rules' guardedness premises.
- **Algorithmic stability lemma chain** — colours and modes survive
  algorithmically; many "obvious" stability claims should reduce to
  the same morph + discipline trick.
