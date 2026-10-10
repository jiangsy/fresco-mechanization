# Fresco — High-Level Design Notes

A single-page mental model for the mechanization. Two parts:

- **[Part 1 — Fresco calculus design](#part-1--fresco-calculus-design)** — the
  paper-level design: what problem Fresco solves, the four mechanisms,
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

# Part 1 — Fresco calculus design

## 1. What problem does Fresco solve?

Type inference for **first-class polymorphism (FCP)** with both
directions of information flow between functions and arguments,
without backtracking and without ad-hoc heuristics.

Concretely, Fresco wants all four of the following in one system:

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
parts of (2). Fresco handles all four uniformly via **skeletons +
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

### 2.3 Tags (`epsvar`, `eps`; tag contexts `Ψ : atoms`)

Tags `ε` are atoms tracking provenance during instantiation. When
subtyping `∀ε α. T ≤ A` triggers via `sub__forall_l`, Fresco picks a
**tagged** instantiation `φ` (a synthesised type whose every ∀ carries
a fresh tag). The tag context `Δ` collects every tag the derivation
binds. This is how "no guessing out of thin air" gets enforced: every
quantifier the algorithm conjures up must be tagged, and the typing
context provides its tags.

In the current mechanization the paper categories are separate generated
syntax categories rather than predicates over one AST:

| Paper | Coq category | Allowed ∀'s / ghosts |
|-------|--------------|----------------------|
| `A`   | `ptyp`       | plain `∀`; no ghosts |
| `B`   | `btyp`       | bidirectional `∀^S` / `∀^I`; no ghosts |
| `C`   | `utyp`       | unresolved `∀^S` / `∀^ε`; no inherited ∀ |
| `G`   | `gutyp`      | generalized unresolved `∀^S` / `∀^I` / `∀^ε` |
| `P`   | `pskl`       | plain skeletons with ghosts / univ_ghosts |
| `Q`   | `bskl`       | bidirectional skeletons |
| `R`   | `uskl`       | unresolved skeletons |

The rule statements use these categories directly.  Predicates such as
`is_styp`, `is_ityp`, `is_dtyp`, `mono_ptyp`, and the guarded predicates
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
two-level context `Γ | Δ` tracks variables: `Γ` is the context, and `Δ`
records the quantifiers bound inside the skeleton (a ∀ binds its variable
in BOTH). A ∀◇ body is checked at `Γ∖Δ` (universal-ghost contents cannot
mention `Δ`-vars), and a ghost fill must avoid `Δ`. Both sides of a
refinement are presupposed well-formed (the mechanization follows the
paper's rules verbatim since 2026-10-08; see
`docs/WF-SIDE-CONDITIONS.md` §1).  A fill-avoidance set is carried as part
of `Δ`; the mechanization's former internal refinement variants with a
separate set `F` (`ad_refine_*_f`) were removed 2026-10-09.

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

### 3.1 Declarative judgments (in `fresco/decl/def_rules.v`)

Roughly the dependency DAG:

```text
d_wf_typ ⊆ {d_wf_dtyp, d_wf_utyp} ⊆ d_wf_pskl ⊆ {d_wf_tskel, d_wf_uskel}
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
Tag contexts `Ψ` thread through `d_consis`, `d_sub`, `d_pat_consis`,
`d_pat_sub` (in a "linear use" discipline — disjoint at arrows,
singleton at tagged ∀, empty at unit/var).

The two-context split `Γ ⨟ Δ` shows up in the skeleton well-formedness
judgments (`d_wf_pskl`, `d_wf_uskl`) and in refinement (`d_refine_syn`,
`d_refine_pskl`). Term-typing judgments use only `Γ`. `Δ` tracks
variables bound *inside* the current skeleton; a ∀ binds its variable in
both `Γ` and `Δ`; arrow rules thread both to both branches; the ∀◇ wf
rule checks its body at `Γ∖Δ` with an empty `Δ`, and the refinement
Ghost rule asks `Δ ∩ ftv(fill) = ∅`. (Paper rule for rule since
2026-10-08; the earlier encoding put a ∀'s variable in `Δ` only and
checked the ghost fill's well-formedness.)

The mutual `d_typing ⇄ d_pat` block exists because:

- `d_typing__app` fires `d_pat` on the argument to grab its skeleton,
  then refines that into the inherited side of the function's arrow.
- `d_pat__app` mirrors the same shape on the skeleton-inference side.

So neither can be defined alone.

### 3.2 Algorithmic judgments (in `fresco/algo/def_rules.v`)

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
mechanization uses explicit conversions from `fresco/coercions.v`:

- `ptyp_to_btyp_syn`, `ptyp_to_btyp_inh`
- `ptyp_to_utyp_syn`
- `ptyp_to_pskl`, `pskl_to_bskl_syn`
- erasing/subset embeddings `utyp_to_btyp`, `btyp_to_ptyp`,
  `bskl_to_pskl`, `uskl_to_bskl`

Metavariable convention in comments and statements: `A` for `ptyp`,
`B` for `btyp`, `C` for `utyp`; `P` for `pskl`, `Q` for `bskl`,
`R` for `uskl`.

### 4.2 Predicative contexts (atom sets)

Tag contexts `Ψ` and skeleton ∀-scope contexts `Δ` are atom sets
(`atoms`) in every layer, compared with `[=]`, as in the paper.
(`Δ` was a `list atom` in the declarative layer until 2026-10-09; that
list, `delta_agree` and `tvars_denv` are gone, and the conservativity
bridges in `algo_decl/prop_conserv.v` are stated at one Δ.)  The paper's
disjoint union `Ψ₁ ⊎ Ψ₂` is `Ψ [=] Ψ₁ ∪ Ψ₂` plus `Ψ₁ ∩ Ψ₂ [=] empty`
in `d_tags`; the subtyping / consistency arrow rules use plain union
(see below), and ForallL's `fresh Ψ'` is a GLOBAL disjointness side
condition.

The `list atom` encoding of `Ψ` (disjoint `++`, a `Permutation`-quantified
conclusion and `list_swap_middle` in the arrow case of
`d_consis_compose`) is historical; the set encoding retired it.

**Set semantics for `d_consis` (2026-05-23).** The paper's `Δ` is a *set*
(`declarative.tex:818`): consistency `[Arrow]` combines tags by **set union**
(no disjointness side-condition) and `[ForallInh]` by **idempotent** union (no
freshness side-condition). The mechanized `d_consis` rules had been *stricter*
— `list_disjoint Δ1 Δ2` on `d_consis__arrow` and `~ List.In ε Δ` on
`d_consis__forall_inh_tagged` — which is exactly what made B.2 (consistency
transitivity) un-provable: composing two derivations can legitimately reuse a
tag, which a set absorbs but disjoint-`++` cannot. Both premises were
**dropped** (paper-faithful set semantics). B.2 then closes with a **superset**
conclusion `∃ Δc, (Δa ∪ Δb) [<=] Δc ∧ …`: the superset is *not* slack but
necessary — the **tagged→syn→inh** path (an tag-∀ syn-matched against the
synthesised middle, then inh-matched against the target) mints a tag that is in
the output but neither input. Conversely the middle MUST stay syn (an inh
middle drops a recorded tag, breaking the superset) — and this is faithful,
since the consistency-transitivity middle is always the LHS of the second
consistency, hence synthesised. Proof uses an explicit witness *function*
`compose_tags : utyp → btyp → atoms` (the output Δ as a function of the
endpoints, invariant under the opening variable), which sidesteps the cofinite
"different Δc per opening X" obstruction. The same superset shape now applies
to B.4 (`d_sub_gen_trans{,_ti_lhs}`); `d_sub_gen_trans_btyp_nil` recovers the
nil output for the tag-free `btyp_to_gutyp` LHS that the gen-typing `__sub`
consumes.

### 4.3 Binder freshness: cofinite in `decl/`, EXISTS-FRESH in `algo/`

Standard locally-nameless mechanization. lngen generates `prop_ln.v`
with the free-variable lemmas, opening / substitution operators, etc.

**The canon (decided 2026-07-31, the uniform-encoding campaign).  There
is ONE freshness discipline per layer:**

| layer | discipline |
|---|---|
| `fresco/decl/` (declarative judgments, incl. the `decl_algo` mirrors) | **cofinite** — `forall α, α ∉ L → …` |
| `fresco/algo/def_decorated.v` (the DECORATED mirrors — a proof device) | **cofinite** — see "the line is *is it the algorithm?*" below |
| the ALGORITHM's own judgments (`a_sub`, `a_sub_flex`, `a_consis`, `a_assign`, `a_unify`, `a_look*`, `a_solve*`, `a_guess*`, `a_extract`, `a_pat`, `a_typing`) | **exists-fresh** — one binder α + explicit freshness side conditions |

#### The line is "is it the algorithm?", not the directory (decided 2026-08-02)

The campaign's first cut drew the line at `decl/` vs `algo/`.  That is wrong at
one place: `algo/def_decorated.v`'s `a_consistag` / `a_subtag` / `a_solvetag`
live under `algo/` but are **not the algorithm** — the decorated system exists
only to state and prove the decoration and soundness results, nothing ever runs
it, and no implementation corresponds to it.  The reason exists-fresh is FORCED
for the algorithm — a cofinite premise demands that one choice of the rule's
OUTPUTS work for every fresh binder, which the algorithm cannot deliver because
it picks one name from a counter — simply does not apply to a relation that is
only ever inhabited by a proof.  So the decorated mirrors keep cofinite
quantification, like `decl/` and the `decl_algo` mirrors.

**The proviso is leakage**, and the right question is *what does each cofinite
family SHARE?* — the output context `Θ1` above all, since a cofinite premise
demands one `Θ1` for every fresh binder.  Audited rule by rule (cluster 5,
2026-08-02):

| rule | shared across the family | verdict |
|---|---|---|
| `a_consistag`'s five ∀ rows | `Θ1` (premise outputs `(α~tvar) ++ Θ1`, conclusion strips it), `Q` (re-bound), `Ψ` | **machine-checked faithful** — identical shape to `a_consis`'s ∀ rows, whose cofinite ⇄ exists-fresh equivalence cluster 4 proved in BOTH directions (prop_consis_rename.v §9), this output-context shape included |
| `a_subtag__forall_l_*`, the TYPE binder α | `Ξ`, `P1` only — `Θ1` does **not** occur under this quantifier | **machine-checked faithful** — `a_extract_family_of_instance` (prop_looksub.v §11) proves one instance generates the whole family with the SAME `Ξ ↪ P1`, because the look cluster's generated names already avoid the looked-for variable |
| `a_subtag__forall_l_*`, the TAG pack `(Ψg, ψg)` | `Θ1` and `Q` | **assumed, not proved** — see below |
| `a_solvetag_sub/eq`'s four ∀ rows | the tag set `Ψ` only; no context output at all | faithful — a type binder cannot enter a set of ε tags |

(NB `a_consistag` has **five** ∀ rows, not four: `__univ_ghost1` is the exact
mirror of the `a_consis__univ_ghost1` that cluster 4 converted.)

So exactly ONE family shares `Θ1` without a machine check: the tag pack.  Two
things make that safe rather than merely convenient.  First, cofinite is the
STRONGER premise, so it makes the decorated relation **smaller**, never larger —
it can only ever block a PRODUCER, never weaken a consumer's hypothesis.
Second, the decorated judgments are **purely internal**: they appear in no
exported statement (`README.v` mentions neither), and are only ever produced
from `a_sub` / `a_consis` by the decoration lemmas and consumed toward the
declarative system by soundness.  A smaller intermediate therefore cannot weaken
any end-to-end theorem — it can only fail to be constructible, and every
construction is `Qed`.

⚠️ **What the cofinite tag pack is actually buying, recorded for the record.**
The paper's own decorated ForallL writes `\Psi_g \text{ fresh}`
(appendices/decorated-algosub.tex:92) — ONE pack, i.e. exists-fresh.  So the
cofinite rendering is a deliberate mech STRENGTHENING, and it is load-bearing:
`a_subtag_decoration_var`'s ForallL crux inverts the node and rebuilds it at the
ENLARGED tag context `Ψ ∪ Ψa`, which needs `Ψg # Ψa` — and `Ψg` and `Ψa` come
from two independent runs, so no input-only side condition on the rule can
separate them (the TWO-INDEPENDENT-GENERATORS gap, tag instance).  The cofinite
quantifier supplies that by fiat; an exists-fresh pack would have to PROVE it,
which needs either an avoid-set hand-back through both decoration inductions or
a genuine RETAGGING lemma ("a derivation is generic in its inert tag names").
Retagging does not exist and would have to be built from scratch — lngen
generated only `subst_uskl_in_uskl`, no tag substitution on `uskl`.  This is
fine as it stands: the decorated system is a proof device, and a proof device is
allowed to assume more than the algorithm.  It is only worth revisiting if
retagging gets built for another reason.

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

**Rule 1 — the freshness side condition may mention INPUTS ONLY.**  A
rule fires by *choosing* its binder, so it can only avoid things that
already exist at that moment.  A condition naming an OUTPUT ("pick β
avoiding `P'`") is not implementable: the algorithm has not computed
`P'` yet.  So the side condition ranges over `dom Θ` and the
`ftvar_in_*` of the rule's *input* skeletons, and never over an output.

**Rule 2 — where the algorithm re-binds its result, the rule CLOSES
explicitly.**  Dropping an output condition would leave the relation
ambiguous: from a premise output `P'` one could read back either the
properly closed body or a body that still mentions β free (both satisfy
`P'^β = <premise output>`).  The cofinite encoding accidentally forced
the closed reading; exists-fresh must say it.  So:

```coq
(* output re-bound by the algorithm — implementation does [bind_var α] *)
| a_<judgment>__<rule> : forall … P' β,
    β `notin` dom Θ `union` <ftv of the INPUTS> ->
    <premise at β, producing P'> ->
    <conclusion with output (pskl_all_syn (close_pskl_wrt_pskl β P'))>

(* output passed through — implementation DISCARDS the binder name *)
| a_<judgment>__<rule> : forall … P' β,
    β `notin` dom Θ `union` <ftv of the INPUTS> ->
    <premise at β, producing P'> ->
    <conclusion with output P'>          (* β may legitimately ESCAPE *)
```

The `pskl_all_syn` wrapper keeps the closed body's index 0 bound, so the
output stays locally closed.

**The reference implementation is the arbiter of which shape a rule
takes** (`paper/artifact/implementation/lib/type.ml`), and it
distinguishes the two cleanly:

| rule | implementation | shape |
|---|---|---|
| `SolS-ForallL` (:499-505) | `unbind` → recurse → **`bind_var alpha`** | close |
| `guess_mono`'s `TForA` (:88-91) | `unbind` → recurse → **`bind_var v`** | close |
| `SolS-ForallR` (:517-520) | `let _, b = unbind b` → recurse, result **unclosed** | escape |

So `SolS-ForallR` really does let its binder escape into the result —
the paper's rule (full-algo-spec.tex:1271) is faithful, not sloppy, and
the mechanization must not narrow it.  Ill-scoped results are filtered
downstream by the wf side conditions that already exist
(`a_sub__forall_l`'s `(Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ P1`), not by the rule.

⚠️ **Known consequence**: `a_solve_sub_eq_ftv`'s SUB half ("solving
introduces no new free variables", prop_solve_sub.v) is FALSE once
`SolS-ForallR` is faithful, and so is the freshness chain built on it
(`a_solve_cstr_ftv` → `a_extract_output_fresh`).  These must be
restated, not worked around by narrowing the rule.

⚠️ **Second known consequence — WELL-FORMEDNESS is not preserved
either**, and this one is *load-bearing*: the escaped binder is a free
variable of the output that the conclusion's context does not bind
(`cex/cex_solve_sub_wf_leak.v`, `◇ ≼[TC] ∀a.a ⤳ ∀◇b` by SolS-ForallR
then SolS-GhostL — the ghost copies the target, skolem and all).  So a
general "sub-solving preserves wf" lemma cannot exist, and the one the
mech had (`a_solve_sub_wf`) was deleted.  **The paper never needed one**:
its P6-Sv states `Θ₀ ⊢ P_a` among its OWN conclusions
(subtyping-proofs.tex:1737) and proves it inside the induction, carrying
it as `Θ₀,β ⊢ P_a` through the SolS-ForallR row and discharging β there
from `β ∉ ftv ψ_a` plus the PRECISION conclusion (:1897-1900).
`a_solve_sub_complete_var` now does the same.  Two mech-only steps the
paper's single-context `Θ ⊢ P` does not need, both in
prop_look_complete_sub_var.v: the mech checks a ∀◇ body at `Θ∖Δ` (the
paper's two-context rule), so adding a binder to Δ (SolS-ForallL's row)
is legal only for an UNSHIELDED variable — hence
`a_wf_pskl_tvar_to_delta` and `a_solve_sub_eq_unshielded` ("solving does
not shield a context variable the subject leaves unshielded"; the escape
disjunct of `a_solve_sub_ftv` is closed off by `β ∈ dom Θ`).

**No function-valued rule arguments.**  A cofinite family whose output
varies with the binder (`Ξf : atom -> aenv`) was built and rejected
during the ForallR fix: it admits exotic name-dependent outputs and is
unusable in inversions.  Exists-fresh is the decided replacement.

#### The avoid-input principle (settled by cluster 1, 2026-08-01)

Input-only conditions alone admit **junk derivations**: with
scope-insensitive generators, a ghost below a `∀` can generate the `∀`'s
own recorded witness (`Ξ ∋ b0`), and the opening/renaming kit is FALSE on
such derivations — no freshness demanded of a lemma's own variables can
fix a collision between two names *inside* a derivation.  The resolution,
still input-only:

- **name-generating rules avoid `ftvar_in_aenv Θ`** (domain *plus*
  payloads — an `α̂ ≔ τ` may mention the offending name), and
- **binder witnesses enter the premise's context** (`(β~tvar) ++ Θ`),

whence *generated names avoid enclosing witnesses* is *derivable*
(`a_guess_mono_generated_fresh`), not assumed.  `Θ` on the paper's
context-free judgments (guess, look, solve) is the relational rendering
of the implementation's global fresh counter.  This is also the honest
account of the `F` avoidance set — `F` supplies exactly this discipline
externally — so internalizing it is what lets `F` be deprecated.

Two consumer-visible consequences:

- **Renaming lemmas constrain their TARGET, never their source**, rename
  the context and the generated block too (`rename_aenv` — keys *and*
  payloads), and induct on the **subject's size** (when the target *is*
  the recorded witness, the derivation is renamed twice, and the second
  rename applies to the first's result — no sub-derivation).
- **Context-generic claims (`forall Θg, a_guess_mono Θg …`) are
  retired** — artifacts of the previously-inert context slot.  They
  become either the *transport* form (`dom Ξ` avoids `ftvar_in_aenv Θg`
  → …) where construction and consumption contexts differ, or the
  *L-bounded* form (`ftvar_in_aenv Θg [<=] L` → …) where a `∀` case must
  pick its witness before the context is known — fixing the bound first
  is what makes that case provable with no weakening lemma
  (`a_guess_ty_witness`, prop_look_complete_extract.v).

#### The look cluster: why the judgment gained a context (cluster 3, 2026-08-01)

`a_looksub` / `a_lookeq` now carry an `aenv` input, written
`Θ ⊢ P ≼[α,M] P' ⤳ Ξ ⨾ 𝒞` / `Θ ⊢ P ∼[α] P' ⤳ Ξ ⨾ 𝒞`.  The paper's look
judgments are context-free; `Θ` is the same relational rendering of the
implementation's global fresh counter that guess and solve already carry
(`incr counter; Bindlib.new_var`, type.ml:563-565).  Three things forced it,
in increasing order of decisiveness:

- the paper's `\lelab{FlexR}` carries `\fresh{\hat\gamma}`
  (algorithmic.tex:1204), which the mech rendered as **no condition at all**;
- without it a flexible generated below a ∀ may BE that ∀'s binder — cluster
  1's junk derivations, in the look cluster;
- **`a_looksub_lookeq_ftv` cannot be STATED without it.**  All five look ∀
  rules LEAK (the implementation unbinds and discards the name in every one:
  `constr_collect_eq` :579-583, :595-598, :610-613; `constr_collect_sub`
  :668-672, :685-688, and neither function ever calls `bind_var`), so the
  exact bound `ftv 𝒞 ⊆ ftv P' ∪ dom Ξ` is FALSE —
  `Θ ⊢ ∀b.α ∼[α] ∀b.b ⤳ · ⨾ [b₀ ≐]` by LE-ForallInh + LE-Var.  Its repair is
  cluster 2's disjunctive shape, and the second disjunct *is* "the run
  invented this name", i.e. `∉ ftvar_in_aenv Θ`.  The chain it feeds is the
  paper's own `lemma:look-output-fresh` (`a_extract_output_fresh`,
  subtyping-proofs:522).

`a_guess` gained the context at the same time, and `a_extract` feeds it
`Ξ ++ Θ0` (the guess runs after the collection, so both halves of the output
block `Ξ ++ Ξ'` avoid the ambient context).  Running the inner guess at `nil`
had left cluster 1's discipline INERT inside `a_extract`.

⚠️ **Consequence — source-side stability needs Barendregt spelled out.**
`cex/cex_look_subst_stable_leak.v` (Qed, axiom-free) refutes the mech's
unconditional `a_looksub_lookeq_subst_stable` (the forward direction of the
paper's `lemma:constraint-collection-stable-substitution`): substituting a
`P0` that happens to carry the derivation's own leaked binder cannot be
re-derived, because every binder the rule may pick avoids
`ftv (subst P0 β P)`.  The paper is fine — it argues under Barendregt.  The
mech states the smallest premise that makes the rule's own side condition
supply it, `ftv P0 [<=] add α (ftvar_in_aenv Θ)`: it names the CONTEXT, not
the input skeletons, because only the context is MONOTONE under descent (an
arrow row shrinks the skeletons, a binder row grows the context).

**RESOLVED 2026-08-02 — the EXISTENTIAL-output form.**  What follows was the
diagnosis; the repair is `a_looksub_lookeq_subst_gen_size` (prop_decorate_sub.v
§8, Qed).  Reading it as a design rule: *where a consumer must substitute a
skeleton it does not control into a run whose binders it does not control, the
lemma drops the context premise and hands back RENAMED outputs.*  The same gap
turns up twice more (the decoration ForallR row, and
`a_extract_family_of_instance`); there only ONE name can offend, so a single
rigid rename settles it (`a_looksub_avoid_atom`) — no second induction.

⚠️ **…and the fixed-output form is not enough for the decoration layer.**
`a_subtag_decoration`'s two ForallL rows substitute the node's GUESS `P1` into
the look run, and `P1`'s variables include the extract's fresh block `dom Ξ`,
which the run's binders have no reason to avoid: `Ξ` and those binders are
produced by two INDEPENDENT runs at the same context, so the premise
`ftv P1 ⊆ add α (ftvar_in_aenv Θ)` is unsuppliable.  (The reference
implementation's global counter keeps them apart; the relational rendering of
it — "avoid `ftvar_in_aenv Θ`" — cannot, because `Ξ` is generated *after*.)
The repair is the campaign's own move applied one level up: let the ∀ rows
RE-PICK their binder away from `P0` and hand back RENAMED outputs, so the
lemma needs no context premise at all and its `Ξ ⨾ 𝒞` become existential,
with the solvetag obligation riding along through `a_solvetag_subst_cstrs`.
The leak counterexample does not touch that form — on its own witness the
substituted run IS re-derivable, at any binder `δ ≠ β₀`, returning `𝒞` rigidly
renamed.  Specified in full (measure, the six re-picking rows, and the free
look context `a_subtag_decoration` must gain) in PROGRESS.md's 2026-08-01
stage-4 entry; `a_looksub_open_target_at_size` is the working model.

The same phenomenon shapes the renaming lemmas, and there the honest premise
is an **output**-freshness one (`α1 ∉ dom Ξ ∪ ftv 𝒞`) plus SIZE induction:
a binder that ESCAPED into the outputs cannot be moved (moving it would
change them), so the target must differ from it; a binder that did not escape
can be moved, and then the outputs stay fixed.  That case split is forced,
and it is the cluster-2 pair of shapes (1) and (3) meeting in one lemma.

Both renames are now closed under exactly that shape
(`a_looksub_lookeq_rename_tvar_size`, `a_looksub_lookeq_rename_var_size`), and
the cluster gained three enablers worth reusing elsewhere:

- **`a_looksub_lookeq_ctx_ftv_mono`** — the judgment reads its context ONLY
  through the avoid-inputs, so it is stable under any context whose
  `ftvar_in_aenv` is no larger.  Its corollary is EXCHANGE
  (`a_looksub_ctx_exchange`), which every consumer that opens two binders in
  the other order needs, because contexts are LISTS.
- **`a_looksub_lookeq_generated_fresh`** — cluster 1's derived junk-freeness,
  in the look cluster: a generated flexible can never BE an enclosing ∀
  binder.  This is what makes "move the binder, keep `Ξ`" a theorem rather
  than a hypothesis.
- **`a_solvetag_subst_cstrs`** — the collected constraints only ever appear as
  a solvetag run's TARGETS, and target renaming is unconditional, so a
  consumer may hand back the RENAMED constraint list.  That, plus an
  existential 𝒞 in the conclusion, is how `a_looksub_open_target_at` copes
  with a binder that leaks into 𝒞.

⚙ **A performance rule the cluster forced.**  These side conditions are
five-way unions, and ONE `fsetdec` against five overlapping such hypotheses
does not terminate in reasonable time (measured: >100s for a single row);
`clear -` scoping is not enough.  Binder rows must never hand a union to
`fsetdec`.  Shatter a `pick fresh` into ATOMIC facts and `clear Fr`, and prove
the union GOALS structurally with the one-line kit (`notin_union_both`,
`notin_add_atom`, `notin_ftvar_in_aenv_cons_tvar`,
`notin_ftvar_in_aenv_rename`, `notin_ftvar_open_var`, `notin_ftvar_subst_var`,
`notin_ftvar_in_cstrs_subst`) driven by the **`look_fresh`** tactic, whose
leaves are `assumption` / `congruence` / a single-hypothesis `fsetdec`.  Same
row: >100s → ~2s; the whole 2000-line file: 11s.

#### Cluster 4 (the consis mutual): a UNIFORMITY conversion, and what it cost

⚠️ **Unlike clusters 1–3, cluster 4 fixed no defect.**  `a_consis`'s three ∀
rows (`__forall_inh`, `__forall_syn`, `__univ_ghost1`) CLOSE: the skeleton
output is re-bound and the context output strips the opener.  So the cofinite
rendering was faithful, and the two encodings are equivalent — machine-checked
in BOTH directions by prop_consis_rename.v §9's `_cofinite` admissibility
lemmas, which are also what consumers wanting a family should apply.  The
conversion was made anyway, for ONE freshness discipline per layer.

The criterion is worth stating on its own, because it decides every remaining
cluster: **cofinite is faithful exactly where a rule re-binds its skeleton
output AND strips the opener from its context output.**  Where either escapes,
cofinite silently degenerates to "fires only when the binder is vacuous".

Three things the conversion cost, all of which generalize:

- **`a_assign_unify_consis_compat` had to be WIDENED.**  Its condition was
  `α1 ∈ F' → α1 ∈ F ∨ α1 ∉ dom Θ1`.  Under cofinite the opener could be chosen
  outside `F'`, so the condition transported into the premise; with the opener
  fixed, `α1 = α` satisfies neither disjunct (`α` IS in `dom ((α~tvar) ++ Θ1)`).
  Re-picking would need §8's rename, which is proved USING compat, so the
  repair went into the statement: a third disjunct `α1 ∈ dom (input context)`.
- **The rename lemma HANDS BACK its own avoid-set** —
  `deriv -> exists L, forall β0 ∉ L, …`, each ∀ case contributing its opener to
  `L`.  This is the two-independent-generators gap again, and it is forced: the
  opener occurs in NO component of the conclusion (the inputs carry `var_b 0`,
  the output is `close α Q`, the context entry is stripped), so no set
  computable from the statement can contain it, and `a_consis : Prop` rules out
  a function from derivations to sets.  Cluster 3's other escape — size
  induction, "rename twice" — is NOT available here: `a_consis` recurses on
  skeleton size, `a_assign`/`a_unify` on the context, and `a_assign__assign`
  crosses from context `(β̂ ≔ τ) ++ Θ0` to a premise at `Ξ ++ Θ0`, so no measure
  decreases on every rule.
- **`a_consis_decorate_gen` MOVED to prop_consis_rename.v §10** and became a
  SIZE induction on `size_pskl P + size_pskl P0` (the subject alone fails —
  UnivGhost1 fixes it and shrinks only the input, ForallSyn does the opposite).
  The decorated `a_consistag` rows are still cofinite, so each ∀ row must
  rebuild a family from the run's ONE opener; the rename lives downstream of
  prop_decorate.v (via algo/prop_basic.v), so the lemma moved rather than the asset.
  It gained a `uniq Θ0` premise, discharged at its three consumers from
  `a_wf_aenv_uniq`.

⚙ **The principled alternative, if renames keep recurring: EQUIVARIANCE.**
The avoid-set exists only because *substitution is not injective* — `subst β0 α`
collapses two distinct free atoms when `β0` happens to be an internal opener.
A **swap** `α ↔ β0` has no such failure mode: it moves every atom of the
derivation at once, including the openers, so equivariance needs NO freshness
side condition at all, and the substitution-shaped rename falls out as a
corollary whenever `β0` is fresh for the STATEMENT's own data — no `L`, and
`tvar_prefix Ξr` and `uniq` both drop out of the hypotheses.  The cost is
building `swap` over `ptyp` / `pskl` / `abind` / `aenv` plus equivariance for
the small side judgments (`a_guess_mono`, `a_flex_tvar`, `a_non_flex`,
`guarded_pskl`); the mutual proof itself gets much SHORTER than the current one
(no crossing case analysis, no freshness bookkeeping).  Clusters 5 and 6 and
P7a's K1–K4 all need renames, so this is the asset to build if the avoid-set
starts leaking into consumer statements.

#### The `F` avoidance set — DELETED (closed 2026-08-03)

**The subsection below this box records the earlier "`F` STAYS" decision and
is SUPERSEDED in full.**  The rejection of the output-premise alternative
rested on a single ground — "that premise shape is exactly the P7a blocker …
this multiplies one unsolved problem by eight" — and that ground evaporated
when `a_sub_flex_complete_skip` discharged the shape, machine-checked.  The
used-name index `F` is now gone from all three judgments; the eight
re-attaching rules of the assign/unify walk carry `β ∉ dom Θ1`, exactly like
`a_sub_flex`'s three.

⭐ **The output-premise shape LOSES NOTHING** — `prop_swap.v` §13b for
`a_sub_flex`'s three rows and §13c for the walk's eight
(`a_assign_{skip,skip_rigid,skip_tm_var,skip_tm_skl,assign}_no_loss`,
`a_unify_{flex_skip,skip_other,flex_assign}_no_loss`), Qed and axiom-free.
A rule
that constrains its own output can only REJECT, so the fair objection is that
the encoded algorithm might fail where `type.ml` (whose global counter makes
the collision impossible) succeeds.  It cannot: a derivation is finitely
supported, so a `γ` fresh for its whole output exists, equivariance moves the
run to `γ` while fixing every INPUT pointwise, and `swap_junk_dom_out` then
discharges the premise.  The rule therefore fires whenever a premise-free
version would, with the run's GENERATED names transposed and nothing else
touched.  ⭐ This is the argument that makes the encoding admissible; without
it the premise is a strengthening, and it should be re-run for any future rule
of this shape.  (`F` and the output premise cannot coexist: the `_no_loss`
argument needs `β ∉ F`, which is false at a premise running at `add β F` —
which is why §13c could only be written AFTER the deletion.)

The paper has neither device.  `Assign-SolveM` (full-algo-spec.tex:1753) has
NO side condition on `β̄`; the only freshness is `\fresh{}` inside
`guessMono`, and `\fresh` is a bare `\newcommand` — informal prose.  Every
skip rule just writes `Θ₁, β̂` in its conclusion.  So the paper relies on a
GLOBAL Barendregt convention a Coq `Inductive` cannot express, and formalizing
it forces a choice with exactly two slots: carry the names DOWN (`F`), or
check the output on the way UP (`β ∉ dom Θ1`).  `F` is an index the paper
never writes; the output premise constrains only what the paper's own
conclusion appends.

**Soundness** (prop_consis_sound.v).  Conjunct 4 (`x ∈ dom Θ1 → x ∈ dom Θ0 ∨
x ∉ F`) is deleted with its projections — vacuous once `F` goes, and no
consumers outside the file.  Conjunct 5's coverage hypothesis was the
load-bearing one (at `Assign-SolveM` it is what excludes the guessed `β̄` from
the protected `Δ`, which both halves of the Δ-invariant need); it is restated
OUTPUT-relative, mirroring the change to the rules themselves:

```coq
Δ ∩ dom Θ1 [<=] dom Θ0      (* replaces  Δ [<=] (F ∪ dom Θ0) *)
```

All 28 cases go through: at Solve-M a guessed `γ ∈ Δ ∩ dom β̄` would have to
lie in `dom ((α ~ flex) ++ Θ0)`, which the rule's own side condition forbids;
at the five re-attaching rows the new `β ∉ dom Θ1` premise is exactly what
pushes the hypothesis into the premise; at Arrow it is `dom`-monotonicity; and
the top-level consumers supply it from `Δ [<=] dom Θ0`.  Conjunct 5's third
component then becomes immediate and leaves the bundle.

⭐ **Completeness** (prop_consis_complete.v §2): the avoid set moves to the
MOTIVE.  The eight discharge sites can no longer read conjunct 4, so the three
completeness statements gain a parameter `N : atoms` and one conclusion
conjunct, between the derivation and the optimality half:

```coq
forall γ, γ `in` dom Θ1 -> γ `in` dom (Ξ ++ Θ0) \/ γ `notin` N
```

This is literally the old `F`, moved from the JUDGMENT to the completeness
theorem — where it is FREE, because completeness is the direction that CHOOSES
the guessed names (`assign_solve_m_complete`'s `set (L := ...)` simply gains
`N`).  The walk rows relay `N := add α1 N` exactly where they used to relay
`add α1 F`.  Four atom-set lemmas do all the work — `avoid_relay` (pop and
re-attach), `avoid_head_miss` (discharge the Barendregt premise),
`avoid_compose` (Arrow's two runs in sequence), `avoid_truncate` (the ∀ rows,
which run under their own rigid binder and hand back the truncation) — plus
`avoid_relay_cons` / `_cons_mid` / `avoid_truncate_cons` / `avoid_same_dom` /
`avoid_mono` as their at-the-shape wrappers.  No new theory.

⭐ **The general lesson: an avoid set is a CONSTRAINT on a judgment and a
FREEDOM on a completeness proof.**  `F` was in the wrong place all along.

The rejected alternative was to junk-swap each IH's run (prop_swap §13) and
transport the OPTIMALITY package with §14/§15's `kswap_msubst` kit — P7a's
`a_sub_flex_complete_skip` eight times over.  Fewer sites, but each needs
`a_wf_aenv Θ1` plus "a name of `dom Θ1 ∖ dom (Ξ ++ Θ0)` is FLEXIBLE", which is
`a_inc_binds_provenance`, currently downstream in prop_sub_complete_thm.v.

*Superseded reading follows.*


---

`F` was listed above as something the campaign would retire; it is not, and the
item is withdrawn.  `F` is the ONLY carrier of the names the assign/unify walk
has passed: `a_assign__skip` recurses at the TAIL (`Θ0`, not `(β~b) ++ Θ0`) and
re-attaches `β` on the way out, and `Ξ` accumulates only Assign-Depend's
dependency block — so during the descent no context slot holds them, and
`a_assign__solve_m`'s guessed `β̄` genuinely need them.  `a_consis` carries `F`
purely to relay it: it appears inside the walk via `a_assign__assign`'s
consistency premise.

Three alternatives were considered and rejected:

- **Output-freshness premises** (`β ∉ dom Θ1` on the ~8 re-attaching rules,
  deleting `F`).  Cleanest definition, but it moves the obligation onto
  completeness — and that premise shape is exactly the P7a blocker
  (`a_sub_flex__assign` / `__skip` / `__skip_rigid`, PROGRESS 2026-07-31).
  `F`'s condition constrains the GUESSED names, which a completeness proof
  picks and therefore controls; `β ∉ dom Θ1` constrains a sub-run's OUTPUT,
  which it does not.  This multiplies one unsolved problem by eight.
- **The walked prefix as a context** (`Θw : aenv` replacing `F : atoms`).  A
  retype, not a deletion — `Θw` cannot be merged into the working context
  (the consistency premise could then SOLVE entries the walk had passed), so
  `a_consis` still carries a slot.  Its one real gain, payload coverage via
  `ftvar_in_aenv`, is already sound transitively.
- **Re-freshening the output before re-attaching** (`⊣ (β ~ b) ++ rename_aenv γ β Θ1`,
  with `γ` fresh for `Θ1`).  This one is genuinely VIABLE and does delete `F`:
  every occurrence of `β` in `Θ1` is necessarily invented by the sub-run (`β`
  was stripped for the recursive call, no pre-existing payload can mention it
  by the scope discipline, and `β ∉ ftv P`), so renaming it is
  meaning-preserving.  It was rejected on cost: it makes the output context
  non-syntactic.  L8 (`a_assign_unify_consis_tvar_prefix`) says an all-rigid
  prefix survives VERBATIM, and that is exactly what shapes the ∀ rules'
  `⊣ (α ~ tvar) ++ Θ1` premise; under the rename it survives only up to
  renaming, and every `dom` / `binds` / `uniq` / soundness statement about the
  output needs a `rename_aenv` commutation.  The output also stops being
  determined, since `γ` is existential.

⚠️ **`F` must NOT enter the ∀ rules' avoid-sets**, tempting though it is (`F`
is the used-name set, so "fresh" would naturally mean `∉ F`).  Adding it
REFUTES `a_assign_unify_consis_compat`: that lemma swaps `F` for any `F'` whose
atoms are old or miss the output, and such an `F'` may well contain the rule's
own opener — which is fresh, hence outside the output.  Soundness' invariant
conjunct, the one place that looked like it needed `α ∉ Δ`, is discharged
instead from `α ∉ dom Θ1`, which the premise's own output well-formedness
supplies.

#### The cost, and the staging rule that pays it

Exists-fresh takes binder choice AWAY from consumers: a proof that needs
the binder somewhere specific must MOVE it.  So every cluster is
converted **rename-lemma-first** — the rename must be Qed before the
rule changes, and the tree stays green at every step.  The four assets
that make the campaign executable already exist:

| cluster | binder-move lemma |
|---|---|
| guess | ~~`a_guess_mono_rename_tvar`~~ → `a_guess_mono_swap` (prop_swap.v) |
| look | `a_looksub_lookeq_rename_tvar` (prop_looksub.v) — needs `β ∉ ftv 𝒞` |
| solve | ~~`a_solve_sub_eq_rename`~~ → `a_solve_sub_eq_swap` (prop_swap.v) |
| consis mutual | `a_assign_unify_consis_rename_tvar` (prop_consis_rename.v §8) |

⚙ **The substitution-shaped renames are being retired in favour of the
equivariance kit** (§4.3 ⚙, prop_swap.v): a transposition is a bijection, so
it carries no target-freshness side condition and no existential avoid-set,
and both halves collapse to the identity exactly where a consumer needs them
(`swap_*_fresh_id`).  Retired so far: the *solve* cluster's rename (its two
wrappers `a_solve_{sub,eq}_rename_var` were deleted 2026-08-06, unused since
`dec_ext_solve_eq_step_size` moved to `a_solve_eq_move_binder`), and the
*guess* cluster's (`a_guess_mono_open_at` now goes through
`a_guess_mono_swap` + `swap_ptyp_as_subst`; the 150-line size induction is
gone).  ⛔ Still standing, and NOT a drop-in: `a_assign_unify_consis_rename_tvar`
(§8, ~590 lines).  Its three consumers in §10 need the output context's
suffix `Θt` to come back UNCHANGED under the move; the swap instead returns
`swap_aenv α β Θt`, so equating the two needs `α ∉ ftvar_in_aenv Θt` — a
scope fact §8 currently sidesteps with its `tvar_prefix` / F-protection
argument and which no existing lemma supplies.  Retiring it is a proof
redesign of §10's three ∀ rows, not a cleanup.  The DECLARATIVE and DECORATED
layers keep their renames outright: there is no swap kit over `d_*` / `ad_*`,
and their targets are cofinite relations with no outputs to leak.

The standing recipe for a consumer that pushes a substitution through a
derivation (it needs every binder ≠ the substituted variable, which
exists-fresh does not give) is to RE-FRESHEN ITS OWN variable away from
the rule's α — see `a_subtag_decoration`'s ForallR case, the worked
precedent.

#### What else the campaign folds in

Two further disciplines are being retired into the canon:

- **The `F` avoidance set** — DELETED 2026-08-03, see "The `F` avoidance
  set — DELETED" above.  (It was withdrawn from the campaign on 2026-08-02
  and re-opened the same day; the box records why the second reading won.)
- **The walk's prose-Barendregt OUTPUT premises** (`β ∉ dom Θ1`, now on
  `a_sub_flex`'s three rules AND the assign/unify walk's eight) — these stay
  as genuine side conditions, are proved to LOSE NOTHING (prop_swap.v §13b),
  and COMPLETENESS discharges them: on the subtyping side with the
  `a_sub` / `a_sub_flex` run-renaming kit (K1–K4), on the consistency side
  with the motive's own avoid set `N`.

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

- `δ = ε ↦ utyp_all_tag ε C` / `uskl_all_tag ε R`
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
new code should use `utyp_all_syn` / `utyp_all_tag` and the skeleton
counterparts directly.

**Rule ordering preference.** In `decl/def_rules.v` the tagged and
untagged constructors of the same paper rule are kept ADJACENT (e.g.
`d_consis__forall_inh_tagged` immediately followed by
`d_consis__forall_inh_untagged`), grouped by paper rule rather than
appended-last. This makes the audit "does Coq cover the paper's δ
spread for rule X?" a one-glance check.

**Rule-body notation.** Notations for the 7 main judgments
(`d_wf_pskl`, `d_wf_dtyp`, `d_wf_tskel`, `d_consis`, `d_sub`,
`d_pat_consis`, `d_pat_sub`) are declared as `Reserved Notation` at
the top of `decl/def_rules.v` and bound via `where` clauses on each
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
  `gutyp_all_tag`; the split syntax also carries the corresponding
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
  `d_pat__abs` carry explicit `d_wf_typ Γ A` /
  `d_wf_pskl Γ nil P`. The paper does not state these — they're
  regularity strengthenings the mechanization needs to close
  `d_typing_pat_preserves_wf`. Worth a paper footnote. (After the
  2026-05-15 re-encoding, `d_typing__abs` / `_abs_anno` wf premise is
  on `inh_color A` / `syn_color A` for the `ctyp` base `A`.)
- **`d_consis__var` carries a `binds X dbind_tvar Γ` premise**
  (paper-faithful: the paper assumes the wf invariant implicitly).
  Without it, `d_consis_preserves_wf`'s var case is open.
- **Linearity of tag contexts** is encoded as set union plus an
  explicit `Ψ₁ ∩ Ψ₂ [=] empty` (in `d_tags`), not multiset. This is a
  prosaic reading of the paper (`Ψ₁ ⊎ Ψ₂` = disjoint union) but readers expecting linear logic
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
lemma in Fresco looks "almost-but-not-quite true" structurally, the
right question is rarely "how do I patch the wf rules" and almost
always "which call-site predicate, induced by the calculus's
colour/mode discipline, makes the bad case unreachable?"**

### The discipline, restated

Fresco factors "what polymorphic type information can flow where" along
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
still-open. Fresco decides more programs than naive bidirectional
systems because it has finer-grained info per ∀.

### Concretely, how this shows up in proof script gaps

Many rules in this system have *implicit* shape constraints baked
into the colour discipline. A few patterns to watch for:

| structural gap | look for this call-site predicate | example |
|---|---|---|
| consistency RHS appears non-wf | `is_syn_skel P` on the calling `d_pat_sub` rule | Lemma 3.7 (`d_pat_preserves_skel_wf`) |
| `d_typing__sub` takes arbitrary B | `is_base_term e` (paper restricts to base terms) | general-subsumption (D1) |
| ∀-introduction in TI mode | `is_value e` (value restriction) | `d_typing__forall` |
| arrow-position pattern coerces freely | `mode_fn m` (function-position mode) | `d_pat_sub__arrow` |
| skeleton input to a refinement rule | `is_inh_skel` / `is_syn_skel` matching colour expectation | `d_refine_*` family |
| `d_consis` LHS shape "looks too permissive" | `d_wf_typ Γ T` to rule out `typ_all_tag` LHS | `d_consis_sub_trans` (D10 / paper B.3) |

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
  of side-condition that the colour discipline supplies.  (The
  `d_refine_syn` rules no longer carry guardedness premises — since
  2026-10-08 it comes from the presupposed well-formedness.)
- **Algorithmic stability lemma chain** — colours and modes survive
  algorithmically; many "obvious" stability claims should reduce to
  the same morph + discipline trick.
- **Phase 3 soundness / completeness HEADLINES** — these are gated on
  five auxiliary `a_*_sound` / `a_*_complete` lemmas. Each is
  expected to follow the same morph + discipline pattern.
