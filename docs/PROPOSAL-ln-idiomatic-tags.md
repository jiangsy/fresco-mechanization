# Proposal: LN-idiomatic tag (`εvar`) freshness — for review before refactor

Status: DRAFT for owner validation. Motivated by the safety-fill obstruction
(see `DESIGN-safe-pat-witness.md` §2.7): the freshness that blocks the abs/forall
fills traces to the **tag** (`εvar`) freshness, which is encoded set-theoretically
and so does not interact with the standard LN rename/strengthen machinery.

## 1. Current encoding (what it is)

- `ε : εvar` is a **distinct atom kind** (alongside term vars and tvars). It is a
  **free label**, not a binder: `uskl_all_etag (ε:εvar) (R:uskl)` (and
  `uskl_topholeg ε R`, `utyp_all_etag ε C`) carry `ε` as a plain parameter; the
  *body* `R`/`C` is opened on its **tvar** binder, which IS cofinite.
- Tag collections are **`atoms` sets** `Δ`/`Ψ`, manipulated set-theoretically:
  - `d_tags_skl : atoms -> uskl -> Prop` (def_extra.v): `__arrow` requires
    `AtomSetImpl.inter Δ1 Δ2 [=] empty` (paper `⊎`, linearity); `__all_etag`
    requires `ε ∉ Δ0`, `Δ [=] add ε Δ0`; `__hole/__unit/__var` require `Δ [=] empty`.
  - `d_consis__forall_inh_tagged` (def_extra.v): `Ψ [=] add ε Ψ0`.
  - `d_pat_sub__forall_l_{tagged,untagged}`: `AtomSetImpl.inter Δ' Δ [=] empty`,
    `d_tags_skl Δ' psi`, `is_tskl psi`.
- Asymmetry: the forall's **tvar `X`** is `forall X ∉ L, …` (cofinite, renamable,
  strengthenable); the **tag `ε`** lives only in a set with `add`/`∉`/`inter`.

## 2. Why this blocks the safety fill (the connection)

The abs/forall fills need the safe tc-witness to be **canonical up to its bound
variable** (so one witness serves the cofinite family of fill instances). The
non-canonicity enters at `d_pat_sub__forall_l`, where instantiating a `∀` picks
`psi` *together with its tag-set `Δ'`* under set side-conditions. For the **safe**
witness `psi` is the ghost (`□`-instantiation) with **no tags** (`Δ' = ∅`), so the
disjointness is trivially true — but because `Δ'`/`Δ` are sets glued by
`inter`/`add`, there is no LN handle (`rename`/`strengthen`/cofinite `intro`) to
*push that canonicity through*. The freshness then leaks into the term-level fill
as the unprovable `x0 ∉ dom Γt''` (the body-hyp's arbitrary context), exactly
where the renames stall. In short: **the obstruction is bookkeeping around `ε`,
not metatheory.**

## 3. Proposed LN-idiomatic encodings (pick one)

### Option A — tag context as a cofinite **list**, freshness via `dom`/`∉` (least invasive)

Keep `ε : εvar` and `uskl_all_etag ε R` syntax. Replace the **set** `Δ : atoms`
with a **binder-style list** `Δ : list εvar` (or `list (εvar * unit)`), and replace
every set op with the LN idiom that the tvar context `Γ` already uses:

| current (set)                              | proposed (LN list)                                  |
|--------------------------------------------|-----------------------------------------------------|
| `Δ [=] empty`                              | `Δ = nil`                                            |
| `Δ [=] add ε Δ0`, `ε ∉ Δ0`                 | `Δ = ε :: Δ0`, `ε ∉ dom Δ0` (or cofinite-introduced) |
| `AtomSetImpl.inter Δ1 Δ2 [=] empty`        | `Δ = Δ1 ++ Δ2` with `disjoint Δ1 Δ2` (list, like ctx)|
| `AtomSetImpl.inter Δ' Δ [=] empty` (sub)   | `Δ' ++ Δ` with `disjoint`, **`Δ'` introduced cofinitely** in `forall_l` |

Crucially, `d_tags_skl__all_etag` and `d_pat_sub__forall_l` **introduce the tag
cofinitely** (`forall ε ∉ L_ε, …`) exactly like the tvar binder, so `ε` becomes
renamable/strengthenable by the *same* lemmas as `X`. Linearity is then "distinct
fresh atoms in a list context", and the safe-witness canonicity (`Δ' = nil`) is a
plain cofinite/`nil` fact, not a set identity.

- Pros: syntax unchanged; mirrors `Γ` exactly; the existing tvar rename/strengthen
  template (`*_rename_tvar`, `*_strengthen`) transfers to `ε`.
- Cons: must re-prove the tag metatheory (`d_tags_skl`, `d_consis` tagged cases,
  `d_pat_sub` `forall_l`, B.2 consistency-transitivity which relies on set-union
  idempotence — a list needs an explicit dedup/permutation story there).

### Option B — identify the tag with the instantiation **tvar** (most idiomatic, more invasive)

Observe that a tag marks *which instantiation happened*, and instantiation already
binds a fresh tvar. So **drop `εvar` entirely** and let the forall's bound **tvar**
serve as its tag: `all_etag ε R` becomes "the `∀` whose instantiation var is the
tag", and the tag context merges into (a marked sub-context of) `Γ`. Linearity =
distinct tvars = automatic from `X ∉ dom Γ`. No `εvar`, no `Δ` sets, no `inter`.

- Pros: removes a whole atom kind and all set machinery; freshness is *entirely*
  the existing tvar story; the safety fills inherit the tvar renames directly.
- Cons: a **syntax change** (ott/lngen regen: `all_etag` loses its `εvar`,
  gains/reuses a binder), and a re-validation that tag=tvar is faithful to the
  paper's linear-instantiation semantics (esp. B.2 and the `δ=ε` vs colour split).

### Option C — targeted, no refactor (fallback)

If a full refactor is undesirable now: prove a *local* lemma that the **safe** tc
inference always instantiates `∀` with the ghost (`Δ' = ∅`) `psi`, making its
erasure canonical, and use that to discharge `bskl_to_pskl Q_x = bskl_to_pskl Qb`
(route 1 of the fill). This sidesteps the encoding but leaves the non-idiomatic
tags in place (and the lemma's proof still wades through the set conditions).

## 4. Recommendation / open questions for you

- **A** is the safe incremental move (cofinite `ε`, list `Δ`); the main risk is
  re-proving **B.2** (consistency transitivity) where set-union *idempotence* is
  currently load-bearing (`Ψ ∪ {ε}` absorbs duplicates) — a list/`disjoint`
  formulation must decide whether tags can legitimately repeat (paper `⊎` says no,
  but B.2's "reuse a tag" note (def_extra.v `d_consis__arrow` comment) says a set
  *absorbs* a reused tag). **This is the crux you should rule on:** are tags truly
  linear (list/`disjoint`) or set-absorbed (idempotent)? That choice decides A.
- **B** is the cleanest long-term but costs a syntax regen + paper re-validation.
- Either way the *safety* benefit is the same: `ε` becomes cofinite, so the
  abs/forall fill's freshness is dischargeable by the standard LN machinery.

Nothing is changed yet — this is for your validation.
