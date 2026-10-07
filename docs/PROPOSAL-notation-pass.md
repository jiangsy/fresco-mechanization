# Notation improvement pass — proposal + status

Goal: (1) stay close to the paper's notation, (2) use notation as much as
possible, (3) use custom scopes to reduce collisions.

Status: **big-judgment relation symbols DONE and merged** (see §1/§5); the
**system/sort axes DONE 2026-08-09** (see §5 — that pass is the one that made
`a/d/ad` legible, and the canonical legend now lives in `fresco/notations.v`);
small operations (§4) catalogued for later, no rush.

⚠️ **This file keeps its ORIGINAL glyphs on purpose** — the "Mech now" columns
below are a historical record of what the notation *was*, and the combining
dots in §2/DECISION B are specimens of the hazard. It is the one file the
2026-08-09 sweep deliberately skipped; do not "fix" its tables.

Paper macro source: `paper/macro.tex`. Rendered forms below use the paper's
actual glyphs.

## IMPLEMENTED (build green, axiom-free flagships intact)

Every big-judgment relation symbol now matches the paper, in both the
definitions AND the proof source (no aliases remain):

- subtyping `d_sub` / `d_pat_sub` / `a_sub` / `ad_pat_sub`: `⊑`/`⊑ᴬ` → **`⩽`**
- consistency `d_consis` / `d_pat_consis` / `a_consis` / `ad_pat_consis`:
  `≈` → **`∼`**, decl turnstile `⊨` → **`⊢`**
- decorated `a_subtag` / `a_consistag`: `⊑`/`≈` → **`⩽˙` / `∼˙`** (paper's
  dotted `⩽̇`/`∼̇`, using the SPACING dot U+02D9 — never a combining diacritic)
- information increase `a_inc`: `Θ ≤[ρ] Θ'` → **`ρ ∷ Θ ⊑ Θ'`** (paper `\inc`;
  `⊑` was freed by the `⩽` move). ~190 proof sites reordered.
- removed duplicate `d_wf_utyp` (`⊢ᵤₜ`) / `d_wf_uskl` notations.

Preserved (correctly NOT swept): precision `⊑ᵖ` / `⊢ₚᵣᵃ … ⊑` (paper `⪯`-family),
unification `≈ᵘ`, and info-increase `⊑` in prose.

NOT yet done (deliberately): §3 custom scope, §4 small-operation notations.

---

## 0. Structural verdict (read first)

The mechanization is **already structurally faithful** for every big judgment:
mode `M` lives in a bracket `[M]`, sort `N` in a subscript, the tag/skeleton
context sits on the left, output contexts are written `⊣ Θ'`, and all of them
are notated inline via `Reserved Notation` + `where`. So objective (2)
("use notation") is essentially met for the big judgments.

The real gap is objective (1): a handful of **relation symbols diverge from
the paper**, and there are a few **collisions / redundant notations** worth
cleaning up. Two structural decisions (`⨟` vs paper `|`; symbol sweep) are
flagged as **DECISION** — they drive large diffs, so hold until confirmed.

---

## 1. Symbol divergences on the big judgments

| Judgment (mech relation) | Mech now | Paper | Paper macro |
|---|---|---|---|
| `d_sub`      | `Ψ ⨟ Γ ⊢[M] C ⊑ B`        | `Ψ \| Γ ⊢_m C ⩽ B`      | `\subtype = \leqslant` |
| `d_consis`   | `Ψ ⨟ Γ ⊨ C ≈ B`          | `Ψ \| Γ ⊢ C ∼ B`        | `\consis = \sim` |
| `d_pat_sub`  | `Ψ ⨟ Γ ⊢ₛ[M] R ⊑ Q`       | `Ψ \| Γ ⊢^sk_m S ⩽ P`   | `\patsub` |
| `d_pat_consis`| `Ψ ⨟ Γ ⊨ₛ R ≈ Q`         | `Ψ \| Γ ⊢^sk R ∼ Q`     | `\typconsis` |
| `d_pat`      | `Γ ⊢[M] e ⇨ P`            | `Γ ⊢_m M ⇛ P`           | `\TTo` = ⇛ |
| `d_refine_syn`| `Γ ⨟ Δ ⊢ᵣ Q ⊳ P`         | `Γ \| Δ ⊢ P ▶ Q`        | `\fillsyn = \syn{\btright}` |
| `a_sub`      | `Θ ⊢ₐ[N\|m\|P0] P ⊑ᴬ Q ⊣ Θ'` | `[P0] \| Θ ⊢^n_m P ⩽ Q ⊣ Θ'` | `\atypsub` |
| `a_consis`   | `Θ ⊢ₐ[F][Δ1\|Δ2\|P0] P ≈ Q ⊣ Θ'` | `[P0] \| Θ ⊢ P ∼ Q ⊣ Θ'` | `\aconsis` |
| `a_subtag`   | `Θ ⊢ᵗ[NM\|M\|P0\|Ψ] S ⊑ Q ⊣ Θ'` | `Ψ \| Θ ⊢^n_m S ⩽̇ Q ⊣ Θ'` | `\subtypedec = \dot{\leqslant}` |
| `a_consistag`| `Θ ⊢ᵗ[Δ1\|Δ2\|P0\|Ψ] S ≈ Q ⊣ Θ'` | `Ψ \| Θ ⊢ S ∼̇ Q ⊣ Θ'`  | `\consisdec = \dot{\sim}` |
| `a_inc`      | `Θ ≤[ρ] Θ'`               | `ρ ∷ Θ ⊑ Θ'`            | `\inc = #1 :: #2 ⊑ #3` |
| `a_split`    | `Θ ⊲ P0 ▹ P ⇢ Q ⊣ Θ'`     | `Θ ⊢ P0 ▷ (P→Q) ⊣ Θ'`   | `\split = \tright` |
| `a_unify`    | `Θ ⊲[F] α ≈ᵘ β ⊣ Θ'`      | `Θ ⊢ P ∼ Q ⊣ Θ'` (`≃` var-form) | `\unify` |

The pattern is uniform:
- **subtyping** is `⊑`/`⊑ᴬ` in mech, `⩽` in the paper;
- **consistency** is `≈` (+ turnstile `⊨`) in mech, `∼` (turnstile `⊢`) in the paper;
- the **decorated** system dots both (`⩽̇`/`∼̇`).

Note `⊑` is currently *spent* on subtyping in mech, whereas the paper uses `⊑`
for **information increase** (`a_inc`, where mech instead writes `≤[ρ]`). Freeing
`⊑` from subtyping lets `a_inc` match the paper.

### DECISION A — adopt the paper's `⩽`/`∼` for subtyping/consistency?

**Recommended: yes.** Sweep:
- `⊑` → `⩽` for `d_sub`; `⊑ᴬ` → `⩽` for `a_sub`; `⊢ₛ[M] … ⊑` → `⩽` for `d_pat_sub`.
- `≈` → `∼` and turnstile `⊨` → `⊢` for `d_consis`, `d_pat_consis`, `a_consis`.
- Frees `⊑` for `a_inc` to become `ρ ∷ Θ ⊑ Θ'` (paper-exact).

Cost: mechanical find/replace inside notation strings + rule bodies; ~450 (`≈`)
+ ~280 (`⊑`) + ~200 (`⊑ᴬ`) token sites, but almost all are *inside the notated
forms*, so the sweep is on the notation definitions + a global glyph replace in
proof scripts. Reversible.

### DECISION B — decorated system: combining dots are a problem

The paper distinguishes decorated subtyping/consistency with a **dot over the
symbol** (`⩽̇` = `⩽`+U+0307, `∼̇` = `∼`+U+0307). These are *combining characters*:
they render as a floating dot in editor/monospace fonts (this is the `⩽̇`
you flagged). **Do not put combining chars in Coq source.**

The decorated relations are *already unambiguously distinguished* from the plain
ones by the `⊢ᵗ` turnstile superscript and the `| Ψ` slot. So:

**Recommended:** decorated `a_subtag`/`a_consistag` reuse the **plain** `⩽`/`∼`
symbols — disambiguation is carried by `⊢ᵗ…|Ψ]`, not by a dot. (Alternatively,
if a visible marker is wanted, use a *superscript* `⩽ᵗ`/`∼ᵗ` — a spacing char,
not combining. But `⊢ᵗ` already carries the `ᵗ`.)

---

## 2. Collisions / redundancy to fix (safe, low-risk)

1. **`d_wf_utyp` has two notations** — `Γ ⊢ᵤ C` (inline `where`) and
   `Γ ⊢ᵤₜ C` (`decl/notations.v:16`). Drop the `⊢ᵤₜ` alias; keep `⊢ᵤ`.
2. **`d_wf_uskl` notation declared twice** — inline `where` (`decl/def_rules.v:184`)
   and again in `decl/notations.v:19`. Delete the `decl/notations.v` copy.
3. **`d_tags` / `d_tags_skl`** have *no* notation (always raw). Minor; give them
   the paper's `φ # Ψ` form (`\tags{Ψ}{φ}`) if desired — low traffic.
4. `a_sub_flex`, `a_subtag_flex`, `a_inc_equiv` have no notation (mutual helpers
   of notated relations). Acceptable; they are internal.

---

## 3. Scopes (objective 3)

Currently **nothing uses a custom scope** — every notation is in `type_scope`
or global. Recommend introducing scopes to (a) contain the dense algorithmic
overloads and (b) let the paper glyphs coexist:

- `Declare Scope fresco_scope` (delimiter `%fresco`), `Open Scope fresco_scope`
  in a central prelude. Move the **global** notations that currently leak
  (`∉`, `⌊ ⌋ˢ`, the `F=∅` overloads, `a_pat`/`a_typing`/`a_sub` where-clauses)
  into it, so they stop polluting the default scope.
- Keep the split judgment worlds legible by *convention* (decl at level 75,
  algo worklist at level 70) rather than separate scopes — separate scopes for
  decl vs algo would force `%`-annotations at every mixed use (soundness lemmas
  mention both), which is worse. One `fresco_scope` for everything Fresco-specific
  is the pragmatic choice.

**Low-risk immediate win:** move the four global leaks (`∉`, `⌊ ⌋ˢ`, `F=∅`
overloads, and the three where-clause turnstiles that omit `: type_scope`) into
`type_scope` / `fresco_scope` so nothing sits in the truly-global namespace.

---

## 4. Small operations — catalogue only (no rush)

These are high-traffic but *unnotated*; notating them is orthogonal to the big
judgments. Proposed paper-faithful notations (paper uses `T[φ/α]` bracket-after
for subst, juxtaposition `κP` for metasubst):

| Op | Uses | Proposed notation | Paper |
|---|---|---|---|
| `open_ptyp_wrt_ptyp A B` | 202 | `A ^ᵗ B` or `A ⟦B⟧` | `A[B/…]` open |
| `subst_ptyp_in_ptyp A' X A` | 198 | already `{A' ᵗ/ₜ X} A` (dead — adopt it) | `A[A'/X]` |
| `msubst_ptyp ρ A` | 243 | `ρ • A` / `[ρ] A` | `κ A` (juxtaposition) |
| `msubst_pskl ρ P` | 351 | `ρ • P` | `κ P` |
| `msubst_compose ζ ρ` | 250 | `ζ ∘ₘ ρ` | `κ∘κ'` |
| `ptyp_to_pskl A` | 275 | `⌊A⌋ᵖ` or a `Coercion` | `⌊·⌋` |
| conversion fns (`ptyp_to_btyp_*`, `pskl_to_bskl_*`, …) | 80–260 each | `Coercion` where injective, else superscript-tagged `⌊⌋` | erasures |

The dead substitution notations (`{_ ᵗ/ₜ _}`, `{_ ᵉ/ₑ _}`, `{_ ᵉ/ₜ _}`, `⌈ ⌉`)
already exist but are never used — a proof-script glyph sweep would adopt them
at zero definition cost.

Recommendation: do the big judgments + collisions + scope-leak fixes first;
tackle §4 as a separate, self-contained pass.

---

## 5. The system / sort axes — DONE 2026-08-09

§1 fixed the relation SYMBOLS. What it did not touch was the turnstile
DECORATIONS, and those had drifted into two genuine defects:

1. **One marker, two systems.** `ᵃ` meant `a_` in `a_wf_pskl` (`Θ ⨟ Δ ⊢ₚₛᵃ P`)
   but `ad_` in `ad_pat_consis` (`Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q`) / `ad_refine_syn`
   (`⊢ᵣᵃ`) / `ad_sd_typing` (`⊢ˢᵃ`) / `ad_pat` (`⊢ᵃ[ M ]`).
2. **The axes shared a device.** `a_consis` / `a_sub` / `a_pat` / `a_typing`
   wrote the SYSTEM as a subscript (`⊢ₐ[ … ]`), while the SORT is a
   subscript everywhere else (`⊢ₛ`, `⊢ₚₛ`, `⊢ᵤₛ`) — so the algorithmic and
   the decorated turnstile differed by sub- vs superscript `a` alone.

Resolved by giving each axis one device — **superscript = system, subscript =
sort** — and stating the sort exactly once (subscript where the system has one
relation per sort, bracket index `N`/`NM` where one relation covers both).
The canonical legend is the header of [`fresco/notations.v`](../fresco/notations.v);
`CLAUDE.md`'s style section points at it. What moved:

| relation | before | after |
|---|---|---|
| `d_pat` | `Γ ⊢[ M ] e ⇨ P` | `Γ ⊢ₛ[ M ] e ⦂ P` |
| `ad_pat` | `Θ ⊢ᵃ[ M ] e ⇨ Q` | `Θ ⊢ₛᵃᵈ[ M ] e ⦂ Q` |
| `a_pat` | `Θ ⊢ₐ[ m ; P0 ] e ⇨ Q ⊣ Θ'` | `Θ ⊢ₛᵃ[ m ; P0 ] e ⦂ Q ⊣ Θ'` |
| `a_typing` | `Θ ⊢ₐ[ m ; P0 ] e ⦂ B ⊣ Θ'` | `Θ ⊢ᵃ[ m ; P0 ] e ⦂ B ⊣ Θ'` |
| `a_consis` | `Θ ⊢ₐ[ Δ1 \| Δ2 \| P0 ] P ∼ Q ⊣ Θ'` | `Θ ⊢ᵃ[ Δ1 \| Δ2 \| P0 ] P ∼ Q ⊣ Θ'` |
| `a_sub` | `Θ ⊢ₐ[ N \| m \| P0 ] P ⩽ Q ⊣ Θ'` | `Θ ⊢ᵃ[ N \| m \| P0 ] P ⩽ Q ⊣ Θ'` |
| `ad_pat_consis` | `Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q` | `Ψ ⨟ Θ ⊢ᵃᵈ R ∼ Q` |
| `ad_pat_sub` | `Ψ ⨟ Θ ⊢ₛᵃ[ NM \| M ] R ⩽ Q` | `Ψ ⨟ Θ ⊢ᵃᵈ[ NM \| M ] R ⩽ Q` |
| `ad_refine_syn` | `Θ ⨟ Δ ⊢ᵣᵃ Q ⊳ P` | `Θ ⨟ Δ ⊢ᵣᵃᵈ Q ⊳ P` |
| `ad_refine_pskl`| `Θ ⨟ Δ ⊢ᵣₚᵃ P ⊳ Q`             | `Θ ⨟ Δ ⊢ᵣₚᵃᵈ P ⊳ Q` |
| `ad_sd_typing`  | `Θ ⊢ˢᵃ[ M ] e ⦂ B`             | `Θ ⊢ᵃᵈ[ M ] e ⦂ B` |
| `ad_partial_precise` | `Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ`     | `Θ ⨟ Δ ⊢ᵃᵈ P ⊑ᵖ[ Ψ ] ψ` |
| `a_wf_pskl`     | `Θ ⨟ Δ ⊢ₚₛᵃ P`                 | unchanged — already correct |

⭐ And the `ˢ` did not survive in the ad system either — for the same reason
one step further.  `ad_sd_typing` first became `⊢ˢᵃᵈ`, which stacks the VARIANT
mark `ˢ` on the SYSTEM mark `ᵃᵈ` and invites reading `ˢᵃᵈ` as one opaque system
name; the superscript must hold the system and nothing else.  Since there is no
`ad_typing`, `ˢ` had nothing to disambiguate from, so it is plain
`Θ ⊢ᵃᵈ[ M ] e ⦂ B`.  This also makes the three copies of typing differ by the
system mark ALONE — `⊢[ M ] e ⦂ A`, `⊢ᵃᵈ[ M ] e ⦂ B`,
`⊢ᵃ[ m ; P0 ] e ⦂ B ⊣ Θ'` — which is what §5 was for.  `⊢ˢ` survives only in
the declarative system, where `d_typing` and `d_sd_typing` genuinely coexist.

⭐ Note where the `ₛ` did NOT survive: `ad_pat_consis` lost it because the ad
system has no type-sort sibling to be told apart from, and `ad_pat_sub` lost it
because its `NM` index already names the sort — the same reason `a_sub` never
had one. Stating the sort twice is how `⊢ₛᵃ[ TY | … ]` came to read as a
contradiction.

⚠️ **`⇨` is retired.** It claims the term SYNTHESISES its skeleton, and that
holds only at `M = TI` — at `TC` the skeleton is an input, so the arrow was
wrong on the majority of the rules that used it. The three `*_pat` judgements
now write `⦂` and let the `ₛ` subscript say "skeleton", which is what the
paper does with its own mode-generic typing (`\typp`, `macro.tex:1087`; the
paper's `⇛`/`\TTo` marks the skeleton judgement, not synthesis, so the mech's
lookalike `⇨` was importing a meaning the glyph never had).

⚙ Sweep mechanics, for the next person who has to do one of these: the
context-free renames are literal-token substitutions, but four are
context-SENSITIVE, because `⊢ₐ[` and `⊢[` are each shared by two judgements
that differ only in the relation symbol several tokens later. Those were done
with a bounded regex whose middle forbids every other relation symbol (plus
`->`, `(*`, `*)`, blank line) — without that guard a comment block showing an
`a_extract` judgement several lines above a prose `⊑ᵖ[∅]` gets its own
turnstile marked (this really happened in `prop_extract.v`). Order matters:
mark the `*_pat` turnstiles WHILE `⇨` still distinguishes them, and only then
replace `⇨` with `⦂`. Script kept out of tree; ~1.7k substitutions in 79 files.

⚠️ Counting sites with `grep -r` over the build tree inflates the number ~4×:
`.vo` / `.glob` / `.aux` artifacts contain the notation strings too, and
`*.v.legacy` is not source. Restrict to tracked `.v` / `.md`.

## 6. Remaining notation residue (not done, deliberately)

1. **`a_solve_sub`'s `⊢ₛ` and `a_solve_consis`'s `⊢ₑ`** mark the SOLVE layer,
   not a sort — the one place a subscript still means something other than the
   sort axis. Fixing it needs a look-vs-solve marker pair (`a_looksub` has a
   bare `⊢`), and the two judgements cannot simply both become `⊢ᵃ`: `⊢ᵃ P ≼[ α ,
   m ]` vs `⊢ᵃ P ≼[ m ]` would leave camlp5 to factor two shared-prefix
   notations whose brackets differ only in ARITY. A separate pass.
2. **`⊢ˢ` (syntax-directed) sits next to `⊢ₛ` (skeleton)** — one glyph apart,
   distinguished only by height. It is not a defect under the scheme (the two
   axes own different devices by construction), and both markers are load-
   bearing in the declarative system, where `d_typing` / `d_sd_typing` /
   `d_pat` all coexist. Changing the sd marker means picking an arbitrary
   third letter; left alone rather than churned.
3. **Algorithm-internal judgements carry no system marker** (`a_looksub`,
   `a_solve_*`, `a_extract`, `a_assign`, `a_unify`, `a_split`, `a_tyequiv`).
   This is a rule, not an omission: the system marker exists to separate one
   relation's copies across systems, and these have no counterpart. Their own
   symbols (`≼ … ⤳`, `≔`, `≈ᵘ`, `▹`, `≡ᵗ`) already identify them.
4. **`a_wf_ptyp` / `a_wf_aenv` / `a_scope_pskl` have no notation** while
   `d_wf_ptyp` has `⊢ₚ`. `Θ ⊢ₚᵃ A` is the obvious form (~430 application
   sites); `d_wf_denv` is unnotated too, so the env-wf pair is at least
   symmetric. Worth doing with §4's small-operation pass.
