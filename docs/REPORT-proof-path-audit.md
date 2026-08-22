# REPORT — proof-path audit (2026-08-22)

Scope: `mechanization/frost/**.v` minus the two generated files.  Build green
before and after; the only tree change this pass is the `bcore` →
`look_pair_fold` rename (§6).

**Part I** is the architecture — how the development is layered and where the
proof path spends itself.  **Part II** (appendix) is the line-level duplication
survey.  Part I is where the structural saving is.

---

# Part I — the proof path

## 1  The layer map

```
   decl/          7,699    the declarative system  (d_)
        ↑  conservativity bridge — algo_decl/  3,473
   algo/         95,698    THE PAPER'S ALGORITHM  (a_)   — 41 files
        │          algo 18,915 · sub 18,161 · sub/look 24,079
        │          consis 18,256 · typing 11,109 · pat 5,178
        ↑  decoration — deco_algo/  8,010   (carries a_sub_sound)
        │
        ↑  ⭐ THE LIFT — ext_algo/prop_lift{,_typing}.v  12,898
   ext_algo/     59,197    THE EXTRACTABLE ENCODING (e_) — 48 files
        │          implementations ~5,000 · runners + BC orders
        │          ρ-pairing machinery 12,322 · termination 1,950
        ↓
   extraction
```

Total 189,497 lines.  **Two complete algorithmic developments** — 95.7k for the
paper's `a_` judgements, 59.2k for the executable `e_` ones — joined by a
12.9k-line lift.

## 2  ⭐⭐⭐ The path climbs the same ladder three times

There are ~12 judgements (guess, look×2, solve×3, cstr-fold, extract, consis,
sub, split, pat, typing).  **Each is traversed three times, by three different
bespoke inductions:**

| ladder | what it proves | lines |
|---|---|---|
| **L1** `algo/` | the paper's algorithm is sound and complete w.r.t. `decl/` | soundness 15,130 + completeness 34,099 = **49,229** |
| **L2** `ext_algo/` runners | the executable runner implements `e_` | `*_impl_complete` + `*_run_complete` = **3,712** |
| **L3** the lift | an `e_` derivation yields an `a_` one and back | the 12 `*_rel_e` rungs = **10,278** |

L1 is 51% of `algo/`.  L3's rungs, largest first: `a_typing_rel_e` 3129,
`a_assign_unify_consis_rel_e` 2300, `a_sub_sub_flex_rel_e` 1692,
`a_looksub_lookeq_rel_e` 1014, `a_pat_rel_e` 609, `a_solve_sub_rel_e` 469,
`a_solve_eq_rel_e` 451, then six more under 240.

L2 is cheap (3.7k) — the runners are thin over `e_`.  **The expensive
connection is L3, and its cost is not the transport itself.  It is ρ.**

## 3  ⭐⭐⭐ The real cost centre: the ρ-pairing

`a_` picks binder names cofinitely (any fresh atom); `e_` draws them from a
threaded supply (forced atoms).  So the lift cannot say "the two derivations
agree" — it must relate them **up to a growing partial correspondence ρ** on
atoms, carried through every rung.

Dedicated ρ machinery:

| lines | file | role |
|---|---|---|
| 5,272 | `prop_look_pair.v` | the look-pair fold-transport at ρ (`look_pair_fold_*`) |
| 5,025 | `prop_solve_rel.v` | the a→a transports at ρ |
| 1,564 | `prop_solve_det.v` | defines `rel_pskl`, the relational currency |
| 461 | `prop_look_equiv.v` | |
| **12,322** | | **plus** ρ threaded through the lift: 852 mentions in `prop_lift.v`, 370 in `prop_lift_typing.v`, 624 in `prop_solve_rel.v`, 416 in `prop_look_pair.v` |

A representative rung shows what ρ costs in the *statement* alone
(`a_solve_sub_rel_e`): of its premises, `rel_pskl ρ V` ×2, `flex_agree_rel ρ V`,
`V ⊆ ftvar Θ1`, `dom Ξ1 ∩ cols_l ρ = ∅`, `V ∪ cols_r ρ ⊆ S0`, and outputs
`Ξ1 = flex_pairs_l ρn`, `Ξ2 = flex_pairs_r ρn`, plus a leaked-opener column
`ρx` with two side conditions.  **Nine of its ~12 premises are ρ bookkeeping.**

⚙ Note `rel_pskl` is barely used outside the lift — only
`algo/prop_wf_preservation.v` and `algo/consis/prop_consis_rename.v` mention it.
It is lift infrastructure, not shared metatheory.

## 4  ⭐⭐⭐ The cheap route: HALF the obstruction is gone, half is live

⚠️ **CORRECTION (2026-08-23).**  The first version of this section claimed the
refutation of the functional currency was simply stale.  That was too strong.
The truth is sharper and more useful.

Both encodings carry a **complete equivariance kit**: `algo/prop_swap.v` is
3,050 lines and there are **43 `*_swap` lemmas** (21 `a_`, 22 `e_`) — one per
judgement on both sides.  The lift barely uses it:

| file | `_swap` | ρ |
|---|---|---|
| `prop_lift.v` | 5 | 879 |
| `prop_lift_typing.v` | 1 | 370 |
| `prop_solve_rel.v` | 2 | 624 |
| `prop_look_pair.v` | 0 | 416 |

There are **two** obstructions to a functional ρ, in two different files, and
they are not the same obstruction.

**(a) `prop_lift.v`'s header — opener vs. sibling FLEXIBLE.  This one is dead.**
It argues a left atom can be *"a binder in one premise and a generated flexible
in its SIBLING — LE-Arrow runs both halves at the SAME Θ, and the two side
conditions do not exclude each other."*  Three facts retire it: it self-flags
*"⚙ INFERRED … not machine-checked"*; it landed in `5528fd1` and the
CROSS-HALF FRESHNESS GUARD landed in `0b08fac` **after** it
(`git merge-base --is-ancestor` confirms the order); and that guard sits on
`a_lookeq__arrow` itself as `ftvar_in_a_cstrs C1 ∩ dom Ξ2 [=] empty` (+ mirror).
`LE-FlexR` emits its fresh atom **into the block** (`Ξ = α1 ~ abind_flex_mono`),
so `dom Ξ2 = {α1}`, and the leaked opener sits in `ftvar_in_a_cstrs C1` — the
guard forces them apart.  **This conflation can no longer happen.**

**(b) `prop_solve_rel.v` §9 — opener vs. sibling OPENER.  This one is LIVE.**

> *"⚠️ It CANNOT be global: §8c.25's Finding 1 is exactly a left atom with two
> right images, and that configuration is REACHABLE above the extract
> (`a_extract_rel_e` hands back a ρx column of leaked openers).  What saves the
> trio is that **a leaked opener is bound NOWHERE** — not in `Θ0`, not in `Ξ` —
> so `D` is taken to be the CONTEXT's DOMAIN."*

`rel_inj` / `rel_fun` already exist and are already maintained — but `rel_fun`
is **local, on `D` = the context's domain**, precisely because a leaked opener
is bound nowhere.  And the guard does **not** close this: it constrains
`C1` against `dom Ξ2`, never `C1` against `C2`.  Two sibling halves may each
leak a ∀ opener and **pick the same atom** — each ∀ row only requires
`β ∉ add α (ftvar Θ ∪ ftvar P ∪ ftvar P')`, which both halves satisfy at the
same `Θ`.  The supply keeps them apart on the right.  One left atom, two right
images.  **Live.**

### ⭐⭐ The missing guard is free on the e-side

The natural closure is a **third cross-half condition, opener vs. opener** —
and it would cost nothing to discharge, by exactly the argument that discharges
the existing two.  The e-side arrow row threads the supply **consecutively**:

```coq
| e_looksub__arrow : forall S0 S1 S2 Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2,
    {{ S0 ↝ S1 ⊨ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}e ->
    {{ S1 ↝ S2 ⊨ Θ ⊢ P2 ≼[ α , m ] P2' ⤳ Ξ2 ⨾ C2 }}e -> …
```

and `e_looksub_lookeq_cstr_ftvar_tight` (already proved) bounds
`ftvar_in_a_cstrs C ⊆ (S1 ∖ S0) ∪ ftvar P ∪ ftvar P'`.  The two generated
intervals `S1∖S0` and `S2∖S1` are **disjoint**, so the *generated* parts of `C1`
and `C2` are automatically apart.  A guard of the shape

```coq
(ftvar_in_a_cstrs C1 ∖ (ftvar_in_pskl P1 ∪ ftvar_in_pskl P1'))
  ∩ (ftvar_in_a_cstrs C2 ∖ (ftvar_in_pskl P2 ∪ ftvar_in_pskl P2')) [=] empty
```

is therefore a **theorem of the supply-threaded encoding**, like its two
siblings — "costs completeness nothing" in the same sense.

### ⛔ …but do NOT add it yet

Adding it now would put a premise on the rules **with no consumer**, and this
codebase has been burned by that twice on the record — `a_extract_rel_e`
carried a premise its only consumer could not satisfy, and the standing lesson
is *"a lemma proved for a consumer that does not exist yet can carry a premise
the consumer cannot satisfy."*  The guard is only worth adding **together with**
the `rel_fun`-goes-global work that consumes it, since the completeness proofs
(`a_looksub_solve_complete_gen`'s Arrow row, and its `eq` twin) would then have
to establish it.

**Sequence, if this is taken up:** (1) probe that (b) is the *only* remaining
source of two-right-images above the extract; (2) add the opener-vs-opener
guard and discharge it on the e-side from `e_looksub_lookeq_cstr_ftvar_tight`;
(3) strengthen `rel_fun` from local-on-`D` to global; (4) collapse `rel_pskl`
toward equality-under-a-renaming, rung by rung.  Only step 4 returns lines —
on the order of the 12,322 dedicated to ρ.

## 4b  ⭐⭐⭐⭐⭐ CAN `a_` AND `e_` BE ONE LAYER?  Yes — and they are already 2/3 merged

The two layers differ in exactly one thing: **how much global freshness they
impose.**  `e_` imposes total discipline (one counter, never reused).  `a_`
imposes only local discipline (each binder avoids its own context).  The lift
(12,898) plus the ρ tower (12,322) is the price of that gap — **~25k lines to
bridge two freshness conventions.**

### `a_` is NOT the paper's rules — it is the paper's rules plus a partial copy of `e_`

`algo/def_rules.v` carries **25 `[paper-gap]` side conditions**.  Classified:

| kind | count | what it encodes |
|---|---|---|
| **DISPATCH / PRIORITY** — ◇-dispatch ×2, absence-first ×5, ForallR-priority ×2, FlexR-priority ×1, solve-dispatch ×2 | **11** | the runner's **rule-selection order** |
| **FRESHNESS / UNIQUENESS** — cross-half ×2, cross-layer ×2, `uniq (Ξ ++ Θ0)`, `uniq (αs ++ Θ1)` | **~6** | the runner's **name discipline** |
| sort / encoding corrections (THE HAT, the split's `A'`, …) | ~8 | genuine mechanization gaps |

**Seventeen of the twenty-five exist only to make `a_` behave like `e_`.**  Each
was added when a proof demanded it, and each was justified the same way — *"IT
COSTS COMPLETENESS NOTHING.  It is a THEOREM of the supply-threaded encoding …
so the reference implementation — one global counter, never reused — cannot
violate it."*  The two layers have been converging **one guard at a time, by
accident rather than by plan.**

### The residual gap is narrow: name INVENTION, not binding

Binder rows are already fine — `a_`'s cofinite `forall β ∉ L` is equivariant by
construction, and 43 `*_swap` lemmas witness it.  The gap is the rows that
**invent a name into an output**: `a_lookeq__flex_r` emits
`Ξ = (α1 ~ abind_flex_mono)`, `a_guess_mono` likewise, and the five ∀ rows of
the collection leak their opener into `𝒞`.  `a_` chooses these existentially;
`e_` chooses them deterministically.  **That residue is the whole of what ρ pays
for.**

### ⭐ Controlled evidence: the guess rung exists in BOTH currencies

`prop_lift.v` §2 proved the guess rung in **chain** currency and §4 proved it
again in **relational** currency.  Same rung, two designs:

| | lines | statement | infrastructure needed |
|---|---|---|---|
| `e_guess_mono_lift_n` (chain, §2) | 212 | `exists S1 ps, e_guess_mono S0 P S1 (swaps_aenv ps Ξ) (swaps_ptyp ps A) /\ …` — **no ρ, no `rel_pskl`, no `cols_l/r`** | **none** |
| `a_guess_mono_rel_e` (rel, §4) | 183 | carries `rel_pskl ρ V` + the scoping premise | **the full 12,322-line ρ tower** |

**Per rung the two cost the same.  One of them needs 12k lines of scaffolding
and the other needs none.**  That is the clearest single measurement in this
report.

⚙ The chain currency was abandoned above the guess because *"a chain is a
FUNCTION on atoms"* and one left atom can need two right images (§4).  Half of
that obstruction is now dead (opener-vs-flexible, killed by the cross-half
guard); half is live (opener-vs-opener, which no guard yet forbids).

### Three single-layer designs

**A — finish the guard program (incremental, recommended).**  Keep adding
freshness guards to `a_` until *"every name a derivation invents is globally
distinct"* is a theorem of `a_` rather than only of `e_`.  Then ρ collapses to
the identity, `rel_pskl` degenerates to equality, and the lift becomes
**erasure of the supply index**.  The next concrete step is the
**opener-vs-opener guard** (§4), which discharges for free on the e-side from
`e_looksub_lookeq_cstr_ftvar_tight` plus the disjointness of consecutive supply
intervals.  Cost: the completeness proofs must establish each new guard.
Return: most of the 12,322-line ρ tower and the ρ premises in all twelve rungs.

**B — supply-index `a_` itself (the from-scratch design).**  One judgement:
define `a_X … := exists S0 S1, e_X S0 … S1 …` and prove the paper's rule shapes
admissible.  This is what one would build knowing what is known now.  ⛔ It is
**not reachable incrementally** — `algo/`'s 95,698 lines induct on `a_`
derivations, and every statement would grow a supply pair.

**C — status quo.**  Keep two conventions and pay ~25k to bridge them.

⚠️ One tempting shortcut does **not** work: normalising an `a_` derivation to
the supply's names *after the fact*.  The rebuilt derivation has different
outputs (`Ξ`, `𝒞` change with the invented names), so relating it to the
original needs exactly the renaming one was trying to avoid.  The win only
comes if the derivation is **built normalised in the first place** — which is
what design A achieves by making the discipline part of the rules, and design B
by making it part of the judgement.

⚙ `e_looksub_lift` / `e_lookeq_lift` (80 lines) are the "lift proper at ρ = nil"
corollaries — written, proved, and **never used**.  They are in the dead list.

## 5  Smaller structural observations

- **`deco_algo/` (8,010) is on the critical path**, not a side branch: the
  README flagship `a_sub_sound` is proved there, via the decorated algorithm.
  It is a fourth encoding of subtyping used purely as a soundness vehicle —
  worth a sentence in the paper's artifact description, since a reader will not
  guess it from the layer names.
- **The `sub`/`eq` halves are near-twins in size at every layer**
  (`a_looksub_solve_complete_gen` 3177 vs `a_lookeq_solve_complete_gen` 2887;
  `look_pair_fold_sub` 2392 vs `look_pair_fold_eq` 1188).  Unlike §A2 these are
  *not* verbatim duplicates — `a_looksub`/`a_lookeq` are genuinely mutually
  inductive with different signatures — so no cheap collapse exists.
- **`algo/sub/look/` is the single densest subtree**: 24,079 lines in 8 files,
  four of which are one theorem each (3177, 2887, 2879, 1496).

## 6  Ranked — structural first

| # | item | est. saving | risk | build green throughout |
|---|---|---|---|---|
| 1 | **§4 probe: is opener-vs-opener the ONLY live source of two right images?** | *decides* ~12k | none (a probe) | yes |
| 2 | §4 steps 2–4: opener-vs-opener guard, `rel_fun` global, collapse `rel_pskl` | 8–12k | high, staged rung-by-rung | yes, rung at a time |
| 3 | §A3 name the hypothesis pack + one `_weaken_tvar` transport | 900–1200 | low | yes, file at a time |
| 4 | §A6 delete the genuine-leftover third of the dead list | ~400 | very low | yes |
| 5 | §A4 merge the runner's seven binder clauses | ~560 | medium | yes |
| 6 | §A2 collapse `uskl`'s constructor pairs | ~2000+ | high | **no** — whole-tree |

Item 1 is half a day and gates the largest saving in the development.  Do it
before anything in Part II.

## 7  ✅ Landed 2026-08-23 — the binder-opening fact, named

`looksub_gen_open_tvar` (`prop_sub_cstr.v`, just above the theorem): *the
context-relative half of the invariant survives opening a fresh rigid binder.*
Nine facts — the two `binds` weakenings, `⊢ Θ` and `⊢ Θ0`, `α ∉ dom` on both,
`κ ∷ Θ0 ⊑ Θ`, and `a_wf_pskl` on `P0` and `Pi` — all at `(β ~ abind_tvar) ++ ·`.

It replaces hand-written blocks at **all three binder rows** of
`a_looksub_solve_complete_gen`: LS-ForallR and LS-ForallL at both tags.
(ForallR takes 8 of the 9 — it descends the *target*, so its `HwfP0β` is about
`open (ptyp_to_pskl A0) β` and stays local.)

⚙ **It is LOC-neutral** — 4031 lines before, 4031 after; the ~40-line lemma
exactly cancels what the three sites gave back.  The gain is structural: the
three ∀ rows now *say* "the invariant is stable under opening a binder" instead
of reproving nine side conditions each, and a fourth binder row would now cost
three lines instead of twenty.  Recorded honestly because it is the shape of
every remaining cleanup at this altitude — **the tractable structural moves in
this development are LOC-neutral; the LOC is locked behind the three projects
in §6.**

⚠️ `Set Implicit Arguments` is on in this file (line 69), so the lemma's type
arguments must be left to inference — passing them positionally fails with a
misleading "expected type `?κ ∷ ?Θ0 ⊑ ?Θ`".

### ⭐ New feasibility fact for §A2's 466-line duplicate

The tagged and untagged LS-ForallL rows share a **466-line byte-identical tail**
(only a comment differs).  Ltac cannot factor it (§A4).  But the tail
**calls the induction hypothesis exactly once** (`eapply (IHHsubty …)`, one
site).  So it *is* extractable as an ordinary lemma taking the IH's instance as
a hypothesis — the obstacle is only the ~50-hypothesis interface, not a
structural entanglement.  That converts §A2's local fix from "delicate, unknown"
to "tractable, one afternoon", and it does not need the whole-tree `uskl`
constructor merge.

---

# Part II — appendix: the line-level survey

## A1  How much of it is literal copy-paste

Measured by hashing every window of *meaningful* lines (blank and
comment-only lines dropped), then extending each repeated window to its
maximal length and greedily selecting non-overlapping families.

- **33,880 lines (22% of the tree)** sit inside an ≥8-line block that occurs
  more than once.
- **14,621 lines (9.4%)** would disappear if every maximal repeat family
  collapsed to a single copy.  569 families.

Worst offenders, by recoverable lines:

| recoverable | file | share of file |
|---|---|---|
| 1658 | `ext_algo/prop_look_pair.v` | 59% duplicated |
| 1346 | `ext_algo/prop_lift.v` | 38% |
| 1138 | `algo/consis/prop_completeness_consis.v` | 28% |
| 988 | `algo/sub/look/prop_sub_cstr.v` | 56% |
| 868 | `ext_algo/prop_lift_typing.v` | 52% |
| 753 | `algo/sub/prop_completeness_sub_gen.v` | 27% |
| 703 | `algo/sub/look/prop_eq_cstr.v` | 31% |

## A2  ⭐⭐⭐ Root cause A — `uskl`'s three constructor pairs

`pskl` has the unified seven constructors.  `uskl` has ten, because three
paper-level notions are each split in two:

| paper notion | `uskl` constructors |
|---|---|
| ∀ | `uskl_all_syn` / `uskl_all_tag ε` |
| ◇ | `uskl_hole` / `uskl_holeg` |
| ∀◇ | `uskl_tophole` / `uskl_topholeg` |

The erasure `⌊·⌋ˢ : uskl → pskl` collapses all three pairs — so **every ∀
case and every ghost case of every induction over `uskl` is written twice**,
and the mechanization says so out loud:

> `prop_sub_cstr.v:2932` — *"ForallL, untagged : **identical to the tagged
> row**; the mech splits the paper's single rule by the subject's POTENTIAL
> tag.  The only textual difference is the ρ-inversion and the absence of a
> binder tag from the subject's tags."*

Machine-checked cost in `a_looksub_solve_complete_gen` alone:

- `ForallL, tagged` (2256–2931) vs `ForallL, untagged` (2932–3506): after the
  ~100-line ρ-inversion prologues, the remaining **466 lines are
  byte-identical** — the two blocks differ in exactly **one word, inside a
  comment** (`sss_forall_l_tag` vs `sss_forall_l_syn`).
- `UnivGhostL` vs `UnivGhostLG`: another ~156 identical lines.
- `Ghost` / `GhostG`: both discharged as impossible, twice.

The same pairing accounts for the 196-line and 100-line twins in
`prop_eq_cstr.v` and the 175-line twin in `prop_look_pair.v`.

**Blast radius of the real fix**: 1,372 hand-written occurrences of the six
constructors, plus regeneration of `def_ott.v` and `prop_ln.v` from
`language.ott`.  This is the single largest conceptual saving available
(order 3–4k lines) and it is a multi-day, whole-tree change — it *cannot* be
done with the build staying green throughout.  Recommended only as a
dedicated campaign, and cheapest for the ∀ pair alone (`uskl_all` carrying an
`option εvar`), which is where most of the duplicated mass is.

## A3  ⭐⭐ Root cause B — the hypothesis pack has no name

`a_looksub_solve_complete_gen` takes **~45 hypotheses** and returns a
**~20-conjunct** existential.  Nothing names that pack, so every binder row
re-derives the whole of it by hand under `(β ~ abind_tvar) ++ Θ` — which is
precisely what the 453-line duplicate in §A2 *is*.

**The codebase already contains the fix, applied in exactly one file.**
`prop_eq_var.v` names its pack and proves the pass-through once:

```coq
Definition solve_eq_complete_var_concl (Θ0 Θ Θw Θr : aenv) … : Prop :=
  solve_ext Θ0 Θw Pi P0 L (solve_eq_complete_var_post Θ Θr κ Δ Ψi Ψa ψa).

Lemma solve_eq_complete_var_tophole_both : …   (* 8-line proof *)
Lemma solve_eq_complete_var_step          : …   (* 4-line proof *)
```

Each pass-through row then costs ~5 lines instead of ~100.  The measured
effect: `prop_eq_var.v` is **22% duplicated**, against 56% for
`prop_sub_cstr.v`, which imports `solve_ext` but never packs its *outer*
induction hypotheses.

**Recommendation (highest value / risk ratio).**  Give the outer pack of
`a_looksub_solve_complete_gen` / `a_lookeq_solve_complete_gen` a
`Definition`, and prove one `…_weaken_tvar` transport lemma:

```coq
pack Θ0 Θ … -> β ∉ L -> pack ((β ~ abind_tvar) ++ Θ0) ((β ~ abind_tvar) ++ Θ) …
```

Both ForallL rows and both UnivGhost rows then open with one `apply`.
Estimated saving 900–1,200 lines across `prop_sub_cstr.v` + `prop_eq_cstr.v`,
file-local, verifiable one file at a time.  This is the item to do first.

## A4  ⛔ Root cause C — and the hard constraint on fixing it by tactic

`look_pair_fold_sub` opens a binder at **seven** sites, and all seven carry
the **same 94 lines, byte-for-byte** (`prop_look_pair.v` 3666, 3770, 3874,
3985, 4262, 4366, 4480).  They exist because the runner `e_looksub_impl` has
seven distinct binder-opening clauses.

**This pass attempted the obvious factoring and it does not work.**  Recorded
so nobody repeats it: an Ltac1 body **globalises eagerly**, so every
identifier in a hypothesis position (`subst s`, `simpl in Hb2 …`,
`clear - HαV Hcov1`) *and* every identifier in a `constr` position
(`set (sf := supply_fresh Sb0)`, `assert (… α `in` Sa0)`) must already
resolve at *definition* time.  Driving the missing-identifier error to a fixed
point demanded **32+ parameters and was still growing**, and it began
demanding `r1` / `Hr1` — names the block itself *creates* via
`destruct … as [[r1 Hr1]|]`.  A tactic that must be handed 35 arguments is
worse than the duplication it removes.  The factoring was reverted.

⇒ **Corollary for all of §A1**: these blocks manipulate the proof context
(introducing and naming hypotheses), so tactic-level factoring is off the
table.  Only three mechanisms actually work here — a **named pack + transport
lemma** (§A3), an **extracted lemma** where the block is IH-free, or
**removing the case distinction at its source** (§A2, and merging the runner's
seven binder clauses).

## A5  ✅ Done this pass — `bcore` → `look_pair_fold`

`bcore` was opaque.  What it is: the **fused look-pair / fold-transport** —
side 1 a supply-threaded `e_looksub`/`e_lookeq` derivation together with its
constraint fold, side 2 the runner's computation, with the fold transported
across the atom-pairing ρ.  Renamed accordingly (134 occurrences, 1 file):

| was | now |
|---|---|
| `bcore_sub` / `bcore_eq` | `look_pair_fold_sub` / `look_pair_fold_eq` |
| `bcore_sub_stmt` / `bcore_eq_stmt` | `look_pair_fold_sub_stmt` / `look_pair_fold_eq_stmt` |
| `bcore_scp` `bcore_flx` `bcore_dr` `bcore_nonflex` `bcore_agr_base` | `look_pair_scp` `look_pair_flx` `look_pair_dr` `look_pair_nonflex` `look_pair_agr_base` |

Prose "b-core" / "b-CORE" updated to "look-pair fold" / "LOOK-PAIR FOLD".
`make coq` green, `README.v` still `Closed under the global context`.

## A6  Dead proofs — 2,746 lines

`docs/AUDIT-dead-names-2026-08-22.txt` lists every proof with **no reference
from any `.v` in the tree** (`README.v` included; glob-based) that is **not**
registered in a hint database.  201 proofs, ~2,746 lines.

⚠️ Not a delete list.  It mixes three kinds:
- genuine leftovers (e.g. `a_typing_swap` 123 L, `swap_aenv_one` 68 L, the
  five `*_no_loss` lemmas in `prop_swap.v`);
- **deliberate API** — `e_typing_run_complete_decl_check`,
  `e_sub_run_complete`, `e_consis_run_complete`, `e_pat_run_complete` are
  campaign deliverables that simply have no internal consumer;
- **cited-but-unused** — `a_looksub_lookeq_subst_stable_rev` (280 L) and
  `a_looksub_lookeq_subst_stable` (206 L) are named as prerequisites in
  `prop_sub_cstr.v`'s ForallL header comment.

Needs a human pass; the first group alone is ~400 lines of free saving.

## A7  Small findings

- `frost/algo/def_rules.v:319` cites `cex/probe_bcore_ug2_flexr.v`, **which
  does not exist** — a stale reference (the only `bcore` mention left in the
  tree after §6; deliberately not renamed, since the file it names is gone
  either way).
- The `sub` / `eq` halves are near-twins at every layer
  (`a_looksub_solve_complete_gen` 3177 vs `a_lookeq_solve_complete_gen` 2887;
  `look_pair_fold_sub` 2392 vs `look_pair_fold_eq` 1188;
  `a_solve_sub_rel_e` 469 vs `a_solve_eq_rel_e` 451).  Unlike §A2 these are
  *not* verbatim duplicates — `a_looksub` and `a_lookeq` are genuinely
  mutually inductive with different signatures — so no cheap collapse exists.
  Flagged only so it is not mistaken for §A2-style duplication.

