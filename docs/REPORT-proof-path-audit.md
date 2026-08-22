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

## 4  ⭐⭐⭐⭐ THE FINDING — the refutation that killed the cheap route is **stale**

Both encodings carry a **complete equivariance kit**: `algo/prop_swap.v` is
3,050 lines and there are **43 `*_swap` lemmas** (21 on `a_`, 22 on `e_` —
`a_typing_swap`/`e_typing_swap`, `a_looksub_lookeq_swap`/`e_looksub_lookeq_swap`,
and so on for every judgement).  A user directive on record calls equivariance
"THE renaming primitive".

**The lift barely uses it.**  Measured `_swap` mentions vs ρ mentions:

| file | `_swap` | ρ |
|---|---|---|
| `prop_lift.v` | 5 | 879 |
| `prop_lift_typing.v` | 1 | 370 |
| `prop_solve_rel.v` | 2 | 624 |
| `prop_look_pair.v` | 0 | 416 |

The functional route (a *swap chain*, ρ as a function, ideally identity) was
tried and **explicitly refuted** in `prop_lift.v`'s header (§2/§3):

> ⛔⛔ *"A chain is a FUNCTION on atoms … ALL FIVE of the collection's ∀ rows
> LEAK their binder into `𝒞` … So a LEFT atom can be a binder in one premise
> and a generated flexible in its SIBLING — **`LE-Arrow` runs both halves at
> the SAME `Θ`, and the two side conditions … do not exclude each other.** …
> ONE left atom needs TWO right images and no chain can supply them."*

**Three facts put that refutation in doubt:**

1. It **flags its own status**: *"⚙ INFERRED from the two rules' side
   conditions, **not machine-checked**; what IS machine-checked is that the
   relational form goes through."*  It is an argument, not a counterexample.
2. It is **stale by one commit**.  The refutation landed in `5528fd1`
   (2026-08-19); the **CROSS-HALF FRESHNESS GUARD** landed in `0b08fac`
   *after* it (`git merge-base --is-ancestor` ⇒ refutation first).
3. The guard forbids **precisely the conflation the refutation relies on**, and
   it is on `LE-Arrow` itself — the very rule cited:

```coq
| a_lookeq__arrow : forall Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2,    (* LE-Arrow *)
    (* [paper-gap] CROSS-HALF FRESHNESS GUARD — see [a_looksub__arrow]. *)
    ftvar_in_a_cstrs C1 ∩ dom Ξ2 [=] empty ->
    ftvar_in_a_cstrs C2 ∩ dom Ξ1 [=] empty ->
```

The leaked opener of half 1 lives in `C1`; the sibling's generated flexible
lives in `dom Ξ2`.  The guard makes them disjoint — so the "one left atom, two
right images" situation is **excluded by the rules as they now stand**.  The
guard's own comment notes it "COSTS COMPLETENESS NOTHING" and is a theorem of
the supply-threaded encoding, so it is not a restriction that would have to be
paid for elsewhere.

⚠️ This is a **hypothesis**, not a result.  The refutation may still hold for a
reason other than the one it gives (the ∀ rows of the *solve* layer,
`SS-ForallR`, also leak by design, and the guard does not speak about them).
But it is the largest structural question open in the tree, and it is cheap to
settle.

**Recommended next step — one probe, not a refactor.**  In the codebase's own
`cex/probe_*.v` idiom, attempt to build the two-right-images configuration
*under the current rules*, i.e. a derivation where one `a_` atom must map to two
distinct `e_` atoms with both cross-half guards in force.  Half a day.
- If it **cannot** be built, the chain/identity currency is back on the table
  and the prize is most of the 12,322 lines of ρ machinery plus the ρ premises
  in all 12 lift rungs.
- If it **can**, the probe becomes the machine-checked counterexample the
  header admits it never had, and the ρ design is vindicated on the record.

Either outcome is worth having; only one of them is worth 12k lines.

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
| 1 | **§4 probe: is the ρ-relation still forced?** | *decides* ~12k | none (a probe) | yes |
| 2 | §4 if the probe clears it — collapse ρ to a chain/identity | 8–12k | high, but staged rung-by-rung | yes, rung at a time |
| 3 | §A3 name the hypothesis pack + one `_weaken_tvar` transport | 900–1200 | low | yes, file at a time |
| 4 | §A6 delete the genuine-leftover third of the dead list | ~400 | very low | yes |
| 5 | §A4 merge the runner's seven binder clauses | ~560 | medium | yes |
| 6 | §A2 collapse `uskl`'s constructor pairs | ~2000+ | high | **no** — whole-tree |

Item 1 is half a day and gates the largest saving in the development.  Do it
before anything in Part II.

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

