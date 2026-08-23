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

⚠️ **CORRECTED — see §4c.**  `a_` is **not** cofinite: only 3 of its 154 rules
are, and all three are well-formedness rules.  The algorithmic layer is
exists-fresh throughout, which is why equivariance had to be *proved* (43
`*_swap` lemmas) rather than come free.  The gap is the rows that
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

## 4c  ⭐⭐⭐⭐ THE ROOT: the ∀ rows LEAK their binder — diagnosis kept, PRESCRIPTION RETRACTED

**Why does `a_` still use cofinite quantification?  It does not.**  Only **3 of
154** rules in `algo/def_rules.v` are cofinite — `a_wf_pskl__all`,
`a_wf_ptyp__all`, `a_scope_pskl__all`, all *well-formedness* rules.  Every
algorithmic rule is **exists-fresh**: one named witness plus a `notin` on the
INPUTS.  The rules were cofinite once and were deliberately moved off.  The
reason is on the record, in `def_rules.v`'s header for the collection:

> *"ALL FIVE ∀ rules **LEAK** their binder — the reference implementation
> unbinds and DISCARDS the name in every one of them (`constr_collect_eq`:
> LE-ForallInh type.ml:579-583, LE-ForallSyn :595-598, LE-UnivGhost1 :610-613;
> `constr_collect_sub`: LS-ForallR :668-672, LS-ForallL :685-688), and neither
> function ever calls `bind_var`.  So the outputs `Ξ` and `𝒞` may mention the
> binder, **which is precisely what the old cofinite rendering forbade:
> sharing one `𝒞` across the whole family silently restricted the rules to
> vacuous binders.**"*

### The whole tower descends from that one fact

1. `type.ml` **unbinds a ∀ and discards the name** — it never re-binds.
2. ⇒ the outputs `Ξ` / `𝒞` may mention the opener: **the five ∀ rows leak**.
3. ⇒ **cofinite is unavailable** — a cofinite premise shares ONE `𝒞` across the
   whole family of `β`, which silently forces the binder to be vacuous.
4. ⇒ the rules become **exists-fresh**, one named witness each.
5. ⇒ equivariance stops being free and must be *proved*:
   `algo/prop_swap.v`, **3,050 lines**, 43 `*_swap` lemmas.
6. ⇒ two derivations that chose different witnesses can be related only by a
   **correspondence, not a function** — a leaked opener is bound *nowhere*, so
   one left atom can need two right images: **ρ, 12,322 lines**.
7. ⇒ and the freshness cofinite would have given structurally has to be
   re-imposed by hand, rule by rule, as `[paper-gap]` guards (cross-half ×2,
   cross-layer ×2, `uniq (Ξ ++ Θ0)`, `uniq (αs ++ Θ1)`).

### ⭐ The control experiment is already in the tree

`a_guess_mono` is the one judgement whose ∀ row **closes its witness away** —
its outputs do not mention `β`.  And it is exactly the one rung where the cheap
currency works.  `prop_lift.v`'s own header says so:

> *"§2 could use a chain only because `a_guess_mono` leaks NOTHING: its ∀ row
> closes its witness away, so every atom the derivation invents lands in
> `dom Ξ`."*

| | leaks? | currency | rung cost | infrastructure |
|---|---|---|---|---|
| `a_guess_mono` | **no** | chain (`swaps_*`) | 212 | **none** |
| the collection, solve, … | **yes** | relational ρ | 451–3129 | 12,322 |

**The disease and the cure sit side by side in the same file.**

### ⛔⛔ RETRACTION (2026-08-23): "go back to cofinite" is WRONG

The causal chain below is a correct *description*.  The prescription first drawn
from it — restore cofinite — is **wrong, and was already settled against.**

There is a **standing user directive**: *"drop cofinite encoding from the WHOLE
algo layer (decl stays cofinite) as a standing campaign"* (2026-07-31,
`60816a9`).  It is not a preference.  Cofinite **broke completeness**:

> `a_sub__forall_r` / `a_subtag__forall_r` used to quantify the DISCARDED junk
> suffix `Ξ` OUTSIDE their cofinite family — one `Ξ` for every fresh α.  That is
> not the paper's rule, and it breaks COMPLETENESS: **junk may lawfully mention
> the binder** (an `a_lookeq__flex_r` guess eq-constrained against it can be
> solved above it).

Two richer encodings were tried and rejected as well: a function-valued
`Ξf : atom -> aenv` inside the cofinite family (*exotic-name danger*), and a
binder-opened template suffix (*still α-dependent junk*).  The design space here
is explored; do not re-propose it.

### ⭐ What survives the retraction — and it is the useful half

**Closing an output is INDEPENDENT of cofinite.**  The two were conflated.  One
can close while staying exists-fresh:

```coq
    {{ Θ ⊢ₛ P ≼[ mode_tc ] (pskl_all_syn B)
       ⤳ Ξ ⨾ (pskl_all_syn (close_pskl_wrt_pskl β P')) }}a
```

— one named witness, as the directive requires, but the *result* is β-free.

⚠️ And it must be applied **only to outputs that are READ**.  `Ξ` is discarded
junk ("anything in `Ξ` is not mentioned in the result"), and the completeness
failure above is precisely about `Ξ`: closing it would re-break what the
de-cofinite fix repaired.  `𝒞` and the solve's `P'` *are* read, and are the
candidates.

### ⭐⭐⭐⭐⭐ THERE ARE **TWO** LEAKS.  One is forced and free; the other is chosen and costs 12k

This is the answer to *"I thought we have to go with the leaked one."*  You do —
but only for the leak that does not cost anything.

**Leak 1 — into `Ξ` (the discarded junk suffix).  FORCED.**  Closing it is what
broke completeness in the cofinite era: *"junk may lawfully mention the binder."*
⭐ But an atom in `Ξ` is in `dom Ξ` — it **is** bound — so `rel_fun` handles it
without complaint.  **This leak is free.**

**Leak 2 — into `𝒞` (the collected constraints, which are READ).  CHOSEN.**  It
mirrors `type.ml`'s unbind-and-discard; nothing in the algorithm demands it.
And it is *exactly* the `ρx` column.  From `prop_lift.v`'s own rung statements:

```coq
    /\ (forall a b, In (a, b) ρx -> a `in` ftvar_in_a_cstrs C)
    /\ cols_l ρx ∩ dom Ξ [=] empty
```

— an atom leaked into `𝒞` and **not** in `dom Ξ`.  That is verbatim the
"bound NOWHERE" class that `prop_solve_rel.v` names as the sole reason
`rel_fun` cannot be global:

> *"`rel_inj ρ V` — **GLOBAL**.  True by construction: every right atom is drawn
> ONCE, from a supply that only grows … `rel_fun ρ V D` — **LOCAL**, on a set
> `D`.  ⚠️ It CANNOT be global: Finding 1 is exactly a left atom with two right
> images … What saves the trio is that a leaked opener is bound NOWHERE — not in
> `Θ0`, not in `Ξ` — so `D` is taken to be the CONTEXT's domain."*

**Injectivity is already global and free.  Only functionality fails, and only
because of leak 2.**  That single class is what forces ρ to be a *relation*
instead of a *function*, and the relational currency is the 12,322 lines.

### ⚙ And leak 2 has no semantics anyway — the probe says so

`cex/probe_extract_conflated_opener.v` §2b: de-conflate the opener to a genuinely
fresh rigid `δ` — *"which is exactly what threading does"* — and

> *"the fold is **STUCK**: `1 ∼ δ` matches NO `a_solve_eq` row.  Not SolE-Unit
> (the target is not `1`), not SolE-Var (the subject is not a variable), not
> SolE-FlexR (`δ` is not hatted), not SolE-GhostL / SolE-VacuousR … and no ⫯ / ∀
> / → row."*

A constraint carrying a genuinely rigid opener **means nothing to the solver**.
The unguarded rules survived only by *accident* — the sibling had made the same
atom flexible, so `SolE-FlexR` fired on it — and the cross-half guard now
excludes that accident outright.

⇒ **The no-leak design for `𝒞` is the standard skolem-escape check**: when a
collected constraint would mention the opened rigid, reject.  That is already
the honest semantics (stuck = failure); making it structural turns a
freshness-guard-plus-ρ apparatus into a rule side condition, and **deletes `ρx`,
hence the reason `rel_fun` is local, hence the relational currency.**

⚠️ **What is not yet established**: that *no* reachable derivation needs a
𝒞-leaked opener to SUCCEED.  The probe shows one such configuration is stuck and
the guard excludes another; "every 𝒞-leak is stuck-or-excluded" is the theorem
to check, and it is a bounded probe — the same shape as the one already in
`cex/`.

### ⛔⛔ …but this does NOT collapse the two layers.  Nothing can.

**Determinism requires threaded state — a short argument.**  For `a_`'s invented
names to be determined (so that two derivations cannot disagree and ρ becomes
trivial), the choice must be a function of something.  At `LS-Arrow` **both
halves run at the same `Θ` with the same inputs in scope.**  A choice function
of the inputs therefore returns the *same* atom in both halves — a collision.
So the choice must depend on something that differs between the siblings, i.e.
**state threaded through the derivation.**  Threaded state *is* the supply.  That
is `e_`.

⇒ The design space has exactly **two** points, not three:

| | | cost |
|---|---|---|
| **(i)** `a_` nondeterministic + `e_` deterministic + a lift | today | swap kit + ρ + lift ≈ 28k |
| **(ii)** one judgement, supply threaded everywhere | §4d design B | supplies in every `algo/` statement, 95,698 lines |

Closing the read outputs does not create a third point.  What it does is make
**(i) cheaper**: it removes the leaked-opener class, which is what forces ρ to be
*relational* rather than functional (§4).  With no leaked openers, `rel_fun`
could go global, the chain currency would reach above the guess, and the ρ tower
(12,322) shrinks toward `e_guess_mono_lift_n`'s shape — zero shared
infrastructure.  **That is the real prize, and it is orthogonal to cofinite.**

### What "close the binder" means, concretely

The codebase already uses the word.  `a_solve_sub__forall_r`'s own comment:

> *"exists-fresh, INPUT-only freshness, **NO close**: the result passes through
> unchanged, so β may legitimately ESCAPE into `P'` … The leak is BY DESIGN;
> ill-scoped results are filtered downstream by wf side conditions
> (`a_sub__forall_l`'s `{{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a`), not by narrowing this
> rule.  **A cofinite rendering would demand ONE β-free `P'` for the whole
> family, degenerating the rule to 'fires only when the binder is vacuous'.**"*

**Today** — the premise runs under β and the conclusion hands back the *same*
`P'` at `Θ`, where β is not bound:

```coq
| a_solve_sub__forall_r : forall Θ P B Ξ P' β,
    solve_l_off P ->
    β `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl B ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ mode_tc ]
         (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₛ P ≼[ mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ P' }}a
```

**Closed** — the output is *abstracted over* β, and the premise **opens** it.
This is the standard locally-nameless idiom for a judgement whose OUTPUT binds,
and `close_pskl_wrt_pskl` is already generated by lngen:

```coq
| a_solve_sub__forall_r : forall L Θ P B Ξ P',
    solve_l_off P ->
    (forall β, β `notin` L ->
       {{ ((β ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ mode_tc ]
            (open_pskl_wrt_pskl B (pskl_var_f β))
          ⤳ Ξ ⨾ (open_pskl_wrt_pskl P' (pskl_var_f β)) }}a) ->
    {{ Θ ⊢ₛ P ≼[ mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ (pskl_all_syn P') }}a
```

⭐ **The comment's objection applies only to the raw output.**  "One β-free `P'`
for the whole family" degenerates the rule *if `P'` is the premise's literal
result*.  Once `P'` is the **closed** form and each member of the family opens
it, one shared `P'` is exactly right and the binder is **not** forced vacuous.
Cofinite was rejected while the output shape was held fixed.

**What it buys:** no name escapes, so equivariance comes free from the cofinite
induction principle (`prop_swap.v` largely unnecessary); `a_solve_sub_ftv` stops
being DISJUNCTIVE ("an output variable is an input variable *or* avoids
`dom Θ`") and becomes plain; and two derivations cannot disagree about the
opener's *name* because there is no name — ρ has nothing to relate.

**What it costs:** every CONSUMER of these outputs changes shape — it must open
what the rule closed, and the wf side conditions that currently filter
ill-scoped results (`a_sub__forall_l`) become structural instead.  `a_cstrs`
needs `open`/`close` (mechanical — it is a list of `a_cstr` holding a `pskl`).
And `type.ml` would call `bind_var` where it now discards, so the reference
implementation changes too.

⚠️ **The open question is completeness** — whether any judgement genuinely needs
an output that mentions the opener in a way abstraction cannot capture.
`a_guess_mono` already closes and works.  The cheapest test is **one rule**:
close `SolS-ForallR` alone, and see whether `a_sub__forall_l`'s wf side
condition can be replaced by the instantiation.

### ⇒ The real question is not about ρ.  It is: must the binder leak?

If the ∀ rows **closed** their opener — returning `𝒞` abstracted over it, the
`bind_var` the implementation never calls — then cofinite comes back, and with
it free equivariance, a functional chain, and no ρ.  That is one design change
at the *root* of the causal chain above, against ~15–25k lines of consequence.

⚙ The leak is not obviously essential.  The implementation *unbinds and
discards*, i.e. treats the name as irrelevant afterwards; and the information
the leak actually carries — "this constraint arose under a binder, so its
solution may not mention it" — is exactly what a **bound index plus a scope
check in the solve** would carry, and arguably carries it better: a scope
violation becomes a structural impossibility rather than a freshness side
condition to be re-imposed at five separate rules.

⛔ But it is a change to the ALGORITHM, not to its encoding — the paper's rules
and `type.ml` both leak today.  It belongs in a design discussion, not a
cleanup pass.  The cost of *not* doing it is now measured: items 5–7 above.

## 4d  ⭐⭐⭐⭐⭐ "Can we just keep `e_` and delete `a_`?"

**Soundly?  Yes — and the tree already contains the proof.**  The two layers are
proved interderivable in *both* directions:

| direction | where | count |
|---|---|---|
| `a_` → `e_` | the lift's `*_rel_e` rungs (campaign closed 2026-08-22) | 12 |
| `e_` → `a_` | `e_*_sound` | 32 |

So **`a_` adds no expressive power.**  It is a presentational layer: it lets the
flagship theorems be stated in the paper's vocabulary, without a supply index.

### The clean form of the change (not "delete" — "demote")

- `e_` becomes the only **`Inductive`**.
- `a_X … := exists S0 S1, e_X S0 … S1 …` becomes a **`Definition`**, so the
  README's statements stay supply-free and still read like the paper.
- The paper's 154 rule shapes become **admissibility lemmas** — each cheap
  (apply the `e_` rule, thread the supply).
- `algo/`'s inductions move onto `e_`'s induction principle.

**Deleted:** `prop_swap.v` (3,050) and the 43 `*_swap` lemmas; the lift
(12,898); the ρ tower (12,322); and the six freshness `[paper-gap]` guards,
which become derivable.  **≈ 28,000 lines.**

**Paid:** `algo/`'s **95,698** lines restated and re-proved over the indexed
judgement — **750 `induction` sites, 2,874 `inversion` sites, 12 mutual
schemes**, and every statement grows an `S0`/`S1` pair with monotonicity
bookkeeping.

### ⛔ Verdict: right design, wrong move

**As a migration it is a bad trade** — touch 95,698 lines to delete 28,000, with
the build red for the duration.  **As the design for a system being built now it
is clearly correct**, and worth writing down for the next calculus.

⚙ One subtlety that decides *why* it would be simpler, and it is not "fewer
judgements".  Defining `a_X` as *"there exists a supply run"* is only faithful
to the paper if the judgement does not depend on **which** supply — i.e. it
needs supply-independence, which is equivariance again.  The reason the
`e_`-only design still wins is sharper: **you never have to move between two
runs.**  Soundness works from *any* run, completeness produces *some* run, and
nothing ever relates two.  ρ exists in the current design precisely because the
lift must relate a run to a non-run.

### ⭐ …but this is a symptom, and §4c is the disease

The `a_`/`e_` split is not itself the redundancy — **the leak is.**  Close the ∀
rows' binder and cofinite returns, equivariance is free, the chain currency
works, and ρ disappears **while both layers stay**.  Same ~15–25k saved, against
a design change at one point instead of a 95k-line migration.

**Ordering, then:**

| | change | saves | disruption |
|---|---|---|---|
| 1 | **close the READ outputs** (`𝒞`, the solve's `P'`) — exists-fresh, NOT cofinite, and NOT `Ξ` | ~12k (the ρ tower) | one design change at the root |
| 2 | finish the guard program (§4b design A) | ~12k | incremental, staged |
| 3 | demote `a_` to a `Definition` over `e_` | ~28k | **95,698 lines re-proved** |
| 4 | status quo | — | — |

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

