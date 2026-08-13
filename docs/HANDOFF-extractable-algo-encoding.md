# HAND-OFF — a second algorithmic encoding whose freshness is not a premise, and extraction from it

Two technical TODOs, recorded 2026-08-13.

> **TODO (1)** — add a SECOND algorithmic encoding in which a rule's freshness
> side condition does not constrain its own OUTPUT, and prove it equivalent to
> the encoding the tree has today.
>
> **TODO (2)** — on top of (1), make the new encoding EXTRACTABLE.

## ⭐ STATUS 2026-08-13 — **TODO (1) IS COMPLETE**; TODO (2) is spiked, not scaled

`frost/ext_algo/` (~5500 lines).  **Every algorithmic judgement is threaded
and bridged** — `guess^TY`, `assign`/`unifyvar`/`consistency`, the constraint
COLLECTION, the SOLVING layer, `extract`, `a_sub`/`a_sub_flex`, `a_split`,
`a_pat` and `a_typing`.  `make coq` green, `README.v`'s 32 assumption reports
all "Closed under the global context", zero admits.

Read §7 before anything else: it is the REVISED plan and supersedes parts of
§4/§5.  §7.6 is the milestone board; §7.7–§7.15 are the per-milestone results.
⚠️ §0–§5 are the ORIGINAL spec and several of their statements have been
overtaken — each is marked where it happens.

⛔ **What is left is TODO (2) at scale.**  M1.7 proved the Bove–Capretta
pipeline end to end on `guess^TY` (§7.1, §7.7) — a domain predicate in `Prop`,
`Equations … by struct` on it, clean OCaml with no `Acc`/`Fix_sub`/proof
residue, axiom-free.  Nothing else has a runner yet.

---

## 0. Why this is worth doing

`frost/algo/def_rules.v` states the operational judgements EXISTS-FRESH: a rule
names the atom it opens a binder at and constrains it.  For most rows that
constraint mentions only inputs, which is unobjectionable.  But **eleven rows
constrain their own OUTPUT** — `β ∉ dom Θ1`, where `Θ1` is what the premise
produced (`def_rules.v:936,956,962,967,972,1030,1039,1046,1296,1312,1319,1337`;
each is marked `(* prose-completion (Barendregt) *)`).

A rule that filters what its own premise produced is a fair thing for a reader
to be suspicious of: a priori it can REJECT where the reference implementation
succeeds, because there a global counter makes the collision impossible and no
check is ever needed (`benchmark/Fresco/lib/type.ml:558-561`, `incr counter`).

The tree already answers that objection — see §1 — but it answers it as a
META-theorem *about* the encoding, not by removing the premise.  Two things
follow:

- a reader must be pointed at eleven side lemmas to be convinced the encoding
  is honest, and
- ⛔ **nothing here is executable.** The judgements are `Prop`-valued
  `Inductive`s, so there is no `Fixpoint`/`Definition` for Coq to extract, and
  the tree currently contains **zero** `Extraction` commands.  The paper ships
  an OCaml implementation (`paper/artifact/implementation/lib/type.ml`) that is
  entirely unverified and related to the mechanization only by our reading of
  it.  (2) is what would close that gap.

## 1. ⭐ (1) IS HALF DONE ALREADY — and this is the main thing to read first

`frost/algo/prop_swap.v` §13b proves exactly the intended statement, for three
rule groups, as the eleven `*_no_loss` lemmas (`a_sub_flex_*_no_loss`,
`a_assign_*_no_loss`, `a_unify_*_no_loss`).  Their argument IS the design the
TODO asks for:

> A derivation is finitely supported, so a `γ` fresh for its WHOLE OUTPUT always
> exists, and equivariance moves the run to that `γ` — whereupon the output
> premise is discharged.  So the rule fires whenever the premise-free version
> would, with the run's GENERATED names transposed and nothing else touched.

The machinery is in place: `a_sub_swap_junk` (`prop_swap.v:1499`),
`a_sub_flex_swap_junk` (`:1518`), `swap_junk_dom_out` (`:1541`),
`a_assign_swap_junk` (`:1571`), `a_unify_swap_junk` (`:1592`),
`a_consis_swap_junk` (`:1606`) — each fixing every INPUT pointwise while moving
the output.

So (1) is **not** new mathematics.  It is: promote that argument from eleven
statements ABOUT the relation into a second `Inductive` WITHOUT the output
premises, plus the two-way bridge.  ⚠️ The `*_no_loss` lemmas are the `->`
direction of that bridge for three groups; the missing groups are `a_pat`,
`a_typing` and the `a_sub`/`a_solve_*` binder rows (65 `notin` occurrences in
`def_rules.v` overall — most are input-only and need nothing).

⚙ If (1) lands, the eleven `*_no_loss` lemmas stop being reader-facing
justification and become the bridge's proof obligations, and the `⛔` keeper
note on them (`prop_swap.v` §13b, `docs/AUDIT-dead-names.txt` `[E]`) can go.

## 2. The two shapes for (1), and which to pick

### (1a) Swap the output — "freshness by transposition"

The rule picks any atom satisfying an INPUT-only condition; collisions with the
output are repaired after the fact by transposing the derivation.

- ✅ Closest to what is already proved (§1): the swap kit is the whole of it.
- ✅ Nothing becomes stateful, so every existing lemma keeps its shape.
- ⚠️ Still not executable on its own — "pick any atom" is not a function.  (2)
  would then have to add a name supply anyway.

### (1b) A global avoidance set threaded as STATE — ⭐ THE CHOSEN ROUTE

Every algorithmic component carries a fresh-name supply (an `atoms` avoid-set,
or a counter) in and out, exactly as the reference implementation does.
Freshness becomes "the supply hands you a name", which is a FUNCTION, not a
side condition.

- ✅ Mirrors `type.ml`'s `counter` directly, so the extracted code and the
  paper's implementation are structurally comparable — which is the real prize.
- ✅ Makes (2) tractable: with a supply threaded, the judgements can plausibly
  become `Fixpoint`/`Equations` returning `option`, and the `Prop` relation
  becomes their specification.
- ⚠️ Touches EVERY rule and every lemma statement in `algo/` — this is the
  expensive option.  Do not start it without deciding §4's measure question.
- ⚠️ It also re-opens a decision the tree deliberately made once: `Δ`/`Ψ` are
  `list atom` and freshness is currently a RELATION, which is what lets the
  metatheory use strong elimination.  A state-threaded rule set is harder to
  reason about, so the equivalence proof in (1) is what pays for it — do not
  MIGRATE the metatheory, keep both and bridge.

**⭐ DECIDED (user, 2026-08-13): (1b) is the route.**  The reason is fidelity,
not convenience — a threaded avoidance set *is* what the implementation does
(`type.ml`'s `counter`), so the new encoding is a model of the real algorithm
rather than a third description of it, and the extracted code in (2) can be
diffed against `type.ml` structurally.

(1a) remains useful as an intermediate if the (1b) bridge proves hard: it is
almost free given §1, and it isolates "freshness is repaired by transposition"
from "freshness is supplied by state".  Take it only if needed — do not build it
speculatively, and in either case the `*_no_loss` kit is the thing to
GENERALIZE, not to re-derive.

## 3. What "equivalent" has to mean

Two directions, and only one of them is the interesting one:

- `new -> current`: needs the output-freshness premise to be RE-ESTABLISHED,
  i.e. the transposition argument of §1.  ⚠️ This is where the work is.
- `current -> new`: should be structural (the new rules have strictly fewer
  premises), modulo the supply in (1b).

⚠️ State it over the SAME contexts, not up to renaming, or the bridge will not
compose with the soundness/completeness theorems, which fix `Θ0`/`Θ1`.  The
`*_swap_junk` lemmas are already stated in the composable form (inputs fixed
POINTWISE) — copy that discipline.

## 4. Traps already known

- ⚠️ **The measure.** `a_typing`'s completeness runs on a lexicographic
  `(size_exp, size_btyp)` and `ad_pat_sub_fuel` carries an explicit fuel.  A
  state-threaded encoding must not disturb either.  ⭐ Settle the (2)-side
  measure BEFORE writing rules — see §5, where it is the TERMINATION question
  and the paper turns out to give no help at all.
- ⚠️ ~~**`a_pat`'s four binder rows are still COFINITE**~~ — ⛔ **OVERTAKEN
  2026-08-13**: they were CONVERTED, in `frost/` itself, at the user's
  direction.  See §7.13 for the decision and §7.15 for what it cost (net −250
  lines, all four flagships re-closed).  The asymmetry this bullet asks about
  no longer exists.
- ⚠️ **Well-formedness judgements are cofinite ON PURPOSE** (`a_wf_ptyp`,
  `a_scope_pskl`, `a_wf_pskl`).  They are static, not runs; do NOT thread a
  supply through them.
- ⚠️ The four check rows of `a_typing` also carry two MECH-ONLY Barendregt
  premises, `uniq (Ξ ++ Θ2)` and the scoping condition (audit §1.1/§1.2).
  Those are a different problem with a different fix (the `a_typing_output_wf`
  merge) — do not conflate them with the output-freshness premises here, and
  ideally land that first, since it changes the same four rows.
- ⚠️ `a_guess_mono__arrow` runs both halves at the SAME `Θ`, which is why
  `AT-Abs` needs `uniq (αs ++ Θ1)` (audit §1.3).  A threaded supply makes that
  premise derivable — ⭐ so (1b) subsumes audit §1.3, which the audit had
  written off as "not worth it" at 316 occurrences.  Worth noting as a payoff.

## 5. What (2) needs beyond (1) — TERMINATION is the real obligation

> ⭐ **PARTLY SUPERSEDED BY §7** (2026-08-13, after reading McTT / Type
> Inference Logics / the worklist prior art).  §7.1 replaces this section's
> "the deliverable is a well-founded recursion with a real measure" with a
> Bove–Capretta domain predicate, under which the measure is NOT needed to
> define the runner; §7.3 sharpens the paper finding below.  Everything this
> section says about *why* fuel was rejected, and about the
> termination ⟹ totality ⟹ decidability chain, still stands.

⛔ **The paper never argues that its algorithm terminates.**  Checked
2026-08-13: `terminat*` / `decidab*` appear in `paper/sections/` only as
background on the undecidability of full System F inference
(`introduction.tex:460,463`, `overview.tex:79`), never about Frost's own
algorithm; and `algorithmic.tex`, `implementation.tex` and
`full-algo-spec.tex` contain no measure, no well-founded order, no size
induction.  So termination is **not** an obligation the mechanization skipped
— it is one nobody has discharged, and (2) cannot avoid it: a Coq `Fixpoint`
must be shown to terminate before it exists at all.

⭐ **This is worth telling the authors** whether or not (2) is ever done — an
algorithm shipped with an implementation and a completeness theorem, but no
termination argument, is a gap of the same kind as the ones already in
`PAPER-GAPS.md`.  ⭐ See §7.3: confirmed by the user, and WT expects the
argument itself to be mostly straightforward.  ⚠️ Not yet filed there: file it only after confirming the
claim against the final paper, since a reviewer may read
`thm:complete-type-inference` as implying it (it does not — completeness says
a derivation EXISTS, not that a search finds it in finite time).

**⛔ DECIDED (user, 2026-08-13): NO FUEL.  Prove termination directly.**
⭐ And it is not a blocker — see §7.3.

A fuel parameter would make the function exist today at the cost of leaving the
real theorem unstated — and worse, a fuel-bounded runner is not the algorithm:
its `None` conflates "untypable" with "ran out", so it cannot even be compared
against `type.ml`, which has no such parameter.  ⚙ The tree's existing fuel
idiom (`ad_pat_sub_fuel`) is a PROOF device for a completeness induction and is
not a precedent for the runner.

So the deliverable is a well-founded recursion with a real measure, via
`Equations … by wf` (or `Function`), and ~~the measure is the open research
question of (2)~~ — ⛔ **both halves of that sentence are withdrawn**: §7.1
replaces `by wf` with a Bove–Capretta domain predicate, and §7.3 records that
the measure is an ordinary obligation rather than a research question.

⚠️ **The measure is NOT the one completeness uses.**  `a_typing_complete` runs
on a lexicographic `(size_exp, size_btyp)` over the DECLARATIVE derivation.
What has to decrease here is the ALGORITHM's own state as it steps, and the
run does things that measure does not see: it INVENTS flexible variables
(`a_guess_mono`), it grows `Θ` under binders, and `a_sub`/`a_solve_*` recur on
a context rather than on a subterm.  Candidate shape, to be confirmed rather
than assumed — a lexicographic combination of
  (i) the number of unsolved flexibles in `Θ`,
  (ii) the ∀-depth / size of the subject and counterpart,
  (iii) the size of the term,
which is the standard shape for worklist-style inference and matches how the
existing files already split their inductions.  ⭐ Check the reference repo
`jiangsy/proof_worklist_remechnization` first — a worklist measure for a
closely related algorithm is exactly the prior art, and the naming conventions
here were already taken from it.

⚙ **Extraction of well-founded recursion is fine, contrary to folklore.**
`Acc` is `Prop`-valued, so extraction ERASES the accessibility argument and the
result is an ordinary OCaml recursive function.  (An earlier draft of this file
claimed the proof "leaks into the extracted term" — that was wrong.)  The real
practical nuisance is the `Fix_sub` / `FixWf` wrappers `Program`/`Equations`
generate, which obscure the output until inlined; `Extraction Inline Fix_sub`
(or `Equations`' own extraction support) handles it.  So the choice between
`Equations` and `Function` is about proof ergonomics, not extractability.

### A note on the word: termination vs decidability

They come apart here, and the distinction decides how much is owed:

- **Termination** — the runner always returns. This is what (2) needs.
- **Decidability** — `{typable} + {~typable}`, a `sumbool` in `Type`. Strictly
  more: the NEGATIVE branch obliges you to refute every derivation, which for
  a rule set with nondeterministic rows (split/guess) is the hard half.
- ⚠️ Do NOT get decidability by extracting a `sumbool` proof: Coq erases
  `Prop`, so the extracted program follows the shape of the PROOF, not of the
  algorithm, and resembles nothing in `type.ml`.

⭐ **Soundness + completeness of the runner DO imply decidability**, and the
derivation is two lines — case on `run x`:

- `Some r` → soundness gives `a_typing x r`, so `exists r, a_typing x r`;
- `None` → if some `r` were typable, completeness would give
  `run x = Some r'`, contradicting `None`.  So `~ exists r, a_typing x r`.

⚠️ **The step that makes this work is `run` being TOTAL**, which is why
termination has to come first and why the fuel shortcut was rejected: a
fuel-bounded runner's `None` means "untypable OR out of fuel", and the second
disjunct is exactly what the argument above must rule out.  Proved directly,
the measure discharges it and `None` means untypable, full stop.

So the dependency is **termination ⟹ totality ⟹ (with soundness +
completeness) decidability** — one direction, no shortcuts, and decidability
is then a corollary worth stating for the paper rather than a separate
obligation.

### The shape of the deliverable

Coq erases `Prop` at extraction, so today's judgements have no computational
content and yield literally nothing.  What has to exist is a FUNCTION in
`Type` — `Definition a_typing_run : … -> option (btyp * aenv)` — with the
`Prop` relation as its specification:

- soundness: `run … = Some (B, Θ1) -> a_typing …`
- completeness: `a_typing … -> exists r, run … = Some r`

⚠️ **Completeness of the RUNNER is a new theorem, and probably the bulk of
(2).**  The rule set is not syntax-directed everywhere — the split and guess
rows branch — so the function must commit to a SEARCH STRATEGY, and the
existing `a_typing_complete` says nothing about it: it is completeness w.r.t.
the DECLARATIVE system, i.e. a declarative derivation implies *some*
algorithmic one, not that this strategy finds one.  Expect to have to show the
strategy exhaustive.

**Then the mechanical part:**

- `Extraction` directives + a driver, and a differential test against
  `benchmark/Fresco` — the benchmark suite (`Bench`, `Doe`, `Fcif`, `HML`,
  `MLF`, `Rosi`, `SuperF`, …) is already checked into the repo root and is the
  obvious oracle.
- ⚠️ `test/test_examples.v` is the existing regression surface; extraction
  should reuse its cases rather than invent new ones.

## 6. Status

⛔ **Not started.**  No branch, no code.  §1 is the only part that exists, and
it exists as metatheory, not as an encoding.

⚙ Superseded 2026-08-13: `frost/ext_algo/def_supply.v` exists (M0).  See §7.6.

---

## 7. REVISION 2026-08-13 — after reading McTT, Type Inference Logics, and the worklist prior art

Prompted by the user, who named McTT and *Type Inference Logics* as references
and pointed out that the sharp undecidability result to cite is the one for
**impredicative polymorphic subtyping**, not the weaker "System F type
inference is undecidable".  Five findings; two change the plan for (2)
materially, one sharpens the paper finding, two are cautions.

### 7.1 ⭐⭐⭐ THE RUNNER DOES NOT NEED THE MEASURE IN ORDER TO EXIST — Bove–Capretta

McTT (`~/Documents/HKU/Research/mctt_ref`) defines **every** executable
component the same way — `theories/Extraction/{Evaluation,Readback,NbE,Subtyping,TypeCheck}.v`:

```coq
Inductive eval_exp_order : exp -> env -> Prop := …          (* the CALL GRAPH *)
Equations eval_exp_impl m p (H : eval_exp_order m p)
  : { d | eval_exp m p d } by struct H := …                 (* recursion ON IT *)
Lemma eval_exp_order_sound : … -> eval_exp_order m p.       (* TOTALITY, apart *)
```

The function recurses **structurally on a `Prop` domain predicate** while
returning a `Type`.  That is legal, and not by any exception: no Prop→Type
elimination happens.  The branches match on the *Set* arguments, and each
recursive call's sub-derivation is produced by inverting `H` in a **`Prop`**
goal — which the guard checker accepts as a structural subterm.

⭐ **Verified in this exact switch** (Coq 8.20 + Equations), on a probe whose
state argument both shrinks and grows so that no structural or lexicographic
argument exists.  Extraction gives:

```ocaml
let rec run s = function
| L n -> add n (length s)
| N (t0, t1) -> let r = run s t0 in add r (run (Cons (r, s)) t1)
```

Domain predicate erased; `sig` erased to its carrier; **no `Acc`, no
`Fix_sub`, no `Obj.magic`, no proof residue** — the user's standing bar (§8)
met by construction rather than by cleanup.  The probe also carried a
higher-order premise (`forall r, dom (r :: s) t2`), i.e. a domain predicate
may quantify over values *earlier calls produce* — which is exactly what a
threaded supply needs (`forall S1, e_guess_mono S0 P S1 Ξ A -> … S1 …`).

Consequences, each of which changes the milestone order:

- ⭐ §5's "the deliverable is a well-founded recursion with a real measure, via
  `Equations … by wf`" is **superseded**.  The measure is not needed to DEFINE
  the runner, only to prove its domain predicate inhabited.
- ⭐ Termination stops being a precondition of writing the code and becomes a
  separate theorem, `<precondition> -> <judgement>_order …`.  So a runner can
  land before termination is settled — and can land with an **explicit, honest
  precondition** instead of a false claim of totality.
- ⭐ The M1.5 hazard largely evaporates.  The domain predicate is read off the
  rules mechanically, so the measure no longer constrains the STATE design;
  only the totality proof depends on it.  M1.5 is downgraded from "gate on M2"
  to "settle before claiming totality".
- ⚠️ What BC does **not** give is a TOTAL `run`: the derivation is an argument.
  Decidability still needs totality, so §5's
  termination ⟹ totality ⟹ decidability chain is untouched — which is what
  makes 7.3 load-bearing rather than decorative.

### 7.2 ⭐ CLEAN EXTRACTION IS A TECHNIQUE, AND McTT SHIPS IT

`theories/Extraction/PseudoMonadic.v` — 51 lines of `sumbool`/`sumor`
"failable bind" combinators (`let*b`, `let*o`, …) with `Extraction Inline`, so
a chain of decisions extracts as plain nested matches instead of a tower of
`left`/`right` plumbing.  **Copy it; do not reinvent.**  ⚙ Its header also
records why it cannot be a type class (Coq issue #19452: no extractable
polymorphism across `Prop` and `Set`) — which is the trap one would otherwise
hit while trying to tidy it.

### 7.3 ⭐⭐ THE PAPER'S TERMINATION GAP IS SHARPER THAN §5 SAYS

§5 says termination is "one nobody has discharged".  True, and an
understatement.  **The undecidability of impredicative polymorphic subtyping
is the paper's own stated motivation**, cited twice as
`\citep{chrzaszcz1998poly,tiuryn1996subtyping}`:

- `overview.tex:79` — "We cannot simply extend such systems with arbitrary
  implicit polymorphic instantiation as this is an undecidable problem"
- `introduction.tex:463` — "even implicit polymorphic instantiation itself
  (question ③) is undecidable"

and the design principle offered in answer is `declarative.tex:856-860`:

> "A fundamental principle of \Calc is to **never guess polytypes out of thin
> air**.  Instead, we only guess polytypes that can be determined by inherited
> type information."

So the paper's argument is: *the general problem is undecidable, therefore we
restrict guessing to what the skeleton determines.*  That is an argument that
Frost **is** decidable, and it is nowhere discharged.  The gap is therefore
not hygiene — **the payoff of the paper's central design decision is
unproved**, and a reader who reaches `thm:complete-type-inference` having read
`overview.tex:79` will read decidability into it.  Completeness does not give
it: a derivation EXISTS is not a search TERMINATES.

⭐ **And it says where the measure lives.**  If the reason the search
terminates is "every polytype guessed is determined by the inherited
skeleton", then what decreases is SKELETON structure — the ghosts and tagged
∀s the skeleton supplies are finite and get consumed — not type structure.  A
measure whose top component is a type size is looking in the wrong place.
⚠️ To be confirmed against the rules, but a far sharper starting point than
§5's guessed three-way shape.

⭐ **CONFIRMED BY THE USER (2026-08-13), with one important qualification.**
The reading above is right — the paper does argue for decidability without
discharging it.  But from the user's discussion with WT, **the termination
argument itself is expected to be mostly straightforward**, so this is a
missing-argument finding, not a suspected-false one, and it is **not a blocker
for (2)**.

Two consequences for this file:

- ⛔ §5's "the measure is the open research question of (2)" is **withdrawn**.
  It is an obligation, not a research problem.  §7.1 already removed it from
  the critical path (the runner exists without it); WT's assessment removes
  the residual risk that it cannot be discharged at all.
- ⚙ So M1.5 stays low-priority, and the right time to do it is when a runner
  wants totality — not before.  Do not treat it as a gate anywhere.

### 7.4 ⚙ THE MEASURE PRIOR ART IS ON DISK, AND ONLY HALF OF IT TRANSFERS

`~/Documents/HKU/Research/worklist_betterfe/mech/systems/feb/algo_worklist/prop_termination.v`
(2707 lines) is the concrete instance of §5's `proof_worklist_remechnization`
pointer.  Its result is `a_wl_red_ss_sn : ⊢ᵃʷ Γ -> Acc a_wl_red_ss_lt Γ`, off a
**five**-component lexicographic measure
`(exp_size_wl, judge_size_wl, split_depth_wl, num_etvar_wl, weight_wl)`.

- ✅ The VOCABULARY transfers, and §5's guessed three-way shape is a sub-list
  of it: the component it was missing is **split depth**.
- ⚠️ `exp_size` there is an inductive RELATION, not a function, because that
  tree's binders are cofinite; totality comes from wf (`exp_size_wl_total`).
  Frost's `a_typing` is exists-fresh, so a plain `size_exp` function may do —
  check before copying the relational form, it is a large tax.
- ⛔ **The SHAPE does not transfer.**  That algorithm is a WORKLIST: one state,
  one small-step relation, so termination is strong normalization and `Acc` is
  the natural formulation.  Frost's is fourteen big-step mutually recursive
  judgements with no single state — there is no step relation to be `Acc` on.
  A second, independent reason BC (7.1) fits Frost where `by wf` does not.
- ⚠️ Its hard case is a forewarning: four etvar-split rules INCREASE
  `num_etvar`, repaired by a "2-step" argument (the reduct has a forced next
  step that drops a higher-priority component).  Frost's `a_split` rows will
  want the same trick.

### 7.5 ⚙ TYPE INFERENCE LOGICS — read; mostly NOT adoptable, two things kept

Carnier, Pottier & Keuchel, OOPSLA 2024 (paper only; no local development).

- ⛔ Its central device is **intrinsic scoping**: types are indexed by a
  `World` (the live existentials), so freshness is a typing property and the
  side conditions disappear ("we leave corresponding freshness side-conditions
  implicit", §3.1).  **Not adoptable**: Frost is locally-nameless with named
  atoms in `Θ`, and re-indexing every sort is a whole-tree rewrite.
  ⚙ Its weakening `w ⊑ w'` with transport `_[_]` is precisely this tree's
  existing `a_inc` / `κ ∷ Θ0 ⊑ Θ` — the abstraction is already here under
  another name.
- ⚙ **Its artifact's representation is HYBRID, and the distinction matters if
  one goes looking for prior art on freshness.**  §5: "We represent
  existentials using a hybrid approach based on well-scoped de Bruijn indices
  and names … used for computations and 'decoration', respectively."  So names
  ARE in the artifact, but only for human-readable output; the computational
  representation is intrinsically-scoped de Bruijn.  Their admission "we do
  generate fresh names but we do not prove that names are sufficiently fresh,
  i.e. that no shadowing occurs" is about the DECORATION names — the
  computation needs no freshness proof because scoping makes it vacuous.
  ⭐ So TIL offers **no** prior art on the problem this hand-off is about
  (proving a named generator fresh); it offers a way to not have the problem,
  at a cost the tree cannot pay.
- ⭐ KEEP 1 — `fresh : World -> Evar`, deterministic, used explicitly at each
  introduction.  That is exactly `def_supply.v`'s `supply_fresh`, and
  independent confirmation that the deterministic gensym belongs in the
  FUNCTION layer and not in the rules.
- ⭐ KEEP 2 — the general lesson of its benchmark (§5.1): what dominated the
  extracted program's running time was the REPRESENTATION, not the verified
  algorithm.  ⚠️ Be precise about what it measured, because the two costs it
  names are not ours: a linear-time free-monad bind (Voigtländer's classic
  problem), and a quadratic overhead in the Prenex monad because unary `nat`
  de Bruijn indices must ALL be incremented each time an existential is
  introduced.  Neither is a fresh-name scan.
  ⚙ **Our own instance of the lesson**, which is an observation about metalib
  rather than a TIL finding: `supply_fresh` is `Atom.fresh (elements S)`, and
  `Atom.fresh` folds `max` over the list, so it is O(|S|) per call and O(n²)
  for n names — against `type.ml`'s O(1) `incr counter`.  ⭐ CONSEQUENCE,
  already honoured in `def_supply.v`: **the rules must touch the supply only
  through `α ∉ S` and `add α S`**, so the representation can be swapped — or
  realized as an `int` counter at extraction — without touching a rule or a
  bridge.
- ⚙ Its correctness statement is a single iff via a weakest-precondition
  semantics (`WP (synth Γ e) Q ↔ ∃…`), replacing separate soundness and
  completeness.  Elegant, but it presupposes the free-monad formulation; for
  Frost the two-statement form of §5 stays.

### 7.6 The revised milestone order

- **M0 ✅ DONE** — `frost/ext_algo/def_supply.v`.  Records two findings of its own:
  a `nat` counter is *impossible* over sealed metalib atoms (`nat_of` is
  exported, no injection back), and `supply_fresh` does not reduce inside Coq
  (every metalib generator is behind the same opaque ascription) though it
  does extract.
- **M1** — unchanged: `e_guess_mono` state-threaded, bridge both ways, and the
  `uniq (αs ++ Θ1)` payoff.
- **M1.5 — DOWNGRADED, no longer a gate.**  Record the measure candidate from
  7.3 + 7.4; do not spend a session on it.  It is now owed only by the
  totality theorem, which can follow the runner.
- **M1.7 ✅ DONE** — `frost/ext_algo/def_guess_impl.v`.  The BC spike passed on every
  count; see §7.7.
- **M2 ✅ DONE** — `frost/ext_algo/notations.v` (the `}}e` scope),
  `frost/ext_algo/def_consis.v` (all 28 rules of the
  `assign`/`unifyvar`/`consistency` block, threaded), `frost/ext_algo/prop_consis.v`
  (§1 supply growth, §2 the domain upper bound, §3 helpers, §4 the bridge, §5
  its projections).  **Ten premises retired; the bridge is closed and
  axiom-free.**  See §7.8.
- **M3a ✅ DONE** — `frost/ext_algo/def_look.v` + `frost/ext_algo/prop_look.v`: the
  CONSTRAINT-COLLECTION cluster (`a_looksub` / `a_lookeq`, 19 rows), threaded,
  with growth / block / bridge and ⭐ the `a_sub__forall_l` payoff.  See §7.9.
- **M3b — PIPELINE ✅ DONE, `a_sub` BRIDGE OPEN.**  `def_solve.v` /
  `prop_solve.v` (`a_solve_sub` / `a_solve_eq`, 21 rows mutual, + the
  constraint fold's 3: growth, block, output bound, bridge), `e_guess` in
  `def_guess.v` / `prop_guess.v`, `def_extract.v` / `prop_extract.v` (the
  collection → solving → guess pipeline, bridged), and `def_sub.v` /
  `prop_sub.v` (`a_sub` / `a_sub_flex`, 16 rows threaded; §1 growth).
  ⭐ **TODO (1)'s definitional target is COMPLETE** — all eleven
  output-constraining rows are now stated without the premise.
  ⛔ **OPEN: the `a_sub` bridge.**  Its shape is settled and written at the
  top of `prop_sub.v`; see §7.10 and §7.12.
- **M4 ✅ DONE** — `frost/ext_algo/def_pat.v` (`e_split` 3 rows + `e_pat` 10),
  `frost/ext_algo/def_typing.v` (`e_typing` 13), with `prop_pat.v` and
  `prop_typing.v`.  ⭐ **TODO (1) IS COMPLETE: every algorithmic judgement is
  now threaded, and every one of them is bridged.**  See §7.14.

⚙ **LOCATION (user, 2026-08-13): the directory is `frost/ext_algo/` and the
namespace `src.frost.ext_algo.*`** — it sits beside `algo/`, `algo_decl/` and
`deco_algo/`, which is what it is: another rendering of the same system, not a
development parallel to `frost/`.

### 7.7 ✅ M1.7 RESULT — the spike passed, and it found one more thing

`frost/ext_algo/def_guess_impl.v`: `e_guess_mono_order` (the call graph, `Prop`),
`e_guess_mono_impl` by `struct` on it, `e_guess_mono_order_total`, and the
argument-free `e_guess_mono_run` with its soundness.  The extracted OCaml is
in the file's header verbatim.  Three results:

- ✅ **The extracted program is clean.**  Domain predicate erased, `lc_pskl`
  erased (so `e_guess_mono_run` eta-reduces to `e_guess_mono_impl`), `sig`
  erased; no `Acc`, no `Fix_sub`, no `Obj.magic`.  The only non-obvious line is
  `| Pskl_var_b _ -> assert false (* absurd case *)`, which is what a
  hand-written implementation writes for an unreachable input.
- ✅ **Axiom-free.**  `Print Assumptions` on `e_guess_mono_impl`,
  `e_guess_mono_run` and `e_guess_mono_run_sound` all say "Closed under the
  global context" — `Equations` contributed nothing, given
  `derive(equations=no,eliminator=no)`.
- ⭐⭐ **NEW FINDING — `type.ml` ALREADY THREADS, so M1's structural change is
  the faithful reading and the existing encoding is the departure.**
  `benchmark/Fresco/lib/type.ml:97-100`'s arrow case is
  `let l, a = aux l Any a in let l, b = aux l Any b in l, TArr (a, b)` — the
  accumulator is threaded through both halves.  `a_guess_mono__arrow` runs
  both at the same `Θ`, which is exactly what costs `AT-Abs` its
  `uniq (αs ++ Θ1)` premise.  ⚙ Row for row the rest of the extracted function
  matches `guess` too (`l`↔`gr_block`, `incr counter`↔`supply_fresh`+`add`,
  `Bindlib.unbind`/`bind_var`↔`open`/`close`, `UGhost p -> aux l k p`↔the
  `Pskl_tophole` row); the one remaining difference is accumulator shape
  (cons onto one list vs concatenate two).

⚠️ **Four traps the spike paid for, all of which will recur at every later
judgement:**

- The tree's substitution notations (`{ A' ᵗ/ₜ α } A`, `frost/notations.v:215`)
  **shadow Coq's `sig` notation**, so `{ r | spec r }` — the return type the
  whole BC pattern is built on — does not parse, and the error names the
  substitution glyphs and nothing else.  Write `sig (spec …)`.
- **Do not `Set Implicit Arguments` in an implementation file.**  The impl's
  `S0` and `P` are inferable from its derivation argument, so the flag makes
  them implicit and the RECURSIVE CALLS inside the `Equations` block read
  `impl S0 P _` as passing `S0` for `H`.
- The obligation tactic must `unfold` the spec **after** inverting `H` and
  **before** `eauto`: the arrow row's second call gets its order argument by
  applying the higher-order premise of `ego_arrow` to the *first* call's
  result, which sits in the context wrapped in the spec definition.
- Without `ExtrOcamlNatInt`, metalib atoms extract as **unary `nat`**
  (`S (nat_list_max xs)`).  Not a footnote — a wall.  McTT imports it in
  `theories/Entrypoint.v`.

### 7.8 ✅ M2 RESULT — ten premises retired, bridge closed

**Ten premises gone in one file.**  `frost/ext_algo/def_consis.v` states the block
without any of: the eight `β ∉ dom Θ1` rows (`def_rules.v:936,956,962,967,972,
1030,1039,1046`), and `Assign-SolveM`'s `uniq βs` and generated-name filter
(`:896-898`) — the last two because `e_guess_mono`'s M1 invariants prove them.
Every rule is in the same order as its `frost/algo` twin and tagged with which
of four differences it carries (`Δ-thread` / `Δ-drop` / `Δ-supply` /
`Δ-guess`), so the two files diff line by line.

⚠️⚠️ **`def_rules.v:879-882` warns against exactly this, and the warning is
right where it stands.**  It says a used-name set `F` "cannot coexist with the
§13b argument, which needs `β ∉ F` — false at a premise running at `add β F`".
That is an objection to putting a supply on *those* rules, whose freshness
premises are justified BY §13b's transposition argument; a supply and that
argument cannot both be the justification.  Here there is nothing to coexist
with — the premises are gone, and what justifies the encoding is the supply
invariant plus the bridge.  ⚙ The warning's other half ("a mech-only device
the paper does not have") is answered by §7.7: `type.ml` does have it.

**What the bridge says** (`e_assign_sound` / `e_unify_sound` /
`e_consis_sound`, all `Closed under the global context`): a threaded run is a
run of `frost/algo`'s encoding, over the SAME contexts — inputs fixed
pointwise, `Θ1` carried across unchanged.  ⭐ So the second encoding is a
front end to the existing metatheory, not a parallel development: composed
with the bridge, every theorem over `a_*` applies verbatim.

Two hypotheses, both the supply's own discipline: `uniq (inputs)` (a
re-attaching row discharges `β ∉ dom Θ1` partly from "β is not in the STRIPPED
context", which is uniqueness) and supply coverage.  ⚠️ The consis component's
coverage must include **`Δ1` and `Δ2`** — the ∀ rows' side condition names
them and they are reachable from neither the context nor the skeletons.

⭐ **The lemma that does the work is `e_assign_unify_consis_dom_upper`**:
`dom Θ1 [<=] dom (inputs) ∪ (S1 ∖ S0)`.  Read against a re-attaching row it IS
the retired premise — the walked-past `β` is in `S0` and not in the stripped
context, so it is in neither summand.  ⚙ Its mirror, bounding the domain from
BELOW, already exists as `a_assign_unify_consis_dom_mono`
(`algo/consis/prop_consis_rename.v` §1); the two together pin the output.

⚙ **Three proof-engineering notes for M3, all learned here.**

- The `uniq` and output-coverage facts had to ride in the bridge's MOTIVE as
  extra conjuncts.  They are mutually needed with the bridge (`Arrow` alone
  forces output-coverage: its second premise runs at `Θ1` and `S1`), and a
  separate bundle would traverse all 28 rows again.
- §2's 27-of-28 uniform close works because a **name-free** `Ltac`
  (`lazymatch`-guarded, or the `repeat` loops) first turns every derivation in
  context into its growth fact.  A `Combined Scheme` goal has auto-generated
  hypothesis names, so spelling them breaks on any rename.
- §4 could not be name-free — each row needs its own `uniq` and coverage
  side-derivations — so it uses explicit `intros` per row and `clear - …;
  fsetdec` at every set step, per CLAUDE.md's `fsetdec` scoping rule.

### 7.9 ✅ M3a RESULT — the collection cluster, and the second `uniq` payoff

`frost/ext_algo/def_look.v` (19 rows) + `frost/ext_algo/prop_look.v`.  Taken before
`a_sub`/`a_sub_flex` because the collection is CLOSED — `a_looksub` and
`a_lookeq` call only each other — while `a_sub__forall_l` consumes a
collection's output block `Ξ`, so threading the subtyping walk first would
leave a hole in the supply exactly where the collection deposits names.

⚙ **Different shape from M2, and worth knowing before M3b.**  The collection
has NO OUTPUT CONTEXT: `Θ` goes in, nothing comes back, and generated names
leave in `Ξ`.  So its invariants are `e_guess_mono`'s, not `e_assign`'s —
growth, block-in-output-supply, block-fresh-for-input-supply, hence `uniq Ξ` —
and there is no domain upper bound and no `uniq`-preservation obligation.  All
hypothesis-free.

⚠️ **No row here constrains its own output**; the collection's freshness side
conditions were already input-only.  So unlike M2 this retires no `Δ-drop`
premise directly.  What it buys is the accounting:

⭐ **`a_sub__forall_l`'s `uniq (Ξ ++ Θ0)` is now derivable**
(`e_looksub_uniq_app`).  `def_rules.v:1253-1256` states that premise as a
prose-completion of the paper's *fresh* `Ξ`, needed because LE-FlexR and
`a_guess_mono`'s hole rule pick arbitrary names.  Threaded, both halves are
theorems.  This is M1's `AT-Abs` payoff at the second of the two sites that
comment names — so between M1 and M3a, **both** of the tree's `uniq`
prose-completions on generated blocks are now consequences.

⚙ **One proof-engineering lesson, worth copying at M3b.**  State the block's
freshness as SET ARITHMETIC (`dom Ξ ∩ S0 [=] empty`), not as
`∀ γ ∈ dom Ξ, γ ∉ S0`.  The `∀γ` form forces a per-row `specialize` whose
`match goal` is fragile under `Combined Scheme`'s auto-generated names; the
set form lets ONE `fsetdec` close every row, and it lets growth,
block-in-supply, block-freshness and `uniq` all ride in a single conjunctive
motive (`e_looksub_lookeq_block`) — the arrow rows' `uniq (Ξ1 ++ Ξ2)` is then
literally "the left block is inside S1 and the right block misses S1", which
is `fsetdec`'s job.  The `∀γ` shape is recovered as a corollary for consumers.

⚠️ And the CLAUDE.md banner-comment trap bit twice here: a quoted phrase
inside a `(* … *)` box swallows the `*)`, because the `"` opens a string that
the terminator then falls inside.  Keep quoted prose out of boxed comments.

### 7.10 ✅ M3b step 1 — the solve layer, and what the tree already knew

`frost/ext_algo/def_solve.v` + `frost/ext_algo/prop_solve.v`.  Both compiled first try,
which is the recipe from §7.9 paying off: state the block's freshness as set
arithmetic, put growth / in-supply / `uniq` / `ftvar ⊆ dom` in ONE conjunctive
motive, and close 24 rows with one tactic.

⭐⭐ **THE TREE HAD ALREADY MADE M1'S ARGUMENT HERE, FOR M1'S REASON.**
`a_solve_sub__arrow`'s comment (`frost/algo/def_rules.v:683-693`):

> "THE SIBLING PREMISE THREADS, `Ξ2 ++ Ξ1`.  Both halves may now GENERATE
> names, and a guess avoids only what its own context mentions — run both at
> `Θ` and the two blocks can pick THE SAME atom, making `Ξ1 ++ Ξ2` non-uniq
> and silently conflating two independently-invented flexibles … Running the
> second half at `Ξ1 ++ Θ` makes disjointness DERIVABLE … **and it is what the
> reference implementation does anyway (one global counter, never reused).**"

That is the M1 finding — including the appeal to `type.ml`'s counter — reached
independently, four rows earlier in the same file.  ⚙ So the tree carries TWO
conventions for one problem: the solve layer and `a_extract` thread by hand
(through the CONTEXT, as a stand-in for a supply), while `a_guess_mono__arrow`
does not, which is exactly what costs `AT-Abs` its `uniq` premise.  A supply is
the uniform version of a device this layer already uses.

⚠️ **The context threading STAYS.**  It is not merely an avoid-set here:
`a_solve_eq__flex_r` asks whether a variable is hatted (`a_flex_tvar Θ α`), so
an arrow row's second premise must SEE the flexibles the first invented.  The
supply is added alongside it.  ⚙ That forces a fourth conjunct on the block
lemma — `ftvar_in_aenv Ξ [<=] dom Ξ` — because the bridge must move the
context `Ξ1 ++ Θ` into the supply, and for the `Ξ1` half it can only do so by
knowing the block mentions nothing beyond its own names.  Expect the same at
`a_extract`.

### 7.11 The bridge premises cost nothing — machine-checked

A fair question about §7.8: does a bridge with hypotheses (`uniq (inputs)`,
supply coverage) buy a weaker guarantee, or reach the extracted program?

- **Extraction: no.**  The bridges are `Prop` and are erased wholesale; the
  Bove–Capretta runner recurses on a domain predicate that never mentions
  them.  §7.7's extracted `e_guess_mono_impl` takes `s0` and `p` and nothing
  else.
- **Guarantee: unchanged.**  Both premises are INITIALISATION conditions and
  both re-establish themselves along a run — that is what §7.8's two extra
  motive conjuncts (`uniq Θ1`, `ftvar_in_aenv Θ1 [<=] S1`) are FOR.  At the
  entry point the context is `nil` and the driver CHOOSES `S0`, so taking it
  to be what the inputs mention makes coverage `reflexivity`.
  ⭐ `e_consis_sound_init` (`prop_consis.v` §6) is that corollary, and it is
  **hypothesis-free**.  ⚙ It is also what `type.ml` does at its own entry
  point: start the counter, start the context empty.

## 8. Standing bar for (2) (user, 2026-08-13)

⭐ **The extracted program must be clean and carry no proof concepts.**  It
has to read as an ordinary OCaml program that can be diffed against
`type.ml` — no `Acc_rect` / `Fix_sub` / `FixWf` wrappers, no `sumbool` / `sig`
scaffolding, no `Obj.magic`, no residue of the termination argument.  This is
why 7.1 and 7.2 are load-bearing rather than stylistic, and it is already
recorded at the definition it most constrains (`frost/ext_algo/def_supply.v`'s
header, on `supply_fresh`).

See also: [`REPORT-postclosure-audit.md`](REPORT-postclosure-audit.md) §1.3,
§1.7, §2.1b; `DESIGN.md` §4.3 ("The look cluster") for why the freshness
premises are shaped the way they are; `CLAUDE.md`'s binder-encoding bullet for
the cofinite/exists-fresh split by layer.

### 7.12 ✅ M3b finished the definitions — and the §0 census was short by one

`def_sub.v` states `a_sub` / `a_sub_flex`'s 16 rows threaded.  All five of
`a_sub_flex`'s output-freshness rows
(`def_rules.v:1296,1312,1319,1337,1342`) lose the premise, which with M2's
eight completes **TODO (1)'s stated census**.

⭐⭐ **AND THE CENSUS WAS SHORT BY ONE.**  `a_sub__forall_r` (`:1217`) also
constrains its own output:

```coq
α ∉ dom (Ξ ++ Θ0) ∪ dom Θ1 ∪ ftvar_in_pskl A ∪ ftvar_in_pskl B
```

Both `Θ1` **and** `Ξ` are premise-produced — `Ξ` is the junk suffix, quantified
by the rule and appearing only in the premise's output context.  It carries no
`*_no_loss` lemma and is not in §0's list, so it is a twelfth site and a
thirteenth constraint.  Threaded, both collapse to `α ∉ S0`.
⚙ `Flex-Solve` sheds two more: it deposits two flexibles and states `α <> β`
plus two avoid-conditions, all three consequences of drawing them from the
supply in sequence.

⚠️ **One premise is kept on purpose** — `a_sub__forall_r`'s `uniq (Ξ ++ Θ0)`.
Retiring it needs domain MONOTONICITY of the walk (`dom Θ0 ⊆ dom Θ1`, the
`a_sub` twin of `a_assign_unify_consis_dom_mono`), because `Ξ` is disjoint
from the premise's *output* `Θ1` and that has to be transported back to the
conclusion's *input* `Θ0`.  Separate lemma, separate claim; not part of the
output-freshness census.

✅ **THE `a_sub` BRIDGE IS CLOSED** (`prop_sub.v` §2–§4, axiom-free).  It is
M2's shape, not M3a's — `a_sub` has an output context — and the three extra
conjuncts predicted here are exactly the three it needed, each forced by the
row named: `uniq` preservation (`ForallR` re-establishes `α ∉ dom Θ1` and
`α ∉ dom Ξ` from uniqueness of the premise's output `Ξ ++ (α~tvar) ++ Θ1`),
the domain upper bound (the six `Flex-*` re-attaching rows), and
`ftvar_in_aenv Θ1 [<=] S1` (`Arrow` and `ForallL`).  Two corrections to the
prediction:

- ⚙ **The domain bound came out HYPOTHESIS-FREE**, so it is a separate
  induction (§2) rather than a fourth motive conjunct.  What pays for the ∀
  row is that the binder is drawn OUT of `S0` while growth puts it IN `S1`,
  so it lands in the bound's own `S1 ∖ S0` summand — no uniqueness needed.
  ⚠️ That same fact is why the bound canNOT serve `ForallR`'s `α ∉ dom Θ1`,
  which is what forces the `uniq` conjunct.
- ⚙ **A FOURTH conjunct was added later**, for M4: `ftvar_in_pskl Q [<=] S1`,
  the OUTPUT SKELETON's coverage.  `a_pat`'s App row runs the function at the
  argument's inferred skeleton, so a later premise's coverage is a statement
  about an earlier premise's output.  Its consistency-level twin
  (`e_consis_out_ftvar`, prop_consis.v §7) could be a separate pass; this one
  could not, because `a_sub__arrow` consumes it beside the context coverage.

⚠️ **Two `fsetdec` traps, both measured.**  §2's uniform closer took 26 s on
ONE row (`ForallL`) until `e_extract_block`'s two irrelevant conjuncts stopped
being posed — `ftvar_in_aenv Ξ [<=] dom Ξ` adds a set LEAF and tips the tauto
search over its cliff.  And metalib's `solve_uniq` unfolds `disjoint` only at
the very end, so a `dom (x ~ a ++ E)` inside a `disjoint` goal never reaches
`simpl_env`; `Flex-Solve`, the one row that inserts into the middle of a
context, needs the local `uniq_env` variant that unfolds first.

### 7.13 ⭐ DECIDED — `ext_algo` CONVERTS `a_pat`'s four cofinite rows

§4 left this open ("decide explicitly").  Decision (user, 2026-08-13):
**`e_pat` is exists-fresh, uniformly with `a_typing`'s six converted rows.**

The reason the tree never converted `frost/`'s own `a_pat` is cost, not
principle — `algo/def_rules.v:1380-1393` and
`docs/REPORT-remech-cleanup-audit.md` §3 both call it "the one real violation"
and recommend converting.  What stops them is that it re-opens `a_pat_sound`
(theorem 1) and `a_pat_complete` (theorem 3), and `a_typing` invokes `a_pat`,
so theorems 2 and 4 feel it too: four flagships in play.

⭐ **The second encoding does not have to pay that.**  It states `e_pat`
exists-fresh and bridges; `frost/`'s `a_pat` is untouched and its four
theorems never move.

⚠️ **But note which direction pays.**  Cofinite is cheap to USE and expensive
to BUILD.  Our composable direction is `e → a`, i.e. exists-fresh → cofinite,
so the bridge must REGENERATE the whole cofinite family from the one instance
`e_pat` gives it.  That is exactly what `a_pat_rename_tm`
(`algo/prop_swap.v:2521`) exists for — today its only consumer is `frost/`'s
own completeness proof.  So the M4 bridge is a citation, not a new proof, and
`a_pat_rename_tm` gains a second consumer.  ⚙ Same pattern as M2: the eleven
`*_no_loss` lemmas were reader-facing justification and became the bridge's
proof obligations.

### 7.14 ✅ M4 RESULT — TODO (1) IS COMPLETE

`frost/ext_algo/def_pat.v` (`e_split` 3 rows, `e_pat` 10) and
`def_typing.v` (`e_typing` 13), with `prop_pat.v` and `prop_typing.v`.
`make coq` green, `README.v`'s 32 assumption reports still all
"Closed under the global context", and `e_split_sound` / `e_pat_sound` /
`e_typing_sound` / `e_typing_sound_init` axiom-free.

⭐ **EVERY ALGORITHMIC JUDGEMENT IS NOW THREADED AND BRIDGED.**  Composed with
the bridges, a threaded run of the whole algorithm is a run of `frost/algo`'s
encoding over the SAME contexts — so the four flagship theorems apply to it
verbatim, which is what the second encoding was for.

⭐⭐ **THE `AT-Abs` PAYOFF LANDED.**  `a_typing__abs`'s `uniq (αs ++ Θ1)` —
the consumer-side filter on `guess^TY`'s block that
`REPORT-postclosure-audit.md` §1.3 priced at 316 occurrences across 19 files
and declined — is `e_guess_mono_uniq_app`, a two-line corollary, and
`e_typing__abs` does not state it.  With `a_sub__forall_l`'s `uniq (Ξ ++ Θ0)`
(§7.9) that is **both** of the tree's `uniq` prose-completions on generated
blocks, now theorems.

⭐ **AND THE BINDER ROWS' SIDE CONDITION COLLAPSES TO `x ∉ S`.**  Since the
2026-08-13 exists-fresh conversion (§7.13, and see below) `frost/`'s own
`a_pat` rows read

    x ∉ dom (Ξ ++ Θ1) ∪ dom Θ2 ∪ fvar_in_exp e

and the threaded rules discharge it in three pieces, none of them a premise:
`dom Θ1` and `fvar_in_exp e` from coverage, `dom Ξ` and `dom Θ2` from
UNIQUENESS of the premise's output `Ξ ++ (x ~ b) ++ Θ2`.  ⭐ The term binder
is drawn from the supply like every other name, which is what `type.ml` does
(`Bindlib.unbind`).

⚠️ **THREE PREMISES ARE KEPT ON PURPOSE, all on `e_typing`'s four CHECK rows**,
and none of them is a freshness side condition:

- `uniq (Ξ ++ Θ)` and `∀γ ∈ dom Ξ, γ ∉ ftvar_in_ptyp B1` (audit §1.1/§1.2) —
  the obligations of DISCARDING the suffix, which the hand-off already says
  are different work.
- `α ∉ ftvar_in_ptyp A` on the two `_step` rows — the peeled binder must not
  ESCAPE into the result body.  ⚙ A supply records where a name CAME FROM,
  not where it may APPEAR, so this is outside what threading can pay for.  It
  could be traded for a `close`-shaped conclusion (as `e_consis__forall_inh`
  does) at the price of an `lc` obligation and of the two rule sets no longer
  diffing line for line; not worth it.

⚙ **The coverage hypothesis grew one slot**, and it is worth knowing why:
`e_pat` / `e_typing` ask the supply to cover the subject's TERM variables
(`fvar_in_exp e`) as well as its type variables.  That is exactly what makes
`x ∉ fvar_in_exp e` free.  It costs nothing at the entry point — a well-formed
subject's free term variables are bound in `Θ0`, and `dom Θ0 ⊆ ftvar_in_aenv
Θ0` already — so `e_typing_sound_init` is still hypothesis-free.

### 7.15 ✅ `a_pat` IS EXISTS-FRESH — the decision of §7.13, taken further

§7.13 decided that **`ext_algo`** would state `e_pat` exists-fresh and bridge,
leaving `frost/`'s `a_pat` cofinite.  The user then asked for the stronger
thing: **convert `frost/`'s own `a_pat`, re-opening finished proofs.**  Done
2026-08-13; `make coq` green, all four flagships re-closed.  Consequences:

- ⭐ **§7.13's warning about the expensive direction is VOID.**  It said the
  M4 bridge would have to regenerate a cofinite family from one instance, via
  `a_pat_rename_tm`.  With both encodings exists-fresh the bridge is
  STRUCTURAL — `prop_pat.v`'s four binder rows are `apply … with (x := x)`
  plus one freshness `fsetdec`.
- ⛔ **`a_pat_rename_tm` IS GONE, and cannot come back**: over exists-fresh
  rows it needs `b <> x` for an `x` the statement cannot constrain.  The ⛔
  note at the end of `algo/prop_swap.v` §6 records the argument.
- ⚙ **Net −250 lines in `frost/`** (`prop_completeness_pat.v` −102,
  `prop_swap.v` −155).  `REPORT-remech-cleanup-audit.md` §3 has the full
  accounting and the corrections to its own estimate.

### 7.16 ✅ TODO (2) — THE EXTRACTION IS REAL NOW (but not yet scaled)

§0's complaint was that the tree contained **zero** `Extraction` commands, so
the paper's shipped `type.ml` was related to the mechanization only by our
reading of it.  That is closed for the part of the algorithm that has a
runner:

- `frost/ext_algo/extraction/PseudoMonadic.v` — McTT's failable-bind
  combinators, **copied verbatim** as §7.2 says to.  ⚠️ Its own header records
  why it cannot be a type class (Coq #19452: no extractable polymorphism
  across `Prop` and `Set`), which is the trap one hits while trying to tidy
  it.  ⚙ Landed BEFORE its consumer on purpose: M1.7's runner is total and
  never fails, but `assign`/`unifyvar`/`consistency` and `a_sub` do, and
  their runners will return `sumor`s.
- `frost/ext_algo/def_guess_impl_sk.v` — `guess^N`, the sort wrapper.  Two
  rows, both decided by the mode, so no domain predicate of its own; it is
  what makes `a_extract`'s LAST stage runnable rather than merely specified.
- `frost/ext_algo/extraction/Extract.v` — the driver.  `ExtrOcamlNatInt`
  (⚠️ without it metalib atoms extract as unary `nat` and the output is
  useless for a differential test), `Extraction Inline proj1_sig`, output to
  `extraction/extracted/frost_guess.ml`.

⭐ **AND THE STANDING BAR (§8) IS MET, MEASURED NOT ASSERTED.**  The emitted
`e_guess_mono_impl` is an ordinary OCaml `let rec` over the skeleton — no
`Acc_rect`, no `Fix_sub`, no `FixWf`, no `sig`/`sumbool` scaffolding, no
`Obj.magic`, no residue of the domain predicate.  The one non-obvious line is
`| Pskl_var_b _ -> assert false (* absurd case *)`, which is what a
hand-written implementation writes for an unreachable input.  ⭐ And it
**compiles**: `ocamlc -c frost_guess.mli frost_guess.ml` is clean, so the
artifact is a type-correct OCaml program and not merely a printed term.

⚙ The Makefile creates the output directory (`Set Extraction Output Directory`
does not) and `make clean` removes it — the `.ml` is a build product,
regenerated every build, to READ and never to edit.

⛔ **WHAT REMAINS OF TODO (2), precisely.**  Every judgement is a threaded
RELATION with a bridge; a relation is `Prop` and extracts to nothing.  So the
remaining work is *writing the remaining Bove–Capretta runners* — a domain
predicate, an `Equations … by struct` on it, and a totality lemma, per
judgement — and the export list in `Extract.v` grows; none of the directives
change.  The order that matches the dependency graph is
`assign`/`unifyvar`/`consistency` → the collection → the solving fold →
`extract` → `a_sub` → `a_split`/`a_pat` → `a_typing`.
⭐ Termination is owed ONLY by the totality lemmas (§7.1), and §7.3 records
that WT expects the argument to be mostly straightforward.

## 8b. ⭐ THE TERMINATION CAMPAIGN — phase 0 and phase 1 (2026-08-13)

Prompted by the user, who pushed back on sequencing the remaining runners
(routine) ahead of termination (the only part that can invalidate them).
That push is right, and it exposes a dependency I had backwards: §7.1 says a
Bove–Capretta runner exists WITHOUT the measure, which I read as "the measure
can wait".  The useful reading is the opposite — **the domain predicate is
read off the rules, so its totality lemma needs no runner, and termination
can therefore be proved FIRST.**

### 8b.1 ✅ PHASE 3 IS ALREADY ANSWERED — `type.ml` commits ForallR first

The search-strategy question (§5: the rule set is not syntax-directed, so a
runner must commit) turns out to be settled by reading the reference
implementation.  `benchmark/Fresco/lib/type.ml`'s `sub` is an OCaml `match`,
so it is ordered, and `SI-ForallR` (`:910`) precedes `SI-ForallL` (`:958`).
**When both the checked type and the subject are `∀`, the target's quantifier
is peeled first.**  That is the order a runner must reproduce, and it is now
a citation rather than a design decision to make.

### 8b.2 ✅ PHASE 0 — no divergence found, and the probes' limits

The reference implementation builds and runs (OCaml 5.4 switch; `bindlib`,
`multicont`, `core`; `dune build --profile release bin/met.exe` — the default
profile fails on an unrelated `unused-var-strict` warning in `type.ml:942`).
`--debug` prints the rule trace, which makes **the count of `SI-ForallL`
firings a divergence detector**.

Result: **no divergence.**  ⚠️ But the battery was weak and should not be
quoted as strong evidence:

- the pair-doubling family did not even parse (`(x, x)` needs a declared
  `Pair` constructor) — it tested nothing;
- the deep-∀-nesting family flatlined at 3 `SI-ForallL` firings for every
  depth 1..12 — it never iterated the interesting path;
- only the self-application family exercised it, and its firing counts
  (3, 8, 20, 48, 112, 256, 576, 1280) track the term size, which itself
  doubles per level — constant work per node, not a blowup.

⭐ **The structural reason it did not diverge is visible in the source**, and
it is worth more than the probes:

- `guess_mono` (`type.ml:80-108`) is a structural map: `Ghost` ↦ a fresh
  flexible, `TForA (k,a)` ↦ recurse and REBUILD the same `TForA`.  It never
  manufactures a quantifier; it only copies one the skeleton already had.
  That IS the paper's "never guess polytypes out of thin air", as a shape
  property.
- `SI-Arrow` (`type.ml:918-922`) sends the DOMAIN to `join_sk` (consistency)
  and keeps only the CODOMAIN in `sub`.  So `sub` walks the arrow SPINE and
  nothing else — and a `∀` that an instantiation drops into a domain
  position can never fire `SI-ForallL` again.

⭐ **THE USER'S ARGUMENT (2026-08-13), which is the frame to build the measure
in**: polymorphic instantiations always come from known information, and
after an instantiation the walk falls back to consistency at every position
except the final contravariance — so it terminates.  Both halves are the two
source facts above.

### 8b.3 ✅ PHASE 1 — the first half is a theorem now

`frost/ext_algo/prop_termination.v`, axiom-free:

    e_guess_mono_nall : e_guess_mono S0 P S1 Ξ A -> nall_ptyp A <= nall_pskl P
    e_guess_mono_size : e_guess_mono S0 P S1 Ξ A -> size_ptyp A <= size_pskl P
    e_guess_nall      : the same, through the sort wrapper

so **`guess^TY` never guesses a polytype out of thin air** is no longer a
reading of the code — the guessed type has no more `∀`s, and is no bigger,
than the skeleton it was guessed from.  The `∀` row is where the content is:
`e_guess_mono__forall` rebuilds the quantifier the skeleton had, and the only
row that INVENTS anything (`__hole`) invents a flexible variable, which is
`∀`-free.

✅ **PHASE 1b (2026-08-13, later): the bound is carried through the WHOLE
extraction — and it is SHARPER than the phase plan asked for.**
`prop_termination.v` §3–§6, axiom-free:

    e_looksub_nall / e_lookeq_nall :
        nall_a_cstrs C <= nall_pskl P'                 (collection)
    e_solve_sub_eq_nall :
        nall_pskl P' <= nall_pskl P + nall_pskl Q      (each solving step)
    e_solve_cstr_nall :
        nall_pskl Q <= nall_a_cstrs C + nall_pskl P    (the fold)
    e_extract_nall :
        nall_pskl Q' <= nall_pskl P'                   (⭐ the composition)

⭐ The plan predicted `nall C <= nall P + nall P'`; the truth is the
COUNTERPART ALONE.  Reading the three depositing rows says why: LS-Var and
LE-Var deposit the counterpart standing opposite the looked-up variable,
LE-FlexR deposits a fresh VARIABLE (∀-free, like `guess^TY`'s hole row) —
the subject is only ever WALKED.  Composed with the fold's `◇` seed, the
instantiation `e_sub__forall_l` recurses on satisfies `nall P1 <= nall P0`
— "we only guess polytypes that can be determined by inherited type
information" with "inherited information" pinned to the single input `P0`.
The proofs are two mutual inductions and a fold, one `lia` per row; the
only row with content is SE-FlexR, where §2's `e_guess_mono_nall` is
consumed.

### 8b.4 ✅ PHASE 2's HEART — the head-chain count strictly decreases at ForallL

⭐⭐ **8b.2's "count ∀s on the codomain spine" is REFINED, not confirmed:
a spine count does NOT decrease at `e_sub__forall_l`.**  An instantiation
CAN put a ∀ on the spine — an eq-constraint hands a counterpart fragment
to the fold wholesale (`SE-GhostL`), so `P1` can be ∀-HEADED (concretely:
subject `∀a.(a→a)`, counterpart `(∀c.c)→D` puts `∀c.c` on the new spine).
What is true is sharper, and it is now a theorem
(`prop_termination.v` §7–§9, axiom-free):

- The right count is `hnall`, the HEAD ∀/⫯-chain length — ∀s reachable from
  the root through ∀ and ⫯ nodes only.  A ∀ below an arrow is charged to
  the MODE: reaching it costs an `e_sub__arrow` step, which consumes one FN
  of `M` (and TC-mode cannot cross an arrow at all — subject arrow + TC is
  `e_sub__check`, which leaves for consistency).
- The instantiation grafts onto the head chain ONLY when the ∀'s body IS
  its own head chain (∀/⫯ are unary — a chain ending at the bound variable
  is the whole body; `chain_hits_pskl` + the graft formula
  `hnall_pskl_open_rec_graft`).  In exactly that case the collection
  deposits AT MOST the one sub constraint carrying `P0`
  (`e_looksub_pure_chain_cstrs` — LS-Check needs a guarded non-α subject,
  LS-ForallR a ∀-headed counterpart, both impossible there), and the
  ◇-seeded fold then yields a guarded-or-⫯-arrow head
  (`e_solve_sub_hole_hnall` — ⚙ a ◇ subject has NO recursive solve row:
  SS-Check demands a GUARDED subject, so the eq layer is not even
  reachable).  `guess^N` never raises the head count (`e_guess_hnall`).

⭐ Composed:

    e_extract_forall_l_hnall :
      e_extract at (open P α) against guarded-or-◇ P0 yields P1 with
      hnall (open P P1) < hnall (∀.P)

with BOTH hypotheses being `e_sub__forall_l`'s own premises.  So the
measure's shape is settled: lexicographic
**( FN-depth of M , nall P0 , hnall subject , #defined-flex , size , walk )**
— arrow rows consume an FN; ForallR consumes `nall P0` (open-at-var
preserves it, the ∀ is gone); ForallL consumes `hnall subject` (this
theorem); Flex-Assign consumes a defined-flex entry (its substituted mono
is ∀-free so the earlier components hold, `hnall`/`nall` stable under
mono-substitution); ⫯-strips consume size.  ⚠️ Flex-Solve's re-entry TIES
the first components (subject `α̂ → β̂`, same mode) — the totality proof
must INLINE one step there: the re-entered subject is an arrow, so its
only non-failure row is `e_sub__arrow`, which strictly drops FN-depth.

### 8b.5 ✅ PHASE 2 ASSEMBLED — `e_sub_order_total` is Qed (2026-08-14)

The plan of the paragraph this section replaces was executed in full;
everything below is axiom-free, zero admits, `make coq` green.

- **`def_order.v`** — the Bove–Capretta domain predicates for `e_sub`'s
  whole call graph (`guess^N` wrapper, collection, solving, the fold,
  extraction, the consistency block, `e_sub`/`e_sub_flex`).  ⭐ ONE
  constructor per judgement with SHAPE-CONDITIONAL premises — a deliberate
  departure from `e_guess_mono_order`'s per-rule shape: these judgements
  are PARTIAL, and per-rule constructors would owe a failure constructor
  per non-matching shape; here a failing input satisfies the constructor
  with every premise vacuous, totality needs no failure enumeration, and a
  runner branch inverts `H` once and selects with its own equations.  Rule
  GUARDS are dropped (the runner tests them; a stronger order is fine) —
  with ONE exception: `e_sub_order`'s ForallL premise keeps guarded-or-◇
  on `P0` (the decrease theorem consumes it) and the wf check on `P1`
  (type.ml:966 recurses behind `is_wf p1`).
- **Routine totality** (`prop_termination.v` §10–§11): collection
  UNCONDITIONAL (it never guesses — not even lc is needed); solving at an
  lc subject (SE-FlexR guesses the accumulated pattern); the fold at lc
  seed + payloads; `e_extract_order_total` at lc inputs.  The informal
  "eq before sub" lex component dissolves — the sub→eq drops go to a
  judgement whose totality is already established.  Fed by an e-side lc
  kit (§10) mirroring `a_solve_sub_eq_lc` row for row.
- **The measure kit** (§12): `fnd_mode`, `ndef_aenv`, mono-substitution
  stability of `nall`/`hnall`, every generated block is flex-only
  (`all_flex_mono`, five lemmas up the pipeline), and ⭐ the consistency
  block PRESERVES the def-payloads-are-mono discipline
  (`e_assign_unify_consis_defs_mono`) — which is what lets the Arrow case
  hand the domain's OUTPUT context to the codomain.
- **⭐⭐ `e_sub_order_total`** (§13): the lex measure
  `(fnd_mode M, nall P0, hnall P, ndef Θ, size P, |Θ|-walk)` assembled as
  nested `lt_wf_ind` inductions, Ψ (the flex walk) proved before Φ inside
  the `ndef` level (its exits reach Φ only through IH1/IH4 or the inline
  arrow step at Flex-Solve — the tied edge, exactly as 8b.4 predicted).

      e_sub_order_total :
        (forall Δ1 Δ2 S Θ P0 P, e_consis_order Δ1 Δ2 S Θ P0 P) ->
        forall S0 NM M P0 Θ0 P,
          lc_pskl P -> lc_pskl P0 -> aenv_defs_mono Θ0 ->
          e_sub_order S0 NM M P0 Θ0 P

⛔ **WHAT REMAINS OF THE CAMPAIGN — the ONE hypothesis.**  The consistency
block's totality is unification-style termination and NOT routine:
`e_assign__solve_m` trades one undefined flexible for a guess block of
fresh ones, and `e_assign__assign`/`e_unify__flex_assign` substitute a
defined entry away and re-enter `e_consis` at a GROWN pattern (the
worklist prior art's `num_etvar`/`split_depth` components, §7.4).  Its
order predicates are DEFINED (def_order.v §5) and its defs-mono
preservation is proved; only `e_consis_order`'s inhabitation is owed.
Discharging it turns `e_sub_order_total`'s hypothesis into a theorem —
and with it, decidability of the subtyping walk.  Phase 4 (the runners)
is unblocked for everything below the consistency block already.

⚙ Traps paid for in the assembly, for whoever extends it: metalib's
`x ~ a` is `one (x, a)` — a DEFINITION — so `Forall`/`ndef` patterns see
the cons only after `simpl`; a `; [ … | … ]` dispatch after a chain binds
to ALL accumulated goals (parenthesize per-goal); `subst` renames the
mode/context variables, so read them off the GOAL in `match goal`; under
`Set Implicit Arguments` a lemma argument under a FUNCTION application
(`open P …`) stays explicit — use `@` and spell everything.

