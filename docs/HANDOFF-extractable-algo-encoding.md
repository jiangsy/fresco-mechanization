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

### 8b.6 ✅ THE HYPOTHESIS IS DISCHARGED — the consistency block terminates, and `e_sub_order_total` is UNCONDITIONAL (2026-08-14, later)

The "NOT routine" campaign closed in one day, because the right fuel
turned out to be visible in the rules (`prop_termination.v` §14–§16,
axiom-free):

    W := nholes(pattern) + nholes(subject) + nundef(context)

⭐ **W never increases, and creating a def strictly consumes it** — holes
are the ONLY source of new flexibles (`e_guess_mono_block_nundef`:
Assign-SolveM's guess block is EXACTLY the pattern's holes), monotype
substitution creates neither a hole nor a flexible
(`nholes_pskl_subst_holefree`, and `ptyp` has no hole constructor at
all), and the unify solutions are variables.  Stated in the addition
form that CHAINS at the Arrow row:

    e_consis_wpres :
      nundef Θ' + ndef Θ' <= nundef Θ + ndef Θ + nholes P0 + nholes P

together with ndef-monotonicity (`e_consis_ndef_mono`).  So at Arrow's
second premise (which runs at the first's OUTPUT context): either the
domain's run created a def — then W strictly dropped and the lex
restarts — or it created none, ndef ties by monotonicity, and SIZE pays.
The walks consume `ndef` at the def-crossings (the crossed entry is
dropped below) and `|Θ|` elsewhere; a variable leaving the skeleton
inputs pays by size on the way into a walk.  Full lex:

    ( W , ndef Θ , size P0 + size P , |Θ|-walk )

assembled as `e_consis_block_order_total_n` (three conjuncts, nested
`lt_wf_ind`, the walks proved inside the ndef level — the §13/§17
template).  Wrapped:

    e_consis_order_total :
      lc P0 -> lc P -> aenv_defs_mono Θ -> e_consis_order Δ1 Δ2 S Θ P0 P

and §17's hypothesis was restated in exactly that shape and DISCHARGED:

    e_sub_order_total : forall S0 NM M P0 Θ0 P,
      lc_pskl P -> lc_pskl P0 -> aenv_defs_mono Θ0 ->
      e_sub_order S0 NM M P0 Θ0 P

**No hypothesis left.**  The termination of the subtyping side — the
walk plus its whole call graph (consistency, collection, solving,
extraction, guessing) — is a closed, axiom-free theorem.  ⚙ The §7.4
prediction that the worklist's `num_etvar`/`split_depth` machinery would
be needed was PESSIMISTIC: holes-as-fuel replaces split-depth entirely,
because Frost's guess consumes the whole pattern shape at once instead
of splitting incrementally.

⛔ ~~**WHAT REMAINS OF TODO (2) — phase 4 only**: the runners (`Equations
… by struct` bodies + soundness) for the thirteen judgements beyond
`guess^TY`~~ — ✅ **DONE, see §8b.7.**  The PAPER-GAPS
entry for §7.3 is FILED (2026-08-14) and records the mechanized status.

⚙ Traps paid for in the assembly, for whoever extends it: metalib's
`x ~ a` is `one (x, a)` — a DEFINITION — so `Forall`/`ndef` patterns see
the cons only after `simpl`; a `; [ … | … ]` dispatch after a chain binds
to ALL accumulated goals (parenthesize per-goal); `subst` renames the
mode/context variables, so read them off the GOAL in `match goal`; under
`Set Implicit Arguments` a lemma argument under a FUNCTION application
(`open P …`) stays explicit — use `@` and spell everything.

### 8b.7 ✅ PHASE 4 COMPLETE — EVERY JUDGEMENT EXECUTES (2026-08-14, later)

**TODO (2) IS DONE.**  Twelve runners now exist beyond `guess^TY`'s —
`e_lookeq_run`/`e_looksub_run` (def_look_impl.v), `e_solve_eq_run`/
`e_solve_sub_run`/`e_solve_cstr_run` (def_solve_impl.v), `e_extract_run`
(def_extract_impl.v), `e_consis_run` for the mutual
`assign`/`unifyvar`/`consistency` block (def_consis_impl.v), `e_sub_run`
for the mutual subtyping walk (def_sub_impl.v), and `e_split_impl`/
`e_pat_run`/`e_typing_run` (def_pat_impl.v, def_typing_impl.v — these two
judgements had no phase-2 orders, so their files carry the template's full
four-layer stack: order, totality, implementation, runner).  Each runner
follows def_guess_impl.v's shape and each `*_run_sound` is Qed and
axiom-free; the dispatch orders are the reference implementation's, cited
per match arm in the file headers (§8b.1's ForallR-before-ForallL
commitment included, def_sub_impl.v).

⭐ **THE RESULT SHAPE, decided at step 2 and used throughout:
`option (sig (spec …))`** — `None` means "no rule applied" and is justified
by nothing; the contract is SOUNDNESS-ONLY, and "rejection is justified"
(runner completeness / determinism) is deferred, exactly as §5's runner-
completeness paragraph anticipated.  `sig` erases, so the OCaml type is a
plain `option`.

⭐ **EVERY REMAINING PRECONDITION IS TESTED, NOT ASSUMED** (def_dec.v, the
guard-decider inventory, each with a SOUNDNESS-ONLY lemma): `guarded`/
`ghost-free`/`mono`/`non-flex` shape checks, context scans, `uniq_ck`,
`suffix_ck`, a fuel-at-`size` wf checker (`wf_pskl_ck` ≈ type.ml's
`is_wf`; the ∀ row's soundness regenerates the cofinite family via
`a_wf_pskl_rename_delta`), `degree_*_ck` for local closure via
`lc_*_of_degree`, and `defs_mono_ck` — so `e_pat_run`/`e_typing_run` take
NO hypotheses at all, and their totality needs none (a pure `size_exp`
induction for `e_pat_order`; lex `(size_exp, size_pskl pattern)` for
`e_typing_order`, the pattern component paying for the check-mode STEP
rows, which recurse on the SAME subject with the pattern's ∀ peeled).

⭐ **ONE PHASE-2 BUG FOUND AND FIXED, BY THE RUNNER** (def_order.v,
ForallL): both extract slots said `S0` where `e_sub__forall_l` runs the
extraction at `add α S0`.  Totality never noticed — every extraction lemma
is supply-parametric — but the runner's extract call must satisfy the
order's premise AND the rule, which pins the slot.  One explicit
application in prop_termination.v §17 moved with it; nothing else.

⚠️ Traps paid for in phase 4, beyond §8b.6's list:
- An `Equations` definition with UNSOLVED obligations behaves like
  `Program`: the command SUCCEEDS silently and the constant simply does
  not exist.  `Obligations.` lists what is left; obligation counts vary
  with the match compiler's clause splitting.
- The re-attaching rows' conclusions are `(β ~ b) ++ Θ` while clause
  patterns produce cons-form goals — a conversion `Hint Constructors`'
  simple-apply cannot make, and an `econstructor` Extern does not
  backtrack usefully inside `eauto`.  The rule instance is built by the
  obligation tactic's TRAILING `solve [ econstructor; eauto ]`, whose
  `;`-composition does backtrack across constructors.
- `Forall_app_intro` must NOT be a bare `Hint Resolve`: on `Forall _ ?l`
  goals `eauto` splits an evar-able list forever (this is what made the
  first def_consis_impl.v build run >25 min).  Deterministic assembly
  Extern instead.
- In a `refine (fix go …)` helper, `subst` on an equation whose variable
  occurs in `go`'s TYPE generalizes over `go` and breaks the guard
  ("recursive call has not enough arguments") — rewrite the GOAL only.
  And a catch-all match row beside a specific-constructor row is
  EXPANDED per constructor, orphaning holes written against the row's
  binder — decide the marker with a `sumbool` helper instead.
- `coqc … | head` lets `head`'s exit kill `coqc` mid-write (SIGPIPE) and
  the stale `.vo` then fails later Requires with "inconsistent
  assumptions" — same family as CLAUDE.md's `make coq > log` trap.

⚙ extraction/Extract.v grew its export list to all runners (plus
`Extraction Inline Sumbool.sumbool_of_bool`, in the service of the same
§8 bar as the two existing inlines); the output keeps its M1.7 name
`frost_guess.ml` though it now holds the whole algorithm.


## 8c. ⭐ THE COMPLETENESS CAMPAIGN — from a sound runner to DECIDABILITY

§8b closed TODO (2): every judgement executes, every runner is sound, the
extracted OCaml compiles.  What that does NOT give is the second half of §5's
two-statement contract.  The runner's `None` is justified by nothing — the
result shape was chosen SOUNDNESS-ONLY on purpose (§8b.7) — so the chain
§5 states,

    termination ⟹ totality ⟹ (with soundness + completeness) decidability

is missing exactly one link.  Termination and totality are closed and
unconditional (§8b.5–§8b.6).  This section is the last link, and its payoff is
the one claim worth putting in `README.v`: **the paper's own undischarged
decidability argument (§7.3), discharged end to end.**

### 8c.1 ✅ STEP (1) — the composed SOUNDNESS corollary (2026-08-14)

`frost/ext_algo/prop_run_corollaries.v`, axiom-free, two corollaries:

    e_typing_run_sound_infer :
      {{ nil ⊢ᵉ e }}a ->
      e_typing_run (ftvar_in_pskl □ ∪ fvar_in_exp e ∪ ftvar_in_exp e)
        mode_ti nil □ e = Some r ->
      … /\ exists ζ, ζ ∷ (ty_ctx r) ⊑ nil /\
        {{ nil ⊢ˢᵈ[ mode_ti ] e ⦂ syn{ msubst_ptyp ζ (ty_out r) } }}d /\
        {{ nil ⊢[ mode_ti ] e ⦂ syn{ msubst_ptyp ζ (ty_out r) } }}d

and `e_typing_run_sound_check` at `⌈A0⌉`, whose answer is `inh{…}`.  Nothing
new is proved: it is `e_typing_run_sound` ∘ `e_typing_sound_init` ∘
`a_typing_sound` ∘ the conservativity corollaries, each already closed.  Three
notes for whoever extends it:

- ⭐ **The entry supply is not a parameter of the claim.**  Both corollaries
  fix it at `ftvar_in_pskl P0 ∪ fvar_in_exp e ∪ ftvar_in_exp e` — the supply
  `e_typing_sound_init` chooses, which is what makes coverage `reflexivity`
  and `uniq` `uniq_nil` (§7.11's argument, at the top of the algorithm).
  A completeness corollary must be stated at the SAME supply or the two do not
  compose into decidability.
- ⚠️ The one surviving side condition is `{{ nil ⊢ᵉ e }}a`, and it is
  `a_typing_sound_infer`'s, not the runner's — a runner may legitimately be
  handed an open term.
- ⚙ **Not in `README.v`, deliberately.**  The paper index carries the paper's
  own labelled statements; this is the extracted program's contract.  The
  README entry belongs to the decidability theorem at the end of 8c.5.

⚠️ **`a_wf_exp` and its `{{ Θ ⊢ᵉ e }}a` notation live in
`algo/pat/prop_soundness_pat.v`**, not in `algo/def_rules.v` — a `Require` of
`prop_closed.v` alone does not bring the notation into scope, and the parse
error names the level-75 alternatives rather than the missing notation.

### 8c.2 ⛔ OPEN — the remaining steps, in dependency order

- ✅ **(2a) DONE (2026-08-14)** — `frost/ext_algo/prop_dec.v`, 24 lemmas, all
  `Closed under the global context`.  The whole inventory of `def_dec.v` and
  `def_pat_impl.v` §1 now has its converse `<the guard> -> … _ck = true`.
  ⭐ All but one are the same induction read backwards, which is what the
  deciders being structural mirrors of their predicates buys.  The exception
  is `wf_pskl_ck`, and both of its difficulties are the ones its own header
  named: FUEL ADEQUACY — the bound is `size_pskl P`, and the ∀ row's descent
  into `open P1 (pskl_var_f β)` costs exactly the `S` the `pskl_all_syn` node
  pays for (`size_pskl_open_pskl_wrt_pskl_var`), so the fuel is the checker's
  own structural depth made explicit rather than a search bound that might
  be short — and THE COFINITE ROW, instantiated at the checker's own
  `supply_fresh` name by `a_wf_pskl_all_inv_at`, the exact mirror of the
  soundness direction's `a_wf_pskl_all_intro_at`.
  ⚠️ State the fuel as an INEQUALITY (`size_pskl P <= n`): at exact fuel the
  statement is not its own induction hypothesis.  The corollary the runners
  call, `wf_pskl_ck_complete_at_size`, specialises it.
- 🟡 **(2b) HALF DONE (2026-08-14).**  Two files moved:
  - `prop_dec.v` §6 — the nine evidence-carrying DECOMPOSITIONS
    (`arrow_split`, `ptyp_arrow_split`, the two `abind_var_*_get`,
    `lookup_binding`, the two `split_at_key_*`, `pskl_readback`,
    `pskl_readback_all`) now each have their converse too, so **every test a
    runner performs — boolean or not — has both directions**.  ⚠️ `uniq` is
    load-bearing in three of them, not decoration: `lookup_binding` and the
    `split_at_key_*` scans stop at the FIRST occurrence, and `binds` is an
    "appears somewhere" predicate, so without uniqueness the scan may return
    a DIFFERENT payload than the derivation used.  The bridge's `uniq`
    conjunct supplies it at every call site.
  - `prop_run_invariants.v` (new) — §1 `e_sub_defs_mono` /
    `e_sub_flex_defs_mono`, the twin of `e_consis_defs_mono` this list flagged
    as missing; §2 `e_consis_lc` and `e_sub_lc` / `e_sub_flex_lc`, the two
    output-skeleton lc facts §10's pipeline kit stops short of.  All eight
    `Closed under the global context`.
    ⭐ Why the `e_sub` twin was missing: §12 proved the consistency block's
    because TERMINATION needed it there (Arrow hands the domain's output
    context to the codomain); `e_sub_order_total` takes `aenv_defs_mono Θ0`
    as an INPUT hypothesis, so the walk never owed the output side.
    Completeness is what makes it load-bearing — `def_typing_impl.v`'s
    AT-Anno/AT-Freeze rows TEST `defs_mono_ck (ty_ctx r1)` on a subtyping
    run's result.
    ⚠️ `e_sub_lc` needs `aenv_defs_mono Θ0`: `Flex-Assign` substitutes a
    context DEFINITION into the counterpart, so the counterpart's local
    closure survives only because the payload is mono, hence lc.
  - `prop_run_invariants.v` §3 — `e_split_defs_mono`, `e_pat_defs_mono`,
    `e_typing_defs_mono`.  ⭐ **The def-payload discipline now holds across
    ALL FOURTEEN judgements, from the entry point down**, which is what the
    runners' `defs_mono_ck` tests need: `def_typing_impl.v` tests it on
    `ty_ctx r1`, the context a RECURSIVE CALL produced, and only a statement
    about OUTPUTS can discharge that.  Two rows generate a block and both
    generate a FLEX-ONLY one (`e_split__flex`'s invented pair, `AT-Abs`'s
    `guess^TY` block), so neither can break the discipline.
    ⚙ Proof-engineering note worth copying: pose the delegations as
    IMPLICATIONS (`pose proof (e_sub_defs_mono H)`, not `… H Hd`) and let
    `eauto` chain them.  Rows like AT-Anno / AT-Freeze / AT-App thread
    `Θ0 → Θ1 → Θ2` through two or three premises and only the FIRST link's
    input is a hypothesis; the guarded form silently matches nothing.
  - ⛔ **STILL OPEN in (2b)**, and ⭐ **the route is cheaper than this list
    assumed**: lc for the `e_pat` / `e_typing` OUTPUTS, and the
    relation-side SHAPE facts (a ForallR run's output context really is
    `Ξ ++ (α~tvar) ++ Θ1`, the abs rows' output splits at the binder marker,
    the readback positions really are `⌈⌉`-images).  §6 says the decomposers
    succeed ON those shapes; what is owed is that the relation PRODUCES
    them.
    ⭐ **Do NOT write these as fresh inductions.**  `a_pat_sound`
    (`algo/pat/prop_soundness_pat.v:2065`) already returns `{{ ⊢ Θ1 }}a` and
    `bskl_to_pskl Qt = P`, and `a_typing_sound` already returns
    `a_wf_ptyp Θ1 A` — so output well-formedness, and with it local closure
    and the readback shapes, comes through the BRIDGE (`e_pat_sound` /
    `e_typing_sound`) composed with the a-side soundness theorems.
    ⚠️ The cost is that soundness' premises come with it (`{{ ⊢ Θ0 }}a`,
    `a_wf_pskl`, mode compatibility, `{{ Θ0 ⊢ᵉ e }}a`).  At the ENTRY POINT
    all four are discharged (`prop_run_corollaries.v`), so the composed
    corollary is free there; what (2d) needs is the INDUCTIVE version, which
    must thread them.  ⭐ Deciding whether to thread those four or to prove a
    lighter payload-lc invariant directly is the FIRST design call of the
    next session, and it should be made together with (2d)'s formulation —
    they constrain each other.
    ⚙ `aenv_defs_mono` does NOT suffice on its own: it constrains
    `abind_flex_mono_def` payloads only, and `AP-Var` needs `lc_ptyp A` for
    an `abind_var_typ A` entry.
- **(2c)+(2d) — ⭐⭐ RESHAPED 2026-08-14.  See §8c.3: they should be ONE
  induction, and it should run on the ORDER, not on either derivation.**
- **(2e) Compose**, then the two-line decidability corollary of §5, a
  `README.v` entry, and `docs/PAPER-GAPS.md` §7.3 updated to
  "discharged end-to-end".

⛔ **A standing constraint from §8b.7: completeness ADDS lemmas, it does not
reshape runners.**  If a runner's test turns out genuinely incomplete-able —
a test the relation does not guarantee — STOP and flag it; do not silently
weaken the test.

### 8c.3 ⭐⭐ RESHAPING (2c)+(2d) — induct on the ORDER, not on either derivation

The plan §8c.2 inherited splits the work as: (2c) lift an `a_*` run to an
`e_*` run at any covering supply, then (2d) turn an `e_*` derivation into a
runner `Some`.  Working (2b) turned up an obstruction to (2c) as stated and,
with it, a better decomposition.  ⛔ **Do not start (2c) in the three-step
shape; start it in the shape below.**

**THE OBSTRUCTION.**  (2c) by structural induction on the `a_*` derivation
does not go through at a binder row.  The `a_*` rule opened its binder at
some `α0` of its own choosing; the `e_*` rule must open at an `α` the SUPPLY
hands out.  So the IH has to be applied to the *transposed* sub-derivation
`(α0 α)·D` — and that is not a structural subterm of `D`, so `induction`
never offers an IH for it.  The two standard repairs are both expensive:

- a nominal-style motive quantified over a PERMUTATION, which needs a
  `list (atom * atom)` action defined and proved an automorphism over every
  sort and every one of the fourteen judgements; or
- a height-indexed mirror of all fourteen judgements (the `ad_pat_sub_fuel`
  idiom) so the induction can run on the height.

**THE REPAIR — induct on `e_*_order`.**  ⭐ The domain predicates of
`def_order.v` are not merely total, they are **CANONICAL**: their premises
name `supply_fresh S0` explicitly rather than quantifying over fresh atoms.
`e_sub_order`'s ForallR premise reads

    e_sub_order (add (supply_fresh S0) S0) a_sub_mode_ty mode_tc
      (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))
      ((supply_fresh S0 ~ abind_tvar) ++ Θ0) P

(`def_order.v:429-433`; ForallL and the flex walk are the same, the latter
drawing two names in sequence).  Three consequences, and together they are
the whole reason to switch:

- ⭐ **The induction is always available.**  `e_sub_order_total` and
  `e_consis_order_total` are UNCONDITIONAL (§8b.5–§8b.6), and `e_pat_order`
  / `e_typing_order` need no hypotheses either (§8b.7), so the order can be
  produced for any input and inducted on.
- ⭐ **The IHs land at the runner's COMMITTED names.**  The `a_*`
  derivation is then only INVERTED at each step, never inducted on — so it
  may be freely transposed before the IH is applied, by ONE transposition,
  with the existing single-swap equivariance lemmas.  No permutation layer,
  no height mirror.  This is exactly §13b's argument, applied once per
  level instead of globally.
- ⭐ **(2c) and (2d) collapse.**  Inducting on the order, the conclusion can
  be the runner's directly — "this branch does not return `None`" — so
  there is no intermediate `e_*` derivation to build and then re-consume,
  and the AGREEMENT the ForallR output test
  (`pskl_eqb (sb_out r) (open B α)`) needs is available because the order
  pins the name the recursive result is compared against.

⚙ **Statement shape to aim at** (type inference; the others mirror it):

    a_typing m Θ0 P0 e B Θ1 ->
    <supply covers the inputs> ->
    exists r, e_typing_run S0 m Θ0 P0 e = Some r

by induction on `e_typing_order S0 m Θ0 P0 e`, inverting the `a_typing`
derivation at each level and transposing it onto the order's committed
names.  ⚠️ `e_typing_run` fixes its domain argument to the totality proof,
so the proof must go through `Equations`' unfolding equations (`simp`),
which compute a clause from the SET arguments and are insensitive to which
domain proof was supplied.

✅ **The one real prerequisite is now SUPPLIED** (2026-08-14):
`algo/prop_swap.v` §16 adds `swap_exp` and the two missing equivariance
lemmas, `a_pat_swap` and `a_typing_swap`, all `Closed under the global
context`.  §5–§12 had covered the whole tower BELOW them
(`a_guess_mono`/`a_guess`, the look/solve/extract cluster, the consis
mutual, `a_sub`/`a_sub_flex`, `a_split`) and nothing else was left.
⚙ The tree had already anticipated the first —
`algo/pat/prop_completeness_pat.v:885` says `a_pat_swap` mirrors them row
by row, written when `a_pat` was still cofinite and it was not yet needed.

⚠️ **`swap_exp` is not optional, and "hold the term fixed" does not work.**
These rows bind a TERM variable, so the transposition has to act on the
subject too.  A statement with the term held fixed fails at the binder
rows: they recurse on `open_exp_wrt_exp e (exp_var_f x)`, so the induction
hypothesis would need `a <> x` and `b <> x` for a binder the ROW chooses.
Swapping the term makes the row's own binder move with everything else,
which is what a transposition is for.

⚠️ **This is NOT a resurrection of `a_pat_rename_tm`**, and the difference
is exactly the ⛔ note's own diagnosis (`prop_swap.v`, end of §6).  That
lemma renamed a type variable ACROSS a run while the row's `x` stayed put
and unconstrained, so it needed `b <> x` with nothing bounding `x`.  A
transposition moves EVERY atom at once, so `x` is not left behind and no
side condition on it is owed.  ⚙ Read the ⛔ note as scoped to its own
statement shape, not as a blanket obstruction.

### 8c.4 ⭐⭐⭐ THE RUNNERS MUST BE MADE REDUCIBLE FIRST — and it is free

⛔ **Before writing a line of §8c.3's induction, know this: as they stand
the runners cannot be reasoned about computationally at all.**  Probed
2026-08-14 on `e_guess_mono_impl`:

- `cbn [e_guess_mono_impl]` does not reduce the application;
- `destruct H` on the domain proof loses the index (it is an indexed `Prop`,
  so plain `destruct` generalises `P` and lands in the wrong branch);
- `reflexivity` is stuck, and `simp` does not exist.

The cause is the `derive(equations=no,eliminator=no)` attribute every one of
the twelve `Equations` blocks carries.  It was chosen for a good reason
(def_guess_impl.v's header: the derived lemmas "would drag dependent
elimination axioms in, and nothing here needs them") — but completeness DOES
need them, so the choice has to be revisited.

⚠️ **Turning `equations=yes` on naively FAILS**, and the error names the
obligation exactly: it asks for

    eq_rect … H0 … (DepElim.pack_sigma_eq_nondep eq_refl e) = ego_unit S0

i.e. **UIP on the domain predicate's PACKED INDEX**.  (A one-index domain
predicate derives its equations with no such obligation — a minimal probe
of the same shape went through untouched, which is why this only shows up
on the real runners.)

⭐⭐⭐ **AND UIP IS AVAILABLE HERE AS A THEOREM, NOT AN AXIOM.**  Verified on
the real `e_guess_mono_impl`: adding

```coq
Set Equations With UIP.
#[export] Instance eqdec_atom : EqDec atom := { eq_dec := fun x y => x == y }.
Derive NoConfusion EqDec for pskl.
#[export] Instance uip_pskl : UIP pskl := eqdec_uip _.
```

makes `derive(equations=yes,eliminator=no)` succeed, and `Print Assumptions`
on the implementation, on `e_guess_mono_impl_equation_1` AND on
`e_guess_mono_run_sound` all report **"Closed under the global context"**.
`pskl` is a first-order inductive over atoms, so its Leibniz equality is
decidable and UIP is Hedberg's theorem.

Three things to carry into the next session:

- ⭐ **`UIP pskl` ALONE is enough.**  The supply component of the packed
  index is matched by `eq_refl`, so no UIP on `atoms` is needed — which is
  fortunate, because metalib's set type carries a sortedness proof and its
  Leibniz equality is NOT readily decidable.  ⛔ Do not go looking for
  `UIP supply`; the first attempt at this wasted a cycle on it.
- ⭐ **`eliminator=no` stays off.**  Only the unfolding equations are
  needed; the derived eliminator is the part with the larger axiom surface,
  and §8c.3's induction runs on `e_*_order`, not on the runner.
- ⚙ Scaling to the other eleven blocks needs the same setup once, in a file
  they all import, plus `EqDec`/`NoConfusion` for whatever other index sorts
  turn out to be inverted.  ⚠️ Verify `Print Assumptions` after every one;
  the bar is unchanged.

✅ **LANDED (2026-08-14)**: `frost/ext_algo/def_uip.v` (the four lines, with
the reasoning) and `def_guess_impl.v` flipped to `equations=yes`.
`make coq` green, README 32/32, and `Print Assumptions` on
`e_guess_mono_impl`, `e_guess_mono_run`, `e_guess_mono_run_sound` AND
`e_guess_mono_impl_equation_1` all "Closed under the global context".
⚠️ `Set Equations With UIP` is a per-FILE flag — `Require` does not export
it, so every impl file needs its own line.

✅ **SETTLED (2026-08-14, later): TEN OF THE TWELVE BLOCKS ARE FLIPPED AND
IN THE TREE.**  `def_guess_impl.v`, `def_look_impl.v` (2 blocks),
`def_solve_impl.v` (3), `def_extract_impl.v`, `def_pat_impl.v` (2) and
⭐ `def_typing_impl.v` — the ENTRY POINT, the one runner whose dispatch the
completeness induction must analyse — all derive their unfolding equations
against `def_uip.v`'s Hedberg UIP, with no extra instances and no tactic
changes.  `make coq` green, README 32/32, spot-checked `Print Assumptions`
(including on `e_typing_impl_equation_1` and `e_pat_impl_equation_1`) all
"Closed under the global context".  ⭐ And the STANDING BAR is untouched:
the emitted `frost_guess.ml` is the same 3,873 lines, still passes
`ocamlc -c`, and still contains no `Obj.magic` / `Acc_rect` / `Fix_sub` /
`FixWf` — the derivation is proof-side only and does not reach extraction.

⛔ **THE TWO THAT DID NOT: `def_consis_impl.v` and `def_sub_impl.v`** — left
at `equations=no` at first.  (✅ **BOTH have since been flipped by
re-encoding, 2026-08-15 — see the tagged-mode entries at the end of this
section; ALL TWELVE blocks now derive their equations.**)  ⭐⭐ **The
characterisation is
sharp, not a guess: these
are exactly the two files that use `Equations`' MUTUAL `with` syntax**
(`with e_unify_impl` / `with e_consis_impl`; `with e_sub_flex_impl`), and in
both the derivation fails on a `with`-COMPANION's clause:

    Unable to unify "None" with "e_unify_impl    S0 nil α β HD H"
    Unable to unify "None" with "e_sub_flex_impl S0 NM M P0 nil Ξ α HP0 HD H"

Both are the companion's base clause — the one that returns `None` at an
empty context.  Every standalone `Equations` block in the tree derives; no
mutual one does.

⚙ **Three routes, in the order worth trying:**

1. ⛔ ~~Establish whether equation derivation for mutual `with` blocks is
   supported at all~~ — **SETTLED, and the answer is no.**  It reproduces
   in thirty lines with nothing of Frost in it, so this is an `Equations`
   limitation and not something about our rules:

```coq
From Equations Require Import Equations.
Set Equations With UIP.
Derive NoConfusion EqDec for nat.
#[export] Instance uip_nat : UIP nat := eqdec_uip _.

Inductive domA : nat -> Prop :=
| dA : forall n, (forall m, n = S m -> domB m) -> domA n
with domB : nat -> Prop :=
| dB : forall n, (forall m, n = S m -> domA m) -> domB n.

#[tactic="idtac", derive(equations=yes,eliminator=no)]
Equations fA (n : nat) (H : domA n) : option nat by struct H :=
fA O H := None ;
fA (S m) H := match fB m _ with None => Some 0 | Some k => Some (S k) end
with fB (n : nat) (H : domB n) : option nat by struct H :=
fB O H := None ;
fB (S m) H := match fA m _ with None => Some 1 | Some k => Some (S k) end.
Next Obligation. inversion H; subst; auto. Defined.
Next Obligation. inversion H; subst; auto. Defined.
```

   fails with `Unable to unify "None" with "fB 0 H"` — the `with`-COMPANION's
   equations, exactly as in `def_consis_impl.v` and `def_sub_impl.v`.  ⭐ So
   no amount of obligation-tactic engineering will fix our two files, and
   the three cycles already spent on that (§8c.4 above) should not be
   repeated.  ⚙ Worth reporting upstream; it is a clean minimal case.
2. ⛔ ~~the flex walk recurses on the CONTEXT and re-enters
   `e_sub_impl` only at `Flex-Solve`, so ask whether it can be hoisted out
   of the `with` into its own block~~ — **REFUTED at the guard checker
   (2026-08-15)**: any continuation-shaped hoist fails guardedness; see
   the tagged-mode entry at the end of this section.
3. ⚠️ The determinism route below does NOT rescue `def_sub_impl.v`:
   §8c.5 shows `e_typing_impl`'s branch calls `e_sub_impl` directly, and
   `e_sub_impl`'s own FlexMono branch calls `e_sub_flex_impl`, so knowing
   the RELATION holds still does not yield `Some`.  It may well rescue the
   consistency block, which `e_sub` reaches only through its own rules.

🟡 **The measurement trail that got there** (first pass flipped all twelve
at once and was reverted):

- ✅ `def_look_impl.v` (2 blocks) and `def_solve_impl.v` (3 blocks) derive
  their equations with no extra instances at all.
- ⛔ `def_consis_impl.v` is the FIRST failure: "Unsolved obligations when
  closing file".  The unsolved goals are the equation obligations of the
  mutual block's nested-match clauses (the log shows one for the
  `pskl_tophole` / `pskl_tophole` row).  ⚙ The cause is structural, not
  deep: `#[tactic="consis_impl_tac"]` applies to EVERY obligation, and that
  tactic was written for the SOUNDNESS obligations — it opens with
  `intros; inversion <the order>`, which destroys an equation goal — so the
  equation obligations fall through unsolved.

  ⚙ **Two attempts made, and what they establish** (so the next session does
  not repeat them):

  1. `Equations.CoreTactics.solve_equation` **does not exist**.  What the
     installed `CoreTactics` exports is `equations_simpl`,
     `equations_simplify` and `simpl_equations`.
  2. Giving `consis_impl_tac` a leading
     `first [ solve [ Equations.CoreTactics.equations_simpl ] | … ]` branch
     changes the failure but does not fix it.  The surviving goal is, e.g.

         e_unify_impl S0 nil α β HD H = None

     ⭐ which says what is actually needed: the runner recurses ON THE DOMAIN
     PROOF, so nothing unfolds until `H` is ELIMINATED.  The equation branch
     has to `depelim` the order hypothesis (`e_assign_order` /
     `e_unify_order` / `e_consis_order`) and only then reduce — which is
     exactly where the `UIP pskl` instance gets used, and why
     `Set Equations With UIP` is the enabling ingredient rather than a
     formality.  ⚙ It also explains the split measured above:
     `def_guess_impl.v`, `def_look_impl.v` and `def_solve_impl.v` needed
     nothing extra because their clauses reduce WITHOUT eliminating the
     domain proof.
  3. ⛔ **And `depelim` does NOT fix it.**  Tried, in the same run: an
     equation branch `intros; repeat depelim <the order>; simp …; simpl;
     try reflexivity`, with and without `Set Equations Transparent`.  The
     goal is unchanged each time —

         Unable to unify "None" with "e_unify_impl S0 nil α β HD H"

     so the block's equations are not merely unproved by the wrong tactic;
     `Equations` is not generating a reducible unfolding for them at all.
     ⚙ The distinguishing feature of the three files that fail-or-are-
     unknown versus the three that work is that this one is a MUTUAL block
     (`e_assign_impl` / `e_unify_impl` / `e_consis_impl` defined together).
     Mutual `Equations` definitions over a `Prop` domain predicate are the
     suspect; confirm that before attacking the tactic again.

⭐⭐ **AN ALTERNATIVE WORTH COSTING BEFORE MORE TACTIC WORK.**  The
completeness induction may not need every runner's equations.  It needs the
unfolding only for the DISPATCH of the judgement currently being proved
complete; for the SUB-CALLS it needs just (i) the sub-call returns `Some`
and (ii) its result is the derivation's.  (ii) does not need any unfolding
if the RELATION is deterministic at fixed inputs and committed names —
which is a `Prop`-level statement, provable by ordinary induction with no
`Equations` machinery at all, and which the dispatch-order analysis
(§8b.1's ForallR-before-ForallL, LE-Var/Absent priority, `type.ml`'s consis
order, the STEP/BASE readback split) is already the raw material for.  ⚙ If
that works, only the judgements whose own dispatch must be analysed need
`equations=yes` — and the mutual consistency block may be reachable purely
through its soundness and determinism.
- ✅ `def_extract_impl.v`, `def_pat_impl.v` and `def_typing_impl.v` were
  UNKNOWN at first (the build stops at the first failure) and were settled
  by reverting the failures and rebuilding: all three derive cleanly.
- ⛔ `def_sub_impl.v` is the second failure, on the same day and with the
  same shape as the consistency block.

⚠️ **And a build-hygiene note**: flipping a file that others `Require`
leaves their `.vo`s stale, and the failure reads "makes inconsistent
assumptions over library …", which looks like an axiom problem and is not.
Rebuild through `make coq`, never file-by-file with `coqc`.

✅ **`def_sub_impl.v` IS FLIPPED (2026-08-15) — BY THE USER'S TAGGED-MODE
ENCODING** (directive: "encode mutual with an extra mode to distinguish
which rule to use"), **plus one measured compile-time repair.**  Route 2
(hoist the flex walk out of the `with`) was REFUTED at the guard checker
first: a walk parameterized by a continuation that re-enters subtyping
fails `Recursive definition is ill-formed` — the checker does not thread
subterm specs through the walk's own inner fix, so the continuation's
domain-proof argument is never recognised as a subterm.  Thirty-line
Frost-free reproduction, same style as the one above; no shape of option
(2) can work.  What landed:

- **The tag.**  `sub_call : Set := sub_call_sub P | sub_call_flex Ξ α`;
  ONE `Equations` block `e_sub_call_impl` over it, `by struct` on a
  combined single-inductive order `e_sub_call_order` (def_order.v §6's
  mutual pair with the same tag, premise for premise).  The mutual orders
  and `e_sub_order_total` are UNTOUCHED — a mutual `Fixpoint` injection
  (`e_sub_order_to_call` / `e_sub_flex_order_to_call`) converts, and
  `e_sub_impl` / `e_sub_flex_impl` survive as thin same-signature
  `Definition` wrappers, so def_typing_impl.v, def_pat_impl.v and
  Extract.v needed NO change.  `sub_call_spec`/`sub_call_lc`/
  `sub_call_defs_mono` key the spec and the two hypotheses by the tag;
  at a concrete tag they are iota-convertible to the side's own forms.
- ⚠️ **The tag must be the FIRST argument.**  Tag-last, Equations split
  the M/P0 columns first and duplicated every mode/shape-generic flex
  clause under each specialization — 840 obligations, 30 of which do not
  close.  Tag-first: 315, all close.
- ⚠️⚠️ **Clause-pattern dispatch + `derive(equations=yes)` is a
  COMPILE-TIME TRAP at this block's size.**  The derivation proves one
  unfolding lemma per case-tree LEAF, and catch-all rows expand per
  constructor of every split column: measured **102 leaf equations,
  965 s, a 105 MB `.vo`** (the original mutual file: 6 s, 3.3 MB, same
  ~309 obligations; the biggest already-flipped peer, def_solve_impl.v:
  85 s).  The obligations are NOT the cost — the same block at
  `equations=no` is 9 s.  **The repair: ONE clause for the whole sub
  side, with the mode/shape dispatch as TERM-LEVEL convoy matches**
  (`match M as M1 return M = M1 -> … with … end eq_refl`).  Term matches
  are opaque to the equations machinery, so the block derives **7 clause
  equations in 150 s with a 26 MB `.vo`** — and each arm's convoy
  equality is exactly what the obligation tactic's `subst` consumes to
  specialize the order's premises, so `sub_impl_tac` needed only the
  combined-order inversion, the tag-wrapper unfolds and a
  `cbv beta iota in *`.  The flex side keeps its six clause patterns —
  `nil` + all five `abind` heads, no catch-all, so it never expanded.
  Extraction is unchanged in shape: the convoy equality is a Prop and
  erases, leaving the same plain nested matches.  Measured:
  `frost_guess.ml` went 3,873 → 3,783 lines (the two mutual functions
  merge into one tagged `e_sub_call_impl` plus two thin wrappers),
  `ocamlc -c` clean, and still no `Obj.magic` / `Acc_rect` / `Fix_sub`
  / `FixWf`.
- `e_sub_call_impl_equation_1` is the ∀-domain-proof clause equation
  §8c.3 wants (`simp` exposes the dispatch term; concrete `M`/`NM`/
  `P0`/`P` then reduce it by `cbn` with H untouched).  `Print
  Assumptions` on the impl, on `..._equation_1`, on the injection and on
  `e_sub_run_sound`: all "Closed under the global context".

✅ **AND `def_consis_impl.v` IS FLIPPED TOO (2026-08-15, later) — ALL
TWELVE BLOCKS NOW DERIVE THEIR EQUATIONS.**  The template applied
verbatim: tag `consis_call` (`_assign Ξ α P | _unify α β
| _consis Δ1 Δ2 P0 P` — ⚠️ `Type`, not `Set`: the Δ-slots carry metalib's
`atoms`), combined order `e_consis_call_order` mirroring §5's mutual
trio, a three-way mutual `Fixpoint` injection, and the three public
functions as wrappers.  Two consis-specific notes:

- ⚠️ **The block returns `consis_result` UNIFORMLY** — assign/unify used
  their own two-field `unify_result`, and a tag-DEPENDENT result type
  would extract through `Obj.magic` (§8's bar).  The assign/unify rows
  put `pskl_unit` in the join field (their specs never read it) and the
  wrappers repack.
- The leaf-explosion trap was avoided up front: the consistency side's
  P0 × P matrix is ONE clause with a convoy double-match in the original
  first-match row order, and assign's `Assign-UnivGhost-Id` special row
  is an inner convoy inside the flexible-head clause (the α-test commutes
  with the shape test, so the two original rows' first-match is
  preserved).  Unify's six clauses cover `nil` + all five heads with no
  catch-all and stay as patterns.  Result: **13 equations — exactly one
  per clause — 117 s, a 17.8 MB `.vo`**, every obligation closed by the
  adjusted tactic on the first run, all axiom-free.

⭐ **The check-mode entry-point exhibit is Qed with it**
(`prop_run_complete.v`): `e_typing_run S0 mode_tc nil ⌈unit⌉ exp_unit
= Some (unit result)` — one layer deeper than the infer twin, through
SI-Check into the consistency block's U-Unit row
(`simp e_consis_call_impl`).  It is the end-to-end witness that all
twelve runner blocks are computationally analysable.  Extraction after
both flips: `frost_guess.ml` 3,873 → **3,460 lines** (each mutual family
merged into one tagged function), `ocamlc -c` clean, no forbidden
constructs.

### 8c.5 ⭐⭐⭐ THE TECHNIQUE IS VALIDATED AT THE ENTRY POINT

With `def_typing_impl.v` flipped (§8c.4), `simp e_typing_impl` exposes the
runner's branch in a proof goal.  Measured on AT-Unit — the goal after
`simp`, verbatim and abridged only in the obligation names:

```coq
match Sumbool.sumbool_of_bool (degree_pskl_ck 0 P0 && defs_mono_ck Θ0) with
| left e =>
    match e_sub_impl S0 a_sub_mode_ty m P0 Θ0 pskl_unit … with
    | Some (exist _ r Hr) =>
        match pskl_readback (sb_out r) with
        | Some (exist _ A HA) =>
            Some (exist _ {| ty_supply := sb_supply r;
                             ty_ctx    := sb_ctx r;
                             ty_out    := A |} …)
        | None => None end
    | None => None end
| right _ => None end
```

⭐⭐ **So the completeness obligation is concrete now, and this session's
2a/2b lemmas are exactly its ingredients.**  To show this branch is not
`None`, in order:

1. `degree_pskl_ck 0 P0 && defs_mono_ck Θ0 = true` — `lc_pskl_ck_complete`
   and `defs_mono_ck_complete` (prop_dec.v §4), fed by the input's local
   closure and by the def-payload discipline (prop_run_invariants.v §1/§3).
2. `e_sub_impl … = Some r` — the sub-call.
3. `pskl_readback (sb_out r) = Some …` — `pskl_readback_complete`
   (prop_dec.v §6), fed by "the subtyping run's output is a `⌈⌉`-image",
   which is the one 2b item still open.

⚠️ **And it settles the priority of the two unflipped blocks.**  Step 2
calls `e_sub_impl` DIRECTLY, so `def_sub_impl.v`'s equations are on the
critical path — the determinism route can spare the consistency block
(which `e_sub` reaches only through its own rules) but not the subtyping
walk.  ⭐ Getting mutual `Equations` blocks to derive is therefore the next
task, not an optional cleanup.

⚙ **What this does NOT change.**  Milestone (1)'s soundness corollary and
its fixed entry supply stay exactly as they are; the decidability corollary
still composes as §5 says.  And the final statement needs only `Some`-ness —
agreement is an INTERNAL obligation of the induction (the ForallR and abs
output tests), not part of what decidability consumes.

✅ **THE ENTRY-POINT EXHIBIT IS QED (2026-08-15)** —
`frost/ext_algo/prop_run_complete.v` §1, the campaign's new file:

    e_typing_run_complete_unit_infer : forall S0,
      e_typing_run S0 mode_ti nil pskl_hole exp_unit
      = Some (mk_typing_result S0 nil ptyp_unit)

axiom-free, and the proof is the §8c.4 machinery end to end:
`simp e_typing_impl` (clause equation), `cbn` (the checker tests compute),
`unfold e_sub_impl` (the wrapper), `simp e_sub_call_impl` (the tagged
block's equation), `cbn` (the term-level dispatch reduces at
mode_ti/pskl_hole to SI-Infer; `pskl_readback` computes), `reflexivity`.
⚙ No `vm_compute` can replace this — the runners recurse on a Qed-opaque
totality proof, so plain reduction is stuck BY DESIGN; the equations
quantify over the domain proof, which is the §8c.3 point in action.
⚠️ **The check-mode twin is the measured boundary**: SI-Check calls
`e_consis_impl`, whose block is still `equations=no`, so its value is
stuck on its own opaque domain proof.  Flipping `def_consis_impl.v` with
§8c.4's template (tag over the three-way mutual, tag FIRST, term-level
convoy dispatch) is therefore the next unblocking move — the determinism
alternative cannot supply "the consis sub-call returns `Some`", which is a
statement about the RUNNER's dispatch, not the relation.
(✅ **Done the same day — see the end of §8c.4; the check-mode twin is Qed
alongside the infer one in `prop_run_complete.v`.**)

### 8c.6 ⭐ §8c.3 levels 1, 2a, 2b and 3 are CLOSED (2026-08-15): the LOOK block, BOTH SOLVE layers, and the CSTR FOLD

`prop_run_complete.v` §2 (1,381 lines total, 18.6 s):
`e_lookeq_run_complete` and `e_looksub_run_complete` are Qed and
axiom-free — an `a_*` derivation whose inputs the supply covers means the
runner does not return `None`:

      {{ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}a ->
      ftvar_in_aenv Θ ∪ {{α}} ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P' [<=] S0 ->
      e_lookeq_run S0 Θ α P P' HP HP' <> None

(and the `≼[α,m]` mirror).  The coverage premise is the ONLY hypothesis
beyond the derivation, exactly as scouted, and it re-establishes at every
recursive call by `ftvar_in_aenv_cons_tvar` + lngen's open-upper +
`clear -; simpl in *; fsetdec`.  The scouted plan held up whole; what the
proof ADDED to it, and what the next levels should copy or watch:

- **§2a — the hand strong inductions ARE the reusable idiom.**
  `e_lookeq_order_sind` / `e_looksub_order_sind`: a `Section` with the
  motive as a `Variable`, ONE `Hstep` hypothesis with every order premise
  doubled by its motive companion, and a term-level `Fixpoint` that
  rebuilds `Hstep`'s arguments — guard-safe exactly as the §8c.4
  injections were (applied-premise subterms; `match … with conj _ Hb =>
  Hb end` through the Arrow conjunction).  Both passed the guard checker
  first try.  For a LAYERED pair (lookeq never calls looksub) the lower
  layer's premises stay UNDOUBLED in the upper sind — the lower lemma is
  finished and ∀-quantified over its domain proof, so it applies at
  whatever proof term the equation's RHS carries.

- **§2b — one swap per row, and outputs requantified EXISTENTIALLY.**
  The five `rebind` helpers (`a_lookeq_rebind`/`_l`/`_r`,
  `a_looksub_rebind_l`/`_r`) move a binder-row premise from the rule's
  own witness `b` to the committed `supply_fresh S0` by ONE
  `a_looksub_lookeq_swap`, with `swap_*_fresh_id` pinning the inputs.
  ⭐ Because the completeness motive is `∀ Ξ 𝒞`, the outputs just ride
  the swap — no `β ∉ dom Ξ ∪ ftv 𝒞` is owed, which is what
  `a_lookeq_forall_move` (which preserves `Ξ`) has to pay.  ⚠️ Under
  `Set Implicit Arguments` their skeleton arguments stay EXPLICIT (they
  sit only under `open_pskl_wrt_pskl`/`ftvar_in_pskl` — non-rigid), so
  each carries an explicit `Arguments {…}` directive; do the same for
  every future helper meant to be applied to hypotheses.

- ⭐⭐ **The ONE thing scouting missed: the runner's rule PRIORITY needs a
  reorder lemma.**  At mode TC with a ghost-free `∀` target, THREE rules
  can root a derivation (LS-ForallR, LS-ForallL, LS-UnivGhostL) and the
  runner commits to ForallR (type.ml:663) — so a left-rooted derivation
  cannot feed the ForallR recursion by inversion alone.
  `a_looksub_forall_r_first` reorders it: plain structural induction on
  the derivation, where the left-rule cases apply the IH FIRST (at a
  fresh opener) and only then swap the two binders into place —
  swaps-after-IH is what keeps it structural, and
  `a_looksub_ctx_exchange` glues the two context entries.  The EQ layer
  has no such overlap: `guarded_pskl` excludes `∀`/`⫯` heads, so every
  eq branch is fed by exactly one candidate rule.  ⚠️ At each NEXT level,
  check the dispatch order in the `_impl` header against the relation's
  overlapping rules FIRST — every priority the runner commits to that the
  relation leaves open needs its own (small) reorder lemma.

- **§2c mechanics** (the case bash walks the runner's dispatch through
  `simp`; the derivation is inverted only to feed recursion — `Some` is
  `Some`):
  - `look_absurd` closes every impossible inversion case from the branch
    tests: mem-vs-`∉`, `guarded_pskl (∀/⫯ …)` inversion, the
    `ghost_free_ck`/`guarded_shape_ck` `_complete` converses against a
    false test, `lc_pskl (var_b _)`.
  - the `kill_*_call` tactics discharge a recursive call: assert
    `≠ None` from the IH, `destruct … eqn:` — ⚠️ the destruct SUBSTITUTES
    the call inside the pre-asserted hypothesis too, and the `None`
    branch closes by `exact (False_ind _ (Hne eq_refl))`, NOT by `exact
    Hne` (the inner call's `option (sig …)` differs from the outer
    result type).  ⚠️⚠️ They must run OUTSIDE any `match goal` branch —
    inside one, the same script makes the whole match report "No matching
    clauses"; the working shape is RENAME-FIRST: a `match goal` that only
    renames the inverted premises into stable names, then the kills at
    the top level.
  - `destruct m` only where the case tree split the mode (arrow subject;
    `∀` target under a `∀`/`⫯` subject).  ⚙ Read the leaf list off
    `Print Rewrite HintDb e_lookeq_impl` (25 leaves) /
    `e_looksub_impl` (41) rather than guessing from the clauses.

- ⭐ **The SOLVE level's eq layer is ALSO CLOSED (2026-08-15, same day):**
  `e_solve_eq_run_complete` / `e_solve_eq_impl_complete`
  (prop_run_complete.v §3), axiom-free.  What the solve adds to the look
  template, and every threading level above will need:

  - ⭐⭐ **The arrow row threads the CONTEXT, so the motive carries the
    derivation's context [`Θd`] separately**, related to the runner's by
    `flex_agree V Θd Θr` — agreement of `a_flex_tvar` on the INPUTS'
    variables `V` — plus a scoped-inputs premise `V ⊆ ftvar_in_aenv Θd`
    (new, also on the run-level statement; every call site satisfies it).
    SE-FlexR's `a_flex_tvar` test is the ONLY context-sensitive read in
    the solve cluster, so this is the whole interface: at the arrow row,
    the derivation's block avoids `ftvar Θd ⊇ V`
    (`a_solve_sub_eq_generated_fresh_set`) and the runner's block avoids
    the covering supply (`e_solve_sub_eq_block`), so
    `flex_agree_push_blocks` lets both blocks ride.  The §3b rebinds
    consequently let the context RIDE the swap (conclusions at
    `swap_aenv b β Θd`; `flex_agree_swap_left` re-establishes agreement) —
    and no `β == b` case split is needed anywhere.
  - ⚠️ **Never `eapply flex_agree_weaken` FIRST** — its set becomes an
    evar and the first `fsetdec` under it HANGS (measured: >110 s vs
    0.3 s).  Build agreement bottom-up with explicit sets (weaken →
    swap_left → push_tvar → final weaken), each as its own `assert`.
  - ⚠️ `nonghost_pskl (pskl_tophole _)` / `pskl_hole` have no
    constructor — SE-FlexR survives inversion at a ⫯ subject until
    `look_absurd` kills the `nonghost_pskl` evidence too.
  - The FlexR branches owe NOTHING for the guess: `e_guess_mono_impl` is
    total (a `sig`, not an `option`), so the branch is `Some` once the
    three tests pass — `flex_bound_ck` by `a_flex_tvar` transport
    through the agreement + `flex_bound_ck_complete`; the other two
    compute by `simpl` (the runner's FlexR subjects are never variables —
    the Var clause catches those first).

- ⭐ **The SOLVE level's SUB layer is CLOSED too (2026-08-15, level 2b):**
  `e_solve_sub_run_complete` / `e_solve_sub_impl_complete`
  (prop_run_complete.v §4), axiom-free — same motive as the eq layer
  (`flex_agree` + scoped inputs + coverage; `Θd := Θ` and reflexive
  agreement at the run level).  What the level added, and what the next
  ones should copy:

  - ⭐⭐ **The ∃-context reorder CANNOT be proved by one direct
    induction** — the scouted "let the context ride and deliver the
    motive facts" statement is right as an INTERFACE, but inside the
    induction the IH hands back an ABSTRACT context, and re-applying
    SS-ForallR needs a witness fresh for it: any swap that renames the
    target opener to such a witness re-pollutes the context it swaps
    (the junk chases the witness).  The resolution is a SPLIT:
    `a_solve_sub_forall_l_hoist` proves the reorder with the context
    FIXED under the STRONG freshness `β ∉ ftvar_in_aenv Θd` — which
    makes the look level's R-first dance apply verbatim (IH first at an
    interim δ, then fixed-context rebinds + `a_solve_sub_ctx_exchange`,
    a `ctx_change` instance as scouted) — and the wrapper
    `a_solve_sub_forall_l_first` BUYS that freshness with ONE
    sanitizing pre-swap `(β δ)` on the input derivation (inputs fixed:
    β, δ avoid them; agreement survives `flex_agree_swap_left`; and
    `β ∉ dom Θd'` — what `flex_agree_push_tvar` needs — is the swap's
    own by-product).  Expect the same split at every later level whose
    runner commits a binder rule the relation leaves open.
  - `a_solve_sub_tophole_l_first` (strip-first) is as easy as scouted:
    no swaps, the ForallR case re-applies at the SAME witness (the
    freshness set only shrinks), Vacuous answers fresh, Check dies
    (guarded excludes ⫯).
  - The case bash: the ∀/⫯ SUBJECT clauses apply their reorder to the
    derivation UNIFORMLY — no inversion at all; the ForallR-committing
    clauses (ghost-free ∀ target over unit/arrow/◇ subjects) rebind the
    rule's witness with the context RIDING (`a_solve_sub_rebind_r_ctx`)
    and re-establish agreement by the §3d chain verbatim; the Check
    clause drops into the finished §3 eq lemma with the motive premises
    passed UNCHANGED (same variable set); Arrow/GhostLF copy §3d's
    arrow case.  All 79 leaf equations
    (`Print Rewrite HintDb e_solve_sub_impl`) close; the pure-`None`
    ti/fn leaves close by `inversion Hd` alone (no rule fits).
  - ⚠️ Three new traps, all now paid for:
    (1) `repeat split` on the conjunction of motive facts DIVES INTO
    `flex_agree` (constructor-search introduces the ∀ and splits the
    iff) — use explicit nested `split`s.
    (2) The §3d by-clauses `clear - Hcov; simpl in Hcov; fsetdec` fail
    whenever the motive set mentions a COMPOSITE subject
    (`ftvar_in_pskl (pskl_arrow …)` stays unreduced in the GOAL and
    fsetdec treats it as an opaque set) — always `simpl in *`.  §3
    never saw this because the eq level's threading cases have bare
    metavariable subjects.
    (3) A finished `_impl_complete` lemma has its result-side arguments
    (`Θd Ξd P'd`) IMPLICIT, so the kill tactic that applies it directly
    must NOT pass the three `_` placeholders the sind-companion version
    passes — `kill_seq_call_g` (mirroring §2c's `kill_eq_call_g`)
    exists for exactly this.
  - `look_absurd` grew the sub level's two clauses: the Check clause's
    3-conjunct test, and `guarded_pskl pskl_hole`.

- ⭐⭐ **The YIELD-MISMATCH design fork is RESOLVED — option (a),
  determinism-up-to-fresh-renaming (2026-08-15, USER DECISION), and its
  metatheory is LANDED** (`frost/ext_algo/prop_solve_det.v`, 1,177
  lines, ~15 s, axiom-free): `a_solve_eq_det` / `a_guess_mono_det` —
  two derivations on the same inputs, at ANY two contexts, produce the
  same block and yield up to an aligned fresh-pair renaming.  Design
  points the file's header records, the short version:

  - ⚠️ A FUNCTIONAL renaming does not exist in general —
    `a_guess_mono__arrow` runs both halves at the same Θ, so ONE
    derivation may legally guess the SAME flexible for two holes
    (yield `α̂→α̂`) where another guesses two distinct ones.  So
    determinism is stated RELATIONALLY (`rel_pskl ρ V`, pairs ρ +
    identity support V), unconditionally; column UNIQUENESS is paid
    only at the TRANSPORT (`rel_pskl_chain` — a PALINDROMIC swap chain
    `(a,z)::(chain …)++[(z,b)]` through globally fresh intermediates,
    built from single swaps, no permutation datatype).  The fold will
    hypothesize `uniq` of the DERIVATION's block (the runner's is
    `uniq` by `e_solve_eq_uniq`), which propagates as ONE `uniq Ξd`
    premise per composite statement (blocks only append upward).
  - ⭐ The det lemmas are HYPOTHESIS-FREE (no flex_agree, no scoping):
    each derivation's side conditions held at its own context, and the
    eq rule choice is forced by input shapes — the overlaps all
    produce identical outputs (`a_solve_eq_var_subject_inv`).  Size
    induction (every eq rule strictly shrinks `size P + size Q`) lets
    BOTH binder rows rebind to a common fresh opener by plain swaps;
    `rel_pskl_close` DROPS the opener from the identity support, so no
    strengthening lemma is ever needed.
  - ⚠️⚠️ Two of the three >100 s hangs this file hit were the KNOWN
    evar-set fsetdec trap in new clothes: `eapply rel_pskl_mono` then
    `apply Hrel` leaves the source V an evar (pin it: `apply (Hrel V)`),
    and un-`clear`ed fsetdecs beside a size-induction IH crawl.  The
    third: `Require`-missing names inside a `match goal` body surface
    as "No matching clauses", not as an unbound-reference error — probe
    with markers before blaming the pattern.

- ⭐⭐ **LEVEL 3 IS CLOSED TOO (2026-08-15): the CSTR FOLD**
  (`e_solve_cstr_run_complete` / `e_solve_cstr_impl_complete`,
  prop_run_complete.v §5, axiom-free; file ~39 s).  The recipe below
  held whole — invert the eq-cons row, kill the head by §3's lemma,
  bridge (`e_solve_eq_sound`), read off ρ (`a_solve_eq_det`), transport
  the TAIL along `chain ρ zs`.  What it added:

  - ⚠️⚠️ **THE `fsetdec` CLIFF IS AT 6 SET VARIABLES, AND IT DICTATES
    HOW A MOTIVE SET IS WRITTEN.**  Measured on this very case, for a
    DISJOINTNESS goal (`_ ∩ _ [=] empty` hypotheses, `∉`/`∈`
    conclusion): **4 vars 0.25 s, 5 vars 2 s, 6 vars > 120 s.**  The
    fold's motive set is `ftv P ∪ ftv 𝒞`, which at the eq-cons row
    reduces to `ftv P ∪ ftv Q0 ∪ ftv 𝒞'` — spelling that out costs
    THREE variables in every column-freshness goal and HANGS the
    build.  The fix, and the rule for every level above: hold the set
    OPAQUE — `pose (V := …)`, one `HVdef : V = …`, `clearbody V`, and
    re-open `HVdef` only in the (four) places that must look inside.
    ⚙ PURE-SUBSET goals are NOT on this cliff (9 set variables cost
    0.1 s), so the discipline is needed for the disjointness family
    alone.  ⚙ This is the same failure MODE as the evar-set hang, but
    a different CAUSE — here every set is concrete.
  - The transport's own kit is mechanical: `flex_agree_swaps_left` and
    `ftvar_in_aenv_swaps_subset` are folds of §3a's singles under ONE
    hypothesis — every chain pair avoids `V` — which is `chain_atoms`
    plus the two column-freshness facts (left column ⊆ `dom Ξd1`,
    which dodges `ftvar_in_aenv Θd ⊇ V`; right column ⊆
    `dom (sv_block r1)`, which dodges `S0 ⊇ V`; intermediates freshly
    drawn).  ⭐ The one NEW lemma is `flex_agree_flex_block`: both
    sides gain the SAME flex block at the head, so agreement EXTENDS
    to that block's atoms — needed because `rel_pskl_ftv_r` bounds the
    transported yield by `V ∪ cols_r ρ`, not by `V`.  (No disjointness
    premise: an atom of the block is flexible on both sides outright,
    and `binds` is membership, so head shadowing is a non-issue.)
  - prop_solve_det.v gained the four facts nothing in the tree had:
    `atoms_fresh_list` (a fresh LIST, by iterating `atom_fresh`
    against a growing avoid-set), `uniq_flex_pairs_l_nodup` / `_r_nodup`
    (the `uniq` premises ARE the chain's two `NoDup`s — ⚠️ `map` is
    metalib's env-map, write `List.map`), and `swaps_aenv_uniq`.
  - The sind is the campaign's smallest — ONE doubled premise, the eq
    tail companion, which already sits at the runner's yield — and the
    case bash has 4 leaves (`Print Rewrite HintDb e_solve_cstr_impl`).
    The sub-WITH-A-TAIL leaf closes by `inversion Hd` alone: no rule
    fits, so the runner's `None` is never reached.  Both fold
    inversions are packaged as lemmas (`a_solve_cstr_sub_inv` /
    `a_solve_cstr_eq_inv`) rather than inlined — the eq one must hand
    back NAMES for both block halves and the middle yield.
  - `uniq Ξd` propagates by `uniq_app_1` / `uniq_app_2` (metalib), and
    the runner's own block is `uniq` for free (`e_solve_eq_uniq`).

- ⛔ **NEXT, in order:**
  1. **The EXTRACT level** (`e_extract_run_complete`) — scouted below
     (§8c.7); it is the first level that needs the LOOK judgements'
     determinism, and that is NOT a mirror of the solve one.
  2. Then the consis trio, and sub through the tagged blocks'
     equations (`simp e_consis_call_impl` / `simp e_sub_call_impl`
     after unfolding the wrappers), with the §8c.2 (2b) shape facts
     needed from the sub level up, ending at the flagship
     `e_typing_run_complete`.

### 8c.7 ⛔ SCOUTING RESULT (2026-08-15): the EXTRACT level's planned route is REFUTED — the collection is not deterministic up to renaming

§8c.6's "NEXT" item 1 was to repeat level 3's recipe one layer up: prove
`a_looksub` / `a_lookeq` determinism up to fresh renaming (with a
`rel_cstrs` congruence over `rel_pskl`, since the openers leak into the
collected 𝒞), then transport `a_extract`'s solve premise from the
derivation's 𝒞 to the runner's.  **That premise is false.**

`cex/cex_looksub_not_det.v` (Qed, axiom-free) exhibits, at subject
`∀_. α`, target `∀_. 1`, mode TC:

      LS-ForallL first:  ∀_.α ≼ ∀_.1  ↝  α ≼ ∀_.1  ↝  𝒞 = [ ≼TC ∀_.1 ]
      LS-ForallR first:  ∀_.α ≼ ∀_.1  ↝  ∀_.α ≼ 1  ↝  𝒞 = [ ≼TC 1    ]

Both derivations exist at the same context with the same block (`nil`),
and **both constraint lists are CLOSED** — so no renaming, and in
particular no swap chain, relates them.  The mechanism is simple and
applies wherever the two peeling rules cross: `LS-Var` emits `≼M P'` at
the CURRENT target, so peeling the target changes what is collected.

⭐ **Root cause, and it is the PAPER's own omission** (filed in
PAPER-GAPS.md): `SI-ForallL` carries the premise
`guarded{P_0} ∨ P_0 = □` with the paper's own comment "avoid overlapping
with ForallR; only need in an algorithmic presentation"
(`full-algo-spec.tex:838`), and `SI-UnivGhostR` carries the same guard
for the same stated reason (`:813`).  The COLLECTION's `LS-ForallL`
(`:1065`) and `LS-ForallR` (`:1049`) have **no such guard**.

⚙ The algorithm is unaffected: both lists are solvable, and the runner
commits to ForallR (`type.ml:663`), which is why level 1 needed
`a_looksub_forall_r_first` and why that lemma is stated with EXISTENTIAL
outputs — it was already the evidence that the reorder changes the
output, and this exhibit is what that existential was hiding.

⛔ **THE FORK — a USER decision, exactly parallel to §8c.6's:**

(a) **Restore the guard.**  Give `LS-ForallL` its counterpart's premise
    (`guarded{P'} ∨ P' = □` on the target) in `frost/algo/def_rules.v`,
    and audit `LE-ForallSyn` / `LE-UnivGhost1` for the same.  Then the
    scouted plan works verbatim: look-det up to renaming becomes
    provable (the crossing is gone), `rel_cstrs` + the ρ split (flex zip
    ++ rigid zip — note `chain_flex_pairs` ALREADY takes a sublist ρ0,
    so no loosening of `rel_pskl` is needed) carry it, and the extract
    level is a copy of level 3.
    COST: re-opens the look level's completeness, `a_extract_complete_gen`
    (P6-L), and the soundness chain through the collection — the guard is
    a new premise every construction site must discharge.  ⚙ The
    re-rooting lemma `a_looksub_forall_r_first` is exactly the tool for
    the completeness direction, and it already exists.

(b) **Keep the rules; carry a SOLVE-EQUIVALENCE invariant instead.**
    Replace "the two collections agree up to renaming" with "a fold
    derivation on one 𝒞 yields a fold derivation on the other (with a
    `uniq` block)".  It is true at the crossing above — `SS-ForallR`
    peels `≼TC ∀_.1` to exactly the `≼TC 1` the other list starts from —
    but it is NOT compositional in the obvious way: the fold THREADS its
    pattern through the list, so equivalence of `𝒞1 ++ 𝒞2` does not
    follow from equivalence of the halves, and the invariant has to be
    threaded through `LS-Arrow` as well as the ∀ crossings.
    COST: a new relation and its metatheory, materially bigger than the
    `rel_pskl` layer prop_solve_det.v already paid for.

(c) **Strengthen the reorder lemmas to be output-aware** and normalize
    the a-side derivation to the runner's dispatch BEFORE applying det.
    ⚠️ This is (b) in disguise: what a reorder must preserve is exactly
    solvability, since the exhibit shows it cannot preserve the output.

⛔⛔ **(a) WAS TRIED AND IT BREAKS COMPLETENESS (2026-08-16).**  The
experiment was carried far enough to be decisive and then reverted;
what it established, so nobody repeats it:

- **The guard must be the MINIMAL one.**  The paper's literal
  `guarded{P'} ∨ P' = □` also blocks a `⫯` target and a non-ghost-free
  `∀` target, where NOTHING else applies at a `∀` subject — the
  collection would be stuck, because "the target is guarded or `□`" is
  not an invariant of this judgement (`LS-Arrow` splits a guarded arrow
  target into halves of any shape).  The right premise is
  `looksub_no_forall_r m P' := ∀B, P' = ∀B → m = TC → ¬ ghost_free B`,
  i.e. "fire only where `LS-ForallR` does not".
- **Everything below P6 goes through, mechanically.**  The e-side rule
  mirrors it; `prop_swap.v` needs `looksub_no_forall_r_swap` and
  `_open`; `def_look_impl.v` discharges it from the runner's OWN
  dispatch (a `Hint Extern` into `lookdec`, since it is a constructor
  PREMISE that `eauto` must solve, not a top-level goal) — the three
  ways a ForallL branch is reached are exactly the three ways the
  premise is discharged, which is the design working; `prop_looksub.v`
  (6 sites) and `prop_decorate_sub.v` (4 sites) need only an extra
  intro name and `assumption`/`looksub_no_forall_r_open`.
  ⚙ `ghost_free_ck_complete` has to MOVE from `prop_dec.v` to
  `def_dec.v` — `prop_dec.v` sits below the runners (it requires
  `def_pat_impl` / `def_typing_impl`), so the runner cannot import it.
- ⛔ **P6 is where it dies, at a documented design point.**
  `alpha_stack_looksub` (`algo/sub/look/prop_sub_cstr.v:373`) proves

        alpha_stack α P → ∀ Θ m P0,
          {{ Θ ⊢ P ≼[α,m] P0 ⤳ nil ⨾ (≼m P0 :: nil) }}a

  — an α-stack collects the WHOLE target, **undescended, for ANY target
  and ANY mode**, by peeling the stack with `LS-ForallL`.  Its header
  says so in as many words: *"So Sub-ForallR's stack branch never
  invokes LS-ForallR, and the β it would have had to strip is simply
  never introduced."*  The guard makes that FALSE at `m = TC` with a
  ghost-free `∀` target — which is the counterexample verbatim, since
  `∀_.α` IS an α-stack.  Repairing it is not a fix-up: the Sub-ForallR
  stack branch would have to be re-derived with the target PEELED
  (`≼TC (open B β)` in place of `≼TC ∀B`), and that changes what the
  solve side of P6-Ss is handed.

So the fork stands, with (a) eliminated: **either P6's Sub-ForallR
stack branch is redesigned around a peeled target (a genuine piece of
work inside a closed proof), or the extract level carries (b)'s
solve-equivalence invariant.**  Both are substantial; (b) at least
leaves the closed theorems alone, which now makes it the better bet.
⚠️ A third possibility worth weighing first: the paper's authors may
prefer to guard `LS-ForallL` AND accept the peeled target in their own
Lemma E.17 proof — this is a finding to send them, not only a
mechanization choice.

### 8c.8 ⭐ The reference implementation, re-checked (2026-08-16) — and why (b) is the right invariant

The user asked whether `type.ml` is deterministic here, and if so whether
its choice is INCOMPLETE or simply better.  Answered against the running
binary (`paper/artifact/implementation`, `bin/met.exe --debug`):

**It is deterministic**, trivially: `constr_collect_sub` is one OCaml
`match` with first-match semantics (type.ml:654-706).  Its order is
Absent, Var, Vacuous, **ForallR**, ModR, Arrow, **ForallL**, ModL,
UnivGhostL, Check — so `LS-ForallR` strictly precedes `LS-ForallL`,
exactly as `e_looksub_impl` mirrors it.  ⚙ Note `LS-Var` precedes BOTH:
when the subject is already the looked-for variable the whole target is
collected verbatim, which is why the non-determinism needs a ∀-STACK
subject (`∀…∀.α`) to show up at all.

**But the order is NOT where anything is lost**, and this is the useful
finding.  A `--debug` trace of

      val f : forall a . forall d . []( unit -> (forall e . a) )
      val h : []( (forall b . b) -> unit )
      let test = h (f u)

walks `SI-ForallL → LS-ForallL → LS-ModL → LS-Arrow → LS-ForallR →
LS-ForallL → LS-Var → SolS-GhostL` and then rejects at SI-ForallL's own
`unless (is_wf p1)` (type.ml:961, the paper's `Θ₀,Ξ ⊢ P₁`): the target's
binder leaked into the collected constraint, so the solved instantiation
is the out-of-scope `β`.  ⚠️ It is TEMPTING to read that as "ForallL-first
would have found the better, closed answer `∀b.b`".  **It would not.**
`SolS-ForallR` does not close either — it opens the RHS and DISCARDS the
binder name (type.ml:517-518), and the mech's `a_solve_sub__forall_r`
says the same in its own comment: *"NO close: the result passes through
unchanged, so β may legitimately ESCAPE into [P'] … The leak is BY
DESIGN; ill-scoped results are filtered downstream by wf side
conditions"* (`algo/def_rules.v:614-640`).  So both orders leak, and the
loss is the DESIGN's (a polymorphic instantiation is not something
`guess^TY` can invent — it produces monotypes), not the dispatch's.

⭐⭐ **THAT IS EXACTLY WHY (b) IS THE RIGHT INVARIANT, and it is tighter
than "equivalent".**  `SolS-ForallR` IS the DELAYED `LS-ForallR`: peeling
a ∀ target during collection and peeling it during solving do the same
work, and neither closes.  On §8c.7's own exhibit the two lists do not
merely both solve — they solve to the SAME yield:

      [ ≼TC ∀_.1 ]  --SolS-ForallR--> [ ≼TC 1 ] --SolS-GhostL--> ⫯1
      [ ≼TC 1    ]                              --SolS-GhostL--> ⫯1

So the invariant to carry at the extract level is not a renaming and not
bare solvability, but **the fold's RESULT agrees** (up to the fresh
renaming §8c.6 already pays at the solve layer).  Concretely, the shape
to aim for:

      a_looksub Θ α m P P' Ξ1 𝒞1  ->  a_looksub Θ' α m P P' Ξ2 𝒞2  ->
      {{ (Ξ1 ++ Θ) ⊩ 𝒞1 ⨾ ◇ ⤳ Ξs1 ⨾ Q1 }}a  ->  uniq … ->
      ∃ Ξs2 Q2 ρ, {{ (Ξ2 ++ Θ') ⊩ 𝒞2 ⨾ ◇ ⤳ Ξs2 ⨾ Q2 }}a
                  ∧ rel_pskl ρ V Q1 Q2 ∧ …

which composes with §8c.6's `rel_pskl` machinery instead of replacing it,
and whose ∀-crossing case is discharged by SS-ForallR-invertibility
rather than by any reorder lemma.  ⚠️ Still to settle before coding: the
`LS-Arrow` case, where the fold THREADS its pattern through `𝒞1 ++ 𝒞2`,
so the two halves' agreements have to compose — that is the one place
this is not a straight induction, and it is where the design effort
should go.

⭐ **SETTLED (2026-08-16), and the whole configuration is now COHERENT
across all four layers** — `cex/probe_buried_forall_reject.v` (Qed,
axiom-free, 0.6 s) machine-checks the a-side:

- **`a_sub` REJECTS the configuration — every derivation, every
  collection order, over ANY context**
  (`probe_buried_forall_sub_reject`).  The node is AT-App's function
  premise inside the argument's SECOND (typing) pass — premise 3 of
  `a_typing__app` paints the inferred domain RIGIDLY (`ptyp_to_pskl A`),
  which is how a rigid `⌈∀b.b⌉` reaches the pattern at all (the SK-phase
  passes only `◇`, so skeleton inference never sees the crossing).
  Machine-checked, branch by branch: ForallL is the only applicable row;
  the collection at `∀_.α ≼TC ⌈∀b.b⌉` has exactly the
  cex_looksub_not_det.v choice (`[≼TC β]` leaked vs `[≼TC ∀b.b]`
  closed); BOTH fold to `⫯β` with β a LEAKED opener — at `◇ ≼TC ∀B`
  only SolS-ForallR applies (∀ is not guarded), and it does not close —
  `guess^TY` returns the bare `β`, and ForallL's disciplined-wf premise
  has no rule for an unbound variable.  So the two orders' folds agree
  up to the fresh opener — the (b) invariant, exhibited live — and the
  runner's ForallR-first commit misses nothing at this node.
- **The DECLARATIVE side rejects the program too** — read off the rules
  (not machine-checked; recorded in the probe's header): a `ForallL`
  instantiation's quantifiers are forcibly TAGGED (`a_tags_sort` at
  either sort requires `is_tskl`, which has no untagged constructor),
  the consistency LEAVES demand `Ψ [=] empty`, and the only Ψ-consuming
  row is `ad_pat_consis__forall_inh_tagged` — a tagged ∀ must meet an
  **inh-∀ of the target inside a consistency premise**.  In this
  configuration the target's only inh-∀ sits at a TC position, where
  Sub-ForallR peels it into a rigid binder before any consistency fires
  (and Check refuses unguarded subjects), so `a ≔ ∀b.b` can never
  discharge its tag: no `ad_pat_sub` derivation exists, and
  `a_sub_complete` is (consistently) vacuous here.  ⭐ This also
  explains the (iii)-vs-(iv) asymmetry as DESIGN, not incompleteness:
  in `f3` the `∀b.b` is part of the DECLARED type — untagged
  `all_syn`, instantiable by the UNTAGGED ForallL with a rigid opener,
  no tag owed.  Impredicative instantiation is exactly as available as
  the tag discipline says: where the instantiated ∀ meets an inh-∀.
- So impl, algorithm, and spec agree on the program; there is no
  impl-vs-spec divergence and no PAPER-GAPS entry owed.  The previous
  session's retracted claim ("a_sub rejects too") happened to be TRUE,
  but for a reason its one-path trace could not establish — the probe
  is the missing exhaustive-inversion argument, and the declarative
  rejection is what squares it with `a_sub_complete`.

⭐ **COROLLARY FOR THE CAMPAIGN: the e_ runner needs NO backtracking at
the look level.**  Phase 2's shapes (A)/(B) from the task plan are DEAD
WEIGHT and must not be built: the probe shows the choice point's two
branches fold to the same yield up to a fresh opener, i.e. shape (C) —
"ForallR-first never loses" — is what holds, and (C) IS option (b)'s
invariant one layer down.  §8c.9 is that invariant's design.

### 8c.9 ⛔ THE EXTRACT LEVEL, option (b) — the design, settled before coding (2026-08-16)

The target is `e_extract_run_complete`.  The extract runner
(def_extract_impl.v:81) is a straight three-stage pipeline — look, fold,
guess — with no recursion of its own, so the completeness proof is an
ASSEMBLY: stage 1 answers by `e_looksub_run_complete` (level 1), stage 3
is total (`e_guess_run`), and the WHOLE new content is stage 2's
obligation — `e_solve_cstr_impl_complete` (level 3) demands an a-side
fold derivation ON THE RUNNER'S collection `𝒞2`, while the inverted
`a_extract` supplies a fold only on the DERIVATION's `𝒞1`.  So the one
new theorem is the b-core, a pure a-side lemma:

      look1 : {{ Θd ⊢ P ≼[α,m] P' ⤳ Ξ1 ⨾ 𝒞1 }}a →
      look2 : {{ Θr ⊢ P ≼[α,m] P' ⤳ Ξ2 ⨾ 𝒞2 }}a →
      {{ Θf1 ⊩ 𝒞1 ⨾ acc1 ⤳ Ξs1 ⨾ Q1 }}a →
      rel_pskl ρ V acc1 acc2 → (agreement/uniq/scoping side conditions) →
      ∃ Ξs2 Q2 ρ', {{ Θf2 ⊩ 𝒞2 ⨾ acc2 ⤳ Ξs2 ⨾ Q2 }}a
                   ∧ rel_pskl ρ' V Q1 Q2 ∧ …

stated FUSED (the fold hypothesis rides the look-pair induction) — do
NOT define a `rel_cstrs` relation first; the fused motive is what makes
the LS-Arrow case compose, which was §8c.8's open design point (see
"the Arrow case" below).  At the assembly, `look2` comes from
`e_looksub_sound` on the runner's stage-1 result, `Θf2` is the runner's
`lk_block r1 ++ Θ0`, and level 3's `e_solve_cstr_run_complete` consumes
the ∃-fold.

**The induction, and why it is the §8c.6 template verbatim.**  Strong
induction on `size_pskl P + size_pskl P'` (every look rule strictly
shrinks it; opens are at variables, so `size_pskl_open_pskl_wrt_pskl_var`
applies), with BOTH look derivations INVERTED at each step, never
structurally inducted — exactly `a_solve_eq_det`'s scheme, which is what
lets either side be REBOUND to a common fresh opener by plain swaps
(`a_looksub_rebind_l/_r`, prop_run_complete.v §2b) before the IH fires.
A structural induction on either look dies at precisely that rebind; do
not try it.

**The crossing inventory — measured against the rules, complete.**  Two
derivations of the same look node can differ ONLY by:

1. **Opener/FlexR names** (all five ∀-rows leak; LE-FlexR invents α1) —
   a fresh-pair renaming, carried by ρ and discharged with the LEVEL-3
   TRANSPORT KIT VERBATIM (`rel_pskl_chain` + `a_solve_cstr_swaps` +
   `flex_agree_swaps_left` + `ftvar_in_aenv_swaps_subset`, all Qed in
   prop_solve_det.v / prop_run_complete.v §5).
2. **The ∀-peel slack** (§8c.7's crossing): at a ghost-free ∀ target at
   TC, LS-Var-now vs LS-ForallR-first changes the final sub-constraint
   from `[≼TC ∀B]` to `[≼TC B^β]` with β leaked.  DIRECTIONAL: the
   runner peels maximally, so the runner's final target is the
   MORE-peeled one, always.  Discharged in the fold transport by the
   NEW ∀-peel lemma on the solve layer (below), never by a look-level
   reorder.
3. **The ◇-emission slack**: at target `◇` with subject `α`, LS-Var vs
   LS-Vacuous is `[≼m ◇]` vs `nil` (and LE-Var vs LE-Vacuous is
   `[eq ◇]` vs `nil`).  Also DIRECTIONAL (the runner's match puts Var
   before Vacuous, so the runner emits MORE).  A `◇`-target solve step
   is the IDENTITY (SS-Vacuous / SE-VacuousR, nil block), so the extra
   constraints are free to BUILD on the runner side; nothing to invert.
4. **α-free subtrees**: LS/LE-Absent vs a structural derivation — both
   produce `nil ⨾ nil` (the only emitting rules, Var/FlexR, need an
   α-occurrence), so no slack at all.  Small lemma:
   `α ∉ ftvar_in_pskl P → look → Ξ = nil ∧ 𝒞 = nil`.

Everything else is shape-forced (checked rule-by-rule for both layers:
the eq layer's only overlaps are 3 and 4; LS-Check×ForallR is excluded
by guardedness, Var×Check by Check's own `A ≠ α`, FlexR×Var by
`P ≠ α`).

**The NEW engine — the ∀-peel lemma** (this is what §8c.8 meant by
"discharged by SS-ForallR-invertibility"):

      a_solve_sub_peel_forall_r :
        {{ Θ ⊢ₛ P ≼[TC] ∀B ⤳ Ξ ⨾ P' }}a → β fresh →
        ∃ Ξ' P'', {{ Θ ⊢ₛ P ≼[TC] B^β ⤳ Ξ' ⨾ P'' }}a  ∧  (P'' ~ρ P')

by size induction on `size P + size Q`: at a ∀ target only SS-Var
(target ignored — rebuild by SS-Var), SS-ForallL / SS-UnivGhostL
(subject peels — rebind the opener away from β, IH, rebuild) and
SS-ForallR (rebind its opener to β; then STRIP the now-unused
`β ~ tvar` entry — context-shrinking is sound because the solve reads
its context only through SE-FlexR's `a_flex_tvar` (β is rigid: not
flex either way) and through freshness avoid-sets (monotone under
shrinking)) can root the derivation — SS-Check/GhostL die on
`guarded (∀B)`.  The REVERSE direction is one constructor (SS-ForallR
at β) and is what the derivation-peeled-runner-not case would need —
it cannot arise (slack 2 is directional), but the constructor is there
if a later consumer wants it.

**The Arrow case (the §8c.8 design point), now closed on paper.**
`𝒞1 = C1a ++ C1b` with `C1a` PURE-EQ (a_lookeq emits only eq
constraints — small lemma) and look2's `𝒞2 = C2a ++ C2b` likewise.
Decompose the given fold by the pure-eq append decomposition (the
missing mirror of `a_solve_cstr_app`, prop_eq_cstr.v:155 — write
`a_solve_cstr_app_inv`), IH-eq on (C1a, C2a) at (acc1, acc2, ρ)
producing the runner-side eq-fold and RELATED mid-yields at ρ', then
IH-sub on (C1b, C2b) at the mids and ρ', recompose with
`a_solve_cstr_app`.  The threading is absorbed by the motive's
∀-quantified (acc1, acc2, ρ) — this is exactly why the statement must
be fused; with a standalone `rel_cstrs` the two halves' agreements do
not compose (the fold's mid-pattern is not describable list-locally).

**Side conditions to carry on the motive** (all §8c.6-standard): the
two folds' contexts related by `flex_agree` on the inputs' variables,
extended to ρ-PAIRS — new small definition, `flex_agree_rel ρ V Θ1 Θ2`
:= id-agreement on V plus `(a,b) ∈ ρ → (flex Θ1 a ↔ flex Θ2 b)` — the
pairs arise at LE-FlexR's invented flexibles, which both sides test
with `a_flex_tvar` later; `uniq` of the derivation-side blocks (the
runner's are uniq for free); scoped inputs `V ⊆ ftvar Θf1`; ρ's columns
fresh on their own sides (what `rel_pskl_chain` needs).  Expect the
exact trap list of §8c.6: hold motive sets opaque (the fsetdec cliff),
pin `apply (Hrel V)`, explicit nested splits, rename-first matches.

**What EXISTS and is reused unchanged**: `rel_pskl` + mono/close/chain
(prop_solve_det.v §1-§2), `a_solve_cstr_swap(s)` (prop_swap.v:1067,
prop_solve_det.v:647), `a_solve_cstr_app` (prop_eq_cstr.v:155),
`a_solve_cstr_sub_inv`/`_eq_inv` (prop_run_complete.v §5),
`a_looksub_rebind_*`/`a_lookeq_rebind_*` (§2b), `flex_agree` + its
push/swap kit (§3a + §5's `flex_agree_swaps_left`), the level-1/2/3
`*_run_complete`s, and `a_looksub_forall_r_first` (which stays as-is;
the fused motive replaces the plan of strengthening it).

**Landed 2026-08-16, all Qed and axiom-free:**

- `frost/ext_algo/prop_look_equiv.v` (new file, below the runner
  stack): `a_lookeq_cstrs_pure_eq`, `a_looksub_subject_absent` /
  `a_lookeq_subject_absent` (crossing 4), the ◇-target identity
  inversions on both solve layers (crossing 3), and
  `a_solve_cstr_app_inv` (the Arrow decomposition); the fold's two head
  inversions moved in from prop_run_complete.v §5.
- **THE ∀-PEEL LEMMA is Qed** — `a_solve_sub_peel_forall_r`
  (prop_run_complete.v §6a), by exactly the recipe above: size
  induction on `size P + size B`; the SS-ForallL case rebinds its
  opener away from the requested β before the IH
  (`a_solve_sub_rebind_l`), the SS-ForallR case rebinds TO β
  (`a_solve_sub_rebind_r`) and strips the spent `β ~ tvar` entry with
  `a_solve_sub_eq_ctx_change` via two new inline helpers
  (`a_flex_tvar_strip_tvar`, `a_flex_weaken_cons`).  ⚠️ Traps paid:
  `a_flex_tvar` has TWO disjuncts (it is `a_binds_tvar` that has
  three); `clear -.` is not syntax (keep one hypothesis); the file
  needed its first `Require Import Coq.micromega.Lia`.

⭐⭐ **THE PAIR INDUCTION'S DESIGN REFINED (2026-08-16, second pass) —
no rebinds, and the re-rootings apply to EITHER side.**  Three
discoveries that reshape §6b, plus its one open hazard, resolved:

1. **The motive relates REL-RELATED node pairs and never rebinds.**
   State the pair over `(P1 ≼[α,m] P1')` vs `(P2 ≼[α,m] P2')` with
   `rel_pskl ρ V` relating subjects and targets componentwise (both
   looks at the SAME Θ — true at the assembly and preserved).  At a
   same-root binder pair the two openers are PAIRED into ρ
   (`rel_pskl_open_pair`: rel bodies → rel of the opens at a fresh
   pair) — no side is ever swapped, so none of the swap-chain/acc
   bookkeeping the first design fought exists at all.  Size induction
   on `size P1 + size P1'` (rel preserves size).
2. **R′/R″ are COLLECTION-PRESERVING, so they may be applied to the
   PINNED side too.**  A constraint list is built from TARGET material
   and generated names alone — the subject never enters it (LS/LE-Var
   emit the target, LE-FlexR a fresh name) — so re-rooting a subject
   peel to the front preserves `(Ξ, 𝒞)` EXACTLY and any fold on 𝒞
   rides for free.  Landed Qed (prop_look_equiv.v §6):
   `a_looksub_strip_tophole_l` (R″ — no freshness owed) and
   `a_looksub_open_forall_l_first` (R′ — target-only size induction;
   LS-ForallL's case is its own premise rebound by one swap, whose
   output-avoidance is `a_looksub_lookeq_generated_fresh` +
   `a_decls_no_ftvar` for the block and the disjunctive
   `a_looksub_lookeq_ftv` for the collection; LS-ForallR's case
   recurses, exchanges, rebuilds, rebinds).  At a
   ForallR-vs-subject-peel diagonal, apply R′/R″ to WHICHEVER side is
   ForallR-rooted and recurse aligned.  With §5's ◇-collapse
   (`a_looksub_hole_target` / `a_lookeq_hole_target`, also Qed) and
   §2's α-free collapse, the ONLY remaining crossing is
   (Var, ForallR-ish) at a ghost-free ∀ target — and there the look
   needs nothing: the fold pays via `a_solve_sub_peel_forall_r` (§6a),
   then the pair recurses on two Var-instances.  ⚙ Support landed:
   `swap_cstr_fresh_id`/`swap_cstrs_fresh_id` (prop_looksub.v, beside
   `ftvar_in_cstrs`), `a_decls_no_ftvar` MOVED to algo/prop_basic.v
   (its a_decls home; only consumer was the P7 file).
3. **The fold transports are REL-transports, not chain equivariance.**
   Direct inductions mirroring the solve rules: given a solve on
   side-1 data and componentwise `rel_pskl ρ V` inputs, produce the
   side-2 solve with rel-related yield, ρ growing by the fresh pairs
   the generative steps invent (SE-FlexR's guess) — binder rows open
   BOTH sides at one common fresh name (each side's freshness is
   per-side, so a globally fresh atom serves both).  Context
   interface: `flex_agree_rel ρ V Θf1 Θf2` := id-agreement on V plus
   `(a,b) ∈ ρ → (flex Θf1 a ↔ flex Θf2 b)`.  Needed for: guess_mono,
   solve_eq, solve_sub, and the fold (pointwise-rel constraint
   lists); the ∀-peel slack enters only through §6a.

⚠️ **THE ONE HAZARD, AND ITS RESOLUTION — pre-normalize side 1.**  A
raw `a_looksub` derivation may reuse ONE atom in two roles (sibling
subtrees' freshness sets don't mention each other — e.g. an eq-half
LE-FlexR name equal to a sub-half ForallR opener).  At the crossing
that atom would need two ρ-pairs with INCOMPATIBLE flex-status on the
runner side (a FlexR name is flex, an opener rigid), making the
extended `flex_agree_rel` unsatisfiable — so the pair motive carries
side-1 APARTNESS premises on the visible outputs, and the assembly
discharges them by PRE-NORMALIZING side 1: a hygienic REDERIVATION
lemma (thread an avoid-set through the look, mirroring the supply
discipline; same rule at every node, fresh pairwise-apart generated
names, outputs pointwise `rel_pskl` at fresh pairs) followed by the
fold rel-transport at the ◇ accumulator.  The runner side needs no
normalization — its supply discipline already yields apartness
(read it off the e_-level block/coverage lemmas).  ⚠️ Do NOT try to
get side-1 hygiene by re-running the runner on side-1's inputs: the
runner is deterministic, so that just reproduces side 2 and is
circular.

⚙ The rel kit's open-compat is LANDED too (prop_solve_det.v §1, Qed):
`rel_pskl_open_pair` (open related bodies at a PAIR — the pair
induction's binder move) and `rel_pskl_open_var` (common opener, the
transports' binder rows), each with its `_rec` engine mirroring
`rel_pskl_close_rec`.

⭐⭐ **ALL FIVE REL-TRANSPORTS ARE Qed (2026-08-16, `d64d164` +
`5999406`)** — new file `frost/ext_algo/prop_solve_rel.v` (between
prop_solve_det and prop_run_complete, which now imports it):

- §2 `flex_agree_rel ρ V Θ1 Θ2` (id-agreement on V + pairwise on ρ's
  pairs) with its push kit: rigid PAIR (`_push_tvar_pair`, both-False),
  common rigid (`_push_tvar`), aligned flex-pair blocks
  (`_push_pairs`); the `a_flex_tvar` context plumbing MOVED here from
  prop_run_complete §3a/§5a.
- §3–§6 transports 1–4: `a_guess_mono_rel` (no agreement — the guess
  never reads flexibility), `a_solve_eq_rel`, `a_solve_sub_rel`,
  `a_solve_cstr_rel` (pointwise `rel_a_cstrs`; ⚠️ the b-core stays
  FUSED, the list rel serves aligned-collection consumers only).
  ⭐ THE PROOF SHAPE BEAT THE PLAN: no side-1 rebind ANYWHERE — binder
  rows open side 2 at its OWN fresh witness, PAIR the openers
  (`rel_pskl_open_pair`), and closing rows re-close by the NEW
  `rel_pskl_close_pair` (det §1, the open_pair mirror; conditions =
  the pair's atoms have no other role) — so none of the det template's
  swap-chain machinery is used, and plain STRUCTURAL induction on the
  side-1 derivation suffices (no size induction: side 1's premises are
  used as-is).  The sub layer's conclusion adds `ρx` — SS-ForallR's
  opener pairs, which never re-close and ride the yield relation as
  RIGID pairs fresh on their own sides.  Every side-2 generated name
  additionally dodges a caller avoid-set `L` (the supply discipline's
  relational rendering); side-2 blocks are `uniq` by construction.
- §7 transport 5 = **THE HYGIENIC REDERIVATION**:
  `a_looksub_lookeq_rel_e` — an a-side look transports to an
  `e_looksub`/`e_lookeq` derivation on rel-related inputs over any
  covering supply (with reflexive inputs: same instance, supply-fresh
  pairwise-apart names, outputs pointwise rel at fresh pairs).  The
  looked-for α stays COMMON (α ∈ V, α outside both columns;
  `rel_pskl_in_id`/`rel_pskl_notin_r` route Var/Absent to the same
  rule).  `ρx` = the five ∀-rows' leaked opener pairs (side-2 names in
  `S1 ∖ S0`, apart from the side-2 block: `cols_r ρx ∩ dom Ξ2`), `ρn`
  = LE-FlexR's block pairs.

⭐⭐ **THE b-CORE'S DESIGN SHARPENED (third pass, 2026-08-16) — state
it over `e_looksub` on BOTH sides.**  Two findings force this:

1. ⛔ "side-1 apartness premises on the visible outputs" are NOT
   MAINTAINABLE: a hygiene companion (an e-derivation of the same
   instance, or any output-level fact pack) does NOT invert in
   lockstep with the a-derivation being inducted on — two derivations
   of ONE instance may use different root rules (that slack IS the
   crossing inventory), so the companion cannot follow the descent.
   Hygiene must ride the inverted derivation itself — i.e. the
   derivation must BE supply-threaded.  (R′/R″-stability of
   output-level premises is real but irrelevant — maintainability is
   what fails.)
2. ⚠️ **A conflated RAW `a_extract` can ACCEPT MORE than the runner**
   — so `e_extract_impl_complete` MUST carry a hygiene premise, in
   level 3's `uniq Ξd` precedent (not internally dischargeable): if a
   leaked look-opener β collides with a SIBLING subtree's LE-FlexR
   name (reachable: LS-Arrow runs both premises at Θ), the raw fold at
   `Ξ ++ Θ0` sees β BOUND FLEX (the sibling's block entry) and may
   fire SE-FlexR at a position where the hygienic collection has a
   RIGID opener — and `[P ≼ β-rigid]` with P non-var non-ghost is
   STUCK.  The honest closed premise: **the look half is e-derivable
   with the same outputs** (`Hhyg : ∃ S0h S1h, {{S0h ↝ S1h ⊨ Θ0 ⊢ P
   ≼[α,m] P' ⤳ Ξ ⨾ 𝒞}}e` + coverage), which the SUB level's
   completeness will thread (transport 5 manufactures it from any raw
   look, at rel-renamed outputs; wf-preservation is the alternative
   source).  Consequently the assembly has NO pre-normalization step:
   side 1 of the b-core IS `Hhyg`'s derivation, and the fold
   rel-transport at the ◇ accumulator is not needed at the assembly
   (transport 5's and 4's roles move UP one level, to whoever
   discharges Hhyg from a raw derivation).

The b-core is then: BOTH looks as e-derivations over the SAME Θ, size
induction on `size P1 + size P1'` (`rel_pskl_size`) with BOTH
e-derivations INVERTED at each step (never structurally inducted), the
fused fold hypothesis riding as designed; each side's freshness facts
read off its own supply thread; same-root binder pairs still pair
openers with NO rebinds.

⭐ **THE e-SIDE LOOK KIT IS LANDED** (`frost/ext_algo/prop_look_pair.v`
§1, Qed, axiom-free, 2026-08-16) — and it came out SMALLER than
planned, because the e-look's CONTEXT IS INERT (every freshness
condition reads the supply; the context only mirrors the a-shape):

- §1a `e_looksub_lookeq_ctx_any` — a derivation transports to ANY
  context; replaces every a-side `ctx_exchange` surgery.
- §1b `e_looksub_lookeq_supply_respect` — both supply indexes
  transport along `[=]` (the re-rootings re-associate `add`s).
- §1c e-R″ `e_looksub_strip_tophole_l` (outputs AND supplies exact)
  and e-R′ `e_looksub_open_forall_l_first` — ⭐ stated with an
  EXISTENTIAL opener (`∃ γ ∉ S0`, derivation of the γ-opened subject
  at `add γ S0`): its ForallL case's premise IS the goal at the
  derivation's own opener, its ForallR case reuses the IH's opener
  below the rebuilt root.  Consequently NO e-swap is ever performed —
  **the planned e-SWAP KIT is NOT NEEDED and was not built** (the
  b-core pairs whatever opener e-R′ returns; its freshness class,
  `∉ S0`, is the same as any e-opener's).

**The b-core's MOTIVE, first cut (worked out on paper 2026-08-16;
maintenance checked for the arrow/binder descents).**  Beyond the
§8c.6-standard pack (fold on `C1` from `acc1` at `Θf1`; `rel_pskl ρ V`
on `acc`; `flex_agree_rel ρ V Θf1 Θf2`; scoped inputs), carry per
side:

- the BINDS premise `∀ (x,bd) ∈ Ξi, binds x bd Θfi` — the collections'
  LE-FlexR names must be FLEX in the fold contexts (their pairs extend
  the agreement True↔True);
- ⭐ the SUPPLY-INTERVAL invariant
  `Hopi : ∀ x, x ∈ Si1 → x ∉ Si0 → x ∉ dom Ξi → ¬ a_flex_tvar Θfi x`
  ("a name of THIS subtree's supply interval that is not in its block
  is non-flex in the fold context") — this is what makes an opener
  pair extend the agreement False↔False, and it MAINTAINS: an arrow's
  first half strengthens `x ∈ S-mid` to exclude the second half's
  block (which avoids S-mid), the second half dually via
  `Sa0 ⊆ S-mid`; a binder premise shrinks the interval.  The naive
  alternatives (`flex Θf1 x → x ∈ Sa0 ∪ dom Ξ1`, or coverage
  `ftvar Θf1 ⊆ Sa0`) are NOT maintainable — checked and rejected.

⚠️ ONE OPEN DESIGN POINT for §6b: when an opener pair `(β1,β2)` enters
ρ, the rel-transports' SCOPING hypotheses demand
`cols_l ρ ⊆ ftvar Θf1` — but a leaked opener is NOT in the fold
context unless enriched.  Two candidate resolutions, to be decided at
the proof: (a) pre-enrich `Θf1`/`Θf2` AT THE ASSEMBLY with rigid
entries for the whole generated interval (atoms are FINITE sets —
`elements (diff Sa1 Sa0)`-style), so the scoping holds globally and
the motive never re-enriches; or (b) generalize the transports'
scoping hypotheses to carry rigid-pair columns separately (a per-pair
avoidance premise instead of ftvar-containment).  (a) touches only the
assembly; (b) touches prop_solve_rel's statements — prefer (a) unless
its `elements`-plumbing turns ugly.

⛔⭐ **FOURTH PASS (2026-08-16) — the third-pass b-core is FALSE as
designed, and the repair is structural.**  Two machine-level findings:

1. ⛔ **The b-core over two ARBITRARY e-derivations is FALSE**
   (`cex/probe_bcore_ug2_flexr.v`, four exhibits, assumptions-closed).
   `guarded_pskl` includes VARIABLES, so at `⫯(α) ∼[α] β` both
   `LE-FlexR` and `LE-UnivGhost2` fire — a root overlap the crossing
   inventory missed (it checked FlexR×Var, not FlexR×UnivGhost2).  The
   collections diverge in KIND (`[eq α̂1]` fresh-flexible vs `[eq β]`
   raw target), and with β RIGID at pattern `1` the FlexR-side fold
   succeeds where the UG2-side fold is STUCK — all of the third-pass
   motive's side conditions are satisfiable around the pair.

2. ⛔ **Decision (a)'s enrichment route cannot run**: "pre-rename
   fold1 via `a_solve_cstr_rel` with reflexive inputs" needs
   `ftv 𝒞l ⊆ V` (`rel_pskl_refl`) AND `V ⊆ ftvar Θf1` (the
   transports' scoping) — but a raw `a_extract`'s collection mentions
   leaked look-openers in NEITHER (rule freshness makes them avoid
   `ftvar Θ0`).  No output-level premise repairs it: a raw fold can
   internally collide with LATER-constraint payload names (the
   one-atom-two-roles hazard, fold edition), so no transport of a raw
   fold exists to build.

**The pivot — the b-core is RUNNER-SIDED.**  Side 2 of the pair
induction is THE RUNNER'S COMPUTATION — the hypothesis is
`e_looksub_impl S0 Θr α m P2 P2' hp hp' H = Some s` (and the eq twin),
with `proj2_sig s` supplying side 2's e-derivation for the
supply/block facts.  Side 1 stays an arbitrary e-derivation (what the
Hhyg premise gives).  Consequences, all favourable:

- The fatal orientation dies structurally: the runner takes FlexR at
  every (⫯-subject, var-target) node (def_look_impl.v).  The surviving
  one (side 1 = UG2ⁿ∘Var retaining the raw target, runner = FlexR) is
  transportable because the runner's target is a FRESH UNDEFINED
  FLEXIBLE: a small JUNK-TARGET head transport (target vars unrelated,
  only "side-2 target flex" assumed; 4 rule cases — SE-Var, SE-FlexR,
  SE-GhostL, SE-GhostGuarded) always answers, at worst with a VAR
  yield on both sides.  The eq motive carries that as a YIELD HATCH
  (`Q1`, `Q2` both vars, NO facts) — harmless because a var pattern is
  a FIXED POINT of the fold (SE-Var/SS-Var ignore their targets), so
  side 2's continuation is total (`a_solve_cstr` from a var pattern
  derives with `nil` block) and side 1's inverts to the same shape.
- Each case has exactly ONE side-2 root (the dispatch is a function of
  the shapes + the mem/gf tests, which side-1 facts resolve).  In
  particular the runner NEVER target-peels at a var subject (the
  var-subject clause fires first), so of §8c.9's crossing 2 only the
  (ForallR₁, runner-Var₂) orientation lives — discharged by recursing
  at a freshly-invoked runner Var-leaf on the peeled target and
  REBUILDING SS-ForallR around the recursion's solve (its premise
  lands exactly at the `(β₂'~tvar)`-consed fold context).  The §6a
  peel is consumed only via a NEW KEEP-variant
  (conclusion at the `(β~tvar)`-consed context — no strip) at the
  OTHER diagonal's Var-bottom.
- The (ForallL/UGL vs runner-ForallR) diagonals re-root SIDE 1 by a
  NEW disjunctive e-side ForallR-FIRST lemma (existential opener β₁,
  `β₁ ∈ S1 ∖ S0`, supply claim `S1' [=] add β₁ S1`; the disjunct
  records the Var-bottom case, whose outputs LEGITIMATELY change from
  `[sub TC ∀B]` to `[sub TC B^β₁]` — there the keep-peel pays on the
  fold and the recursion runs at one-sided-enriched fold contexts).
  §1c's e-R′/R″ are NOT consumed by the runner-sided b-core; they stay
  as Qed kit.
- Conclusion packs split: the SUB pack is BARE (`∃ fold2, uniq,
  L-avoid` — nothing consumes a sub yield or pairing), the EQ pack
  keeps block-pairing (`ρn`), an interval/status-iff fact pack for its
  `ρe` extension (look-opener pairs AND the same-root flex pairs ride
  one iff-shaped promise), and the rel-or-hatch yield.
- Contexts: the two LOOK contexts need not be related at all (the
  e-look context is inert; no ctx_any is spent).  Coverage premises:
  `V ∪ ftv P ∪ ftv P' ⊆ S0`, per side.

**The hygiene premise GROWS a fold half.**  `e_extract_impl_complete`
takes, beyond scoping (`add α (ftv P ∪ ftv P') ⊆ ftvar Θ0`) and the
two coverages: the look half `{{Sh0 ↝ Sh1 ⊨ Θ0 ⊢ P ≼[α,m] P' ⤳ Ξl ⨾
𝒞l}}e` AND the fold half `{{Sh1 ↝ Sf1 ⊨ (Ξl ++ Θ0) ⊩ 𝒞l ⨾ ◇ ⤳ Ξs1 ⨾
Q1}}e`, supply-chained.  The e-fold's freshness reads the SUPPLY, so
it rigid-weakens freely (new small lemma) to the ENRICHED context
(rigid entries at `elements (Sh1 ∖ Sh0)`) and projects
(`e_solve_cstr_sound`) to the well-scoped a-fold the motive carries —
enrichment decision (a) survives in THIS form only.  The raw a-side
look is no longer a premise (project the look half).  Level 8 owes a
fold analog of transport 5 (or emits e-side folds directly from the
completeness constructions) — the "transport 4's role moves up"
already anticipated.

⭐⭐⭐ **THE EXTRACT LEVEL IS CLOSED (2026-08-16, four commits:
`ffafc83` kit, `e314bff` eq-core, `8ecd372` sub-core, `6aa230c`
assembly — all Qed, axiom-free, `make coq` green).**  What landed, in
the order it was built:

- **§2, the KIT** (prop_look_pair.v, 22 lemmas): `flex_agree_rel`
  iff-pair cons + one-sided rigid pushes; the e-side collection
  structure (pure-eq, the sub-shape `Ce ++ (at most one sub)`, the
  α-free and ◇-target collapses, the var-target inversion, and the
  TIGHT bound `ftv C ⊆ (S1 ∖ S0) ∪ ftv P ∪ ftv P'` — the interval form
  the enrichment needs); the DISJUNCTIVE e-ForallR-first; the
  var-pattern fold fixed point (build + invert, both with and without
  a terminal sub); fold structure facts; the JUNK-TARGET head
  transport; the KEEP-peel; and e-solve context equivalence with its
  rigid-weakening corollary.
- **§3, the b-CORE** — two size inductions, `bcore_eq` then
  `bcore_sub` (the eq layer never calls the sub layer, so the eq half
  stands alone and the sub half's Check row consumes it).  Both are
  RUNNER-SIDED: side 1 an arbitrary e-derivation, side 2 the runner's
  `Some`-equation.  The eq conclusion carries block pairing, the
  interval/status-iff pack for its ρe extension, and the rel-or-HATCH
  yield; the sub conclusion is BARE (`∃ fold2, uniq, L-avoid`).
  Crossings paid exactly as designed: the (FlexR/UG2-var vs runner)
  divergence by the junk transport into the hatch, the o2 crossing
  (ForallR₁ vs runner-Var₂) by rebuilding SS-ForallR around a freshly
  invoked runner Var-leaf at a RIGHT-enriched fold context, and the
  (ForallL/UGL vs runner-ForallR) diagonals by re-rooting side 1 with
  the disjunctive ForallR-first — its Var-bottom disjunct paid by the
  keep-peel at a LEFT-enriched fold context.
- **§4, the ASSEMBLY**: `e_extract_impl_complete` /
  `e_extract_run_complete`.  Enrichment decision (a) works in its
  fourth-pass form — `rigids (S1 ∖ S0)` per side, the hygienic e-fold
  rigid-weakens into it and projects by `e_solve_cstr_sound`; stage 2
  reads the b-core's fold back down to the runner's own context
  through the rigid-prefix agreement.

⚠️⚠️ **A MEASURED SPEED TRAP, new and general** (§6c): killing a
runner call by matching the GOAL'S NESTED MATCH —
`match goal with |- context [ match ?call with Some _ => _ | None => _
end ] => destruct call …` — HANGS (>200 s, killed; the `context`
selection can land on an inner stage whose type depends on an outer,
not-yet-introduced result).  prop_run_complete.v §5c's `kill_*` recipe
— match the APPLICATION with its argument metavariables, `assert (… <>
None)` first, then `destruct` that exact application — does the same
job in 0.05 s.  Use it at every level above.

⛔ **WHAT THE LEVEL OWES UPWARD** (unchanged by the closure, and now
concrete): `e_extract_*_complete` takes the look half AND the fold
half as supply-threaded e-derivations on the SAME outputs, chained
`Sh0 ↝ Sh1 ↝ Sf1`.  Transport 5 manufactures the look half from any
raw look; the FOLD half has no transport yet — building one (or
emitting e-side folds directly from the completeness constructions) is
the flagship's burden, exactly the "transport 4's role moves up"
the third pass anticipated.

### 8c.10 ⛔ THE CONSIS TRIO — the design crux, settled by inspection (2026-08-16)

Level 5's fork (rel_aenv transports vs determinism-up-to-renaming) was
to be decided by "does any rule re-read a threaded output in a
premise".  **Checked against the rules — it does**, in two places:
`e_consis__arrow` runs its SECOND premise at `Θ1`, the first premise's
OUTPUT context (def_consis.v:183), and `e_assign__assign` runs its
consistency premise at `Ξ ++ Θ0` and re-wraps the resulting `Θ1`
(:96).  So the output context is DATA that later premises read, not a
by-product — a status-only interface like `flex_agree_rel` cannot
carry it.

⚠️ And relating contexts here is strictly heavier than at the extract
level: payloads are `ptyp` (`abind_flex_mono_def τ`,
algo/def_rules.v:63), so a `rel_aenv` would need a ptyp-level
companion to `rel_pskl`, plus transports for all three judgements —
a whole new layer.

⭐⭐ **THE LEVEL-4 LESSON COLLAPSES THE FORK: go RUNNER-SIDED from the
start.**  The extract level's b-core did NOT need a free-standing
relation between two arbitrary derivations — and the attempt to state
one was FALSE (see the fourth pass).  Stating level 5 the same way —
side 1 an arbitrary e-derivation, side 2 the RUNNER'S computation —
means the motive relates the derivation's `Θ1` to the RUNNER'S output
context, which is a single relation carried through one induction, not
a transport layer that must compose with itself.  Build `rel_aenv`
only if a case genuinely needs it, and expect the same YIELD-HATCH
trick where a generative row (Assign-SolveM's `guess^TY`) makes the
two output contexts differ by invented names.

⭐ **The runner's shape is already favourable**: the trio extracts as
ONE tagged `Equations` block, `e_consis_call_impl`, over a
`consis_call` sum (def_consis_impl.v:471) — so completeness is ONE
induction over `e_consis_call_order`, mirroring levels 1–2's
order-sind template, NOT the 3-way mutual induction the original plan
assumed.  Per-priority reorder lemmas are still owed wherever the
dispatch commits (the file's own comments flag the convoyed
`Assign-UnivGhost-Id` row as the first such site).

⚠️ Carry the §6c speed trap: kill each runner call with the `kill_*`
recipe (match the APPLICATION, `assert (… <> None)`, destruct that),
never by capturing the goal's nested match.

⛔ NEXT: §8c.10 as scoped above, then sub, pat/typing, and the
flagship — per §8c.6's NEXT list.

### 8c.10b ⛔⭐ SECOND PASS — the scoped output relation is REFUTED, and the case backbone is settled (2026-08-16)

§8c.10 above left exactly one decision to the proof: the shape of the
output relation, with the recommendation "equality up to a RENAMING,
the renaming forced only by `Assign-SolveM`'s `guess^TY`".  **Settled
against real goals, and the recommendation is wrong**
(`cex/probe_consis_ghost_flex.v`, five exhibits, assumptions-closed).

**⛔ THE FINDING (machine-checked).**  At a GHOST-versus-FLEXIBLE node

    pattern ◇     subject α̂        (α̂ an UNDEFINED flexible)

both `U-GhostR` and `U-FlexL` fire — `nonflex{P0}` rules out a
flexible VARIABLE, not a hole — and their output CONTEXTS differ:

    U-GhostR    Θ0                                  (unchanged)
    U-FlexL     (α ~ def β̂) ++ (β̂ ~ flex) ++ Θ0'    (α̂ SOLVED)

because `guess^TY(◇)` invents a fresh flexible (`e_guess_mono__hole`).
**The RUNNER takes `U-GhostR`** — machine-checked by reducing
`e_consis_run` itself (`probe_consis_runner_ghostr`), not merely read
off the clause order: the consistency clause matches the PATTERN first
and its `pskl_hole` arm is unconditional in the subject
(def_consis_impl.v:759).  The mirror pair (pattern α̂, subject ◇)
diverges identically, `U-Ghost` against `U-FlexR`.

⚠️ This is the PAPER's system, not an encoding artefact: `U-FlexL` /
`U-FlexR` carry only `\nonflex{P_0}` / `\nonflex{P}`
(algorithmic.tex:757, :764) and `U-GhostR` only `Δ1 ∩ ftv(P) = ∅`
(:782); `frost/algo`'s twin is identical (def_rules.v:1127-1137).
Filed in PAPER-GAPS.

**⭐ THE CASE BACKBONE IS SETTLED** (INSPECTED, rule-by-rule against
the runner's clause list — not machine-checked; the enumeration is
what a builder should re-verify case by case as the induction is
written).  Every OTHER (pattern, subject) shape pair admits **exactly
one** consistency rule, so the runner's first-match commits to the
derivation's root everywhere else.  The complete overlap inventory:

- (◇, α̂) and (α̂, ◇) — **the genuine divergence**, above.
- (◇, ◇) — `U-Ghost` and `U-GhostR` agree on BOTH output and join.
  Benign, no lemma owed.
- inside `unifyvar`: `Flex-Flex-Id` overlaps `Flex-Flex-Skip` (at an
  undefined non-matching head) and `Flex-Flex-Assign` (at a DEFINED
  head), because neither carries `α ≠ β`.  Benign, but it owes one
  small lemma: **`α̂ ≈ᵘ α̂` returns the supply AND the context
  unchanged** — the Assign route runs a self-consistency of a
  MONOTYPE, and monotypes have no ∀/⫯/◇, so only Unit / Rigid / Arrow
  / Flex fire and none of them invents a name or moves the context.
  State it jointly with `consis P ∼ P at a ptyp_to_pskl P` and prove
  it by the trio's mutual induction.
- everything else: unique.  In particular `guarded_pskl` does NOT
  cause the level-4 hazard here, because `U-UnivGhost2` / `U-UnivGhostR`
  additionally demand `nonflex`, which excludes the flexible variable
  that made `guarded_pskl` dangerous at the look level.

**⛔ WHY IT BREAKS THE DESIGN, and it is ONLY the Arrow row.**  The
output relation is consumed in exactly ONE place: `U-Arrow`, the only
row whose premise re-reads a threaded output as another premise's
INPUT.  (Re-checked: `Assign-Assign` and `Flex-Flex-Assign` re-wrap
their single premise's output but never re-read it; the ∀ rows split
the head off theirs and have no sibling premise.  §8c.10's first pass
cited these two as evidence that the output is "data later premises
read" — that is right that a status-only interface cannot carry it,
but the CONSUMER is Arrow alone.)  So what the level owes is:

    given premise 2 derivable at the DERIVATION's Θd1,
    derive it at the RUNNER's Θr1.

The divergence is INFORMATION-FREE (α̂ solved to a fresh unconstrained
flexible, so the runner's context is strictly MORE GENERAL and can
never fail where the derivation succeeds), but it is **not a
renaming**: Θd1 has one entry more than Θr1 and binds α̂ where the
runner leaves it free.

**⛔ AND A SYNTACTIC ALIAS RELATION IS NOT CLOSED** (INFERRED — worth
a probe before anyone builds on it).  The obvious repair is a context
operation `alias α β̂ Θ` (split at α, keep the prefix verbatim, replace
`(α ~ b)` by `(α ~ def β̂) ++ (β̂ ~ b)`) and the claim
`Θd = alias α β̂ Θr`, maintained.  It survives the easy cases —
including the delicate one, `Assign-SolveM` at the alias entry, where
the Θd side does `Assign-Assign` into a consistency that re-walks the
SAME Depend block and lands on `β̂ ~ def guess(P)`, matching
`alias α β̂` of the Θr side's `α ~ def guess(P)` exactly (the
occurs-check forces `α ∉ ftv P`, so the substitution `P[α:=β̂]` is the
identity).  It **fails** when the assign's TARGET is some δ̂ ≠ α and
the pattern P DOES mention α: the Θd side takes `Assign-Assign` at the
alias entry and ends with `δ̂ ~ def guess(P[α:=β̂])`, mentioning β̂,
where the Θr side takes `Assign-Depend` and ends with
`δ̂ ~ def guess(P)`, mentioning α.  Equi-general, syntactically
different.  ⇒ the relation must be **up to RESOLUTION** — the two
contexts induce the same idempotent substitution modulo the renaming
`α ↦ β̂` — which is the `a_inc` / `msubst_*` metasubstitution order of
`algo/def_meta.v`, not a syntactic context relation.

**THE FORK, for the next session (USER DECISION).**  Both routes are
multi-session; neither is the "one induction" §8c.10 scoped.

  (A) **Reuse `algo/`'s metasubstitution layer.**  Project the Arrow
      row's premise 2 to the `a_` side (`e_consis_sound`, Qed), move it
      from Θd1 to the more general Θr1 with the `κ ∷ Θ0 ⊑ Θ` machinery,
      and lift back to `e_` by a NEW a→e transport for the trio (the
      analog of transport 5 — mechanically the same job: rename the
      generated names to avoid the supply, `Δ-drop`/`Δ-guess` both make
      `e_` the WEAKER side, so the direction is favourable).
      ⚠️ COST CHECKED: the a-side generalization is not sitting there
      ready.  `a_consis_complete` / `complete_mu`
      (`algo/consis/prop_completeness_consis.v`, ~8600 lines) is stated
      against the DECLARATIVE-in-algo layer — it takes an `ad_` join
      and two `ad_refine_*_f` premises and returns an optimality
      package — so route (A) would have to round-trip through `ad_`
      joins, not just through κ.
  (B) **Build the metasubstitution/⊑ layer directly on `e_`** and prove
      one generalization transport for the trio.  Self-contained, no
      a→e bridge and no `ad_` round trip, but duplicates machinery
      `algo/` already has.

  ⚙ A THIRD, SMALLER OPTION, if the ladder wants a rung now: the
  divergence needs a `pskl_hole` on one side, and hole-freeness is
  MAINTAINED by the entire recursion (arrow halves, ∀ openings, and —
  the point — `Assign-Assign` / `Flex-Flex-Assign` substitute `ptyp`s,
  which have no holes).  So level 5 restricted to hole-free inputs is
  exactly the originally-scoped design (one induction, output relation
  up to renaming).  That yields **`e_unify_run_complete` UNRESTRICTED**
  — a unify call's only consistency premise is on `ptyp_to_pskl`
  monotypes — and assign/consis restricted.  ⛔ It does NOT reach the
  flagship path: subtyping and typing call consistency precisely on
  ghost-carrying skeletons.

⚠️ Nothing above changes levels 1–4; they are Qed and untouched.

### 8c.10c ⭐⭐ LEVEL 5 IS CLOSED — the hole-free rung is Qed (2026-08-17)

`e_consis_call_impl_complete` and the three headlines
(`e_assign_impl_complete`, `e_unify_impl_complete`,
`e_consis_run_complete`) are Qed and assumptions-closed;
prop_consis_complete.v §6 (the motive) / §7 (the induction) / §8 (the
headlines).  ⭐ **The unify headline is UNRESTRICTED** — a `unifyvar`
call carries no skeleton and its one consistency premise runs on
`ptyp_to_pskl` payloads, so the hole-free fragment contains it outright;
assign and consistency carry `pskl_no_hole`, and §8c.10b says what
lifting that costs (THE FORK, still the user's call).

**⭐ THE MOTIVE, and the direction is the content.**  The derivation is
transported ONTO THE RUNNER'S RAILS:

```coq
    forall Sd Θd Qd, consis_call_run S0 Θ c Sd Θd Qd ->
    exists r ps,
      consis_call_answer (e_consis_call_impl c S0 Θ Hlc HD H) = Some r
      /\ (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
      /\ swaps_atoms ps Sd [=] cs_supply r
      /\ swaps_aenv ps Θd = cs_ctx r
      /\ consis_call_out_rel c (swaps_pskl ps Qd) (cs_out r)
```

⚠️ The MIRROR reading (`Θd = swaps_aenv ps (cs_ctx r)`) dies at
`U-Arrow`: transporting premise 2 along `ps1` would apply the chain a
SECOND time, and a chain is not an involution — only each transposition
is.  With the direction above `ps` composes as `ps1 ++ ps2`, and what
`ps2` must leave alone is the FIRST half's yield — which is exactly what
prop_consis.v §4's output-context bound and §7's output-skeleton bound
provide.  The side conditions (`uniq`, coverage incl. Δ1/Δ2) are §4's,
verbatim, which is what makes the soundness bridge reusable inside the
proof.

⭐ `U-Rigid` versus `U-Flex` at `(β̂, α̂)` with `α0 = β0` needs NO
uniqueness argument: whichever the derivation took, §5's `e_unify_refl`
says the answer is `(S0, Θ)`.  The motive's `uniq` premise is for the
WALKS.  Six consistency shape pairs — (1,→) (1,∀) (→,1) (→,∀) (∀,1)
(∀,→) — admit no rule and close by one `inversion`.

**⚠️⚠️ THE PERFORMANCE FINDING, and it is the reusable one.**  The first
assembly took **>20 minutes**; it now takes **12 s**, and the whole
difference was TWO `fsetdec` calls — the Assign-Assign and
Flex-Flex-Assign coverage goals, each ~8 set variables with one of them
under a `remove`.  ⚙ `clear -` did NOT help: the cliff is the GOAL's
variable count, not the context's.  What helped was spelling the
derivation out so no single `fsetdec` sees more than four variables, and
proving the two `α ∈ S0` facts WITHOUT `simpl` so that `dom Θ` and
`ftvar_in_aenv Θ` stay opaque.  ⭐⭐ **`coqc -time` is how to find such a
thing in one run**: it prints per-SENTENCE timings as it goes, so the
sentence after the last one printed is the one that hangs.  Bisecting by
admitting cases would have cost five 7-minute probes.

**⚠️ Three more mechanics traps, all measured, all live at level 6.**

1. **`simp` is the wrong tool at the consistency clause** — its recursive
   call sits at the SAME clause pattern, so `simp` unfolds that too and
   the application the kill-tactic matches is gone.  Rewrite with the
   clause's own equation: `_13` is consistency, `_1`…`_6` assign at
   nil/tvar/var_typ/var_skl/flex/def, `_7`…`_12` the unify twins.
2. **The runner's atom tests are CONVOYED**, so `destruct (x == y)` on a
   term of one's own does not always abstract the goal's occurrence.
   Destruct the GOAL's own scrutinee — and ⚠️ keep the pattern
   FIRST-ORDER where the goal is a whole clause body: matching
   `context [ match ?e with left _ => _ | right _ => _ end ]` there does
   not terminate (>800 s, measured), while the same pattern is fine on
   the small goals inside a branch.
3. **`repeat split` introduces products** (Coq's `constructor` does) and
   dives through a `forall a b, In (a,b) ps -> …` conjunct; and
   `cbn [cs_supply]` misses `proj1_sig` once a witness comes from
   `eexists`.  `split_tvar_head` at `cs_ctx r` cannot be reached by
   `rewrite` at all (its branch reads the decomposition proof) — go
   through `split_tvar_head_hit_eq` (def_dec.v).

⚙ Helpers this level added to the tree: `mono_ck_complete`,
`rigid_bound_ck_complete`, `flex_tvar_flex_bound_ck`,
`split_tvar_head_hit{,_eq}` (def_dec.v — the runners TEST what the
derivations CARRY, so every decision procedure owes both directions);
`mono_ptyp_swaps`, `swaps_abind_def`, `swaps_aenv_one_def`
(prop_solve_det.v).  ⚠️ `mono_ptyp_swap` was already in
algo/prop_swap.v:439 — grep before adding.

⛔ NEXT: THE FORK (§8c.10b (A)/(B), user decision) for the unrestricted
statement, then level 6 (e_sub) per §8c.6's NEXT list.  ⚠️ Re-run the
OVERLAP AUDIT first — that audit is what turned §8c.10 from three design
passes into one.

### 8c.11 ⭐ LEVEL 6's OVERLAP AUDIT — done, and it found ONE thing (2026-08-17)

The audit §8c.10c's NEXT list asks for, run before any level-6 proof: for
every input shape, which `e_sub` rules can fire, and which one the runner
takes.  Sources: `ext_algo/def_sub.v` (nine `e_sub` rows + seven
`e_sub_flex` rows) against `ext_algo/def_sub_impl.v:484-857` (the runner's
dispatch, which is the case list).

**⭐ THE AUDIT'S GOOD NEWS: `guarded_pskl` collapses almost everything.**
It is `unit | var | arrow` and NOTHING else (`frost/def_shapes.v:182`), so
`∀`, `◇` and `⫯` are all UNGUARDED, and five candidate overlaps that look
real on the rule list are vacuous:

| configuration | looks like | actually |
|---|---|---|
| `tc`, `ty`, `P0 = ∀B` | ForallR vs Check vs ForallL | **ForallR alone** — Check wants `guarded P0`, ForallL wants `guarded P0 ∨ P0 = ◇` |
| `tc`, `ty`, `P = ∀Q` | ForallL vs Check | **ForallL alone** — Check wants `guarded` of the SUBJECT |
| `tc`, `sk`, `P = ∀Q`, `P0 = ◇` | ForallL vs UnivGhostR | **ForallL alone** — UnivGhostR wants `guarded P` |
| `tc`, `sk`, `P = ⫯Q`, `P0 = ◇` | UnivGhostL vs UnivGhostR | **UnivGhostL alone**, same reason |
| `tc`, `sk`, `P = ◇`, `P0 = ◇` | Ghost vs UnivGhostR | **Ghost alone**, same reason |

The last one matters most: Ghost yields `P0` and UnivGhostR yields `⫯P`, so
had `◇` been guarded the level would have opened with a genuine
output divergence — §8c.10b's shape, at the sub level.  It is not.

⭐ **The whole `e_sub_flex` side is overlap-free by construction** — the
three `flex_mono` rows are separated by `γ = α` / `γ ∈ ftv P0` / neither,
which is a decision, and the other four rows are keyed to distinct binding
shapes.  `Flex-Assign` carries no `γ ≠ α` side condition and the runner
fires it unconditionally at a `def` head: they agree.  The rigid row is the
only one whose rule conditions the runner re-tests (`γ ≠ α`, `γ ∉ ftv P0`),
and it rejects on exactly those two.

**⛔ THE ONE FINDING, machine-checked: `cex/probe_sub_ghost_ti.v`.**
`SI-Ghost` has NO mode restriction — the paper writes it as an axiom over
an arbitrary `M` (full-algo-spec.tex:849) while the neighbouring
`SI-UnivGhostL` (:855) says `M ≠ TI` outright, with the comment "should not
inst when TI".  The runner dispatches on the MODE first and its `mode_ti`
arm is `SI-Infer`'s alone: counterpart `◇` or `None`
(def_sub_impl.v:509-515).  So at

    NM = SK    M = TI    P0 ≠ ◇    subject ◇

the relation derives what the runner rejects.  The probe checks both halves
at `P0 = 1`, the runner half for EVERY order proof (that arm consumes none).

⭐ **The premise this buys, and why it is not enough by itself.**  The
callers do satisfy `M = ti -> P0 = ◇`: `e_typing` calls subtyping only at
`NM = ty` (def_typing.v:66,71,76) and reaches `TI` only at `◇`
(`e_typing__freeze`, :80), and `e_pat` — the only `NM = sk` caller —
threads its own `(m; P0)` unchanged.  Under that premise the `TI` mode is
settled, because at `(TI, ◇)` both Infer and Ghost fire and return the SAME
triple `(S0, Θ0, P)`: no uniqueness argument needed, exactly as
`e_unify_refl` settled level 5's `U-Rigid`/`U-Flex` pair.

⚠️ **But the premise is not hereditary — and the right invariant is not
something to design, it is something to TRANSCRIBE.**  `SI-Arrow` concludes
at `FN M` and runs premise 2 at `M` against the counterpart's CODOMAIN, so

    NM = SK    M = FN TI    P0 = 1 → 1    subject 1 → ◇

puts the rejected configuration one level down with `P0b = 1 ≠ ◇`, and a
root-level premise is vacuous at the conclusion (`FN TI ≠ TI`).  The probe's
§3 checks this configuration's relation half.

⭐⭐ **The authors' implementation already carries the invariant in its
TYPES.**  The paper's figure indexes the judgement by `M` and `P0`
separately; the implementation fuses them into ONE datum and projects the
paper's `P0` back out (`paper/artifact/implementation/lib/type.ml:8-11` and
`:395-398`):

```ocaml
  type mode = Infer | Check of pure_type | Fun of pure_type * mode

  let rec sk_of_mode = function
    | Infer -> Ghost
    | Check p -> p
    | Fun (p, m) -> TArr (p, sk_of_mode m)
```

So `P0 = sk_of_mode M` holds by construction there: `TI` pairs with `◇` and
cannot do otherwise, and each `FN` layer pairs with one arrow of the
counterpart.  That is exactly the hereditary premise level 6 needs, and in
this encoding it is a relation rather than a function, since Coq's `mode`
carries no payload:

```coq
Fixpoint mode_counterpart (M : mode) (P0 : pskl) : Prop :=
  match M with
  | mode_ti    => P0 = pskl_hole
  | mode_tc    => True
  | mode_fn M' => exists P0a P0b,
                    P0 = pskl_arrow P0a P0b /\ mode_counterpart M' P0b
  end.
```

⚙ **And it threads, contrary to what the first pass of this section said.**
`SI-Flex-Assign` re-enters subtyping under `subst τ β P0`, which looked like
it would have to RE-ESTABLISH the invariant — a substitution can turn a
counterpart variable into an arrow.  It cannot break this one: substitution
is structural, so it maps `pskl_arrow P0a P0b` to an arrow and `pskl_hole`
to `pskl_hole`, and `mode_counterpart` only ever inspects those two
positions.  Every other recursive site is easier — `SI-Arrow` peels one
layer off both indices at once, `SI-ForallL` / `SI-UnivGhostL` /
`SI-Flex-Solve` / the four skip rows leave `(M, P0)` alone, and `SI-ForallR`
lands at `mode_tc`, where the invariant is `True`.  ⚠️ Preservation is
argued by INSPECTION here, not machine-checked; it is the first thing
level 6 should prove.

⭐ One free consequence worth noticing: under the invariant, `P0` at any
`FN` mode IS an arrow, hence `guarded`, so `SI-ForallL`'s
`guarded P0 \/ P0 = ◇` guard is automatic in function mode and a real test
only at `TC`.

⚙ Two more configurations the audit clears, both by the runner and the
relation agreeing to reject: `(tc, sk)` with a guarded subject and `P0 ≠ ◇`
(no rule at all), and `(fn, ty)` with subject `◇` or `⫯Q` (Ghost and
UnivGhostL are both `SK` rules).

⛔ NEXT, unchanged: THE FORK (§8c.10b (A)/(B)) is still the user's call, and
level 6 proper is the template of §8c.6 plus the four mechanics traps of
§8c.10c — which the audit expects to recur verbatim, since the sub runner is
the same tagged-block shape with the same convoyed atom tests.
### 8c.12 ⭐⭐ THE FORK, RESOLVED AS (B) — and the route is much cheaper than §8c.10b estimated (2026-08-17)

USER decision (2026-08-17): "at your discretion, try to build an elegant
proof."  Route **(B)** — the generalization layer native to `e_` — chosen
over (A)'s round-trip through `algo/`'s metasubstitution layer, on two
grounds: it keeps the runner-sided architecture levels 1–5 were built on,
and (A)'s cost was already checked to be a THREE-level round-trip
(`a_consis_complete` / `complete_mu`, ~8600 lines, is stated against the
`ad_` layer, so (A) must go through `ad_` joins, not just through `κ`).

⭐ **And (A) would not have bought the right statement anyway.**
`a_consis_complete` (algo/consis/prop_completeness_consis.v:8605) is
DECLARATIVE completeness — "if a `}}ad` join exists, the algorithm finds a
most-general solution".  What level 5 needs is RUNNER completeness — "if the
`e_` RELATION derives it, the RUNNER computes it".  Different statement;
(A)'s reuse was never as direct as the fork note assumed.

**⭐⭐ THE COST ESTIMATE WAS WRONG, IN OUR FAVOUR: (B) OWES NO NEW RELATION.**
§8c.10b called (B) "self-contained, duplicates machinery algo/ already has".
It does not have to duplicate any of it: `ext_algo` shares `aenv` with
`algo/`, so the paper's own information-increase `κ ∷ Θ ⊑ Θ'`
(`a_inc`, algo/def_meta.v:213) applies to a THREADED run's contexts
verbatim — and so does its metatheory.  Already Qed in the tree and
directly usable:

| fact | where | what it gives §8c.12 |
|---|---|---|
| `a_inc_compose` | prop_compose.v:778 | `κ ∷ Θ0 ⊑ Θ1` and `ζ ∷ Θ1 ⊑ Θ` give `ζ∘κ ∷ Θ0 ⊑ Θ` — **GENERAL, not identity-restricted**, which is exactly what U-Arrow's chain composes with |
| `a_inc_trans` | prop_inc.v:491 | the identity shorthand `⊴` |
| `a_isub_refl` | prop_basic.v:222 | `Θ ⊴ Θ` at a well-formed `Θ` — the reflexive base |
| `a_isub_cons_{flex,flex_def,var_typ,var_skl}` | prop_basic.v:109-166 | the four entry-extension rows |

⚠️ Grep before adding anything here — this is exactly the situation
`feedback-grep-completeness-kits-first` warns about, and the fork note's own
cost estimate is what it caught.

**⭐ FEASIBILITY, MACHINE-CHECKED: `cex/probe_inc_more_general.v`.**  At the
very configuration that refuted the first scoping, the runner's answer is
the ⊑-more-general one:

    runner      (U-GhostR)   α̂                 (untouched)
    derivation  (U-FlexL)    α̂ := β̂, β̂        (α̂ SOLVED)

and `[β̂/α̂] ∷ (α̂) ⊑ (α̂ := β̂, β̂)` holds in `a_inc` outright.  ⭐ Note the
two routes' output SKELETONS already AGREE (both `α̂` —
`cex/probe_consis_ghost_flex.v`), so only the CONTEXT slot of the motive has
to weaken; the payload slot can stay as it is.

**THE STATEMENT TO BUILD.**  Level 5's hole-free rung relates the
derivation's output to the runner's up to a fresh RENAMING `ps`.  The
unrestricted rung replaces that with an increase, in the same direction (the
derivation is still transported onto the runner's rails — §8c.10c's finding
stands, and for the same reason):

    forall Sd Θd Qd, consis_call_run S0 Θ c Sd Θd Qd ->
    exists r κ,
      consis_call_answer (e_consis_call_impl c S0 Θ …) = Some r
      /\ κ ∷ cs_ctx r ⊑ Θd                     (* runner is MORE GENERAL *)
      /\ (the payload relation, msubst'd along κ)

⭐ **Why this is the elegant form and not merely the weaker one.**  A
renaming IS an increase in both directions, so the new statement SUBSUMES
the hole-free rung rather than sitting beside it, and the `swaps`/`ps`
bookkeeping of §8c.3-§8c.10 is absorbed into `κ` — `a_inc_compose` does at
U-Arrow what the `ps1 ++ ps2` chain did, with composition already proved.
The one thing to keep from the old shape is the SUPPLY relation, which is
orthogonal to `⊑` and still needs threading.

⛔ **WHAT IS STILL OWED — this is the induction, and it is NOT started.**
The trio's ⊑-MONOTONICITY: run at a more general context, the runner still
succeeds and its output is still more general.  That is genuinely new (the
facts above are about `⊑` alone, not about `e_assign`/`e_unify`/`e_consis`),
and it is the whole of §8c.12.  Expect the level-5 shape: order-sind over
the runner's clause list, the four mechanics traps of §8c.10c, and U-Arrow
as the only row with content.  ⚙ Start by checking whether the monotonicity
premise needs `{{ ⊢ Θ }}a` — `a_inc_compose` takes well-formedness of BOTH
contexts, so the motive will have to carry it or derive it from
`prop_run_invariants.v`.
### 8c.12a ⚙ §8c.12 IN PROGRESS — the scoping is DONE and much smaller than feared; the support induction is NOT finished (2026-08-17)

⛔ **Nothing from this section is committed to the tree.**  The work in
progress is `~/frost-level6-scratch/isub-increase-wip.v`, which compiles
(`timeout 900 coqc -R . src <file>` from `mechanization/`) with `Admitted`
on the two inductions below.  ⚠️ Do not land it until both are Qed.

**⭐⭐ THE SCOPING RESULT, and it is the useful part.**  The hole-free
restriction buys EXACTLY SIX case-kills in the level-5 induction — five
`destruct Hnh1` and one `destruct Hnh0`
(prop_consis_complete.v:1824, 2006, 2112, 2209, 2292, 2402).  Reading them
against the rule set:

| cell | rules that fire | verdict |
|---|---|---|
| pattern `1` / `→` / `∀` / `⫯`, subject `◇` | `U-Ghost` alone | ⭐ UNIQUE — no `⊑` needed |
| pattern `β̂` RIGID, subject `◇` | `U-Ghost` alone (`U-FlexR` would need `β̂` flex-bound, and `e_assign_target_flex` forbids it) | ⭐ UNIQUE |
| pattern `◇`, subject not a flexible var | `U-GhostR` alone (at `(◇, ◇)` `U-Ghost` also fires, but returns the SAME triple) | ⭐ UNIQUE |
| **pattern `β̂` FLEXIBLE, subject `◇`** | `U-Ghost` vs `U-FlexR` | ⛔ divergent |
| **pattern `◇`, subject `α̂` FLEXIBLE** | `U-GhostR` vs `U-FlexL` | ⛔ divergent |

So `⊑` is needed at TWO cells, mirror images of each other, and the other
four groups are ordinary work.

**⭐⭐ AND THE TWO CELLS COLLAPSE TO ONE FACT.**  At subject `◇` the runner
takes `U-Ghost` in EVERY pattern clause, and at pattern `◇` it takes
`U-GhostR` unconditionally in the subject (def_consis_impl.v:759-763 and the
`pskl_hole` subject arm of each pattern clause, :770, :808, :938, :989,
:1056, :1134) — in both cases returning `(S0, Θ, other side)` with the
context **UNCHANGED**.  The runner never commits at a ghost row.  So the
whole `⊑` obligation is

    Θ ⊲[nil] α̂ ≔ P ⊣ Θd   ⇒   Θ ⊴ Θd

— *an assign walk only adds information*.  Not a runner-monotonicity
induction over 40 cells, as §8c.12 assumed.

**⚠️ AND THE RELATION IS `⊴`, NOT GENERAL `a_inc`.**  Pushing the same entry
on both sides is FALSE for a general `κ`: `a_inc__flex_def` demands
`τ' ≡ᵗ msubst_ptyp κ τ`, and `a_inc` permits a `κ` that solves variables the
TARGET leaves flexible (take `Θ = Θ' = (α̂)`, `κ = [1/α̂]`), so `τ` and `κτ`
need not be equivalent there.  The identity shorthand `⊴` has exactly the
right content — the paper's own "all entries of flexible variables in Θ are
preserved in Θ'" (algorithmic.tex:135) — and its congruence family already
exists: `a_isub_cons_{flex,flex_def,var_typ,var_skl}` (prop_basic.v:109-176)
and `a_isub_cons_tvar` (prop_stability.v:44).  ⭐ `cex/probe_inc_more_general.v`
proves the divergence's instance with a NON-identity `κ`; the identity one
works too and is what to use.

**WHERE TO BUILD IT.**  At the `a_` layer, in a NEW file
`frost/algo/consis/prop_consis_inc.v` (no cycle: it imports
`prop_soundness_consis` for `a_isub_strip_tvar`, `prop_stability` for
`a_isub_cons_tvar`, `prop_inc_strengthen` for
`a_assign_unify_consis_flex_preserve`; none imports it).  The `e_` side then
comes from `e_assign_unify_consis_sound` (prop_consis.v §4), whose `uniq` and
coverage hypotheses **the level-5 motive already carries**
(`consis_call_uniq` / `consis_call_cover`), so they are free at the use site.

**STATE OF THE TWO INDUCTIONS** (both `Admitted` in the scratch file):

1. `a_assign_unify_consis_lc` — the output context is locally closed.  Needed
   because `U-Arrow`'s second premise runs at the FIRST's output, so the
   increase's own induction cannot supply its `lc` side condition.  ⚙ A
   SEPARATE induction on purpose, as prop_consis.v §7 is.  **4 rows open**:
   `Assign-SolveM` and the three entry-pushing rows
   (`var_typ` / `var_skl` / `skip_other`), all of which need the payload's
   `lc_abind` rebuilt after `simpl` — the `lc_ih` tactic in the scratch is
   the thing to fix, and it regressed `SolveM` when simplified, so fix it
   without dropping the `a_decls βs` branch.
2. `a_assign_unify_consis_isub` — the increase itself, motives
   `a_suffix Ξ -> lc_aenv (Ξ ++ Θ0) -> Θ0 ⊴ Θ1` (assign) and
   `lc_aenv Θ0 -> Θ0 ⊴ Θ1` (unify / consis).  ⭐ The motive drops the block
   from the SOURCE — that is what makes almost every row a one-liner; the
   alternative `(Ξ ++ Θ0) ⊴ Θ1` forces a reordering argument at SolveM,
   Assign and the three skips.  6 rows close by `a_isub_refl_lc` alone and
   11 more by the congruence block; **the open ones are** `Assign-SolveM`
   (use `a_isub_solve_head` — already **Qed** in the scratch — over
   `a_isub_weaken_suffix` with `a_guess_mono_decls`), `Assign-Depend` (needs
   `a_isub_prepend_decls_src` plus `flex_preserve` for "the head survives"),
   `U-Arrow` (`a_isub_trans`, blocked on induction 1), and the three `∀` rows
   (`a_isub_strip_tvar`).

⚙ `a_suffix Ξ` had to join the assign motive: `Assign-SolveM` deposits the
block below the solved head and needs it to be a suffix to weaken past.  It
is `nil` at the top and `Depend` only ever extends it with a flexible.
