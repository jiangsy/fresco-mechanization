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
  - ✅ **CLOSED 2026-08-18 — see §8c.22.**  The route taken is the SECOND
    one below (a direct invariant, not the bridge composition), and it cost
    one context hypothesis instead of soundness' four premises.  The text
    that follows is kept because its analysis of the alternative, and its
    ⚙/⚠️ notes, are still the record of why.
  - ⛔ **STILL OPEN in (2b)** *(as of 2026-08-14; closed 2026-08-18)*, and
    ⭐ **the route is cheaper than this list
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

**⭐ BOTH INDUCTIONS ARE NOW Qed** — `frost/algo/consis/prop_consis_inc.v`
(commit `faadc87`, assumptions-closed, tree green 32/32, the file costs
18 s).  Three results:

| lemma | what it says |
|---|---|
| `a_assign_unify_consis_lc` | the output context is locally closed.  A SEPARATE induction on purpose, as prop_consis.v §7 is — `U-Arrow`'s second premise runs at the FIRST's output, so the increase cannot supply its own side condition |
| `a_assign_unify_consis_defs_lc` | every DEFINITION in the output is locally closed.  ⚠️ Needed because `lc_abind` sends `flex_mono_def τ` to `True` (algo/prop_inc.v:75) and so constrains no payload at all, while `a_isub_cons_flex_def` wants `lc_ptyp τ`.  ⚙ The `e_` layer gets the same content free from `e_assign_unify_consis_defs_mono` (ext_algo/prop_termination.v), whose `aenv_defs_mono` is already an INPUT of every runner call |
| **`a_assign_unify_consis_isub`** | **`Θ0 ⊴ Θ1`** — the increase itself |

⭐ Four helpers the tree did not have, all in the same file:
`a_isub_solve_head` (solving a flexible HEAD is an increase, with the
target's tail allowed to have grown — SolveM's shape),
`a_isub_weaken_suffix2`, `a_isub_strengthen_suffix_src` (the `a_decls`
version existed; `Assign-Assign` needs the `a_suffix` one, because a pending
block may already carry DEFINITIONS), and the `lc_aenv` / `aenv_defs_lc`
plumbing.

⚠️ **Two mechanics traps, both measured, both worth carrying to level 6.**

1. **An unknown constant inside a tactic fails SILENTLY.**  Half of the case
   scripts sat "unprovable" for several rounds because `a_isub_solve_head`
   had been dropped in a refactor — `apply <unknown>` inside a
   `try (now …)` just fails, and the case falls through to the next
   alternative with no diagnostic.  Same hazard the notation pass recorded
   for `match goal`.  ⚙ Check the lemma EXISTS before believing a case is
   hard.
2. **⚠️⚠️ `eapply` of a lemma with a list-valued index leaves an EVAR that a
   structural tactic then explores forever.**  `eapply
   a_isub_strengthen_suffix_src` left `a_suffix ?Ξ`, and the `a_suffix_app`
   loop ran past 900 s.  Fix: pin the index from the IH with a `match goal`
   (`IH : lc_aenv (?X ++ ?A) -> … -> (?X ++ ?A) ⊴ ?B`), then `apply` the
   strengthening at `X` explicitly.  Cost of NOT doing it: two killed runs.

⚙ **The technique that made this tractable** and should be reused at every
later level: after the mutual induction, close the easy rows with
`all: try (now …)` and then
`all: match goal with |- ?G => idtac "REMAINS:"; idtac G end` — `coqc`
prints every surviving goal, so ONE run gives the exact open-row list.  It
took the increase from 28 rows to a tracked list that shrank 22 → 13 → 11
→ 9 → 8 → 5 → 1 → 0.

⭐ **(a) AND (b) ARE NOW DONE TOO** — `frost/ext_algo/prop_consis_inc.v`
(commit `970f423`, assumptions-closed, tree green 32/32).

§2 gives the three `e_`-level increases (`e_assign_isub`, `e_unify_isub`,
`e_consis_isub`) and the one the divergent cells actually consume,
`e_assign_nil_isub` — both `U-FlexL` and `U-FlexR` call the walk with an
EMPTY pending block.  They are pure bridge composition, and their `uniq` and
coverage hypotheses are EXACTLY `consis_call_uniq` / `consis_call_cover`, so
they cost the consumer nothing.
⚠️ **`lc_aenv Θ` is a genuinely new side condition** the motive must carry:
`consis_call_lc` constrains the SKELETONS, coverage is about names, and
reflexivity of `⊴` cannot do without it (`a_inc`'s term-variable rows demand
`Θ' ⊢ A' ≡ᵗ κA`, whose base rule demands local closure).  It is the minimal
such hypothesis — every well-formed context satisfies it.  `aenv_defs_lc` is
FREE (`aenv_defs_mono` is already an input of every runner call).

§3's four inversions confirm §8c.12a's table by machine: at a hole SUBJECT
only `U-Ghost` fires unless the pattern is a variable; at a hole PATTERN only
`U-GhostR` unless the subject is; `U-UnivGhostR` is excluded throughout
because it demands a GUARDED subject and `◇` is not guarded.  The two
divergent cells come out as disjunctions whose second branch is the
assignment walk §2 measures.  ⚙ The `(◇, ◇)` overlap needs no uniqueness
argument — `U-Ghost` and `U-GhostR` return the same triple there.

⛔ **WHAT IS LEFT IS (c), THE MOTIVE — and here is its shape.**  The
existing motive fixes the derivation's context to be the runner's own `Θ`.
That cannot survive `U-Arrow` once the ghost rows diverge: the runner's
second call sits at `cs_ctx r1` while the derivation's second premise sits
at `Θd1`, and those are related by `⊴`, not by equality.  So the motive has
to quantify over the derivation's input separately:

```coq
  ... -> forall Θd0, cs_ctx-side ⊴ Θd0 ->
         forall Sd Θd Qd, consis_call_run S0 Θd0 c Sd Θd Qd ->
         exists r ps, answer = Some r /\ … /\ cs_ctx r ⊴ swaps_aenv ps Θd /\ …
```

⭐ **Why it then composes at `U-Arrow`, and why the sind already supports
it.**  §1's arrow companion quantifies the second half over ANY
relation-derived `(S1, Θ1, Q1)`, not over the runner's own output.  So
instantiate it with the RUNNER's first-half answer — legitimate because the
runner is SOUND, `consis_call_spec` being exactly that — which yields the
motive at `(cs_supply r1, cs_ctx r1)`, i.e. at the runner's actual second
call.  Feed that the derivation's premise 2 together with
`cs_ctx r1 ⊴ Θd1` from the first IH, and the chain closes by
`a_isub_trans`.  ⚙ This is the same soundness-bridge move §8c.10c already
used; what changes is only that the relation carried across is `⊴` rather
than an equality.

⚠️ **The renaming does NOT go away.**  `guess^TY` still invents names, so
`ps` stays and the two relations COMPOSE, keeping §8c.10c's direction (the
derivation is transported onto the RUNNER's rails).

⛔⛔ **CORRECTION (same day, machine-checked): the context clause is
`a_inc`, NOT `⊴`.**  The paragraph above originally wrote it as
`cs_ctx r ⊴ swaps_aenv ps Θd`.  That is TOO STRONG, and the counterexample
sits ONE `U-Arrow` away from the divergent ghost cell — i.e. it is reached by
exactly the configuration the lift exists to handle
(`cex/probe_isub_too_strong.v`).  At `Θ = (β̂)`, pattern `β̂ → β̂`, subject
`◇ → 1`:

```
  RUNNER      half 1 U-Ghost (Θ untouched), half 2 U-FlexR → SolveM
              ⇒  β̂ ≔ 1
  DERIVATION  half 1 U-FlexR → SolveM, and guess^TY(◇) invents a FRESH γ̂
              ⇒  β̂ ≔ γ̂ ; half 2 finds β̂ DEFINED, so Assign-Assign
                 substitutes and solves γ̂
              ⇒  β̂ ≔ γ̂, γ̂ ≔ 1
```

The two agree on everything the equational theory can see
(`β̂ ≡ᵗ γ̂ ≡ᵗ 1` in the derivation's context) but disagree SYNTACTICALLY on
what `β̂` is defined to be.  `a_isub` has two conjuncts and it is the second
that dies: it demands `binds α (flex_def τ) Θ -> binds α (flex_def τ) Θ'`,
and the derivation's `β̂ ≔ γ̂` is an ALIAS where the runner committed to
`β̂ ≔ 1`.  The `a_inc` half SURVIVES — `a_inc__flex_def` asks only for
`Θ' ⊢ τ' ≡ᵗ κτ`, equivalence rather than equality, and the alias chain
supplies it (the probe's §2 witness is the IDENTITY metasubstitution).

⭐ **The increase lemma is unaffected and still usable.**
`a_assign_unify_consis_isub` compares a walk's INPUT with its OUTPUT, where
there is no committed definition to contradict — the walk only adds — so its
`⊴` conclusion stands, and `⊴`'s FIRST conjunct is precisely the `a_inc` the
motive needs.

⚠️⚠️ **AND THE COST ESTIMATE ABOVE WAS TOO OPTIMISTIC.**  "Mechanical for ~38
of 40 cells" assumed the runner and the derivation still take the SAME rule
everywhere but the two ghost cells.  Once the motive lets the derivation run
at a more informative context, that is false: flexibility is read off the
CONTEXT, so wherever the derivation's context has a flexible SOLVED that the
runner's leaves open, the derivation takes `Assign-Assign` where the runner
takes `Assign-SolveM` — a different rule, at every flexible-sensitive row.
The probe above is exactly that situation.  ⇒ Budget (c) as a genuine
induction with content in the flexible rows, not as a mechanical rewrite.

⚙ One factoring worth weighing before starting: instead of generalizing the
motive, prove `⊑`-MONOTONICITY OF THE RELATION as a separate lemma
(`Θr ⊑ Θd` and a derivation at `Θd` give a derivation at `Θr` with a
`⊑`-below output), then transport the derivation's second premise DOWN onto
the runner's context at `U-Arrow` and keep the same-context motive.  That
puts all the rule-switching content in one relation-only induction (28 rows,
no runner) instead of spreading it through the runner's 40 cells.  ⚠️ Not yet
checked for truth — the flexibility-sensitive rows are where it would fail
too, so probe it before building.

### 8c.12b ⚙ TWO SCOUTING RESULTS FOR (c) — one dead end, one primitive (2026-08-17)

**⛔ THE OPTIMALITY LEAD IS A DEAD END, and it is worth knowing why.**
§8c.12a floated reusing `a_consis_complete`'s optimality conjunct
(`ζ ∷ Θ1 ⊑ Θ` — the algorithm's output factors any competing solution)
instead of rebuilding the context clause.  The pieces really do fit:
`a_consis_sound` (consis/prop_soundness_consis.v:5163) concludes exactly
what `a_consis_complete` (consis/prop_completeness_consis.v:8605) consumes —
a `}}ad` join plus the two refinements — at `κ = identity` and `Θ` := the
derivation's own output.  So the composition is available.

⚠️ But its conclusion is `exists P1 Θ1, a_consis … P1 Θ1 /\ …`: the
derivation is EXISTENTIALLY QUANTIFIED.  It says *some* algorithmic
derivation is optimal, not that *the runner's* answer is.  Connecting the two
is exactly what level 5 proves, so the lead is circular.  ⇒ Do not spend time
on it; (c) needs its own induction.

⚙ **THE PRIMITIVE THE MOTIVE WILL NEED IS ALREADY THERE.**  The motive mixes
a renaming with an increase (`cs_ctx r ⊑ swaps_aenv ps Θd`), so it needs
`a_inc` to be equivariant.  `a_inc_kswap` (algo/prop_swap.v:2260) is the
SINGLE-swap, SOURCE-only transport:

```coq
  ζ ∷ Θ1 ⊑ Θ -> a <> b -> {{ ⊢ Θ1 }}a ->
  b `notin` ftvar_in_aenv Θ1 ->
  (forall bd, binds a bd Θ1 -> bd = abind_flex_mono
                            \/ exists τ, bd = abind_flex_mono_def τ) ->
  (kswap_msubst a b ζ) ∷ (swap_aenv a b Θ1) ⊑ Θ
```

and `kswap_msubst` is the matching action on metasubstitutions.
prop_consis_complete.v §3 already shows how to iterate a single swap into a
CHAIN (`swaps_*`), so the chain version is a mechanical lift of that pattern.
⚠️ Which DIRECTION is needed — source-side as above, or a target-side twin —
cannot be pinned until the induction is written, so do not build it
speculatively; write the `U-Arrow` case first and let it say.

⛔ **STATE.**  (a) and (b) are Qed and in the tree; (c) is designed, its
relation is settled as `a_inc` (§8c.12a's correction), its cost is understood
(a real induction, content in the flexible rows), and its two scouting
questions are answered.  Nothing of (c) is started, and nothing partial is
committed.

### 8c.12c ⛔ (c)'s DESIGN HAS A THIRD OBSTRUCTION — `a_inc` IS HEAD-BLIND (2026-08-17)

**Machine-checked: `cex/probe_inc_head_blind.v`.**  §8c.12a settled the
motive as "the derivation runs at some `Θd` with `κ ∷ Θ ⊑ Θd`" and checked
that `U-Arrow` closes under that reading.  It did NOT check the ASSIGN
component, and that is where the reading breaks.

The assignment judgement dispatches on the CONTEXT'S HEAD — `Assign-SolveM`
when the head IS the flexible target, `Assign-Assign` when it is another
DEFINED flexible, `Assign-Skip`/`Depend`/`SkipRigid` otherwise.  `a_inc`
constrains none of that.  The probe exhibits

    Θ  = α̂                     Θd = β̂ ≔ 1, α̂

with `id ∷ Θ ⊑ Θd` — an entirely new defined flexible pushed ON TOP, and the
increase still holds at the IDENTITY.  So the runner at `Θ` fires
`Assign-SolveM` at once while the derivation at `Θd` must first step past
`β̂ ≔ 1` by `Assign-Assign`.  ⇒ From `κ ∷ Θ ⊑ Θd` one may conclude neither
that the two walks take the same RULE nor that they take the same NUMBER of
steps, and a runner-sided induction consumes exactly one runner step per
case, so the derivation's extra steps have nowhere to go.

⚠️ **And this also sinks the alternative factoring of §8c.12b.**  Runner
MONOTONICITY ("the runner's answer at `Θ` is `⊑`-below its answer at any
`⊑`-larger `Θd`") reads the head of `Θd` for its own dispatch, so it meets
the identical problem.  Both routes recorded so far are blocked by the same
fact.

⭐ **WHAT WOULD WORK — a STRUCTURAL refinement, and it is the next design
pass.**  Replace bare `a_inc` in the motive by a relation that DOES
determine the head, e.g.

```coq
Inductive ctx_ref : aenv -> aenv -> Prop :=
| ctx_ref__nil    : ctx_ref nil nil
| ctx_ref__same   : forall a b Θr Θd, ctx_ref Θr Θd ->
                      ctx_ref ((a ~ b) ++ Θr) ((a ~ b) ++ Θd)
| ctx_ref__solve  : forall a τ Θr Θd, ctx_ref Θr Θd ->      (* solved IN PLACE *)
                      ctx_ref ((a ~ abind_flex_mono) ++ Θr)
                              ((a ~ abind_flex_mono_def τ) ++ Θd)
| ctx_ref__insert : forall a b Θr Θd, a_suffix_binding b -> ctx_ref Θr Θd ->
                      ctx_ref Θr ((a ~ b) ++ Θd).           (* fresh, right only *)
```

`__solve` is what a divergent ghost cell produces and `__insert` is what
`guess^TY(◇)`'s fresh flexible adds.  Then (c) needs, beside the motive:

1. `ctx_ref` implies `a_inc` (so §8c.12's landed increase still plugs in);
2. an ABSORPTION lemma — a walk at `Θd` whose head is an `__insert`ed entry
   reduces to a walk at `Θd`'s tail — proved by induction on `ctx_ref`, NOT
   on the runner's order, which is what makes the extra derivation steps
   affordable;
3. the ghost cells produce `ctx_ref`, not merely `a_inc`.

⛔ **HONEST STATE.**  (c) is NOT close.  Three designs have now been tried
and each was refuted by a machine-checked probe — the renaming form
(§8c.10b), the `⊴` form (`cex/probe_isub_too_strong.v`), and now the bare
`a_inc` form.  What survives is the list above, and it is a fresh design pass
plus at least two new inductions.  ⚙ None of this disturbs what is landed:
the increase, its `e_` face and the ghost-row inversions are all statements
at a SINGLE context and are unaffected by how the two-context relation is
eventually chosen.

### 8c.12d ⛔ THE `ctx_ref` SKETCH IS REFUTED TOO — the walk MIGRATES (2026-08-17)

**Machine-checked: `cex/probe_assign_migrates.v`.**  §8c.12c proposed
replacing bare `a_inc` by a POSITIONAL structural refinement (same entry /
solved in place / fresh insert).  All three rows walk the two contexts in
lockstep, and the assignment walk does not respect positions:
`Assign-Depend` moves a flexible the payload MENTIONS into the pending
block, and `Assign-SolveM` deposits that block BELOW the solved target.

```
    input   β̂, α̂        walk:  α̂ ≔ β̂
    output  α̂ ≔ β̂, β̂    — the two entries have SWAPPED
```

⚙ The migration is forced by well-formedness (the deposited definition
mentions `β̂`), and it is the same phenomenon PAPER-GAPS records under "flex
migration below term binders defeats the factoring" — which is why the
paper's own information increase is non-positional.

⇒ **FOUR designs, four machine-checked refutations.**  The problem is now
stated as a constraint system, with C4 (head-determining) pulling against C5
(migration-tolerant), in the dedicated self-contained hand-off
[`HANDOFF-close-consis-unrestricted.md`](HANDOFF-close-consis-unrestricted.md).
**Continue there, not here.**

### 8c.13 ⛔⛔ LEVEL 6 IS BLOCKED ON A MISSING DISPATCH GUARD IN THE COLLECTION — machine-checked (2026-08-17)

**The level-5 motive does not mirror.**  Level 5 relates the derivation's
outputs to the runner's UP TO A SWAP CHAIN, with the supply conjunct
`swaps_atoms ps Sd [=] cs_supply r`.  At level 6 that conjunct is **FALSE**,
and the witness is `cex/probe_extract_supply_drift.v`
(`e_extract_det_false`, Qed, assumptions-closed):

    Θ = ·      α ∈ S0      subject  1      counterpart  ∀_. 1      NM = SK

    LS-Absent    α ∉ ftv(1): collects nothing, spends nothing   (S0 ↝ S0)
    LS-ForallR   peels the counterpart at a DRAWN opener β,
                 then LS-Absent                                 (S0 ↝ S0 ∪ {β})

Both emit `Ξ = ·` and `𝒞 = ·`, so the fold is empty, the yield is the
accumulator `◇` on both sides and the guess is the identity at `SK`.  The two
`e_extract` derivations therefore agree on their BLOCK and their
INSTANTIATION and differ only in how much supply they spent — by one atom.
A chain whose pairs dodge `S0` fixes `S0` exactly (`swaps_atoms_notin`), so no
renaming relates the two output supplies.

⚠️ The further claim — that the drift REACHES `e_sub` through `SI-ForallL`,
so the level-6 motive itself is false — is argued by inspection in that
file's closing note (`NM = TY`, `M = FN TC`, `P0 = 1 → ∀_.1`, subject
`∀β. (1 → 1)`: the same two routes reappear one arrow down, and `P0` is an
arrow so `SI-ForallL`'s `guarded P0 ∨ P0 = ◇` guard is satisfied).  Writing
that end-to-end probe is the first thing to do on resuming.

**⭐⭐ THE DIAGNOSIS IS §8c.12's, ONE LAYER DOWN.**  The reference
implementation tests ABSENCE FIRST (`type.ml`'s `constr_collect_sub`,
:649-701), and so does this tree's runner: every non-Absent clause of
`e_looksub_impl` / `e_lookeq_impl` sits behind `mem α (ftvar_in_pskl P)`
(`def_look_impl.v:360, 377, 393, 406, …`).  A relational encoding has no match
order, so that exclusion must be a PREMISE — and `LS-ForallR` and its
neighbours carry none.  Identical species to `U-FlexL`/`U-FlexR`'s missing
`≠ ◇` (`0829607`) and `SI-Ghost`'s missing `M ≠ TI` (`35a13b3`), and the same
one-line-per-rule fix is indicated:

- add `α ∈ ftvar_in_pskl P` to every `a_looksub` / `a_lookeq` row except
  `LS-Absent` / `LE-Absent` (and to their `e_` twins), and
- add the mirror exclusion for `LS-Vacuous` / `LE-Vacuous` (counterpart `◇`),
  which the runner tests second.

⚠️ Budget one build-iterate loop per rule changed: adding a premise shifts
every `intros` pattern in every induction over the collection, and P6's
`look/` chain is the tree's biggest consumer.  Both encodings need it, plus a
`[paper-gap]` comment and a `docs/PAPER-GAPS.md` entry.

**WHAT LANDED ANYWAY, and it is motive-independent** — `frost/ext_algo/prop_sub_complete.v`:

| § | content |
|---|---|
| §1 | the strong-induction principle for `e_sub_call_order` (premises DOUBLED, prop_consis_complete.v §1's idiom) |
| §3 | `e_sub_swaps` / `e_sub_flex_swaps` (chains) and `a_suffix_swaps` |
| §4 | ⭐ THE ROOT INVERSIONS — §8c.11's overlap table as sixteen lemmas, every one a SINGLE rule: `guarded_pskl` is `unit \| var \| arrow` and nothing else, so the ∀/◇/⫯ overlaps the rule list suggests are all vacuous, and the four cells where the runner returns `None` come out as `False` |

and the whole RENAMING KIT it rests on (`b9daaa8`): equivariance and supply
respect for `e_looksub`/`e_lookeq`, `e_solve_sub`/`e_solve_eq`/`e_solve_cstr`,
`e_guess`, `e_extract` and `e_sub`/`e_sub_flex` — none of which existed, and
all of which the level needs whatever the motive ends up being.

⚙ **THE REPAIR WAS ATTEMPTED AND MEASURED (2026-08-17), then reverted.**  The
guard was carried through both encodings far enough to be decisive; the
measurement and the two lemmas it produced are in `docs/PAPER-GAPS.md` under
this entry.  Headline: **no semantic obstruction** — the guard threads through
openings and substitutions, and where a leaking row can no longer fire the
`LS-Absent` row gives the same block and collection, so the replacement answer
is the empty one.  The cost is BREADTH (~70 constructor sites / ~170 case
labels over twelve files; five files if scoped to `ext_algo/`, of which
`def_look.v`, `prop_look.v` and `prop_solve_rel.v` reached green and only
`prop_look_pair.v`'s b-core is left — and its breakage is the shifted
`pose proof`-without-`as` names, not the guard).  ⭐ Two lemmas worth
re-writing verbatim when it is redone: `e_looksub_lookeq_absent_pins` (at an
α-free subject the collection returns `Ξ = ·`, `𝒞 = ·` AND the supply
unchanged — hypothesis-free, and FALSE without the guard) and
`rel_e_absent_{sub,eq}` (the empty answer for `a_looksub_lookeq_rel_e`, which
is where the a-side's un-guarded rules meet the e-side's guarded ones).

### 8c.14 ⭐⭐⭐ THE ABSENCE-FIRST GUARD IS LANDED ON BOTH ENCODINGS — and the level-6 gate is machine-checked (2026-08-17/18)

**What §8c.13 left open is now closed at its first two steps, and the third is
scoped exactly.**

**⭐ THE GATE (`eabf308`).**  §8c.13's diagnosis had one step argued by
INSPECTION: that the collection's supply drift REACHES `e_sub` through
`SI-ForallL`.  It is now `e_sub_det_false`, Qed and assumptions-closed.  The
configuration is tuned so that EVERYTHING BELOW THE FORK IS FREE, which is why
no counting argument is needed:

    NM = SK    M = FN TC    P0 = 1 → ∀_.1    subject ∀_. (◇ → ◇)

`SI-ForallL` applies (`M ≠ TI`, `P0` an arrow hence guarded) and runs
`extract` at the α-FREE subject `◇ → ◇`; at `NM = SK` the guess is the
IDENTITY, so the block is `·` and `P1 = ◇`; and the tail is two AXIOMS —
`SI-Arrow` splits into `C-Ghost` (`◇ ∼ 1`) and `SI-Ghost` (`◇ ⩽ ∀_.1`).
⚙ It needs `swaps_atoms_add` (prop_solve_det.v §2, three lines, new): peel the
`add`, fix the base with `swaps_atoms_notin`, and the chain is forced to
identify the drawn opener with the drawn peeler.

**⭐⭐ THE GUARD, ON BOTH ENCODINGS (`3f371c2`, `caf096c`).**  The five leaking
rows of `a_looksub`/`a_lookeq` AND `e_looksub`/`e_lookeq` carry
`α ∈ ftvar_in_pskl <subject>`.  `make coq` rc=0, README 32/32.

⭐ **THE MOVE THAT MADE THE a-SIDE CHEAP, and it is the reusable lesson:
THE GUARD IS ADMISSIBLE.**  `prop_looksub.v` §2b gives five lemmas
(`a_looksub_forall_r_adm`, …) reinstating each rule in its PRE-GUARD form by
the one case split the guard introduces — at an α-free subject the opener is
fresh for α, so the premise collected NOTHING
(`a_looksub_lookeq_absent_nil`) and LS/LE-Absent gives the very same answer.
So the premise rejects no ANSWER, only a wasteful DERIVATION of it, and every
CONSTRUCTION site swaps a constructor for a lemma of the same name.  **P6 cost
eleven one-word substitutions**, against an estimate of a re-opened
completeness chain.  ⚙ Where the guard IS available the sites take it
directly; its two structural transports are named once in `algo/prop_basic.v`
(`ftvar_in_pskl_subst_keep` / `_reflect`, `ftvar_in_pskl_open_keep`).

⭐ And **transport 5 SIMPLIFIED AWAY**: `rel_e_absent_{sub,eq}` plus five
`sumbool` splits — the whole price of the one-sided design — are deleted,
because `a_looksub_lookeq_rel_e` now hands the a-side's own premise to the
e-side rule through `rel_pskl_in_id`.

**⛔⛔ WHAT IS STILL OWED, AND WHY IT IS NOT ANOTHER `caf096c`.**
`e_extract_det` is STILL FALSE after this guard —
`cex/probe_vacuous_supply_drift.v`, Qed:

    Θ = ·   α ∈ S0   subject ∀_. α   counterpart ◇

The binder is VACUOUS over the looked-for variable, so the absence-first guard
is SATISFIED; LS-Vacuous spends nothing, LS-ForallL peels at a drawn opener,
and both answer `·  ⨾ ·`.  The runner tests VACUOUS second — every `pskl_hole`
counterpart answers before the α-membership test is reached — and that test is
still not on the rules.

⚠️ **THE ADMISSIBILITY TRICK DOES NOT EXTEND**, and that is machine-checked in
the same file (§3–§4).  At (subject `α`, counterpart `◇`) LS-Var and
LS-Vacuous emit DIFFERENT collections (`[≼m ◇]` vs `·`), so the a-side's
ForallL-over-Var derivation at `(∀_. α, ◇)` has NO guarded counterpart with
the same answer — `rel_a_cstrs` is a `Forall2` and the lists differ in LENGTH.
The remaining guards therefore SHRINK the relation for real, which also means
they must be two-sided (a one-sided ◇-guard breaks transport 5 outright).

**THE REMAINING GUARD SET, read off the runner's dispatch
(`def_look_impl.v`) — this is the audit, do not redo it.**  Subject first,
then counterpart, then mode:

| subject | counterpart | mode | runner takes | relation owes |
|---|---|---|---|---|
| `var_f α` | any | any | LS-Var | `LS-Vacuous` needs `P ≠ α`; `LS-ForallR` needs `A ≠ α` |
| `arrow` / `∀Q` / `⫯Q` | `◇` | any | LS-Vacuous | `LS-ForallL`, `LS-UnivGhostL` need `P' ≠ ◇` |
| `∀Q` | `∀B` | tc | ghost-free `B` ? ForallR : ForallL | `LS-ForallL` needs "ForallR does not apply" |
| `⫯Q` | `∀B` | tc | ghost-free `B` ? ForallR : UnivGhostL | `LS-UnivGhostL` needs the same |
| everything else | | | — | already single-rule (audited) |

⛔ **THE ONE HARD OBSTRUCTION, and it bites at the ◇ guard, not only at the
ForallR one.**  `alpha_stack_looksub` (`algo/sub/look/prop_sub_cstr.v:373`) is
stated `forall Θ m P0` — **including `P0 = ◇`** — and claims the α-stack
collects `[≼m P0]` undescended.  Under `P' ≠ ◇` the stack cannot be peeled at
a ghost target, so the lemma becomes FALSE there, not merely unproved.  Lemma
E.17's `Sub-ForallR` stack branch must be redone against a PEELED target
before the ◇ guard can land.  **That is the next unit of work**, and it is
self-contained.

⚙ Order to execute in: (1) restate/re-prove `alpha_stack_looksub` at a peeled
target and repair E.17's `Sub-ForallR` branch; (2) land `P' ≠ ◇` on
`LS-ForallL`/`LS-UnivGhostL` and `P ≠ α` on `LS-Vacuous`/`LS-ForallR`, both
encodings; (3) land the ForallR-priority split; (4) `e_extract_det` is then a
direct induction and level 6 is level 5's shape verbatim (§8c.13's plan, §6/§7
of `prop_sub_complete.v`, whose §1/§3/§4 are already Qed).

### 8c.15 ✅ GUARD 3, THE ForallR-PRIORITY SPLIT — LANDED, AND THE TREE IS GREEN (2026-08-18)

`make coq` rc=0, `README.v` 32/32, zero `Admitted`/`Axiom`.  The guard is on
both encodings, P6-Ss included, and `cex/cex_looksub_not_det.v` is deleted
(retracted by it — `docs/PAPER-GAPS.md`).

#### A. The guard

```coq
(* frost/def_shapes.v *)
Definition forall_r_off (m : mode) (P' : pskl) : Prop :=
  forall B, P' = pskl_all_syn B -> m = mode_tc ->
    ~ pskl_ghost_free (pskl_all_syn B).
```

"`LS-ForallR` does not apply at this counterpart and mode" — the row fires
exactly at a GHOST-FREE `∀` counterpart in CHECK mode, and
`constr_collect_sub` commits it at type.ml:663 before `ForallL` (:680) and
`UnivGhostL` (:690).  It sits on `a_looksub__forall_l`,
`a_looksub__univ_ghost_l` and their `e_` twins — four rule sites, two
encodings — and on nothing else.

⭐ **`a_lookeq` owes NOTHING**, and that is checked: `e_lookeq_impl`'s dispatch
is already syntax-directed on the (subject, counterpart) SHAPE PAIR, and the
two rows that look like overlaps demand a `guarded` side, which no `∀` is.

⚠️ **NOT admissible**, unlike the absence-first guard: the two rows genuinely
disagree, which is what `cex_looksub_not_det.v` exhibited.

#### B. ⭐⭐ IT REMOVES WORK — THREE REPAIR LEMMAS COLLAPSE

All three existed only to repair the priority the rules did not state:

| lemma | what died |
|---|---|
| `a_looksub_open_target_at_size` (`deco_algo/prop_decorate_sub.v`) | its `LS-ForallL` branch re-freshened a colliding binder — the ONLY reason the lemma was an induction on the SOURCE'S SIZE |
| `a_looksub_forall_r_first` (`ext_algo/prop_run_complete.v`) | the re-rooting itself: four rebindings + two `a_looksub_ctx_exchange` steps |
| `e_looksub_open_forall_l_first` (`ext_algo/prop_look_pair.v`) | the same, e-side, with a SUPPLY exchange on top |

Read forwards: **the guard is the statement those three lemmas were proving.**
⛔ And `alpha_stack_looksub` is RETIRED — "an α-stack collects the whole target
undescended" is FALSE under the guard at exactly the cell its one consumer sat
in.

#### C. The kit

| where | what |
|---|---|
| `frost/def_shapes.v` | `forall_r_off` + `_nontc` / `_nonall` / `_ghosty` — the three ways a ForallL / UnivGhostL branch is reached |
| `frost/prop_basic.v` | `pskl_ghost_free_dec`, `pskl_ghost_free_subst_inv`, `forall_r_off_subst_var`, `forall_r_off_open_var` |
| `frost/algo/prop_basic.v` | `open_var_eq_var_inv` |
| `frost/algo/prop_swap.v` | `forall_r_off_swap` |
| `frost/ext_algo/def_dec.v` | `forall_r_off_ck`; `ghost_free_ck_complete` MOVED here from `prop_dec.v`, which is DOWNSTREAM of `def_look_impl.v` |
| `frost/ext_algo/prop_solve_rel.v` | `rel_pskl_all_syn_r_inv`, `rel_pskl_forall_r_off` |
| `frost/algo/sub/prop_looksub.v` §2c | ⭐ `a_looksub_var_subject_inv`, `a_looksub_open_target` |
| `frost/algo/sub/look/prop_eq_cstr.v` | ⭐ `a_solve_sub_open_target`(`_avoid`), `a_solve_sub_ctx_exchange`, `a_solve_cstr_sub_single_inv`, `binds_tvar_exchange`, and THE REORDER — `a_looksub_solve_forall_l` / `_univ_ghost_l` and their `_mode` wrappers |

⛔ `forall_r_off_subst` at an ARBITRARY substitute is FALSE (`P' = γ` satisfies
the guard vacuously, `P'[∀_.1/γ]` does not).  Only the VARIABLE form is true,
and it is the only one the tree needs.

#### D. ⭐⭐⭐ THE REPAIR OF P6-Ss, in one idea

**Where `LS-ForallL` is blocked, PEEL THE COUNTERPART FIRST and carry the SOLVE
across the peel.**

1. **The collection peel is an INVERSION.**  Under the guard, a collection at a
   ghost-free `∀` counterpart in check mode has only THREE possible roots —
   `LS-Var`, `LS-Absent`, `LS-ForallR` — because `LS-Check` wants a `guarded`
   counterpart, `LS-Vacuous` a ghost one, and the two left rows are what the
   guard forbids.  `a_looksub_open_target` hands the rule's OWN binder back, so
   `Ξ` and `𝒞` come through ON THE NOSE.
2. **The solve peel is the mirror.**  At the same cell only `SS-Var`,
   `SS-ForallL`, `SS-UnivGhostL`, `SS-ForallR` survive; the two left rows
   recurse and need a context exchange, which is free because the solve reads
   its context only for FLEXIBILITY and freshness.
3. ⭐ **THE BINDER MISMATCH, and how it dissolves.**  The collected constraint
   NAMES the peeled counterpart, so both peels must use THE SAME atom — and at
   the α-STACK leaf the collection's opener is free while the solve's is FORCED
   (`SS-ForallR` leaks its binder into the output `Pa`).  The forced one can be
   SWAPPED, because the two side conditions the swap needs are consequences of
   the run itself:

   - `γ0 ∉ dom Ξ` — junk-freeness, since the premise ran at `(γ0 ~ tvar) ++ Θ`
     (`a_solve_sub_eq_generated_fresh_set`);
   - `γ0 ∉ ftv Pa` — the output is scoped by the block and the context
     (`a_wf_pskl_ftv_dom` at the use site), and `γ0` dodges both.

   That is `a_solve_sub_open_target_avoid`, and it is the whole crux.
4. **One peel is not enough** (the peeled counterpart can be a ghost-free `∀`
   again), so the reorder is an induction on the counterpart's SIZE.
5. **The α-stack cell.**  `𝒞` moves in exactly one place, and the reorder
   reports it by returning `Q = α`, which is what lets the rows REBUILD the
   stack (`ast_all` at a VACUOUS binder) rather than inherit it.  The disjunct
   weakens from "`𝒞` is the sub-constraint at `P0`" to "`𝒞` is SOME singleton
   sub-constraint".
6. **The `Sub-ForallR` α-stack branch splits on the STACK'S OWN HEAD**: at the
   bare variable `LS-ForallR` is barred (its ◇-dispatch guard is `A ≠ α`), so
   `LS-Var` still answers at the undescended counterpart and the solve is
   lifted by `SS-ForallR` — the branch as it always was; at a `∀`- or
   `⫯`-headed stack `LS-ForallR` is the only row, it lifts the IH's collection
   with `𝒞` kept, and the branch collapses into the LEFT branch's own moves.
   ⭐ `a_looksub_var_subject_inv` — at the looked-for variable only `LS-Var`
   fires — is what tells the two halves apart, and it is the ◇-dispatch guard
   paying a third time.

#### E. ⛔ Refuted routes — do not retry

- **A one-sided guard** (e-side only): `cb067e8` §4 — `rel_a_cstrs` is a
  `Forall2` and the lists differ in LENGTH.
- **`forall_r_off M P0` as a premise of `a_looksub_solve_complete_gen`**: dies
  at the `Sub-Arrow` row, whose codomain can be a ghost-free `∀` at `TC`.
- **Reading it off `SI-ForallL`'s own `guarded{P_0} ∨ P_0 = ◇`**: that
  constrains the TOP-LEVEL collection call only; the induction descends under
  `Sub-ForallR` where the counterpart IS a `∀`.
- **`forall_r_off_subst` at an arbitrary substitute**: FALSE (§C).

#### F. ⚠️⚠️ TRAPS PAID

- **An Equations obligation the tactic cannot close is DEFERRED, not
  reported.**  The command prints nothing, defines nothing, and the only
  symptom is `The reference … was not found` at the NEXT command.  To see it,
  truncate the file right after the `Equations` block — Coq then says
  `Unsolved obligations when closing file`, and `Next Obligation. Show. Abort.`
  prints the goal.  ~40 minutes.
- **A guard that is a `Definition` unfolding to a product must be discharged
  BEFORE the obligation tactic's `intros`**, which would strip the shape its
  discharge lemmas match on.  The runner's tactic opens with
  `try forall_r_off_tac`.
- **`{A} + {B}` does not parse in this tree** — the notation layer claims `+`
  at term level 50.  Write `sumbool A B`.
- **`Set Implicit Arguments` leaves a NON-STRICT binder explicit** (one that
  occurs only under `open_pskl_wrt_pskl`), so a positional application of the
  reorder lemmas fails.  Drive them with `edestruct` + a bracket list.

#### G. What is next — `e_extract_det`, and what it actually costs

The level-6 chain is unblocked: with the collection syntax-directed,
`e_extract_det` is TRUE.  ⚠️ But "a direct induction" (the estimate in §8c.14)
is optimistic — `e_extract` is one rule composing look → solve → guess
(`ext_algo/def_extract.v`), so its determinism needs the three factors, and
**only two of them exist**:

| factor | where | status |
|---|---|---|
| `a_guess_mono_det` | `ext_algo/prop_solve_det.v` §3 | ✅ Qed |
| `a_solve_eq_det` | `ext_algo/prop_solve_det.v` §4 | ✅ Qed |
| `a_solve_sub_det` / `a_solve_cstr_det` | — | ⛔ MISSING |
| `a_looksub_lookeq_det` | — | ⛔ MISSING, and it is what the guard just made TRUE |

`prop_solve_det.v`'s §3/§4 are the template: `_det_n` on a size, then the
`_det` wrapper, with `swaps_*` chains and the `flex_pairs` kit that is already
there.  ⚠️ **AND BE PRECISE ABOUT WHAT THE GUARDS BOUGHT.**  They do NOT make the
collection literally single-rule at every cell — they remove the overlaps whose
two rows DISAGREE.  One family of overlaps survives and is harmless: at an
α-FREE subject, `LS-Absent` still races the rows that do not carry guard 1
(`LS-Arrow`, `LS-Check`, `LS-UnivGhostL`), and there the two answers COINCIDE,
because the premises of those rows are α-free too and collect nothing
(`a_looksub_lookeq_absent_nil`, `algo/sub/prop_looksub.v`).  So `_det`'s case
analysis is: single-rule wherever the answer could differ, and
`a_looksub_lookeq_absent_nil` at the α-free races.  `prop_sub_complete.v` §4's
sixteen root inversions are the audit of the first half.

The statement to lift is preserved in git at **`eabf308`**,
`cex/probe_extract_supply_drift.v` §2 (`Definition e_extract_det : Prop`).
⚙ It is stated on the `e_` (supply-threaded) judgement, so the `a_`-level
determinism above has to be composed with `e_extract_supply_respect` and
`e_extract_swap` (`ext_algo/prop_extract.v`), both already Qed.

After that: §6/§7 of `frost/ext_algo/prop_sub_complete.v` (§8c.13's recipe;
§1/§3/§4 are already Qed), then §8's three headlines.

### 8c.16 ✅ GUARD 4, THE FlexR-PRIORITY SPLIT — LANDED, AND THE TREE IS GREEN (2026-08-18)

✅ **`make coq` rc=0, `README.v` 32/32, zero `Admitted`.**  `LE-UnivGhost2`
carries `flex_r_off Θ P'` and `LE-FlexR` carries the HAT it was missing
(`a_flex_tvar Θ β`), on both encodings and in the runner.  ⭐ **AND IT FIXED A
MECH BUG**: pre-guard the runner invented a fresh flexible at a RIGID-variable
counterpart, where the paper strips the ⫯.

⚙ What the landing cost, in one line each: the collection's context lemmas
gained a COUNTERPART-SCOPED flex-agreement; the P6 flex-P0 block was FACTORED
out of the induction (454 lines, no IH, subject-generic); the
decoration-soundness proof's shrink-to-`·` became `flex_restrict`; and the
b-core gained five threaded premises and lost one branch that only existed
because of the unguarded cell.

---

**The record of why the guard was needed.**
`e_extract_det` was **false after the three earlier guards**, and the
witness is `cex/probe_extract_flexr_ug2_drift.v` (`e_extract_det_false`, Qed,
assumptions-closed).  §8c.15 G's plan — "compose the three factors" — is
sound as far as it goes, but its first factor does not exist yet, because the
COLLECTION is still ambiguous at one cell.

#### A. The cell, and it is `probe_bcore_ug2_flexr.v`'s, one level up

`guarded_pskl` is `unit | var | arrow` (frost/def_shapes.v), so a VARIABLE is
guarded.  At

    ⫯Q   ∼[α]   β          (α ∈ ftv Q,  the subject is not α)

both rows fire and their answers are of different KINDS:

| row | Ξ | 𝒞 | supply |
|---|---|---|---|
| `LE-FlexR` | `α̂1 ~ flex` | `[ ≐ α̂1 ]` | `S ↝ add α̂1 S` |
| `LE-UnivGhost2` ∘ `LE-Var` | `·` | `[ ≐ β ]` | `S ↝ S` |

⭐ **THE LIFT TO `e_extract` IS ONE ARROW AND ONE `LS-Check`**, and everything
below the fork is free:

    NM = SK   m = TC   Θ0 = ·   subject (⫯α) → 1   counterpart β → 1

`LS-Check` is the only collection row there (α occurs, the counterpart is
guarded and ghost-free), and it hands the pair straight to `LE-Arrow`, whose
LEFT half IS the cell.  The right halves are α-free, both folds are one
`SE-GhostL` at the accumulator `◇`, and at `NM = SK` the guess is the
identity.  ⛔ The BLOCK conjunct alone refutes the statement — a chain maps
`·` to `·` — so no counting argument is needed.

⚙ **WHY LEVEL 4 DID NOT HAVE TO CARE.**  §8c.9's fourth pass met this exact
pair and DODGED it, by re-stating the b-core RUNNER-SIDED.  That is sound
there: `bcore_eq_stmt`'s conclusion carries a **rel-or-HATCH** yield ("or both
are raw variables") and NO supply conjunct, and the runner always takes FlexR,
so only the transportable orientation arises.  ⛔ Level 6 cannot dodge it:
`SI-ForallL` calls `e_extract_impl` and then recurses at
`(ex_supply rx, ex_block rx ++ Θ0, open Q (ex_out rx))`, so the DERIVATION's
extract outputs must be moved onto those rails by a swap chain — and a chain
relates neither the two blocks nor the two supplies, and the HATCH is exactly
a pair of variables it cannot relate (one of them is in `S0`).

#### B. ⛔ THE FORK — and (A), the cheap form, is REFUTED

| | premise on `LE-UnivGhost2` | verdict |
|---|---|---|
| (A) | `flex_r_off P' := forall β, P' <> pskl_var_f β` — context-free | ⛔ **REFUTED** |
| (B) | `P'` is not a FLEXIBLE variable, **and** `LE-FlexR` gains `a_flex_tvar Θ β` | ✅ the faithful one |

**(A) was carried through both encodings and is parked on branch
`remech-guard4-wip` (`40f900c`, marked [WIP — DOES NOT BUILD]).**  It is
machine-BLOCKED at `algo/sub/look/prop_eq_cstr.v:4676-4698`: the P6 chain at a
⫯-headed subject against `P0 = pskl_var_f β0` BUILDS `LE-UnivGhost2` there,
and (A) bars the row.  Under (A) that site would have to route through
`LE-FlexR`, whose answer throws the counterpart away — wrong when `β0` is
RIGID, and the site does not split on rigidity.

⭐ **AND THE REFERENCE IMPLEMENTATION SIDES WITH THE SITE.**
`constr_collect_eq`'s FlexR row is `| _, MFlex beta ->` (type.ml:561) and
`MFlex` is a constructor DISTINCT from `TVar` (lib/type.ml:23), so at a RIGID
variable counterpart the match falls through to `| UGhost p, p' ->`
LE-UnivGhost2 (:618).  The implementation takes FlexR only at a FLEXIBLE
counterpart.

⭐⭐ **SO THE MECH HAS A BUG OF ITS OWN, AND (B) FIXES BOTH.**
`a_lookeq__flex_r` / `e_lookeq__flex_r` fire at ANY `pskl_var_f β` — no
`a_flex_tvar Θ β` premise — where the paper's conclusion is at `β̂`
(`full-algo-spec.tex:1110-1116`).  Contrast the SOLVE layer's mirror
`a_solve_eq__flex_r`, which DOES carry `a_flex_tvar Θ α` and whose comment
argues at length that the narrow reading is the unfaithful one.  The two rows
are mirror images and only one of them was made faithful.  `docs/PAPER-GAPS.md`
has the paper-facing half.

#### C. ⚙ WHAT (B) COSTS — NOW MEASURED IN FULL (2026-08-18, branch `remech-guard4b-wip` `c1d3c70`)

| site | what it needs | status |
|---|---|---|
| the 12 `LE-FlexR` construction sites | `a_flex_tvar Θ β` | ⭐ the two P6 ones ALREADY HAVE IT — `prop_eq_cstr.v:2405-2418` splits `a_binds_tvar β0` and kills the RIGID branch as refinement-absurd; the other ten are transports (swap / rename / ctx-change), where it moves with the transport |
| the ~6 `LE-UnivGhost2` construction sites | the negative | vacuous by `discriminate` at a non-variable counterpart; ⛔ `prop_eq_cstr.v:4676` must ADD the rigid/flexible split and route the FLEXIBLE branch through `LE-FlexR`, mirroring `:2497` |
| `e_lookeq_impl` | `sumbool_of_bool (flex_bound_ck Θ β)` at the three (subject, `var`) clauses | `flex_bound_ck` already exists (`ext_algo/def_dec.v:146`) with soundness AND the `flex_bound_false_non_flex` corollary |
| `e_lookeq_order` | — | ⭐ **NOTHING**: its LE-UnivGhost2 clause is already `forall Q, P = ⫯Q -> e_lookeq_order S0 Θ α Q P'`, unconditional in `P'` (def_order.v:126-129), so the new recursion at a rigid-variable counterpart is already covered |
| the intros / destruct patterns | one extra binder per mutual induction over the collection | ⚙ MEASURED under (A): six sites — `ext_algo/prop_look.v` ×3, `algo/sub/prop_looksub.v` ×3 (incl. two `destruct … as` lists), `deco_algo/prop_decorate_sub.v` ×2, `ext_algo/prop_solve_rel.v` ×1 |
| the transports | `flex_r_off_swap` (`algo/prop_swap.v`), `rel_pskl_flex_r_off` (`ext_algo/prop_solve_rel.v`) | ⚙ both WRITTEN under (A) and reusable verbatim once the predicate gains its `Θ` |

⭐⭐ **(B) WAS CARRIED THROUGH AND IS GREEN ON EVERYTHING BUT TWO SITES**
(branch `remech-guard4b-wip`, `c1d3c70`, marked [WIP — DOES NOT BUILD]).  What
landed, beyond the table above:

| where | what |
|---|---|
| `frost/algo/def_rules.v` | `flex_r_off Θ P'` + `flex_r_off_nonvar` / `_rigid` |
| `frost/ext_algo/def_look_impl.v` | ⭐ THE RUNNER — `flex_bound_ck Θ β` at the three (subject, `var`) clauses; arrow and ∀ gain a `None` arm, **⫯ gains the LE-UnivGhost2 RECURSION**, and the two `lookdec` Hint Externs that let the obligation tactic see through the guard |
| `frost/algo/prop_swap.v` | `flex_r_off_swap` — needs the REVERSE of `a_flex_tvar_swap`, which involutivity supplies |
| `frost/ext_algo/prop_solve_rel.v` | ⭐ `a_flex_tvar_cons_tvar_any` — *a RIGID entry is invisible to `a_flex_tvar` at EVERY atom, its own included*, because `binds` is membership — and `flex_agree_rel_push_look`, WEAKER than `flex_agree_rel_push_tvar_pair`, whose `cols` / `V` conditions are NOT available at the collection's binder rows and (by the lemma above) are not needed |
| `frost/ext_algo/prop_run_complete.v` | `flex_test_absurd` — the derivation's own premise forces the runner's new test, in both directions — plus the three cells |
| `frost/algo/sub/prop_looksub.v` | `a_looksub_lookeq_ctx_ftv_mono` gains the flex-agreement side condition; `a_looksub_ctx_exchange` discharges it FREE (two RIGID entries) |
| `frost/ext_algo/prop_solve_rel.v` | `a_looksub_lookeq_rel_e` gains `flex_agree_rel ρ V Θ1 Θ2`, threaded by `flex_agree_rel_push_look`; its LE-FlexR and LE-UnivGhost2 rows move the guard across `rel_atom`'s two constructors |

⛔ **THE TWO SITES LEFT, AND THEY ARE ONE OBSTRUCTION** — a context move that
DROPS FLEXIBLES, which a GLOBAL flex-agreement cannot survive:

1. `algo/sub/look/prop_eq_cstr.v:3212` — the `LE-Arrow` row drops the
   all-`flex_mono` blocks `Ξs1 ++ Ξc1` down to `Θ0`.
2. `deco_algo/prop_soundness_sub.v:296` — shrinks the run's own context to
   `nil`, to make an opener's `ftvar_in_aenv` freshness vacuous.

⭐ **THE FIX IS A STATEMENT CHANGE, NOT A PROOF ONE — AND IT IS NOW LANDED,
WITH THE FIRST OBSTRUCTION CASHED** (second pass, `remech-guard4b-wip`
`b412b61`): the side condition is agreement on the COUNTERPART's free
variables, not a global iff —

```coq
  forall β, β `in` ftvar_in_pskl P' ->
    (a_flex_tvar Θ β <-> a_flex_tvar Θ' β)
```

— which is exactly what the collection reads, and which the induction
PRESERVES: `LE-Arrow` SHRINKS `ftv P'`, and every binder row adds an opener
that is RIGID on both sides.  Its kit is in `frost/algo/prop_basic.v`, where
both encodings can see it:

| lemma | content |
|---|---|
| `a_flex_tvar_cons_tvar_any` | ⭐ a RIGID entry is invisible to `a_flex_tvar` at EVERY atom, **its own included** — `binds` is membership, so a rigid binding neither creates a flexible one nor hides one further down.  Every transport rests on this. |
| `a_flex_tvar_in_dom` | flexible ⇒ in the domain |
| `a_flex_tvar_app_notin` | a PREFIX the atom is not bound in is invisible |

✅ **THE FIRST OBSTRUCTION IS CLOSED.**  `prop_eq_cstr.v`'s `LE-Arrow` row
drops its two all-flex blocks and the agreement survives, because `P02` is
Θ0-scoped and misses both — exactly the `HfrP02Ξs` / `HfrP02Ξ` the site
already proves.  ⚠️ `Set Implicit Arguments` makes all three binders of
`a_flex_tvar_app_notin` implicit (each occurs in the conclusion), so the site
drives it with `@`.

✅ **BOTH OF THOSE SITES ARE NOW CLOSED** (fourth pass, `remech-guard4b-wip`
`9c6a4de`), and `make -k` fails in exactly ONE file.

| site | how it closed |
|---|---|
| `prop_eq_cstr.v` | ⭐⭐ **`a_lookeq_flex_p0_complete`** — the ARROW grid's flex-P0 case, 454 lines, LIFTED OUT OF THE INDUCTION into a standalone Qed lemma.  It works because **the block never looked at the subject's shape** (only `≠ α`, `α ∈ ftv`, and its freshness unions) and uses NO induction hypothesis.  Factoring was a RENAMING of SIX spots.  Both grids call it; the ⫯ grid's var-P0 row becomes a rigid/flexible split.  ⚠️ `Set Implicit Arguments` makes ALL its binders implicit, so the calls use `@` + a positional list; and `apply a_lookeq__flex_r`'s subgoal ORDER is not the premise order, so its bullets must be `solve [ … ]`. |
| `prop_soundness_sub.v` | ⭐ **`flex_restrict`** (`frost/algo/prop_basic.v`) — keep exactly the flexibles the COUNTERPART mentions, payloads dropped.  Enough for the guard (scoped to `ftv P'`) and it still lands `ftvar_in_aenv` inside `ftv (∀B)`, which is what the shrink to `·` was for. |
| `prop_sub_cstr.v` | the same block-drop repair as `prop_eq_cstr.v`'s `LS-Arrow` row |
| `prop_look_pair.v` §1a | ⚠️ **the e-look's context is NO LONGER INERT** — two eq rows read it for hattedness — so `e_looksub_lookeq_ctx_any` gains a flex-agreement side condition, discharged FREE at both consumers (`flex_rigid_iff`) |

⛔ **WHAT IS LEFT — ONE SITE, AND IT IS A THIRD LAYER: the b-CORE**
(`ext_algo/prop_look_pair.v`).  ⭐ Fifth pass (`remech-guard4b-wip`
`b1d973a`) took it most of the way:

**LANDED.**  `bcore_eq_stmt` / `bcore_sub_stmt` gain three premises —

```coq
  flex_agree_rel ρ V Θd Θr      (* the two LOOK contexts agree *)
  ftvar_in_aenv Θd [<=] Sa0
  ftvar_in_aenv Θr [<=] Sb0
```

— threaded through all **32** `IHn` applications (one appended triple each,
discharged by the `bcore_dr` / `bcore_scp` tactics), and ⭐ **the CELL itself
is closed**: the runner's `flex_bound_ck Θr β` test is destructed and its
`false` arm killed by carrying side 1's `a_flex_tvar Θd β1` across
`rel_atom ρ V β1 β2`.  ⚙ One edit upstream: the `LE-FlexR` case used to
`clear` the counterpart's ρ-link; it now `rename`s it, because under the guard
that link is exactly what transports hattedness.

⛔ **THE REMAINING OBSTACLE IS A DESIGN POINT, NOT AN APPEND:
`flex_agree_rel ρ V Θd Θr` is not preserved when ρ GROWS.**  The `LE-Arrow`
row's second IH runs at `ρea ++ ρna ++ ρ`, so the agreement must hold at the
NEW pairs too.

| new pairs | verdict |
|---|---|
| `ρea` (the look's own extension) | ✅ free — `Hρea` gives `a ∈ Sa1 ∖ Sa0` and `b ∈ lk_supply ∖ Sb0`, which with the two new scopings makes BOTH sides non-flexible, so the iff is `False <-> False` |
| `ρna` (the FOLD's pairing, `Ξs1 = flex_pairs_l ρn`) | ⛔ no handle — the fold is on the `a_` side and its generated names are known fresh only for `ftvar_in_aenv Θf1` and `L`, never for `Sa0` / `Sb0` |

⭐⭐ **THE DESIGN THAT RESOLVES IT IS IN** (sixth pass, `remech-guard4b-wip`
`1ebde40`), and the non-obvious part is WHICH invariant to add.  Two premises
kill the ρ-growth, and a BINDER row preserves them for FREE:

```coq
  (forall a, a_flex_tvar Θd a -> a `in` ftvar_in_aenv Θf1)
  (forall b, a_flex_tvar Θr b -> b `in` ftvar_in_aenv Θf2)
```

⚙ Free because **a RIGID entry is invisible to `a_flex_tvar` at every atom**
(`a_flex_tvar_cons_tvar_any`), so `Θd` growing by an opener changes nothing.
⛔ The two obvious candidates both BREAK there — `ftvar_in_aenv Θd [<=]
ftvar_in_aenv Θf1` and `Sa0 [<=] ftvar_in_aenv Θf1` — because `Θf1` is CONSTANT
across the recursion while `Θd` and `Sa0` are not.  That is the whole content
of the choice.

Plus `flex_agree_rel_extend_nonflex` (`prop_solve_rel.v`): ρ may grow by pairs
the two contexts know nothing about, and there both halves of the new
obligation are FALSE.

✅ **THE ρ-GROWTH IS CLOSED** (seventh pass, `remech-guard4b-wip` `dba1382`).
Both arrow rows build the extended agreement with
`flex_agree_rel_extend_nonflex`, splitting the new pairs two ways:

| new pairs | how they die |
|---|---|
| `ρea` (the look's extension) | `Hρea` gives `a ∉ Sa0` and `b ∉ Sb0`; `Hscpd` / `Hscpr` turn those into non-flexibility |
| `ρna` (the FOLD's pairing — `cols_l ρna = dom Ξs1a`, `cols_r ρna = dom Ξ2a`) | ⭐ `Hflxd` / `Hflxr` send a flexible into `ftvar_in_aenv Θf1` / `Θf2`, and `a_solve_cstr_generated_fresh_set` says the fold's block dodges exactly that — **which is why the two new premises are stated about the FOLD contexts and not about the supplies** |

⚙ Also repaired on the way: **10** `eapply (IHn Sa0 Sa1 …) with (s := …)`
sites, where the blanket append had put the new arguments in the WRONG
positions (they now go through the trailing `all: try solve`);
`bcore_dom_fresh` no longer `clear`s the opener's own freshness; and
`e_lookeq_var_target_inv` now REPORTS the target's hattedness, which is
`LE-FlexR`'s own premise under the guard.

⛔ **WHAT IS LEFT — ONE CASE, AND IT IS A RESTRUCTURE, NOT A DISCHARGE.**
`bcore_eq`'s `LE-UnivGhost2` case, sub-case *"target a VAR"*.  Its comment says
*"the runner FlexRs"* — that was the **pre-guard** dispatch.  Under the guard,
side 1 stripping a ⫯ at a variable target carries `flex_r_off Θd (var t)`, i.e.
`t` is RIGID, so the runner does **not** FlexR: it takes the `LE-UnivGhost2`
RECURSION.  The branch has to follow that recursion (call the IH at the
stripped subject) instead of treating the head as junk.  ~30 lines.

⭐⭐⭐ **AND THAT IS THE ARGUMENT FOR §C'.**  The b-core's case structure was
shaped by the UNGUARDED dispatch: runner-sidedness, the rel-or-HATCH yield, and
now this branch all trace to the same cell.  **Re-stating the b-core two-sided
with a clean `rel_pskl` yield is very likely cheaper than repairing it case by
case — and it is what level 6 needs anyway.**  Decide that before spending the
~30 lines.

⚙ `e_extract_impl_complete` is the only call site of the b-core, and there
`Θd = Θr = Θ0`, so all five new premises are reflexivity or a one-line `binds`
argument.

⚙ **HISTORICAL — the two sites this replaces:**

1. **`algo/sub/look/prop_eq_cstr.v:4737`** — ⭐ **now ONE LEAF, not a case**
   (third pass, `remech-guard4b-wip` `244971e`).  A new lemma does the work:

   ```coq
   (* algo/sub/prop_looksub.v §2c *)
   Lemma a_lookeq_tophole_flex_counterpart : forall Θ α P β Ξ 𝒞,
     {{ Θ ⊢ P ∼[ α ] (pskl_var_f β) ⤳ Ξ ⨾ 𝒞 }}a ->
     a_flex_tvar Θ β -> P <> pskl_var_f α ->
     {{ Θ ⊢ (pskl_tophole P) ∼[ α ] (pskl_var_f β) ⤳ Ξ ⨾ 𝒞 }}a.
   ```

   ⭐⭐ **At a FLEXIBLE counterpart a ⫯ on the subject is INVISIBLE.**  At a
   variable counterpart only four rows can root a collection — `LE-Var` (the
   excluded leaf), `LE-UnivGhost2` (⛔ barred — that IS the guard), and
   `LE-Absent` / `LE-FlexR`, both of which read the subject ONLY through
   `ftv` and `≠ α`, neither of which a ⫯ changes.  The outputs therefore come
   through ON THE NOSE and the completeness chain does not re-derive the
   cell.  The row becomes a two-line split: RIGID β0 keeps `LE-UnivGhost2`
   (`flex_r_off_rigid` + `binds_unique`), FLEXIBLE β0 hands the IH's own run
   to the lemma.  Its two neighbours (`P0 = unit`, `P0 = arrow`) take
   `flex_r_off_nonvar`.

   ⛔ **THE RESIDUAL OBLIGATION IS `⌊R0⌋ˢ <> pskl_var_f α`** — the sub-case
   where the ⫯-headed subject is `⫯α` itself.  ⚠️ It is NOT derivable from the
   context (checked: `HscopeS`, `HαR`, `HαΘ0` and `Hrhobody` all admit
   `R0 = α`), and it is exactly the leaf where the two rows genuinely
   disagree: the stripped run is `LE-Var` and collects the RAW counterpart
   `[≐ β̂]` where the ⫯-headed one must INVENT `[≐ γ̂]`.  That branch has to
   build the FlexR answer itself, mirroring the ARROW grid's flex-P0 block
   (`:2398-2860`) — `𝒞 := [≐ γ̂]`, `Ξc := γ̂ ~ flex_mono`, then either the
   ρ-VARIABLE arm (`:2467-2536`) or the CLEAN arm's Pi-grid (`:2537-2810`).
   ⚙ Everything that block needs is already in scope at the leaf; the block is
   subject-generic apart from its freshness unions and its
   `ad_pat_consis_rsubst_psia_mono` call, **so the cheapest route is to FACTOR
   it out of the arrow grid and call it from both**.
2. **`deco_algo/prop_soundness_sub.v:296`** — shrinks the run's context to
   `·`, to make an opener's `ftvar_in_aenv` freshness vacuous.  The scoped
   condition asks only `~ a_flex_tvar Θl β` for β in the counterpart, and
   `Θl` is universally quantified INSIDE `a_subtag_decoration` with no
   constraint at all.  ⭐ Two routes: give the Θl-block that hypothesis
   (there is exactly ONE external caller, `:3593`), or — cleaner — restate
   `a_looksub_avoid_atom` and `a_looksub_open_target_at` to conclude at
   `rename_aenv δ β Θ`, which drops their `β ∉ ftvar_in_aenv Θ` premise and
   makes the context move unnecessary altogether.

**Resume there**, then §D's four lemmas.

⭐ **AND ONE THING (B) BUYS BACK.**  Under (A), `prop_decorate_sub.v`'s "FlexR
assignment of the ∀◇-headed subject to the flexible input" branch collapsed to
`exfalso`, retiring a use of `flexvar_decoration_swap`.  Under (B) that branch
SURVIVES (its input IS flexible) — so expect (B) to remove less work than (A)
appeared to, and budget the branch as-is.

#### C'. ⭐⭐ IS THE DESIGN OPTIMAL?  — a review, and ONE thing it changes

Worth asking, because (B) has now cascaded through four layers.  The answer is
that the FORK is forced but the PLAN downstream of it should change.

**The fork is forced.**  ⛔ (A) dies at `prop_eq_cstr.v:4676` and disagrees with
`constr_collect_eq`.  ⛔ Putting the guard on `LE-UnivGhost2` ALONE leaves the
(⫯, RIGID var) overlap standing, because without the hat `LE-FlexR` still
fires there.  ⛔ Copying the SOLVE layer's answer (`nonghost_pskl` on FlexR)
inverts the implementation's own match order.  So both premises are needed,
and the cost is the price of fixing a REAL mech bug: pre-guard, the runner
invents a fresh flexible at a rigid-variable counterpart where the paper
strips the ⫯.  That cell is ordinary — the counterpart is a sub-skeleton of
the inherited type — so this is not a corner.

**The b-core's premise shape is right too**, and the alternatives were checked:
a V-only agreement does not reach the cell (the counterparts can be ρ-paired);
collapsing `Θd`/`Θr` does not help for the same reason; and stating the
agreement at the cell's own counterparts is not re-establishable at the
recursive calls.  ⭐ The one simplification worth taking is to state it as an
IMPLICATION rather than an iff — the cell only needs "side 1 flexible ⇒ side 2
flexible", which halves every discharge obligation.

⭐⭐⭐ **WHAT THE REVIEW DOES CHANGE — §D's plan.**  Level 4's b-core carries a
rel-or-**HATCH** yield ("or both are raw variables"), and that hatch is there
for exactly ONE reason: the (⫯, var) cell, where `LE-FlexR` and
`LE-UnivGhost2` disagreed and the two yields were unrelated variables
(`cex/probe_bcore_ug2_flexr.v`, §8c.9's fourth pass).  **Under the guard that
cell is gone, so the hatch can be DELETED and the b-core's conclusion becomes a
clean `rel_pskl`.**  The hatch is precisely what made level 4's conclusion too
weak for level 6.  So before writing §D's four new `_rel` lemmas — which
duplicate a great deal of the b-core — check whether STRENGTHENING the b-core
(drop the hatch, add the supply conjunct) reaches `e_extract_impl_rel`
directly.  That is a smaller and better-tested path than a fresh induction.

#### D. What this leaves for STEP 2, unchanged and still correct

Once (B) lands, §8c.15 G's factor table stands, with one correction: the
statement to prove is on the `e_` judgements with SWAP CHAINS, and the
template is **not** `prop_solve_det.v` §3/§4 (which are `a_`-level and in the
PAIRING formulation, carrying no supply) but
**`prop_consis_complete.v` §3b, `e_guess_mono_rel_n` / `e_guess_mono_rel`** —
already Qed, already chain-formulated, already a size induction for exactly
the reason level 6 needs one (the arrow row threads, so the second halves sit
at DIFFERENT input supplies and a derivation-indexed IH would be pinned to
one).  ⚙ **THE FORK OF §8c.15 G IS THEREBY RESOLVED: go `e_`, not `a_`.**  The
`a_`-level pairing form cannot express the supply conjunct at all, and
bridging it would require a separate "the supply increment is the block domain
plus the openers" invariant for each of look / solve / guess — three different
fates for an opener (LEAKED into 𝒞 by `LS-ForallR`, LEAKED into the output by
`SS-ForallR`, CLOSED by `SS-ForallL`), none of which exists.

The four lemmas STEP 2 then owes, in order:

1. `e_looksub_lookeq_rel` — mutual, size induction, chain conclusion.  ⭐ Its
   case analysis is the audit in §E below.
2. `e_solve_sub_eq_rel` + `e_solve_cstr_rel`.  ⚙ The `a_`-level
   `a_solve_eq_det` (prop_solve_det.v §4) is Qed and HYPOTHESIS-FREE, and its
   case skeleton — `det_absurd`, `det_nil_refl`,
   `a_solve_eq_var_subject_inv` — transfers row for row.
3. `e_guess_rel` — three lines from `e_guess_mono_rel` (`e_guess__sk` is the
   identity at `ps = nil`; `e_guess__ty` needs
   `swaps_pskl ps (ptyp_to_pskl A) = ptyp_to_pskl (swaps_ptyp ps A)`).
4. `e_extract_rel` — compose, moving each stage onto the previous chain with
   the `_swaps` iterations of §3 (`e_looksub_lookeq_swaps` etc. do NOT exist
   yet; `e_guess_mono_swaps` and `e_consis_swaps` are the pattern).

#### E. ⭐ THE COLLECTION'S OVERLAP AUDIT — done, do not redo it

Checked row by row against `e_looksub_impl` / `e_lookeq_impl`
(`ext_algo/def_look_impl.v`).  With guards 1–3 landed and (B) added, the
dispatch is SINGLE-RULE at every cell where the answers could differ:

**`e_looksub`** — at a subject the marker does not occur in, `LS-Absent`
races `LS-Vacuous` / `LS-Check` / `LS-Arrow` / `LS-UnivGhostL` and they all
COINCIDE (`e_looksub_lookeq_absent_pins`: `Ξ = ·`, `𝒞 = ·`, supply
unchanged).  Where the marker DOES occur:

| subject | counterpart | rule, and what excludes the others |
|---|---|---|
| `α` | any | `LS-Var` — the ◇-dispatch guard puts `≠ α` on Vacuous / Check / ForallR |
| any | `◇` | `LS-Vacuous` — `P' ≠ ◇` on ForallL / UnivGhostL |
| `∀Q` / `⫯Q` | ghost-free `∀B`, `TC` | `LS-ForallR` — `forall_r_off` blocks ForallL / UnivGhostL |
| `∀Q` | else | `LS-ForallL` — Check wants a `guarded` subject, and `∀` is not |
| `⫯Q` | else | `LS-UnivGhostL` — likewise |
| `arrow` | `guarded` ghost-free, `TC` | `LS-Check` — Arrow wants `mode_fn` |
| `arrow` | `arrow`, `mode_fn` | `LS-Arrow` — Check wants `TC` |

**`e_lookeq`** — same absent-race, and then:

| subject | counterpart | rule |
|---|---|---|
| `α` | any | `LE-Var` |
| any | `◇` | `LE-Vacuous` |
| any | flexible `β̂` | `LE-FlexR` — ⛔ **this is the row (B) is about**; today `LE-UnivGhost2` races it at a `⫯` subject |
| `arrow` | `arrow` | `LE-Arrow` |
| `arrow` | `⫯Q'` | `LE-UnivGhostR` (`guarded` subject) |
| `∀Q` | `∀Q'` / `⫯Q'` | `LE-ForallInh` / `LE-ForallSyn` |
| `⫯Q` | `⫯Q'` / `∀Q'` | `LE-UnivGhost` / `LE-UnivGhost1` |
| `⫯Q` | `1`, `arrow`, RIGID var | `LE-UnivGhost2` |

⚙ Every other (subject, counterpart) pair has NO rule, which is the runner's
`None`.

#### F. Resume point

1. Scope the collection's context-weakening lemma against (B) (§C's
   obstruction).  Everything else in (B) is mechanical.
2. Land (B) on both encodings + the runner; `[paper-gap]` comments and the
   `docs/PAPER-GAPS.md` entry are ALREADY WRITTEN (the 2026-08-18
   `LE-UnivGhost2` entry).
3. Then §D's four lemmas, then §6/§7 of `prop_sub_complete.v` (§8c.13's
   recipe — its header still says the level is blocked on the ABSENCE guard,
   which is stale; the blocker is now this one), then §8's three headlines.

⚠️ `frost/ext_algo/prop_sub_complete.v`'s file header (lines 19-46) is STALE:
it names the absence-first guard as what is owed.  Update it when (B) lands.

### 8c.17 ✅ THE HATCH IS DELETED — the b-core's yield is a clean `rel_pskl` (2026-08-18)

✅ **`make coq` rc=0, `README.v` 32/32, zero `Admitted`.**  §C''s prediction
holds: `bcore_eq_stmt`'s conclusion is now

```coq
  /\ rel_pskl (ρe ++ ρn ++ ρ) V Q1 Q2
```

with no `\/ (exists γ1 γ2, Q1 = pskl_var_f γ1 /\ Q2 = pskl_var_f γ2)`.  That
disjunct is what made level 4 too weak for level 6, and it is gone.

**⭐ THE SOURCE WAS ONE ROW, AND THE FIX IS ONE PAIR.**
`a_solve_eq_var_target_junk` took `t1` and `t2` with nothing relating them, and
its `SE-GhostL` row yields the TARGET on each side — so with unrelated targets
the conclusion could not be a `rel_pskl`.  The lemma now takes
`rel_atom ρ V t1 t2` and concludes `rel_pskl (ρn ++ ρ) V mid1 mid2`
unconditionally; `SE-GhostL` closes by `rel_pskl__var_f`.

⚙ **AND THE TARGETS WERE ALWAYS RELATABLE — the b-core just never said so.**
Its single caller is `bcore_eq`'s `LE-FlexR` row, where `t1` is the
derivation's own generated flexible (`α1 ∉ Sa0`, `Sa1 = add α1 Sa0`) and `t2`
is the runner's (`supply_fresh Sb0`).  ⭐ That is EXACTLY the shape of a `ρe`
entry — `a ∈ Sa1 ∖ Sa0`, `b ∈ lk_supply ∖ Sb0`, flex-status agreeing — so the
row now emits `ρe := (α1, supply_fresh Sb0) :: nil` instead of `nil` and calls
the junk head at the extended pair list.  The five interval obligations are
one line each, and the flex-status iff is `True <-> True` (both names are
`abind_flex_mono` in their own fold context, via `Hb1` / `Hb2`).

⚙ **NOTHING ELSE HAD TO MOVE.**  The `LE-Arrow` rows are generic in `ρea` —
they only ever read `Hρea`'s five facts — so a `ρe` that is no longer always
`nil` costs them nothing, and the ρ-growth argument of the seventh pass covers
the new pair unchanged (`α1 ∉ Sa0 ⊇ ftvar_in_aenv Θd` makes it non-flexible on
the LOOK side, which is what `flex_agree_rel_extend_nonflex` wants).

⚙ **WHAT WENT AWAY**: both "hatch branch" blocks (`bcore_eq`'s `LE-Arrow` and
`bcore_sub`'s `LS-Arrow`, ~25 lines each), six `destruct Hyield as [ … | … ]`
splits, and §2d's role in the roadmap (the var-pattern fixed point is still
used elsewhere, but it is no longer *what makes the hatch harmless*).
⚠️ **The net line count went UP by 19**, not down as §C' guessed: the pairing
bookkeeping at `LE-FlexR` (~46 lines) costs about what the two hatch branches
paid.  The win is the STATEMENT, not the size.

⚙ `bcore_sub_stmt` needed no change — its conclusion was already BARE (no
yield); it consumes `bcore_eq`'s at its `LS-Arrow` row, and at three
`LS-Check` sites it discards it with `_`.

**Resume: §D's four lemmas** (§8c.16 §D), then §6/§7 of
`prop_sub_complete.v`, then §8's three headlines.

### 8c.18 ⛔⛔ A FIFTH DISPATCH GUARD IS OWED — `e_extract_det` IS STILL FALSE, AND THE DRIFT IS IN THE SOLVE LAYER (2026-08-18)

**⛔ THE PREMISE OF §8c.16 §D IS REFUTED.**  With all four dispatch guards
landed, `e_extract_det` is still false, and this time the ambiguity is one
layer BELOW the collection: `cex/probe_solve_sub_forall_r_drift.v`
(`e_extract_det_false`, Qed, assumptions-closed).

#### The cell

At subject `γ` — a VARIABLE — against counterpart `∀_. 0` (ghost-free) in
CHECK mode, two rows fire:

| row | Ξ | yield | supply |
|---|---|---|---|
| `SS-Var` | `·` | `γ` | `S ↝ S` |
| `SS-ForallR` ∘ `SS-Var` | `·` | `γ` | `S ↝ add β S` |

The block and the yield AGREE; the supplies differ by ONE ATOM.  Exactly the
species of `cex/probe_extract_supply_drift.v` (retracted by the absence-first
guard) and `cex/probe_extract_flexr_ug2_drift.v` (retracted by the
FlexR-priority guard).

⚙ **THE LIFT TO `e_extract` IS ONE ARROW**, and it is in the probe: at
`NM = SK`, `m = FN(TC)`, `Θ0 = ·`, subject `α → α`, counterpart `γ → ∀_.0`,
`LS-Arrow` hands its first half to `LE-Var` (collecting `≐ γ`) and its second
to `LS-Var` (collecting `≼TC ∀_.0`); the fold solves `◇ ∼ γ ⤳ γ` and hands
the accumulated `γ` to the cell above.  ⭐ The BLOCK conjunct is not needed —
the SUPPLY conjunct alone refutes the statement.

#### ⭐ AND THE REFERENCE IMPLEMENTATION ALREADY DISAGREES WITH THE RELATION

`solve_sub` (`paper/artifact/implementation/lib/type.ml:494`) matches

```
| _, (TVar _ as alpha)              -> SolS-Var          (* FIRST, any mode *)
| m, TForA (k, p)                   -> SolS-ForallL
| m, TMod (mu, p)                   -> SolS-ModL
| m, UGhost p                       -> SolS-UnivGhostL
| (Infer | Check Ghost), p          -> SolS-Vacuous
| Check (TForA (_, b)), a when is_type a -> SolS-ForallR
…
```

so a VARIABLE subject takes `SolS-Var` in every mode and never reaches
`SolS-ForallR`.  This tree's runner renders the same order
(`ext_algo/def_solve_impl.v:316`).  A relational encoding has no match order,
so the exclusion must be a PREMISE — the argument that landed guards 1–4,
verbatim.

#### ⭐ TWO PREMISES ARE OWED, NOT ONE — the second cell is machine-checked too

`SS-Vacuous` races `SS-ForallL` at a `∀` SUBJECT against a `◇` counterpart
(`vacuous_route` / `forall_l_route` in the same probe, both Qed): `SS-Vacuous`
answers `∀P` spending nothing, `SS-ForallL` draws an opener and answers
`∀(close β (open P β))`, which IS `∀P`.  Same drift, and the implementation
again takes the earlier clause (`SolS-ForallL` precedes `SolS-Vacuous`).

#### ⚙ THE OVERLAP AUDIT FOR `e_solve_sub` — done, and only these two DRIFT

Checked row by row against the runner's clause order.  Every other overlap
either COINCIDES (same block, same yield, same supply) or is a COMMUTATION
that spends the same atoms on both routes:

| cell | rows | verdict |
|---|---|---|
| (var, ∀ gf, TC) | `SS-Var` / `SS-ForallR` | ⛔ **DRIFT** — one atom |
| (∀, ◇) | `SS-Vacuous` / `SS-ForallL` | ⛔ **DRIFT** — one atom |
| (var, ◇) | `SS-Var` / `SS-Vacuous` | ✅ coincide |
| (⫯P, ◇) | `SS-UnivGhostL` / `SS-Vacuous` | ✅ coincide |
| (var, guarded gf, TC) | `SS-Var` / `SS-Check` | ✅ coincide — `SS-Check`'s premise is the EQ layer, and a variable subject answers itself there (`e_solve_eq_var_subject`) |
| (∀, ∀ gf, TC) | `SS-ForallL` / `SS-ForallR` | ⚙ COMMUTATION — both routes draw TWO openers, so a chain relates them; this is the "peel" §8c.16 §D already budgeted |
| (⫯, ∀ gf, TC) | `SS-UnivGhostL` / `SS-ForallR` | ⚙ COMMUTATION — one opener each |
| (◇, ∀ gf, TC) | `SS-ForallR` alone | ✅ `SS-GhostL` / `SS-Check` want a GUARDED counterpart |
| everything else | — | ✅ single-rule by shape or mode |

#### ⛔ THE FORK — and it is the USER's call, because it is a RULE CHANGE

| | premises on the two rows | cost |
|---|---|---|
| (i) MINIMAL | `SS-ForallR` gains "the subject is not a variable"; `SS-Vacuous` gains "the subject is not a `∀`" | two one-line premises, but the (∀,∀) and (⫯,∀) COMMUTATIONS survive and still need the peel |
| (ii) RUNNER-MIRRORING | `SS-ForallR` additionally excludes `∀` and `⫯` subjects; `SS-Vacuous` additionally excludes `⫯` | dispatch becomes SINGLE-RULE and the peel EVAPORATES — §8c.15's lesson ("a dispatch guard can REMOVE work") one more time — but it is a bigger rule change and every `SS-ForallR` construction site must be re-checked |

⚙ **A THIRD, INDEPENDENT OBSERVATION worth a `[paper-gap]` line either way**:
the implementation's `SolS-ForallR` carries `when is_type a` — the SUBJECT
must be GHOST-FREE (`is_type` is exactly "no `Ghost` / `UGhost`",
type.ml:`is_type`) — and neither `a_solve_sub__forall_r` nor
`e_solve_sub__forall_r` carries it.

#### ✅ WHAT LANDED ANYWAY — STEP 2's first three lemmas do not depend on the fork

`frost/ext_algo/prop_extract_det.v`, all Qed:

| § | content |
|---|---|
| §1 | the `_swaps` CHAIN iterations §8c.16 §D found missing — look (both layers), solve (sub / eq / cstr), guess, extract |
| §2 | fourteen ROOT INVERSIONS for the collection — §8c.16 §E's table, machine-checked |
| §3 | ⭐ `e_lookeq_rel` — the eq collection is deterministic up to a fresh renaming, SUPPLY INCLUDED |
| §4 | ⭐ `e_looksub_rel` — the sub collection, same |
| §5 | ⭐ `e_solve_eq_rel` — the SOLVE layer's EQ half, same.  ⚙ Its `a_`-level twin `a_solve_eq_det` (prop_solve_det.v §4) transfers row for row; the binder rows get SIMPLER (pair the two openers with ONE transposition instead of rebinding both to a globally fresh third atom — the supply already says each opener is fresh for `S0`) |

⛔ `e_solve_sub_rel` is what the fork blocks; `e_solve_cstr_rel`,
`e_guess_rel` and `e_extract_rel` are downstream of it.

**Resume: take the fork, land guard 5 on both encodings + the runner
(`[paper-gap]` comment + `docs/PAPER-GAPS.md` entry), then §6–§9 of
`prop_extract_det.v`.**

### 8c.19 ✅ GUARD 5, THE SOLVE-DISPATCH SPLIT — LANDED, AND THE TREE IS GREEN (2026-08-18)

✅ **`make coq` rc=0, `README.v` 32/32, zero `Admitted`.**  §8c.18's fork was
taken as **(ii), MIRROR THE RUNNER** (user's call).  On both encodings:

```coq
  (* frost/def_shapes.v *)
  Definition peel_l_off (P : pskl) : Prop :=        (* SS-ForallL / SS-UnivGhostL *)
    (forall Q, P <> pskl_all_syn Q) /\ (forall Q, P <> pskl_tophole Q).
  Definition solve_l_off (P : pskl) : Prop :=       (* … and SS-Var as well *)
    (forall α, P <> pskl_var_f α) /\ peel_l_off P.
```

`SS-Vacuous` gains `peel_l_off P`; `SS-ForallR` gains `solve_l_off P`.
⛔ `cex/probe_solve_sub_forall_r_drift.v` is RETRACTED by the guard and
DELETED; its text is at `5e2384f`.

#### ⭐ WHAT THE GUARD REMOVED, AND WHAT IT MOVED — both, and it is worth knowing which

**REMOVED.**  `prop_run_complete.v`'s two reorder lemmas collapse.
`a_solve_sub_tophole_l_first`'s Vacuous and ForallR roots and
`a_solve_sub_forall_l_hoist`'s are now `exfalso` — three lines each — and
with them goes the hoist's ~45-line INTERIM-OPENER DANCE (IH at a fresh δ on
top of the premise's context, then two rebinds and two context exchanges to
renest the openers).  §8c.15's lesson a third time.

**MOVED, not removed.**  ⚠️ The commutation reappears one level up, because
the completeness chain BUILDS `SS-ForallR` at an arbitrary accumulated
pattern.  The old rule survives as a DERIVED one, proved once in
`algo/sub/look/prop_eq_cstr.v`:

```coq
  Lemma a_solve_sub_forall_r_gen : forall Θ P B Ξ P' β,
    pskl_ghost_free (pskl_all_syn B) ->
    β `notin` ftvar_in_aenv Θ ∪ ftvar_in_pskl P ∪ ftvar_in_pskl B ->
    {{ ((β ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ mode_tc ]
       (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ P' }}a ->
    {{ Θ ⊢ₛ P ≼[ mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ P' }}a.
```

a size induction on the SUBJECT with three interesting leaves — a VARIABLE
subject (`a_solve_sub_var_subject`: every route answers the variable itself,
so `SS-Var` rebuilds the conclusion), a `∀` subject (peel, `EXCHANGE` the two
rigid openers, recurse, re-close — the commutation, paid ONCE here instead of
at every consumer), and a `⫯` subject (strip, recurse, re-wrap).  Its
supporting inversions — `a_solve_eq_var_subject`,
`a_solve_sub_inv_forall_l`, `a_solve_sub_inv_univ_ghost_l` — are the guard's
own single-rule dispatch, machine-checked.  ⭐ Net: the dance is written once
and deleted twice.

⚙ **AND THE SAME SHAPE FOR `SS-Vacuous`** — `a_solve_sub_vacuous_gen`
(`algo/prop_basic.v`), an unconditional
`{{ Θ ⊢ₛ P ≼[m] ◇ ⤳ · ⨾ P }}a`: at a `∀` the peeled route re-CLOSES over
the opener it drew and at a `⫯` it re-wraps, so the answer is the subject
back either way.  Every old `apply a_solve_sub__vacuous` site reads this
instead, verbatim.

#### ⚙ THE LANDING, SITE BY SITE

| file | what |
|---|---|
| `frost/def_shapes.v` | `peel_l_off` / `solve_l_off` + nine discharge lemmas + `frost` hints |
| `frost/algo/def_rules.v`, `frost/ext_algo/def_solve.v` | the two premises, `[paper-gap]`-commented |
| `frost/algo/prop_swap.v` | `peel_l_off_swap` / `solve_l_off_swap` — pure shape predicates, so a swap moves them for free |
| `frost/algo/prop_basic.v` | ⭐ `a_solve_sub_vacuous_gen` |
| `frost/algo/sub/look/prop_eq_cstr.v` | ⭐⭐ `a_solve_sub_forall_r_gen` + its three inversions |
| `frost/ext_algo/prop_solve_rel.v` | `rel_pskl_peel_l_off` / `rel_pskl_solve_l_off` — the guards transport along `rel_pskl` (a variable relates only to a variable, so even the var-exclusion survives) |
| `frost/ext_algo/def_solve_impl.v` | the runner: guard hints in `solvedec`, and ⚠️ TWO `Next Obligation`s spelled out — the obligation tactic does not reach the `SS-Vacuous` leaves at `var_b` / `arrow` |
| `frost/ext_algo/prop_run_complete.v` | the two reorder lemmas collapse |
| the rest | intros / `destruct … as` patterns shifted by one, at `prop_rsubst.v`, `prop_solve_ext.v`, `prop_soundness_sub.v`, `prop_look_pair.v`, `prop_solve.v`, `test_examples.v`, `cex_solve_sub_wf_leak.v` |

⚠️ **THE DECORATED SYSTEM NEEDED NOTHING.**  Decoration CONSUMES an
`a_solve_sub` derivation, so a new premise on the source is extra
information, not an extra obligation.

⚠️ **A TRAP PAID.** An Equations obligation that its `#[tactic=…]` does not
reach is deferred with NO diagnostic; `Next Obligation. lazymatch goal with
|- ?G => idtac "CONCL:" G end. Admitted.` on a TRUNCATED copy is what named
the two leaves.  ⚠️ And raising `eauto 6` to `eauto 8` there does not fix it
— it just never terminates.

**Resume: §6–§9 of `prop_extract_det.v`** — `e_solve_sub_rel` is now TRUE
(its two drifting cells are gone and the (∀,∀) / (⫯,∀) commutations are
single-rule), then `e_solve_cstr_rel`, `e_guess_rel`, `e_extract_rel`.

### 8c.20 ✅ STEP 2 IS CLOSED — `e_extract_det` IS Qed — and §6 of level 6 is in (2026-08-18)

✅ **`make coq` rc=0, `README.v` 32/32, zero `Admitted`.**

#### What closed

`frost/ext_algo/prop_extract_det.v`, all Qed and assumptions-closed:

| § | content |
|---|---|
| §1 | the seven `_swaps` CHAIN iterations §D found missing (look ×2, solve ×3, guess, extract) |
| §2 | fourteen collection ROOT INVERSIONS — §E's overlap table |
| §3 / §4 | `e_lookeq_rel` / `e_looksub_rel` |
| §5 | `e_solve_eq_rel` |
| §6 | `e_guess_rel` |
| §7 | `e_solve_sub_rel` + nine root inversions |
| §8 | `e_solve_cstr_rel` |
| §9 | ⭐⭐⭐ `e_extract_rel` / `e_extract_det` |

⭐ **THE HEADLINE WAS REFUTED THREE TIMES ON THE WAY**, each time by a missing
dispatch guard one layer further down, and each refutation is retracted by the
guard that answers it — `probe_extract_supply_drift.v` (absence-first),
`probe_extract_flexr_ug2_drift.v` (FlexR-priority),
`probe_solve_sub_forall_r_drift.v` (solve-dispatch).  **That is the level's
lesson in one line: when a supply conjunct is false, look for a rule that the
implementation's MATCH ORDER excludes and the relation does not.**

⚙ Two conventions that paid throughout and are worth keeping: put the
DERIVATION before the size and coverage premises in a `_rel_stmt`, so
`IH _ … _ D ltac:(lia) …` elaborates the `ltac:` after `D` has fixed every
underscore; and take names off `match type of D1`, never off `inversion`'s
generated ones (they clash — `inversion` already binds `β` at a binder row).

#### `prop_sub_complete.v` §6 — the motive — is in, and the header is fixed

`sub_call_complete`, with §8c.13's predicted simplification: BOTH call tags
carry an output skeleton, so the output conjunct is a plain EQUALITY.

#### ⛔ WHAT IS LEFT: §7 and §8, and here is the plan, validated as far as it goes

**⭐ SPLIT §7 AT §1's TWO HYPOTHESES.**  Do NOT write one monolithic
induction.  State two standalone lemmas whose statements are *literally*
§1's `Hsub` and `Hflex` with `Qc` replaced by `sub_call_complete`:

```coq
  Lemma sub_call_complete_sub  : forall S0 NM M P0 Θ0 P,   … (Hsub's premises) …
    -> sub_call_complete S0 NM M P0 Θ0 (sub_call_sub P).
  Lemma sub_call_complete_flex : forall S0 NM M P0 Θ0 Ξ α, … (Hflex's premises) …
    -> sub_call_complete S0 NM M P0 Θ0 (sub_call_flex Ξ α).
```

then §7c is three lines:

```coq
  Lemma e_sub_call_impl_complete : forall S0 NM M P0 Θ0 c
      (H0 : e_sub_call_order S0 NM M P0 Θ0 c),
      sub_call_complete S0 NM M P0 Θ0 c.
  Proof.
    intros. apply (e_sub_call_order_sind sub_call_complete);
      [ exact sub_call_complete_sub | exact sub_call_complete_flex | exact H0 ].
  Qed.
```

⚙ Extract the two statements MECHANICALLY from §1 (they are ~120 lines of
premises between them and must match to the character, or the `apply` fails):
read the `Hypothesis Hsub`/`Hflex` blocks out of the file and substitute
`Qc ` → `sub_call_complete `.  ✅ The FLEX statement was extracted that way
and type-checks, together with its opening —

```coq
  intros S0 NM M P0 Θ0 Ξ α hsl Hsl hag Hag hdp Hdp hrg Hrg htv Htv hts Hts.
  unfold sub_call_complete.
  intros HP HP0 HD Hord Hu Hcov Sd Θd Qd Hd.
  cbn [sub_call_uniq sub_call_cover sub_call_run] in *.
  destruct Θ0 as [ | [γ b] Θ0' ]; [ destruct (e_sub_flex_inv_nil Hd) | ].
  destruct b as [ | A | Qp | | τ ].
```

— so the five head shapes come out in `abind`'s declaration order:
`tvar`, `var_typ`, `var_skl`, `flex_mono`, `flex_mono_def`.

**THE FLEX HALF, case by case.**  Each row is: invert the derivation with its
§4 lemma, walk the runner's own tests, recurse through the motive premise,
and re-wrap the head.

| head | §4 inversion | the runner's tests (def_sub_impl.v:759-856) | motive premise |
|---|---|---|---|
| `γ ~ tvar` | `e_sub_flex_inv_tvar` | `γ == α` → right (from the inversion's `α <> γ`), then `mem γ (ftv P0)` → right | `Hrg γ Θ0' eq_refl` |
| `x ~ var_typ A` | `e_sub_flex_inv_var_typ` | none | `Htv x A Θ0' eq_refl` |
| `x ~ var_skl Q` | `e_sub_flex_inv_var_skl` | none | `Hts x Q Θ0' eq_refl` |
| `γ ~ flex_mono`, `γ = α` | `e_sub_flex_inv_self` | `γ == α` → left | `Hsl Θ0' eq_refl` — ⭐ the PRE-SWAP row, below |
| `γ ~ flex_mono`, `γ ≠ α` | `e_sub_flex_inv_other_flex` | `γ == α` → right, then `mem γ (ftv P0)`: **left** = Depend (accumulate into `Ξ`), **right** = Skip (re-wrap the head) | `Hdp γ Θ0' eq_refl`, whose two conjuncts are exactly those two branches |
| `γ ~ flex_mono_def τ` | `e_sub_flex_inv_def` | none | `Hag γ τ Θ0' eq_refl` — note the call tag flips to `sub_call_sub` and the mode to `mode_fn M` |

⭐ **THE ONE NON-ROUTINE ROW IS `SI-Flex-Solve`** and §8c.13 pinned its chain:
the derivation draws `ad`, `bd` (`e_sub_flex_inv_self` gives `ad ∉ S0`,
`bd ∉ add ad S0`) where the runner draws `a1 := supply_fresh S0` and
`b1 := supply_fresh (add a1 S0)`.  Pre-swap with

```coq
  bd' := swap_atom ad a1 bd        ps0 := (ad, a1) :: (bd', b1) :: nil
```

and the ONE obligation that is not `solve_notin` is `a1 <> bd'`.  Move the
derivation with `e_sub_swaps ps0` before handing it to `Hsl`.

⚙ **THE RECURSION TACTIC** is level 5's `kill_ccall`
(prop_consis_complete.v §7) with the extra `NM`/`M`/`P0` arguments:

```coq
  Local Ltac kill_scall Hmot Hu Hcov Hder r Hr ps Hav HS HT HQ :=
    match goal with
    | |- context [ e_sub_call_impl ?c ?S ?nm ?m ?p0 ?T ?hp ?hp0 ?hd ?h ] =>
        let Hx := fresh in let Hcl := fresh in let rr := fresh in
        destruct (Hmot hp hp0 hd h Hu Hcov _ _ _ Hder)
          as [r [ps [Hx [Hav [HS [HT HQ]]]]]];
        destruct (e_sub_call_impl c S nm m p0 T hp hp0 hd h)
          as [ [rr Hr] | ] eqn:Hcl;
        try rewrite Hcl in Hx; cbn [sub_call_answer] in Hx;
        [ inversion Hx; subst; clear Hx Hcl; cbv beta iota | discriminate ]
    end.
```

and the head re-wrap is level 5's `head_fresh` verbatim (the head atom is in
`sub_call_cover`, hence in `S0`, which every chain pair dodges).

**THE SUB HALF** dispatches as the runner does and every cell has its §4
inversion by name in §8c.13's table.  ⭐ Its one genuinely new row is
`SI-ForallL`, and it is the row all five guards were landed for: it runs
`e_extract_impl` and then recurses at
`(ex_supply rx, ex_block rx ++ Θ0, open Q (ex_out rx))`, so the derivation's
extraction must be moved onto the runner's rails — which is exactly
`e_extract_det` (`prop_extract_det.v` §9), now available.

**Then §8**: `e_sub_impl_complete`, `e_sub_flex_impl_complete` and
`e_sub_run_complete`, exactly as prop_consis_complete.v §8 does for
consistency.

### 8c.21 ⭐⭐⭐ LEVEL 6 IS CLOSED — the SUBTYPING runner is COMPLETE, §7 and §8 (2026-08-18)

✅ **`make coq` rc=0, `README.v` 32/32, zero `Admitted`/`Axiom` in
`frost/`, `cex/`, `test/`.**  `frost/ext_algo/prop_sub_complete.v` is Qed
end to end, and its three headlines are assumptions-closed:

| lemma | what it says |
|---|---|
| `e_sub_impl_complete` | a derivation of `{{ S0 ↝ Sd ⊨ Θ0 ⊢[NM\|M\|P0] P ⩽ Qd ⊣ Θd }}e` makes `e_sub_impl` answer `Some r`, with a chain `ps` (each pair dodging `S0`) sending `Sd`/`Θd`/`Qd` to `r`'s three components |
| `e_sub_flex_impl_complete` | the same for the flexible WALK |
| ⭐ `e_sub_run_complete` | the same over the argument-free `e_sub_run` — the twin of `e_sub_run_sound` |

Side conditions: `uniq Θ0` and `ftvar Θ0 ∪ ftv P0 ∪ ftv P ⊆ S0`
(prop_sub.v §4's, verbatim).  ⭐ **Nothing is restricted**: level 5's
hole-free rung was lifted in §8c.10c/§8c.17, so ghost-carrying skeletons
are in scope.

#### The shape §8c.20 predicted, and it held

§7 splits at §1's two hypotheses — `sub_call_complete_flex` and
`sub_call_complete_sub`, statements extracted mechanically from `Hflex` /
`Hsub` with `Qc := sub_call_complete` — and §7c is the three-line
`e_sub_call_order_sind` application.  The flex half is §8c.20's table
verbatim; the sub half dispatches as `e_sub_call_impl_equation_1` does
(mode, then `NM`, then the shape column that arm keys on).

**Three rows carry the level; the rest is dispatch.**

1. ⭐ **`SI-Flex-Solve`** — §5, `e_sub_flex_solve_realign`.  The row invents
   TWO names at once and §8c.20's chain is right, but the reason is worth
   keeping: the second pair's LEFT column is `swap_atom ad a1 bd`, not
   `bd`, because the first transposition may already have moved `bd` —
   namely when `bd = a1`, where it lands on `ad`.  `remember` that atom and
   the rest is `swaps_atoms_add` twice plus `swaps_atoms_notin`.
2. ⭐ **`SI-ForallR`** — pre-swap the derivation's opener onto
   `supply_fresh S0`, recurse, then read the junk block back off the
   runner's own answer.  That last step is a new decomposition lemma,
   `split_at_tvar_complete` (§5b, prop_dec.v §6's shape): on the context
   the rule produces, `split_at_tvar` SUCCEEDS and returns the rule's own
   two pieces.  ⚠️ It needs `uniq` of the runner's OUTPUT context, which
   comes from `e_sub_sub_flex_sound`'s second conjunct applied to the
   recursive answer — the scan stops at the FIRST marker, so without
   uniqueness it could split somewhere else.
3. ⭐⭐ **`SI-ForallL`** — pre-swap the opener, then `e_extract_det`
   (prop_extract_det.v §9) moves everything the extraction invented.  The
   `e_extract_impl` call is killed with prop_run_complete.v §5c's `kill_*`
   recipe off level 4's `e_extract_impl_complete`, whose two supply-threaded
   halves come free from `e_extract_inv` (`e_extract` has ONE rule).

#### ⛔⛔ AND LEVEL 4's HEADLINE HAD A PREMISE THAT IS UNSATISFIABLE AT ITS ONLY CONSUMER

`e_extract_impl_complete` (prop_look_pair.v §4) carried

```coq
  add α (ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] ftvar_in_aenv Θ0
```

("scoping", §8c.9's fourth pass).  ⛔ At `SI-ForallL` the extraction's `α`
IS the rule's own FRESH opener — `a_sub__forall_l` states
`α ∉ ftvar_in_aenv Θ0 ∪ ftv P ∪ ftv P0` — so `α ∈ ftvar_in_aenv Θ0` is not
merely unproved, it is UNSATISFIABLE there, and `e_extract_*_complete` was
unusable at the only place that calls it.  ⚙ **The lemma was never wrong**;
it was too weak to apply, and dropping the hypothesis makes it strictly
stronger, so no existing use is disturbed.  The level's own note ("what the
level owes upward") listed the two e-derivation halves and treated the
scoping premise as free; it is not.

✅ **The repair is local to that one proof and RETIRES the premise.**  The
premise existed only to put `V := add α (ftvar Θ0 ∪ ftv P ∪ ftv P')` inside
`ftvar_in_aenv Θf1` / `Θf2`, which the b-core's two scoping premises
demand.  So cut the RIGID ENRICHMENT at the CONTEXT instead of at the input
supply:

```coq
  set (Δr1 := rigids (Sh1 ∖ ftvar_in_aenv Θ0)) in *.        (* was Sh1 ∖ Sh0 *)
  set (Δr2 := rigids (lk_supply r1 ∖ ftvar_in_aenv Θ0)) in *. (* was ∖ S0 *)
```

Now each side's WHOLE supply is visible in that side's enriched context, so
`V ⊆ Sh0 ⊆ Sh1 ⊆ ftvar Θf1` and the scoping premises are immediate.  ⭐ The
one proof step that had to change is `flex_agree_rel nil V Θf1 Θf2`: the
old script peeled both rigid prefixes by FRESHNESS (`x ∉ dom Δr`), which
now fails for exactly the names the enrichment was widened to cover — peel
them by RIGIDITY instead (`a_flex_tvar_rigid_prefix_iff`, which holds
unconditionally), and only the two BLOCK prefixes still need `x ∉ dom Ξ`
(free: `V ⊆ Sh0` and the blocks are fresh for `Sh0`).  Everything else is
set arithmetic through two new named facts, `Sh1 [<=] ftvar Θf1` and
`lk_supply r1 [<=] ftvar Θf2`.

⚙ This is a mech-internal weakening of a lemma statement — no rule changed,
so there is no `PAPER-GAPS` entry.  `e_extract_run_complete` drops the
premise too.  ⚠️ Both lemmas had NO consumers before today, which is why
the premise survived the level's own closure.

#### ⚙ Traps paid in §7, none of them in §8c.20's list

- ⚠️⚠️ **An `Ltac` body resolves a bare identifier at DEFINITION time.**  A
  tactic that factors a row cannot mention `S0`, `Θ0`, `P0`, `Qd` … — they
  must be parameters — and it cannot mention a name its OWN `destruct as`
  pattern introduces.  The `(ty, TC)` arm's `SI-ForallL` branch therefore
  reads its `Q` off the goal with a `lazymatch` on the `e_extract_impl`
  call.  ⚠️ And `ltac:(…)` in a tactic-ARGUMENT position becomes a
  tacvalue, not a term ("should be bound to a term but is bound to a
  tacvalue") — pass a real term, or make the tactic prove the thing itself
  (`ck_true` / the `SI-ForallL` guard's three-way `solve`).
- ⚠️⚠️ **`apply andb_true_intro` unifies up to delta.**  On
  `ghost_free_ck (P → Q) = true` it happily UNFOLDS the fixpoint and splits
  a goal the `_ck_complete` lemma answers whole, so
  `repeat (apply andb_true_intro; split); solve […]` fails at every arrow
  column.  Try the LEAF first: `repeat (ck_leaf || (apply andb_true_intro;
  split))`.
- ⚠️ **Do not `rewrite` the runner's own output into a decomposed form.**
  `SI-ForallR`'s answer carries an Equations obligation whose TYPE mentions
  `sb_ctx r`; rewriting `sb_ctx r` in the goal retypes the obligation and
  the `Some (exist _ p Hp)` branch no longer typechecks.  State the
  decomposition lemma with the equation as a PREMISE
  (`Θ = Ξ ++ (α ~ tvar) ++ Θ'` → `split_at_tvar α Θ = Some r ∧ …`) so its
  conclusion is about the runner's own term.
- ⚠️ `Set Implicit Arguments` leaves a context that occurs only under `++`
  EXPLICIT (non-strict position), so a caller would have to count
  underscores — pin the prefix with `Arguments` instead
  (`e_sub_flex_solve_realign`, `split_at_tvar_complete`).

#### ⛔ WHAT IS LEFT

Levels 1–6 are closed — look, both solve layers, the cstr fold, extract,
the consistency trio and now subtyping.  Above subtyping the campaign has
never numbered its rungs: what is left is the `e_pat` and `e_typing`
runners, whose remaining prerequisites are §8c.2's (2b) checklist (output
lc for `e_pat`/`e_typing`, and the relation-side shape facts).  ⚠️ §8c.9's
closing note still stands for whoever writes them: `e_extract_*_complete`
takes its two halves as supply-threaded e-derivations, and a FOLD analog of
transport 5 does not exist — at level 6 the halves came free because
`SI-ForallL` already carries an `e_extract` derivation to invert, which is
not something a raw a-side construction can supply.


### 8c.22 ✅ §8c.2's (2b) IS CLOSED — the run preserves `lc_aenv`, and every runner's output is locally closed (2026-08-18)

✅ **`make coq` rc=0, `README.v` 32/32, zero `Admitted`/`Axiom`.**
`frost/ext_algo/prop_run_invariants.v` §4, plus one new coercion fact.

**The fork (2b) left to the next session was decided as the DIRECT
invariant** (user's call: *"(2b) is a minor problem, choose whichever is
simpler to prove"*).  The alternative — compose the bridge with
`a_pat_sound` / `a_typing_sound`, which already return output
well-formedness — drags soundness' four premises (`{{ ⊢ Θ0 }}a`,
`a_wf_pskl`, mode compatibility, `{{ Θ0 ⊢ᵉ e }}a`) into every completeness
motive above, and each has to be re-established at every recursive call.
The direct invariant costs ONE context hypothesis, `lc_aenv Θ0`, beside the
`aenv_defs_mono Θ0` the tree already threads.

⭐ **And it is cheap for a reason worth recording**: `lc_abind`
(algo/prop_inc.v) sends `tvar`, `flex_mono` AND `flex_mono_def` to `True`,
so every block the algorithm generates is `lc_aenv` outright and only the
rows that push a TERM VARIABLE have anything to discharge.  ⚙ The predicate
is not new — it is what `a_wf_aenv_lc_aenv` projects a well-formed context
to; what is new is that the RUN preserves it.

| § | what |
|---|---|
| §4 kit | `lc_abind_*`, `all_flex_mono_lc_aenv`, `a_suffix_lc_aenv`, `lc_aenv_binds` |
| §4a | `e_assign_unify_consis_env_lc` / `e_consis_env_lc`; `e_sub_sub_flex_env_lc` / `e_sub_env_lc` |
| §4b | `e_split_lc`, `e_split_env_lc` |
| §4c | `e_pat_lc_env` (+ `e_pat_lc` / `e_pat_env_lc`) |
| §4d | `e_typing_lc_env` (+ `e_typing_lc` / `e_typing_env_lc`) |

#### ⭐ The one thing the typing half needed, and it did not exist

`ptyp_to_pskl_lc_inv` (prop_coercions.v): local closure comes BACK through
the painting.  The typing rules pin their subtyping and splitting premises
to `⌈A⌉`, so what those rows hand the caller is `lc_pskl ⌈A⌉` while what the
caller owes is `lc_ptyp A`; only the forward direction was in the tree.

⚠️ **Neither induction works directly.**  On `A`, the `∀` row's IH is about
the BODY while the goal is about its OPENING; on the `lc_pskl` derivation,
the index is the IMAGE, so inverting it never exposes `A`'s own
constructor.  Go through `degree`, which is indexed by binder depth and
therefore structural: `degree_ptyp_to_pskl_inv`, then lngen's
`lc_ptyp_of_degree` / `degree_pskl_wrt_pskl_of_lc_pskl`.

#### ⚙ Two traps

- ⚠️⚠️ **`eauto` indexes hints by the head symbol of their CONCLUSION.**
  These scripts run with `lc_aenv` UNFOLDED (the `Forall` surgery needs it),
  so a hint concluding `lc_aenv …` is never even tried — hence the
  `all_flex_mono_lc_forall` / `a_suffix_lc_forall` restatements, whose head
  is `Forall`.  The same reason the `Forall_cons` leaves need
  `lc_abind_tvar` &c. in the `using` list: the residual goal is
  `lc_abind abind_tvar`, not `True`.
- ⚠️ **`ltac:(assumption)` as a lemma argument runs against the lemma's own
  evar.**  `ptyp_to_pskl_lc ltac:(assumption)` fails (the index is still
  `?A`) where `ltac:(apply ptyp_to_pskl_lc; assumption)` succeeds, because
  the latter runs at a goal the consumer's argument type has already fixed.
  Same species as prop_extract_det.v's "derivation before the size premise".
- ⚙ `binds`, `lc_aenv` and `lc_abind` are all DEFINITIONS, so none of
  `lc_aenv_binds`' three indexes is a strict implicit; the prefix is pinned
  with `Arguments` rather than counted.

#### ⛔ What (2b) still leaves for levels 7/8

The SHAPE facts are NOT proved as standing invariants, and level 6 says they
should not be: `SI-ForallR` got `split_at_tvar`'s decomposition from the
RULE (transported along the chain), not from an invariant about outputs.
Expect the same at `AT-AbsCheck`'s `split_at_tvar` and at the
`pskl_readback` positions — the rule pins them.  What genuinely needed an
invariant was local closure, and that is what §4 is.

### 8c.23 ⭐⭐⭐ LEVELS 7 AND 8 ARE CLOSED, AND SO IS (2e) — THE CAMPAIGN IS FINISHED (2026-08-19)

✅ **`make coq` rc=0, `README.v` 33/33 (the new entry is §VI, DECIDABILITY),
zero `Admitted`/`Axiom` in `frost/`, `cex/`, `test/`.**  Three new files'
worth of work, all Qed and `Closed under the global context`:

| headline | file | what it says |
|---|---|---|
| `e_split_impl_complete` | prop_pat_complete.v §4 | the splitting runner answers wherever the relation derives |
| `e_pat_impl_complete` / `e_pat_run_complete` | §7 | the same for SKELETON INFERENCE |
| `e_typing_impl_complete` / `e_typing_run_complete` | prop_typing_complete.v §5 | and for TYPE INFERENCE |
| `e_typing_dec` / `e_typing_dec_init` | prop_run_corollaries.v §4 | ⭐⭐ DECIDABILITY |

#### ⭐ The level's good news, and it was checked before any code was written

**The runners above subtyping are INDEPENDENT.**  `e_pat_impl` calls
`e_sub_impl`, `e_split_impl` and itself; `e_typing_impl` calls those three
and itself.  Neither calls the other, so §8c.4's tagged single-block
workaround is NOT needed here: each is one `Equations` with its own order,
and completeness is one order-induction per runner.

⭐ **And §1's hand-written induction principle has no counterpart.**
`e_pat_order` and `e_typing_order` are conjunction-free ONE-CONSTRUCTOR
orders, so Coq's own `_ind` already doubles every recursive premise — the
exact shape prop_sub_complete.v §1 had to write by hand for
`e_sub_call_order`, whose premises carry `/\`.

#### ⭐⭐ What was new above level 6, and it is one thing

The four abs rows bind a TERM variable.  So the chain that realigns a
derivation onto the runner's rails has to act on the SUBJECT too, and the
e-side equivariance for that did not exist:

- `prop_pat.v` §4 — `e_split_supply_respect` / `e_pat_supply_respect` and
  `e_split_swap` / `e_pat_swap`, the ∃-shaped twins of algo/prop_swap.v
  §16's `a_split_swap` / `a_pat_swap`.
- `prop_typing.v` §3 — the same for `e_typing`.
- `prop_pat_complete.v` §1 — `swaps_exp` and its two lemmas,
  `swaps_notin_eq`, `swaps_atom_dodge`, the `swaps_abind`/`swaps_aenv`
  var-marker clauses, and the `e_split_swaps` / `e_pat_swaps` iterations.

#### ⭐ THE DISPATCH IS OVERLAP-FREE, and stating the inversions as
#### DISJUNCTIONS is what cashes it

Nine of the ten `e_pat` rows and eight of the eleven `e_typing` rows are
keyed by the SUBJECT's head constructor.  The cells that are not:

- `exp_abs` / `exp_abs_anno` at `e_pat`: the two rows are separated by
  `m <> mode_tc`.
- `exp_abs` / `exp_abs_anno` at `e_typing`: THREE rows, separated by
  `m <> mode_tc` and then by whether the pattern is `⌈∀A0⌉`.  ⭐ The check
  cell needs no new side condition: at `⌈∀A0⌉` the BASE row would need a
  SPLIT of `pskl_all_syn ⌈A0⌉` and `e_split` has no ∀ row, so the STEP row
  is the only one — which is what the runner picks (`pskl_readback_all`).
- `exp_var_f`: the two `AP-Var` rows are separated by the BINDING's payload
  sort, and `uniq Θ0` makes that binding unique.

⭐ **Stating each such cell's inversion as ONE DISJUNCTION** (rather than as
two or three lemmas with discriminating premises) is what lets each branch
of the mode/readback dispatch kill the arms it does not want by
`congruence`, WITHOUT first having to produce the discriminating premise —
and the check arm hands back `P0 = pskl_hole` (resp. `P0 = ⌈∀A0⌉`), which is
what makes the runner's clause reachable at all.

#### ⭐⭐ ONE PIECE OF UPSTREAM METATHEORY WAS MISSING: `e_guess_mono_det`

`AT-Abs` runs `guess^TY`, the runner runs its own copy, and the two invent
different atoms — so the level needs `guess^TY` DETERMINISTIC UP TO A
FRESH-PAIR CHAIN (prop_typing_complete.v §1).  Every other recursive call in
these two files is a runner whose completeness already comes in that form.

⚙ **Its COVERAGE hypothesis (`ftv P ⊆ S0`) is load-bearing, not
decoration**: at a VARIABLE subject the row returns `α` itself, so without it
the answer could mention a name the chain is free to move.  Every call site
has it — `AT-Abs` guesses on a SPLIT's domain, and prop_pat.v §2 bounds that
by the split's output supply.

⚙ It sits in the level-8 file rather than in prop_guess.v because the
`swaps_*` family it is stated over (prop_solve_det.v §2) is downstream of
that file — prop_solve_det.v §3's own precedent for `ptyp_to_pskl_close`.
Alongside it: `e_guess_mono_swaps`, the block's `lc_aenv` / `aenv_defs_mono`
(bare flexibles, so both are immediate), `e_guess_mono_lc_type`, and
`ptyp_to_pskl_inj` — the painting is a constructor relabelling, and that is
what identifies the ∀-body the runner READ BACK with the one `AT-AbsCheck`'s
STEP rule existentially names.

#### ✅ (2e) IS CLOSED TOO — and read its SCOPE before citing it

`prop_run_corollaries.v` gains §3 (the completeness half at the entry point,
where every side condition but local closure of the two inputs is
`reflexivity`) and §4, the decidability corollary §5 of this document
predicted, verbatim: case on the runner's answer; `Some r` is a derivation by
soundness, `None` would be contradicted by completeness.  ⭐ The step that
makes it work is the runner being TOTAL, which is why termination had to come
first.

⚠️⚠️ **What `None` refutes is a derivation of the SUPPLY-THREADED relation
`e_typing`** — the relation every rung of the ladder is stated over.  The
POSITIVE branch composes all the way down to the paper's declarative
judgement (§1/§2 of that file); the NEGATIVE branch stops at `e_typing`,
because the converse of the bridge — `a_typing` ⟹ `e_typing` at a covering
supply — is NOT proved.

⛔ **That converse is the one thing the campaign still owes**, and it is not
an oversight: it is §8c.3's obstruction, unchanged.  A derivation opens its
binder wherever it likes and the threaded rules open at the SUPPLY, so a
structural induction on the `a_*` derivation would need its IH at a
TRANSPOSED sub-derivation, which is not a subterm — which is exactly why the
campaign quantified over `e_*` throughout.  ⭐ Closing it is one more
order-induction of the same shape as levels 7/8, and the a-side equivariance
it needs (`a_pat_swap` / `a_typing_swap`, algo/prop_swap.v §16) already
exists.  ⚙ Nothing else is missing on the declarative side:
`a_typing_complete` and its closed-program corollaries are closed
(README.v §III).

#### ⚙ Traps paid, none of them new in kind

- ⚠️⚠️ **An `fsetdec` inside an `ltac:` ARGUMENT does not return** — the
  recursive call's own `S0` is still an EVAR there, so the search is
  unbounded.  Every coverage side condition is a NAMED hypothesis.  (The
  feedback rule already says this; it cost a >150 s compile with no error to
  rediscover.)
- ⚠️⚠️ **An `fsetdec` over six or seven set variables does not return
  either.**  The abs rows' coverage is assembled SUMMAND BY SUMMAND, four or
  five variables at a step.
- ⚠️⚠️ **A `[=]` lemma cannot be `rewrite`n UNDER `swaps_atoms`**: there is no
  `Proper` instance and the failure reads "setoid rewrite failed: UNDEFINED
  EVARS".  Go through `swaps_atoms_cong` explicitly.
- ⚠️ **§8c.21's fourth trap, at four new places.**  A recursive answer's
  projection must NOT be rewritten into a decomposed form; §4b of
  prop_pat_complete.v and §2b of prop_typing_complete.v restate
  `arrow_split`, `ptyp_arrow_split`, `split_at_key_skl` / `_typ` and the two
  readbacks with the DECOMPOSITION AS A PREMISE, and `kill_dec` destructs the
  goal's own call.  `AT-AbsCheck`'s STEP row must not rewrite its `close`
  into the goal either, and `AT-App` needs a COPY of the function's spec
  proof before rewriting its arrow shape into it.
- ⚠️ `Set Implicit Arguments` makes everything under `++` (and under
  `ptyp_to_pskl`) explicit — a non-rigid position — so every `_complete_eq`
  lemma pins its prefix with `Arguments`.
- ⚙ **An `all: ( … )` block is a tactic INVOCATION, not an `Ltac`
  definition**, so names its own `destruct as` patterns introduce resolve
  fine.  That is what lets the two non-check abs clauses share one script
  instead of being written twice.
- ⚠️ `bool_true_ty` freshens to `Hb0` on its SECOND use in a case, so a later
  `destruct … as [Ha0 Hb0]` collides; the scripts use `Hka`/`Hkb`.
- ⚠️ The tree's meta-level substitution notations claim the `{ term …`
  prefix, so Coq's own `sumbool` notation does not parse — §4's statements
  are written in APPLICATION form (`sumbool A B`), the same trap
  def_guess_impl.v's header records for `sig`.


### 8c.24 ⛔ THE LIFT, `a_*` ⟹ `e_*` — the campaign's LAST DEBT, SCOUTED AND DESIGNED (2026-08-19)

⛔⛔ **SUPERSEDED IN ITS PLAN BY §8c.25 (2026-08-19) — READ THAT FIRST.**
The MOTIVE below is right for `guess^TY` and WRONG for every block above
it (a chain is a function; the rules above the guess leak binders into
their outputs), the LOOK rung listed below as "next" was already proved in
§8c.9, and the whole solve layer has since landed relationally.  What stays
valid here: the technique (induct so the `a_` derivation is a hypothesis),
the two premises `guess^TY` needs, and the three performance rules.

🟡 **THE SCOUT HAS LANDED; TEN BLOCKS REMAIN.**
`frost/ext_algo/prop_lift.v` §2 is Qed and `Closed under the global context`:
`e_guess_mono_lift` and `e_guess_lift`, plus §1's `close` rename fact.  That
is `guess^TY` — the block with all three hard shapes — so the MOTIVE below is
no longer a proposal but a validated one.  What is left is look, solve, cstr,
extract, consis, sub, split, pat and typing, in that order.

#### Why it is the last debt

§8c.23's decidability corollary refutes a derivation of the SUPPLY-THREADED
`e_typing`, because that is the relation every rung of the ladder is stated
over.  The chain that would make the extracted program SOUND AND COMPLETE
for the paper's DECLARATIVE system is

| link | status |
|---|---|
| `d_` ⟹ `a_typing` | ✅ `a_typing_complete_decl_infer` / `_check` (README §III) |
| `a_typing` ⟹ `e_typing` | ⛔ **THIS** |
| `e_typing` ⟹ `run = Some` | ✅ `e_typing_run_complete` (level 8) |

and the soundness direction is already closed end to end
(`e_typing_run_sound_infer` / `_check`).

#### ⭐⭐ THE TECHNIQUE — settled, and both halves of it are affordable now

A structural induction on the `a_*` derivation FAILS at every row that
invents a name: the `a_` rule chose its atom freely, the `e_` rule must
choose one fresh for the SUPPLY, so the IH is wanted at a TRANSPOSED
sub-derivation, which is not a subterm.  That is §8c.3's obstruction, and it
is why the campaign quantified over `e_*` in the first place.  Two repairs
work:

- ⭐ **Induct on the e-side ORDER** (§8c.3's own recommendation).  The orders
  are total and unconditional, so the `a_*` derivation stays an ordinary
  HYPOTHESIS — and a hypothesis may be transposed freely with
  algo/prop_swap.v's single-swap equivariance, which covers all fourteen
  judgements (`a_looksub_lookeq_swap`, `a_solve_sub_eq_swap`,
  `a_solve_cstr_swap`, `a_extract_swap`, `a_assign_unify_consis_swap`,
  `a_sub_sub_flex_swap`, `a_split_swap`, `a_pat_swap`, `a_typing_swap`,
  `a_guess_mono_swap`).  Use this for look / solve / cstr / extract / consis
  / sub / pat / typing.
- ⭐ **A plain syntactic measure** where one exists — `size_pskl` of the
  subject for `guess^TY` (the ∀ row opens at a variable, which preserves
  size, and the `pskl_all_syn` node pays the `S`).

⚙ Either way the conclusion is EXISTENTIAL up to a CHAIN, exactly as the
levels' motives are: the `e_` derivation's outputs are `swaps_*` images of
the `a_` derivation's.

#### ⛔⛔ THE TWO REAL OBSTRUCTIONS THE SCOUT FOUND — read these first

**(1) `a_guess_mono__arrow` does NOT thread.**  Both halves run at the SAME
`Θ`, so the two blocks may COLLIDE — which is exactly why `AT-Abs` carries
`uniq (αs ++ Θ1)` (docs/REPORT-postclosure-audit.md §1.3) — while
`e_guess_mono` threads and its block is `uniq` outright.  NO single chain
sends a colliding block to a `uniq` one.  ⇒ The guess lift must take
`uniq Ξ` as a premise.  It is available at the only consumer: `AT-Abs`
already carries it.

**(2) THE `a_`-SIDE BLOCKS ARE NOT FRESH FOR THE SUPPLY.**  `a_guess_mono`'s
invented atoms avoid `ftvar_in_aenv Θ` and nothing else; the `e_` side needs
them off `S0`.  Every "this premise's chain fixes that premise's data" step
in the arrow row turns on it, and without it the row does not close.
⇒ The lift must take `dom Ξ ∩ (S0 ∪ L) [=] empty` as a premise, and the
CONSUMER discharges it by PRE-FRESHENING.  ⭐ That is affordable precisely
because the consumer inducts on the ORDER: the guess sub-derivation and the
BODY sub-derivation are both plain hypotheses, so one application of
`a_guess_mono_swap` and one of `a_typing_swap` — along the SAME chain — move
`(αs, A)` and the body's context together, and the chain fixes `Θ1` because
`a_guess_mono_generated_fresh` puts `dom αs` off `ftvar_in_aenv Θ1`.

#### ⭐⭐ THE MOTIVE, AS BUILT — and it carries TWO avoid-sets

```coq
Lemma e_guess_mono_lift_n : forall n P, size_pskl P <= n ->
  forall Θ Ξ A, a_guess_mono Θ P Ξ A -> uniq Ξ ->
  forall S0 (L K : atoms),
    ftvar_in_pskl P [<=] S0 ->
    dom Ξ ∩ (S0 ∪ L) [=] empty ->
    S0 ∩ K [=] empty ->
  exists S1 ps,
    e_guess_mono S0 P S1 (swaps_aenv ps Ξ) (swaps_ptyp ps A)
    /\ (forall a b, In (a, b) ps -> a `in` dom Ξ /\ b `notin` L)
    /\ dom (swaps_aenv ps Ξ) ∩ L [=] empty
    /\ S1 ∩ K [=] empty.
```

⭐ **`L` and `K` do different jobs and ONE SET CANNOT DO BOTH.**  `L` is
dodged by the chain's TARGETS and by the IMAGE BLOCK — that is what lets one
premise's answer be fixed by the other premise's chain.  `K` is dodged by the
OUTPUT SUPPLY — that is what lets the arrow row's SECOND call know the
right-hand block is still off the threaded supply.  Demanding a single set be
disjoint from both is CONTRADICTORY, because the image block LIVES in the
output supply.  ⚙ The arrow row instantiates them as
`L1 := L ∪ dom Ξ2 ∪ S0`, `K1 := K ∪ dom Ξ2` on the left, and
`L2 := L ∪ dom (swaps_aenv ps1 Ξ1) ∪ S1`, `K2 := K` on the right.

⭐ The SOURCE column ranging over `dom Ξ` is the other half of the trick: it
is what the ∀ row uses to know the recursive chain does not move its own
witness (choose the witness outside `dom Ξ`), so the third conjunct an
earlier draft carried — "targets land inside the image block" — is not
needed.

⭐ **THE ∀ ROW IS SHORTER THAN IT LOOKS.**  `close` does not remember which
atom it abstracted, so the transposition that moves the `a_` rule's witness
onto a supply-fresh one does NOT appear in the conclusion's chain at all.
The fact, and its proof route (four lines, no hand induction — a swap at a
fresh target IS a substitution, a substitution IS an `open` of a `close`, and
`close` of that `open` is the identity):

```coq
Lemma close_ptyp_wrt_ptyp_rename : forall A β β',
  β' `notin` ftvar_in_ptyp A ->
  close_ptyp_wrt_ptyp β' (swap_ptyp β β' A) = close_ptyp_wrt_ptyp β A.
Proof.
  intros A β β' Hβ'.
  rewrite (swap_ptyp_as_subst β β' A Hβ').        (* algo/prop_swap.v:693 *)
  rewrite subst_ptyp_in_ptyp_spec.                (* prop_ln.v            *)
  apply close_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp.
  rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp. clear - Hβ'. fsetdec.
Qed.
```

⚙ Everything else the arrow row needs comes off the E-SIDE invariants of the
first call's answer, not off the `a_` side: `e_guess_mono_generated_ftvar`,
`_generated_in_supply`, `_block_fresh`, `_ftv`, `_supply_grows`.

#### ⛔ THE SIZE OF THE JOB — do not underestimate it

Sixteen judgements, 120 `a_*` rows:

| block | rows |
|---|---|
| `a_guess_mono` / `a_guess` | 6 + 2 ✅ **DONE** |
| `a_lookeq` / `a_looksub` | 11 + 8 |
| `a_solve_eq` / `a_solve_sub` / `a_solve_cstr` | 12 + 9 + 3 |
| `a_extract` | 1 |
| `a_assign` / `a_unify` / `a_consis` | 8 + 6 + 14 |
| `a_sub` / `a_sub_flex` | 9 + 7 |
| `a_split` / `a_pat` / `a_typing` | 3 + 10 + 11 |

Each row is SHORTER than its completeness counterpart — there is no runner,
no `Equations` obligation, no boolean test, no decomposer, and above all NO
DETERMINISM: the lift CHOOSES the `e_` rule (the one the `a_` derivation
used), so none of `e_extract_det`, `e_guess_mono_det` or the five dispatch
guards is needed.  What replaces them is the freshness algebra above, and it
has to be got right ONCE PER BLOCK.  Budget it like levels 6–8, i.e. as its
own campaign, and do it bottom-up: guess, look, solve, cstr, extract, consis,
sub, split, pat, typing.

#### ✅ What the composition looks like once the lift lands

```coq
Corollary e_typing_run_complete_decl_infer : forall e B,
  {{ nil ⊢[ mode_ti ] e ⦂ B }}d ->
  exists r, e_typing_run (… entry supply …) mode_ti nil pskl_hole e = Some r.
```
by `a_typing_complete_decl_infer` → `e_typing_lift` → `e_typing_run_complete`,
and the decidability corollary's NEGATIVE branch then refutes the DECLARATIVE
judgement rather than the threaded one.  That is the statement README.v §VI
should carry when it lands.

#### ⚙ WHAT THE SCOUT COST, AND WHERE — measure before writing the next block

`e_guess_mono_lift_n` is 11 s.  Its first draft was **>120 s with no error**,
and `coqc -time` put the whole of it in two places, both the documented
traps:

- **40 s in the `ltac:`-ARGUMENT `fsetdec`s** of the two `IHn` applications.
  Every side condition of a recursive call is now a NAMED hypothesis
  (`HcovP`, `HΞ1`, `HK1`, …) asserted before the call.
- **10 s + 3.7 s in two `fsetdec`s over EIGHT set variables.**  Each is now
  split into two or three `assert`s of at most five.

⚠️ And one that is new: the ∀ row draws its witness against SEVEN sets at
once, so every use of that freshness goes through `destruct_notin; auto`, not
through an `fsetdec` over the seven-fold union.  Expect the same at every
binder row above.

⚙ Write the next block with those three rules from the start; they are not
optimisations, they are the difference between 10 s and not returning.

### 8c.25 ⭐⭐⭐ THE LIFT, SECOND PASS — THE LOOK RUNG WAS ALREADY CLOSED, THE CHAIN CURRENCY DIES ABOVE THE GUESS, AND THE WHOLE SOLVE LAYER NOW LIFTS (2026-08-19)

✅ **`make coq` rc=0, `README.v` 33/33, zero `Admitted`/`Axiom`.**
`frost/ext_algo/prop_lift.v` grows from 377 to ~1570 lines (21.6 s), and
every one of its seven new headlines is `Closed under the global context`:

| § | headline | what it lifts |
|---|---|---|
| §3 | `e_looksub_lift` / `e_lookeq_lift` | the COLLECTION, 19 rows — **by instantiating an existing lemma** |
| §4 | `a_guess_mono_rel_e` / `a_guess_rel_e` | `guess^TY` again, in the REL currency |
| §5 | `a_solve_eq_rel_e` | the eq-solve, 12 rows |
| §6 | `a_solve_sub_rel_e` | the sub-solve, 9 rows |
| §7 | `a_solve_cstr_rel_e` | the constraint fold, 3 rows |

So §8c.24's costed plan is discharged through `cstr`: guess, look, solve,
cstr are done and 46 of the 120 rows are behind us.

#### ⛔⛔ FINDING 1 — §8c.24's CHAIN CURRENCY CANNOT REACH ANY BLOCK ABOVE THE GUESS

§8c.24 proposed one motive for the whole campaign: the `e_` outputs are
`swaps_*` IMAGES of the `a_` outputs, along a chain `ps`.  ⛔ **That is
available at `a_guess_mono` and nowhere above it**, and the reason is
structural, not a proof difficulty:

- A chain is a **FUNCTION** on atoms.  `rel_pskl` (prop_solve_det.v §1) is
  deliberately a **RELATION**, and its header already says why for the
  guess: `a_guess_mono__arrow` runs both halves at the same `Θ`, so one
  derivation may guess the SAME flexible for two holes.
- §2 could still use a chain because **`a_guess_mono` LEAKS NOTHING**: its
  ∀ row closes its witness away, so every atom the derivation invents lands
  in `dom Ξ`, and `uniq Ξ` — one premise, available at the only consumer —
  makes the columns distinct.
- ⚠️ **ALL FIVE of the collection's ∀ rows LEAK their binder into `𝒞`**
  (def_look.v's header; `a_looksub_lookeq_ftv`'s three target-opening
  rows), and `SS-ForallR` leaks its opener into the solve's YIELD **by
  design** (def_rules.v:625-638).  A leaked binder is NOT in `dom Ξ`, so no
  strengthening of `uniq Ξ` can see it — and `LE-Arrow`'s two halves run at
  the SAME `Θ`, so ONE left atom can be a leaked opener in one half and a
  generated flexible in the other.  The e-side keeps those apart (opener
  drawn at `S0`, flexible at `S1 ⊇ add opener S0`), so that one left atom
  needs TWO right images.  **No chain, at any premise, supplies them.**

⇒ Everything from the collection up is stated over `rel_pskl` /
`rel_a_cstrs` at a pair list ρ that GROWS, with the blocks read off as
`flex_pairs_l ρn` / `flex_pairs_r ρn`.  §2's chain form is kept: it is
what a consumer holding `uniq Ξ` wants (`AT-Abs`), and §4 is the same fact
in the currency the solve layer needs.

#### ⭐⭐⭐ FINDING 2 — THE LOOK RUNG WAS ALREADY PROVED, IN §8c.9, AND NOTHING NOTICED

`prop_solve_rel.v` §7's **`a_looksub_lookeq_rel_e`** — campaign §8c.9's
"transport 5, the hygienic rederivation" — is stated **a → e** already: an
`a_looksub`/`a_lookeq` derivation transports to an `e_looksub`/`e_lookeq`
derivation over any supply covering side 2.  At `ρ = nil` (where
`rel_pskl_refl` makes both sides the same skeleton and `flex_agree_rel` is
two `reflexivity`s) it **IS** the lift, and §3 is thirty lines of
instantiation for the pair.

⚙ The other four transports of that file (§3-§6, guess / eq-solve /
sub-solve / fold) are a → **a**, which is why §4-§7 above had to be
written — but they are the exact templates, row for row, and each took one
compile to land.  ⚠️ **The user's own standing rule caught this** ("grep
the completeness files for existing transports before mirroring to a new
level"); it is worth one grep per block for the six blocks that remain.

#### ⚙ WHAT CHANGES BETWEEN THE a → a TEMPLATE AND THE a → e COPY

Three edits, mechanical once seen:

1. **The avoid-set `L` and its two conclusions DISAPPEAR.**  On the a-side
   the caller had to be told `uniq Ξ2` and `dom Ξ2 ∩ L [=] empty`;
   threaded, both are theorems of the e-side derivation alone
   (`e_solve_sub_eq_block`, `e_guess_mono_block_fresh`), so the arrow rows'
   bookkeeping collapses to "the supply grew".
2. **Every invented atom is drawn against the SUPPLY** — `atom_fresh S0`
   in place of `atom_fresh (ftvar_in_aenv Θ2 ∪ …)`.
3. ⭐ **ONE new premise, `dom Θ2 [<=] S0`.**  Side 2's openers need `∉ S0`
   for the rule and `∉ dom Θ2` for `flex_agree_rel_push_tvar_pair`; the
   supply cannot supply the second without it.  ⚙ `dom`, NOT
   `ftvar_in_aenv`: `dom` is the version the arrow rows can re-establish
   for `Ξ2a ++ Θ2` out of the e-side block facts alone.

⚠️ And the coverage is **three separate premises**
(`dom Θ2 [<=] S0`, `V ∪ cols_r ρ [<=] S0`,
`ftvar P2 ∪ ftvar Q2 [<=] S0`), never one union — written as a union every
later `fsetdec` would face six set variables, which is §8c.23's cliff.

#### ⛔⛔ FINDING 3 — THE NEXT ROW, `a_extract`, IS **FALSE** AS A LIFT

`a_extract` has ONE rule and it composes §3, §7 and §4, so it looks like
three `destruct`s.  It is not.  The full configuration, the four solve rows
that fail to apply, and what the repair has to be are written at the end of
`prop_lift.v` (the `⛔⛔ WHAT THE NEXT BLOCK OWES` box) — read it there, it
is the live statement.  In brief:

- `LE-Arrow` can hand back `𝒞 = [eq 1 ; eq γ ; eq γ]` with `Ξ = (γ ~ ⌢)`,
  where one `γ` is a LEAKED OPENER of one half and the block's `γ` is the
  OTHER half's invented flexible.
- Side 1's fold sees that leaked `γ` as FLEXIBLE (it is in `Ξ`) and fires
  `SE-FlexR`; side 2's `γ1` is bound nowhere — `e_looksub` discards its
  openers, exactly as `type.ml` does — and `1 ∼ γ1` matches NO `e_solve_eq`
  row.  The threaded fold is STUCK where the unthreaded one runs.
- ⇒ no `flex_agree_rel` between `Ξ ++ Θ0` and `Ξ2 ++ Θ2` exists, and that
  is precisely §7's premise.

✅ **MACHINE-CHECKED (2026-08-19): `cex/probe_extract_conflated_opener.v`**,
four lemmas, all Qed and assumptions-closed.  §1 builds the conflating
collection (`Ξ = γ̂`, `𝒞 = [≐1, ≐γ, ≐γ]`, first `γ` invented by LE-FlexR,
second leaked by LE-ForallInh — **and both rows' side conditions read
`γ ∉ {α, β̂}`, so nothing separates them**); §2a runs the a-side fold on it;
§2b shows that fold is STUCK once the opener is any atom the context does
not bind; §3 builds the THREADED collection at the same inputs and it
returns `[≐1, ≐γ1, ≐γ2]` with `γ2 ∉ dom Ξ2`; §4 composes — the a-side fold
runs and the threaded one cannot, at one configuration.  ⚙ The threaded
fold is refuted through `e_solve_cstr_sound`, so §2b does both jobs.

⭐ **The repair has to be a PREMISE that the collection's leaked openers
are apart from its own block** — the fourth instance of a prose-completion
this tree has already made three times (`AT-Abs`'s `uniq (αs ++ Θ1)`,
`a_sub__forall_l`'s `uniq (Ξ ++ Θ0)`, §2's `uniq Ξ`).  ⚠️ `uniq Ξ` does
NOT suffice and no strengthening of it can — a leaked opener is not a block
member.  ⛔ Nor does a scoping hypothesis on the look's inputs: both side
conditions already dodge `ftvar_in_aenv Θ` and that is all scoping buys.
So the premise is about the DERIVATION, and WHERE it is discharged
(`a_sub__forall_l` is the extract's only consumer) is the design question
the next session opens on.  It belongs in docs/PAPER-GAPS.md once
machine-checked.

#### ⭐ THE EXTRACT RUNG, FULLY SCOPED — what the guard still owes transport 5

With the guard landed, `a_extract`'s lift is the composition

    §3 (look, transport 5)  →  §7 (fold)  →  §4 (guess)

and each step's premises are available EXCEPT one, which is worth writing
down because deriving it took a full pass.

**THE FOLD'S `flex_agree_rel` NEEDS ρx TO BE NON-FLEX ON SIDE 1.**  Step 2
calls `a_solve_cstr_rel_e` at `ρ' := ρxL ++ ρnL ++ ρ` over the contexts
`Ξ ++ Θ1` and `ΞL2 ++ Θ2`.  For the ρn pairs `flex_agree_rel_push_pairs`
does it, for ρ it is inherited, and for the ρx pairs (the collection's
LEAKED OPENERS) `flex_agree_rel_extend_nonflex` wants `¬ a_flex_tvar` on
both sides.  Side 2 is already a conclusion of transport 5
(`cols_r ρx ∩ dom Ξ2 [=] empty`, plus `b ∉ S0 ⊇ dom Θ2`).  **Side 1 is
not**: nothing says a leaked opener misses `dom Ξ1`.

**⚠️ AND THE GUARD ALONE DOES NOT GIVE IT.**  The guard is about
`ftvar_in_a_cstrs`, and transport 5 puts an opener into ρx whether or not
it SURFACES in 𝒞.  An opener that surfaces nowhere is invisible to any
conclusion-level side condition — so the arrow row's four-case analysis has
a hole exactly at "half 1's opener never occurs in `𝒞₁` and equals half 2's
flexible".

**⇒ TRANSPORT 5 MUST DROP THE UNUSED OPENERS.**  Its five ∀ rows case-split
on `β ∈ ftvar_in_a_cstrs 𝒞`: if it surfaces, keep the pair as now; if not,
hand back `ρx` unchanged and drop `(β, β2)` from the relation.  ✅ **The kit
for that is landed** — `rel_atom_drop_head` / `rel_pskl_drop_head` /
`rel_a_cstr(s)_drop_head` (prop_solve_rel.v §6): a pair whose left atom is
absent from the constraint list is INERT and deletable.

Then transport 5's conclusion gains two conjuncts, and both go through:

    (A)  forall a b, In (a,b) ρx -> a `in` ftvar_in_a_cstrs 𝒞₁
    (B)  cols_l ρx ∩ dom Ξ₁ [=] empty

- (A) is immediate in the ∀ rows (that is what the case split buys) and
  monotone in the arrow rows (`ftvar 𝒞₁ₐ ⊆ ftvar (𝒞₁ₐ ++ 𝒞₁_b)`).
- (B): ρx = · rows are trivial; the ∀ rows add `β`, and
  `a_looksub_binder_not_generated` puts it off `dom Ξ`; the ARROW rows are
  the four-case analysis, and (A) is what makes the two cross cases land on
  the guard's two conjuncts — `ftvar 𝒞₁ₐ ∩ dom Ξ₁_b` and
  `ftvar 𝒞₁_b ∩ dom Ξ₁ₐ` — with the within-half cases coming from the IHs.

⚙ Budget: 14 of the 19 rows inherit both conjuncts verbatim; the five ∀
rows gain ~20 lines each (the split) and the two arrow rows ~20 each.  After
that §8 (the extract lift itself) is one row: look, fold, guess, with the
blocks read off as `flex_pairs_l (ρnL ++ ρnF ++ ρnG)` by `flex_pairs_l_app`.

#### ⛔⛔ AND THE EXTRACT RUNG HITS A SECOND CONFLATION, ONE LAYER UP (2026-08-19)

✅ Transport 5 IS strengthened (both conjuncts, `90f7076`), so the fold's
`flex_agree_rel` at the ρx pairs now goes through on BOTH sides.  ⛔ But the
composition still does not close, and the obstruction is a DIFFERENT
conflation of the same species — worth writing down before anyone re-derives
it.

**WHERE.**  Step 2 calls `a_solve_cstr_rel_e` at
`ρ' := ρxL ++ ρnL ++ ρ` over `Ξ ++ Θ1` and `ΞL2 ++ Θ2`.  That transport
carries the hypothesis `V ∪ cols_l ρ [<=] ftvar_in_aenv Θ1`, and at this
call `cols_l ρ' ⊇ cols_l ρxL` — the COLLECTION's leaked openers — which are
NOT in `ftvar_in_aenv (Ξ ++ Θ1)`.  The hypothesis is unsatisfiable there.

**WHY THE HYPOTHESIS CANNOT SIMPLY GO.**  It has two uses in the solve
transports' ∀ rows:

- `flex_agree_rel_push_tvar_pair`'s `β ∉ dom Θ1 ∪ V ∪ cols_l ρ`.  ⭐ THIS
  ONE IS FREE TO DROP: `flex_agree_rel_push_look` (prop_solve_rel.v §2,
  added for the collection's binder rows) proves the same push from
  `β ∉ dom Θ1` and `β2 ∉ dom Θ2` alone.  Switching §5/§6's five binder rows
  to it removes that use.
- ⛔ `rel_pskl_close_pair`'s `β1 ∉ V` and **`β1 ∉ cols_l ρ`**.  That one is
  genuine: closing at `β1` on side 1 must correspond to closing at `β2` on
  side 2, and a `β1` that is already a LEFT COLUMN would misalign the other
  occurrences.

⇒ The extract row needs **the SOLVE layer's ∀-binders to avoid the
COLLECTION's leaked openers**.  Both are only "fresh for the ambient
context" (`β ∉ ftvar_in_aenv Θ` on each side), so nothing separates them —
the same species as the conflation the cross-half guard just fixed, one
layer up (collection-opener vs SOLVE-binder rather than collection-opener vs
collection-flexible), and again INVISIBLE at `a_extract`'s conclusion.

**⚙ ROUTES, and the two cheap-looking ones are closed:**

- ⛔ Weaken side 1's context by the openers as rigid tvars, so
  `cols_l ρxL ⊆ ftvar_in_aenv (Ξo ++ Ξ ++ Θ1)`.  A rigid-tvar weakening for
  the solve layer was DELETED in 2026-08-04 and its RESTART NOTE
  (sub/look/prop_rsubst.v:617) says the SUB twin is **FALSE** — `SS-ForallR`
  pins its leaked witness — and the eq half needs `β ∉ dom Ξ`.
- ⛔ Put the openers in `V` instead of `ρx`: only legal when the two sides
  pick the SAME atom, and the e-side opener must be supply-fresh.
- 🟡 Pre-freshen the collection's openers away from the solve's binders.
  The machinery exists in one direction (`a_looksub_rename_tvar` moves a
  leaked binder and substitutes `𝒞`), but doing it for ALL openers at once
  is transport 5 again, now on the a-side.
- 🟡 A guard on `a_extract__solve`.  Same shape as the one just landed, and
  the same obstacle: the solve's binders are internal to its derivation.

#### ⚙ COST, AND WHAT IT SAYS ABOUT THE REMAINING BUDGET

`prop_lift.v` is 21.6 s for ~1570 lines.  §8c.24's three performance rules
were followed from the first draft (named hypotheses for every recursive
call's side conditions, no `fsetdec` past five set variables, openers
consumed by `destruct_notin`) and **no row needed a second attempt** —
§§4-7 each compiled the first time they were written.  ⇒ the remaining
blocks are cheap IF a template exists; the expensive ones are the two where
none does and where the a-side is genuinely larger than the e-side
(`a_extract` above, and — expect the same question — `a_sub__forall_l`,
which is the same block's consumer).

#### ✅✅ THE REPAIR IS LANDED (2026-08-19) — the guard is on both arrow rows and the tree is GREEN

`make coq` rc=0, `README.v` 33/33, zero `Admitted`/`Axiom`.  Both collection
arrow rows now carry

    ftvar_in_a_cstrs 𝒞₁ ∩ dom Ξ₂ [=] empty
    ftvar_in_a_cstrs 𝒞₂ ∩ dom Ξ₁ [=] empty

(frost/algo/def_rules.v, `a_looksub__arrow` / `a_lookeq__arrow`), and
`cex/probe_extract_conflated_opener.v` is the record of why: its §1c shows
the second conjunct is exactly what excludes the conflating configuration,
and §3 shows the threaded encoding could not have produced it anyway.

**What it cost, file by file — and the surprises are worth reading.**

- ⚙ `ftvar_in_a_cstr` / `_cstrs` / `_app` MOVED to `frost/algo/def_rules.v`
  above the rules, and the tree's TWO identical copies collapsed into it
  (`algo/sub/prop_looksub.v`'s `ftvar_in_cstrs` and `ext_algo/def_look.v`'s
  `ftvar_in_a_cstrs`, 118 sites).  `def_look.v`'s header had asked for
  exactly this move.
- `prop_swap.v` gains `swap_cstrs_ftv_notin` / `swap_look_guard` — a
  transposition is a bijection, so the guard travels.
- `prop_look.v` gains **`e_looksub_lookeq_cstr_old`**: *a constraint
  variable already in the INPUT supply came from the INPUTS*.  That is what
  lets `e_looksub_sound` discharge BOTH conjuncts — §2's coarse bound can
  only do the first, because it allows the whole output supply and the left
  block lives there.  ⇒ the guard costs the threaded encoding nothing, and
  that is now a theorem rather than an argument.
- `prop_looksub.v` (9 sites): every one is `assumption` — its lemmas rebuild
  the SUBJECT and leave `Ξ`/`𝒞` alone.
- ⭐ `a_looksub_lookeq_subst_gen_size` (prop_decorate_sub.v) is the only
  lemma that needed design.  See below.
- ⭐ The two P6 completeness lemmas (`look/prop_eq_cstr.v`,
  `look/prop_sub_cstr.v`) each needed a ~20-line derivation of the two
  conjuncts — and **both were already facts of the configuration**: the
  right run's block dodges the left run's constraints by its own ftv-𝒞
  bound (the proofs already had it in ∀-form as `HΞ2C1`), and the right
  run's constraints dodge the left run's block by
  `a_looksub_lookeq_ftv`'s DISJUNCTIVE bound — the "outside the context"
  disjunct is impossible because `Ξc1` IS in the right run's context, and
  the other lands in `P02` or `Ξc2`, both already apart.
- `test_examples.v` (10 sites, all `nil` blocks) and two `cex/` files.

**⭐⭐ THE ONE PIECE OF DESIGN: `a_looksub_lookeq_subst_gen_size`.**  Its
conclusion is EXISTENTIAL in the outputs and its binder rows RE-PICK the
rule's opener away from `P0`, so the arrow case must prove the guard for
outputs it has just invented.  Two shapes were tried:

- ⛔ `dom Ξ' ∩ L [<=] dom Ξ` plus `ftvar 𝒞' ∩ L [<=] ftvar 𝒞 ∪ ftvar P0`.
  It works inside the lemma, but it needs `ftvar P0 [<=] ftvar_in_aenv Θ`,
  and that CANNOT be discharged at the consumer: `a_subtag_decoration`
  quantifies the run's context `Θl` INSIDE the induction (deliberately —
  its header explains the ForallL rows need a different one), with no link
  to the node's guess `P1`, whose only wf sits at `Ξ ++ Θ0`.
- ✅ **`dom Ξ' ∩ L [=] empty`** — the produced block is ENTIRELY fresh for
  the caller's avoid-set.  Then the arrow row runs the RIGHT half first
  with `L2 := L ∪ ftvar 𝒞1 ∪ ftvar P0` and the LEFT half with
  `L1 := L ∪ ftvar 𝒞2' ∪ dom Ξ2'`, both guards are one `fsetdec` each, and
  **nothing about `P0` is hypothesised** — so `a_looksub_subst_gen` keeps
  its signature and `prop_soundness_sub.v` is untouched.

⚙ THE PRICE of the second shape, and it is the lesson: **every row must now
go through the induction.**  The rows that used to hand the premise back
VERBATIM would hand back its ORIGINAL block — so `LS-Check`'s unit/var
subcases and `LE-UnivGhostR`'s route through the IH (the substitution is
vacuous there, `cbn` or `subst_pskl_in_pskl_fresh_eq` removes it), and the
three ∀-VACUOUS shortcuts (`β = b`, the rule's own binder) are DELETED:
every ∀ row re-picks, exactly as `LS-ForallR` always did.  ⚠️ Also
`dom Ξ' [=] dom Ξ` is FALSE — `LE-FlexR` re-picks its generated flexible
away from `P0`.

⚠️⚠️ **AND ONE FALSE START WORTH RECORDING.**  The symmetric guard looks
like it must break look COMPLETENESS, because at the P6 arrow the right
half genuinely runs at `Ξs1 ++ Ξc1 ++ Θ0` and its constraints are bounded
by a set containing `dom κc1`.  It does not: that is only a coarse bound.
`a_looksub_lookeq_ftv` gives the sharp statement, and the right half's
constraints really do miss the left half's block.

⚙ Traps paid: `remember` the arrow rows' avoid-sets (written out, every
later `fsetdec` faces SEVEN set variables); the size fact handed to the
size-indexed lemma must be a NAMED hypothesis (inside an `ltac:` argument
the skeletons are still evars and `lia` has nothing to work on); and a
`python`-side regex over `IH _ _ _ _ _ _` must allow BOTH the six- and
seven-underscore arities.

#### ⚙ COST, AND WHAT IT SAYS ABOUT THE REMAINING BUDGET

`prop_lift.v` is 21.6 s for ~1570 lines.  §8c.24's three performance rules
were followed from the first draft (named hypotheses for every recursive
call's side conditions, no `fsetdec` past five set variables, openers
consumed by `destruct_notin`) and **no row needed a second attempt** —
§§4-7 each compiled the first time they were written.  ⇒ the remaining
blocks are cheap IF a template exists; the expensive ones are the two where
none does and where the a-side is genuinely larger than the e-side
(`a_extract` above, and — expect the same question — `a_sub__forall_l`,
which is the same block's consumer).

#### ⚙ THE REPAIR WAS ATTEMPTED AND COSTED (2026-08-19, same day) — one lemma blocks it, and it is NOT one of the 31 construction sites

The guard was written and carried through most of the tree before being
**reverted** (a half-landed rule change is not committable).  What the
attempt measured, so the next session does not re-measure it:

**What landed cleanly** (patch kept at
`<session scratchpad>/cross-half-guard-wip.patch`, ~1900 lines, applies to
`4f1dc9c`):

- `ftvar_in_a_cstr` / `_cstrs` / `_app` MOVED to `frost/algo/def_rules.v`
  above the rules — and the tree's TWO identical copies collapsed into it
  (`algo/sub/prop_looksub.v`'s `ftvar_in_cstrs` and `ext_algo/def_look.v`'s
  `ftvar_in_a_cstrs`; 118 call sites renamed to the surviving name).
  ⭐ Worth doing on its own: `def_look.v`'s header had asked for exactly
  this move.
- Both guard conjuncts on both arrow rows, and `def_rules.v` compiles.
- ✅ `prop_swap.v` (two new kit lemmas, `swap_cstrs_ftv_notin` /
  `swap_look_guard` — a transposition is a bijection, so the guard
  travels), `prop_looksub.v` (9 sites; every one is `assumption`, because
  its lemmas rebuild the SUBJECT and leave `Ξ`/`𝒞` alone),
  `look/prop_eq_cstr.v`, `look/prop_sub_cstr.v` (the P6 completeness
  lemmas — **they compiled untouched**, which was the biggest risk retired),
  `prop_solve_rel.v` §7, `test/test_examples.v` (10 sites, all `nil`
  blocks), two `cex/` files.
- ✅ **`e_looksub_sound` DISCHARGES BOTH CONJUNCTS**, which is the
  faithfulness claim made good.  It needed one new e-side lemma —
  `e_looksub_lookeq_cstr_old`: *a constraint variable already in the INPUT
  supply came from the INPUTS*.  §2's coarse bound cannot do the second
  conjunct (it allows the whole output supply, where the left block lives).

**⛔ WHAT BLOCKS IT — `a_looksub_lookeq_subst_gen_size`**
(`deco_algo/prop_decorate_sub.v:2866-3352`, ~490 lines, 6 `pick fresh`
rows), consumed by `a_looksub_subst_gen` and thence twice inside
**subtyping soundness** (`deco_algo/prop_soundness_sub.v:616, :914`).

Unlike every other site, this lemma's conclusion is EXISTENTIAL in the
outputs (`exists Ξ' 𝒞', …`): its binder rows RE-PICK the opener, so `𝒞'`
carries a name `𝒞` never had.  The arrow case must then prove the guard for
outputs it has just invented, and the two facts that would give it —
`dom Ξ' [=] dom Ξ` and a bound on `ftvar 𝒞'` — are **not enough on their
own**: the re-picked opener `δ` is drawn fresh for the local block only, so
nothing stops `δ ∈ dom Ξ2'`, the SIBLING's block.  ⇒ the lemma needs an
**avoid-set parameter** `L` threaded through all 19 rows, plus the two
output invariants, plus a new hypothesis (`ftvar P0` misses the block) that
its two consumers inside `a_sub_sound` must discharge.

⭐ That is a campaign of its own, the same size as guards 3/4/5 — not a
mechanical follow-on.  ⚙ And note where it is: the obligation lands in the
DECORATION path (`}}a ⇒ }}da ⇒ }}ad ⇒ }}d`), i.e. in subtyping SOUNDNESS,
which is a closed flagship theorem.

#### ⚙⚙ SECOND ATTEMPT, SAME DAY — the blocking lemma WAS strengthened, and the obstruction moved ONE LEVEL UP

The strengthening was written and **`prop_decorate_sub.v` compiles with the
guard in place** (patch kept as `cross-half-guard-wip2.patch`, ~2500 lines,
applies to `4f1dc9c`).  What `a_looksub_lookeq_subst_gen_size` needed, and
it is exactly what was predicted:

- an **avoid-set parameter `L`**, threaded through all 19 rows and added to
  every `pick fresh` set (the re-picked opener must dodge it);
- two bookkeeping conjuncts — `dom Ξ' ∩ L [<=] dom Ξ` and
  `ftvar_in_a_cstrs 𝒞' ∩ L [<=] ftvar_in_a_cstrs 𝒞 ∪ ftvar_in_pskl P0`
  ("inside the caller's avoid-set, nothing new");
- ⚠️ `dom Ξ' [=] dom Ξ` is **FALSE** — `LE-FlexR` re-picks its generated
  flexible away from `P0`, so the domain genuinely moves.  That is why the
  conjunct is `∩ L [<=]` and not `[=]`;
- the two ARROW rows run the **RIGHT half first** (so its answer is
  concrete when the left half names the set it must dodge) with
  `L2 := L ∪ dom Ξ1 ∪ ftvar 𝒞1` and
  `L1 := L ∪ dom Ξ2' ∪ ftvar 𝒞2' ∪ ftvar 𝒞2`;
- ⚙ the avoid-sets are `remember`ed: written out, every later `fsetdec`
  would face SEVEN set variables, which is §8c.23's cliff.  Every `fsetdec`
  in the row is scoped to five.
- one new hypothesis, `ftvar_in_pskl P0 [<=] ftvar_in_aenv Θ` — the guard
  also needs the SUBSTITUTED skeleton to miss the block, which is
  `a_looksub_lookeq_generated_fresh` once `P0` is scoped in `Θ`.

⛔ **AND THAT LAST HYPOTHESIS IS WHERE IT STOPS.**  Its consumer is
`a_looksub_subst_gen`, called twice inside `a_subtag_decoration`
(prop_soundness_sub.v:~616, :~914) — and that lemma quantifies the run's own
context `Θl` **INSIDE** the induction (deliberately: its header explains the
ForallL rows need a different one), with no scoping link to the node's guess
`P1`, whose only well-formedness in scope is `{{ Ξ ++ Θ0 ⨟ empty ⊢ₚₛ P1 }}a`
at a DIFFERENT context.  So `ftvar P1 [<=] ftvar_in_aenv Θl` is simply not
available, and supplying it means adding a scoping hypothesis to
`a_subtag_decoration` itself — where `P1` is existential in the `}}da`
premise, so the hypothesis would have to relate `Θl` to `Θ0`.  Another
design decision, one level further up a closed flagship proof.

⭐⭐ **THE CANDIDATE THAT REMOVES THE HYPOTHESIS ALTOGETHER** — worth trying
before the `Θl`-vs-`Θ0` route.  Strengthen the conclusion instead to

    dom Ξ' ∩ L [=] empty

("the produced block is ENTIRELY fresh for the caller's avoid-set").  Then
the two arrow guards fall out with `L1 := L ∪ ftvar 𝒞2 ∪ ftvar P0` and
`L2 := L ∪ ftvar 𝒞1' ∪ dom Ξ1'`, and **no hypothesis on `P0` is needed at
all** — so `a_looksub_subst_gen` keeps its signature and
`prop_soundness_sub.v` is untouched.  ⚙ THE PRICE: the rows that hand back
the ORIGINAL subtree verbatim (`LS-Check`'s unit/var subcases, the
∀-VACUOUS branches) must instead RE-PICK their block names, which wants a
BLOCK-FRESHENING lemma for `a_looksub`/`a_lookeq`.  ⭐ One exists in
substance: `a_looksub_lookeq_rel_e` (prop_solve_rel.v §7) composed with
`e_looksub_sound` rederives any collection with a supply-fresh block — what
has to be added is transporting the `{{ 𝒞 ⊩ ψa ⤳ Ψa }}da` solvetag
obligation across `rel_a_cstrs`.

### 8c.26 ⭐⭐⭐ THE EXTRACT RUNG COMPOSES — one obstruction RETIRED, the other REDUCED TO A NAMED SIDE CONDITION (2026-08-19)

✅ **`make coq` rc=0, `README.v` 33/33, zero `Admitted`/`Axiom`.**  Two
commits, `89555ab` and `e0c3809`.

§8c.25's last box named TWO obstructions on the extract rung.  The first is
GONE; the second is now a single, named, machine-checked side condition, and
`prop_lift.v` §8 (`a_extract_rel_e_gen`, `Closed under the global context`)
is the proof that it is EXACTLY what the rung needs — nothing weaker,
nothing more.

#### ✅ OBSTRUCTION 1 IS RETIRED — the scoping premise SPLITS, and the PAIR RESTRICTION pays for the half that could not be satisfied

The solve transports carried one premise, `V ∪ cols_l ρ [<=] ftvar_in_aenv
Θ1`, and it is unsatisfiable at the extract (ρ carries the collection's
leaked openers, bound nowhere).  ⭐ **It had TWO jobs and they separate:**

| job | row | new premise |
|---|---|---|
| `β ∉ V` | the five ∀ rows | `V [<=] ftvar_in_aenv Θ1` |
| `β ∉ cols_l ρ` | the five ∀ rows | — **the PAIR RESTRICTION** |
| the new block dodges the pair columns | the four ARROW rows | `dom Ξ1 ∩ cols_l ρ [=] empty` |

⭐⭐ **THE PAIR RESTRICTION** (prop_solve_rel.v §6, new).  `restrict_pairs
β1 β2 ρ` DELETES every pair whose LEFT atom is `β1` or whose RIGHT atom is
`β2`, and `rel_pskl_restrict` says that is invisible to a relation whose two
sides are already fresh for the two atoms — which is exactly a binder row's
input, **BEFORE it opens**.  So `rel_pskl_close_pair`'s `β1 ∉ cols_l ρ` is
bought BY CONSTRUCTION instead of by a scoping premise side 1 has no supply
to satisfy.  `rel_pskl_close_pair_restrict` packages the whole ∀-row move
(restrict → open → IH → bubble → close → widen back by `rel_pskl_mono`), and
all six binder rows go through it in one line each.

⚙ With that, `flex_agree_rel_push_tvar_pair` has no user left at a binder
row: the WEAK `flex_agree_rel_push_look` (only `β ∉ dom Θ1` / `β2 ∉ dom Θ2`)
does every one.  §8c.25 predicted this half was free; it is.

⚙ Third premise deleted, not added: §4's coverage loses `cols_r ρ` — its
only use was `β2 ∉ cols_r ρ`, which the restriction also buys.

⚙ New in prop_lift.v: `a_solve_cstr_block_fresh_set` (the SET form of
`a_solve_cstr_generated_fresh`; prop_look_pair.v has one, but that file is a
heavy dependency for a single fact) and the `in_incl` tactic.

#### ⛔ OBSTRUCTION 2 IS NOW ONE NAMED SIDE CONDITION, AND IT IS A RULE CHANGE

    ftvar_in_a_cstrs 𝒞 ∩ dom Ξs [=] empty        on [a_extract__solve]

*the FOLD's generated flexibles are fresh for the constraints it is
solving.*  ⛔ **WHY IT IS OWED** — the same species as the CROSS-HALF guard,
one layer up.  The collection LEAKS openers into `𝒞` (all five ∀ rows do)
and they are bound NOWHERE — not in `Θ0`, not in `Ξ`.  The fold then runs at
`Ξ ++ Θ0` and `SE-FlexR`'s guess draws its flexibles fresh for
`ftvar_in_aenv (Ξ ++ Θ0)` ONLY, so it may draw one.  Side 1 then reads that
atom as FLEXIBLE (it is in `Ξs`) where side 2 reads its counterpart as a
rigid free atom — `SE-FlexR` fires on one side and no rule matches on the
other.  ⇒ no `flex_agree_rel` between the two contexts exists, which is
precisely §7's premise, and it is exactly the configuration
`cex/probe_extract_conflated_opener.v` refutes one level down.

⭐ **UNLIKE the solve layer's ∀-binders, this one IS expressible at the
rule**: `𝒞` and `Ξs` are both named in `a_extract__solve`'s premises.
Transport 5's `∀ (a,b) ∈ ρx, a ∈ ftvar_in_a_cstrs 𝒞₁` (landed `90f7076`) is
what connects the guard to the pair columns.

✅ **AND IT COSTS THE THREADED ENCODING NOTHING — a THEOREM**,
`e_extract_solve_guard` (prop_lift.v §8, five lines): the collection's
constraints live in the supply it has already spent
(`e_looksub_cstr_ftvar`) and the fold's block is drawn STRICTLY ABOVE that
supply (`e_solve_cstr_block`).  Both facts are ALREADY `pose proof`ed inside
`e_extract_sound`, so that site's discharge is two lines.

#### ⚙ THE COSTING OF THE RULE CHANGE — 20 sites, 19 cheap, ONE that is a campaign

`a_extract__solve` has far fewer construction sites than `a_looksub__arrow`
did (20 vs 31+):

| site | count | cost |
|---|---|---|
| `test/test_examples.v` | 9 | concrete `𝒞`/`Ξs` — `fsetdec` |
| `cex/probe_flexr_repair.v` | 2 | concrete |
| `ext_algo/prop_extract.v` (`e_extract_sound`) | 1 | ✅ `e_extract_solve_guard`, two lines |
| `algo/prop_swap.v` | 1 | ✅ a transposition is a bijection — `swap_cstrs_ftv_notin` already exists (it was added for the cross-half guard) |
| `algo/sub/prop_looksub.v` (`a_extract_family_of_instance`) | 1 | 🟡 the collection is RENAMED there, so `L` grows by `dom Ξs`; small |
| `algo/sub/look/prop_extract.v` (**P6-L**) | 2 | ⛔ **the campaign** |

⛔ **WHY P6-L IS THE CAMPAIGN, and it is NOT a missing `fsetdec`.**  Both of
its sites get `𝒞`, `Ξc`, `Ξs` from ONE call to
`a_looksub_solve_complete_gen` (prop_sub_cstr.v:670).  That theorem already
has an AVOID-SET PARAMETER `L` with the output conjunct
`∀ α0 ∈ dom Ξs, α0 ∉ L` — but **`L` is chosen BEFORE `𝒞` exists** (`𝒞` is
existential in the same conclusion), so it cannot absorb
`ftvar_in_a_cstrs 𝒞`.  ⇒ the guard has to become an OUTPUT CONJUNCT proved
INSIDE that induction, and its arrow rows will then face a cross-half
obligation of exactly the shape the landed guard has (half 1's constraints
vs half 2's solve block).

⛔ **AND IT IS NOT DERIVABLE FROM THE EXISTING BOUND.**
prop_sub_cstr.v:750's comment says "the STRUCTURAL bound
`ftv 𝒞 ⊆ ftv P0 ∪ dom Ξc` is already available as `a_looksub_ftv`" — that is
loose prose.  `a_looksub_ftv` is **DISJUNCTIVE** (`α0 ∈ ftv P' ∪ dom Ξ` OR
`α0 ∉ ftvar_in_aenv Θ`), and its own header says why: the five ∀ rules leak,
so the exact bound is FALSE.  A leaked opener lands in the SECOND disjunct,
which says nothing about `dom Ξs`.

⚙ A cheaper PLACEMENT was considered and is not cheaper: putting the guard
on `a_solve_cstr__eq` (the head's block dodges the whole constraint list)
needs the tail row to see the constraints ALREADY CONSUMED, so it wants an
extra index — and the discharge still lands on P6-Ss, which builds the fold.

#### ⭐⭐ THE DIAGNOSTIC, FOURTH CONFIRMATION

Every obstruction on this campaign has had ONE shape: two sibling premises
invent names independently, each avoids only `ftvar_in_aenv Θ`, and `Θ` does
not record what the sibling did.  Here the siblings are the COLLECTION (which
leaks) and the FOLD (which generates), and `a_extract__solve`'s own comment —
"the guess runs AFTER the collection AND the solving, so its avoid-input is
the whole `Ξs ++ Ξ ++ Θ0`" — shows the authors' threading argument covers the
GUESS against the two blocks but says nothing about the fold against the
collection's LEAKS, because on paper a leaked opener is not a name at all.

#### ⛔ WHAT §8 STILL OWES ABOVE ITSELF

`a_extract_rel_e_gen` takes the three sub-derivations directly rather than an
`a_extract` derivation, because the guard cannot be stated about an
`a_extract` whose `𝒞`/`Ξs` are existential.  Once the rule carries it, the
wrapper is one `inversion`.  ⚠️ And note the conclusion carries a ρx column
(`ρxL ++ ρxF`) — `SS-ForallR`'s leak survives the extract, so `a_consis` /
`a_sub` will meet the same currency; §8c.25's prediction that it EASES above
the extract (those judgements THREAD an output context, so siblings do see
each other's inventions) is still unverified.

### 8c.27 ⭐⭐⭐ THE EXTRACT RUNG IS CLOSED — the CROSS-LAYER GUARD IS LANDED, and `a_extract` LIFTS (2026-08-20)

✅ **`make coq` rc=0, `README.v` 33/33, zero `Admitted`/`Axiom`.**
`a_extract_rel_e` (prop_lift.v §8) is `Closed under the global context`:
an `a_extract` derivation transports to an `e_extract` derivation.  §8c.26's
one remaining side condition is now a premise of the rule.

#### THE RULE CHANGE

`a_extract__solve` (frost/algo/def_rules.v) gains, `[paper-gap]`-tagged and
filed in docs/PAPER-GAPS.md together with the CROSS-HALF guard (which had
never been filed):

    ftvar_in_a_cstrs 𝒞 ∩ dom Ξs [=] empty

⚙ Placed LAST, after the guess premise, so every consumer's positional
tactic list grows at its END.

#### THE DISCHARGE — 20 sites, and the costing in §8c.26 was right

| site | count | what it took |
|---|---|---|
| `test/test_examples.v` | 9 | `simpl. clear. fsetdec.` (all `Ξs = nil`) |
| `cex/probe_flexr_repair.v` | 2 | same |
| `ext_algo/prop_extract.v` (`e_extract_sound`) | 1 | ⭐ ONE LINE, `clear - Hcs Hfr2; fsetdec` — both facts were already `pose proof`ed there.  The faithfulness claim, made good in practice |
| `algo/prop_swap.v` | 1 | `apply swap_look_guard` (already existed) |
| `algo/sub/prop_looksub.v` | 1 | `eassumption` — `a_looksub_rename_var` moves the SUBJECT and the marker and leaves `Ξ`/`𝒞` alone |
| `algo/sub/look/prop_extract.v` (**P6-L**) | 2 | the campaign |

#### ⭐⭐ THE CAMPAIGN, AND WHY IT WAS NOT A MISSING `fsetdec`

P6-L gets its collection AND its fold from ONE call to P6-Ss, whose
avoid-set parameter `L` is chosen **before `𝒞` exists**.  So P6-Cs
(`a_lookeq_solve_complete_gen`, `a_lookeq_flex_p0_complete`) and P6-Ss
(`a_looksub_solve_complete_leaf` / `_gen` / `a_looksub_solve_complete`) each
gained an OUTPUT conjunct, proved inside their inductions:

    forall α0, α0 `in` dom Ξs -> α0 `notin` ftvar_in_a_cstrs 𝒞

⚙ **It was nearly free**, and for a reason worth keeping: both ARROW rows
already had the two cross facts in the shapes they need.
`dom Ξs2 ∩ ftv 𝒞1` is bought by putting `ftvar_in_a_cstrs C1` into the RIGHT
recursion's avoid-set — legal because `𝒞1` is CONCRETE by then — and
`dom Ξs1 ∩ ftv 𝒞2` holds because the RIGHT look runs at a context
**containing `Ξs1`**, so `a_looksub_ftv_ctx` / `a_lookeq_ftv_ctx` apply.
P6-Cs was already making that exact derivation for its ftv-𝒞 bound.  Every
other row is a pass-through or an empty block.

⭐ **The one place that needed design** is the ForallL / UnivGhostL REORDER
(`a_looksub_solve_forall_l` / `_univ_ghost_l` + their `_mode` wrappers): its
α-stack leaf RE-DERIVES the solve at a fresh opener γ and puts γ into the
new constraint, so the invariant is CARRIED (a new premise) rather than
re-derived — and γ misses `dom Ξs` by the re-derived solve's own freshness
at `γ,Θ2`.  ⇒ those four lemmas gained the premise and the conjunct too.

⚠️ **`a_looksub_ftv` cannot substitute for it.**  prop_sub_cstr.v:750's
comment calls it "the STRUCTURAL bound `ftv 𝒞 ⊆ ftv P0 ∪ dom Ξc`"; that is
loose prose.  The lemma is DISJUNCTIVE precisely because the five ∀ rules
leak, and a leaked opener lands in the disjunct that says nothing about
`dom Ξs`.

#### ⚙ TRAPS PAID

- ⚠️⚠️ **`repeat split` DISMANTLES an `[=]` through its `iff`.**  A conjunct
  written `X ∩ Y [=] empty` costs every row TWO goals; the ∀ form
  (`forall α0, α0 ∈ dom Ξs -> α0 ∉ …`) is one, and matches the neighbouring
  avoid-set conjunct's shape.  (`[<=]` is safe — it is a bare `forall`.)
- ⚠️ A destructuring pattern that is one component SHORT does not fail: the
  last name silently binds the remaining CONJUNCTION, and the error surfaces
  much later as "No product even after head-reduction" or a bullet
  complaint.  Check the `as (…)` arity first when a row breaks oddly.
- ⚙ `inter_dom_empty_of_avoid` / `inter_dom_empty_of_forall`
  (prop_eq_cstr.v) convert between the ∀ form and the rule's set form.

#### ⛔ WHAT IS LEFT OF THE LIFT

consis, sub, split, pat, typing.  ⚠️ `a_extract_rel_e`'s conclusion carries a
ρx column — `SS-ForallR`'s leak survives the extract — so the same currency
continues upward.  §8c.25's prediction that it EASES above the extract
(those judgements THREAD an output context, so siblings do see each other's
inventions) is still unverified.

### 8c.28 ⚙ THE CONSIS RUNG, SCOPED — the CONTEXT RELATION is landed, and the four things the trio still owes (2026-08-20)

✅ **`make coq` rc=0, `README.v` 33/33, zero `Admitted`/`Axiom`.**
`prop_solve_rel.v` §8 is new and is pure currency — no rung uses it yet.

#### ⭐ WHY THE CURRENCY HAS TO GROW HERE

Everything up to and including `a_extract` outputs SKELETONS, so
`rel_pskl` + `flex_agree_rel` was the whole interface.  The consis trio
(`a_assign` / `a_unify` / `a_consis`) outputs a **CONTEXT**, and its rows
READ the payloads — `Assign-Assign` and `Flex-Flex-Assign` SUBSTITUTE the
definition they find — so the two sides' contexts must be related entry by
entry.  §8 adds

    rel_ptyp   ρ V A1 A2   :=  rel_pskl ρ V ⌈A1⌉ ⌈A2⌉   (the painting is injective)
    rel_abind  ρ V b1 b2                                (five rows, one per binder shape)
    rel_aenv   ρ V Θ1 Θ2                                (POSITIONAL: same shape, entries pairwise)

with `rel_aenv_mono` / `_widen` / `_app` / `_refl`, `rel_aenv_binds_l` /
`_binds_r` (how a row reads a definition off the context) and
`rel_aenv_flex_pairs` (what `Assign-SolveM`'s `guess^TY` hands back).

⭐ **POSITIONAL is the right choice** and the algorithm licenses it: every
rule that grows a context grows it on BOTH sides at once, and the
`Assign-*` walk is driven by the SHAPE of `Θ0`, which `rel_aenv` makes
common.  So `Assign-Depend`/`Skip`/`SkipRigid`/`SkipTmVar` are one
`inversion` each, and `Assign-Depend`'s `Ξ ++ (β ~ ⌢)` is `rel_aenv_app`.

⚠️⚠️ **`rel_aenv` DOES NOT SUBSUME `flex_agree_rel`, and the two must be
carried together.**  A left atom may have two right images (§8c.25's
Finding 1), so "entry `i` of `Θ1` is flexible at `a`" says nothing about an
ARBITRARY pair `(a,b) ∈ ρ` — only about the pair entry `i` itself carries.
Making `rel_aenv` imply the agreement would need ρ to be a FUNCTION on
`dom Θ1`, which is exactly the currency §8c.25 retired.

⚙ Also landed: `rel_pskl_ftv_corr_l` / `_corr_r` — *every free variable of
one side is RELATED to one of the other*, sharper than `rel_pskl_ftv_l/_r`
(which only bound the two sets by `V ∪ cols`).  It is what transports a
DISJOINTNESS across the relation, which is what the consis rows' `Δ` guards
are.

#### ⛔ WHAT THE TRIO STILL OWES — four things, in order of risk

1. ✅ **A relation for `Δ1` / `Δ2` — LANDED, and it is the piece that
   validated the design.**  They are atom SETS of bound variables, grown by
   the three ∀ rows — which pick `α` on side 1 and a supply-fresh `α2` on
   side 2, so the two sets DIFFER.  The rows that read them are `Ghost`
   (`Δ2 ∩ ftvar P0 [=] empty`) and `GhostR` (`Δ1 ∩ ftvar P [=] empty`).

       rel_atoms ρ V D1 D2 := forall a b, rel_atom ρ V a b -> (a ∈ D1 <-> b ∈ D2)

   (`flex_agree_rel`'s shape), with `rel_atoms_disjoint` — the guard
   transports, through `rel_pskl_ftv_corr_r` — and `rel_atoms_push` for the
   ∀ rows.

   ⭐⭐ **AND THE PUSH NEEDS `β1 ∉ cols_l ρ` / `β2 ∉ cols_r ρ` — i.e. THE
   PAIR RESTRICTION AGAIN.**  Without it a left atom already paired
   elsewhere lands in `add α Δ1` while its partner misses `add α2 Δ2`.
   Side 2 buys it from the supply; side 1 uses `restrict_pairs` (§6),
   exactly as the solve layer's ∀ rows do.  That the same move is forced at
   a completely different judgement is the strongest evidence so far that
   the currency is the right one.

   ⚙ Also new: `rel_atom_cons_inv`, `rel_atom_l_in`, `rel_atom_r_in` — the
   three shape facts about `rel_atom` that had never been needed.

2. **The ∀ rows' DROP.**  `e_consis__forall_inh` runs its premise at
   `(α ~ ⌢) ++ Θ0` and outputs `(α ~ ⌢) ++ Θ1`, but the CONCLUSION outputs
   `Θ1` — so the pair `(α, α2)` must leave ρ at the conclusion.  That is
   `rel_*_drop_head` (prop_solve_rel.v §6) generalized to `rel_aenv`, and it
   needs `α ∉` the surviving context — i.e. the openers must not escape into
   `Θ1`'s payloads.  ⚙ The rules' own `Δ`-guards are what should give it;
   worth checking against `cex/` before assuming.

3. **`flex_agree_rel` ON THE OUTPUTS.**  Plausible and cheap: solving does
   not change flex-ness (`a_flex_tvar` holds for `flex_mono_def` too), and
   `Assign-SolveM`'s two new blocks are `flex_pairs_l/r` of one pair list.
   ⚙ UNVERIFIED.

4. **The rows themselves** — 9 (`a_assign`) + 6 (`a_unify`) + 14
   (`a_consis`), one mutual induction.  The templates are §5-§7's.

5. ✅ **THE IDENTITY SUPPORT HAS TO SHRINK WITH THE WALK — found by
   designing the motive, and the piece for it is LANDED.**  This is the
   trio's real first obstruction and it is worth stating carefully.

   The consis ∀ rows need their side-1 opener OFF `V`, and the only source
   is the rule's own `α ∉ ftvar_in_aenv Θ0` — so the transport must carry
   `V [<=] dom Θ0`.  ⛔ **But the ASSIGN WALK SHRINKS the context.**
   `Assign-Skip` runs its premise at the TAIL with `β` gone, so a `V` tied
   to the caller's context is too big there — and `Assign-Assign` hands that
   smaller context to a CONSISTENCY derivation, whose ∀ rows may then
   legitimately pick the dropped `β` as their opener.  If `β ∈ V` the close
   is asymmetric (side 2's opener is supply-fresh, hence `≠ β`) and
   `rel_pskl_close_pair` is unavailable.

   ⭐ The repair is to shrink `V` alongside the context, which is FREE
   exactly when the dropped atom does not occur — and `Assign-Skip`'s own
   premise is `β ∉ ftvar_in_pskl P`.  `rel_pskl_shrink_V` / `rel_ptyp_` /
   `rel_abind_` / `rel_aenv_shrink_V` (prop_solve_rel.v §8), stated with an
   arbitrary `V'` and a USED-PART condition rather than with `remove`, so
   one lemma covers every row.  ⚙ `flex_agree_rel` needs nothing —
   `flex_agree_rel_weaken` already shrinks `V`.

   ⭐⭐ **THAT IS THE THIRD INDEPENDENT APPEARANCE OF ONE IDEA**: the
   PAIR RESTRICTION (§6, the solve layer's ∀ rows), `rel_atoms_push`'s
   `β1 ∉ cols_l ρ`, and now the V-shrink.  All three say the same thing —
   *a binder row must not be handed a relation that already speaks about its
   own opener* — and all three are discharged by DELETING the offending part
   of the relation rather than by strengthening a rule.

   ⚙ AND THE ONE THING IT NEEDS FROM WELL-FORMEDNESS: at `Assign-Skip` the
   TAIL's payloads must not mention `β` either (for `rel_aenv_shrink_V`).
   That is ordinary scoping (`Θ0` is older than `β`), but it is a premise
   the transport will have to carry — `a_wf_aenv` is the obvious source and
   has NOT been checked.

#### ⚙ AND THE RUNG ORDER ABOVE

consis → sub (which is `a_extract`'s consumer, `a_sub__forall_l`) → split →
pat → typing.  ⚠️ `a_extract_rel_e` hands back a ρx column, so `a_sub` meets
the leaked-opener currency immediately.

### 8c.29 ⛔ THE TRIO'S FOURTH OBSTRUCTION — the rows dispatch on atom EQUALITY, so ρ needs a SHAPE, and the currency for it is landed (2026-08-20)

✅ **`make coq` rc=0, `README.v` 33/33, zero `Admitted`/`Axiom`.**
`prop_solve_rel.v` §9 is new and is pure currency — no rung uses it yet.
The motive below is DESIGNED and its every premise traced to a checked
source, but the 29 rows are NOT written.

#### ⛔⛔ THE FINDING — `rel_atom` alone cannot drive the walk

Everything up to and including `a_extract` dispatches on the **SHAPE** of a
skeleton, so an arbitrary `rel_atom ρ V α α'` was all any row ever asked of
a variable.  **The trio dispatches on atom EQUALITY**, in four places:

| row | what it needs of side 2 |
|---|---|
| `Assign-SolveM`, `Assign-UnivGhost-Id` | the context HEAD **is** the subject |
| `Assign-Skip` (and `Flex-Flex-Skip`) | the head is **not** the subject |
| `Assign-Assign`, `Flex-Flex-Assign` | SUBSTITUTE at the head's atom, on BOTH slots |
| `Rigid`, `Flex`, `FlexL`, `FlexR` | `binds` / `a_flex_tvar` at the subject's IMAGE |

⛔ None of these is available from a relation.  Concretely at
`Assign-SolveM`: side 1 is `(α ~ ⌢) ++ Θ0 ⊲[Ξ] α ≔ P`, side 2 is
`(b ~ ⌢) ++ Θ0'` with subject `α'`, and `rel_aenv` gives `rel_atom ρ V α b`
while the caller gives `rel_atom ρ V α α'`.  **With `α` related to two right
atoms, `b ≠ α'` and side 2 must take a DIFFERENT rule** — the walk would
skip past the head it was supposed to solve.  ⇒ the transport is false
without a further hypothesis on ρ.

#### ⭐ THE REPAIR — TWO shape conditions, of DIFFERENT strengths on purpose

    rel_inj ρ V     := forall a1 a2 b, rel_atom ρ V a1 b -> rel_atom ρ V a2 b -> a1 = a2
    rel_fun ρ V D   := forall a b1 b2, a ∈ D -> rel_atom ρ V a b1 -> rel_atom ρ V a b2 -> b1 = b2

- `rel_inj` is **GLOBAL** and true by construction: every right atom is
  drawn ONCE, from a supply that only grows, so no two invention events can
  produce it.  ⚙ It subsumes `V ∩ cols_r ρ [=] empty`.
- `rel_fun` is **LOCAL, on `D`**, and ⚠️ it CANNOT be global — §8c.25's
  Finding 1 IS a left atom with two right images, and that configuration is
  REACHABLE above the extract (`a_extract_rel_e` hands back a ρx column of
  leaked openers).  What saves the trio is that **a leaked opener is bound
  NOWHERE** — not in `Θ0`, not in `Ξ` — so `D` is taken to be the CONTEXT's
  DOMAIN, where every pair was created by a row that pushed an entry on
  BOTH sides at once.

⭐⭐ **AND THE BINDER ROWS PAY FOR THEM WITH THE SAME MOVE AS EVERY OTHER
RUNG.**  `rel_inj_push` wants `β2 ∉ V ∪ cols_r ρ` and `rel_fun_push` wants
`β1 ∉ V ∪ cols_l ρ` — *the pair restriction, a fifth time*, on the same two
columns `rel_atoms_push` already asks about.  Side 2 buys its half from the
supply; side 1 uses `restrict_pairs`.

#### ⚙ WHAT §9 LANDS (prop_solve_rel.v, all Qed)

    rel_inj / rel_fun               + _sub / _weaken / _push / _app
    rel_atom_incl / _app_inv / _off_l / _l_in / _r_in
    rel_atom_id_of_fun              (an atom of V the context binds is related to ITSELF)
    rel_atom_inj_eq_r
    rel_pskl_subst / rel_ptyp_subst ⭐⭐ the Assign-Assign / Flex-Flex-Assign
                                    transport: "a = β1 iff b = β2" for every
                                    related pair, which is EXACTLY the two
                                    conditions above — it is why they exist
    rel_aenv_cons_inv_l             the walk's one-line inversion
    rel_ptyp/abind/aenv_drop_head   the head pair leaves with its entry
    restrict_pairs_app,
    rel_ptyp/abind/aenv_restrict    the ∀ rows strip their opener off the
                                    OUTPUT context, and by then the row's own
                                    generated pairs sit in FRONT of the
                                    opener's — so drop_head is not enough
    rel_ext ρe W S                  the spec of the pairs a row ADDS
    rel_inj_app / rel_fun_app       rebuild the two predicates at the BIGGER list

⚠️⚠️ **NEITHER `rel_inj` NOR `rel_fun` NOR `flex_agree_rel` CAN BE AN OUTPUT
CONJUNCT.**  All three put `rel_atom` in a HYPOTHESIS position, so all three
are ANTITONE in ρ and in `V` — a premise that ran at a smaller `V` (the
assign walk's V-shrink, §8c.28 item 5) or at a restricted ρ cannot hand them
back at the caller's.  What travels is `rel_ext ρe`, a statement about the
NEW pairs alone, and `rel_inj_app` / `rel_fun_app` rebuild the predicates
from it.  ⇒ every row re-establishes them from its OWN input plus the row's
surgery; only the inner part comes from the IH.

#### ✅ §8c.28's "ONE UNCHECKED SCOPING FACT" — CHECKED, AND IT MOVES

§8c.28 predicted `Assign-Skip` would need "the TAIL's payloads must not
mention `β`", with `a_wf_aenv` the likely source.

- ✅ The lemma EXISTS: `a_wf_aenv_ftv_dom` (algo/prop_basic.v:1373),
  `{{ ⊢ Θ }}a -> ftvar_in_aenv Θ [<=] dom Θ`.
- ⭐ But at `Assign-Skip` it is **not needed**, if the shrink is taken as
  `V' := V ∩ ftvar_in_aenv (Ξ ++ Θ0)` rather than as `remove β V`.  Then
  `rel_aenv_shrink_V`'s and `rel_pskl_shrink_V`'s used-part conditions are
  DISCHARGED BY CONSTRUCTION, and the only rule premise consumed is
  `Assign-Skip`'s own `β ∉ ftvar_in_pskl P` (with
  `V [<=] ftvar_in_aenv (Ξ ++ (β ~ ⌢) ++ Θ0)` giving `V \ V' ⊆ {β}`).
- ⛔ **Where self-scoping IS needed is `rel_fun_app`**, at a NEWLY generated
  context atom: `a ∈ dom Θ1 \ dom (Ξ ++ Θ0)` must miss `V`, and `V` is only
  bounded by `ftvar_in_aenv (Ξ ++ Θ0)`.  So the premise the transport has to
  carry is `{{ ⊢ (Ξ ++ Θ0) }}a` — which is also what the two tm-var skip
  rows need (their dropped entry has a PAYLOAD, unlike the flex/rigid ones,
  and nothing in the rule says the payload misses `ftvar_in_pskl P`).
- ✅ And it is INDUCTIVE where the naive `ftvar_in_aenv Θ [<=] dom Θ` is
  not: `a_wf_aenv` scopes each payload in **its own tail**, so it survives
  dropping a middle entry, whereas self-scoping of the whole context does
  not.  Outputs are covered by `a_assign_unify_consis_sound`'s conjunct 2
  (`{{ ⊢ Θ1 }}a`), which `Arrow`'s second premise needs.

#### ⭐ THE MOTIVE, AS DESIGNED (assign shown; unify/consis are the same minus `Ξ` / plus `Δ`)

    forall S0 Θ0' Ξ' α' P' ρ V,
      rel_aenv ρ V Θ0 Θ0' ->  rel_aenv ρ V Ξ Ξ' ->
      rel_atom ρ V α α' ->    rel_pskl ρ V P P' ->
      flex_agree_rel ρ V (Ξ ++ Θ0) (Ξ' ++ Θ0') ->
      rel_inj ρ V ->  rel_fun ρ V (dom (Ξ ++ Θ0)) ->
      {{ ⊢ (Ξ ++ Θ0) }}a ->  a_decls Ξ ->  uniq (Ξ' ++ Θ0') ->
      V [<=] ftvar_in_aenv (Ξ ++ Θ0) ->
      (forall a, a ∈ dom Θ1 -> a ∉ dom (Ξ ++ Θ0) -> a ∉ cols_l ρ) ->
      dom (Ξ' ++ Θ0') [<=] S0 ->  V ∪ cols_r ρ [<=] S0 ->
      ftvar_in_pskl P' [<=] S0 ->
      exists S1 ρe Θ1',
        {{ S0 ↝ S1 ⊨ Θ0' ⊲[ Ξ' ] α' ≔ P' ⊣ Θ1' }}e
        /\ rel_aenv (ρe ++ ρ) V Θ1 Θ1'
        /\ flex_agree_rel (ρe ++ ρ) V Θ1 Θ1'
        /\ rel_ext ρe (ftvar_in_aenv (Ξ ++ Θ0)) S0
        /\ (forall a b, In (a, b) ρe -> a ∈ dom Θ1 /\ b ∈ dom Θ1')

⚙ **The last conjunct is load-bearing three times over**: it re-establishes
the `cols_l` dodge for a SIBLING premise (`Arrow`'s second half — a newly
bound atom of `Θ2` cannot be in `cols_l ρe1`, because `ρe1`'s left atoms are
in `dom Θ1`), it feeds `rel_fun_app`, and it is what makes the ∀ rows'
`restrict_pairs α α2 ρe` still satisfy the spec (its members have left
atom ≠ α, hence lie in `dom Θ1` after the opener is stripped).

⚙ **`S0 [<=] S1` and `dom Θ1' [<=] S1` are NOT conjuncts** — both are
theorems of the e-derivation alone (`e_assign_unify_consis_supply_grows`,
`_dom_upper`), which is the same collapse §8c.25's edit 1 describes.

⚙ Coverage stays THREE separate premises (§8c.23's fsetdec cliff).

#### ⚙ THE ROUTES THE ROWS WILL TAKE — all four checked to EXIST

| need | source |
|---|---|
| side 2's `b ∉ dom Θ1'` (the e-side DROPPED the Barendregt premise) | `e_assign_unify_consis_dom_upper` + `uniq` + `dom (Ξ'++Θ0') [<=] S0` |
| side 1's opener ∉ `ftvar_in_aenv Θ1` (∀ rows' drop) | `a_assign_unify_consis_sound` conjunct 2, then `a_wf_aenv_ftv_dom` |
| side 2's opener ∉ `ftvar_in_aenv Θ1'` | `e_consis_sound` (⇒ the a-side fact), same two steps |
| the rigid-prefix SHAPE `(α ~ ⌢) ++ Θ1` | `a_assign_unify_consis_tvar_prefix` (L8) |

#### ⛔ WHAT IS LEFT

The 29 rows.  ⚙ Templates: §5-§7 for the ∀ / arrow shapes, and
`a_solve_eq_rel_e`'s `SE-Forall` case is the exact model for the pair
restriction + close.  ⚠️ Budget honestly: the four skip rows each need
~30 lines of `flex_agree_rel` surgery on their own (the V-shrink's `{β}`
has to be re-added by hand, using `rel_fun` to force side 2's head to be
`β` as well), and `Assign-SolveM` composes `a_guess_mono_rel_e`.

### 8c.30 ⚙ THE TRIO'S WALK KIT, AND FOUR OF THE 28 ROWS MACHINE-CHECKED — the motive is VALIDATED (2026-08-20)

✅ **`make coq` rc=0, `README.v` 33/33, zero `Admitted`/`Axiom`.**
`prop_solve_rel.v` §10 is new (28 lemmas, all Qed) and `a_guess_mono_rel_e`
(prop_lift.v §4) is GENERALIZED.  The 28 rows are still not in the tree —
a mutual induction is all-or-nothing — but **four of them were written and
compiled against the motive**, which is what §8c.29's design needed.

#### ⭐⭐ WHAT WAS PROVED (in a scratch file, then harvested)

| row | what it took | the point |
|---|---|---|
| `Assign-UnivGhost-Id` | `rel_aenv_cons_inv_l`, then `rel_fun` to force `α' = b` | the shortest witness that §8c.29's `rel_fun` is the right premise |
| ⭐⭐ `Assign-SolveM` | the guess (below), `rel_pskl_notin_r_inj`, `rel_ptyp_mono_ptyp`, `nodup_{fst,snd}_*`, `a_flex_tvar_solve_m` | **the hardest assign row, and it lands** — `rel_fun` gives the head/subject identification, `rel_inj` transports `α ∉ ftv P`, `rel_ext` is discharged from `uniq βs` + `e_guess_mono_uniq` |
| ⭐⭐ `Assign-Assign` | `rel_pskl_subst` (§9), `flex_agree_peel`, `a_wf_aenv_{strip_mid,mid_def_inv}`, `e_..._dom_upper` | the SUBSTITUTION row — and the V-SHRINK's first real use |
| `Assign-Depend` | `simpl_env` throughout, `rel_pskl_ftv_corr_l` + `rel_fun` for `β ∈ ftv P ⟹ b ∈ ftv P'` | the post transfers verbatim; the row is app-associativity |

#### ⭐ THE GUESS TRANSPORT HAD TO BE WIDENED, and the reason is exactly `Assign-SolveM`

`a_guess_mono_rel_e`'s scoping premise was `V [<=] ftvar_in_aenv Θ1`.  It is
**unsatisfiable at `Assign-SolveM`**: the guess runs at the walk's TAIL
`Θ0`, while `V` is bounded by the whole `Ξ ++ (α ~ ⌢) ++ Θ0` — and every
`Ξ` atom is in `ftvar_in_pskl P` by `Assign-Depend`'s own premise, so no
shrink of `V` to `ftvar_in_aenv Θ0` can keep `rel_pskl ρ V P P'`.  The
premise is now

    V [<=] ftvar_in_aenv Θ1 ∪ ftvar_in_pskl P1

which is what the ∀ row's OWN side condition
(`β ∉ ftvar_in_aenv Θ ∪ ftvar_in_pskl P`) always licensed.  ⚙ Strictly
weaker, so both existing consumers widen by one `fsetdec`.  The ARROW row
pays for it with a V-SHRINK, and that is free **because this lemma's only
conclusion about `V` is a `rel_pskl`, which is MONOTONE in `V`** — the
contrast with §8c.29's antitone trio is the thing to remember.

#### ⚙ §10 — THE WALK KIT

§8/§9 are about the RELATION; the walk rows also reason about the CONTEXT
SURGERY, and every such step is a statement about `a_flex_tvar`, which had
no algebra at all.  §10 gives it one — `a_flex_tvar_app_iff`,
`_one_flex` / `_one_other`, `_cons_other`, `_mid_other`, `_decls`,
`_notin_dom`, `_insert`, `_prepend`, `_head_flexish`, and
`a_flex_tvar_solve_m` (SolveM's whole surgery in one rewrite) — plus
`a_decls_{app,one,flex_pairs_l,flex_pairs_r}`, `rel_aenv_dom_{l,r}_inv`,
`rel_atom_mono_V`, `rel_{inj,fun}_weaken_V`, `flex_agree_rel_use`,
`rel_pskl_notin_r_inj`, `rel_ptyp_mono_ptyp`, `nodup_{fst_fun,snd_inj}`.

⭐⭐ **And the two moves EVERY walk row makes are factored**:
`flex_agree_peel` takes the agreement down to the tails (with `V` shrunk so
the peeled atom is out of it) and `flex_agree_reattach` puts the entry back
on both sides.  Between them they are what the four skip rows,
`Assign-Assign` and `Flex-Flex-Assign` all do; writing `Assign-Assign`
first and factoring afterwards was the right order.

#### ⭐ A NEW a-SIDE INVARIANT: `a_assign_unify_subject_flex`

    a_assign Θ0 Ξ α P Θ1 -> a_flex_tvar (Ξ ++ Θ0) α
    a_unify  Θ0 α β Θ1   -> a_flex_tvar Θ0 α /\ a_flex_tvar Θ0 β

⛔ WHY IT IS OWED: the V-SHRINK needs `α <> β` at `Assign-SkipRigid` and
the two `Assign-SkipTmVar` rows — an `α` that dropped out of `V` with the
peeled entry is no longer `rel_atom`-related — and those rows carry no such
premise (they do not need one on the a-side).  What supplies it is that the
walk's SUBJECT is flexible in its own context, so it cannot BE the rigid or
term-variable entry the row is peeling.  ⚙ Six of the fourteen rows are
`a_flex_tvar_prepend`; `Assign-Depend` is `simpl_env`.

#### ⛔ THE ONE DESIGN QUESTION LEFT OPEN, and it is at the TWO tm-var skip rows

`Assign-SkipTmVar` (both sorts) peels `(x ~ A)` / `(x ~ Q)` with **no
`x ∉ ftvar_in_pskl P` premise** — unlike `Assign-Skip` and
`Assign-SkipRigid`, which have one.  So the V-shrink cannot re-establish
`rel_pskl ρ V' P P'` there.  Two routes, and the first is the one the
soundness proof already takes:

1. ⭐ **Carry `{{ (Ξ ++ Θ0) ⨟ ∅ ⊢ₚₛ P }}a` in the assign motive**, exactly as
   `assign_sound_concl` does (prop_soundness_consis.v).  Then `x ∉ ftv P`
   because `a_wf_pskl__var` at `Δ = ∅` makes every free variable
   `a_binds_tvar`, which a `var_typ` entry is not; and
   `a_wf_pskl_strip_mid` (algo/prop_basic.v:1082) re-establishes the
   premise for the smaller context — it wants precisely that freshness.
   ⚙ The missing step is a lemma "the ftv of a `Δ = ∅`-wf skeleton are all
   `a_binds_tvar`"; the SHAPE is already a hypothesis at prop_basic.v:592
   and :673, so it may only need extracting.
2. ⛔ **Adding the slack `∪ ftvar_in_pskl P` to the scoping premise does NOT
   work**, and the refutation is worth keeping: it makes the four skip rows
   free, but the consis motive would then need
   `V [<=] ftvar_in_aenv Θ0 ∪ ftvar P0 ∪ ftvar P ∪ Δ1 ∪ Δ2` (the ∀ rows'
   own side condition, so that part is fine) — and **`Arrow` breaks**: its
   two premises see only HALF the skeletons each, so `V` must shrink, and
   the row then needs `flex_agree_rel` back at the larger `V`, which is
   ANTITONE (§8c.29).  ⇒ the consis motive must stay at the no-slack
   `V [<=] ftvar_in_aenv Θ0`, and `Assign-Assign` must hand it
   `V ∩ ftvar_in_aenv (Ξ ++ Θ0)` — which is what the proved row does.

#### ⚙ THE MOTIVE AS IT NOW STANDS (assign; the two others follow it)

Changed from §8c.29 in three places: side 2's `uniq` became
`{{ ⊢ (Ξ' ++ Θ0') }}a` (the `Assign-Assign` row needs
`ftvar_in_ptyp τ2 [<=] S0`, and only wf gives it), `a_decls Ξ'` joined
`a_decls Ξ`, and `a_flex_tvar (Ξ ++ Θ0) α` was added.

    rel_aenv ρ V Θ0 Θ0' -> rel_aenv ρ V Ξ Ξ' -> rel_atom ρ V α α' ->
    rel_pskl ρ V P P' -> flex_agree_rel ρ V (Ξ ++ Θ0) (Ξ' ++ Θ0') ->
    rel_inj ρ V -> rel_fun ρ V (dom (Ξ ++ Θ0)) ->
    a_flex_tvar (Ξ ++ Θ0) α ->
    {{ ⊢ (Ξ ++ Θ0) }}a -> a_decls Ξ -> a_decls Ξ' -> {{ ⊢ (Ξ' ++ Θ0') }}a ->
    V [<=] ftvar_in_aenv (Ξ ++ Θ0) ->
    (forall a, a ∈ dom Θ1 -> a ∉ dom (Ξ ++ Θ0) -> a ∉ cols_l ρ) ->
    dom (Ξ' ++ Θ0') [<=] S0 -> V ∪ cols_r ρ [<=] S0 ->
    ftvar_in_pskl P' [<=] S0 ->
    exists S1 ρe Θ1', e_assign … /\ rel_aenv (ρe ++ ρ) V Θ1 Θ1'
      /\ flex_agree_rel (ρe ++ ρ) V Θ1 Θ1'
      /\ rel_ext ρe (ftvar_in_aenv (Ξ ++ Θ0)) S0
      /\ (forall a b, In (a, b) ρe -> a ∈ dom Θ1 /\ b ∈ dom Θ1')

⚙ **`b ∉ dom Θ1'` — side 2 lost the Barendregt premise, and the row needs it
back.**  `e_assign_unify_consis_dom_upper` + `uniq` + `dom (Ξ' ++ Θ0') [<=] S0`
give it in three lines; that is the pattern for every re-attaching row.

#### ⛔ WHAT IS LEFT

24 rows: the four skips (blocked only on the `a_wf_pskl` premise above),
six `a_unify` (the same shapes, without `Ξ`), fourteen `a_consis`.  ⚠️ The
three ∀ rows of `a_consis` are the ones NOT yet validated: they must
`restrict_pairs`, push, and then DROP the opener pair off the output
CONTEXT — `rel_aenv_restrict` (§9) is what returns the conclusion to the
caller's list, and the opener's absence from `Θ1` / `Θ1'` comes from
`a_assign_unify_consis_sound` conjunct 2 (`{{ ⊢ Θ1 }}a`) plus
`a_wf_aenv_ftv_dom`, with `e_consis_sound` supplying the same on side 2.

### 8c.31 ⭐⭐ THE ASSIGN AND UNIFY BLOCKS LIFT — 14 of the 28 rows, and what the CONSIS block still needs (2026-08-20)

✅ **`make coq` rc=0, `README.v` 33/33, zero `Admitted`/`Axiom`.**
`prop_solve_rel.v` §11 is new.  **All eight `a_assign` rows and all six
`a_unify` rows were written against §8c.30's motive and compiled** — the
whole walk lifts.  The 14 `a_consis` rows are not written and the reason is
identified below; a mutual induction is all-or-nothing, so none of the 28 is
in the tree yet.

#### ✅ THE TM-VAR BLOCKER OF §8c.30 IS RESOLVED — and NOT by the `a_wf_pskl` route

`Assign-SkipTmVar` (both sorts) peels an entry with no
`x ∉ ftvar_in_pskl P` premise, so the V-shrink cannot re-establish
`rel_pskl ρ V' P P'` by freshness.  ⭐ The repair is the DELETE-don't-
strengthen move once more, run BACKWARDS: **`V` keeps `x` as an IDENTITY
PAIR while the premise runs, and the pair is deleted again at the
conclusion, where it is redundant.**  It is legal exactly because `rel_fun`
forces side 2's head to be `x` as well whenever `x ∈ V` — and when `x ∉ V`
there is nothing to shrink at all, which is the row's other branch.
⇒ no skeleton-well-formedness premise anywhere in the assign/unify blocks.

§11 lands the kit: `rel_pskl_shrink_V_id`, `rel_{atom,pskl,ptyp,abind,aenv}_drop_id`,
`flex_agree_rel_push_id_absent`, `rel_inj_push_id`, `rel_fun_push_absent`,
plus the binder-shape algebra the skip rows read —
`a_flex_tvar_one_nonflex` / `_cons_absent` / `_mid_nonflex_absurd` (what
gives `α <> β` at the rows carrying no such premise),
`a_flex_tvar_head_swap_flexish` and `flex_agree_rel_head_swap`
(`Flex-Flex-L/R`'s whole output move), `flex_agree_peel_cons`,
`a_wf_aenv_mid_var_typ_inv` / `_var_skl_inv`, `a_wf_aenv_cons_payload_ftv`.

⚠️ **CORRECTION to §8c.30**: `a_assign_unify_subject_flex` is NOT new — it
already exists at `algo/consis/prop_consis_rename.v:334`, beside
`a_assign_unify_consis_uniq` (:408).  §10's duplicate has been deleted and
replaced by a pointer.  Both had no consumer before; the V-shrink is one.

#### ⛔ WHAT THE CONSIS BLOCK NEEDS, and it is ONE premise package

`a_consis__arrow` runs its second premise at `Θ1`, the FIRST premise's
OUTPUT.  Everything the motive says about the context therefore has to be
re-established there, and `{{ ⊢ Θ0 }}a` is the one piece that does not come
free:

| needed at `Θ1` | source |
|---|---|
| `uniq Θ1` | ✅ `a_assign_unify_consis_uniq` (prop_consis_rename.v:408) |
| `V [<=] ftvar_in_aenv Θ1` | ✅ `V ⊆ ftvar_in_aenv Θ0 ⊆ dom Θ0 ⊆ dom Θ1` (`a_wf_aenv_ftv_dom` + `a_assign_unify_consis_dom_mono`) |
| `rel_fun … (dom Θ1)` | ✅ `rel_fun_app` (§9), with `Hblk` for the new atoms |
| ⛔ `{{ ⊢ Θ1 }}a` | `a_assign_unify_consis_sound` conjunct 2 — and its consis component wants SIX premises |

⇒ the consis motive has to carry `consis_sound_concl`'s package:
`{{ Θ0 ⨟ ∅ ⊢ₚₛ P0 }}a`, `{{ Θ0 ⨟ ∅ ⊢ₚₛ P }}a`,
`∀α ∈ Δ1∪Δ2, binds α abind_tvar Θ0`, `no_flex_dep (Δ1∪Δ2) Θ0`,
`flex_above_free (Δ1∪Δ2) Θ0` — and the assign motive
`{{ (Ξ ++ Θ0) ⨟ ∅ ⊢ₚₛ P }}a`.  ⭐ It is NOT extra invariant-maintenance
work: soundness' conjunct 4 re-establishes the Δ package at `Θ1`, and its
two output-relative side conditions (`Δ ∩ dom Θ1 [<=] dom Θ0` and
"a Δ-name outside `dom Θ0` misses the skeletons") are DISCHARGED by the
seventh premise below.

⭐ **AND THE PACKAGE PAYS FOR TWO MORE THINGS AT ONCE**, which is why it is
the right design rather than a tax:
- the two tm-var skip rows would no longer need §11's identity pair
  (`a_wf_pskl` at `Δ = ∅` makes every free variable `a_binds_tvar`, which a
  `var_typ` entry is not, so `x ∉ ftvar P` is a theorem);
- ⭐⭐ **the three ∀ rows' DROP** (§8c.28 item 2) becomes free: the premise's
  output is `(α ~ ⌢) ++ Θ1` and wf of it gives `α ∉ dom Θ1`, whence
  `a_wf_aenv_ftv_dom` gives `α ∉ ftvar_in_aenv Θ1` — exactly what
  `rel_aenv_restrict` (§9) needs to return the conclusion to the caller's
  pair list.  ⛔ Without it the opener pair would have to STAY in `ρe`, and
  then `a_consis__arrow`'s second premise — whose generated names avoid only
  `dom Θ1`, which the stripped opener is not in — could reinvent that
  opener and give one left atom TWO right images, which is precisely the
  configuration `rel_fun` exists to exclude.

⚙ **A SEVENTH premise, `Δ1 ∪ Δ2 [<=] ftvar_in_aenv Θ0`, is owed for a
different reason**: `rel_atoms` is ANTITONE in ρ (it quantifies over
related pairs), so `a_consis__arrow`'s second premise, which runs at the
WIDER `ρe1 ++ ρ`, must discharge the new pairs — and it does, because
`ρe1`'s left atoms miss `ftvar_in_aenv Θ0 ⊇ Δ1` and its right atoms miss
`S0 ⊇ Δ1'`.  ⚙ It is maintained: the ∀ rows add `α` to `Δ` and to the
context at once, and `Arrow` inherits it through `dom Θ0 [<=] dom Θ1`.

#### ⛔ WHAT IS LEFT

The 14 `a_consis` rows, once the package above is threaded through the 14
that exist (mechanical: the skip rows gain `a_wf_pskl_strip_mid`, and the
two tm-var rows SHRINK because the identity-pair branch disappears).
⚠️ Budget honestly: threading a seven-premise package through a 28-row
mutual induction is the bulk of the remaining work, not the consis rows
themselves — ten of those are one `inversion` and a `rel_pskl` constructor.

### 8c.32 ⭐⭐ 18 OF THE 28 ROWS — the whole WALK plus four of `a_consis`, and the ONE fact the ∀ rows still owe (2026-08-20)

✅ **`make coq` rc=0, `README.v` 33/33, zero `Admitted`/`Axiom`.**
`prop_consis.v` gains `e_assign_unify_consis_ctx_ftvar`; `prop_solve_rel.v`
gains §12.  Written and compiled against the motive: **all 8 `a_assign`
rows, all 6 `a_unify` rows, and `C-Ghost` / `C-Unit` / `C-Rigid` /
`C-Arrow`** — 18 of 28.  Still all-or-nothing, so none is in the tree.

#### ✅ THE PREMISE PACKAGE §8c.31 PREDICTED IS LANDED, AND SIDE 2 DOES NOT NEED IT

The consis motive now carries `consis_sound_concl`'s six premises plus
`Δ1 ∪ Δ2 [<=] ftvar_in_aenv Θ0`, and `C-Arrow` re-establishes them at `Θ1`
by applying `a_assign_unify_consis_sound` to its FIRST premise — conjunct 1
(`Θ0 ⊴ Θ1`), conjunct 2 (`{{ ⊢ Θ1 }}a`) and conjunct 4 (the Δ transport) are
exactly what the second premise wants.

⭐⭐ **AND SIDE 2's HALF OF THE PACKAGE IS NOT NEEDED AT ALL** — which is the
finding that made the row tractable.  Side 2's context is used for four
things only (`uniq`, the mid-strip, the payload's supply bound, the head's
freshness), and all four follow from

    uniq Θ0'   and   ftvar_in_aenv Θ0' [<=] S0

so those two REPLACE `{{ ⊢ Θ0' }}a` in all three motives.  ⭐ Both are then
re-established at `Θ1'`: `uniq` through `e_consis_sound` +
`a_assign_unify_consis_uniq`, and the coverage through the new

    e_assign_unify_consis_ctx_ftvar  (prop_consis.v, 28 rows, Qed)
      ftvar_in_aenv Θ0 ∪ ftvar P0 ∪ ftvar P [<=] S0 -> ftvar_in_aenv Θ1 [<=] S1

— the CONTEXT twin of `_dom_upper`, and the half `dom_upper` does not give.
⚙ Its 28 rows are 16 one-liners after the growth facts; the work is in
`Assign-SolveM` (`e_guess_mono_ftv` + the two block lemmas), the two
substitution rows and the three ∀ rows.

#### ⭐ AND §8c.31's OTHER PREDICTION HELD: the tm-var rows STOP needing §11's identity pair

With `{{ (Ξ ++ Θ0) ⨟ ∅ ⊢ₚₛ P }}a` in the assign motive, `x ∉ ftvar P` is a
theorem (`a_wf_pskl_ftv_tvarish` + `a_binds_tvar_not_var_typ`), so
`a_wf_pskl_strip_mid` re-establishes the premise and the `x ∈ V` branch is
dead weight.  ⚙ §11's identity-pair kit is kept: it is what the rows were
first proved with, and it is the only route that needs NO skeleton
well-formedness at all.

#### ⛔ WHAT THE THREE ∀ ROWS STILL OWE — one fact, precisely

The ∀ rows restrict ρ (`restrict_pairs α α2 ρ`, as the solve layer's do),
push the opener pair, run the premise, and close.  Three of the four
obligations are discharged:

| obligation | source |
|---|---|
| side 1's opener off `V` and off `cols_l` | the rule's own `α ∉ ftvar_in_aenv Θ0` + `V [<=] ftvar_in_aenv Θ0`, and `restrict_pairs` |
| the premise's wf / Δ package at `(α ~ ⌢) ++ Θ0` | `a_wf_pskl_all_syn_open_tvar`, and the Δ invariants by hand (~25 lines, written and compiled) |
| the YIELD's close | `rel_pskl_close_pair_restrict` — it UN-restricts, so the yield lands at the caller's ρ |
| ⛔ the CONTEXT's conclusion at the caller's ρ | see below |

⛔ **The gap.** `rel_aenv` is monotone in ρ, so widening back is free once
the opener PAIR is deleted — and deleting it needs only
`α ∉ ftvar_in_aenv Θ1`, which wf of the premise's output gives.  ⚠️ But
`flex_agree_rel` is ANTITONE, so the conclusion must also cover the pairs
`restrict_pairs` DELETED — the pairs `(α, b) ∈ ρ` — and for those it must
show `¬ a_flex_tvar Θ1' b`.  It is TRUE and the argument is short:
`α ∉ dom Θ0` makes the INPUT agreement give `¬ a_flex_tvar Θ0' b`, and the
run never makes an OLD atom flexible.  ⇒ what is owed is exactly

    a_assign / a_unify / a_consis:  a_flex_tvar Θ1 b -> b ∈ dom Θ0 ->
                                    a_flex_tvar Θ0 b

the CONVERSE of `a_assign_unify_consis_flex_preserve`
(algo/prop_inc_strengthen.v:119) restricted to old atoms — a 28-row mutual
induction whose rows are one or two lines each (every rule either keeps an
entry, turns `α̂` into `α̂ ≔ τ`, or adds a FRESH one).  ⚙ The pairs
`restrict_pairs` deletes on the RIGHT cannot occur: `α2 ∉ S0` while
`cols_r ρ [<=] S0`.

#### ⚙ §12 — the rung's prerequisites, and their natural homes

`a_wf_pskl_ftv_tvarish`, `a_binds_tvar_not_var_{typ,skl}` (prop_basic's
neighbourhood); `a_wf_pskl_weaken_tvarish`, `a_isub_wf_pskl` (prop_inc's —
⚙ `a_wf_pskl_weaken` itself is too strong, it asks for `binds`
preservation and the run turns `α̂` into `α̂ ≔ τ`);
`a_wf_aenv_mid_var_{typ,skl}_inv`, `a_wf_aenv_cons_payload_ftv` (the `_def`
twin already existed); and the two REL facts the arrow and binder rows
need — `rel_atoms_app` / `rel_ext_app` (both ANTITONE predicates re-proved
at a WIDER pair list from the new pairs' spec) and `rel_aenv_ftv_corr_r`.

### 8c.33 ⚙ IS THE `a_` LAYER'S EXISTS-FRESH DISCIPLINE A DETOUR? — the structural question, answered (2026-08-20)

Raised by the user while §8c.32 was landing.  The answer is *no for the
layer, yes for one rendering choice, and the choice does not generalize*.

#### ⭐ WHERE THE COST ACTUALLY IS

`a_*` is the PAPER's algorithm and carries all four theorems, the whole
completeness ladder, and every `[paper-gap]`; `e_*` exists for EXTRACTION
and DECIDABILITY.  Neither is removable.  What the lift pays for is ONE
difference between them: **the `a_` binder rows pick a LOCALLY fresh atom
(fresh for what that node can see) while `e_` draws from a supply that only
grows.**  Every piece of §§8-12's currency follows from that single fact:

- the two runs invent DIFFERENT atoms ⇒ nothing can be stated by equality,
  hence the pair list ρ;
- the correspondence is not even a FUNCTION — two `a_` nodes in different
  subtrees may reuse an atom where the supply cannot (§8c.25's Finding 1)
  ⇒ `rel_fun` is local to the context's domain (§8c.29);
- an `a_`-invented name may COLLIDE with an atom both sides agree on
  ⇒ `V [<=] ftvar_in_aenv Θ0`, hence the V-SHRINK along the assign walk.

#### ⭐⭐ AND COFINITE WOULD REMOVE IT — WHERE THE RULE CLOSES

A COFINITE rule hands its induction principle a **cofinitely quantified
IH**.  At a ∀ row the lift could then instantiate the IH at side 2's own
supply-fresh `α2`, and BOTH SIDES OPEN AT THE SAME ATOM: no pushed pair, no
`restrict_pairs`, no drop, and no antitone `flex_agree_rel` gap — i.e.
exactly the one fact §8c.32 says the three ∀ rows still owe.

⚙ And for `a_consis`'s three ∀ rows the cofinite rendering IS equivalent —
machine-checked, `a_consis_forall_{inh,syn}_cofinite`
(prop_consis_rename.v:1369, :1392), in the standard LN shape (the yield is
`open Q α` and the conclusion `pskl_all_syn Q`).  The de-cofinite conversion
was DESIGN.md §4.3's freshness campaign, for one discipline per layer, not
because cofinite was wrong there.

⚠️ **The renaming lemma is NOT a substitute.**
`a_assign_unify_consis_rename_tvar` (L9) moves a derivation's rigid opener
to any fresh atom — but it produces a NEW derivation term, and an induction
on the ORIGINAL derivation has no IH for it.  Only a cofinite RULE, or a
motive quantified over a swap, gives the IH at the atom one wants.

#### ⛔ BUT IT DOES NOT GENERALIZE — and that is why the currency is not wasted

Cofinite is degenerate exactly where a rule **LEAKS its binder into an
output that the whole family would have to share**:

- `a_sub__forall_r` — "the junk suffix `Ξ` may legitimately MENTION `α`, so
  a COFINITE premise sharing `Ξ` across the family is unsatisfiable in
  reachable configurations" (algo/def_rules.v, encoding fix 2026-07-31);
- the look / solve / guess clusters — all five collection ∀ rows leak
  (§8c.25's Finding 1), which is what killed the CHAIN currency.

`a_sub` is the NEXT rung.  So the pair/restriction/`rel_fun` machinery is
needed there no matter what, and switching `a_consis` to cofinite would be a
LOCAL saving on three rows, not a redesign.

#### ⚙ THE COSTING, AND THE CALL

| option | cost | buys |
|---|---|---|
| (A) finish the current path | ONE 28-row induction, one or two lines per row (§8c.32's owed fact), then 3 ∀ rows + 7 easy consis rows | the rung |
| (B) re-cut `a_consis`'s three ∀ rows as cofinite | 3 rules + 3 `e_` mirrors + every consumer that INVERTS them (soundness, completeness, `prop_consis_inc`, `prop_consis_rename`, the runner `def_consis_impl.v`, the decorated mirrors) | 3 of the remaining 10 rows |

⇒ **(A).**  Revisit (B) only if the ∀ rows resist after the owed fact is in
hand — and if they do, prefer the SWAP-QUANTIFIED MOTIVE (levels 1-2's
"rebind-by-ONE-swap") over changing the rules, since the swap only has to
move ONE atom and `algo/prop_swap.v` already has equivariance for all
fourteen judgements.

### 8c.34 ⚙ THE SAME COSTING ONE RUNG UP — what `a_sub` will need, and the ONE interface decision to take before its motive is written (2026-08-20)

Requested by the user before any `a_sub` row is written, because §8c.24's
CHAIN currency was retired one rung too late.  The three questions, answered
against the rules as they stand (`algo/def_rules.v:1385` for
`a_sub__forall_r`, `ext_algo/def_sub.v:74` for its mirror).

#### (i) WHICH OF §8–§12's CURRENCY `a_sub__forall_r` ACTUALLY NEEDS

Its shape is the consis ∀ rows' shape with ONE difference: both sides'
premise output is `Ξ ++ (α ~ ⌢) ++ Θ1`, not `(α ~ ⌢) ++ Θ1` — the junk
suffix sits ABOVE the opener and may legitimately mention it (that is the
2026-07-31 encoding fix, and it is why the row is exists-fresh).  So:

| needed | source | status |
|---|---|---|
| `restrict_pairs` + `cols_*_restrict_pairs` + `rel_{aenv,pskl,ptyp,abind}_restrict` | §9 | ⭐ verbatim |
| the opener PUSH (`rel_aenv__cons`, `flex_agree_rel_push_look`, `rel_inj_push`, `rel_fun_push`) | §9/§10 | ⭐ verbatim |
| the YIELD's close, un-restricting (`rel_pskl_close_pair_restrict`) | §9 | ⭐ verbatim |
| `rel_inj_app` / `rel_fun_app` from the premise's `rel_ext` | §9 | ⭐ verbatim |
| the PEEL — ⭐ **already stated at `a_sub`'s shape**: `flex_agree_peel` is `Ξ ++ (β ~ bd) ++ Θ0` vs `Ξ' ++ (b ~ bd') ++ Θ0''` (prop_solve_rel.v:3917); the consis rung only ever used its `Ξ = nil` corollary `flex_agree_peel_cons` | §10/§11 | ⭐ verbatim |
| ⛔ a `rel_aenv` APP-INVERSION — `rel_aenv ρ V (Ξ ++ Θ) Θ2 -> exists Ξ2 Θ2', Θ2 = Ξ2 ++ Θ2' /\ rel_aenv ρ V Ξ Ξ2 /\ rel_aenv ρ V Θ Θ2'` | NEW | ~15 lines, positional, no new idea |
| ⛔ the DELETED-PAIR obligation (`flex_agree_rel` is ANTITONE) | see (iii) | the ONE real cost |

⚙ `flex_agree_peel`'s two side conditions are already ON the rules:
`α ∉ dom (Ξ ++ Θ0) ∪ dom Θ1` is `a_sub__forall_r`'s own premise (and `Ξ`
there IS the output junk), and `α2 ∉ dom (Ξ2 ++ Θ1')` follows on the `e_`
side from the supply discipline (`α2 ∉ S0`, `Ξ2`'s names drawn above
`add α2 S0`).  ⇒ nothing new is owed there.

#### (ii) DOES `a_extract_rel_e`'s ρx COLUMN MAKE `rel_fun` UNAVAILABLE?

**No — but its INTERFACE does, and the fix is one conjunct.**

`a_extract_rel_e` (prop_lift.v:2033) hands its caller a yield at
`ρx ++ ρn ++ ρ`, where ρx is the LEAKED OPENERS: `a ∉ ftvar_in_aenv Θ1` and
`b ∉ S0`.  `rel_fun`/`rel_inj` are ANTITONE in ρ, so the caller
(`a_sub__forall_l`, the only consumer) has to REBUILD them at the wider
list — and `rel_inj_app` / `rel_fun_app` do exactly that, from a `rel_ext`.
`rel_fun_app` wants `D0 [<=] W` with `D0 = dom Θ0` and `W` the avoid set;
`dom Θ0 [<=] ftvar_in_aenv Θ0` holds by construction
(`dom_subset_ftvar_in_aenv`), so the ρx column is NOT an obstruction.

⛔⛔ **AND THE FIX THIS SECTION FIRST PROPOSED IS REFUTED — by §8c.29, which
was already written.**  The proposal was "return `rel_ext ρx (ftvar_in_aenv Θ1) S0`
from `a_extract_rel_e`".  `rel_ext` has THREE conjuncts, and the third is
LEFT-FUNCTIONALITY (`In (a,b1) ρe -> In (a,b2) ρe -> b1 = b2`) — which is
exactly what §8c.29 records as FALSE on this column:

> `rel_fun` is **LOCAL, on `D`**, and ⚠️ it CANNOT be global — §8c.25's
> Finding 1 IS a left atom with two right images, and that configuration is
> REACHABLE above the extract (`a_extract_rel_e` hands back a ρx column of
> leaked openers).

⇒ **do not strengthen `a_extract_rel_e` to a `rel_ext`.**  ⚙ Checked, not
inferred: `a_looksub_lookeq_rel_e` (prop_solve_rel.v §7) is where ρx is born,
and its spec is four conjuncts — `a ∉ add α (ftvar_in_aenv Θ1) /\ b ∈ S1 /\
b ∉ S0`, `cols_r ρx ∩ dom Ξ2 [=] empty`, `a ∈ ftvar_in_a_cstrs C1`,
`cols_l ρx ∩ dom Ξ1 [=] empty` — none of them an injectivity, so the
strengthening would have to be pushed down a whole layer even if it were true.

⭐ **WHAT ACTUALLY PAYS, and why nothing is owed for `rel_fun`.**  Read
`rel_fun_app`'s proof: the left-functionality of ρe is consumed in ONE branch
only, `a ∈ D1 \ D0`.  And ρx's left atoms are outside the context's domain
altogether — `a ∉ ftvar_in_aenv Θ1 ⊇ dom Θ1` and `cols_l ρx ∩ dom Ξ1 [=] empty`
— which is precisely §8c.29's "a leaked opener is bound NOWHERE".  So at
`D = dom (Ξ ++ Θ0)` that branch is vacuous, and what the row needs is a
weaker-premise variant

    rel_fun_app_off : rel_fun ρ V D ->
                      (forall a b, In (a, b) ρe -> a `notin` D) ->
                      rel_fun (ρe ++ ρ) V D

(~8 lines, and `a_extract_rel_e` already returns everything it needs).

⛔ **THE ONE THING THAT MAY STILL BE OWED IS `rel_inj`, NOT `rel_fun`.**
`rel_inj_app` wants ρe RIGHT-injective (`In (a1,b) -> In (a2,b) -> a1 = a2`).
That is plausible — ρx's right atoms are supply draws, and §8c.29 calls
`rel_inj` "GLOBAL and true by construction: every right atom is drawn ONCE"
— but it is NOT among the four conjuncts above, so it would have to be added
at the LOOK layer.  ⚙ Whether the `a_sub__forall_l` row needs `rel_inj` at
the widened list at all is not yet known; settle it when the row is written,
and do not pre-emptively re-open `a_looksub_lookeq_rel_e`.

#### (iii) ⭐⭐ THE ONE INTERFACE DECISION — take it BEFORE the `a_sub` motive

The deleted-pair obligation is the same at every binder row: for
`(α, b) ∈ ρ` thrown away by `restrict_pairs`, the conclusion still owes
`a_flex_tvar Θ1 α <-> a_flex_tvar Θ1' b`, and side 2's half needs

    a_flex_tvar Θ1' b -> b `in` dom Θ0' -> a_flex_tvar Θ0' b

(`b ∈ dom Θ0'` comes from `e_*_dom_upper` plus `cols_r ρ [<=] S0`).  There
are exactly TWO ways to get it, and they trade the same cost differently:

| route | what it costs | what it buys |
|---|---|---|
| (A) a per-family mutual induction — `a_assign_unify_consis_flex_rev`, what this rung used | ~180 lines ONCE per family; **no premise at all** (not `uniq`, not wf, not lc) | side 2 stays wf-free |
| (B) ⭐ the GENERIC `a_isub_flex_rev` : `Θ ⊴ Θ' -> uniq Θ' -> α ∈ dom Θ -> a_flex_tvar Θ' α -> a_flex_tvar Θ α` | ~40 lines ONCE for ALL families, but each rung must supply `Θ0' ⊴ Θ1'` on SIDE 2 | the rung's motive must carry side 2's wf package |

For the consis rung (B) was unavailable: `a_assign_unify_consis_isub` wants
`lc_aenv Θ0'` + `aenv_defs_lc Θ0'`, and §8c.32's finding is that side 2
carries only `uniq Θ0'` + `ftvar_in_aenv Θ0' [<=] S0`.  ⇒ (A), and it is
done.

⛔⛔ **CORRECTION (same day, on the user's challenge).**  An earlier draft of
this section said "one rung up the trade FLIPS, because `a_sub`'s soundness
gives `Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a` for free".  That reason is WRONG, and the
question it answers — *do the layers expose inconsistent interfaces?* — has
the answer **no**:

| rung | the ⊴ fact, and what it costs |
|---|---|
| `a_consis` | `a_consis_isub_wf` (consis/prop_consis_inc.v:492): `{{ Θ0 ⊢[…] }}a -> {{ ⊢ Θ0 }}a -> Θ0 ⊴ Θ1`; and `consis_sound_post` returns `Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ …` under the same `{{ ⊢ Θ0 }}a` |
| `a_sub` | `subtag_sound_concl` (sub/prop_soundness_subtag.v:1832): `{{ ⊢ Θ0 }}a -> … -> Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ …` |

Identical shape, identical premise.  ⚙ If anything `a_consis` is the STRONGER
of the two — it ALSO has the lc-only `a_assign_unify_consis_isub`, which
`a_sub` has no analogue of.  ⇒ **nothing to fix in the `a_` layer.**

⭐⭐ **WHERE THE ASYMMETRY ACTUALLY LIVES: the LIFT's own motive, which is
ours to choose.**  §8c.32 chose side 2 to carry `uniq Θ0'` +
`ftvar_in_aenv Θ0' [<=] S0` and NO well-formedness — that is what made
`C-Arrow` tractable, and under it no ⊴ is reachable on side 2, so route (A)
was forced.  It paid: `a_assign_unify_consis_flex_rev` needs no premise at
all.  The same two options are open at `a_sub`; the `a_` layer does not
prefer either.

⇒ **REVISED CALL: keep side 2 WF-FREE at `a_sub` too, and take route (A)
there as well.**  The argument is composition, not cost-per-lemma:

- `a_sub`'s rows CALL the consis lift (`a_sub__check` through
  `a_consis_chk`, which is a bare existential wrapper on `a_consis`,
  def_rules.v:1353; `a_sub__arrow`; `a_split__flex`).  A wf-free side-2
  package is WEAKER, so `a_sub` can always supply it — that direction is
  free.
- But a `a_sub` motive that carried `{{ ⊢ Θ0' }}a` on side 2 would have to
  RE-ESTABLISH it after every one of those calls, and the only route is
  `e_consis_sound` then `consis_sound_concl` — whose SIX premises at side 2
  are exactly the package §8c.32 removed.  ⇒ carrying wf on side 2 at
  `a_sub` re-imports the cost the consis rung just shed.
- And route (A) at `a_sub` is smaller than it looked: `a_sub` + `a_sub_flex`
  is **16 rows**, and the callees are already covered — `a_consis` /
  `a_consis_chk` by `a_assign_unify_consis_flex_rev`, `a_extract` because it
  has no output context to change.

⇒ **`a_isub_flex_rev` should NOT be built.**  One discipline for every rung:
side 2 carries `uniq` + the supply bound, and each family gets its own
premise-free flex-reflect.

⚙ Two smaller notes for the same motive:
- the consis CLOSER never consumes `rel_fun` after the IH — only `rel_inj`.
  `rel_fun` is spent solely by the ASSIGN WALK (it is what forces side 2's
  head to be side 2's subject).  `a_sub` has no walk of its own, so its
  motive carries `rel_fun` only to hand it down to the `a_consis` calls;
  do not look for a use of it in `a_sub`'s own rows.
- the V-shrink stays as it is: `a_sub__forall_r` opens at a name fresh for
  `ftvar A ∪ ftvar B` as well as the context, so `V [<=] ftvar_in_aenv Θ0`
  survives the push unchanged.

### 8c.35 ⭐⭐⭐ THE CONSIS RUNG IS CLOSED — all 28 rows, and the owed fact was NOT the induction it looked like (2026-08-20)

`a_assign_unify_consis_rel_e` is **Qed** (ext_algo/prop_lift.v §9): one
mutual induction, 28 rows, zero `Admitted`.  §8c.32's 18 rows plus the three
∀ rows and the seven remaining `a_consis` rows.  ⇒ the lift now reaches
`a_consis`; **`a_sub` is the next rung** (its costing is §8c.34, written
BEFORE any of its rows, as the user asked).

#### ⭐⭐ THE OWED FACT — smaller than §8c.32 predicted, and PREMISE-FREE

    a_assign_unify_consis_flex_rev   (algo/consis/prop_consis_rename.v §1b)
      a_flex_tvar Θ1 α1 -> α1 ∈ dom (Ξ ++ Θ0) -> a_flex_tvar (Ξ ++ Θ0) α1

28 rows, **no premise at all** — not `uniq`, not `{{ ⊢ Θ0 }}a`, not
`lc_aenv`.  §8c.32 guessed "one or two lines each" and that held: every
re-attaching row reads its OWN Barendregt premise (`β ∉ dom Θ1`) to kill the
head case, the rigid-head rows do the same, `Assign-SolveM` reads its block
freshness, and `C-Arrow` chains the two IHs through
`a_assign_unify_consis_dom_mono`.

⚙ **A route that was tried and rejected, and why it is still worth knowing.**
The fact also follows generically from the ⊴ order:

    a_isub_flex_rev :  Θ ⊴ Θ' -> uniq Θ' -> α ∈ dom Θ ->
                       a_flex_tvar Θ' α -> a_flex_tvar Θ α

(40 lines: `a_inc_binds_tvar` already existed, and the two term-entry KIND
transports are 6-row inductions — ⚠️ not the SYNTACTIC payload transports
deleted at prop_inc_strengthen.v:391, the payload here is existential).
⛔ It is unusable at THIS rung because `a_assign_unify_consis_isub` wants
`lc_aenv Θ0` + `aenv_defs_lc Θ0` and §8c.32's side 2 carries neither.  ⭐ But
at `a_sub` the trade flips — see §8c.34 (iii).  The lemma is NOT in the tree;
re-derive it there.

#### ⭐ WHERE THE FACT IS SPENT, and the shape of the three ∀ rows

`lift_consis_forall_close` (prop_lift.v §9) is the three rows' SHARED closer
— everything after the IH is rule-independent, so it is written once and the
three rows differ only in their premise package (~110 lines each, mechanical:
which Δ gains the opener, whether `P0`/`P` is `∀` or `⫯`).

The closer's one non-bookkeeping step is the DELETED PAIR.  `restrict_pairs α α2 ρ`
throws away every `(α, b) ∈ ρ`, and `flex_agree_rel` is ANTITONE, so the
conclusion still owes `a_flex_tvar Θ1 α <-> a_flex_tvar Θ1' b` there.  Both
halves are FALSE:

- side 1: `α ∉ ftvar_in_aenv Θ1` — from `{{ ⊢ (α ~ ⌢) ++ Θ1 }}a`, which is
  `a_assign_unify_consis_sound` applied to the premise;
- side 2: `b ∈ cols_r ρ [<=] S0`, so `e_assign_unify_consis_dom_upper` puts
  `b ∈ dom Θ0'` (the run's new names come from `S1 ∖ S0`); then
  `e_consis_sound` gives the `a_consis` image and **flex_rev** carries the
  input agreement's `¬ a_flex_tvar Θ0' b` down to `Θ1'`.

⚙ The pairs deleted on the RIGHT cannot occur (`α2 ∉ S0 ⊇ cols_r ρ`), exactly
as §8c.32 predicted.  ⚙ `α2 ∉ ftvar_in_aenv Θ1'` — needed to drop the pair
from `rel_aenv` — is **not** a freshness side condition but a consequence:
`rel_aenv_ftv_corr_r` produces a side-1 partner and `rel_inj` forces it to be
`α`, which side 1 has just shown absent.

⭐ **`flex_agree_peel` was already stated at the shape a_sub needs.**  The
consis rows use only its `Ξ = nil` corollary `flex_agree_peel_cons` — §8c.34
(i) records that the general form is what `a_sub__forall_r` will want.

#### ⚙ THE SEVEN REMAINING `a_consis` ROWS, and what each cost

`C-UnivGhost` / `C-UnivGhost2` / `C-UnivGhostR` strip a `⫯` off one, two or
three positions: one `inversion` on `rel_pskl`, one `a_wf_pskl` inversion for
the premise's skeleton wf, and `rel_pskl_guarded` / `rel_pskl_non_flex` for
the e-side rule's two dispatch premises.  `C-Flex` / `C-FlexL` / `C-FlexR`
hand to the unify / assign IHs — their `a_flex_tvar` obligation is
`a_assign_unify_subject_flex`, and the assign ones run at `Ξ = nil` (every
context premise needs a `simpl_env` first, which is why they are `assert`ed
rather than passed inline).  `C-GhostR` is an identity row whose only content
is `rel_atoms_disjoint`.

#### ⚠️⚠️ PERF — ONE `fsetdec` WAS 90 % OF THE FILE

The ∀ rows' `flex_above_free` obligation is
`(add α Δ1 ∪ add α Δ2) ∩ (add γ (dom Θb)) [=] empty` — six set atoms, and a
direct `fsetdec` costs **40 s PER ROW** (135 s for the three).  Splitting it
at the `add` (`inter_empty_add` + `inter_empty_cong_l`, prop_solve_rel §13)
takes the three rows to **7.4 s total**.  ⇒ the memory's "2 s at 5 atoms,
>120 s at 6" is confirmed once more, and the fix is always the same: extract
the ONE inclusion, then combine.

#### ⚙ WHERE THE NEW MATERIAL LANDED

- `algo/prop_basic.v` — `a_flex_tvar_cons_other` MOVED here from
  prop_solve_rel §10 (the consis rung's flex-rev lives in `algo/`).
- `algo/consis/prop_consis_rename.v` §1b — `in_dom_{mid,cons}_other`,
  `a_assign_unify_consis_flex_rev`.
- `ext_algo/prop_solve_rel.v` §13 — `restrict_pairs_in`,
  `rel_atoms_push_absent`, `inter_empty_add`, `inter_empty_cong_l`.
- `ext_algo/prop_lift.v` §9 — the three motives,
  `lift_consis_forall_close`, the three ∀ row lemmas, and the theorem.

### 8c.36 ⭐⭐ THE `a_sub` RUNG OPENS — its flex-reflect is landed, premise-free, 16 rows (2026-08-20)

`a_sub_sub_flex_flex_rev` is **Qed** (algo/prop_wf_preservation.v §5):

    a_sub:       a_flex_tvar Θ1 α1 -> α1 ∈ dom Θ0 -> a_flex_tvar Θ0 α1
    a_sub_flex:  a_flex_tvar Θ1 α1 -> α1 ∈ dom (Ξ ++ Θ0) ->
                 a_flex_tvar (Ξ ++ Θ0) α1

16 rows, **no premise** — the same discipline as the consis rung, and the
first concrete consequence of §8c.34 (iii)'s corrected call (side 2 stays
wf-free everywhere, so `a_isub_flex_rev` is not built).

⚙ What each interesting row reads:

| row | what pays |
|---|---|
| `Check` | the consis flex-rev, through `a_consis_chk`'s existential |
| `Arrow` | the consis flex-rev, then the IH, with `auc_dom_mono_consis` moving `α1` from `dom Θ0` into `dom Θ1` |
| `ForallR` | the junk suffix AND the opener both leave the output — weaken twice into `Ξ ++ (α ~ ⌢) ++ Θ1`, apply the IH, peel the opener (`α ∉ dom Θ0` from the rule's own freshness) |
| `ForallL` | the collection's block is PENDING, not an output: apply the IH at `Ξ ++ Θ0`, then `uniq (Ξ ++ Θ0)` puts an OLD atom off `dom Ξ` |
| `Flex-Solve` | the only row that peels THREE mid entries (`α̂0 ≔ α̂→β̂`, `β̂`, `α̂`) — `α̂0`'s case is answered by the conclusion's own head, and `α̂`/`β̂` cannot be old atoms because the rule's freshness dodges `add α0 (dom (Ξ ++ Θ0))` |

⚙ It needed one move `algo/` did not have: `a_flex_tvar_mid_other` (peel one
entry under a pending suffix), MOVED down from ext_algo/prop_solve_rel.v §10
next to `a_flex_tvar_cons_other`, which moved for the same reason yesterday.

⚠️ **TRAP PAID: a dangling EVAR reads as "incomplete proof term" at `Qed`
with no goals left.**  `eapply in_dom_mid_other; [ simpl_env; exact Hd | … ]`
lets `simpl_env` destroy the `(?c ~ ?bd)` shape before `exact Hd` unifies, so
`?bd` is never determined — and the row APPEARS to close.  Drop the
`simpl_env` and let `exact Hd` see the folded context.
