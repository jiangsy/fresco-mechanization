# HAND-OFF (OPEN, not started) — a second algorithmic encoding whose freshness is not a premise, and extraction from it

Two technical TODOs, recorded 2026-08-13.  Neither is started; this file is the
spec, the survey of what already exists, and the traps that are already known.

> **TODO (1)** — add a SECOND algorithmic encoding in which a rule's freshness
> side condition does not constrain its own OUTPUT, and prove it equivalent to
> the encoding the tree has today.
>
> **TODO (2)** — on top of (1), make the new encoding EXTRACTABLE.

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
- ⚠️ **`a_pat`'s four binder rows are still COFINITE** (`def_rules.v:1382`), the
  one departure from exists-fresh, left that way because converting re-opens
  theorems 1 and 3 (audit §1.7).  A new encoding either converts them — paying
  that cost — or carries the asymmetry.  Decide explicitly.
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
`PAPER-GAPS.md`.  ⚠️ Not yet filed there: file it only after confirming the
claim against the final paper, since a reviewer may read
`thm:complete-type-inference` as implying it (it does not — completeness says
a derivation EXISTS, not that a search finds it in finite time).

**⛔ DECIDED (user, 2026-08-13): NO FUEL.  Prove termination directly.**

A fuel parameter would make the function exist today at the cost of leaving the
real theorem unstated — and worse, a fuel-bounded runner is not the algorithm:
its `None` conflates "untypable" with "ran out", so it cannot even be compared
against `type.ml`, which has no such parameter.  ⚙ The tree's existing fuel
idiom (`ad_pat_sub_fuel`) is a PROOF device for a completeness induction and is
not a precedent for the runner.

So the deliverable is a well-founded recursion with a real measure, via
`Equations … by wf` (or `Function`), and **the measure is the open research
question of (2)** — settle it before writing any rules (§4).

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

See also: [`REPORT-postclosure-audit.md`](REPORT-postclosure-audit.md) §1.3,
§1.7, §2.1b; `DESIGN.md` §4.3 ("The look cluster") for why the freshness
premises are shaped the way they are; `CLAUDE.md`'s binder-encoding bullet for
the cofinite/exists-fresh split by layer.
