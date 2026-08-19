# Paper gaps and paper-flagged notes (re-mech)

> **Notation.** This file stays in the PAPER's notation.  In the Coq
> development the information-increase metasubstitution the paper writes
> `θ` is spelled **`κ`** (θ is unreadable next to the context Θ), and `ρ`
> is reserved for the paper's rigid-variable substitution.  See the
> metavariable convention in CLAUDE.md.

> ⚠️ **NAMES (2026-08-12).**  The `ad_pat_sub` family was reduced to TWO
> `Inductive`s.  What this file calls `ad_pat_sub_gv` (leaf-valid + fuel) is now
> **`ad_pat_sub_fuel`**, and it appears nowhere outside the completeness proof;
> `ad_pat_sub_g` (fuel without the leaf datum), `ad_pat_sub_n` and
> `ad_pat_sub_v` (the fuel existentially closed) no longer exist — the leaf
> presupposition sits on `ad_pat_sub` itself, so every rule and every statement
> in the tree uses the paper's own relation.  Names below are kept as written:
> they record the plan and the findings as they stood.

Canonical registry for everything found while mechanizing that the paper's
authors should see.  Ground rule (CLAUDE.md): paper definitions and lemma
statements are never changed; a broken proof STEP gets a repair here + a
`[paper-gap]` comment at the lemma; a genuinely FALSE statement (with a
counter-example) stops the work and is flagged to the user.

Each entry: status ∈ {GAP (confirmed proof-step problem, repaired),
PROSE-COMPLETION (figure rule completed from the paper's own prose),
WATCH (tension spotted, not yet confirmed to matter), FALSE (statement
refuted by a machine-checked counterexample — see the entries below, most
recently P6-Sv at the end of this file)}.

> **See also [WF-SIDE-CONDITIONS.md](WF-SIDE-CONDITIONS.md).**  The paper
> systematically states well-formedness (and sometimes a further judgment) as an
> EXTERNAL requirement in prose — "we require well-formedness of both …", "we
> already required well-formedness separately", "as usual, all inputs are
> well-formed" — and its rules then omit the side conditions well-formedness
> would supply.  A Coq `Inductive` has no such notion, so each of these becomes a
> proof obligation, either as a rule premise or as a hypothesis on every lemma.
> Several judgments looked broken until that condition was restored.  **Check
> that file before concluding a lemma is unprovable.**

## MISSING SIDE CONDITION (2026-08-19, machine-checked) — `LE-Arrow` / `LS-Arrow` run both halves at ONE context, so a ∀ OPENER leaked by one half and a FLEXIBLE invented by the other can be THE SAME ATOM — and the constraint solver's answer then depends on the collision

> **Status: OPEN in the mech.**  The refutation is
> `cex/probe_extract_conflated_opener.v` (four lemmas, all Qed and
> assumptions-closed).  The repair is proposed below and not yet landed —
> it is a rule change, so it is the authors' / user's call.

**Where.**  `fig:poly-info-extraction`, the two arrow rows of the
constraint collection.  Both premises run at the SAME `Θ`:

    Θ ⊢ P₁ ∼[α] P₁' ⤳ Ξ₁ ⨾ 𝒞₁      Θ ⊢ P₂ ∼[α] P₂' ⤳ Ξ₂ ⨾ 𝒞₂
    ----------------------------------------------------------- LE-Arrow
    Θ ⊢ P₁→P₂ ∼[α] P₁'→P₂' ⤳ Ξ₁,Ξ₂ ⨾ 𝒞₁,𝒞₂

**The finding.**  All five of the collection's ∀ rows LEAK their opener —
the reference implementation unbinds and discards the name
(`type.ml:579-613`, `:668-688`), so the opener may occur in `𝒞`.  A leaked
opener is *not* in `Ξ`, so no `uniq Ξ` condition can see it.  And the two
freshness side conditions

    LE-ForallInh   β ∉ {α} ∪ ftv(Θ) ∪ ftv(P) ∪ ftv(P')
    LE-FlexR       γ̂ ∉ {α} ∪ {β̂} ∪ ftv(Θ) ∪ ftv(P)

do not exclude each other.  At

    Θ₀ = β̂ ,   subject (α → (α→α)) → ∀. α ,   target (1 → β̂) → ∀. 0

both read `∉ {α, β̂}`, and the collection derives

    Θ₀ ⊢ subject ∼[α] target ⤳ γ̂ ⨾ [≐1, ≐γ, ≐γ]

where the FIRST `γ` is the flexible LE-FlexR invented in the left half and
the SECOND is the opener LE-ForallInh leaked in the right half.  **One
atom, two roles.**

**Why it matters — the collision is LOAD-BEARING.**  `look` hands `𝒞` to
the solver at `Ξ, Θ₀`.  There the leaked `γ` *is* hatted, because the
sibling half put it in `Ξ`, so `SolE-FlexR` fires on it.  Give the opener
any name the context does not bind — which is exactly what a run with a
global fresh counter does, since it draws the opener and the flexible at
different counter values — and the fold is STUCK: `1 ∼ δ` matches no
constraint-solving rule at all (not `SolE-Unit`: the target is not `1`; not
`SolE-Var`: the subject is not a variable; not `SolE-FlexR`: `δ` is not
hatted; not `SolE-GhostL` / `SolE-VacuousR`: neither side is `◇`; and no
`⫯` / `∀` / `→` row).  So the relation as written derives an extraction
**no run of the algorithm can produce**.

**Consequence for the mech.**  This is what blocks the last link of the
extractable-encoding chain: `a_extract ⟹ e_extract` is FALSE as stated
(docs/HANDOFF-extractable-algo-encoding.md §8c.25), and with it the
converse bridge the decidability corollary's NEGATIVE branch would need to
reach the paper's declarative judgement.

**Proposed repair — one side condition per arrow row:**

    ftv(𝒞₁) ∩ dom(Ξ₂) = ∅

It costs completeness NOTHING: it is a THEOREM of any run threaded through
a fresh-name supply (`ftv 𝒞₁ ⊆ S₁` under input coverage, and `dom Ξ₂` is
drawn outside `S₁`), so the reference implementation — one global counter,
never reused — cannot violate it.  ⚙ It is the same move the paper's own
`SolS-Arrow` already makes by threading its second premise at `Ξ₁, Θ`, and
the fourth instance of the freshness prose-completion this mechanization
has had to supply (`AT-Abs`'s `uniq (αs, Θ₁)`, `SI-ForallL`'s
`uniq (Ξ, Θ₀)`, and `guess^TY`'s `uniq Ξ`).  ⚠️ Threading the arrow rows'
CONTEXT — running the second half at `Ξ₁, Θ`, as the solve layer does —
fixes only the mirror direction (a right-half opener colliding with a
left-half flexible); the direction above survives it, because a left-half
opener is invisible to the right half no matter what the context carries.

---

## MISSING SIDE CONDITION (2026-08-17, machine-checked) — the COLLECTION rules lack the `α ∈ ftv(subject)` guard that renders the implementation's absence-first dispatch, so a collection call can spend a fresh name it never needed

> **✅ FIXED IN THE MECH ON BOTH ENCODINGS (2026-08-17/18).**  The five LEAKING
> rows of `frost/algo/def_rules.v` AND `frost/ext_algo/def_look.v` —
> `LS-ForallR`, `LS-ForallL`, `LE-ForallInh`, `LE-ForallSyn`, `LE-UnivGhost1` —
> now carry `α ∈ ftvar_in_pskl <subject>` (`LE-FlexR` already did).
> `make coq` rc=0, `README.v` 32/32.  **The finding below stands unchanged for
> the PAPER**: the figure still owes the exclusion premise on both of its
> collection judgements.
>
> ⭐⭐ **AND IT COST THE CONSUMERS NOTHING, because THE GUARD IS ADMISSIBLE** —
> the result worth passing to the authors alongside the gap itself.
> `algo/sub/prop_looksub.v` §2b proves each rule in its PRE-GUARD form
> (`a_looksub_forall_r_adm`, …) by the one case split the guard introduces: at
> an α-free subject the rule's own opener is fresh for `α`, so the premise
> collected NOTHING (`a_looksub_lookeq_absent_nil`) and `LS`/`LE-Absent`
> returns the very same answer.  **So the premise rejects no ANSWER the
> premise-free rule accepted, only a wasteful DERIVATION of it.**  Every
> construction site swaps a constructor for a lemma of the same name: the P6
> completeness chain — the estimated ~250-site risk — cost ELEVEN one-word
> substitutions, and `alpha_stack_looksub` was untouched.
>
> ⚠️ **The admissibility does NOT extend to the two REMAINING dispatch guards**
> (the `◇` exclusion the runner tests second, and the ForallR-before-ForallL
> priority).  Those change WHICH RULE fires rather than blocking a no-op, so
> they shrink the relation for real, they must be two-sided, and they make
> `alpha_stack_looksub` FALSE at a `◇` target.  Machine-checked in
> `cex/probe_vacuous_supply_drift.v`; the execution order is
> `docs/HANDOFF-extractable-algo-encoding.md` §8c.14.
>
> ⭐ **What it bought**, and it is exactly the refutation read forwards:
> `e_looksub_lookeq_absent_pins` (`prop_look.v` §2c) — at an α-free subject the
> collection returns `Ξ = ·`, `𝒞 = ·` **and the supply unchanged**,
> hypothesis-free.  The third conjunct is FALSE without the guard.
>
> ⛔ **The two refutations are RETRACTED**, because they refute the UNGUARDED
> rules and stop typechecking the moment the guard lands.  Their proof texts
> are preserved in git at commit **`eabf308`**; see "WHERE THE RETRACTED FILES
> WENT" below, to which their citations elsewhere now resolve.
>
> | deleted file | what it proved |
> |---|---|
> | `cex/probe_extract_supply_drift.v` | `e_extract_det_false` — `e_extract` is not deterministic up to a renaming: at `Θ = ·`, subject `1`, counterpart `∀_. 1`, `NM = SK`, LS-Absent spends nothing and LS-ForallR draws an opener, both emitting the empty collection |
> | `cex/probe_sub_supply_drift.v` | `e_sub_det_false` — ⭐ the drift REACHES SUBTYPING, which had been argued by inspection only.  At `NM = SK`, `M = FN TC`, `P0 = 1 → ∀_.1`, subject `∀_. (◇ → ◇)`, `SI-ForallL` runs the collection at the α-free subject `◇ → ◇` and the tail below the fork is two AXIOMS (`C-Ghost`, `SI-Ghost`), so the two derivations agree on their output CONTEXT and SKELETON and differ by exactly one atom of supply |

**Where.**  `LS-ForallR`, `LS-Arrow`, `LS-ForallL`, `LS-UnivGhostL`, `LS-Check`
and their `LE-*` twins (`full-algo-spec.tex`'s collection figure;
`frost/algo/def_rules.v:418-528` and its threaded copy
`frost/ext_algo/def_look.v`).  `LS-Absent` fires whenever the looked-for
variable `α` does not occur in the SUBJECT, and it is stated with no exclusion
against any of them.  The same holds for `LS-Vacuous` (counterpart `◇`).

**What the implementation does.**  It tests ABSENCE FIRST — `type.ml`'s
`constr_collect_sub` (:649-701) and `constr_collect_eq` (:542-626) — and this
tree's runner faithfully renders that: every non-Absent clause of
`e_looksub_impl` / `e_lookeq_impl` sits behind `mem α (ftvar_in_pskl P)`
(`frost/ext_algo/def_look_impl.v:360, 377, 393, 406, …`), with the Vacuous test
second.  A relational encoding has no match order, so the exclusion has to be a
PREMISE.

**Why it matters, machine-checked** (`cex/probe_extract_supply_drift.v`,
`e_extract_det_false`, Qed and assumptions-closed).  At

    Θ = ·      α ∈ S      subject  1      counterpart  ∀_. 1

`LS-Absent` collects nothing and spends nothing, while `LS-ForallR` peels the
counterpart at a freshly drawn opener and THEN collects nothing.  Both emit the
empty block and the empty constraint list, so the solving fold and the guess
agree — the two runs of `extract` differ ONLY in how much of the fresh-name
supply they consumed, by exactly one name.  Consequently `extract` is not
deterministic up to renaming: no bijection on names relates the two results,
because one result's name set properly contains the other's.

⚠️ The knock-on claim — that the drift reaches SUBTYPING through `SI-ForallL`
(at `NM = TY`, `M = FN TC`, counterpart `1 → ∀_. 1`, subject `∀β. (1 → 1)`), so
the algorithm's own answer is not merely one of several equally-general ones but
differs in name COUNT from a legal derivation — is argued by inspection in that
file's closing note and is not yet machine-checked.

**The repair, and its MEASURED cost (2026-08-17).**  The premise
`α ∈ ftv(subject)` is enough on the LEAKING rows alone — `LS-ForallR`,
`LS-ForallL`, `LE-ForallInh`, `LE-ForallSyn`, `LE-UnivGhost1` (`LE-FlexR`
already carries it) — because those are the only rows that spend a name, and
at an α-free subject every remaining rule is a no-op hereditarily.

⚙ The change was carried through the mechanization far enough to be decisive
and then reverted.  **No semantic obstruction appeared.**  The guard threads:
it survives an opening (`ftvar_in_pskl_open_pskl_wrt_pskl_lower`) and survives
a substitution (the substituted variable is `≠ α`, so
`ftvar_in_pskl_subst_pskl_in_pskl_lower` keeps it); each of the two transport
tactics it needs is three lines; and where a rule can no longer fire, the
`LS-Absent` row gives the SAME block and collection
(`a_looksub_subject_absent`), so the answer that replaces it is the empty one.
Two lemmas were written and pass: `e_looksub_lookeq_absent_pins` — at an
α-free subject the collection returns `Ξ = ·`, `𝒞 = ·` **and the supply
unchanged**, hypothesis-free, which is exactly what the guard buys — and
`rel_e_absent_{sub,eq}`, the empty answer for the a→e transport.

⛔ What it costs is BREADTH.  Both encodings: ~70 constructor sites and ~170
case labels over twelve files, of which `algo/sub/prop_looksub.v` (32 sites),
`deco_algo/prop_decorate_sub.v` (10) and the P6 `look/` chain are the bulk.
Scoped to the THREADED encoding alone — which is where the fact it protects
(the supply) lives, and where `e_looksub_sound` keeps the a-side untouched —
it is five files; `def_look.v`, `prop_look.v` and `prop_solve_rel.v` were all
carried to green, and the residue is `prop_look_pair.v`'s b-core, where the
breakage is not the guard but the `pose proof`-without-`as` names it shifts.
Budget a day, not a research risk.

⚙ This is the THIRD instance of one species in three days — `SolE-FlexR`'s `nonghost`,
`U-FlexL`/`U-FlexR`'s `≠ ◇`, `SI-Ghost`'s `M ≠ TI` — and the pattern is worth
stating to the authors directly: **wherever the reference implementation
dispatches by match order, the figure owes an exclusion premise.**

## MISSING SIDE CONDITION (2026-08-17, machine-checked) — `U-FlexL` / `U-FlexR` lack the `≠ ◇` guard that renders the implementation's ghost-first dispatch, so consistency is AMBIGUOUS at two cells and derives a strictly less general answer than the algorithm computes

`U-FlexL` (`algorithmic.tex:757`) and `U-FlexR` (`:764`) carry only
`nonflex{P_0}` / `nonflex{P}`.  That predicate rules out a flexible
VARIABLE — **it does not rule out a hole** — so at

```
    pattern ◇,  subject α̂   (α̂ an undefined flexible)
    pattern β̂,  subject ◇   (the mirror)
```

TWO rules fire, and they disagree on the OUTPUT CONTEXT:

| rule | output |
|---|---|
| `U-GhostR` / `U-Ghost` | `Θ` unchanged |
| `U-FlexL` / `U-FlexR`  | `α̂` SOLVED to `guess^TY(◇)`, a fresh unconstrained flexible |

⭐ **The implementation never takes the second route.**  Its consistency
clause matches the PATTERN first and the hole arm is unconditional in the
subject, so a `◇` pattern always answers by `GhostR`; the mirror arm bars
`FlexR` at a `◇` subject.  This is exactly the situation the paper's own
`SolE-FlexR` is in, where the mechanization already carries
`nonghost{P}` as a premise for the same reason (`algo/def_rules.v`, and
the note in this file's `SolE-FlexR` entries): **a relational encoding has
no match order, so a dispatch exclusion must be a premise.**

⚙ **The ghost route is also the RIGHT one**, independently of the
implementation: it leaves the flexible unsolved, where `FlexL` commits it
to a fresh unconstrained variable, so `GhostR`/`Ghost` is strictly more
general.  The rules as published therefore admit a derivation that is not
optimal, at a configuration that is REACHED — `(λf. f (λy. f y)) (λz. z)`
gets there through `AT-Abs`'s guess, `AP-AbsCheck`'s skeleton-`◇` binder
and `AP-Var`+`Arrow` (`cex/probe_pat_presents_hole_flex.v`).

**What the mechanization does**: `a_consis__flex_l` carries
`P0 <> pskl_hole` and `a_consis__flex_r` carries `P <> pskl_hole`
(`frost/algo/def_rules.v`), with the `ext_algo` twins identical.
Completeness is UNAFFECTED — `a_consis_complete` is re-proved with the
guards, by trying `C-GhostR` BEFORE the two flexible layers (the
implementation's own order) and adding the mirror `C-Ghost` node at a
flexible input.

⚠️ **What it cost to discover.**  Without the guards the two outputs must
be RELATED by the completeness proof, and five candidate relations are
machine-checked refuted: renaming (`cex/probe_consis_ghost_flex.v`), `⊴`
(`probe_isub_too_strong.v`), bare `a_inc` (`probe_inc_head_blind.v`), a
positional refinement (`probe_assign_migrates.v`) and the alias-collapse
function (`probe_collapse_orientation.v`, where the two sides pick
opposite REPRESENTATIVES for one equivalence class).  The guard removes
the problem at its source instead.

## MISSING SIDE CONDITION (2026-08-17, machine-checked) — `SI-Ghost` lacks the `M ≠ TI` guard that its NEIGHBOUR `SI-UnivGhostL` carries, so the relation derives inference-mode judgements against a counterpart the implementation never accepts

> **✅ FIXED IN THE MECH (2026-08-17).**  `a_sub__ghost` now carries
> `M <> mode_ti` (`frost/algo/def_rules.v`; `e_sub__ghost` likewise), which
> makes `SI-Infer` the ONLY rule at `TI` — every other row fixes the mode to
> `TC` or `FN _`, and `SI-ForallL` / `SI-UnivGhostL` already carried this
> very premise.  ⭐ The guard had to go ON THE RULE rather than onto a
> completeness motive, because the bad configuration is reached
> HEREDITARILY: `SI-Arrow` runs its second premise at `M` against the
> counterpart's codomain, so a root-level premise is vacuous one arrow down
> (`cex/probe_sub_ghost_ti.v` §3).  ⚙ Completeness is UNAFFECTED — the
> subtyping bundle's ghost case already carried `skmod[SK]{P0}{M}`, which
> forces `P0 = ◇` at `TI`, so it simply names `SI-Infer` there instead;
> that is the same invariant `type.ml`'s fused `mode` has by construction.
> The probe now machine-checks the RESOLUTION (relation and runner agree,
> at the root and one arrow down).

**What the paper says.**  `SI-Ghost` (`full-algo-spec.tex:849-853`) is an
axiom over an arbitrary mode:

```
  ─────────────────────────────── SI-Ghost
   Θ_0 ⊢[SK][M][P_0] □ ⩽ P_0 ⊣ Θ_0
```

The very next rule in the same figure, `SI-UnivGhostL` (`:855-860`), does
carry the restriction, with the paper's own comment on the line:

```
  M ≠ TI          % should not inst when TI
```

**Why the omission bites.**  At `M = TI` there is no counterpart to check
against — that is exactly why `SI-Infer` (`:795-797`) fixes `P_0 = □`.  With
`M` unrestricted, `SI-Ghost` also fires at `M = TI` for an ARBITRARY `P_0`,
and returns that `P_0` as the result: a counterpart nothing synthesised.

**The authors' own implementation carries the restriction.**  Its `SI-Ghost`
clause patterns the mode explicitly, and `Infer` is not among the shapes it
matches (`paper/artifact/implementation/lib/type.ml:981-984`):

```ocaml
  (* SI-Ghost *)
  | (Fun _ | Check _), Sk, Ghost ->
    rule "SI-Ghost" >> end_rule @@ sk_of_mode m
```

— the same `(Fun _ | Check _)` guard its `SI-UnivGhostL` (`:976`) and
`SI-ForallL` (`:957`) carry, and `SI-Infer` (`:903-906`) is the first clause
of the match, taking `Infer` for every subject.  So the paper's figure is
strictly more permissive than the algorithm it specifies: it admits
derivations no run produces.

**Machine-checked** in `cex/probe_sub_ghost_ti.v` — at `NM = SK`, `M = TI`,
`P_0 = 1`, subject `□`, the relation derives the judgement (§1) and the
mechanized runner returns `None` (§2), the latter for EVERY termination
proof, since its `TI` arm consumes none.

**Suggested repair.**  Add `M ≠ TI` to `SI-Ghost`, matching `SI-UnivGhostL`
and the implementation.  It costs nothing reachable: at `(TI, □)` — the only
inference-mode configuration that arises — `SI-Infer` already derives the
same triple `(Θ_0, P, Θ_0)` that `SI-Ghost` would.

⭐ **A second, larger observation the same clause exposes, and it is not a
gap so much as an invariant the paper leaves implicit.**  The figure carries
`M` and `P_0` as two independent indices, but the implementation fuses them
into ONE datum (`type.ml:8-11`), with a projection back to the paper's
`P_0` (`:395-398`):

```ocaml
  type mode = Infer | Check of pure_type | Fun of pure_type * mode

  let rec sk_of_mode = function
    | Infer -> Ghost
    | Check p -> p
    | Fun (p, m) -> TArr (p, sk_of_mode m)
```

So in the implementation `P_0 = sk_of_mode M` holds BY CONSTRUCTION: `TI`
pairs with `□` and cannot do otherwise, and each `FN` layer of the mode
pairs with one arrow of the counterpart.  The paper's two-index presentation
can express pairs that are not of this form, and `SI-Ghost` at `TI` is
simply the first place that shows.  ⚠️ Note the consequence for a
root-level repair: `SI-Arrow` concludes at `FN M` and runs its second
premise at `M` against the counterpart's CODOMAIN, so

```
  NM = SK    M = FN TI    P_0 = 1 → 1    subject 1 → □
```

reaches the offending configuration one level down, where a restriction
phrased on the judgement's root is vacuous (`FN TI ≠ TI`).  The probe's §3
checks that configuration's relation half.  Repairing `SI-Ghost` alone fixes
the rule; stating `P_0 = sk_of_mode M` as a standing well-formedness
condition on the judgement's indices — as the implementation's types already
do — would fix the class.

⚙ Found by the overlap audit run before mechanizing subtyping completeness
against the runner (`docs/HANDOFF-extractable-algo-encoding.md` §8c.11).
The same audit clears every OTHER apparent overlap in the figure: `guarded`
is `1 | α | A → B` and nothing else, so `∀`, `□` and `⫯` are unguarded and
the five candidate pairs — including `SI-Ghost` against `SI-UnivGhostR` at
`□ ⩽ □`, whose results would have DIFFERED (`P_0` versus `⫯P`) — cannot
both fire.

## MISSING SIDE CONDITIONS (2026-08-18, machine-checked) — `SolS-ForallR` and `SolS-Vacuous` lack the exclusions the implementation's MATCH ORDER supplies, so the SOLVE layer answers the same query with two different amounts of fresh supply

> **✅ FIXED IN THE MECH ON BOTH ENCODINGS (2026-08-18).**  `SolS-Vacuous`
> carries `peel_l_off P` (*"the subject is neither a `∀` nor a `⫯`"*) and
> `SolS-ForallR` carries `solve_l_off P` (*"…and not a variable either"*),
> which is `solve_sub`'s own match order.  `make coq` rc=0, `README.v` 32/32.
> **The finding below stands unchanged for the PAPER**: the figure still owes
> the two exclusion premises.
>
> ⚙ The refutation `cex/probe_solve_sub_forall_r_drift.v` is RETRACTED by the
> repair and deleted; its text is at commit `5e2384f`.  What the repair cost,
> and the one place where it MOVED work rather than removing it (the
> ForallL/ForallR commutation, now paid once in
> `a_solve_sub_forall_r_gen`), is in
> [`HANDOFF-extractable-algo-encoding.md`](HANDOFF-extractable-algo-encoding.md)
> §8c.18–§8c.19.

**What the paper says.**  `SolS-Var` answers a VARIABLE subject with itself in
any mode; `SolS-ForallR` peels a ghost-free `∀` counterpart in check mode at
an arbitrary subject; `SolS-Vacuous` answers a `◇` counterpart with the
subject, again at an arbitrary subject; `SolS-ForallL` peels a `∀` subject.
Neither `SolS-ForallR` nor `SolS-Vacuous` excludes the earlier rows' subjects.

**Why that is a gap.**  Two cells admit two derivations that agree on
everything the paper writes down and disagree on how many fresh names were
drawn:

| cell | the two rows | difference |
|---|---|---|
| subject `γ`, counterpart `∀_. 0`, mode `TC` | `SolS-Var` / `SolS-ForallR` then `SolS-Var` | ONE opener |
| subject `∀P`, counterpart `◇` | `SolS-Vacuous` / `SolS-ForallL` then `SolS-Vacuous` | ONE opener (`close β (open P β)` is `P`) |

Both answer with the same block (`·`) and the same skeleton, so on the paper's
own statement of the rules the two derivations are indistinguishable — which
is exactly why the gap is invisible until freshness is made explicit.

**The implementation does not have the ambiguity**, because `solve_sub`
(`lib/type.ml:494`) matches `SolS-Var` FIRST, then `SolS-ForallL`,
`SolS-ModL`, `SolS-UnivGhostL`, and only then `SolS-Vacuous` and
`SolS-ForallR`.  A relational presentation has no match order, so the
exclusions have to be premises.  This is the same species as the four
guards already filed (absence-first, ◇-dispatch, ForallR-priority,
FlexR-priority) — one layer further down.

**Suggested repair.**  `SolS-ForallR` gains *"the subject is not a variable"*
and `SolS-Vacuous` gains *"the subject is not a `∀`"* — or, mirroring the
match order exactly, both additionally exclude `⫯` subjects, which makes the
solve layer's dispatch single-rule.

**⚙ A third, independent observation.**  The implementation's `SolS-ForallR`
carries `when is_type a` — the SUBJECT must be ghost-free (`is_type` is
"contains no `Ghost` / `UGhost`") — and neither the paper's rule nor either of
the mech's encodings carries it.

**What is NOT affected.**  Soundness is untouched: it quantifies over the
derivations that exist.  What the gap blocks is the statement that the
algorithm is a FUNCTION of its inputs up to a renaming of the names it
invents, which is what a decidability corollary and any completeness proof of
the runner against the rules need.

## MISSING SIDE CONDITION (2026-08-18, machine-checked) — `LE-UnivGhost2` lacks the exclusion that would keep `LE-FlexR` off a FLEXIBLE counterpart, so the COLLECTION is still ambiguous at a ⫯ subject — and the two answers differ in KIND, not in names

> **✅ FIXED IN THE MECH ON BOTH ENCODINGS (2026-08-18).**  `LE-UnivGhost2` —
> and its `e_` twin — carries `flex_r_off Θ P'` (`frost/algo/def_rules.v`),
> *"`LE-FlexR` does not apply at this counterpart"*, and `LE-FlexR` gains the
> HAT it was missing, `a_flex_tvar Θ β`.  `make coq` rc=0, `README.v` 32/32.
> **The finding below stands unchanged for the PAPER**: the figure still owes
> the exclusion premise.
>
> ⭐ **AND THE MECH HAD A BUG OF ITS OWN HERE**, which the same repair fixes:
> `a_lookeq__flex_r` fired at ANY `pskl_var_f β`, so at a RIGID variable
> counterpart the runner invented a fresh flexible where the paper strips the
> ⫯.  That cell is ordinary — the counterpart is a sub-skeleton of the
> inherited type — so it was not a corner case.
>
> ⛔ **The CONTEXT-FREE form of the guard is REFUTED** (`remech-guard4-wip`):
> it is machine-blocked at `algo/sub/look/prop_eq_cstr.v`'s ⫯-grid, and the
> implementation sides with that site (`MFlex` ≠ `TVar`, `lib/type.ml:23`).
> The design, the four passes it took, and the two simplifications it bought
> are in
> [`HANDOFF-extractable-algo-encoding.md`](HANDOFF-extractable-algo-encoding.md)
> §8c.16.

**What the paper says.**  `LE-FlexR` (`full-algo-spec.tex:1110-1116`) concludes
at a HATTED counterpart,

```
  P ≠ α      α ∈ ftv(P)      fresh γ̂
  ------------------------------------------
  look_eq[α]{P}{β̂}{ ≐ γ̂ }[γ̂]
```

and `LE-UnivGhost2` (`:1155-1161`) carries exactly one side condition:

```
  guarded{P'}      look_eq[α]{P}{P'}{𝒞}[Ξ]
  ----------------------------------------
  look_eq[α]{⫯P}{P'}{𝒞}[Ξ]
```

**What is missing.**  `guarded` is defined on skeletons as *"`⫯.P` and `◇`
are unguarded"* (`declarative.tex:1304-1306`), so **a flexible `β̂` IS
guarded** — and at

```
  ⫯P   ≐?   β̂          (α ∈ ftv P,  P ≠ α)
```

*both* rules apply.  Their answers are of different KINDS:

```
  LE-FlexR       Ξ = γ̂            𝒞 = [ ≐ γ̂ ]      (a FRESH flexible, invented)
  LE-UnivGhost2  Ξ = the IH's     𝒞 = the IH's     (the ⫯ is stripped)
```

— at `P = α` the second is `Ξ = ·`, `𝒞 = [≐ β̂]`, so the two disagree in the
block, in the collected constraint, and (with a threaded name supply) in how
much supply was spent.

**Which one is the algorithm?**  `LE-FlexR`.  `constr_collect_eq`'s match is

```
  LE-Var (type.ml:549) → LE-Absent (:553) → LE-Vacuous (:557)
                       → ⭐ LE-FlexR (:561) → … → LE-UnivGhost2 (:618)
```

and `MFlex` is a constructor DISTINCT from `TVar` (`lib/type.ml:23`), so the
row fires only at a FLEXIBLE counterpart; at a RIGID variable the match falls
through to `LE-UnivGhost2`.  So the minimal correct premise on
`LE-UnivGhost2` is *"`LE-FlexR` does not apply"*:

```
  P' is not a flexible variable
```

**Why that is not harmless, and where it bites.**  Machine-checked twice, in
the mech's `e_` (supply-threaded) encoding:

- [`cex/probe_bcore_ug2_flexr.v`](../cex/probe_bcore_ug2_flexr.v) — the two
  routes at the cell, plus the two folds below them (one succeeds, one is
  stuck).  Found 2026-08-16; the level-4 b-core DODGED it by being stated
  RUNNER-SIDED, which is sound there because that level's conclusion carries
  a rel-or-HATCH yield and no supply.
- [`cex/probe_extract_flexr_ug2_drift.v`](../cex/probe_extract_flexr_ug2_drift.v)
  (`e_extract_det_false`, Qed, assumptions-closed) — the LIFT, one arrow and
  one `LS-Check` up: at `NM = SK`, `m = TC`, `Θ0 = ·`, subject `(⫯α) → 1`,
  counterpart `β → 1`, two `extract` derivations at the SAME inputs differ in
  their BLOCK (`·` versus a singleton), so no renaming relates them.  Level 6
  cannot dodge it: `SI-ForallL` must move the DERIVATION's extract outputs
  onto the RUNNER's rails by a swap chain.

⛔ **THE FORK, AND THE CHEAP FORM IS REFUTED.**  Two guards are available:

| | premise on `LE-UnivGhost2` | verdict |
|---|---|---|
| (A) | `P'` is not a VARIABLE (context-free) | ⛔ **REFUTED** |
| (B) | `P'` is not a FLEXIBLE variable, *and* `LE-FlexR` gains `α̂ ∈ Θ` | ✅ faithful |

(A) is what the mech's own runner would justify, because `e_lookeq_impl`
takes FlexR at ANY variable counterpart — but that is the MECH being
unfaithful, not the paper.  It is machine-BLOCKED: `algo/sub/look/prop_eq_cstr.v`
:4676-4698, the P6 chain at a ⫯-headed subject against `P0 = pskl_var_f β0`,
BUILDS `LE-UnivGhost2` there, and under (A) that row is barred.  Parked on
branch `remech-guard4-wip` (`40f900c`) with the full measurement.

⭐ **AND THE MECH HAS ITS OWN BUG HERE, which (B) fixes.**
`a_lookeq__flex_r` / `e_lookeq__flex_r` (`frost/algo/def_rules.v`,
`frost/ext_algo/def_look.v`) fire at ANY `pskl_var_f β` — no `a_flex_tvar Θ β`
premise — where the paper's conclusion is at `β̂`.  Contrast the SOLVE layer's
twin `a_solve_eq__flex_r`, which DOES carry `a_flex_tvar Θ α` and documents at
length why the exclusion matters.  The two rows are mirror images and only one
of them was made faithful.

⚙ **SEVERITY.**  Presentation/metatheory, as with the `LS-ForallL` entry
below: the implementation is unambiguous and the paper's figure is not.  What
turns on it is any statement that speaks of *the* collected constraints — and,
in this mech, campaign level 6, which needs the collection's outputs to be a
function of its inputs up to renaming.

## MISSING SIDE CONDITION (2026-08-15, machine-checked) — `LS-ForallL` lacks the `guarded` guard that `SI-ForallL` carries "to avoid overlapping with ForallR", so the COLLECTION is not deterministic — and its two answers differ in SHAPE, not just in names

> **✅ FIXED IN THE MECH ON BOTH ENCODINGS (2026-08-18).**  `LS-ForallL` and
> `LS-UnivGhostL` — and their `e_` twins — carry `forall_r_off m P'`
> (`frost/def_shapes.v`), *"`LS-ForallR` does not apply at this counterpart
> and mode"*.  `make coq` rc=0, `README.v` 32/32.  **The finding below stands
> unchanged for the PAPER**: the figure still owes the exclusion premise.
>
> ⭐⭐ **AND THE GUARD REMOVES WORK RATHER THAN COSTING IT** — the result worth
> passing to the authors alongside the gap.  THREE mechanized lemmas existed
> only to repair the missing priority, and all three collapse:
>
> | lemma | what it did | now |
> |---|---|---|
> | `a_looksub_open_target_at_size` (`deco_algo/prop_decorate_sub.v`) | re-freshened a colliding binder inside the re-rooting — and that branch was the ONLY reason it was an induction on the SOURCE'S SIZE | two `exfalso`s |
> | `a_looksub_forall_r_first` (`ext_algo/prop_run_complete.v`) | the re-rooting itself: four rebindings + two context exchanges | two `exfalso`s |
> | `e_looksub_open_forall_l_first` (`ext_algo/prop_look_pair.v`) | the same, e-side, with a SUPPLY exchange as well | two `exfalso`s |
>
> ⛔ **What it did cost** is Lemma E.17's own proof, and in FIVE places, not
> the one this entry predicted: the `Sub-ForallR` α-stack step, and — not
> anticipated — both `Sub-ForallL` rows and both `Sub-UnivGhostL` rows, where
> the counterpart is the lemma's own parameter.  ⚠️ `SI-ForallL`'s published
> `guarded{P_0} or P_0 = □` does NOT discharge those four: it constrains the
> TOP-LEVEL collection call, while the induction descends under `Sub-ForallR`
> where the counterpart IS a `∀`.  Anyone writing this proof on paper meets
> the same four cases.
>
> ⭐ **The repair, in one line**: where `LS-ForallL` is blocked, PEEL THE
> COUNTERPART FIRST and carry the solve across the peel.  The collected
> constraints move in exactly ONE cell — the α-STACK leaf, where `LS-Var`
> deposits the counterpart itself — and there the two peels must agree on ONE
> opener.  They can: the solve's opener is forced (`SS-ForallR` hands its own
> binder back) but it can be SWAPPED, because it dodges both the block and the
> context and the output is scoped by those.
>
> ⛔ **`cex/cex_looksub_not_det.v` is RETRACTED by the guard** — its exhibit is
> precisely the overlap removed.  Its proof text is preserved in git at
> `remech`'s parent of the guard commit; see "WHERE THE RETRACTED FILES WENT".

**What the paper says.**  `SI-ForallL` (`full-algo-spec.tex:835-838`) carries
the premise

```
  guarded{P_0}  or  P_0 = □          % avoid overlapping with ForallR;
                                     % only need in an algorithmic presentation
```

— the comment is the paper's own, verbatim, and `P_0` is the *inherited*
(target) type.  `SI-UnivGhostR` (`:813-816`) carries the same guard for the
same stated reason (`guarded{P}`, "% avoid overlapping").

**What is missing.**  The *collection* judgement's own ∀ rules —
`LS-ForallR` (`:1049-1054`) and `LS-ForallL` (`:1065-1071`) — carry **no
such guard**.  `LS-ForallL`'s only commented-out side condition is
`M ≠ TI`.  So at mode `TC`, subject `∀β.P` and target `∀β.B`, *both* rules
apply.

**Why that is not harmless.**  `LS-Var` emits `≼M P'` where `P'` is the
**current target**, so peeling the target changes what gets collected.
At subject `∀_. α`, target `∀_. 1`, mode `TC`:

```
  LS-ForallL first:  ∀_.α ≼ ∀_.1  ↝  α ≼ ∀_.1  ↝  𝒞 = [ ≼TC ∀_.1 ]
  LS-ForallR first:  ∀_.α ≼ ∀_.1  ↝  ∀_.α ≼ 1  ↝  𝒞 = [ ≼TC 1    ]
```

Both derivations exist; both constraint lists are **closed** (no free type
variables), so this is not a choice-of-fresh-name difference that a
renaming could absorb — the two lists are simply different constraints.
Machine-checked: [`cex/cex_looksub_not_det.v`](../cex/cex_looksub_not_det.v)
(`cex_looksub_not_det`, Qed, axiom-free).

**Is the algorithm wrong?  No.**  Both lists are solvable, and the
reference implementation commits to `ForallR` (`type.ml:663`), so it
always collects the second.  What the omission costs is the *invariant*:
the paper presents `look[N][M]{α}{P}{P'}{𝒞}[Ξ]` as computing 𝒞 from its
inputs, and the rules as given do not determine it.  Anything that reasons
"the collection's output" — rather than "some collection's output" — needs
either the guard or a weaker, solve-level equivalence.

**Suggested repair, and what it costs — MEASURED (2026-08-16).**  The
guard cannot be `SI-ForallL`'s literal `guarded{P'} or P' = □`: that also
blocks a `⫯` target and a non-ghost-free `∀` target, where no other rule
applies at a `∀` subject, and "the target is guarded or `□`" is not an
invariant of this judgement (`LS-Arrow` splits a guarded arrow target
into halves of any shape).  The minimal correct premise is *"`LS-ForallR`
does not apply"*:

```
  ∀B.  P' = ∀B  →  M = TC  →  ¬ guarded-free(B)
```

⛔ **But it is NOT free, and the price falls on Lemma E.17's own proof.**
The change was carried through the mechanization far enough to be
decisive and then reverted.  Everything below the completeness layer
absorbs it mechanically — the runner discharges the premise from its own
dispatch, since the three ways a `ForallL` branch is reached are exactly
the three ways the premise holds.  What breaks is one step of the
look-completeness argument:

> an **α-stack** subject (`∀…∀. α`, the shape a `Sub-ForallR` leaves
> behind) collects the WHOLE target, *undescended*, for any target and
> any mode — because `LS-ForallL` peels the stack while the target stays
> put, and `LS-Var` fires at the leaf.

Mechanized as `alpha_stack_looksub`
(`frost/algo/sub/look/prop_sub_cstr.v:373`), whose comment records the
consequence the proof relies on: *"Sub-ForallR's stack branch never
invokes `LS-ForallR`, and the β it would have had to strip is simply
never introduced."*  With the guard that is false exactly at `M = TC`
with a ghost-free `∀` target — i.e. at the counterexample above, since
`∀_. α` *is* an α-stack.  The `Sub-ForallR` stack branch would have to be
re-derived against a PEELED target (`≼TC B[β]` in place of `≼TC ∀β.B`),
which changes what the solving half of the lemma is handed.

**So the authors have a real choice**, and it is worth their attention
either way: guard `LS-ForallL` and redo that step of Lemma E.17 with the
peeled target, or leave the rules alone and treat `look`'s output as
determined only up to solve-equivalence — in which case the paper should
not speak of *the* collected constraints.

⚙ **SEVERITY, checked against the running implementation (2026-08-16).**
This is a presentation/metatheory issue, **not** a defect in the
algorithm: the two collections are not merely both solvable, they solve
to the *same* result.  `SolS-ForallR` is the DELAYED `LS-ForallR` —
peeling a ∀ target during collection and peeling it during solving do the
same work, and *neither closes the binder* (`type.ml:517-518` opens the
RHS and discards the name; the paper's rule runs its premise at `B` with
β still free).  On the exhibit above both lists solve to `⫯1`.  So
nothing the implementation accepts or rejects turns on the choice; what
turns on it is any statement that speaks of *the* collected constraints
as a function of the inputs.

⚙ **MEASURED IN FULL (2026-08-18), and the finding for the PAPER is
unchanged.**  The guard was carried through the mechanization as
`forall_r_off m P'` (`frost/def_shapes.v`) on `LS-ForallL` and
`LS-UnivGhostL`, both encodings.  It is GREEN on fourteen of the fifteen
files it touches; the fifteenth is Lemma E.17's own proof
(`algo/sub/look/prop_sub_cstr.v`), exactly as predicted above.  The work is
preserved on branch `remech-guard3-wip` (`d78d8f6`) and the full design,
measurement and remaining obligations are in
[`HANDOFF-extractable-algo-encoding.md`](HANDOFF-extractable-algo-encoding.md)
§8c.15.

⭐ **Two things the measurement adds for the authors.**

1. **The guard is not merely affordable, it is REDUNDANT WORK REMOVED.**  Two
   mechanized lemmas exist only to repair the missing priority — one
   re-freshens a binder inside the reordering (and is a size induction solely
   for that branch), the other IS the reordering.  Both collapse to `exfalso`
   under the guard.  So the metatheory currently PAYS for the ambiguity, and
   the premise is where that payment belongs.

2. **The price is larger than the entry above estimated, and it is not the
   α-stack step alone.**  Five sites in Lemma E.17 need the premise: the
   `Sub-ForallR` α-stack branch (where it is outright FALSE, the target being
   a ghost-free `∀`), and — the ones not anticipated — both `Sub-ForallL` rows
   and both `Sub-UnivGhostL` rows, where the target is the lemma's own
   parameter and nothing bounds it.  ⚠️ In particular `SI-ForallL`'s own
   published guard `guarded{P_0} or P_0 = □` does NOT discharge them: it
   constrains the top-level collection call, while the lemma's induction
   descends under `Sub-ForallR`, where the target is a `∀`.  Anyone writing
   this proof on paper will meet the same four cases.

⛔ **Still open in the mechanization.**  The fork's other side, with the
measured evidence, is in
[`HANDOFF-extractable-algo-encoding.md`](HANDOFF-extractable-algo-encoding.md) §8c.7;
it is a USER decision.

## ✅ RESOLVED (2026-08-11) — `fresh Ψ'` must mean GLOBAL freshness, and all four subtyping judgements now read it that way

`ForallL`'s side condition is the single word *fresh* on `Ψ'`:

```text
    M ≠ TI      Ψ' fresh      tags{Ψ'}{φ}      Γ ⊢ φ      φ tagged
    [Ψ,Ψ'] Γ ⊢[M] C[φ/α] ⩽ B
    ───────────────────────────────────────────────────────────── ForallL
                   [Ψ] Γ ⊢[M] ∀^ε α. C ⩽ B
```

**The word has to mean GLOBAL freshness** — fresh for the SUBJECT's own tags,
not only for the tag context `Ψ`.  `lemma:precision-substitution` is FALSE over
derivations that have only the context-local reading, because **Arrow splits the
tag context but not the subject** (`[Ψ₁,Ψ₂]` goes to the two premises while the
subject keeps all its tags), so a tag can leave the context on one branch and
still sit in the subject on the other.  (The same conclusion was reached from the
`lemma:precision-substitution` side on 2026-07-24; see the entry near the bottom
of this file.)

Until 2026-08-11 the mechanization rendered the word **two different ways** — the
weak one on `d_sub` / `d_pat_sub` / `ad_pat_sub`, the strong one only on the fuel
mirrors `ad_pat_sub_g` / `_gv` — so a completeness statement over the declarative
judgements could not reach the mirrors the theorems consume.  **All four now
carry the strong reading**, as one extra premise per `ForallL` row:

```coq
    Ψ' ∩ ftag_in_utyp (utyp_all_etag ε C) [=] empty      (* d_sub *)
    Ψ' ∩ ftag_in_uskl (uskl_all_etag ε R) [=] empty      (* d_pat_sub, ad_pat_sub *)
```

**Cost: one lemma, and it is not bookkeeping.**  Roughly 35 of the ~38 build
sites are mechanical: every transport either keeps the subject, takes `Ψ' := ∅`,
or substitutes a type variable — and a substitution by a TAG-FREE term cannot
change a tag (`ftag_in_utyp_subst_tagfree` / `ftag_in_uskl_subst_tagfree`,
`frost/prop_tag.v` §0).  Two places are genuine obstructions, and one of them
is deep:

> **`d_consis_sub_trans_mid`** — CST, paper B.3, `decl/prop_general_subsumption.v`,
> feeding general subsumption.  Its `ForallL` case transports a derivation along
> `utyp_tag_refines C' Cmid`, where the subject **GAINS** tags (`utr_etag_syn`
> turns a `∀ˢ` into a `∀^ε`).  Rebuilding `ForallL` at `C'` owes
> `Ψ' ∩ tags(C') = ∅` and the derivation supplies only `Ψ' ∩ tags(Cmid) = ∅`;
> nothing local bounds the ADDED tags.  ⚠️ Neither can a swap repair it in place:
> a structural induction ties the IH to the ORIGINAL instantiation `φ`, and
> applying the swap to the IH's OUTPUT instead moves the subject too, because
> there the instantiation's tags and the refined subject's tags sit in the SAME
> term `T0[φ]`.

> **`d_sub_prefix_spine_perm`** — `decl/prop_stability.v`, the second and much
> smaller one.  It PERMUTES an argument spine, so the hygiene has to be
> re-established for a reordered subject.  Two lines of syntax settle it — ε
> tags are order-blind on a spine and blind to a ∀-prefix
> (`ftag_spine_utyp_perm`, `ftag_utyp_all_syn_n`) — once
> `d_sub_fn_all_syn_inv` / `_fnn_`, which are INVERSION lemmas, report the
> hygiene premise they were dropping.

**The repair for CST, and it is a general technique.**  Stop freshening node by node.

1. `frost/prop_tag.v` + `frost/decl/prop_tag_swap.v` §1–§2 — ε-tag
   EQUIVARIANCE.  `fresh` is a statement about NAMES, so the primitive is a
   TRANSPOSITION of two tags, which is an automorphism of `d_tags`,
   `d_tags_skl`, `d_wf_utyp`, `d_wf_uskl`, `d_consis`, `d_pat_consis`, `d_sub`
   and `d_pat_sub` with **no freshness side condition**.  (A one-way rename
   would need ε₂ fresh for the whole derivation, and "the tags of a derivation"
   is not collectable from a `Prop`.)
2. `decl/prop_tag_swap.v` §4 — a tags-BOUND twin `d_sub_tagsin U`: `d_sub`
   with `Ψ' [<=] U` on the two `ForallL` rows.  `d_sub_to_tagsin` COLLECTS the
   bound by a plain induction (no freshening anywhere); `d_sub_tagsin_of`
   forgets it.  ⚙ Its `ForallR` is EXISTS-FRESH where `d_sub`'s is cofinite —
   the collection must produce ONE `U` for the whole rule, and a cofinite
   premise would demand a bound uniform in infinitely many `α`.
3. `decl/prop_tag_swap.v` §5 — `d_sub_freshen`: with all the derivation's tags
   inside one `U`, a single chain of transpositions moves `U` off any finite
   set, provided that set avoids what the CONCLUSION mentions (its tag context
   and its subject's tags) — then no swap touches the conclusion.
4. `decl/prop_general_subsumption.v` — CST runs on `d_sub_tagsin U` against a
   tag-BOUNDED refinement `utyp_tag_refines_in V` (the added tags confined to
   `V`), with one global `U ∩ V = ∅`.  Its `ForallL` case then closes from the
   node's own hygiene plus `Ψ' ⊆ U`.  ⚙ The bound must be carried by an indexed
   RELATION, not by the set inclusion `tags(C') ⊆ tags(Cmid) ∪ V` it implies:
   the inclusion does not survive descending into a ∀'s body, since
   `tags(∀^ε T0)` has already absorbed ε.
5. Both call sites (`decl/prop_stability.v`, the spine case of
   `d_sub_trans_spine`) discharge `U ∩ tags(C') = ∅` by (3) — legitimate exactly
   there, because the transported derivation runs at the EMPTY tag context and
   its subject is a PAINTING `⌈B⌉ˢ`, hence tag-free.

**What the paper's own statements lost: nothing.**  `d_consis_sub_trans` (the
paper's CST, `appendices/full-decl-proofs.tex:93`) gains `Δb [=] empty` —
which is verbatim the paper's own statement, which is at `·`; the general-context form was a mech-internal
inductive generalisation and survives as `d_consis_sub_trans_mid_tagsin`.
`d_sd_typing` / `d_typing` are untouched, and every `README.v` claim still
reports "Closed under the global context".

⚙ ONE THING SETTLED ALONG THE WAY (2026-08-11, independent): the non-hygienic
fuel mirror `ad_pat_sub_n` and its five bridge lemmas (~290 lines) had **no
consumer anywhere** — §1 of the completeness skeleton named it as the measure
but the development settled on the hygienic `ad_pat_sub_g` and never came back.
Deleted.  ⚙ And `ad_pat_sub_g` now differs from `ad_pat_sub` by its FUEL
discipline alone; the hygiene is shared.

## PROSE-COMPLETION (2026-08-10) — `app:decl-in-algo-context`'s "it is easy to extend them" is a CONSERVATIVITY lemma, and it holds in one direction only

`app:decl-in-algo-context` (full-algo-spec.tex:97-115) introduces the whole
decl-in-algo layer with

> *"Although all the declarative judgements in §declarative are defined on
> declarative contexts Γ, **it is easy to extend them to algorithmic contexts
> Θ**. For most rules we simply replace declarative contexts Γ with algorithmic
> contexts Θ… other rules simply switch from Γ to Θ."*

and then states **no conservativity lemma in either direction**.  Everything
in §D — including the four theorems — is therefore stated over `⊢ᵃᵈ`, and a
reader who has only met the §declarative figure never learns how to get back.

**The mechanization supplies the translation** (algo_decl/prop_conserv.v).
A declarative context IS an algorithmic one with no flexible variables
(`denv_to_aenv`), each `ad_` judgement is its `d_` version plus the
flexible-lookup rows, and those rows are vacuous in the image — so the
`ad_ → d_` direction is a plain induction, judgement by judgement:
consistency (both sorts), refinement, subtyping (both sorts), skeleton
inference and syntax-directed typing.  Three things the paper leaves implicit
have to be made explicit on the way, and each is a small finding of its own:

1. **The four explicit type-equivalence premises collapse to equality.**  The
   appendix adds `Θ ⊢ A ≡ B` to Freeze / AbsAnnoCheck / AbsAnno (and, per the
   2026-08-07 entry below, to App) *"because of the existence of flexible
   variables"*.  At a flexible-free Θ the equational theory has no definition
   to unfold, so `Θ ⊢ A ≡ B` implies `A = B` — which is exactly why the
   §declarative figure may silently reuse an annotation.
2. **The colour-discipline premises the two systems state differently must be
   RECOVERED, not assumed.**  `d_sub`'s Infer states `is_styp B`, its Check
   states guardedness of both sides plus `is_ityp B`, its ForallR states
   `is_ityp (∀ⁱ B)`; the fused `typsub^N_M` figure states none of them,
   because at `N = TY` they follow from the sort.  The mech proves that: the
   target is a `btyp`'s skeleton there, and a skeleton predicate on it
   transports back (`is_styp_of_btyp_to_bskl`, `is_ityp_of_btyp_to_bskl`,
   `ad_pat_sub_ty_tc_target_ityp`).
3. **The ∀-scope context Δ and the tvar context Γ swap roles between the
   sorts.**  Skeleton well-formedness and refinement put a bound rigid into Δ;
   type well-formedness puts it into Γ.  Translating a ForallL instantiation
   between the sorts therefore has to move the Δ-vars into Γ
   (`d_wf_utyp_of_d_wf_uskl`).

⛔ **The `d_ → ad_` direction does NOT hold as stated**, and the reason is not
bookkeeping.  Two independent obstructions, both recorded at
algo_decl/prop_conserv.v §12:

- **(A) the leaf-valid datum.**  `ad_pat` / `ad_sd_typing` embed the augmented
  join (`ad_pat_sub_v`), whose consistency leaves additionally carry the
  subject's refinement `Θ ⨟ ∅ ⊢ᵣₚ ⌊R⌋ ⊳ ⌊Q⌋`; `d_pat` / `d_sd_typing` embed
  the plain join.  The capture configuration (subject `∀X.◇`, counterpart
  `∀ˢX.X`) has a plain join and provably no leaf-valid one — see the ⛔ GAP
  entry of 2026-08-06 below and cex/cex_ad_pat_join_not_leaf_valid.v.
  ⭐ **What is new here**: at a GHOST-FREE subject the datum IS derivable from
  consistency alone (`d_pat_consis_subject_refine_ghost_free`, machine-checked).
  Since the three base rules of syntax-directed typing join `syn{A}` for a
  *type* `A`, TYPING's own base rules are never the obstruction; what is left
  is exactly **skeleton inference's P-Var at an entry `x : P` whose `P` has a
  ghost under a ∀** — which P-Abs may introduce with any well-formed `P`, and
  which typing reaches through App's skeleton-inference premise.
- **(B) tag hygiene — ✅ RESOLVED 2026-08-11**, see the entry at the top of
  this file.  The mech used to render the paper's prose `fresh Ψ'` two ways —
  GLOBAL on the fuel mirrors, tag-context-local on `d_sub` / `d_pat_sub` /
  `ad_pat_sub` — and the two come apart at Arrow, where the tag context is
  split but the subject is not.  All four now read it GLOBALLY, so this one is
  no longer an obstruction at either sort.

**Consequence for the paper.**  `thm:sound-type-inference` can be stated
against the §declarative system at a closed program and the mechanization now
does so (`a_typing_sound_infer` / `_check`, README.v) — modulo one further
step the paper does not mention, that the run's OUTPUT context still holds
flexibles and must be closed off by a metasubstitution `ζ ∷ Θ₁ ⊑ ·` before
the answer is a declarative type at all.  `thm:complete-type-inference`
cannot, for (A).

## PROSE-COMPLETION (2026-08-10) — `sd-Anno` must require its annotation well formed, like its four siblings

`fig:declarative-in-algo-context`'s **sd-Anno** is the one rule that puts a
type into the term without asking the type to be well formed in the context:

```
    Θ ⊢ᵃᵈ[TC] e ⦂ inh{A}      typsub^TY[∅] Θ ⊢ syn{A} ⩽ ⌊B⌋
    ─────────────────────────────────────────────────────── sd-Anno
                     Θ ⊢ᵃᵈ[m] (e : A) ⦂ B
```

Its four type-carrying siblings — sd-AbsCheck (→), sd-AbsAnnoCheck (→),
sd-Abs, sd-AbsAnno — all state `Θ ⊢ A`.  The join in the second premise does
not cover for it: the only wf a join yields is about its **target**
(`ad_pat_sub_target_wf` gives `a_scope_pskl Θ (bskl_to_pskl Qt)`), and
subject well-formedness is one of the paper's EXTERNAL side conditions
(docs/WF-SIDE-CONDITIONS.md).  So as printed, a derivation says nothing about
the scope of the types its subject mentions.

**The mechanization adds `a_wf_ptyp Θ A` to the rule** (2026-08-10,
algo_decl/def_typing.v).  It is free on the soundness side —
`a_typing_sound` already carries `a_wf_exp Θ0 e`, which stores exactly this
for every annotation — and it buys

```coq
Lemma ad_sd_typing_wf_exp : forall M Θ e B, Θ ⊢ᵃᵈ[ M ] e ⦂ B -> a_wf_exp Θ e.
```

i.e. a derivation EXHIBITS its own subject as a well-formed term, which is
what the paper's ambient "all inputs are well formed" is supposed to mean.
The visible payoff: `a_typing_complete_infer` (algo/typing/prop_closed.v)
— completeness of INFERENCE at a closed program — now has the declarative
derivation as its **only** premise.

⚠️ The corresponding fact does NOT hold for the ALGORITHMIC judgement, and
adding the same premise to `AT-Anno` would not make it hold: `AT-Abs` runs
the body under the flexibles `guess^TY` has just invented, and nothing stops
a nested annotation from mentioning one — so a run can accept a term whose
type variables are not those of its INPUT context.  `a_wf_exp Θ0 e` therefore
stays an input condition of `thm:sound-type-inference`, as in the paper.

## PROSE-COMPLETIONS (2026-08-07) — three facts thm:complete-skeleton-inference uses and never states

The mechanized `a_pat_complete` (algo/prop_completeness_pat.v) had to state
and prove three facts the paper's proof of thm:complete-skeleton-inference
(proofs.tex:1711-2197) uses silently:

1. **The Anno slack is the annotation's RIGIDITY.**  The `P-Anno` case
   needs `θ` to fix the annotation (`θA = A`).  This is true because an
   annotation is SOURCE syntax — its type variables are rigid, and an
   increase's domain is exactly the source context's FLEXIBLES — but it is
   a genuine side condition ON THE TERM, which the mech carries explicitly
   (`forall α ∈ ftv(annotations of e), Θ0 ∋ α rigid`; `msubst_ptyp_rigid_id`).
   ⚠️ The tempting `dom θ ∩ dom Θ = ∅` is FALSE for identity increases.

   ⭐ **THE PAPER ASSERTS THIS IN PROSE, MID-PROOF, AND NEVER AS A PREMISE**
   (located 2026-08-10).  The type-inference completeness proof's
   `sdty{Anno}` case opens with, verbatim (proofs.tex:679):

   > *Since annotations $A$ contain no flexible variables,*
   > $(\inc[\theta]{\Theta_0}{\Theta};A)$ *is a solution to the type
   > inference problem* $(\Theta_0;\TC;A;M)$.

   That sentence is the whole of the justification, and it is doing real
   work — it is what licenses re-entering the IH at the TC problem with `A`
   ITSELF as both the input skeleton and the solution's type.  ⚠️ It is NOT
   implied by the problem definition (algorithmic.tex:392), which asks only
   that "$P$ and $M$ are well-formed in $\Theta_0$": well-formedness gives
   SCOPE, not flex-freeness, and the paper defines term well-formedness
   nowhere — there is no `Θ ⊢ M` judgement in any figure and no prose
   definition.  So the mech premise is the CONJUNCTION of the definition's
   clause (in scope) and this in-proof sentence (not flexible), promoted to
   the statement where it belongs.

   ⚠️ The skeleton-inference twin does not even assert it.  Its `P-Anno`
   case (proofs.tex:1761-1773) ends "Our goal follows from
   $\inc[\theta]{\Theta_0}{\Theta}$ and $\Theta\vdash\precise{\theta A}{A}$"
   — the conclusion `θA ⊑ A` with no argument at all.  ⭐ Compare the `P-Var`
   case immediately above (:1744-1760), which discharges the SAME shape of
   obligation properly: "By $\inc[\theta]{\Theta_0}{\Theta}$ and
   $\Theta\ni x:P$, we have $\Theta_0\ni x:P'$ and $\theta P' = P$
   syntactically".  For a context lookup the paper derives the
   substitution's effect; for an annotation it writes both sides as `A` and
   moves on.

   ⭐ **`θA = A` IS NOT THE WHOLE REASON, and on its own it would NOT justify
   rigidity** (sharpened 2026-08-09, after the obvious weakening was
   questioned).  An UNRESOLVED flexible satisfies `θA = A` perfectly well:
   `is_id_entry` is literally `snd e = ptyp_var_f (fst e)`, so an identity
   increase maps each flexible to ITSELF.  The premise is carrying TWO
   obligations, and only the first is about `θ`:

   - (A) *the solution fixes the annotation* — `msubst_ptyp κ A = A`.  Needs
     only `α ∉ dom κ` (`a_inc_rigid_notin_dom`), which rigidity gives but so
     does an unresolved flexible under an identity `κ`.  **Weakenable.**
   - (B) *the RUN cannot rewrite the annotation* — `A' = A`
     (`a_typing_tc_rigid_output`), via `core_rigid` in `a_typing_ty_core`.
     This mentions no `κ` at all: it is about what the algorithm's own
     subtyping rows may do to `Θ0`.  `a_sub_sub_flex_ty_core` consumes the two
     NEGATIVE conjuncts of `a_rigid_only` at one row each —
     **Flex-Solve** uses `~ binds α' abind_flex_mono` to show the variable
     being solved is not a core variable (so an *unresolved* flexible is
     excluded: the row would solve it and the core would move), and
     **Flex-Assign** uses `forall τ, ~ binds α' (abind_flex_mono_def τ)` to
     show the walked definition misses the core (so a *defined* flexible is
     excluded: the row replaces it by `τ`).  **Not weakenable** — both kinds
     of flexible are ruled out, each for its own reason.

   So the premise is already the WEAKEST form of (B): with the `uniq` that
   `a_wf_aenv` supplies, `binds α abind_tvar Θ0` implies all three conjuncts of
   `a_rigid_only` (that is exactly how the Anno rows discharge them, by
   `binds_unique`), and nothing less does.  ⚠️ Allowing flexibles therefore
   requires RESTATING the Anno rows, not relaxing a hypothesis: `A' = A` would
   become something like `Θ1 ⊢ A' ≡ᵗ κA`, and the rows of theorems 3 and 4 that
   consume the equality would be re-proved against the weaker identity.  No
   caller wants this — no `a_typing`/`a_pat` rule substitutes a type into a
   term (`open_exp_wrt_exp` is the only rewriting of `e`), so a source
   expression's annotations can never come to mention the algorithm's own
   flexibles.
2. **"Consistency of syn{A} with bid{A}"** (the AbsAnno case, :2005) —
   a type's SYN painting is consistent with any of its BID paintings.
   Stated and proved as `ad_pat_consis_syn_bid` (induction over the wf
   derivation; the two ∀-colourings go through `forall_syn` /
   `forall_inh_untagged`).
3. **Reflexivity of context precision** (:1915) is NOT free at the mech's
   `Θ ⊢ ctx`: `a_wf_aenv__var` stores the DISCIPLINED `Θ ⨟ ∅ ⊢ₚₛᵃ P` for a
   skeleton term entry, which is what the paper's convention (every context
   wf in its own figure's sense, payload-wf included) asks for, and what
   refinement reflexivity needs — a scope-only payload refutes it
   (`ad_ctx_precise_refl`).

Also worth the authors' eyes: the paper's step "the solution θ' extends to
the binder-extended contexts" (⟨27⟩, :1927) is justified in the mech by
**identity witnesses being determined by their source** — any two identity
increases out of the same question context carry the same substitution
(`a_inc_id_msubst_unique`) — which is what lets the run's own identity
witness stand in for the universally-quantified one.

## ⛔ ⚠️ CORRECTED 2026-08-11 — this entry over-claimed. The paper DOES state the condition; the MECHANIZATION deferred it, and the deferral has now bitten

**Read this correction before the entry below.** The 2026-08-06 text says the
paper's solution notion for the two inference problems "does not carry the leaf
data", and that "the paper's own proofs invoke a theorem whose hypothesis they
have not established". Checked against the sources, both readings are too strong:

1. **The paper's three solution notions all carry a refinement datum** — at the
   ROOT. `algorithmic.tex:392` (type inference), `:559` (skeleton inference),
   `:1423` (subtyping) each read "…such that ⟨judgement⟩ **where**
   `Θ₁ ⊢ inh{θ₁P₀} ⊳ bid{P₁}`". The paper's own `sd-Sub` case
   (`appendices/proofs.tex:721-730`) transports that datum from the typing
   problem into the subtyping problem, so its chain is internally consistent.
2. **And the paper separately states the LEAF condition, as a presupposition on
   skeleton consistency itself**: `declarative.tex:2073-2075` — "skeleton
   consistency … requires well-formedness of `syn{S}` and `bid{P}` under Γ **as
   well as the refinement judgement `Γ ⊢ ⌊S⌋ ⊳ P`**". That is exactly the datum
   `ad_pat_sub_gv` carries at its consistency leaves. Registered all along in
   [`WF-SIDE-CONDITIONS.md`](WF-SIDE-CONDITIONS.md) §2 as `[WATCH]`.

So this is **not a defect in the paper's statements**: it is a presupposition the
paper declares and the mechanization deferred on the `d_` side. What the entry
below gets RIGHT, and what remains the finding, is that the presupposition is
**load-bearing and not derivable from the consistency rules** — machine-checked
at the capture configuration.

✅ **RESOLVED 2026-08-11 by carrying it.** `d_pat_sub`'s three
consistency-bearing rows and `d_pat`'s three base rows now state the two
presuppositions (`declarative.tex:2074` and `:1595`), so `d_pat` and `ad_pat`
agree row for row. `d_pat_to_ad` and `d_sd_typing_to_ad` are hypothesis-free
theorems, and the closed-program completeness corollaries are stated over the
paper's own `⊢ˢ` / `⊢` (`a_typing_complete_sd_infer` and its three siblings,
README.v). ⚠️ **For the authors the finding stands regardless of the mech**: a
reader who takes the consistency rules at face value gets a system that types
programs the algorithm provably cannot, so the prose sentence is doing real
work and should be visible in the figure.

⭐ Two things the correction adds:

- the ROOT datum does **not** imply the leaf one (`P₀ = ◇` makes the root
  condition vacuous while the subject captures), and moving the leaf condition
  to the root is wrong in the other direction (`cex_p7_univ_ghost_r_vacuous.v`,
  `cex_p7_third_premise_forall.v`) — so the leaf placement is forced;
- the consequences for the `d_` side are machine-checked in
  `cex/cex_d_pat_bridges_false.v`: skeleton inference read without the
  presupposition derives `x : ∀α.◇ ⊢ₛ[TI] x ⦂ ∀ˢα.α`, no bridge to the
  presupposition-carrying judgement exists, and `App`'s existentially quantified
  skeleton does not repair it.

**Author-facing note, in the paper's notation, with the repair costed:**
[`ghost-capture.tex`](ghost-capture.tex) — build with
`make -f Makefile.ghost-capture`.

---

## ⛔ GAP (2026-08-06, superseded by the correction above) — the SOLUTION notion for the two INFERENCE problems must carry the leaf data, exactly as the consistency one already does

`thm:complete-skeleton-inference` and `thm:complete-type-inference` are
stated over a declarative derivation `Θ ⊢ₛ[M] M ⦂ bid Q` / `typp[M]`, whose
`Unit` / `Var` / `Anno` rows embed a declarative SUBTYPING premise.  Their
proofs then invoke `thm:complete-subtyping` on that premise (proofs.tex:731,
:1811).

But `thm:complete-subtyping`'s own solution notion is not the paper's
2-condition one: the mechanization had to add the third condition of the
paper's AUGMENTED `thm:complete-consistency` (consistency-proofs.tex:
2230-2242) at every consistency LEAF of the join rather than at its root —
at the root it is vacuous, cutting exactly the ForallL / ForallR /
UnivGhostR solutions subtyping exists to produce (`cex_p7_univ_ghost_r_
vacuous.v`, `cex_p7_third_premise_forall.v`).

⭐ **So the inference problems' solution notion must carry it too, and the
gap is real rather than bookkeeping.**  Machine-checked in
`cex/cex_ad_pat_join_not_leaf_valid.v`, at the CAPTURE configuration of
DESIGN-subtyping.md §3.1:

    subject  ∀X.◇        counterpart  ∀ˢX.X

- the plain declarative subtyping derivation EXISTS (`Sub-Infer` on the
  consistency `∀X.◇ ∼ ∀X.X`, filling the ghost with the bound `X`);
- the leaf datum `Θ ⊢ ⌊∀X.◇⌋ ⊳ ⌊∀ˢX.X⌋` does NOT hold;
- and the configuration is reachable as `P-Var` at a context entry
  `x : ∀X.◇`.

⭐ The mechanism is the paper's own asymmetry: **consistency's ∀-rows put
the rigid `X` into `Θ`, so the ghost's fill may capture it; refinement's
∀-row puts it into `Δ` and the hole rule's fill is `Δ`-free** — which is
precisely the no-capture discipline the augmented consistency solution was
introduced to enforce.

For the authors: the fix is uniform — state "solution to the skeleton /
type inference problem" so that the embedded subtyping premise is itself a
solution in the augmented sense.  The mechanization carries this by making
the `ad_pat` / `ad_sd_typing` base rows embed the leaf-valid mirror
`ad_pat_sub_gv`.

---

## ⛔ GAP (2026-08-06) — `lemma:suffix-erasure` is NOT a "straightforward induction on the typing derivation"; its ForallL row is a genuine obstruction

    Lemma (Suffix erasure).  If typp[M]{Θ,Ξ}{M}{bid A} and Ξ is fresh for
    bid{A}, then typp[M]{Θ}{M}{bid A}.
    Proof.  Straightforward induction on the typing derivation.

**The statement is believed TRUE.  The proof is not the stated one**, and
the obstruction is not bookkeeping.

The typing judgement embeds the all-in-one subtyping judgement, whose
`ForallL` row **instantiates with a decorated skeleton `ψ` that the rule
chooses freely** — its only conditions are `Θ ⊢ tags{Ψ'}{ψ}` and
`Θ,Ξ ⊢ ⌊ψ⌋`, both of which admit a `ψ` mentioning `Ξ`'s variables.  The
sub-derivation then runs on `open R ψ`, which is *not* fresh for `Ξ`, so
the induction hypothesis does not apply — even though the conclusion is
`Ξ`-free.  The configuration is reachable: with `α̂ ∈ Ξ` **defined**, its
definition is a monotype scoped in `Θ`, so `∀a. a → 1 ⩽ Q` can be derived
through `ψ = α̂` with a completely `Ξ`-free `Q`.  Every other way a
derivation reaches into `Ξ` does surface in the types (the FlexL/FlexR
lookups and the rigid-variable rows all put the variable in the subject or
the target); `ForallL` is the one row that does not.

⚙ **The mechanization already had this insight one layer down.**
`ad_pat_sub_strip_suffix` (`algo/prop_pat_sub.v`), built during the
subtyping-soundness campaign, IS this lemma for the all-in-one subtyping
judgement, and `ad_pat_sub_subst_flex`'s header states the reason
verbatim: *"the ForallL witnesses are rewritten too, which is exactly why
this is provable where naive strengthening is not"*.  So the obstruction
is not news to the tree — but it is news to the paper, whose proof of
`lemma:suffix-erasure` is the one-line induction quoted above, for the
TYPING judgement, which sits above subtyping and inherits the problem.

**The route that works** (built for refinement, type equivalence and
consistency 2026-08-06; `algo/prop_suffix_erase.v`): erase by
**solving**, not by dropping.  A suffix of flexible entries always admits
a metasubstitution `θ` into `Θ` — map an undefined `α̂` to `1` and a
defined one to (the image of) its definition, which is well-scoped in the
tail by context well-formedness — so state the lemma as

    Θ,Ξ ⊢ J   ⟹   Θ ⊢ θJ            (θ solves Ξ into Θ)

and recover the paper's form because `θ` is the identity on `Ξ`-free
types.  At `ForallL` the instantiation becomes `θψ`, which is `Ξ`-free and
still a decorated skeleton (θ's images are monotypes: no quantifiers, no
ghosts, no tags).  Cost: one such transport per judgement the typing
derivation embeds (`⩽`, `⦂`, `∼`, `⊳`, `≡`, wf) — five context-carrying
ones, since `skmod{TY}` is context-free.

⚠️ **A weaker statement needs none of this**, and the mech may fall back
to it: if the theorem's conclusion is read up to a flexible suffix
("`typp{Ξ,Θ1}{M}{bid A}` for some suffix `Ξ`"), the four check rows close
by `lemma:suffix-moving` alone — which is free, because moving a block
changes no `binds` fact at all.  That is strictly weaker than the paper's
claim, so it is a fallback, not a fix.  **It is no longer needed**: the
solving route is being built and is already Qed for four of the six
judgements.

**What the authors should do**: replace the one-line proof with the
solving generalization, and say why — the ForallL instantiation is the
whole content of the lemma.

## WATCH (2026-08-06) — `thm:sound-type-inference` has TWO more inline steps with no lemma

Found while checking the mechanization's route against `proofs.tex`
app:proof-type-inference case by case.  Same species as the AbsAnno step
below: a clause of prose standing in for a lemma.  Marked WATCH rather than
GAP because the mechanization has not yet reached these rows — the
statements are believed true, and the first one's hard half is already
proved.

1. ✅ **RESOLVED (2026-08-06) BY ADDING THE PREMISE** — see the note at the
   end of this item.

   **`\tilab{App}`** — "Thus by ⑧ and ⑬, we have `\typc{\Theta_3}{N}{\inh{A}}`".
   The induction hypothesis checks the argument at `inh{A'}` and the rule
   wants it at `inh{A}`; the bridge is `Θ3 ⊢ A ≡ A'`.  That is a
   **transport of the typing judgement along type equivalence at TC**, which
   the paper states nowhere.  ⭐ The equivalence `Θ3 ⊢ A ≡ A'` itself is
   already available in the mech: it is `ad_refine_syn_inh_tyequiv`
   (`algo/prop_soundness_typing.v` §2) — a refinement between two ghost-free
   paintings IS a type equivalence — which was built for `Freeze` and turns
   out to be needed here too.

   ⭐ **It is a MISSING APPENDIX PREMISE, not a missing lemma.**  The
   appendix already adds an explicit `Θ ⊢ _ ≡ _` premise to exactly three
   syntax-directed rules (`sd-Freeze`, `sd-AbsAnnoCheck`, `sd-AbsAnno`) for
   precisely this reason — in an algorithmic context a flexible may stand
   for either type, so the two are equivalent, not equal — and then says
   "we only need to extend freezing and annotated lambda rules".  `sd-App`
   is the fourth rule that needs it: its argument premise reuses the
   function's domain by equality.

   **What the mech did (2026-08-06)**: added the premise.
   `ad_sd_typing__app` now carries
   `Θ ⊢ (btyp_to_ptyp B1) ≡ᵗ A2` beside `Θ ⊢ᵃᵈ[TC] N ⦂ inh{A2}`.  Four
   construction sites needed the accompanying `a_tyequiv` transport, each
   of which already existed.

   ⛔ **The alternative, and its cost.**  Keeping `sd-App` unchanged makes
   the step a TYPING-under-`≡ᵗ` transport at TC, which bottoms out in an
   `ad_pat_consis` **TARGET** transport along `≡ᵗ` — both directions at
   once (so `≡ᵗ`'s `sym` row closes), by a nested induction, the mirror of
   `skl_tyequiv_consis_transport`'s SUBJECT one — and, because `sd-App`'s
   own conclusion type is the function's CODOMAIN, a mode-indexed
   generalization over a new colour-preserving `btyp` equivalence.  Several
   hundred lines and a new relation, to recover a premise the appendix adds
   to three sibling rules already.  ⛔ There is no third way: `B1` is
   existentially chosen by the rule, but every way of re-choosing it needs
   the same transport in the function's DOMAIN instead.
2. **`\tilab{Abs}`** — "By ⑯ and definition of `\guessMono{P}`, we have
   `Θ1,ᾱ ⊢ inh{P} ⊳ inh{A}`".  A refinement property of `guess^TY` used as
   if definitional; the mech had no such lemma (algo/prop_basic.v carries only its
   freshness, `a_decls` and ftv facts).
   **✅ SUPPLIED AND PROVED (2026-08-06)**: `a_guess_mono_refine`
   (`algo/prop_soundness_typing.v` §9), Qed and axiom-free.  What the
   authors would have to write down: the statement carries a **Δ**, because
   the ∀ row must put its witness in the refinement's own tag context
   rather than in Θ — the same decoupling `a_consis_chk_annot_refine`
   needed below — and it is sound here for the reason it was unsound
   there, namely that `guess^TY`'s fills are the generated flexibles,
   which live in Θ and are therefore Δ-free as the `□` rule requires.
   Note also that a universal ghost `⫯.P` is DROPPED by `guess^TY`, so its
   row is refinement's `tophole_remove`, not `tophole_keep`.

## MISSING LEMMA — ✅ SUPPLIED BY THE MECH (2026-08-06) — `thm:sound-skeleton-inference`, AbsAnno: "preservation of refinement under type equivalence" is asserted inline and never stated

In the AbsAnno case of `thm:sound-skeleton-inference` the proof runs
`thm:sound-consistency` on the annotation check `\aconsis{\Theta_1}{A}{P}{\Theta_2}`,
gets the hidden output `A'` with

    inc{Θ1}{Θ2}     Θ2 ⊢ inh{P} ⊳ bid{A'}     Θ2 ⊢ A' ≡ A

and then says: **"Thus, by preservation of refinement under type equivalence,
we have `Θ2 ⊢ inh{P} ⊳ bid{A}`."**  There is no such lemma anywhere in the
paper, and it is not a one-liner: the refinement judgement's TARGET must be
re-coloured, and `≡` is colour-blind while refinement is not (`⊳`'s ∀ row
demands an INHERITED quantifier on both sides, its `□` row demands a
SYNTHESISED painting on the right).  The same step is used again, in the
`≡`-only direction, by `thm:sound-type-inference`'s Freeze case ("which
further gives `Θ2 ⊢ B ≡ A`").

**Status in the mech: SUPPLIED AND PROVED** (2026-08-06).
`a_consis_chk_annot_refine` (`frost/algo/prop_soundness_pat.v` §4) is Qed and
axiom-free, so `thm:sound-skeleton-inference` (`a_pat_sound`) is now *Closed
under the global context*.  What the proof needed, and what the authors would
have to write down:

- it is a **target transport** on the DECLARATIVE layer — going back through
  the algorithmic consistency re-does consistency soundness, because that
  judgement binds a ∀'s witness in Θ while refinement binds it in Δ;
- ⭐ the transport's statement must **decouple the consistency's context from
  the refinement's**.  With one shared context the ∀ row cannot be closed in
  either direction: moving the constructed output back (Θ → Δ) is unsound,
  since the `□` rule's fill is Δ-free *by rule* while the transport's fills
  are paintings of the sub-annotations, which do mention the witness;
- ⭐ the `□` row additionally needs an **occurrence lemma** — a free variable
  of a type-painting subject either survives into the consistency's target or
  escapes through a definition — which is what shows the annotation is
  Δ-free there;
- ⭐ the two flexible rows are sound only because **a definition is a
  monotype**, hence uniquely coloured.

**What the authors should do**: state the lemma, in whichever of the two
forms is primary — the refinement-target form or the `≡ᵗ` form — and prove
the other from it.  The `≡ᵗ` form is the one `thm:sound-type-inference`'s
Freeze case invokes ("which further gives `Θ2 ⊢ B ≡ A`").

## ⭐⭐ RETRACTION (2026-08-05) — the `SolE-FlexR` repair NEUTRALISES two of OUR OWN counterexamples, and the whole P6 cluster now goes through

**Not a paper gap — a correction to two findings we raised.**  Both
`cex/cex_p6_flex_counterpart.v` and `cex/cex_p6sv_forall_flex.v` refuted
`-var` completeness lemmas by the SAME step: the published `SolE-FlexR`
read `P ∼ α̂ ⤳ α̂`, DISCARDING the accumulated pattern, so the solve's answer
at a flexible counterpart was forced to be the flexible, and the enclosing
precision obligation then compared that flexible's κ-image with the ideal
guess.  The authors' repaired row returns `guess^TY(P)`; at both
configurations `P` is ghost-free, so `guess^TY` invents nothing and the
answer IS the pattern:

| configuration | old answer | repaired answer | old obligation | now |
|---|---|---|---|---|
| `P_i = c → ⟨⟩` vs `P_0 = β̂`, `κ β̂ = ⟨⟩→⟨⟩` | `β̂` | `c → ⟨⟩` | `(⟨⟩→⟨⟩) ⊑ᵖ (c→⟨⟩)` — no rule at the rigid `c` | reflexivity |
| `∀β.β→β ≼[TC] f̂` | `∀_.f̂` (vacuous binder) | `∀β.β→β` | `f̂` cannot mention the bound β | the shape the lemma asks for |

Machine-checked, Qed and axiom-free, in
`cex/probe_flexr_neutralises_p6.v`.

### ⚙ WHERE THE RETRACTED FILES WENT (2026-08-06)

Three files under `cex/` had been reduced to a retraction header with no Coq
content — the tree's standing rule is that a KNOWN-FALSE proof is not
committed, so each had lost its body while keeping its narrative.  They were
DELETED on 2026-08-06; **this section is now their home**, and every
`cex/…` citation of them elsewhere in the docs resolves here.  All three
proof texts are preserved in git at commit **`d5f9169`** — the last commit
under the published `SolE-FlexR` — and their headers, at `18cc7e4^`.

| deleted file | what it claimed | why it is retracted |
|---|---|---|
| `cex/cex_p6_flex_counterpart.v` | the `-var` completeness lemmas are false at a flexible solve counterpart (`cex_solve_forces_flex`: "the only solve derivation forces `P_a = β̂`") | that central lemma is now FALSE — the repaired row returns `guess^TY(P_i) = c → ⟨⟩`, and the obligation becomes reflexivity (row 1 of the table above).  Its OTHER half — that the configuration is unreachable because `LE-FlexR` freshens a flexible target facing a compound subject — survives untouched in `cex/cex_p6_flex_freshened.v` (still green), and the `a_flex_tvar` WIDENING it motivated (`algo/def_rules.v`, `SolE-FlexR`'s comment) still stands: that is about which counterparts the rule ACCEPTS, not what it RETURNS |
| `cex/cex_thm_complete_subtyping.v` | `thm_complete_subtyping_false` — Theorem 4.6 is false, by the double-occurrence instance `Θ0 = f̂`, `P0 = (∀γ.γ→γ) → f̂`, `P = ∀β.β→β` at `NM = TY`, `M = FN(TC)` | the authors accepted the refutation and replaced the row.  `guess^TY(β→β) = (·; β→β)`, so nothing is invented and nothing lost, the close re-binds a REAL occurrence, and A FULL RUN EXISTS.  Its direct negation is `cex/probe_flexr_repair.v` (`new_extract`, `new_run_exists`; Qed, axiom-free).  ⭐ Soundness of subtyping survived the repair unchanged (`a_sub_sound`) |
| `cex/probe_solve_flexr.v` | `run_exists_at_correct_instantiation` — localizing the failure to that one row by showing the continuation succeeds if handed the right instantiation | SUPERSEDED, not false: under the repair the algorithm *chooses* that instantiation itself, so the hypothetical is the TAIL of `new_run_exists` in `cex/probe_flexr_repair.v`, which additionally rests on nothing but `algo/def_rules.v` |

⚙ **A SECOND PAIR WENT THE SAME WAY (2026-08-17)**, and for the cleanest
possible reason: they are refutations OF a rule set, and the rule set was
repaired.  Both proof texts are preserved in git at commit **`eabf308`**.

| deleted file | what it proved | why it is retracted |
|---|---|---|
| `cex/probe_extract_supply_drift.v` | `e_extract_det_false` — `e_extract` is not deterministic up to a renaming, because at an α-FREE subject against a `∀` counterpart both `LS-Absent` (spends nothing) and `LS-ForallR` (draws an opener) fire and both emit the empty collection | the absence-first guard landed on `e_looksub`/`e_lookeq`'s five leaking rows, so the second derivation cannot be built.  ⭐ Its POSITIVE replacement is `e_looksub_lookeq_absent_pins` (`ext_algo/prop_look.v` §2c): at an α-free subject the collection returns `Ξ = ·`, `𝒞 = ·` AND the supply unchanged, hypothesis-free — which is precisely the conjunct this file refuted |
| `cex/probe_sub_supply_drift.v` | `e_sub_det_false` — the same drift REACHES SUBTYPING through `SI-ForallL`, so level 6's motive is false at its supply conjunct.  ⭐ It closed the one step of the §8c.13 diagnosis that had been argued by INSPECTION | same guard.  It was written as the GATE for the repair — the whole plan rested on the inspection step, so it was machine-checked first and the repair only then begun.  Having done its job it is retracted with the file it was checking |

⚙ **AND A THIRD WENT THE SAME WAY (2026-08-18)** — same reason again: it
refutes a rule set, and the rule set was repaired.

| deleted file | what it proved | why it is retracted |
|---|---|---|
| `cex/cex_looksub_not_det.v` | `cex_looksub_not_det` — the COLLECTION is not deterministic: at subject `∀_. α`, counterpart `∀_. 1`, mode `TC`, `LS-ForallL` first collects `[≼TC ∀_.1]` and `LS-ForallR` first collects `[≼TC 1]`, and both lists are CLOSED, so no renaming absorbs the difference | the ForallR-PRIORITY guard landed on `LS-ForallL` / `LS-UnivGhostL` and their `e_` twins (`forall_r_off`, frost/def_shapes.v), so the ForallL-first derivation cannot be built.  ⭐ Its POSITIVE replacements are `a_looksub_open_target` (under the guard, only Var / Absent / ForallR can root a collection at a ghost-free `∀` counterpart in check mode, so one peel is an INVERSION) and its solve-side mirror `a_solve_sub_open_target` |

⛔ **What this does NOT settle.**  The mech's `sub_shield` premise was
invented as the repair of the second of these, and P6-Sv / P6-Ss / P6-L
still carry it.  One dead witness does not license dropping it — that has
to be decided by re-proving without the premise.

✅ **What did land**: all five P6 lemmas are Qed and axiom-free under the
repaired rule (P6-Cv, P6-Cs, P6-Sv, P6-Ss, P6-L), and the whole tree
builds.  One genuinely new premise was needed across the cluster —
`ftvar_in_uskl ψa [<=] dom Θ`, the ideal guess's own well-formedness in the
ambient context — because the repaired `SolE-FlexR` reads the solve block's
payloads off that guess.  It is the paper's prose "all inputs are
well-formed" again and is registered in `docs/WF-SIDE-CONDITIONS.md`; it is
NOT derivable (when α does not occur in `κR` the subject never mentions ψa).

---

## SORT DISCIPLINE (2026-08-06) — the algorithmic rules distinguish TYPE positions from SKELETON positions by METAVARIABLE, and the mechanization now enforces it

**Status: PROSE-COMPLETION, with one metavariable SLIP and one position left
unmechanized (both argued below).**

The algorithmic judgements all range over ONE syntactic category — skeletons
— but their rules are *sorted by metavariable*: a rule written with `A` / `B`
is restricted to positions the grammar only ever fills with a TYPE, while a
rule written with `P` / `Q` admits a full skeleton.  `\silab{Check}`
(`full-algo-spec.tex:799-804`) is the clearest case:

    guarded{A,B}    aconsis[B]{Θ0}{A}{B}{Θ1}
    ------------------------------------------
        atypsub[TY][TC][B]{Θ0}{A}{B}{Θ1}

Nothing in the *rule* forces `A`, `B` to be ghost-free; the sort is carried
entirely by the choice of letter, and a Coq `Inductive` has no such notion.
The mechanization therefore states it: `pskl_ghost_free` (frost/def_shapes.v)
holds exactly of the ghost-free skeletons, i.e. of the painted `ptyp`s
(`pskl_ghost_free_to_ptyp`).

**Where the paper sorts a position, and what is mechanized:**

| rule | paper | mechanized |
|---|---|---|
| `SI-Check` | `guarded{A,B}` | subject **and** target |
| `SI-ForallR` | `A ⩽ ∀α.B` | target only — see (1) |
| `SolS-Check` | `guarded{P,B}` | target only (LHS is the accumulated pattern, a skeleton — the paper agrees) |
| `SolS-ForallR` | `solvesub{A}{TC}{∀β.B}` | target only — see (2) |
| `SolS-GhostL` | `guarded{B}` | yes |
| `LS-Check`, `LS-ForallR` | `A`, `B` | target only — see (3) |
| `U-*` (consistency), `assignvar`, `unifyvar` | `P`/`Q`/`τ` throughout | nothing to add |

**(1) The two figures DISAGREE on `SI-ForallR`'s subject.**  The plain rule
writes `A` (`full-algo-spec.tex:806-811`); the decorated mirror writes the
unresolved SKELETON `S` (`decorated-algosub.tex:64`) while still writing `T`
— an unresolved TYPE — at `SI-Check`.  Only the target is common to both, so
only the target is mechanized.  The subject's sort is pinned anyway by the
`SI-Check` leaf the row eventually reaches.  **Authors: please reconcile.**

**(2) `SolS-ForallR`'s LHS `A` is a SLIP.**  Its own premise is dischargeable
by `SolS-GhostL`, whose LHS is the ghost `◇` (`:1283-1288`).  Sorting the LHS
would leave `◇ ≼TC ∀β.B` with NO rule, and that configuration is reachable:
subject `∀α.α` against a ∀-target makes `LS-Var` emit `sub_TC(∀β.B)` while
the accumulated pattern is still `◇`.  Read `P`, not `A`.

**(3) `LS-Check` / `LS-ForallR`'s subject `A` is TRUE but not free.**  These
rows are reachable at the TY sort ALONE — they need a guarded target, and
`skmod{SK}` pins the collection's target to `◇` at every mode — so the
subject IS a type whenever they fire.  But the collection's STRUCTURAL
lemmas are mode-agnostic by design, and two of them substitute an arbitrary
skeleton into the subject: `a_looksub_lookeq_subst_stable` and
`a_looksub_lookeq_subst_gen_size`.  The latter's consumer,
`a_subtag_decoration`'s ForallL row, feeds it the node's guess `P₁`, and at
the SK sort `P₁` is the raw solve output — ghosts and all.  Mechanizing the
subject sort here would mean threading `skmod` through the whole structural
kit; the payoff is nil, since the target premise already makes the rows
non-overlapping.  Recorded rather than done.

**Cost to the metatheory: none.**  The TARGET premises are read straight off
`skmod{TY}` (`a_ty_mode_compat_tc_ghost_free`), which every completeness
lemma already carries; `SI-Check`'s SUBJECT premise is derived in P7 from the
motive's TY-sort ghost-freeness of the unresolved subject, transported across
`≡ᵘ` (`a_uskl_tyequiv_ghost_free` — the relation maps a ghost only to the SAME
ghost, and its one non-structural row to a monotype painting), reflected
through the metasubstitution (`msubst_pskl_ghost_free_inv` — images are
monotypes) and then through the erasure (`uskl_ghost_free_to_pskl`).  Both
directions of subtyping stay closed and unconditional.

## PROSE-COMPLETION — `⊑`'s flex-def rule lacks the θ-image side-condition
- Where: fig:information-increase (full-algo-spec.tex:30-35); mech
  `a_inc__flex_def` (algo/def_meta.v).
- The figure's rule for `Θ,α̂:=τ ⊑[θ,τ'/α̂] Θ'` constrains `τ'` only by
  `Θ' ⊢ τ' ≡ θτ`, but the prose (algorithmic.tex:123-126) says θ maps
  flexible variables to *well-formed monotypes in Θ'*.  Without the wf
  side-condition, identity increases may drop defined variables from the
  target, and stability of variable lookups fails.  Mechanized with the
  prose side-condition (`a_wf_ptyp Θ' τ'`, `mono_ptyp τ'`) on the rule.

## PROSE-COMPLETION — identity metasubstitutions preserve entries
- Where: algorithmic.tex:135 ("For an identity metasubstitution, all
  entries of flexible variables in Θ are preserved in Θ'"); mech `a_isub`
  (algo/def_meta.v).
- The figure alone does not pin the target's flexible entries even for ι.
  The identity shorthand `⊴` therefore carries the prose characterization
  as a second component: definitions, once made, are preserved verbatim.
  This is what makes the FlexL/FlexR lookup rules stable under `⊴`
  (algo/prop_stability.v) — without it, a definition could be swapped for
  an ≡-equivalent one and the lookup-shaped rules would not transport.

## MECH-BUG (FIXED 2026-07-14) — `Flex-Flex-Assign` must recurse into CONSISTENCY, not into `unifyvar`
- Where: full-algo-spec.tex:1707 (`Flex-Flex-Assign`), :1754 (`Assign-Assign`),
  :393 / algorithmic.tex:330 (skeleton splitting); mech `a_unify__flex_assign`
  (algo/def_rules.v:487).
- NOTATION — **the paper says this outright**, full-algo-spec.tex:1440-1442:

      "We write  Θ₀ ⊢ P ∼ P₀ ⊣ Θ₁  for  Θ₀ ⊢[P₀] P ∼ Q ⊣ Θ₁
       WHEN THE OUTPUT Q IS NOT USED."

  So the two-slot form `Θ₀ ⊢ A ∼ B ⊣ Θ₁` IS the CONSISTENCY judgment with the
  output dropped: **SUBJECT `A`, INPUT `B`, output existentially quantified**.
  (Consistency "takes two skeletons P and P₀ as input, checks their consistency,
  and calculates their JOIN Q as output" — :1436-1438.  That is why it is a
  4-place relation.)  The macros agree: `\unify{A}{B}` renders `A ∼ B`
  (macro.tex:1234) and `\aconsis`'s relation is `\consis` = `\mathrel{\sim}`
  (macro.tex:1271) — the same symbol.
  It is NOT a separate unification judgment, and it is NOT missing.
  Consistent with the Flex rule, whose premise `unifyvar{α̂}{β̂}` sits under the
  conclusion `aconsis[β̂]{Θ₀}{α̂}{α̂}{Θ₁}` — subject α̂, input β̂.
  And `Δ₁∣Δ₂` are omitted on that premise, which per :1472-1473 means BOTH EMPTY.
- Under that reading all three sites make sense, and only that reading does:
  - Flex-Flex-Assign, when γ̂ IS a subject: substituting turns the subject into
    the monotype τ, and consistency's **FlexR** then assigns `β̂ ≔ τ`.
  - Assign-Assign: subject α̂ against a general SKELETON `P` — only consistency
    takes a skeleton argument at all; **FlexL** assigns `α̂ ≔ P`.
  - Skeleton splitting: subject α̂ against the ARROW `β̂ → γ̂` — **FlexL** again.
    This one cannot be `unifyvar` under any reading.
- THE BUG: mech `a_unify__flex_assign` recurses into `a_unify` (the var-only
  `unifyvar`) where the paper recurses into CONSISTENCY.  So the mechanized
  algorithm gets STUCK the moment a definition is a non-variable monotype —
  machine-checked at the time (`a_unify_stuck_on_arrow_definition`, Qed,
  axiom-free): with `Θ₀ = (α̂ ≔ unit → unit), β̂` it could not unify α̂ with β̂,
  though a solution plainly exists.  That instance is now the SUCCESS
  regression test `frost/algo/test_unify_regression.v`
  (`a_unify_succeeds_on_arrow_definition`).  A definition CAN be an arrow — that is what `Assign-SolveM`
  produces via `guess^TY`.
- NB `a_unify_var_inv` ("every derivable `a_unify` has VARIABLE subjects",
  prop_consis_sound.v) reads like a theorem but is a SYMPTOM of this bug.
- FIX (IMPLEMENTED, algo/def_rules.v).  The premise became, with the output
  existential and both Δs empty (per the shorthand above):

      a_unify__flex_assign : forall Θ0 Θ1 γ τ A B Q,
        a_consis empty empty Θ0
          (ptyp_to_pskl (subst_ptyp_in_ptyp τ γ B))   (* INPUT   = B[τ/γ] *)
          (ptyp_to_pskl (subst_ptyp_in_ptyp τ γ A))   (* SUBJECT = A[τ/γ] *)
          Q Θ1 ->
        ((γ ~ abind_flex_mono_def τ) ++ Θ0) ⊲ A ≈ᵘ B
          ⊣ ((γ ~ abind_flex_mono_def τ) ++ Θ1)

  (until 2026-08-03 this also carried a used-name set `F`, threaded through
  the whole cycle — see the PROSE-COMPLETION entry below, now superseded).
  So `a_unify`
  and `a_consis` are MUTUALLY inductive — a 2-WAY mutual, not the paper's
  3-way: the mech reads `Assign-Assign` as CONTINUING the assignment (see the
  note at `a_assign` in algo/def_rules.v), so `a_assign` stays BELOW the
  cycle and its lemmas enter the mutual soundness proof as black boxes.
  `a_unify`'s subjects became ATOMS (the paper's hatted `unifyvar{α̂}{β̂}`).
  Also fixed: `a_split__flex` (full-algo-spec.tex:393), whose premise input
  is an ARROW and so could never have been `unifyvar` — forcing it through
  `a_unify` is what made `a_unify` take general monotypes in the first place.
- CONSEQUENCES, all landed (algo/prop_consis_sound.v, prop_mono_bridge.v):
  - `a_unify_consis_sound`: ONE mutual induction (Combined Scheme, 6+14
    cases) proving parts 1+2 of thm:sound-consistency together, exactly how
    the paper organises its own proof (consistency-proofs.tex:1562).  The
    invariant-preservation conjuncts are generalized over the protected Δ
    (Flex-Flex-Assign's consistency premise runs at `Δ₁ = Δ₂ = ∅`).
  - Part 2's conclusion is now a type EQUIVALENCE `Θ₁ ⊢ α̂ ≡ᵗ β̂`.  The
    Flex-Flex-Assign case recovers it from consistency's join + the input's
    refinement via the monotype BRIDGE (`consis_refine_mono_tyequiv`), and
    part 1's Flex case converts it back to declarative consistency via the
    CONVERSE bridge (`tyequiv_mono_consis`) — both in prop_mono_bridge.v.
  - `a_consistag_sound_aux` (decorated, Appendix B) stays a PLAIN induction
    above the bundle: `a_consistag` is not in the recursion cycle (its flex
    rules take `a_unify`/`a_assign` derivations as opaque premises).
  - DELETED as artifacts of the bug: `a_unify_var_inv` (vacuous — subjects
    are atoms), `a_unify_dom` (now FALSE: unification can GROW the context
    via consistency → Assign-SolveM; part-2 soundness only claims an
    information increase), `a_unify_sym` (consistency is subject/input
    asymmetric; symmetry now comes from `a_tyequiv__sym`).
- STATUS: fixed; `make coq` green, zero admits, all flagships axiom-free
  (README.v).  Completeness is unblocked.

## MECH-BUG (FIXED 2026-07-14) — `Assign-Assign` must recurse into CONSISTENCY too (the OTHER back-edge)

Exactly the same bug as the `Flex-Flex-Assign` entry above, on the other
auxiliary judgment, and missed the first time round.  The paper's two-slot
`∼` is the OUTPUT-SUPPRESSED CONSISTENCY abbreviation
(full-algo-spec.tex:1440-1442), so `Assign-Assign`'s premise
`unify(α̂[τ/β̂])(P[τ/β̂])` over `Θ₀,Ξ` is CONSISTENCY, not a continued
assignment.  The paper expands it exactly so and appeals to "the IH of
consistency" (consistency-proofs.tex:1720-1724).  That is why its soundness
proof is a **3-way** mutual induction, "together with the two auxiliary
judgements of variable unification and assignment" (:1562) — the mech had
`a_assign` outside the cycle entirely.

The reference implementation confirms it: BOTH `U-Flex-Flex-Assign`
(type.ml:316-321) and `U-Assign-Assign` (type.ml:358-363) call `join_sk` —
the consistency/join function — not `join_var`/`assign`.

`a_assign` is now the first motive of the `a_assign`/`a_unify`/`a_consis`
mutual block, and soundness is the 28-case `a_assign_unify_consis_sound`.
Four further encoding bugs fell out of the fix:

* **`β̂ = α̂` IS REACHABLE — do NOT premise `α̂ ≠ β̂`, and substitute BOTH
  slots.**  It is tempting to argue that an assignment's subject must be an
  UNDEFINED flex var, so `α̂ ≠ β̂` by uniqueness, so the subject stays the bare
  variable `α̂`.  That is FALSE.  *Nothing* requires the subject to be
  undefined: neither `a_consis__flex_l` nor the implementation's `U-FlexL`
  (`| p0, MFlex alpha -> assign alpha p0 [] theta`, type.ml:182-185) guards on
  it.  So a DEFINED `α̂` can be the subject, the walk then reaches `α̂`'s OWN
  definition, and the rule must fire with `β̂ = α̂` — whereupon the subject
  `α̂[τ/α̂]` is the MONOTYPE `τ`, not a variable.  With `α̂ ≠ β̂` premised, NO
  rule fires and assignvar is STUCK, exactly as the old `unifyvar` reading was
  stuck on an arrow-valued definition.  The implementation computes precisely
  this (`subst_var (MFlex alpha) tau beta` with `beta = alpha` reduces to
  `tau`).  Machine-checked both ways:
  `a_assign_succeeds_on_own_definition`, algo/test_unify_regression.v.

* **PROSE-COMPLETION: `Assign-Assign` needs a HATTED-SUBJECT premise.**  Before
  the fix, "the subject of an assignment is flexible" was *derivable* — every
  rule either matched `α ~ abind_flex_mono` or inherited it from the `a_assign`
  IH.  With an opaque consistency premise that argument dies, and worse:
  `a_consis__rigid` accepts a var subject for a RIGID `α`, so the rule would
  admit a degenerate "assign a rigid type variable" derivation.  The paper
  excludes this only through the hatted-metavariable convention (`α̂`).  Added
  `a_flex_tvar ((β ~ abind_flex_mono_def τ) ++ Θ0) α` — the same
  prose-completion `Flex-Flex-Assign` already carried, for the same stated
  reason.  It **must** be on the CONCLUSION's context: on `Ξ ++ Θ0` it is FALSE
  in exactly the `β̂ = α̂` case above.

* **`Assign-Depend` REVERSED Ξ.**  The paper's premise suffix is `β̂,Ξ`
  (consistency-proofs.tex:1763) and the implementation does
  `assign alpha p (xi @ [hd]) theta` — both put `β̂` at the `Θ₀`-adjacent end.
  The mech consed at the head.  Inert on its own (every `Ξ` entry is an
  undefined flex var, so their relative order carries no information) but fatal
  for the fix above, whose premise context is literally `Ξ ++ Θ0`.  Now
  tail-appends.

* **`Flex-Flex-Id` was stricter than the paper.**  Paper premise is
  `α̂ ∈ dom(Θ₀)` (implementation: `is_in_dom_`, type.ml:302) — flexible,
  DEFINED or not.  The mech demanded `binds α abind_flex_mono`.  No derivation
  was lost (a defined `α̂` routes through `Flex-Flex-Assign`, whose premise
  degenerates to the consistency `τ ≈ τ`), but the rule was not the paper's.
  Now `a_flex_tvar Θ0 α`.

Gotcha worth recording: `nonflex(P)` is **head-level** — "P is not ITSELF a
flexible variable", NOT "P contains no flexible variables".  The
implementation encodes it as match-arm ORDER.  Read it the other way and
`FlexL` looks inapplicable to `γ̂ → unit`, and the whole "the premise is
consistency" reading looks broken.

## IMPLEMENTATION DISCREPANCY (report to WT) — `U-Flex-Flex-Assign` has its `join_sk` slots SWAPPED

Found while auditing the mech against `paper/artifact/implementation/lib/type.ml`.
**No mech change — we follow the paper.  This is a note about the artifact.**

`join_sk p0 p` takes the INPUT `P₀` first and the SUBJECT `P` second.  This is
pinned three ways: the arm `| Ghost, p -> rule "U-GhostR"` versus
`| p, Ghost -> rule "U-Ghost"` (and `GhostR` is the rule whose *input* is `□`);
the arm `| MFlex alpha, p -> rule "U-FlexR"; assign alpha p [] theta` (and
`FlexR` is the rule whose *input* is `α̂` and which assigns `α̂ := P`, the
subject — the code assigns the second argument); and the `\aconsis` macro
itself (macro.tex:1002 renders `#3 ⊢ #4 ∼ #5 ⊣ #6`, and the abbreviation at
full-algo-spec.tex:1440-1442 writes `\aconsis{Θ₀}{P}{P₀}{Θ₁}`, so LEFT of `∼`
is the subject).

`U-Assign-Assign` respects this — `join_sk (subst_var p tau beta)
(subst_var (MFlex alpha) tau beta)` puts the flex var in the subject slot,
matching the paper.  But `U-Flex-Flex-Assign` (type.ml:319-320) does

```ocaml
join_sk (subst_var (MFlex alpha) tau gamma) (subst_var (MFlex beta) tau gamma) theta
```

i.e. INPUT `α̂[τ/γ̂]`, SUBJECT `β̂[τ/γ̂]` — whereas the paper's
`\unify{α̂[τ/γ̂]}{β̂[τ/γ̂]}` means subject `α̂`, input `β̂`.  **The implementation
is internally inconsistent about its own convention**, which is the strongest
evidence that this is a slip in one of the two sites, and the paper says which.

BENIGN, but for a subtler reason than "both sides are monotypes".  Algorithmic
consistency is **mirror-symmetric** under the swap `(P₀ ↔ P, Δ₁ ↔ Δ₂)`: all 14
rules pair up (`Ghost`↔`GhostR`, `ForallSyn`↔`UnivGhost1`,
`UnivGhost2`↔`UnivGhostR`, `FlexL`↔`FlexR` — which even produce the *same*
output `α̂`; `Unit`/`Rigid`/`Arrow`/`ForallInh`/`UnivGhost`/`Flex` self-mirror),
and the side conditions swap `Δ₁`/`Δ₂` in exactly the right direction.  The one
residue is that `Flex` outputs the *subject's* variable, so `Q` can change.  At
`Flex-Flex-Assign`, however, `Δ₁ = Δ₂ = ∅` and the output `Q` is DISCARDED — so
both caveats vanish precisely there.

Status: **argued, not proved.**  See the DEFERRED entry below.

## DEFERRED — `a_consis_sym` (would turn the above from argued-benign into proved-benign)

The 1011-line archived attempt (`algo/prop_symmetry.v.deferred`) was DELETED
2026-08-09 — recoverable from git history, but there is no reason to want it.
It never compiled (it HANGS: 90s+ of CPU at 98% without terminating, reason 1
below), its approach is the wrong one (reason 2 below), and 28 of its 65
definitions have since been re-proved — correctly, and in the build — by the
swap kit `algo/prop_swap.v`.  Everything it recorded is in this section.

Intended statement:

```coq
Theorem a_consis_sym : forall F Δ1 Δ2 Θ0 P0 P Q Θ1,
  Θ0 ⊢ᵃ[ F ][ Δ1 | Δ2 | P0 ] P ≈ Q ⊣ Θ1 ->
  exists Q', Θ0 ⊢ᵃ[ F ][ Δ2 | Δ1 | P ] P0 ≈ Q' ⊣ Θ1.
```
(mutually with `a_unify_sym`; `a_assign` needs no symmetry and no IH, since
`FlexL` and `FlexR` carry the *same* assign premise and re-use it as a black
box.  `Θ₁` is expected to be preserved; only `Q` may differ, and only at `Flex`.)

TWO REASONS IT STALLED, both worth knowing before anyone retries:

1. **The hang.**  `swap_ptyp_subst` contains
   `repeat match goal with |- context [ if ?t then _ else _ ] => destruct t end`.
   `destruct t` does NOT eliminate that `if`: `subst_ptyp_in_ptyp`'s scrutinee
   elaborates to `@eq_dec ptypvar EqDec_eq_of_X ...`, which a plain `destruct`
   does not abstract, so the `if` survives, the `match` fires again, and
   `repeat` loops forever.  The working form is
   `destruct (@eq_dec ptypvar EqDec_eq_of_X x y)`.  (Same gotcha bites
   `subst_pskl_in_pskl`; recorded in algo/prop_basic.v.)  The file also has ~10
   UNSCOPED `fsetdec` calls, which are minutes-slow in this codebase.

2. **The design, which is the real obstacle.**  The output must be
   EXISTENTIALLY quantified, and that collides with cofinite quantification: in
   `ForallInh` the IH yields some `Q'_α` for each fresh `α ∉ L`, but the
   conclusion needs a SINGLE `Q'` with `open Q' α` for every `α`.  You cannot
   just pick one.  The archived attempt reached for a 960-line atom-swapping /
   equivariance library to get around this.  **That is not how this codebase
   solves it.**  The precedent is `d_consis_compose` (see
   [[frost-compose-tags-witness]]): it dissolved exactly this
   "different witness per fresh variable" blocker by making the output an
   EXPLICIT WITNESS FUNCTION of the inputs — invariant under opening a variable
   — instead of an existential.  Retry that way; it should be a fraction of the
   size and need no equivariance machinery at all.

Priority: LOW.  It changes nothing in our mechanization — our rules already
follow the paper.  It only upgrades our verdict on someone else's code.

## MECH-BUG (fixed) — metasubstitution was a SEQUENTIAL fold, but the paper says "finite map"
- Where: algorithmic.tex:123 — "A metasubstitution `Θ ⊑[θ] Θ'` is a finite **MAP**
  θ from flexible variables in Θ to well-formed monotypes in Θ'."  A finite map is
  a SIMULTANEOUS substitution.  Mech `msubst_ptyp` / `_pskl` / `_btyp` / `_bskl`
  (algo/def_meta.v) instead encoded a SEQUENTIAL fold:
  `msubst ((α,τ)::θ) A = msubst θ (A[τ/α])`.
- These are DIFFERENT functions: the fold lets a LATER entry rewrite inside an
  EARLIER entry's image.  Take the (perfectly legal) `θ = [α ↦ β̂, β̂ ↦ unit]` — the
  fold sends `α ↦ unit`, the map sends `α ↦ β̂`.
- Why it never bit: the two coincide on IDENTITY metasubstitutions (each `α ↦ α`
  substitution is a no-op), and *"our algorithms always give identity
  metasubstitutions"* (algorithmic.tex:140).  Every existing use goes through
  `msubst_ptyp_id` / `msubst_pskl_id`, so nothing depended on the difference.
- Why it matters NOW: completeness/optimality is stated up to `θ ≡ ζ ∘ θ₁`, so it
  needs GENERAL metasubstitutions and their COMPOSITION.  Composition is pointwise
  (`(ζ∘θ)(α) = ζ(θ(α))`), and its action law `msubst (ζ∘θ) A = msubst ζ (msubst θ A)`
  is simply FALSE for the fold — the fold's later-entry interference breaks it.
- Fix (IMPLEMENTED): all four `msubst_*` now recurse on the TYPE and look each free
  variable up in θ (`msubst_lookup`), i.e. they are finite maps, as the paper says.
  Only the two `_id` lemmas needed re-proving; `make coq` green, zero admits.

## GAP — `lemma:precision-preserves-refinement` is stated with NO PROOF, and is FALSE without the external wf condition
- Where: full-algo-spec.tex:716-721.  The lemma is asserted bare — `\begin{lemma}
  … \end{lemma}` followed straight by the next `\begin{definition}`.  There is no
  `\begin{proof}`, here or anywhere else in the appendices.
- It is the key lemma under completeness/optimality of consistency AND of type
  inference, so it carries a lot of weight for something never proved.
- Writing the proof is what exposed the entry below: **the lemma is false unless
  the refinement judgment's external well-formedness condition
  (declarative.tex:1427) is carried**.  Precision is DEFINED as
  `Θ ⊢ inh{P} ⊳ inh{Q}`, so the lemma is an instance of transitivity of
  refinement — and refinement is not transitive on the bare rules
  (`algo/cex/cex_refine_not_transitive.v`).  An unwritten proof hid that.
- MECHANIZED (algo/prop_precise.v, Qed + axiom-free): `ad_refine_syn_trans`
  (general transitivity, given the result is well-formed) and
  `ad_precise_preserves_refine` (the paper's lemma, a direct corollary).
- Proof shape, for the authors: OUTER induction on the second derivation, INNER
  induction on the first to peel the left-hand administrative rules
  (`tophole_remove` / `flex_l`, which shrink the left skeleton while the right
  stands still).  Every case whose left side is a ghost needs the crux: *assuming
  the result is well-formed*, whatever a syn painting refines to is a syn painting
  of a skeleton well-formed at the EMPTY Δ — which is what re-applying the Ghost
  rule requires.
- RELATED, also unproved but TRUE (algorithmic.tex:537): "Since `inh{Q}` is
  inherited, the refinement relation cannot fill Q with more quantifiers, but can
  only fill with monotypes and remove universal ghosts."  This holds because
  `tophole_fill`'s right-hand side is `syn{∀…}` — a SYNTHESISED quantifier — so
  the rule cannot fire against an INHERITED painting.  It is the exact dual of the
  fact our proof turns on (a SYN painting on the LEFT can never fire the `all`
  rule, hence Δ never grows).  The paper could cite it to shorten its own proof;
  our `ad_refine_syn_trans` is strictly stronger (general transitivity) and so has
  to handle `tophole_fill` rather than rule it out.

## RESOLVED (was FALSE) — refinement does not preserve wf; wf is carried by the STATEMENTS
- Where: fig. of refinement, `declarative.tex:1505-1510` (the GhostForall
  rule); the consequence hits `lemma:precision-preserves-refinement`
  (full-algo-spec.tex:716) and hence the whole completeness/optimality
  development, which rests on it.
- Machine-checked artifact: `cex/cex_refine_not_transitive.v` —
  `ad_refine_syn_not_transitive` is Qed and axiom-free.
- The GhostForall rule binds `α` in `Γ` but deliberately KEEPS `Δ`
  (the paper's own inline comment: "It's fine to keep Δ since we already
  required well-formedness separately").  But `Δ` is exactly what the Ghost
  rule tests (`Δ ∩ ftv(syn{Q}) = ∅`).  So a ghost nested UNDER a GhostForall
  may be filled with the very `α` that GhostForall binds — `α` is in `Γ`,
  not in `Δ`, so the side condition does not forbid it.  Witness:

      □ ⊳ syn(∀◇(□→□))              (Ghost; the fill is well-formed)
      ∀◇(□→□) ⊳ ∀α. ∀◇(α→α)         (GhostForall, then two Ghost fills at α)
      but NOT  □ ⊳ ∀α. ∀◇(α→α)

  The last step fails because the Ghost rule may only produce a WELL-FORMED
  skeleton, and `∀α. ∀◇(α→α)` is not one: skeleton well-formedness binds a
  quantifier's variable in `Δ`, while a `∀◇`-ghost's body must be well-formed
  at the EMPTY `Δ`.  Hence transitivity — and precision-preserves-refinement
  — fail.
- The MECH rule is FAITHFUL here (`ad_refine_syn__tophole_fill` puts `α` in
  the context and leaves `Δ` alone), so this is a paper-level problem, not an
  encoding slip.  (Unrelated minor discrepancy: mech's `ad_refine_syn__all`
  adds the variable only to `Δ`, where the paper adds it to both `Δ` and `Γ`.)
- LIKELY FIX (needs the authors): make GhostForall extend `Δ` as well as `Γ`
  (`Δ,α ⨟ Γ,α`), exactly as the ∀-rule does.  The Ghost rule's side condition
  then forbids the capture and the second step above becomes underivable.
  This is the same "inherited variables must not fill ghosts" discipline that
  the soundness proof had to carry explicitly as the fill-hygiene set `F`
  (`ad_refine_syn_f`) — evidence the constraint genuinely belongs in the rule.
- RESOLUTION (user-directed, and what the paper's comment actually says): do NOT
  add the premise to the rule.  The declarative rules stay verbatim; instead the
  METATHEORY carries well-formedness — a "solution" is a derivation *whose types
  are well-formed*, so the capturing derivation above is simply not a solution
  (its output is well-formed in NO context, `Pres_not_wf`).  Threading wf into
  the rules was tried and rejected: it does not survive `ad_refine_*_f_strip`
  (a ∀◇-ghost body may mention a context rigid α that the strip removes, and
  α ∈ Δ does not rescue it because ∀◇-ghost bodies are checked at the EMPTY Δ).
- MECHANIZED (algo/prop_precise.v, all Qed + axiom-free): `ad_refine_syn_syn_l`
  (a syn-headed refinement lands in a syn painting — shape only, no wf),
  `ad_wf_pskl_delta_shrink`, `ad_wf_pskl_empty_delta_free`,
  `ad_refine_syn_syn_delta_free` (a syn-headed refinement never fires the `all`
  rule, so Δ never grows and Δ-freeness propagates), and the crux
  `ad_refine_syn_syn_l_wf`: ASSUMING the result is well-formed, it is a syn
  painting of a skeleton well-formed at the EMPTY Δ — exactly what re-applying
  the Ghost rule needs.
- NEXT: the main induction for lemma:precision-preserves-refinement, then the
  metasubstitution-composition algebra, then completeness.

## MECH-BUG (fixed) — decorated FlexR had an over-general subject
- Where: fig:decorated-alg-consistency (decorated-algosub.tex:237-238); mech
  `a_consistag__flex_r` (algo/def_decorated.v).  Found while closing the
  FlexR case of lemma:sound-decorated-consistency.
- The paper says the flexible-variable rules "are inherited unchanged" from
  fig:alg-consistency, whose FlexR subject is a PLAIN skeleton `P`
  (`a_consis__flex_r`, algo/def_rules.v:630).  Read into the decorated
  system, its subject is therefore the embedding `pskl_to_uskl P` — a
  decorated skeleton with no tags and no dotted ghosts, exactly as
  `a_consis_decorate` produces.  The MECH rule instead took an ARBITRARY
  unresolved skeleton `S` with the premises stated on the erasure
  (`a_non_flex Θ0 ⌊S⌋ˢ`, `Θ0 ⊲[·] α ≔ ⌊S⌋ˢ ⊣ Θ1`) — strictly more
  derivations than the paper's rule.
- The over-general rule makes the soundness lemma FALSE.  Counter-example:
  take `S = ●` (a DOTTED hole, `uskl_holeg`).  Then `⌊S⌋ˢ = □`, which is
  non-flex and assignable (`guess^TY(□)` is a fresh monovar), so the mech
  FlexR fires and yields `Θ0 ⊢ᵗ[…|α̂|·] ● ≈ α̂ ⊣ Θ1`.  Soundness would then
  demand `· ⨟ Θ1 ⊨ ● ≈ α̂`; but the only consistency rule with a dotted hole
  on the left (`GhostG`) forces the right-hand side to be `□` itself, while
  `α̂` is defined to a monotype — unprovable.  The paper's rule never
  produces this, because `●` is not in the image of `pskl_to_uskl`.
- Fix (IMPLEMENTED): `a_consistag__flex_r` now quantifies a plain skeleton
  `P`, keeps the ordinary premises on `P`, and states the subject as
  `pskl_to_uskl P` — mirroring `a_consistag__flex_l` (whose subject
  `uskl_var_f α` is likewise the embedding of the ordinary `pskl_var_f α`).
  `pskl_to_uskl` moved from prop_decorate.v into def_decorated.v so the rule
  can mention it.  The FlexR soundness case then mirrors the ordinary one
  verbatim, and `a_consis_decorate`'s FlexR case gets simpler.

## RESOLVED (was WATCH) — Assign-SolveM and polymorphic definitions
- Where: fig:alg-consistency `Assign-SolveM` (full-algo-spec.tex:1744).
- Earlier concern: `guess^TY` keeps universal quantifiers, so the rule
  seemed able to define `α̂ := ∀…` against the entry grammar `α̂ := τ`.
- Resolution (user-pointed): the rule binds the result to the SORTED
  monotype metavariable `τ` — under the paper's metavariable convention the
  premise `guess^TY(P) = (β̄; τ)` only matches when the result IS a
  monotype (hence Solve-M).  On a polytype result no assignvar rule
  applies and the algorithm fails, which is correct: a monomorphic `α̂` has
  no polytype solution.  The MECH rule was the unfaithful one (missing the
  mono constraint); fixed by adding `mono_ptyp τ` to `a_assign__solve_m`.
  Consequently every stored definition is a monotype and `Θ ⊢ ctx` is
  preservable across the algorithm.

## PROSE-COMPLETION — unifyvar's hatted subjects + guess^TY freshness carry the no-Δ-dependence invariant
- Where: fig:alg-consistency `Flex-Flex-L`/`Flex-Flex-R`
  (full-algo-spec.tex:1683-…); mech `a_unify__flex_l/_flex_r`
  (algo/def_rules.v).  Found while assembling thm:sound-consistency
  part 1 (consistency-proofs.tex, "Soundness of Consistency").
- The augmented solution in the part-1 proof requires that "no flexible
  variables in Θ depend on variables in Δ1 and Δ2", and the proof needs
  this invariant PRESERVED by every unifyvar/assignvar step.  For
  assignvar, `Assign-SkipRigid`'s occurs condition (`β ∉ ftv(P)`) does
  the work.  For unifyvar, preservation rests entirely on the paper's
  METAVARIABLE CONVENTION: the subjects `α̂, β̂` are hatted, i.e.
  flexible variables — `Flex-Flex-Skip'` has no occurs condition, so
  without the convention a rigid variable (skipped earlier, e.g. an
  opened Δ-binder) could flow to a leaf and be captured as a definition
  `β̂ := X` bound ABOVE `β̂` — ill-scoped, and breaking the invariant.
  The mech rules were the unfaithful ones (payload side unconstrained).
- Mech completion (IMPLEMENTED; mirrors the Assign-SolveM sorted-τ
  resolution): `a_flex_tvar` premises on the payload side of
  `a_unify__flex_l/_flex_r`.  For guess^TY's `β̄` freshness (the paper's
  "fresh" is GLOBAL, but the solve node only sees its local tail —
  and the created names escape into the output context, so they cannot
  be cofinitely quantified the way continuation-passing formulations
  do, cf. worklist `a_wl_red__sub_arrow2`): `a_assign` now carries a
  USED-NAME set `F` accumulated by the entry-walking rules, and
  `Assign-SolveM` requires `uniq β̄` and `dom β̄` fresh from
  `F ∪ {α̂} ∪ dom(Ξ,Θ0)` — which at the solve node covers exactly the
  original context.  The paper-shaped judgments are the `F = ∅` notations.
- EXTENDED to the mutual cycle (2026-07-14): with `Flex-Flex-Assign`
  recursing into consistency, a solve node can fire deep inside a
  consistency premise, BELOW entries that `a_unify`'s skip rules walked
  past — and below the Δ-binders walked past by `Flex-Flex-Skip'`.  Those
  names can only reach the solve node through `F`, so `a_unify` and
  `a_consis` now carry the used-name set too (their skip/assign rules
  accumulate the walked head; all other rules pass `F` through).  Without
  it, `a_guess_mono__hole` may pick a walked head's name and re-attaching
  that head breaks context well-formedness — i.e. wf-preservation (and Δ-
  invariant preservation) would be FALSE for the mutual definitions.
  The invariant-preservation lemmas are now PROVED as conjuncts of the
  mutual soundness bundle `a_assign_unify_consis_sound`
  (algo/prop_consis_sound.v): new names avoid `F`; no-flex-dep +
  flex-above-free + domain bookkeeping are preserved for every protected
  Δ with `Δ ⊆ F ∪ dom Θ₀`, using Assign-SkipRigid's occurs condition and
  the positional fact that Δ-binders sit above all flexible entries.
- ⭐ SUPERSEDED (2026-08-02, executed 2026-08-03).  `F` was a MECH-ONLY
  device: the paper has no such index, it writes the walked entry back as
  `Θ₁,β̂` and relies on the Barendregt convention.  **`F` is now DELETED from
  all three judgments.**  The mechanization states the convention directly —
  each of the eight re-attaching rules of the walk carries `β ∉ dom Θ₁`, of
  the entry it puts back — which is the same discipline `a_sub_flex` already
  used (DESIGN §4.3).
  **Nothing here is a gap in the paper**: the premise is not a strengthening.
  `prop_swap.v` §13b proves (Qed, axiom-free) that a rule of this shape fires
  whenever a premise-free version would, with only the run's GENERATED names
  transposed — a derivation is finitely supported, so a fresh `γ` exists and
  equivariance moves the run to it while fixing every input.  So the two
  entries above should be read as: the paper's "fresh β̄" needs SOME formal
  completion, and the mechanization's is the paper's own convention rather
  than an extra index.  The freshness obligation the index used to discharge
  now sits where it costs nothing — as an avoid-set parameter `N` on the
  three COMPLETENESS motives, completeness being the direction that chooses
  the guessed names.  Soundness' matching coverage hypothesis is likewise
  OUTPUT-relative (`Δ ∩ dom Θ₁ ⊆ dom Θ₀`), replacing the old
  `Δ ⊆ F ∪ dom Θ₀`.

## FALSE — `thm:complete-consistency` optimality (parts 2/3): flex migration below term binders defeats the factoring

**Status: FALSE against the paper's rules; MECH HAS ADOPTED THE FIX
(2026-07-15, same day).  The counterexample is machine-checked, axiom-free
(`algo/cex/cex_assign_optimal_syn_middle.v`, now stated against a local copy
`a_inc_syn` of the original rules).  The mechanized `a_inc`/`a_inc_equiv`
(def_meta.v) now use GMM-style SEMANTIC ENTRIES — binder middles up to
`≡ᵗ`/`≡ˢ` (new skeleton equivalence `a_pskl_tyequiv`) — and the same instance
then factors (`cex_zeta_semantic`).  THE PAPER MUST ADOPT THE RULE BELOW
(draft note: sections/appendices/optimality-cex.tex, commented-out \input
after the lemma).**

The OPTIMALITY half of `thm:complete-consistency` part 3 (assignment) is
false as stated; part 2 (unification) inherits the falsity through
`Flex-Flex-Skip'` for contexts with term binders.

Two paper ingredients conspire:

1. **Flex migration.**  `Assign-Depend` moves a payload flexible `X̂` into the
   pending suffix `Ξ`; `Assign-SkipTmVar` threads `Ξ` below walked term
   binders; `Assign-SolveM` deposits it at the subject's position.  The
   migration is FORCED by well-formedness: the deposited definition
   `α̂ ≔ guessᵀᵞ(P)` mentions `X̂`, so `X̂` must end up below it.

2. **Syntactic middles + positional wf in information increase**
   (algorithmic.tex:91-121).  The var rule `Θ,x:P ⊑[θ] Θ',x:θP,Ξ` pins the
   target's binder payload to the SYNTACTIC `θP`, and the flex rule demands
   each image be well-formed in the POSITIONAL remainder of the target.

Instance (5 atoms; `assignvar α̂ ≔ X̂→()`):

    Θ₀ = c : X̂→(), X̂, y : (), α̂
    algorithm:  Θ₁ = c : X̂→(), y : (), α̂ ≔ X̂→(), X̂     (X̂ migrated below y)
    competing:  θ = [δ̂/X̂, ()→()/α̂]  into  Θ = c : δ̂→(), δ̂ ≔ (), y : ()

The competing solution is valid (increment ✓, `a_wf_aenv Θ` ✓, join
`θP ≈ θα̂` ✓ — `δ̂` unfolds to `()`), and `δ̂` is in scope at `X̂`'s ORIGINAL
position (above `y`).  Any factoring `ζ : Θ₁ ⊑ Θ` must reproduce `c`'s payload
`δ̂→()`, forcing `ζX̂ = δ̂` syntactically — but `X̂`'s entry in `Θ₁` is consumed
against the target remainder BELOW `y` (here: empty), where `δ̂` is not
well-formed.  No `ζ` exists.  (Note: GMM, from whom the information-increase
device is borrowed, compare context-entry payloads up to EQUIVALENCE, not
syntax; their minimality theorem does not face this.)

**Provenance (2026-07-15, verified against both sources):** the syntactic rule is
faithful to **Gundry's thesis** (Gundry13, Fig. 2.4: term middles `x : θσ`,
recursion on the stripped remainder, term variables separate localities) — NOT
to the MSFP paper's base relation, whose `≼` is per-entry SEMANTIC
(GundryMM10 §3.1, `Δ ⊩ δ⟦vD⟧`).  The thesis also moves metavariables past term
entries (`inst-depend`/`inst-skip-tm`, Fig. 2.5), so the analogous instance is
constructible in plain HM (`Θ0 = …, γ̂, y:σy, α̂, x:α̂`; solve `γ̂ ≡ α̂→1`), and the
thesis's own generality proof (Lemma 2.6, App. D.1) covers only "some of the
more interesting cases" — the term-walk cases are dispatched by "θ can be
rearranged", a definition-swap that is only valid against the SEMANTIC relation
(it is MSFP Lemma 10's "ψ ≡ θ" step).  So the gap predates this paper; the
repair below applies to the thesis's formulation as well.

**Candidate fix (authors' call, not applied):** make information increase's
binder middles ≡ᵗ-tolerant, GMM-style:

    Θ ⊑[θ] Θ'    Θ' ⊢ P' ≡ θP
    --------------------------------
    Θ,x:P ⊑[θ] Θ',x:P',Ξ

Then `ζ` may use a depth-legal representative of `δ̂`'s ≡ᵗ-class (here `()`)
and the counterexample dissolves; the soundness development only ever uses the
middle up to ≡ᵗ, so it survives.  Affected mech cases (marked FALSE in
`algo/prop_consis_complete.v`): Assign-SkipTmVar (typ/skl) and
Flex-Flex-Skip' (var_typ/var_skl branches).  All other optimality cases are
unaffected (their walks carry no type payload, or none that can migrate).

**UPDATE (2026-07-16): Assign-SkipTmVar(typ) is now CLOSED under the adopted
semantic rule** (`skip_tm_var_case`, Qed, axiom-free, `algo/prop_consis_complete.v`;
optimality bundle admits 13→12).  The factoring is the GMM Lemma 2.6 construction
in full: `a_inc_self_downarrow` + `a_inc_downarrow_prefix` land the competing
increment at `ρ_sub = ⇓ρ = compose(aenv_msubst Θ) ρ` over the sub-target `Θ'`
(below the walked binder); `consis_downarrow_subject` (the join is invariant under
⇓-normalizing the subject when the RHS is monotype) plus the O2 grounding
`join_pskl_downarrow_mono_scoped` transfer the competing join to `Θ'`; the sub-IH
runs; and `a_inc_equiv_mid_insert_var` + `a_inc_equiv_self_downarrow` +
`a_inc_equiv_trans` rebuild the factoring over the original `ρ`.  SkipTmVar(skl)
and SkipRigid are the pskl/tvar mirrors (pending).

**NEW (minor) unstated-invariant gap — `dom Ξ ⊆ ftv P`.**  The optimality induction
needs, at every node, that the pending declarations `Ξ` all occur in the assigned
skeleton `P` (`dom Ξ ⊆ ftvar_in_pskl P`).  It is used to ground each pending decl's
competing image into the sub-target `Θ'` (O2 only reaches decls appearing in `P`);
a decl `Y ∉ ftv P` is unconstrained by the join and its ⇓-image can escape `Θ'`,
i.e. the SAME flex-migration phenomenon (a genuine counterexample, not just a proof
obstacle).  This is NOT a free invariant of the `a_assign` judgment — `Assign-SolveM`
takes `Ξ` as an input.  But it IS an invariant of every REACHABLE derivation: the
top-level `assignvar` starts with `Ξ = nil`; `Ξ` grows only via `Assign-Depend`,
whose premise is literally `β̂ ∈ ftv P` (def_extra.v); the skip/solve rules keep
`Ξ` and `P`.  So a config with a dangling `Y ∈ Ξ, Y ∉ ftv P` is unreachable from
the top.  The mechanization threads `dom Ξ ⊆ ftv P` through `assign_optimal_post`
and `a_assign_optimal_thm`, maintaining it across the closed rules
(UnivGhost-Id/Depend/Skip) and instantiating it vacuously at the corollary's
`Ξ = nil` — so the TOP-LEVEL optimality statement is unchanged and unweakened.  The
paper's assignment optimality, if stated over general `Θ₀ ∣ Ξ` (it is —
consistency-proofs.tex:2420) and inducted without this invariant, has the same
unstated-invariant gap; it should carry `dom Ξ ⊆ ftv P` (or be stated at the
top-level `Ξ = ·`, where it is vacuous).

## GAP — `thm:complete-consistency`: the three induction subjects DO NOT COMBINE

Full analysis, with per-edge verification and the measure that works:
[DESIGN-completeness-measure.md](DESIGN-completeness-measure.md).

The lemma is proved "by mutual induction for the three parts", but each part
declares a DIFFERENT induction subject: §1 (consistency) on the DECLARATIVE
consistency derivation; §2 (unification) on the CONTEXT `Θ₀`; §3 (assignment)
on the PAIR `Θ₀ ∣ Ξ` (consistency-proofs.tex:2257, :2277, :2420).  A
mechanization needs ONE well-founded order, and BOTH obvious candidates are
dead — with witnesses:

* **No context measure can be outermost.**  `Arrow`'s SECOND premise runs at the
  OUTPUT context `Θ₁` of the first, and `Assign-SolveM` can have extended it with
  fresh flexible variables AND made a definition.  Witness: `Θ₀ = (α̂)`, input
  `(◇→unit)→unit`, subject `α̂→unit` ⇒ `Θ₁ = (α̂ ≔ β̂→unit), (β̂)`.  Any weight goes
  up.  (`ForallInh`/`ForallSyn`/`UnivGhost1` break `|Θ₀|` more cheaply, `+1` rigid.)

* **No declarative-derivation measure can be outermost either** — and it does not
  merely fail to shrink, it can GROW.  At `Assign-Assign` the derivation handed to
  the consistency IH is the paper's REFLEXIVITY derivation on `θ(α̂[τ/β̂])`
  (:2510-2515).  Witness: `Θ₀ = (β̂≔unit),(α̂)`, `P = ◇→unit`,
  `θα̂ = (unit→unit)→unit` — caller's derivation is 3 nodes, callee's is 5.  The
  mechanism is `Ghost`: it absorbs an arbitrarily large `Q` in ONE node, so the
  assignment node's derivation is bounded by the GHOST-RIDDEN `P` while the
  spawned consistency node's is bounded by the FULLY-SOLVED `θα̂`.

  **Corollary: §1's "induction on the declarative consistency derivation" is not
  a well-founded induction as written** — `UnivGhostR` (:2570-2572) recurses with
  the LITERALLY IDENTICAL derivation.

The two failures land on DISJOINT edge sets, so no lexicographic combination of
them in either order works.

RESOLUTION (not a paper error, just an unstated measure).  Induct on
`V` = the size of the skeletons **as the SOLUTION sees them** — pushed through the
solution's `θ`, then through the target `Θ`'s own definitions.  `V` strictly
decreases on all 11 consistency-internal edges and is EXACTLY CONSTANT on all 4
cross-edges and both back-edges, which is what lets `|Θ₀|` carry the second
lexicographic component.  The back-edges `X ↦ X[τ/γ̂]` only unfold a definition
THE SOLUTION HAD ALREADY UNFOLDED, so `V` cannot see them; the consistency rules
decompose, so `V` cannot miss those; and the context growth is simply not measured.

PREREQUISITE: `≡ᵗ` is NOT size-preserving (`a_tyequiv__flex_def` gives `α ≡ᵗ τ` for
ANY `τ`), and `≡ᵗ` is exactly what `a_inc_equiv` uses.  So `V` is not even a
well-defined natural number until the skeletons are put in a total-unfolding normal
form.

## GAP — `thm:complete-consistency` §1: the flexible cases are ONE SENTENCE, hiding two obligations

consistency-proofs.tex:2568-2569 — "The cases where `P` or `P₀` is a flexible
variable are handled by the other two parts of the lemma" — is the ENTIRE treatment
of `Flex`, `FlexL`, `FlexR`.  Two things are missing:

* **Constructing the callee's solution.**  A consistency solution gives
  `Θ ⊢ syn θS ≈ bid Q` AND `Δ₁ ⊢ inh θP₀ ⊳ Q`.  The unification/assignment problem
  needs `Θ ⊢ θα̂ ≈ θβ̂` / `Θ ⊢ θP₀ ≈ θα̂` — a DIFFERENT judgment, between the TWO
  INPUTS, with `Q` eliminated.  That needs the BRIDGE (consistency-into-`Q` plus
  refinement-of-`Q` ⟹ a relation between the two inputs) — the same bridge
  soundness already required.  The paper never invokes it here.
* **Recovering PRECISION.**  §1's conclusion demands `Δ₁,Δ₂ ⊢ θ₁P₁ ⊑ Q`, and for
  these three rules the algorithmic output is `P₁ = α̂`.  The §2/§3 IHs produce NO
  precision statement at all (:2266-2270, :2412-2416).  So `Θ ⊢ θ₁α̂ ⊑ Q` must be
  proved separately — it is NOT "handled by the other two parts".

## GAP — `thm:complete-consistency` §3 never proves the assignment walk is not STUCK

§3's skip cases are dismissed as "Our goal follows from IH and context weakening"
(:2557-2558).  But `Assign-Skip`/`Assign-SkipRigid` carry `β̂ ∉ ftv(P)`, and there
is NO RULE AT ALL for a RIGID head `β ∈ ftv(P)`.  Completeness must therefore PROVE
the walk never reaches such a head — the escape/scope check, the classic hard step
in DK-style completeness.  It is true and provable (`a_inc` peels the rigid `β`
before it reaches `α̂`, so `θα̂` is well-formed BELOW `β`; whereas `β ∈ ftv(P)` forces
`β ∈ ftv(θP)` since `θ` cannot erase a rigid variable, and consistency against the
MONOTYPE `θα̂` then forces `β ∈ ftv(θα̂)` — contradiction).  The paper does not do it.

*Status (2026-07-17, 47bcc36):* the stuck-check is MACHINE-CHECKED in
`algo/prop_consis_complete.v` (`assign_complete_step`, rigid-head case,
`γ ∈ ftv(P)` sub-path).  Ingredient (i) is `a_inc_strip_decls_prefix` +
`a_inc_tvar_inv` (the competing increment peels `γ`, so `θα̂` is wf in the
truncated target); ingredient (ii) is the new scoped join ftv-survival
`ad_pat_consis_rigid_ftv_rev_scoped` (the definition side condition holds only
for definitions reachable from the truncated target's scope — the blanket
version is false, definitions above `γ` may mention it).

Likewise `Assign-SolveM` (:2430-2461) silently assumes BOTH of its premises: the
occurs check `α̂ ∉ ftv(P)`, and that `guess^TY(P)` succeeds AND returns a MONOTYPE
(`a_guess_mono` has no `all` case; `a_assign__solve_m` additionally premises
`mono_ptyp τ`).  Both follow from the solution; neither is proved.

## GAP — the SOLUTION notions: the active 2-condition definitions admit binder-capturing fills

*(2026-07-18, found while mapping the subtyping proofs; DESIGN-subtyping.md §3.1.)*

The completeness proof for consistency AUGMENTS the definition of a solution
to THREE conditions — join, `P0`-fill at Δ₁, and the subject-side refinement
`skctx[Δ2]{Θ} θ⌊S⌋ ⋈ Q` (consistency-proofs.tex:2230-2242) — and the
standalone 2-condition Definition of consistency solutions is commented out
in algorithmic.tex.  The third condition is NOT derivable from the other
two: on `(P0 = ∀X.X, P = ∀X.◇, Q = ∀X.X)` the join and the fill hold (the
capturing `X` sits at a concrete position of `P0`, so the fill premise never
inspects it; the join's hole rule checks the fill's well-formedness over the
binder-EXTENDED context), the subject refinement fails, and the algorithm is
stuck (its Ghost rule carries `Δ2 ∩ ftv(fill) = ∅`, and the ∀-step puts the
binder in both Δs — by design, so that soundness outputs refine both
inputs).  So completeness against the 2-condition notion is false; the
mechanization states it against the paper's own augmented (3-condition)
notion.

The subtyping-solution Definition (algorithmic.tex:1423-1437) is ACTIVE and
2-condition, and the same capture transplants: at `TI`,
`(P0 = ◇, P = ∀X.◇, Q = syn ∀X.X)` passes the `typsub`-Infer premise and the
`P0`-fill, yet the optimality conclusion demands `θ(∀X.◇) ⊑ ∀X.X`, which the
precision rules forbid (the hole rule's `Δ ∩ ftv ψ = ∅`).  The subtyping
proofs' appeals to thm:complete-consistency ("(θ;Q) is a solution to the
consistency problem") silently assume the augmented notion.  SUGGESTED FIX:
add the subject-side refinement `Θ ⊢ θ⌊S⌋ ⋈ Q` to the definitions of
solutions (both consistency and subtyping); soundness already establishes it
for every algorithmic output, so the theorems still characterize the
algorithm exactly.  The mechanization proceeds with the augmented notion;
no machine-checked counterexample was made (the mech never diverges from the
paper's PROOF-level statements here — unlike the optimality-cex case).

## Resolved definition-sync findings (step 1 of the restart)
See [REPORT-remech-decl-sync.md](REPORT-remech-decl-sync.md) — notably the
`is_tskl` untagged-∀ fix (A1), whose downstream effect invalidated the
pre-restart `pskl_to_tskl` decorated witnesses (prop_safety machinery).


## Soundness ForallR: the strengthening step is TRUE but needs the substitution generalization (2026-07-18)

`subtyping-proofs.tex` (lemma:sound-decorated-subtyping, ForallR case,
~:1293-1314) discards the trailing suffix Ξ with "Since Ξ is fresh for S and
B, by context strengthening for unused variables in Ξ".  The strengthening
STATEMENT is true — but it is not provable by direct induction on the
derivation: a ForallL instantiation witness may mention a Ξ-variable the
conclusion (S, B) does not expose, so the conclusion-only freshness motive
does not propagate to the premises.  The decl layer hit the same for
`d_sub` (decl/prop_syntax_directed.v NOTE — its "is FALSE" refers to the
induction motive, not the theorem).

Mech route (decl-style): the inductive generalization is SUBSTITUTION —
substitute the stripped variables away, rewriting
witnesses too — unit for an undefined flex entry, its own definition
painting for a defined one, iterating head-first over Ξ (defs scope to
tails, so the head entry is never mentioned elsewhere).  Foundations in
algo/prop_pat_sub.v §4 (`guarded_pskl_subst`, `a_wf_pskl_subst_ctx`,
`uskl_to_pskl_subst_unit`); the `ad_pat_consis`/`ad_pat_sub` strip
inductions and the suffix driver are the remaining pieces (the decl cribs
are `d_pat_consis_subst_unit` / `d_pat_sub_subst_unit`,
decl/prop_skeleton.v:268/313).

Paper note: the step is correct; a footnote that the strengthening lemma is
proved via witness-rewriting substitution (not direct induction) would make
the appendix self-contained.


## Decorated ForallL: the ∃-decoration is a cofinite tag FAMILY (prose-completion, 2026-07-19)

`subtyping-proofs.tex`'s decorated ForallL (and lemma:subtyping-decoration's
use of it) picks ONE decoration ψ of the guessed instantiation P1 ("let ψ be
a decorated skeleton with ⌊ψ⌋ = P1 ...") and treats its choice as
WLOG-irrelevant.  The mech's `a_subtag__forall_l_{tagged,untagged}`
(algo/def_decorated.v) instead quantifies the premise over EVERY sorted
decoration whose tag names avoid the rule's cofinite set L:

    forall Ψg ψg, inter Ψg L [=] empty -> a_tags_sort NM Ψg ψg ->
      ⌊ψg⌋ˢ = P1 -> subderivation @ (Ψ ∪ Ψg)

— the tag analog of cofinite binder quantification.  Consumers pick a
witness via `pskl_decorate_exists` / `a_tags_sort_decorate_exists`
(algo/prop_pat_sub.v §7).  This is an ENCODING device, not a semantic
strengthening: with a decoration-renaming lemma the single-witness rule is
equivalent (renaming lets any consumer move to fresh tag names); the family
form just avoids proving that renaming.  Paper needs no change beyond
reading "let ψ be" as "for any fresh ψ".

## PROSE-COMPLETION — `lemma:precision-substitution`'s `fresh Ψ'` must mean GLOBAL tag freshness (2026-07-24)

`lemma:precision-substitution` (subtyping-proofs.tex:1664) carries the
side condition `fresh{Ψ'}` on the instantiation's tags.  The weakest
faithful reading of ForallL's own freshness — the instantiation's tags
are disjoint from the current *tag context* — makes the lemma **false**:
the tag context splits at Arrow (`Ψ = Ψ₁, Ψ₂`), so a tag `ε` of `ψa` can
leave the context on one branch while `ψa`-copies still carry it
syntactically on the other; a ForallL deeper in that branch may then
legally reuse `ε` in its own instantiation `ψ''`, and one can build a
derivation in which `ε` is consumed at a `ψa`-node while the `ψ''`-node
faces an `all_syn` target (which records nothing).  After substituting
`Pa` for `ψa`, the `ψ''`-ForallL still re-introduces `ε`, no remaining
node can consume it, and every leaf forces the tag context to `∅` — the
transported judgment is underivable.

So `fresh{Ψ'}` must be read as Barendregt-style *global* freshness: fresh
from the context AND from every tag in the subject (in particular from
the tags of previously substituted instantiations).  The mechanization
renders this as a tag-HYGIENIC mirror of the fuel-indexed judgment
(`ad_pat_sub_g`, def_decl_algo_sub_hyg.v: ForallL additionally requires
`inter Ψ' (ftag_in_uskl subject) = ∅`), over which precision-substitution
is proved (`ad_pat_sub_precise_upre`, prop_sub_complete.v, Qed); an
arbitrary derivation is converted once, at the completeness theorem's
entry point, by a tag-renaming freshening lemma.  Nothing is wrong with
the paper's statement under the intended reading — but the proof depends
on the global reading in an essential, non-obvious way, and a reader
formalizing the local reading gets a false lemma.

## GAP (proof-step) — `lemma:precision-substitution`'s "straightforward induction" does not go through as stated; the motive must be generalized (2026-07-24)

The paper proves `lemma:precision-substitution` by "a straightforward
induction on the subtyping derivation …, observing that … replacing
ψa with Pa would not result in any type mismatch"
(subtyping-proofs.tex:1668-1673).  Two steps of that induction are not
straightforward and required genuine repairs (both machine-checked,
prop_consis_precise.v / prop_sub_complete.v, all Qed axiom-free):

1. **The substitution motive is too weak for its own ForallL case.**
   When the subject is (an occurrence of) `ψa` itself and the last rule
   is ForallL on `ψa`'s own quantifier, the premise's subject is
   `ψa-body[ψ''/α']` and the reconstruction needs
   `Pa-body[ψ''/α']` — the changing part is the *whole* skeleton
   surrounding `ψ''`, not the positions of the substituted variable, so
   the `S[ψa/α] → S[Pa/α]` induction hypothesis does not apply (and
   re-instantiating with the stripped `⌊ψ''⌋` is not a legal ForallL
   instantiation, since decorated skeletons have no untagged
   quantifier).  REPAIR: generalize the motive from single-variable
   substitution to a *decorated subject-precision relation* ⊑ᵤ
   (`uskl_precise`) — congruences + refinement-mirroring ghostier-side
   rules + reflexivity — which is closed under instantiation
   (`uskl_precise_subst`) and embeds plain precision against a decorated
   target (`uskl_precise_of_precise`).  The subst-form is the special
   case `S[Pa/α] ⊑ᵤ S[ψa/α]`.

2. **Fuel/height preservation needs a rule-granularity accounting.**
   The main completeness induction applies its IH to the substituted
   premise, so precision-substitution must not increase the derivation
   height — but the more-precise subject may carry `∀◇`-wrappers or
   fold flexible definitions that the original derivation lacks, forcing
   extra UnivGhostL / FlexMono steps.  REPAIR: in the measure-carrying
   mirror, leaves take any fuel and UnivGhostL/UnivGhostLG/FlexMono are
   non-incrementing (only Arrow/ForallR/ForallL increment); the main
   theorem's measure is then lex(fuel, derivation structure), which its
   non-incrementing cases support because they recurse structurally.

Also elided by "no type mismatch": the transported subject's tag
context must drop *exactly* by the substituted instantiation's consumed
tags — the mechanization threads the invariant "tag context ⊆ the
subject's syntactic tags" (`ad_pat_consis_ftag_sub`,
`ad_pat_sub_g_ftag_sub`) to pin the residual context, and threads the
solution target's well-formedness (external-wf reading) for the
ghost-introduction cases.

## RESOLVED (isolated statement FALSE, but NOT a completeness problem) — the -var completeness lemmas: a flexible counterpart `P0` refutes the ISOLATED statement (machine-checked, 2026-07-24; resolved 2026-07-25)

> **Resolution (2026-07-25):** the isolated `-var` statement is false as
> written, but the refuting configuration is UNREACHABLE, so it is not a
> completeness problem and needs no P0-side premise.  See the "### Resolution"
> subsection at the end of this entry.  The earlier "Suggested repair"
> (a P0-side positional condition) is SUPERSEDED and was reverted from the
> mechanization.

`lemma:complete-consistency-constraint-collection-solving-var`
(consistency-proofs.tex:1181) and its subtyping twin
`lemma:complete-constraint-collection-solving-var`
(subtyping-proofs.tex:1696) are FALSE as stated.  Machine-checked
counterexample: `cex/cex_p6_flex_counterpart.v` (Qed, axiom-free,
refuting the conclusion for EVERY `P_a`, EVERY `θ_a` with
`inc[θ≡θ_a]{Θ0}{Θ}`, and every Δ/tag-set in the conclusion's precision).
⚠️⚠️ **RETRACTED 2026-08-05 and the file DELETED 2026-08-06** — the authors'
repaired `SolE-FlexR` neutralises it; see "WHERE THE RETRACTED FILES WENT" at
the top of this file, and `cex/probe_flexr_neutralises_p6.v` for the machine
check.  The text below describes the PRE-repair state.

The configuration: `Θ0 = X, α̂`; `Θ = X`; `θ = [α̂ ↦ unit→unit]`;
`ψ_a = X → unit`; `ρ = [X ↦ unit]` (so `ρ(ψ_a) = unit → unit`);
`P_i = X → unit`; `P_0 = α̂`; `Q = unit → unit`.  Every premise holds —
including the positional side condition ("P_i has the same rigid
variable in the same position") and the freshness facts it stands for.
The only applicable solve rule is FlexR, forcing `P_a = α̂`; the
conclusion `precise[Ψi,Ψa]{θ_a P_a}{ψ_a}` then demands
`(unit→unit) ⊑ (X → unit)` (θ ≡ θ_a pins `θ_a α̂` up to ≡, which is
syntactic at the definition-free Θ), whose argument obligation
`unit ⊑ X` has no derivation — X is rigid.

Root cause: every case analysis in the five completeness lemmas of the
cluster recovers `P_0`'s shape by inversion on the refinement premise
`Θ ⊢ inh{θP_0} ⊳ Q`, silently assuming the subject exposes a matching
constructor (or ∀◇/□).  But the inversion also admits `P_0` = flexible
variable, whose θ-IMAGE supplies the constructor.  The algorithm's own
rule for flexible counterparts — LE-FlexR (fig:poly-info-extraction),
which replaces the payload by a fresh `γ̂ ∈ Ξ_c` — is never invoked in
either completeness appendix.  At the non-var lemmas the fresh-`γ̂`
mechanism can repair the flexible subcase (θ_a extends to Ξ_c and may
map `γ̂` to a ψ_a-refining monotype when ψ_a is mono-paintable; when it
is not, the premises are vacuous — but BOTH facts need proof).  At the
-var lemmas there is no Ξ_c and θ_a is pinned on all of Θ0, so the
flexible subcase is not repairable in place: the statement itself needs
a premise excluding it (e.g. `P_0` is not a flexible variable, with the
flexible case handled at the caller via LE-FlexR before descending), or
a rephrased conclusion.  Blocked pending the authors' intended reading.

A related mech-side infidelity was found and FIXED in the same pass
(independent of this refutation, which uses an UNDEFINED flexible):
`a_solve_eq__flex_r` was encoded for undefined flexibles only
(`binds α abind_flex_mono Θ`), while the paper's context-free FlexR
(full-algo-spec.tex:1374) fires on any hatted variable.  A DEFINED
flexible nested inside a structural counterpart (e.g. `P0 = unit → β̂`,
`β̂ := unit`) made the mech solve stuck where the paper succeeds — a
second, mech-side falsifier of the completeness statements that would
have survived any repair of the paper-level gap.  The rule now takes
`a_flex_tvar Θ α` (hattedness); the soundness stack is unaffected
(restriction → relaxation; the decorated twin SEq-FlexR was already
context-free).

### Addendum (2026-07-25): the `nonflex{P0}` repair is INSUFFICIENT — refuted at depth

Trying the proposed repair in the mechanization before adopting it
falsified it: `cex_p6_var_nonflex_insufficient` (same cex file, Qed,
axiom-free) reruns the refutation with `ψa = 1 → (X→1)`, `Pi = 1 → (X→1)`,
`P0 = 1 → β̂` — the counterpart is an arrow, so `nonflex{P0}` HOLDS, but
the -var lemma's Arrow case recurses on P0's PIECES and the right piece is
the old flexible β̂ opposite the ρ-leaf position: solving is forced through
SE-Arrow then SE-FlexR to `Pa = 1 → β̂`, and the conclusion precision fails
one constructor down.  A head-shape premise cannot survive the structural
recursion.

Two further facts locate the real repair:
* At the TOP of the call chain (ρ = identity, the P = α crux), the bad
  configuration is UNSATISFIABLE: the subject there is ψa itself, and the
  consistency/subtyping premise at the leaf position (rigid X vs the
  flexible's unit-image) has no derivation.  The falsity is an artifact of
  the ρ-GENERALIZATION being too coarse: it forgets that in premise sets
  arising from actual runs, a flexible counterpart piece cannot sit at or
  above a ρ-substituted position.
* The implementation's `solve_eq` (type.ml) confirms the context-free
  FlexR reading (any flexible target wins, keeping the flexible), so the
  solve side cannot be tightened; the invariant must exclude the
  configuration.

### Resolution (2026-07-25): the configuration is UNREACHABLE — no P0-side premise needed

The "Suggested repair" above (a P0-side positional condition) is SUPERSEDED.
It patched an isolated statement that does not need patching, and its ForallL
maintenance turned out not to be derivable from the local solve (SolE-Check
bridges the subtyping solve into SolE-FlexR). The whole `pskl_dominates_rho`
experiment was REVERTED from the mechanization.

Three facts settle it (all machine-checked; new file
`algo/cex/cex_p6_flex_freshened.v`, Qed axiom-free):

1. **Only the Arrow case can even have a flexible `P0`.** θ maps flexibles to
   MONOTYPES (unit / mono-or-rigid var / arrow). Refinement `inh{θP0} ⊳ Q`
   into a ∀ or ∀◇ requires a ∀/∀◇/defined-flex source (inversion on
   `ad_refine_syn` into `bskl_all_inh`), which a monotype never is. So
   ForallInh/ForallSyn/ghost provably have non-flex `P0`; leaves are handled
   directly (SolE-Flex / the SolE-Var ρ-var special case).
2. **No flex-SPLIT rule exists in constraint solving, and none is needed.**
   SolE-Arrow needs both sides arrows; SolE-FlexR solves the flexible
   counterpart directly to `β̂`. `split[α̂][β̂→γ̂]` lives only in the
   inference/`⤳ᵐ` layer.
3. **The cex's θ is FORCED BY ρ; the configuration is not producible.** ρ
   substitutes the rigid `c` away, so `ρ(ψa)=unit→unit ∼ Q` and
   `inh{θβ̂} ⊳ Q` (same Q) pin `θβ̂ = unit→unit` — c is stripped from
   everything θ sees, while ψa (used only for the final precision) keeps it.
   A run never emits a raw Θ0-flex payload at a compound subject: LE-FlexR
   FRESHENS a flexible counterpart there to a fresh `γ ∈ Ξ`
   (`a_lookeq_arrow_subject_flex_target_freshened`; and
   `a_lookeq_flex_target_raw_subject_not_arrow`: a raw flex payload's subject
   is never an arrow). The fresh `γ` is the NON-var lemma's job (θ extends
   over Ξ and can assign `γ` the rigid `c`, so precision holds).

**P6-Cv/Sv plan:** ∀/∀◇/ghost cases prove non-flex `P0` from the
monotype→refinement fact (no premise); leaf cases as the paper does; the
Arrow case handles a flexible `P0` via SolE-FlexR like the leaf case, relying
on the freshening so a raw Θ0-flex opposite a ρ-rigid-var cannot occur.

## GAP (REPAIRED 2026-07-27 — proof-step gap; statement TRUE) — `complete-consistency-cc-solving-var` ForallInh/ForallSyn Subcases `Pi=□` and `Pi=∀◇.Pi'`: the Δ-bookkeeping of the IH output is broken

> **Resolution.** Repair candidate (1) below was implemented, as the
> generalized theorem `a_solve_eq_complete_var_gen`
> (algo/prop_look_complete_var.v): the refinement premise is carried at
> `(Θr, Δr)` with `Δr [=] dom Θtv` (the ForallInh descent binders), which
> keeps □-fills wf away from those binders; the precision conclusion is
> strengthened to a fresh-extension family `∀S` so the ∀-rows can fold
> their bodies.  The split is a binds-level BAG (`aenv_split`) — an
> earlier LIST-equation form (`Θ = Θtv ++ Θr`) forced the ForallSyn
> binder into Θtv and with it a mech-only `pskl_no_hole P0` premise; the
> bag form (2026-07-27) removed that premise, so the statement is
> premise-faithful to the paper (see WF-SIDE-CONDITIONS.md, historical
> entry).  The one genuinely-implicit paper step made explicit is the
> aenv-tvar precision rename `ad_partial_precise_rename_tvar` (the
> paper's silent "removing β as necessary").  `a_solve_eq_complete_var`
> is Qed, axiom-free.

- Where: consistency-proofs.tex, Lemma
  `lemma:complete-consistency-constraint-collection-solving-var`
  (:1181), cases ForallInh/ForallSyn, Subcases `P_i = □` and
  `P_i = ∀◇.P_i'`; mech `a_solve_eq_complete_var` (dev scratch
  `algo/cex/p6cv_dev_tmp.v`, cases forall_inh_tagged /
  forall_syn_tagged).  Status 2026-07-25: the mech is at 13/15 cases
  (all others Qed-threaded); these two rows are the only blockers.
- The paper's subcases invoke the IH at the ∀-body and conclude with the
  ∀-precision rule, whose body obligation lives at `Δ,β | Θ,β`.  But the
  IH's PRECISION PREMISE for `P_i = □` can only be built by the □-rule,
  whose side condition `Δ ∩ ftv(ψ') = ∅` FAILS at `Δ,β` whenever the
  target body `ψ'` uses its binder — so the IH can only be invoked at
  `Δ`, and its output precision is at `Δ`, not the `Δ,β` the ∀-rule
  needs.  The □-rule's side condition is not Δ-monotone, so the step
  "goal follows from GhostL" silently uses an inadmissible Δ-weakening.
  The `∀◇` subcase (precision inverted through the fill rule, concluded
  by SolE-GhostForall) has the same mismatch: its body precision sits at
  `Δ | Θ,β` and must be moved to `Δ,β | Θ`.
- The STATEMENT survives: the configurations that would break the
  weakening are premise-unreachable.  A refinement □-fill is wf in
  `Θ` at empty Δ (the refinement's own □-rule), hence β-free; the
  consistency and ρ transfer that β-freeness to the □-opposite TARGET
  subtrees.  Concretely, with `ψ' = β→1` and `P_0' = □→1` the □-fill's
  synthesised-paint would have to be `β` itself, whose wf premise fails —
  so a □ of `P_0` never sits opposite a β-containing subtree.  But no
  premise of the lemma EXPOSES this fact, so the proof step needs a
  repair, not just a rewording.
- Repair candidates (DESIGN-completeness-subtyping.md §6(l); decision
  pending): (1) generalize the lemma's refinement premise to a Δr that
  carries the descent binders (keeps fills β-free by the refinement's
  own wf discipline; touches the case-lemma kit that pins `Δr = ∅`);
  (2) a standalone `P_i = □`-column lemma by its own consistency
  induction with a Δr-indexed refinement premise + ftv-bound lemmas for
  consistency (`ftv S ⊆ ftv Q ∪ dom Θ`) and ρ (`ftv ψa ⊆ ftv ψsub ∪ Δρ`);
  (3) a positional hole-apartness premise (flex_apart-style) — 
  dispreferred, since call sites cannot derive it across the binder
  descent from cleanliness alone.

## FALSE (machine-checked, 2026-07-28) — `lemma:complete-constraint-collection-solving-var` (P6-Sv) is FALSE: its own ForallL case MANUFACTURES the configuration that the 2026-07-25 "unreachable" resolution excludes

- Where: subtyping-proofs.tex:1696 (`lemma:complete-constraint-collection-
  solving-var`, the SUBTYPING twin of the consistency lemma at
  consistency-proofs.tex:1181).  Mech: the counterexample is
  `frost/algo/cex/cex_p6sv_forall_flex.v`
  (`p6sv_with_p6cv_premises_is_false`, Qed, axiom-free).
- **Status: FALSE as an isolated statement, and — unlike the 2026-07-25
  entry above — the standing reachability argument does NOT cover it.**
  The statement still needs a decision by the paper's authors.
- **RESOLVED IN THE MECHANIZATION (2026-07-29), statement-side.**  The
  algorithm is UNCHANGED; the lemma carries one extra premise,
  `flex_shield Θ₀ Ψ' Δρ P₀ ψa` (a positional invariant: at every position
  where a raw Θ₀-flexible faces the guess, the guess is both Δρ-clean and
  Ψ'-tag-free — with an explicit row keeping it from being too strong, see
  `fsh_rsubst_var`), plus `flex_apart_walk` (P6-Cv's own premise at every state
  the descents can reach).  `a_solve_sub_complete_var` is now **Qed and
  axiom-free** in `frost/algo/prop_look_complete_sub_var.v`, and
  `flex_shield_excludes_cex` is the machine-checked regression test that the
  premise rules out the witness below.  What the authors must decide is
  whether the PAPER adopts this side condition (or an equivalent one) —
  the write-up as it stands claims a statement that is false.

### The witness (ρ is the IDENTITY — this is not a ρ-encoding artefact)

```
Θ₀ = α̂            Θ = α̂ := ⟨⟩→⟨⟩        θ = [α̂ ↦ ⟨⟩→⟨⟩]
N = TY  M = TC    Pi = ∀β. β→β          P₀ = α̂
ψa = ψsub = ∀^ε β. β→β                  Q  = inh{⟨⟩→⟨⟩}
Ψ' = Ψi = {ε}     Ψa = Ψsub = Ψρ = ∅    Δ = Δρ = ∅
```

Every premise of the paper's statement holds — and so does every premise of
the mech's CLOSED consistency twin `a_solve_eq_complete_var`, including the
mech-only `flex_apart` freshening invariant (vacuous at `Δρ = ∅`), the
subject well-formedness premise that made P6-Cs true, and the subtyping-side
tag EQUATION `Ψi , Ψa = Ψ'`.  The subtyping premise is `Sub-ForallL`
instantiating `β := ⟨⟩`, then `Sub-Check`; the refinement is a mono paint
refining itself; the precision is `P-Forall` over the identity.

The algorithm is then FORCED: a `∀` is not `guarded`, so the only solve rule
with a `∀` input skeleton is `SolS-ForallL`; its body `β→β ≼[TC] α̂` can only
go `SolS-Check` + `SolE-FlexR`, giving `P_a = ∀β. α̂`.  The precision
obligation `θ_a(∀β.α̂) ⊑ᵖ ∀^ε β.(β→β)` reduces to `⟨⟩ ⊑ᵖ β` — no rule.  The
refutation holds for **every** output metasubstitution `θ_a : Θ₀ ⊑ Θ` (the
file proves the general fact `mono_paint_ppre_target_ftv`: a mono-paint
subject is never precise to a target mentioning a variable outside Θ), so it
is not an artefact of the mech's `θ_a := θ` strengthening.

### Why the 2026-07-25 resolution does not apply

That resolution (entry above) rules the bad configuration — a raw Θ₀-flexible
payload facing a ρ-substituted part of `ψa` — UNREACHABLE, because `LE-FlexR`
freshens a flexible counterpart at a compound subject.  Two independent gaps
at the subtyping level:

1. **ρ is created by the lemma's own induction, not by constraint
   collection.**  The paper's ForallL case sets `ρ_b = ρ ∘ [ψ_b/β]` starting
   from `ρ = id`; so the recursive call sees `ψa = β→β` with `β` ρ-substituted
   — i.e. the induction manufactures the "unreachable" premise set out of
   innocent inputs.  Any `flex_apart`-style invariant stated at the CURRENT
   `ψa` is destroyed by that descent (`Δρ := Δρ ∪ {β}` while `P₀` is not
   decomposed), so it cannot be maintained.
2. **The raw flexible payload does not come through `LE-FlexR` at all.**  It
   comes from `LS-Var` — and `a_looksub` (fig:constraint-collection) has NO
   FlexR rule, so nothing freshens `α̂` on the subtyping route.
3. The paper's own side condition ("for every rigid variable in `ψa`
   substituted by ρ, `P_i` has the same rigid variable in the same position",
   :1730) is SATISFIED all the way down: at the recursive call `ψa = β→β`,
   `ρ_b` substitutes `β`, and `P_i = β→β` does have `β` in exactly those
   positions.

### What a repair has to do (for the authors)

The failing configuration is "the accumulated input skeleton is a `∀` while
the constraint payload is a raw flexible whose θ-image is fixed before the
`∀`'s binder exists".  Either

- (a) exclude it by an invariant that is stable under the ForallL descent —
  it must forbid a raw Θ₀-flexible payload facing ANY tagged `ψa` (not just a
  Δρ-dirty one), since a tagged `ψa` will become Δρ-dirty one ForallL step
  later — together with a reachability argument covering the `LS-Var` route;
  or
- (b) accept that the ALGORITHM is incomplete here and change it (e.g. freshen
  the flexible payload when solving under a `∀` binder, mirroring what
  `LE-FlexR` does at arrow nodes); or
- (c) restrict the declarative guesses `ψa` that the completeness statement
  quantifies over.

Nothing in the mechanization is retracted by this entry: P5, P6-Cv and P6-Cs
are unaffected (they have no ForallL, so ρ never grows there).

### Addendum (2026-07-28, after re-reading paper + implementation): root cause is `SolE-FlexR`; proposed fix = keep the non-flexible side

Verified against all three witnesses:

* **Paper** (fig:constraint-solving, full-algo-spec.tex:1371): `SolE-FlexR`
  is `nonflex{P} ⊢ solveeq{P}{α̂}{α̂}` — context-free, keeps the flexible,
  discards `P`.  The consistency -var proof's Arrow case says "*We assume
  P₀ = P₀,₁→P₀,₂*" (consistency-proofs.tex:1421) — the flexible-P₀ subcase
  is silently absent, and the leaf cases dispatch it with one sentence
  ("use SolEqFlexL or SolEqFlexR", :1272) with no precision argument.  The
  missing subcase is exactly where the subtyping ForallL descent lands.
* **Implementation** (type.ml): `solve_eq`'s `| _, (MFlex _ as alpha) ->
  end_rule alpha` and `solve_sub`'s ForallL/Check chain reproduce the mech
  behaviour line-for-line; `Pa = ∀β.α̂` on the witness.  The `(β,γ)` pairs
  LE-FlexR puts into ξ are consumed by `look` only to propagate the KIND
  (`BMFlex (γ, None, k)`) — no link constraint — so the mech's unlinked
  fresh flexible is a faithful encoding.  `LS-Var` passes the raw payload;
  the sub route has no freshening anywhere.
* **Mech**: `cex_p6sv_forall_flex.v` (Qed).

**Why the failure is forced.**  `SolE-FlexR` is the ONLY solve rule in
which the payload REPLACES a structured subject (`SolE-Var`/`FlexL`/
`VacuousR` all keep the subject; every other rule is a congruence or a
ghost step).  Under a `SolS-ForallL` descent the subject's body mentions
the locally-opened rigid `β`; replacing it by `α̂` commits the skeleton to
"whatever monotype α̂ becomes", and no future solution of `α̂` can mention
`β` (it is bound outside `α̂`'s scope) — the accumulated information
`β→β`, which an earlier eq-constraint had established and which the
declarative `ψa` retains, is unrecoverable.  Freshening the payload (the
LE-FlexR treatment) does NOT help: a fresh `γ̂ ∈ Ξ` is equally bound
outside the binder.  The eq route never hits this because CONSISTENCY (no
ForallL) pins `ψa` mono against a flexible counterpart; only the sub
route, where the declarative side may instantiate a `∀` down to the
flexible's mono image, exposes it.

**Proposed fix (one rule): flip `SolE-FlexR`'s output —**

```
nonflex{P}  ⊢  solveeq{P}{α̂}  ⤳  P        (was: ⤳ α̂)
```

(and correspondingly `end_rule p` in type.ml's `solve_eq`.)  Arguments:

1. *Completeness*: in every flex-payload case of the -var lemmas the
   refinement premise pins `θα̂` mono ⇒ `Q` mono-ish ⇒ no tag of `ψa` is
   solved by this constraint (`Ψa = ∅`), so the required conclusion
   `θ Pa ⊑ᵖ[Ψi ∪ Ψa] ψa` with `Pa := Pi` IS the precision premise.  On
   the counterexample the fixed algorithm yields `Pa = ∀β.β→β` and the
   needed precision is literally the cex's own `Hpre`.
2. *Soundness*: keep-subject-discard-payload is the existing `SolE-Var`
   pattern; the discarded `α̂`-constraint is re-established by the main
   subtyping run on the committed skeleton (unchanged discipline).  On
   the witness the recheck goes `∀β.β→β ⩽ α̂` → flex split
   `α̂ := β̂₁→β̂₂` → instantiate `β := β̂₁` — accepts, matching the
   declarative run.
3. *Old behaviour never load-bearing*: the two mech sites that USED
   keep-`α̂` (P6-Cv's flexible-P₀ chain, P6-Cs's LE-FlexR row) both have
   `ψa` pinned mono there, and close via the premise under keep-`P` as
   well — more simply.  In particular the mech-only `flex_apart` premise
   of P6-Cv (and the whole 2026-07-25 "unreachable-configuration"
   resolution, incl. `cex_p6_flex_counterpart`'s isolated falsity) exists
   ONLY to protect keep-`α̂`; under the flip it can be dropped, making
   P6-Cv premise-faithful to the paper.
4. *No alternative*: a statement-side premise cannot exclude the
   configuration (the top-level instance is reachable and declaratively
   solvable — e.g. `(fun x y -> y x) (id0 ids) useMono` puts a raw
   λ-bound flexible opposite `id0`'s result while `ids` forces the
   ∀-instantiation); restricting the declarative side would reject
   standard impredicative programs; freshening fails on scope as above.

Mech impact if adopted: rule flip in algo/def_rules.v (full algo
rebuild); ~13 construction sites (all in prop_look_complete*.v, get
SIMPLER); one changed case in each induction over `a_solve_eq`
(prop_solve_sub, prop_decorate_sub/key, prop_sub_sound,
prop_look_complete utility lemmas, test_unify_regression); plus a small
new "mono-ish target solves no tags" lemma for `ad_pat_sub_g`.

### Correction (2026-07-28, after TESTING the implementation): the source-level reachability claims above were WRONG; the composed pipeline shields the SolE-FlexR site; statement-side fix is back on the table; NEW independent impl crash found

Ran the built artifact (`met.exe`) on the constructed programs.  Three
results, two of which refute my own earlier end-to-end claims:

1. `(fun x y -> y x) (id0 ids) useMono` — **ACCEPTED** (rc=0).  The
   claim above that this exhibits the failure is WRONG on two counts:
   (i) `I-App` pre-shapes an applied λ's binder by
   `guess_mono(skeleton-of-argument)` — the expected type is an arrow of
   fresh flexibles, never a bare flexible; (ii) the skeleton pass
   (`PI-*`) ERASES top-level ∀s of argument skeletons to `∀◇(□→□)`
   (SI-ForallL + SI-UnivGhostR), so the eq-payload never carries the
   rigid `∀β.β→β` and a MONO instantiation suffices — which is exactly
   what the run does.
2. `h id0 3` with `h : ∀c.((∀b.b→b)→c)→c` — rejected, but CORRECTLY:
   checking against a guarded type is `LS-Check` = pure CONSISTENCY
   (shallow subtyping — no covariant descent under arrows in TC mode),
   so it is declaratively rejected too.  My "FN-mode arrow" reading of
   that shape was wrong.
3. **NEW BUG** — `k : ∀a. list a → a`, `args : list (∀b.b→b)`,
   `let g = fun f -> f (k args)` (f unannotated): the implementation
   **CRASHES** with `Failure("broom_flex_poly: should not happen")`
   (type.ml:1048 — `sub_flex` pops a `Marker`/`Lock` while brooming the
   bare flexible `f` against a Fun-mode whose argument skeleton carries
   the manifest rigid `∀b.b→b`, kept by the eq-solve under the `list`
   constructor, which skeleton erasure does NOT strip).  The annotated
   twin `fun (f : (int→int)→int) -> f (k args)` is ACCEPTED.  Whether
   the unannotated program is declaratively typeable turns on whether
   the declarative skeleton judgment may return a lazy/ghosted skeleton
   for `k args` (if yes — which the ghost rules suggest — this is a real
   completeness failure of the composed algorithm, through the
   flex-broom/mono-assign wall, NOT through SolE-FlexR).  Either way the
   assertion failure is an artifact bug to report.

CONSEQUENCE FOR THE FIX.  The pipeline appears to maintain exactly the
invariants that keep the SolE-FlexR configuration out of real runs:
FN-mode eq-payloads are skeletons with ghost-erased top-level ∀s;
TC-mode collapses to consistency (where a flexible payload pins
everything mono — the closed P6-Cv/P6-Cs territory); bare-flexible
expected types arise only from inference-mode λs, and routes combining
them with manifest-∀ payloads hit the flex-mono wall earlier (finding
3).  So the -Sv LEMMA as stated remains FALSE (the mech counterexample
stands), but the repair should likely be STATEMENT-SIDE after all:
strengthen P6-Sv's premises with the reachability invariant — a
candidate formulation: "every tag in Ψi was solved by a GHOST (∀◇/fill)
step of the precision derivation, not by a rigid quantifier of Pi,
whenever some constraint payload is a raw flexible" — equivalently,
rigid top-level ∀-spines in Pi and raw-flexible payloads for the same
look are mutually exclusive.  The exact form must be read off P6-Ss's
call sites and proved supplied by the pipeline (P7).  The SolE-FlexR
flip remains sound and uniformizing but is no longer forced; it would
not fix finding 3 (different wall).  Decision deferred to the authors.

## IMPLEMENTATION BUG (report to WT) — `broom_flex_poly: should not happen` assertion failure on a 5-line program (2026-07-28)

- Where: `paper/artifact/implementation/lib/type.ml:1048` (`sub_flex`, the
  flexible-variable broom walk: `| Marker | Lock _ -> failwith
  "broom_flex_poly: should not happen"`).
- Witness (benchmark vocabulary; crashes with
  `Fatal error: exception Failure("broom_flex_poly: should not happen")`):

  ```text
  type list a = Nil | Cons of a, list a

  val k    : forall a . list a -> a
  val args : list (forall b . b -> b)

  let g = fun f -> f (k args)
  ```

  The annotated twin `let g2 = fun (f : (int -> int) -> int) -> f (k args)`
  is ACCEPTED (rc=0).
- Mechanism: the skeleton pass keeps the manifest `∀b.b→b` when it sits
  UNDER a constructor (`list`) — ghost erasure strips only top-level ∀s of
  the argument type — so `k`'s eq-solve yields `a := ∀b.b→b` and the
  skeleton of `k args` has a rigid top-level ∀.  `f` is an inference-mode
  λ-binder, i.e. a BARE flexible; inferring `f` against the Fun-mode whose
  payload is that poly skeleton enters `sub_flex` (SI-FlexMono), whose
  context walk pops a `Marker`/`Lock` before resolving — a state the code
  asserts unreachable.
- Status — **ROBUSTNESS BUG ONLY (author decision 2026-07-28: the program
  should be REJECTED; the impl must reject cleanly instead of crashing).**
  The lazy-skeleton worry raised earlier is unfounded — the declarative
  side rejects it too, and the mech rules show why: the skeleton of `args`
  is derived from its type by SK-checking against □, whose Check case is
  CONSISTENCY against the fill — and consistency has NO rule for a
  ∀-subject against a hole or ∀◇ TARGET (only `ad_pat_consis__hole` with
  the hole as SUBJECT), so the inner `∀b.b→b` survives into every
  derivable skeleton; `k`'s instantiation must be consistent with it, so
  `k args`'s skeleton is forced poly; and the declarative app rule's
  domain premise is consistency `τ_dom ∼ skel(arg)`, mono vs ∀ — no rule.
  Hence rejection is forced declaratively; no completeness gap here, and
  the flex-mono wall is the intended design.


## GAP (proof-step; statement TRUE) — `complete-constraint-collection-solving-var`'s UnivGhostLG case omits the `P_i = □` subcase (2026-07-28)

- Where: subtyping-proofs.tex:2196, case `UnivGhostLG` of
  `lemma:complete-constraint-collection-solving-var`.  Mech: the `□` row of
  the `univ_ghost_lg` case in `frost/algo/prop_look_complete_sub_var.v`
  (now proved).
- The paper writes "We know that `P_i` must have a top-level `∀◇`", reading
  the precision premise `Δ|Θ ⊢ᵃᵈ precise[Ψi]{θP_i}{∀◈ψ'}` as if only
  `P-UnivGhostKeep` — whose subject is `∀◇P` — could target a `∀◈`.  But
  **`P-Ghost` is target-agnostic**: `□ ⊑ᵖ[·] ψ` holds for ANY `ψ` (given its
  Δ-disjointness side condition), so a hole input skeleton is precise to a
  `∀◈` as well, and the subcase is real.
- Not a statement problem: the row goes through.  Nothing is decomposed (a
  `□` input stays `□`), so the induction hypothesis's own solve is the one
  needed; only its precision must be lifted back under the ghost.  In the
  mech that lift is `ad_ppre_lift_topholeg`, which needs (i) the shape of a
  `□`-input solve output (`a_solve_sub_hole_output`: `□` or `∀◇B`), (ii)
  stripping a `∀◇` from the subject against a guarded guess
  (`ad_ppre_tophole_strip`, whose FILL/KEEP rows die on guardedness and
  whose flexible-target row recurses through the definition), and (iii)
  guardedness of the guess's erasure, transported along ρ by
  `uskl_rho_guarded_erase`.
- **Corroboration (checked 2026-07-28, and it is decisive): the same
  authors handle `P_i = □` FIRST in the IDENTICAL situation on the
  consistency side.**  `complete-consistency-cc-solving-var`'s case
  `UnivGhostG` (consistency-proofs.tex:1477-1516) has exactly this shape —
  `ψ_a = ∀◈ψ'`, a dotted universal ghost on the guess — and its subcase
  list is:
    1. `P_i = □` — "IH on refa and refb with input `□` … our goal follows
       from SolEq-GhostL and choosing `P_a = ∀◇P_0'`", i.e. precisely the
       row the mech proves (nothing decomposed, the IH's own solve reused);
    2. `P_i = ∀◇P_i'`;
    3. "the remaining non-flexible shapes are impossible by inversion on
       the precision premise; the flexible case follows from SolEq-FlexL".
  Were there an invariant forcing a `∀◇` input skeleton opposite a dotted
  ghost, subcase 1 would be dead and would have been listed as impossible
  (as the same proof does list `Ghost`, `UnivGhost`, `UnivGhost1` and
  `UnivGhost2`).  It is not; so the subtyping side's compressed write-up
  ("Similar to the previous case of ForallL … It is simpler …") simply
  dropped it.
- To be fair to the paper's phrasing, its claim is ALMOST right: precision
  does force the input skeleton to be GHOSTLY at a `∀◈` guess — the only
  live shapes are `□` and `∀◇P_i'` (unit / var / arrow / ∀ are refuted, in
  the mech by `ad_ppre_guarded_topholeg_absurd`).  It named one of the two
  ghost shapes.
- Side note on the same case: the paper also provides for a FLEXIBLE `P_i`
  ("the flexible case follows from SolEq-FlexL").  In the mech that case is
  VACUOUS — `θP_i` is then a monotype painting, and
  `ad_ppre_mono_paint_topholeg_absurd` (already needed by P6-Cv) shows no
  painting is precise to a dotted ghost.  Harmless over-provision, recorded
  only so the discrepancy is not re-investigated.

## ~~GAP~~ RESOLVED BY THE AUTHORS (2026-07-29) — `lemma:complete-constraint-collection-solving` (P6-Ss), ForallR case: \lslab{ForallR} does NOT need `β ∉ ftv 𝒞`; scope is checked SEPARATELY at the use site.  Reclassified to a MECH-ENCODING question

- Where: subtyping-proofs.tex:2412 (the ForallR case of P6-Ss); the rule is
  full-algo-spec.tex:1049.
- **The rule lets `𝒞` escape the binder's scope.**  \lslab{ForallR} reads

  ```
        looksub[TC] α A B 𝒞 [Ξ]
    ────────────────────────────────
      looksub[TC] α A (∀β.B) 𝒞 [Ξ]
  ```

  Under the Barendregt convention the premise's `B` has β free, so the
  premise's `𝒞` may mention β — while β is BOUND in the conclusion's
  `∀β.B`.  For the rule to be well-scoped it needs `β ∉ ftv 𝒞` (and
  `β ∉ dom Ξ`).  A locally-nameless encoding makes this explicit: the
  mechanized `a_looksub__forall_r` is cofinite in β with the SAME `Ξ ⨾ 𝒞`,
  which IS that side condition.
- **The proof does not supply it.**  The ForallR case applies
  \lslab{ForallR} to a single IH instance ("By \lslab{ForallR} on \refc")
  and then establishes β-freshness only for `P_a` — "by \refh, we have
  β∉ftv(θ_a P_a), and thus β∉ftv(P_a)" — never for `𝒞` or `Ξ_c`.
- **The gap is real, not vacuous.**  With `A = ⟨⟩→α` and `B = ⟨⟩→β`,
  \lslab{Arrow} then \lslab{Var} collect `𝒞 = [ ≼ β ]`, and \lslab{ForallR}
  cannot fire.  Completeness therefore has to SHOW that configuration
  unreachable.  On the consistency side that is exactly what the invariant
  `ftv 𝒞 ⊆ ftv ψ_a ∪ dom Ξ_c ∪ dom θ ∪ def_ftv Θ` does (ψ_a is Θ-scoped,
  hence β-free); the mechanized P6-Cs carries it as a conclusion.
- Note the consistency route does NOT transport verbatim: it comes from the
  target-ftv bound for consistency, whose ForallInh opens with a fresh
  VARIABLE, whereas Sub-ForallL instantiates with a GUESS whose only bound
  is `ftv ψ_b ⊆ dom Θ`.  The subtyping proof needs the bound tied to `ψ_a`
  through the PRECISION and REFINEMENT premises instead.
- **\lslab{ForallL} is NOT affected — the two rules bind on opposite sides.**
  Constraints carry TARGET subterms (`ftv 𝒞 ⊆ ftv P' ∪ dom Ξ`,
  `a_looksub_ftv`).  \lslab{ForallL} binds β in the SUBJECT and leaves the
  target `P'` untouched, so β cannot reach `𝒞` at all and the side
  condition is discharged structurally, with no completeness argument;
  likewise for `Ξ`, whose entries are freshly generated by \lslab{FlexR}.
  \lslab{ForallR} binds β in the TARGET, and the premise's target is
  `B[β]`, so the same bound ADMITS β.  The obligation is ForallR-only.
- **RESOLUTION (WT, 2026-07-29).**  *"look 不管 scoping — look 完另一个单独的
  wellformedness 检查了"*: constraint collection is deliberately
  scoping-AGNOSTIC.  The scope check is the SEPARATE premise at the use
  site — the extract rule's `\Theta_0,\Xi \vdash P_1` (full-algo-spec, the
  `[P_0] \vdash^n_m \forall\alpha.P \leqslant Q \dashv \Theta_1` rule) — which
  rejects an instantiation candidate that escaped its binder.  So
  \lslab{ForallR} carries NO `β ∉ ftv 𝒞` obligation and the completeness
  proof owes nothing: this is NOT a paper gap.  The entry stays for the
  record and because it leaves a MECH question behind.
- **What remains is a MECHANIZATION-ENCODING question — and it is settled:
  KEEP the cofinite rule.**  The locally nameless `a_looksub__forall_r` is
  cofinite in β with one `Ξ ⨾ 𝒞`, which *is* the side condition, so the mech
  rule is strictly narrower than the paper's.  That is not a defect:
  completeness of a NARROWER algorithm is a STRONGER theorem, and soundness
  is unaffected.  The only real question is whether the completeness proof
  can still discharge `β ∉ ftv 𝒞` — and it can, by re-acquiring the
  ψa-RELATIVE bound P6-Cs already carries as a conclusion,
  `ftv 𝒞 ⊆ ftv ψ_a ∪ dom Ξ_c ∪ dom θ ∪ def_ftv Θ` (β is fresh for all four).
  P6-Ss's statement dropped that conjunct; the ForallR row must put it back.
- **Why that route is available NOW but was not before.**  The bullet three
  up says P6-Cs's bound "does not transport, because \sublab{ForallL}
  instantiates with a GUESS bounded only by `ftv ψ_b ⊆ dom Θ`".  The
  ρ-generalized induction (next entry) DISSOLVES that objection: under ρ the
  lookup side never sees a guess at all — every \sublab{ForallL} opens with
  a fresh RIGID and the guess rides in ρ — so the collected constraints stay
  bounded by ψ_a exactly as on the consistency side.  ρ's own binders live
  in Δρ, and ForallR's β is a genuine context rigid, never a Δρ entry, so
  the bound still excludes it.  ⇒ ForallL and ForallR are fixed by the SAME
  change.
- ⚠️ **For the record: the two rule ENCODINGS are NOT literally equivalent**
  (checked, not assumed).  `SS-Var` is `Θ ⊢ₛ α̂ ≼[m] Q ⤳ α̂` — it DISCARDS
  the target — so a `𝒞` that mentions β can solve to a `P_1` that does not,
  and `\Theta_0,\Xi \vdash P_1` then lets it through.  The lax rule therefore
  admits derivations the cofinite one refuses.  This costs nothing here
  (narrower algorithm ⇒ stronger completeness claim), but it means "the wf
  check catches it anyway" is not by itself a proof of equivalence, and the
  exists-fresh relaxation should NOT be adopted on that basis.
- ⚠️ **CORRECTION (2026-07-30): the ψa-relative bound above is NOT reachable
  in that form, and the ForallR row does NOT use it as stated.**  Its leaf
  would need the sub-side analogue of `ad_pat_consis_target_ftv`
  (`ftv Q ⊆ ftv R ∪ def_ftv Θ` from a subtyping derivation with a decorated
  subject), and that lemma is FALSE — machine-checked,
  `cex/cex_p6ss_sub_target_ftv.v`.  `is_tskl` excludes the
  \sublab{Ghost} row but NOT \sublab{ForallL}: a tagged `∀^ε` IS a decorated
  skeleton, and its instantiation is bounded only by `dom Θ` — the
  DERIVATION's context, which \sublab{ForallR} grows by the very β being
  stripped.  So `dom Θ` is the strongest sound bound and it is exactly the
  wrong one; the "ρ dissolves the objection" argument above is right about
  the LOOKUP side but does not reach the derivation's own ForallL guesses.
- **The row is nonetheless CLOSED (2026-07-30), by a case split the paper
  does not make.**  \sublab{ForallR} forces mode `TY`/`TC`, where the only
  applicable rules are \sublab{Check}, \sublab{ForallR} and
  \sublab{ForallL} — so under a \sublab{ForallR} the `P = α` leaf is
  reachable ONLY when `P` is a ∀/⊤◇-STACK over α, and such a `P` never
  descends the target at all (\lslab{ForallL}/\lslab{UnivGhostL} peel the
  stack and \lslab{Var} fires at the UNDESCENDED `∀β.P_0`).  Every other
  α-leaf sits under \lslab{Check}, i.e. inside P6-Cs, whose bound IS
  ψa-relative.  Mechanized as a mode-guarded disjunction; see
  docs/DESIGN-completeness-subtyping.md §8 (h).  **Authors: the paper's
  ForallR case should say which of the two it is in, or the step is
  incomplete as written.**
- Mech status: **P6-Ss is CLOSED** (2026-07-30) —
  `a_looksub_solve_complete_gen` and the paper's premise-free
  `a_looksub_solve_complete` are `Qed` and axiom-free in
  `frost/algo/prop_look_complete_sub_cstr.v`; all twelve rows and both
  special cases are proved.

## GAP (proof-step, 2026-07-29) — `lemma:complete-constraint-collection-solving` (P6-Ss), ForallL case: the IH instance needs `θψ_b = ψ_b`, which fails even for legitimate θ; no side condition on θ repairs the step — the statement is believed TRUE via a ρ-generalized induction

- Where: subtyping-proofs.tex:2600–2643 (the \sublab{ForallL} case of P6-Ss).
  Machine-checked evidence: `cex/cex_p6ss_inc_compat.v`.
- **The step.**  The rule's premise is
  `⊢ ((θ S')[ψ_a/α])[ψ_b/β] ⩽ Q`, and the proof rewrites it (\refe) as
  `⊢ ((θ S')[ψ_b/β])[ψ_a/α] ⩽ Q`, then applies the IH with
  `S := S'[ψ_b/β]` and `P := P'[⌊ψ_b⌋/β]` (\reff).  For the IH's subject —
  which by the lemma's own statement is `(θ S)[ψ_a/α]` — to BE \refe, one
  needs

  ```
      θ (S'[ψ_b/β])  =  (θ S')[ψ_b/β] ,     i.e.     θ ψ_b = ψ_b .
  ```

  The paper justifies \refe by "capture-avoiding substitution and freshness
  conditions", which covers the α/β commutation but NOT the θ/ψ_b one.
  Nothing gives `θψ_b = ψ_b`: `ψ_b`'s only constraint is `Θ ⊢ ⌊ψ_b⌋`, so
  `ftv ψ_b ⊆ dom Θ`, and a Θ-scoped guess may mention `dom θ` variables.
  Nor can `ψ_b` be re-based below θ: θ's images are MONOTYPES while `ψ_b`
  is a general tagged skeleton (impredicative instantiation is the point of
  the rule), so `ψ_b` has no θ-pre-image in general.
- **No side condition on θ rescues the step** (this bullet went through two
  corrections, both machine-checked, before converging):
  1. Barendregt disjointness `dom θ ∩ dom Θ = ∅` is UNSATISFIABLE at
     identity metasubstitutions — their flexible entries are all PRESERVED
     in the target (algorithmic.tex:135–140, "our algorithms always give
     identity metasubstitutions"), so `dom ι ⊆ dom Θ`
     (`id_inc_dom_overlap`).
  2. Syntactic compatibility `∀ α̂ ∈ dom θ ∩ dom Θ, θα̂ = α̂` EXCLUDES a
     legitimate θ: at `Θ = [α̂ := ⟨⟩]` the θ with `θα̂ = ⟨⟩` substitutes a
     DEFINED survivor's definition — exactly what "preserved … but possibly
     with more monomorphic information (e.g., from α̂ to α̂ := ⟨⟩)"
     licenses — and it is inc-EQUIVALENT to ι
     (`def_subst_theta_is_legit`).
  3. The strongest defensible invariant is therefore SEMANTIC:
     `α̂ ∈ dom Θ ⟹ Θ ⊢ θα̂ ≡ α̂` (for an UNDEFINED survivor ≡ collapses to
     `θα̂ = α̂`; for a defined one it licenses the definition).  It still
     does NOT give the syntactic `θψ_b = ψ_b` the IH needs — the
     definition-substituting θ of point 2 satisfies it and still moves a
     `ψ_b` that mentions α̂.  The written step holds essentially only at
     ι-like θ, while the lemma quantifies over general θ.
- **Mech repair (decided; keeps the paper's statement UNCHANGED).**
  Restructure the induction as P6-Sv's already is: generalize the motive
  over an accumulated rigid substitution ρ.  Each ForallL opens with a
  FRESH RIGID β and absorbs its guess into ρ (`ρ ∘ [ψ_b/β]`,
  `uskl_rho_subst`), so the subject is `ρ((θS)[ψ_a/α])` with β ∉ dom θ and
  θ's images β-free — the θ/ψ_b commutation never arises, for ANY θ.  The
  theorem is the ρ = identity instance.  The `P = α` leaf then calls
  `lemma:…-var` (P6-Sv) at the ACCUMULATED ρ — its general-ρ interface,
  which the paper's own "with the identity substitution" leaf never
  exercises.  The paper could adopt the same restructuring; alternatively
  its authors may prefer to note the lemma is only ever instantiated at
  ι-like θ (where the written step is sound) — but then the ForallL
  recursion must be checked to preserve ι-likeness, which is the same
  obligation in different clothes.
- **Independent definitional observation** (for the authors; surfaced by
  the same review).  The figure's flex rule for `inc[θ]{Θ,α̂}{Θ'}`
  constrains the image by nothing but `Θ' ⊢ τ`, so it formally admits a θ
  that "solves" α̂ to ⟨⟩ while Θ' keeps the SAME α̂ UNDEFINED —
  `[(α̂,⟨⟩)] ∷ [α̂] ⊑ [α̂]` is derivable (`inc_moves_survivor`) — junk
  under the information-increase reading (the target does not refine such
  a θ's claim).  The invariant of point 3 above
  (`α̂ ∈ dom Θ' ⟹ Θ' ⊢ θα̂ ≡ α̂`) is the side condition that excludes it
  while keeping the legitimate definition-substituting θ.  The mech keeps
  `a_inc` faithful to the figure (the ρ-repair needs no such condition);
  whether the paper's definition should carry it is the authors' call.
- **Scope of the ρ-repair, measured (2026-07-29).**  The Check row of P6-Ss
  hands its WHOLE subject to P6-Cs (`a_lookeq_solve_complete`), and a
  ForallL can sit above a Check — so **P6-Cs must be ρ-generalized too**.
  That is threading, not new theory: P6-Cv
  (`a_solve_eq_complete_var_gen`, prop_look_complete_var.v:505) ALREADY
  takes `uskl_rsubst NM Θ Δρ Ψρ ψsub ψa` and the whole `uskl_rho_*_l_inv`
  inversion kit exists, so P6-Cs's rows invert ρ per subject shape exactly
  as P6-Cv's do, its measure (`size R' + size P0`, on the ρ-FREE ideal
  subject) is unaffected, and its leaf passes the real ρ down instead of
  `urho__refl`.  P6-Cs's own ∀ rows open with fresh VARIABLES, so ρ never
  grows inside it.
- **Bookkeeping done en route** (2026-07-29, committed):
  - The scope premise `ftv S ⊆ {α} ∪ dom Θ0` was relaxed to
    `ftv S ⊆ {α} ∪ dom Θ0 ∪ dom Θ` with the dual conclusion
    `α0 ∈ dom θ_c ⇒ α0 ∉ {α} ∪ dom Θ0 ∪ dom Θ` strengthened to match, in
    both `prop_look_complete_cstr.v` (P6-Cs, re-`Qed`ed) and
    `prop_look_complete_sub_cstr.v`.  Kept: harmless, and the Arrow row
    wants the strengthened conclusion.
  - The reverse direction of
    `lemma:constraint-collection-stable-substitution` is mechanized as
    `a_looksub_lookeq_subst_stable_rev` (algo/sub/prop_looksub.v §4b, `Qed`, axiom-free).
    The ρ-route does not need it (the looksub side stays on var-opened
    subjects), but it is the lemma the PAPER's own proof route ends with,
    and it is true and kept.
  - `sub_shield` now carries Δρ (the current statement instantiates it at
    `empty`, so nothing else moved), with `sub_shield_add_fresh` /
    `_weaken_tvar` — Sub-ForallL grows Δρ by a fresh β while ψa does NOT
    move, so neither `fastep_all_r` nor `fsh_all_r` applies and the Δρ
    quantifier is built into the definition instead (as the `ss_walk` one
    already is).
  - `ad_partial_precise_delta_shrink_fresh` (`Qed`) — the mirror of
    `ad_partial_precise_delta_weaken_fresh`: Sub-ForallL hands the IH the
    precision premise at `add β Δ` (β joins Δρ, and `Δρ ⊆ Δ`) and must
    return the conclusion at plain Δ.

## ⚠️ REPAIR-PREMISE GAP (authors' call) — `flex_apart` is missing `fsh_rsubst_var`'s mirror, and without it P6-L's side condition is UNSATISFIABLE at an arrow (2026-07-30)

**Machine-checked:** `frost/algo/cex/cex_p7_shield_arrow.v`
(`p7_shield_arrow_flexfree_is_unsatisfiable`,
`p7_shield_arrow_poly_is_unsatisfiable`; both Qed, axiom-free).

P6-Cv's repair premise `flex_apart` and P6-Sv's `flex_shield` are deliberate
mirrors, and `flex_shield` carries

    fsh_rsubst_var : α ∈ Δρ  →  flex_shield Θ0 Ψ' Δρ P0 (uskl_var_f α)

whose own comment records why it had to be added: *"a ρ-REPLACED RIGID VARIABLE
is safe opposite ANY payload, flexible or not — this is P6-Cv's leaf … WITHOUT
this rule the premise is TOO STRONG."*  **`flex_apart` never got the mirror.**

The consequence only shows up at P7.  `sub_shield` (P6-Ss/P6-L's premise) has a
`flex_apart_walk` conjunct that quantifies over the ρ-walk, and Sub-ForallL's
walk step `fastep_all_r` — which P6-Sv's own ForallL row builds — opens a tagged
quantifier of the guess at a fresh β, adds β to Δρ, and leaves `P0` alone.  So
from `(∅, P0, ∀^ε b. b)` the walk reaches `flex_apart Θ0 {β} P0 (var β)`, and at
an **arrow** `P0` no rule applies: `fa_clean` wants `{β} ∩ {β} = ∅`, the
congruence rows want another shape, and there is no `fa_rsubst_var`.

So `sub_shield Θ0 Ψa ∅ (P1 → P2) (∀^ε b. b)` is **unsatisfiable** — P6-L is
vacuous there, and P7b's Sub-ForallL cannot use it.  Two witnesses, because they
say different things: `⟨⟩ → ⟨⟩` is FLEX-FREE (so `flex_apart` is also missing
`fsh_flexfree`'s mirror), while `(∀γ. γ→γ) → α̂` is not flex-free and its
counterpart is not mono-ish, so no existing route reaches it either.

**Recommended repair:** add `fa_rsubst_var` to `flex_apart`, mirroring
`fsh_rsubst_var` verbatim.  It kills both witnesses.  **Cost, measured:** the ~8
`flex_apart` inversion lemmas each gain a case, all but one closing with
`apply fa_rsubst_var; assumption`; and `flex_apart_flex_var_clean` must weaken to a
disjunction (its single consumer, P6-Cs's Arrow row, still reaches its "ψa is a
mono paint" conclusion, since a Δρ-variable IS one — but only after peeling a
∀◈ stack, which at `SK` is not free).

**Held pending the authors' decision** because `flex_apart` is a side condition
the paper must adopt; see docs/DESIGN-completeness-subtyping.md §9.0.

### RESOLVED (2026-07-30) — the repair LANDED

`fa_rsubst_var` **and** `fa_flexfree` were added to `flex_apart`, and
`fa_topholeg_t` was deleted (with `fa_rsubst_var` present it was the only way a
guard could hold at a ∀◈ that is neither clean nor flex-free, and it produced a
"∀◈-stack over a Δρ-variable" that no consumer can use).  Both witnesses are
now shielded; `cex/cex_p7_shield_arrow.v` became the regression test
`cex/regr_p7_shield_arrow.v`.  The measured cost above is what it actually
cost.  See docs/DESIGN-completeness-subtyping.md §10.6.

⚠️ **The authors still have to adopt the reshaped `flex_apart`** — it is
P6-Cv's repair premise, so the paper's side condition changes shape.  What
changed for a reader: the two guard predicates now have IDENTICAL base rows
(clean / flex-free / ρ-var) and differ ONLY in their descent, because
consistency MATCHES quantifiers while subtyping INSTANTIATES them.

---

## FALSE (machine-checked, 2026-07-30) — the property `subtyping-proofs.tex:3243` marks with its own TODO: "when input `P_0` is a concrete type, the RHS of algo subtyping is always `P_0`"

The paper records, inside P7b's Sub-ForallR case:

> % WT: We may have the property that, in algo subtyping, when input P_0 is a
> % concrete type, RHS of subtyping is always P_0. TODO: optional: check this.
> % If yes, use this to simplify the proof.

**Checked, and it is false.**  Machine-checked witness:
`cex/cex_p7_concrete_rhs.v` (`p7_concrete_rhs_is_false`, Qed,
axiom-free).

At `N = TY` the mode constraint `skmod[TY]{P_0}{TC}` forces `P_0` to be a TYPE
embedded into the skeleton sort — that IS the paper's "concrete type", and it
is the only place the concreteness comes from.  But consistency's `FlexL` row
returns the **subject**, not the input skeleton:

    Θ ⊢[P_0] α̂ ∼ α̂ ⊣ Θ'          (α̂ ≔ P_0 recorded in Θ')

and algorithmic `Arrow` copies that output into its own.  So already at

    P_0 = unit → unit        (concrete — and entirely flexible-FREE)
    P   = α̂ → unit
    RHS = α̂ → unit  ≠  P_0

The witness carries `Θ_0` well-formed and `skmod[TY]{P_0}{FN TC}` as premises,
so no missing side condition explains it away; and reading "concrete" as also
excluding flexible variables does not help, because the flexible is on the
SUBJECT side, which the property does not constrain.

**This does NOT break either case that uses it.**  The paper's own text for
both already argues via the EQUIVALENCE — "`P'_0` is equivalent to `P_0`"
(:3181) and "`P'_0` and `P_1` are equivalent through `Q`" (:3238) — and the
equivalence is exactly what the run's output context supplies (`α̂ ≔ unit`
here).  What is refuted is only the proposed SIMPLIFICATION.  Recommendation
to the authors: drop the TODO, or restate it as the equivalence

    θ_1(RHS) = θ_1 P_0

which is what the mechanization proves, for BOTH judgments
(`frost/algo/prop_sub_concrete_rhs.v`, Qed + axiom-free):
`a_consis_concrete_output_equiv` and `a_sub_concrete_output_equiv` each give
`Θ_1 ⊢ P_0 ≡ˢ P'_0` for a ghost-free (concrete) `P_0`, in the OUTPUT context —
which is where the definition the equivalence uses was recorded.

Worth reporting: neither needed a new induction.  Both soundness theorems
(`a_consis_sound`, `a_sub_sound`) already export the output's REFINEMENT
from the input skeleton, and refinement out of a ghost-free source can only
unfold definitions — every ghost row of refinement demands a ghost on the left,
and the two flexible-lookup rows ARE the equivalence's `flex_def` rule, one on
each side.  (Note also that algorithmic
`Check` already outputs `P_0` on the nose, since the paper's own
`aconsis{Θ_0}{P}{P_0}{Θ_1}` abbreviation suppresses the consistency output —
so the syntactic reading is only ever needed for the OTHER rows, which are
exactly the ones that refute it.)

---

## ~~FALSE~~ **NOT A GAP — RETRACTED (2026-07-30)** — `thm:complete-subtyping`'s Sub-Infer / Sub-UnivGhostR precision step (:3134, :3288)

⚠️ **This entry originally claimed the paper's step was false.  That was a
MISREADING of the paper and is withdrawn.**  Kept because the reasoning under it
is still worth having, and because the misreading is instructive.

The paper writes, at Sub-Infer:

> The consistency premise, together with `⌊S⌋ = P` and
> \Cref{thm:complete-consistency}, gives `Θ ⊢ precise{θP}{Q}`.

I read that as "read a precision off the consistency premise" and refuted THAT
(`cex/cex_p7_sskl_precise.v`).  But the paper says what it means: it
invokes **thm:complete-consistency** — a theorem, already mechanized as
`a_consis_complete` — on the consistency problem `(Θ_0; □; P)`, and takes
the precision from its conclusion.  That route is sound.

**The only thing it needs is small and now proved** (`a_consis_hole_p0_output`,
Qed): at `P_0 = □` the algorithmic consistency OUTPUT is the SUBJECT.  Of the
fifteen consistency rules only three admit `P_0 = □` — Ghost (whose subject is
`□`), GhostR, and FlexL — and each returns its own subject.  UnivGhost2 is the
only rule that does not fix `P_0`'s shape, and its `guarded{P_0}` premise
excludes the ghost.  So thm:complete-consistency's precision, which is about the
run's output, IS a precision about `P`.

**What survives, and is still worth the authors' attention.**  The refuted
statement is a tempting SHORTCUT — proving the precision directly from the
consistency premise, without going through completeness.  It fails, and the
reason is structural rather than incidental: consistency opens a ∀ into the
CONTEXT while refinement (hence precision) opens it into the ghost-fill scope
`Δ`, so a consistency derivation may fill a ghost with a binder that precision
cannot see.  Witness: `∀◇.` against `∀α. α` over the empty context.  Anyone
tempted by the shortcut — in the paper or in a mechanization — should know it is
closed off.

---

## MECH-PREMISE ~~(found 2026-07-30)~~ **RESOLVED same day — option (c) IMPLEMENTED** — the root-level **third** solution condition made `Sub-UnivGhostR` vacuous (and truncated ForallL/ForallR)

**RESOLUTION (2026-07-30).**  Option (c) below — the leaf-level formulation —
is now IMPLEMENTED: the motive's join is the LEAF-VALID mirror
`ad_pat_sub_gv` (def_decl_algo_sub_hyg.v), which carries the subject
refinement exactly on the three consistency-leaf rows (`__infer`, `__check`,
`__univ_ghost_r` — the last at the STRIPPED counterpart), and the root-level
third premise is GONE from `sub_complete_concl` / `sub_flex_complete_concl`.
All previously closed rows re-closed, and `a_sub_complete_univ_ghost_r` is
now a REAL proof (algorithmic `UnivGhostR` + the `□`-P0 precision core + a
`∀◇`-wrap), Qed + axiom-free.  The two cex files remain as historical
witnesses of why the root formulation was wrong.  What remains for the
AUTHORS is the PAPER-side decision recorded at the end of this entry
(the paper's own statements are still gapped as described).  Known future
obligation on the mech side: the P5 precision-substitution and the `_n→_g`
freshening kits must eventually be transported to `ad_pat_sub_gv` (needed by
the ForallL / ForallR rows of P7b); at the leaves this adds one new fact —
precision-substitution must preserve the leaf's subject refinement.

**The original entry follows.**  This was the MECHANIZATION's own premise,
not the paper's — but the authors need it, because it decided what the
mechanized theorem covers.

The paper's generalized `thm:complete-subtyping`
(`subtyping-proofs.tex:3054-3074`) gives a solution TWO conditions:

    (join)     typsub^N_M[Ψ] Θ ⊢ syn(θS) ⊑ bid Q
    (P0-fill)  Θ ⊢ inh(θP_0) ⤳syn bid Q

`DESIGN-completeness-subtyping.md` §1 added a THIRD — the SUBJECT's own
refinement `Θ ⊢ᵣₚ θ⌊S⌋ ⊳ ⌊Q⌋` — on the ground that it is what SOUNDNESS
produces for every algorithmic output, so that the sound/complete pair still
characterizes the algorithm exactly.

**That ground holds for consistency and fails for subtyping.**
`a_consis_sound` really does export `Θ_1 ⊢ᵣₚ P ⊳ P'`.  `a_sub_sound`
exports NO such conjunct — and it cannot, because algorithmic `UnivGhostR`
outputs `∀◇.P` from the input `P`, while refinement has no rule putting a `∀◇`
on the RIGHT of a non-ghost left-hand side.

**Consequence, machine-checked** (`cex/cex_p7_univ_ghost_r_vacuous.v`,
Qed + axiom-free, and `ad_refine_pskl_f_tophole_r_shape` in
`prop_sub_complete_thm.v`): declarative `Sub-UnivGhostR` has a GUARDED subject
and the counterpart `∀◇.Q_0`, so the third condition reads
`θ⌊S⌋ ⊳ ∀◇.⌊Q_0⌋` with a guarded left — underivable.  The row's case of P7b is
therefore closed BY CONTRADICTION (`a_sub_complete_univ_ghost_r`, Qed), and the
mechanized theorem says nothing about the solutions that row describes.  §2 of
the cex file exhibits the smallest configuration where the paper's two
conditions DO hold (`Θ = ·`, `θ = ι`, subject `unit`, counterpart `∀◇.unit`),
so the exclusion is a real loss of coverage, not a vacuity that was there
anyway.

**The truncation is NOT confined to the ghost row — machine-checked
(2026-07-30, `cex/cex_p7_third_premise_forall.v`, Qed +
axiom-free).**  The third condition is a LOCKSTEP relation —
`ad_refine_pskl` descends both sides together, so it can hold only when
subject and counterpart agree in shape (modulo ghosts on the LEFT and
flexible definitions) — while `Sub-ForallL` strips a ∀ from the subject and
`Sub-ForallR` adds one to the counterpart.  Both files' configurations
satisfy the paper's two conditions, are well formed and mode-compatible, and
fail the third:

- `∀a.a ⩽ unit` (ForallL — the INSTANTIATION subtyping exists for): the
  third condition reads `∀a.a ⊳ unit`, underivable;
- `unit ⩽ ∀a.unit` (ForallR — checking a guarded subject against a ∀): it
  reads `unit ⊳ ∀a.unit`, underivable.

So the mechanized theorem is close to content-free on TY-mode subtyping: it
covers only solutions whose two sides already agree at every head.  **Why
consistency does not have this problem**: `ad_pat_consis` is itself lockstep
(every ∀-inh-counterpart row — `__forall_inh_tagged` / `__forall_inh_untagged`
/ `__tophole_inh` — requires a ∀ or a ghost subject), so on consistency the
paper's own augmented third condition excludes nothing the join doesn't
already exclude at the heads; its one contribution there is the no-capture
discipline on hole fills, which is exactly what it was added for.  Subtyping's
`ForallL` / `ForallR` / `UnivGhostR` break lockstep — that is their job — so
importing consistency's condition verbatim cuts exactly the solutions those
rules create.

**The decision the authors must make.** Either

- (a) drop the third condition for subtyping, and give `Sub-Infer` /
  `Sub-Check` the subject refinement their `thm:complete-consistency` call
  needs some other way; or
- (b) keep it, and state the theorem as not covering head-disagreeing
  solutions (this now means: not covering ForallL instantiation and ForallR
  generalisation — i.e. most of the relation); or
- (c) RECOMMENDED — move the condition from the ROOT to the CONSISTENCY
  LEAVES of the declarative derivation: require, for each `Sub-Infer` /
  `Sub-Check` / `Sub-UnivGhostR` leaf of the join derivation, the subject
  refinement `θ⌊S'⌋ ⊳ ⌊Q'⌋` at THAT leaf's subject/counterpart pair (for
  `UnivGhostR`, at the STRIPPED counterpart `Q_0`).  This is precisely the
  data the `thm:complete-consistency` invocations consume, it is satisfied
  in all three counterexample configurations (each leaf there is
  `unit ⊳ unit`), and it still excludes the capture configuration
  (`(P_0=◇, P=∀X.◇, Q=∀X.X)`: its Infer leaf demands `∀X.◇ ⊳ ∀X.X`, which
  refinement's binder discipline forbids).  Mechanically: either a
  leaf-augmented variant of `ad_pat_sub_g` (subject-refinement premises on
  `__infer` / `__check` / `__univ_ghost_r` only) or a mirror predicate over
  the derivation; the cost is transporting it through the P5
  precision-substitution and the renaming/freshening kits.

Note the third condition is genuinely LOAD-BEARING for the leaf rows: it is
literally `thm:complete-consistency`'s own third premise at the consistency
subproblem `(Θ_0; □; P)`, which is what `Sub-Infer` and `Sub-Check` invoke.  So
(a) is not free — and (a) is in fact impossible as a plain derivation: the
capture configuration passes join + fill, so no proof can conjure the leaf
refinement from the two paper conditions.  A restricted derivation lemma
(join ⇒ leaf refinement) IS plausible for HOLE-FREE subjects — the TY-mode
call sites — which would let the paper keep its 2-condition statement for
TY-mode subtyping and require leaf-validity only for SK.

**Consequence for the paper's own statements.**  The paper's top-level
`thm:complete-consistency` (2-condition, full-algo-spec.tex:1473-1546) is
FALSE as literally stated — the augmented 3-condition version proved in
consistency-proofs.tex:2230-2242 is the true theorem, and the 2-condition
Definition is never rederivable from it (same capture configuration).  The
`thm:complete-subtyping` cases that invoke `thm:complete-consistency`
(`Sub-Infer` :3134, `Sub-Check` :3167, `Sub-UnivGhostR` :3282, `Sub-Arrow`
:3334) therefore invoke a false statement; under the true (augmented) one
they need the leaf refinement of (c) at each invocation, which the paper's
2-condition solution notion does not supply.

## WF-SIDE-CONDITION (found 2026-07-30) — P7b's `Sub-Check` needs the COUNTERPART well-formed in the solution context

Registered also in [WF-SIDE-CONDITIONS.md](WF-SIDE-CONDITIONS.md).  The
`Sub-Check` case moves its precision from `θ` to the package's `ζ`, and the
composition step is `ad_refine_syn_trans` — which refinement only admits under
the paper's external well-formedness of the RESULT (refinement is not
transitive outright; `cex_refine_not_transitive.v`).  At `P_0 = □` that
well-formedness is free (`ad_refine_syn_hole_l_target_wf`: only `__hole` and
`__flex_r` have a ghost source, and both carry it).  At `Sub-Check` it is not,
so `a_sub_complete_check` takes `Θ ⨟ ∅ ⊢ P_B` as a hypothesis.  It is the
paper's usual "all inputs are well-formed", and the P7 bundle will have to
carry it on the motive.

`a_sub_complete_check` also takes `guarded{P_0}`: the DECLARATIVE `Check` row
does not pin `P_0`'s shape, but the ALGORITHM dispatches on it — a `∀` `P_0` is
`ForallR`, not `Check`.  That is the paper's own case split, not a new
hypothesis.

## PROSE-COMPLETION — `lemma:constraint-collection-stable-substitution` needs its Barendregt condition stated (2026-08-01)

The paper's constraint-collection stability lemma (algorithmic-proofs
tex:504-520) says: substituting an `α`-free `Q` for `β ≠ α` into the SOURCE
leaves the collected `Ξ ⨾ 𝒞` unchanged.  Under the Barendregt convention
that is correct.  Stated without it, it is **false**, and the mechanization
has the witness (`cex/cex_look_subst_stable_leak.v`, Qed,
axiom-free):

    Θ ⊢ ∀. (α → β)   ∼[α]   ∀. (0 → 0)   ⤳   ·   ⨾   [ β₀ ≐ ]

by `LE-ForallInh` at `β₀` and then `LE-Arrow` (`LE-Var` left, `LE-Absent`
right).  All five look ∀ rules let their binder ESCAPE into the outputs —
the reference implementation `unbind`s and discards the name in every one
(`constr_collect_eq` type.ml:579-583, :595-598, :610-613;
`constr_collect_sub` :668-672, :685-688; neither function ever calls
`bind_var`) — so `β₀` really does appear in `𝒞`.  Substituting `Q := β₀` for
`β` puts that binder FREE in the source, and now every binder the rule may
pick avoids it, so the collected constraint is `δ ≐` for some `δ ≠ β₀`.

Nothing about the paper's rules or its proof needs changing; what a
mechanization must add is the Barendregt condition as an explicit premise.
The smallest one that the ∀ rules' own side conditions then supply is

    ftv Q ⊆ {α} ∪ ftv(Θ)

("the substituted skeleton introduces no name the judgment does not already
mention").  It names the CONTEXT rather than the input skeletons because
only the context is monotone as the induction descends: an arrow row shrinks
the skeletons, a binder row grows the context.

The same phenomenon makes the mech's renaming lemmas carry an OUTPUT
freshness premise (`α1 ∉ dom Ξ ∪ ftv 𝒞`): a binder that escaped into the
outputs cannot be moved without changing them, so a rename target must
simply differ from it.  See DESIGN.md §4.3, "The look cluster".

**Addendum (2026-08-01).** The Barendregt condition above cannot always be
stated as the context bound `ftv Q ⊆ {α} ∪ ftv(Θ)`.  Where the substituted
skeleton is a ForallL node's GUESS, its variables include the extract's
freshly generated block `Ξ`, and `Ξ` is produced *after* the collection run,
by an independent generator at the same context — so the run's binders have
no reason to avoid it.  Two independent "fresh" generators at one context are
kept apart by the implementation's global counter (`incr counter`,
type.ml:563-565) and by the paper's Barendregt convention, but not by any
side condition a relational rule can carry.  A mechanization therefore needs
the stability lemma in a second, EXISTENTIAL-output form as well: the ∀ rows
re-pick their binders away from the substituted skeleton and return `Ξ ⨾ 𝒞`
up to a rigid renaming.  Nothing in the paper changes; this is a note about
what "by Barendregt" costs to discharge.

---

## ⛔ INCOMPLETE RULE SET (2026-08-03) — the flexible SUBTYPING walk has NO rule for a TERM-VARIABLE head

**Where.**  `fig:alg-subtyping`'s second box (the auxiliary judgment
`\atypsub[\N][\FN\M][P_0]{\Theta_0\mid\Xi}{\hat\alpha}{Q}{\Theta_1}`,
full-algo-spec.tex:883-912) has exactly five rules — `Flex-Solve`,
`Flex-Assign`, `Flex-Depend`, `Flex-Skip`, `Flex-SkipRigid`.  Every one of
them matches a *type*-variable entry (`\hat\beta`, `\hat\beta\assign\tau`,
`\beta`).  None matches a **term** entry `x : P`.

**Why that is a gap.**  The paper's algorithmic contexts *do* contain term
entries — `e ::= \alpha \mid x : P \mid \hat\alpha \mid \hat\alpha \assign
\tau` (algorithmic.tex:60-66) — and the paper's **twin** walk, the assignment
walk of `fig:alg-consistency`, *does* have the corresponding rule:

```
\inferrule*[Lab=\ulab{Assign-SkipTmVar}]
{ \mov{\Theta_0\mid\Xi}{\assignvar{\hat\alpha}{P}}{\Theta_1} }
{\mov{\Theta_0,x:Q\mid\Xi}{\assignvar{\hat\alpha}{P}}{\Theta_1,x:Q}}
```

(full-algo-spec.tex:1791; mechanized as `a_assign__skip_tm_var` /
`a_assign__skip_tm_skl`, algo/def_rules.v).  So the omission in the subtyping
box is almost certainly a typo rather than a design decision — but as printed
it makes the walk **stuck** whenever a term entry sits above the subject
`\hat\alpha`, and `thm:complete-subtyping` demands a run there.

Nothing in the theorem's problem definition (algorithmic.tex:1423-1436)
excludes the configuration: it asks only that `\Theta_0` be well formed and
`P_0`, `P` well formed in it, and well-formedness is perfectly happy to put a
term entry above a flexible variable (`a_wf_aenv__var` / `__var_typ`,
algo/def_rules.v:192-201).  The configuration is reachable in the real
algorithm too: checking a lambda against a guessed `\hat\alpha` splits it,
pushes `x : \hat\alpha_1`, and any later application-mode subtyping call whose
subject is a flexible declared *before* the lambda must walk past `x`.

**The third witness agrees with the paper, and therefore shares the gap.**
The reference implementation's `assign` has the case —

```ocaml
(* U-Assign-SkipTmVar *)
| ((BVar _ | Marker | Lock _) as hd) :: theta -> ...        (* type.ml:386-390 *)
```

— while `sub_flex` has no term-entry case at all and falls through to

```ocaml
| _ -> Errors.type_mismatch loc ~expected:(sk_of_mode m) ~got:(MFlex alpha0)
                                                            (* type.ml:1047-1050 *)
```

**The repair** is to add `Flex-SkipTmVar` in the paper's own idiom, mirroring
`Assign-SkipTmVar`:

```
\inferrule*[Lab=\silab{Flex-SkipTmVar}]
{ \atypsub[\N][\FN\M][P_0]{\Theta_0\mid\Xi}{\hat\alpha}{Q}{\Theta_1} }
{\atypsub[\N][\FN\M][P_0]{\Theta_0,x:Q'\mid\Xi}{\hat\alpha}{Q}{\Theta_1,x:Q'}}
```

**⭐⭐⭐ MACHINE-CHECKED, AND THE IMPLEMENTATION CRASHES ON AN ORDINARY
PROGRAM.**  `cex/cex_p7_flex_walk_tm_var.v`
(`complete_subtyping_false_at_a_term_variable_head`, Qed + axiom-free)
exhibits the smallest witness — `Θ0 = x : (), α̂`, `P_0 = ◇ → ◇`, `P = α̂`,
`N = SK`, `M = FN TI` — and checks all three halves: the PROBLEM side holds,
a SOLUTION exists (increase, join, fill, external wf — every hypothesis of
the completeness statement), and NO algorithmic run exists.  And the shape is
the ordinary one: `a_typing__abs` pushes the lambda binder ABOVE the
flexibles `a_guess_mono` just invented, and `a_typing__var` hands that very
flexible to subtyping at an FN mode when the variable is applied.  Against
the reference implementation:

```
$ cat t.mle
let f = fun x -> x 1
$ met.exe --debug t.mle
- I-Abs
-- I-App
--- PI-Int  ---- SI-UnivGhostR
--- I-Var
---- SI-FlexMono                          <- subtyping enters the walk
Fatal error: exception Failure("broom_flex_poly: should not happen")
```

`fun g -> fun y -> g y` and `fun g y -> g (g y)` crash identically.
`fun x -> x` is fine (no application, hence no FN-mode subtyping on the
flexible), and so is any version where the applied variable's type is
concrete (give it a `val` signature).  **The trigger is exactly "apply a lambda-bound variable
whose type is still an unsolved flexible".**  (The impl reaches `failwith`
rather than `Errors.type_mismatch` because its contexts also carry
`Marker` / `Lock` entries, which `assign` skips as `U-Assign-SkipOthers` and
`sub_flex` does not — the same omission, one entry sort further out than the
paper's `x : P`.)


⭐ **THE GAP IS EXACTLY "CHECKING WORKS, INFERENCE DOES NOT".**  The spec DOES
give these terms types — the same programs check fine against a signature,
because then `x`'s type is CONCRETE and no flexible reaches the walk:

| program | annotated (checking) | unannotated (inference) |
|---|---|---|
| `fun x -> x 1` at `(int -> int) -> int` | accepted | crash |
| `fun x -> x 1` at `forall b . [] ((int -> b) -> b)` | accepted (and usable at two result types) | crash |
| `fun g y -> g y` at `forall a b . [] ((a -> b) -> a -> b)` | accepted | crash |
| `fun x -> x` (no application) | accepted | accepted |

So the missing rule costs exactly the INFERENCE of any term that applies a
lambda-bound variable.

⚠️ **The right column is NOT the left one minus an annotation.**  The
declarative spec does not derive the `forall` in inference mode at all.
`\dtylab{Abs}` (full-decl-spec.tex:210) guesses the argument type in an
INHERITED position, `inh{A} -> bid{B}`, and the paper's own gloss says why
(declarative.tex:577-580): *"We require the argument type to be inherited to
avoid guessing quantifiers without restricting it to monotypes"*, and
(:621) *"our rule Abs allows monotypes to be guessed for arguments of lambda
abstractions"*.  So for `fun x -> x ()` inference derives

    (unit -> τ) -> τ        for each MONOTYPE τ

— an open family, no quantifier; there is no `Gen` rule anywhere in the
syntax-directed figure, and the `forall ᾱ` prefix is introduced ONLY by
`\dtylab{AbsCheck}`, in CHECKING mode.  The algorithm represents that family
by the unsolved flexible: `(unit -> γ̂) -> γ̂`, and optimality says every
solution is a MONOTYPE instantiation of it (`a_inc__flex` carries
`mono_ptyp τ`, algo/def_meta.v:211-215), so `γ̂` cannot be instantiated with a
polytype.  `forall b . (unit -> b) -> b` is a *different, stronger* statement
reachable only by annotation — the observable difference is that a checked
`ap` is usable at two result types while an inferred one is not
(`let id = fun x -> x` then `id 1` and `id "s"` is rejected).

**⭐ STATUS: REPAIRED IN THE MECHANIZATION (2026-08-03).**  The rules are added,
in the paper's own idiom, as verbatim mirrors of `Assign-SkipTmVar`:

```
                    Θ₀ ∣ Ξ  ⊢[N][FN M][P₀] α̂ ⩽ Q ⊣ Θ₁
  ──────────────────────────────────────────────────────────────── Flex-SkipTmVar
   Θ₀, x:Q' ∣ Ξ  ⊢[N][FN M][P₀] α̂ ⩽ Q ⊣ Θ₁, x:Q'
```

`a_sub_flex__skip_tm_var` / `__skip_tm_skl` (algo/def_rules.v) with decorated
mirrors on `a_subtag_flex` (algo/def_decorated.v) — the mech splits the
paper's single `x : P` entry into a type binding and a skeleton binding, hence
two rules for the paper's one.  All three mutual inductions over the
`a_sub` / `a_sub_flex` pair carry their two new cases: the soundness bundle
(prop_sub_sound.v), the decoration bundle (prop_soundness_sub.v), and
equivariance (prop_swap.v).  `make coq` green, admit-free, axiom-free.

⭐ **One thing worth telling the authors**: neither the new rules nor the twin
walk's `Assign-SkipTmVar` carries a freshness premise for `P₀`, and none is
needed — a term entry is never `a_binds_tvar`, so under `uniq` no free
variable of a well-formed `P₀` can be it, and `x ∉ ftv P₀` is DERIVED at each
consumer.

⭐ **FULLY CLOSED (2026-08-03): P7a's two completeness rows are `Qed` too.**
`a_sub_flex_complete_skip_tm_var` / `_skip_tm_skl`
(algo/prop_sub_complete_thm.v §(N)/§(O)).  `a_inc__var` / `a_inc__var_skl`
shrink the `a_inc` TARGET exactly as `a_inc__tvar` does, so each row is
`a_sub_flex_complete_skip_rigid`'s ⇓-truncation apparatus with the tvar pieces
swapped for the var ones (`a_inc_var_inv`, `a_inc_var_mid_strip_id`,
`a_inc_equiv_mid_insert_var`) plus ONE genuinely new obligation the rigid
entry does not have: the SEMANTIC MIDDLE `Θ' ⊢ A' ≡ᵗ κ A`, cribbed from the
consistency twin's `Assign-SkipTmVar` case (prop_consis_complete.v:5595-5690)
and read back through the junk swap with `msubst_ptyp_kswap`.  Both rows are
axiom-free.  The stop-gap `a_sub_flex_walkable Θ0` premise on P7c's
`sub_flex_complete_holds` is DELETED; the walk now dispatches a term-variable head like any
other head.

---

## ⚠️ PROOF-STEP (2026-08-03) — `thm:complete-subtyping`'s ForallL case: the "WLOG guarded `P_0`" step is a JOIN PERMUTATION, and it is the whole obligation

**This is NOT an unaddressed hole — the paper handles it in one sentence.**
`thm:complete-subtyping`'s ForallL case (subtyping-proofs.tex:3385-3387) opens

> Since declarative subtyping is congruent, we assume WLOG that
> $\guarded{P_0}\gor P_0=\Hole$; otherwise we apply \sublab{ForallR} first.

That sentence is exactly right, and it is exactly what a mechanization has to
pay for.  Recording it here so the cost is visible.

**Why the step is needed.**  The dispatcher is "invert the declarative
derivation, apply the matching algorithmic rule".  That correspondence fails
at ForallL:

* `\silab{ForallL}` fires when the **subject** is a `∀`, and carries the
  premise `\guarded{P_0} \gor P_0 = \Hole`;
* `\silab{ForallR}` fires when the **input** `P_0` is a `∀`
  (`a_sub__forall_r`, algo/def_rules.v:1013);
* `skmod[TY]{P_0}{TC}` is `P_0 = A` for an arbitrary **type** `A`
  (`a_ty_mode_compat__tc`), and a `∀`-type is a type.

So at `N = TY`, `M = TC` with **both** a `∀` subject and a `∀`-headed `P_0`,
the declarative derivation may end in ForallL while the algorithm has no
choice but ForallR — the two rules commute, and ForallL is blocked by its own
premise.

**What "apply ForallR first" costs mechanically.**  The algorithmic ForallR
premise runs at `open P_0 α` over `α, Θ_0`, so its IH needs the declarative
side at the *extended* context and at `open B α` where the counterpart is
`\inh{\forall\alpha.B}`.  The fill supplies that half (a `bskl_all_inh` source
refines only to a `bskl_all_inh` target — `ad_refine_syn_f_all_inh_l_shape`,
algo/prop_sub_complete_dispatch.v §8), but the JOIN does not: it is
ForallL-rooted.  The missing step is therefore a **join permutation** — push
the ForallL instantiation under the ForallR binder, i.e. from

    ad_pat_sub_gv (S n) TY TC Ψ Θ (∀^ε.R) (bskl_all_inh B)

extract the cofinite family

    ∀ α ∉ L, ad_pat_sub_gv n' TY TC Ψ (α, Θ) (∀^ε.R) (open B α)

that `a_sub_complete_forall_r` consumes.  This is the mechanical content of
"declarative subtyping is congruent"; the paper is entitled to it, but it is
not free.

**Status in the mechanization — ⭐ PAID (2026-08-03).**  The permutation is
`sub_gv_all_inh_forall_r_family` (algo/prop_sub_complete_dispatch.v §11),
proved by induction on the join: the ForallL chain must bottom out in
`__forall_r`, because `__check` is the only other TY/TC row that can carry a
`bskl_all_inh` target and its `guarded_pskl` premise refutes a `∀`-inh
counterpart.  Each ForallL step is re-applied under the new binder.  It needs
one companion, `ad_pat_sub_gv_fuel_weaken`, because the extraction returns the
family at whatever height it finds while `a_sub_complete_forall_r` wants it at
exactly `n`.  `sub_complete_all_inh_counterpart` then closes the excluded
configuration outright: **whenever the counterpart is `∀`-inh the row goes
through ForallR, whatever the join's last rule and whatever `P_0`.**

The single residual hypothesis of the assembled bundle
(`a_sub_complete_bundle_holds`, §12) is still `main_forall n`, but it now
carries only TASK 0's `sub_shield` supply — a MECH-INVENTED premise, not a
paper statement (its residual case is logged in
docs/DESIGN-completeness-subtyping.md, not here).  Nothing in this entry is a
defect in the paper's statement or proof.

## ⚠️⚠️ FALSE AS STATED — `lemma:complete-look` (Look completeness, subtyping-proofs.tex:2730), machine-checked

**Status: REAL, for the authors** (mech-side statement, but it is the
PAPER's lemma, not a mech-invented premise).  Witness:
`cex/probe_double_occ_run.v`, `p6l_look_completeness_fails`, Qed +
axiom-free.

At the double-occurrence configuration of `cex_p7_shield_double_occ.v` —

    Θ0 = f̂ ~ flex    P0 = (∀γ.γ→γ) → f̂    S = ∀^t.(□₀→□₀)    N = TY, M = FN(TC)
    guess ψa = ∀^e β.β→β     Ψa = {e}     κ = f̂ ↦ 1→1

**every premise of the lemma holds**: `Θ0 ⊢ P0` (`P0d_wf`), `skmod[N]{P0}{M}`
(`P0d_mode`), `erase S = P` , `inc[κ]{Θ0}{Θ}` (`inc_d`), the guess's tag
sorting `Θ ⊢^N tags{Ψa}{ψa}` (`ψd_tags`) with `Ψ = ·` disjoint from `Ψa`,
the declarative premise `typsub[N][M][Ψ,Ψa]{Θ}{(κS)[ψa/α]}{Q}`
(`join_premise_d`), and the fill `Θ ⊢ inh{κP0} fillsyn Q` (`fill_d`).

**The conclusion fails.**  The look/extract is DETERMINISTIC here
(`probe_extract_det`, uniform in every fresh name — the collapsed binder is
vacuous, so it swallows them): its only output is `Pa = ∀_.f̂`.  The lemma
demands `Θ ⊢ precise{κ Pa}{erase ψa}`, i.e. `∀_.(1→1) ⊑ ∀β.β→β` — refuted:
one arrow step leaves `1 ⊳ β`, and the only rule that could refine a unit
to a variable (`ad_refine_syn__flex_r`) demands a DEFINED flexible, while
`Θ0` carries an undefined one.

### ⭐⭐⭐ THE CAUSE, LOCALIZED TO ONE SOLVE ROW (2026-08-04)

`cex/probe_solve_flexr.v`, `run_exists_at_correct_instantiation`, Qed +
axiom-free.  (⚙ That file was SUPERSEDED by `cex/probe_flexr_repair.v` and
DELETED 2026-08-06 — see "WHERE THE RETRACTED FILES WENT" at the top; the
statement below is now the tail of `new_run_exists` there.)  **The algorithm is not missing machinery — it discards an answer
it has already computed.**  Hand ForallL the instantiation `∀β.β→β` (the
declarative guess `ψa` with its tag erased) and the run goes through, at the
very configuration where `probe_no_run` says none exists:

* DOMAIN — `(∀β.β→β) ∼ (∀γ.γ→γ)` by ForallInh at a fresh rigid, then Arrow of
  two Rigids;
* CODOMAIN — `∀β.β→β ⩽[TC] f̂` by ForallL, whose look takes LS-Check and then
  ⭐ **LE-FlexR**: facing a flexible payload it invents a FRESH flexible `α1̂`
  and emits `eq(α1̂)` rather than letting `f̂` overwrite anything;
* CONTINUATION — `α1̂→α1̂ ⩽[TC] f̂` by Check → FlexR → Assign-Depend →
  Assign-SolveM, setting `f̂ ≔ α1̂→α1̂`, which is MORE GENERAL than the
  declarative `κ f̂ = 1→1` (take `α1̂ ↦ 1`).

So every rule the run needs exists and works.  What the algorithm cannot do is
CHOOSE `∀β.β→β`, and the extract is deterministic there
(`probe_extract_det`), forced through

    SE-FlexR    (`a_solve_eq__flex_r`)    : P ∼ α̂ ⤳ α̂     -- DISCARDS P
    SE-VacuousR (`a_solve_eq__hole_r`)    : P ∼ ◇  ⤳ P     -- KEEPS P
    SS-Vacuous  (`a_solve_sub__vacuous`)  : P ≼[m] ◇ ⤳ P   -- KEEPS P

The look collects `[eq(∀γ.γ→γ); sub_tc(f̂)]`; `a_solve_cstr__eq` threads the
eq's yield into the sub-constraint; SS-ForallL opens β and SS-Check hands
`β→β ∼ f̂` to SE-FlexR, which replaces the accumulated pattern by the
flexible — and the close then re-binds a VACUOUS binder, `∀_.f̂`.

⭐ A raw flexible and a ghost are the SAME epistemic situation (nothing known
at that position), and the two rows treat the already-computed information
oppositely.  The look itself takes the other side: on the EQ side `LE-FlexR`
invents a fresh flexible instead of letting the payload's flexible win.  And
the case that makes returning `α̂` useful — pattern `= ◇`, where it lets the
guess SHARE the flexible instead of inventing a new one — is already covered
by SE-GhostL (`◇ ∼ Q ⤳ Q`), so the two readings differ only where the pattern
already carries information.

**Suggested repair, for the authors:** SE-FlexR (full-algo-spec.tex:1374)
should yield the accumulated pattern, the flexible being recorded in `Θ` by
the assignment that follows rather than in the solve's output.  ⚠️ NOT applied
in the mechanization — a paper rule is not changed silently.  What still needs
checking before applying it: subtyping SOUNDNESS and the P6-Sv / P6-Ss
statements under the changed row.  DESIGN §14.10a.

**Why it matters.**  This locates the gap in the PAPER's proof chain rather
than in the mech: `thm:complete-subtyping`'s ForallL case
(subtyping-proofs.tex:3371) has NO shield-like side condition — it invokes
exactly this lemma — so the mech's `sub_shield` is precisely the repair OF
THIS LEMMA (it is P6-L's premise), and the configuration refutes the
unrepaired statement directly.  Both this and `thm:complete-subtyping`
therefore need the same restriction on `P0`; whether the configuration is
typing-REACHABLE is open (DESIGN §14.9 states the question sharply), so the
likely repair is a reachability/payload side condition rather than a change
to the algorithm.  Cf. the already-registered falsity of P6-Sv
(`cex/cex_p6sv_forall_flex.v`), which is the same phenomenon one lemma
lower.

## RETRACTED (2026-08-03, same day): the source-level "incompleteness on programs" claim was WRONG — the declarative system rejects that program too

An earlier revision of this file claimed that

    arg  : (∀c. c → c) → 1
    pipe : ∀r. ((∀b. b → b) → r) → r
    test = pipe (λg. g arg)

separates the systems (declarative accepts, algorithm rejects) and hence
refutes `thm:complete-subtyping` ON PROGRAMS.  **That claim is WITHDRAWN.
The declarative system rejects it too** — the program is an instance of the
paper's own §2.9 limitations, and met.exe's rejection is CORRECT behaviour.
Nothing here goes to the authors.

### Why the declarative system rejects it (the TAG obligation)

The declarative ForallL (`d_sub__forall_l_untagged`) does not restrict its
instantiation `ph` to monotypes — but that is NOT the operative constraint,
and reading only for a `mono_ptyp` premise is what produced the false claim.
The operative constraint is the TAG discipline, i.e. the paper's *"never
guess polymorphism out of thin air"* principle:

* the rule runs its premise at `Ψ ∪ Ψ'` where `d_tags Ψ' ph` — so a `ph`
  containing a ∀ contributes a tag ε that the premise's derivation must
  PRODUCE;
* the ONLY rule in `d_consis` that puts a tag into Ψ is
  `d_consis__forall_inh_tagged`, whose counterpart must be `btyp_all_inh B`
  — an INHERITED ∀;
* `d_sub__infer` demands `Ψ [=] empty` at TI.

So a polytype instantiation must be PAID FOR by an inherited ∀ at that
position of the counterpart, and the counterpart is what the SKELETON
supplies.  In `pipe (λg. g arg)` the argument's skeleton is `⫯(◇ → ◇)`: it
carries no ∀ at `r`'s position, so `r := (∀c. c → c) → 1` is unpayable.
(`is_ttyp` also excludes ghosts, so no ghost-carrying instantiation evades
this.)  The needed instantiations of `pipe`'s `r` and `g`'s `b` are mutually
dependent, which is exactly the limitation below.

### The paper already documents this, twice (§2.9)

* *"Only flowing back and forth once"* — the third limitation — is this
  program structurally: for `f : ∀c d. (c → c → List d) → Int` applied to
  `g : ∀b. (∀a. a→a) → b → List b`, `g`'s skeleton guides `f` to instantiate
  `c`, and instantiating `b` needs that information to flow BACK, which
  \Calc allows only once.  The co-author's note: the program becomes
  typeable if `pipe`'s skeleton first flows INTO `λg. g arg` — i.e. exactly
  this extension.
* *"Ghosts are nameless"* — the second limitation — is the same defect in
  the skeleton `⫯(◇ → ◇)`: the ghosts lose the connection between the
  argument and result positions, so "the inherited information is too
  coarse" to license the polytype instantiation.

### What still stands (mech-side, unaffected)

The RULE-LEVEL result of `cex/probe_double_occ_run.v` is untouched and
remains machine-checked: at the configuration of
`cex_p7_shield_double_occ.v` no `a_sub` run exists (`probe_no_run`), the
P7b motive instance is false (`probe_motive_instance_false`), and
`main_forall` — the completeness assembly's one hypothesis — is refuted
(`probe_main_forall_false`).  ⭐ That configuration's declarative side DOES
pay its tag: `consis_d` discharges ε against a `bskl_all_inh` counterpart at
the arrow's DOMAIN, so `join_d` is a legitimate declarative solution there.
The mech-side consequence is unchanged — `a_sub_complete_bundle_holds` and
`a_sub_complete` are vacuous as stated.

### The question that is REOPENED

Whether that configuration is TYPING-REACHABLE is open again (the claim
that it is, is what is withdrawn here).  The sharpened form: the cex needs
BOTH

1. payload codomain = a raw `Θ0`-flexible — the algorithm has NO inherited
   information at that position, and
2. counterpart codomain = a concrete arrow, with the guess's tag paid at the
   DOMAIN by an inherited ∀ — the declarative side HAS the information.

These pull in opposite directions: the payload's flexible arises exactly
where inherited information is absent, while the counterpart records what is
available.  The failed program above is the instructive near-miss — it gets
(1) but its counterpart is a GHOST, so it loses (2), and the declarative
side rejects with it.  If the conjunction is unreachable, the theorem is
merely OVER-QUANTIFIED and the repair is a reachability side condition on
the payload (docs/HANDOFF-completeness-repair.md TASKS 2–3, which are
therefore back ON, not invalid).

### The methodological lesson (same species as the MODE confusion)

Before any "the declarative system accepts X" claim, enumerate ALL of its
side conditions, not the first plausible one.  Here I checked
`d_sub__forall_l_untagged` for a monotype restriction, found none, and
concluded instantiation was free — missing the tag obligation, which IS the
paper's ghost/haunting discipline.  ⭐ Cheap standing check: the paper's
§2.9 limitations are the authoritative list of what the declarative system
deliberately rejects; consult it before reporting any separation.  The
repro files `docs/repros/thm_complete_subtyping_reachable_*` are retained as
documentation of this limitation (BOTH systems reject the first; the control
and ablation show what restores acceptance), NOT as counterexamples.

## RETRACTED same day: the suspected thm:complete-subtyping refutation was a MODE confusion (2026-08-03)

An earlier revision claimed the closed pair `A = ∀b. b → b`,
`B = (∀c. c → c) → (1 → 1)` refutes `thm:complete-subtyping`.  **WITHDRAWN**
— the two probes ran the algorithm at the WRONG MODE and at every mode
probed the two systems AGREE:

* At **M = TC** (checking a variable against an annotation): the
  DECLARATIVE side rejects too — Sub-Arrow concludes only at `fn M`, so at
  TC an arrow subject goes Check → consistency, where the codomain copy of
  the ForallL guess must MATCH `1 → 1`, and a ∀ does not.  met.exe's
  rejection is correct behaviour
  (`..mode_tc_rejected_by_both.mle`, `..mode_tc_flexible_rejected_by_both.mle`).
* At **M = FN(TC)** — the mode of the machine-checked join `join_d`,
  reachable only from a real application — the implementation ACCEPTS
  (`..fn_tc_passes.mle`).

Any decl-vs-algo claim must pin the MODE first.

## ⭐⭐⭐ RESOLVED BY THE AUTHORS — `SolE-FlexR` repaired; and three findings ON the repair (2026-08-04)

The two refutations recorded above — `lemma:complete-look` (Lemma E.17) and
`thm:complete-subtyping` (Theorem 4.6) — were both traced to one row,

```
  SolE-FlexR    nonflex(P)  ⟹  solveeq P α̂ ⤳ α̂           (full-algo-spec.tex:1371)
```

which DISCARDS the pattern the collection has already accumulated
(`docs/refutations.tex`).  The authors accepted the diagnosis and proposed

```
  nonflex(P)      guess^TY(P) = (Ξ; P')
  ─────────────────────────────────────
        solveeq P α̂ ⤳ Ξ ⨾ P'
```

with the note *"Thread the fresh suffix Ξ through all constraint-solving
judgements, add it to Look's output suffix, and update the corresponding
specification and proofs."*  The mechanization is propagating it.  **Three
things the authors need to know about the repaired rule itself.**

### FINDING 1 — soundness of subtyping survives, and its STATEMENT does not move

`a_sub_sound` (prop_soundness_sub.v) is `Qed` and axiom-free under the
repaired row, with the *same statement*.  Every new obligation is absorbed
inside the proof out of well-formedness premises the theorem already had.
The one real obligation the repair creates — *a decoration of the guess is a
decoration of the source* (`dec_ext_guess_source`) — holds because `guess^TY`
only ever LOSES information, and the decorated system already had the row to
fire (`SEq-FlexR`), so no new decorated rule was needed.  **The repair costs
nothing at the soundness interface.**

### FINDING 2 — ⚠️ the repaired row OVERLAPS `SolE-GhostL`, and must exclude a GHOST subject

Under the OLD row the overlap at a ghost subject was harmless: `◇ ∼ α̂` gave
`α̂` by `SolE-GhostL` and `α̂` by `SolE-FlexR` — **the same answer**.  Under
the repair they DISAGREE: `guess^TY(◇)` invents a FRESH `α̂₁`, so FlexR
returns `α̂₁` where GhostL returns the target `α̂`, and the sharing that makes
the marker's solution land on `α̂` is lost.  (`refutations.tex` §"Suggested
repair" already observes that the useful `P = ◇` case "is already covered by
`SolE-GhostL`" — this is the same observation, now load-bearing.)

The reference implementation never takes that branch: `solve_eq` is an OCaml
**match**, and both ghost-subject rows — `Ghost, q -> q` (`SolE-GhostL`,
`type.ml:412`) and `UGhost p, q when is_guarded q` (`SolE-GhostGuarded`,
`:457`; note `is_guarded (MFlex _) = true`, `:21-23`) — come **strictly
before** `SolE-FlexR` (`:466`).  So there FlexR fires only on a
`TCon`/`TArr`/`TForA`/`TMod` subject.  A relational rule set has no match
order, so the exclusion has to be a premise:

```
  nonflex(P)     nonghost(P)     guess^TY(P) = (Ξ; P')
  ────────────────────────────────────────────────────
              solveeq P α̂ ⤳ Ξ ⨾ P'
```

`nonghost(P)` = P's head is neither `◇` nor `∀◇` (mech `nonghost_pskl`,
frost/def_shapes.v).  It costs completeness NOTHING — at `◇`, `SolE-GhostL`
is strictly *more* informative, and at `∀◇P₀`, `SolE-GhostGuarded` peels to
the same place — and it keeps TRUE the fact the paper uses silently in every
`P_i = □` subcase of the -var lemmas: *solving with the ghost subject
returns the target verbatim* (mech `a_solve_eq_hole_subject_inv`).
**Suggested action: state `nonflex` as excluding ghosts, or add `nonghost`,
in `fig:constraint-solving`.**

### FINDING 3 — the binder rows' witness must avoid `ftvar(Θ)`, not just `dom(Θ)`

Consequence of the repair, not of the paper: the solve used to generate NO
names, so its five binder rows could merely *avoid* their witness.  Now a
guess can fire below such a binder, and four of the five rows CLOSE over the
witness, so a generated name equal to it would be captured.  Two changes
follow, both forced:

1. the witness **enters the premise's context** (`(β : *) , Θ`), which is
   what makes "the generated block is apart from β" DERIVABLE rather than
   assumed — the same avoid-input discipline `guess^TY` and the `Look` rules
   already use;
2. the witness avoids **`ftvar(Θ)`**, not `dom(Θ)` — a flexible's PAYLOAD
   `α̂ ≔ τ` may mention an atom that is in no domain, and `dom` is therefore
   the wrong avoid-set for anything that touches the guess.  This is again
   exactly what `guess^TY`'s own ∀ row and every `Look` binder row already
   require.

Similarly the SIBLING-premise rows must **thread**: `SS-Arrow`, `SS-GhostLF`,
`SE-Arrow` and the constraint-list `eq` row run their second premise at
`Ξ₁, Θ` and output `Ξ₂, Ξ₁`.  Run both halves at `Θ` and the two blocks can
pick the SAME atom, silently conflating two independently-invented
flexibles.  (One global counter, never reused, is what the implementation
does.)

⚠️ NOT derivable, and inherited rather than new: `uniq Ξ`.  `guess^TY`'s own
arrow rule runs both halves at the same `Θ`, exactly as `LS-Arrow` does;
colliding blocks are filtered downstream by `Sub-ForallL`'s `uniq (Ξ, Θ₀)`.

### Status of the two refutations

Both are **retracted** — machine-checked, at the very configuration that
refuted them (`cex/probe_flexr_repair.v`, `Qed` + axiom-free):
`new_solve` (the solve yields `∀γ.γ→γ`, not the vacuous `∀_.f̂`),
`new_extract`, and `new_run_exists` (a full algorithmic run EXISTS) are the
direct negations of `probe_solve_det`, `probe_extract_det` and
`probe_no_run`.  The old files are retained as history with retraction
headers; their Coq text is at commit `d5f9169`.

⭕ **`main_forall` is OPEN again.** It was refuted BY the retracted probe, so
the hypothesis of `a_sub_complete_bundle_holds` is no longer known-false.
Re-deciding it is the pay-off the campaign is aiming at, since the mech's
`sub_shield` premise was invented as a repair of exactly the lemma that
configuration refuted.

---

## ⭐⭐ RULE-LEVEL SIDE CONDITIONS `thm:sound-type-inference` NEEDS (2026-08-06)

Closing theorem 2 (`a_typing_sound`, `frost/algo/prop_soundness_typing.v` §13,
Qed and axiom-free) forced **three** additions to `fig:alg-type-inference` and
**one** correction.  All four are one-line, INVERSION-only for every existing
consumer, and cleanly revertible; the benchmark derivations (`test/`) discharge
every one of them at `Ξ = ·`.  They join the two already recorded above:
`sd-App`'s fourth `≡ᵗ` premise and `a_split__flex`'s freshness.

### 1. The four CHECK rows DISCARD the pending suffix — and the paper's proof knows it

`AT-AbsCheck` and `AT-AbsAnnoCheck` (both the `∀`-peeling and the `→` rows)
return an output context that DROPS the suffix `Ξ` the body's run deposited,
exactly as the figure writes them.  `AP-*` keeps its suffix, which is why
`thm:sound-skeleton-inference` never met this.  The paper's own proof
discharges the mismatch with `lemma:suffix-erasure`, *"since all variables in
Ξ do not appear in `inh{B}`"* — i.e. it ASSUMES two facts no rule states:

1. **`uniq (Ξ, Θ)`** — the run's new names avoid the input context.  This is
   verbatim the premise `Sub-ForallR` already carries for its own discarded
   suffix, and `Sub-ForallL` for the extract's.
2. **`Ξ` does not occur in the RESULT type.**

⛔ Neither is derivable.  A scoping theorem cannot supply (2): at the
`∀`-peeling rows the body's own result may legitimately mention flexibles the
body created, and nothing in the rule says those flexibles were re-deposited
BELOW the discarded prefix.  (Positionally they always are — the assignment
walk re-inserts a solved flexible at the solved variable's position — but that
is a property of the SOLVER's placement, several judgements away, not
something `AT-AbsCheck` can see.)

⚙ With them, the mechanization gets both halves it owes: `lemma:suffix-erasure`
for `ad_sd_typing` (`algo/prop_suffix_erase.v`) and the same strip for the
information increase (`a_isub_strip_tvar_mid` / the new
`a_isub_strip_var_typ_mid`), whose ⊴-obligation also has to lose `Ξ`.

**Suggested action:** state both on the four rules, or say in prose that the
suffix returned by a checking body is fresh for the result.

### 2. `AT-Abs` must filter `guess^TY`'s block: `uniq (ᾱ, Θ₁)`

`guess^TY`'s ARROW row runs both halves at the same `Θ`, so two
independently-invented blocks can pick the same atom and **`uniq ᾱ` is not
derivable** — this registry already records the same fact for the collection
walk ("two independent generators", above), where it is filtered downstream by
`Sub-ForallL`'s `uniq (Ξ, Θ₀)`.  `AT-Abs` is the other consumer: it puts the
block INTO the context, so without the filter the body's premise runs at a
context that is not well-formed, and the soundness proof has no induction
hypothesis to appeal to.  Same premise, same idiom.

### 3. `AT-AbsAnnoCheck`'s result domain is the SPLIT's `A'`, not the annotation

The rule (`algorithmic.tex:296-303`, currently commented out) reads

```
  Θ₀,ᾱ ⊢ split(A₀) = A' → B ⊣ Θ₁,ᾱ     Θ₁,ᾱ ⊢ A' ∼ A ⊣ Θ₂,ᾱ
  Θ₂,ᾱ,x:A ⊢[TC][B] M ⦂ B ⊣ Θ₃,ᾱ,x:A,Ξ
  ───────────────────────────────────────────────────────────
  Θ₀ ⊢[TC][∀ᾱ.A₀] λx^A.M ⦂ ∀ᾱ.A → B ⊣ Θ₃
```

Its consistency is oriented `A' ∼ A` — **subject the split's domain, input the
annotation** — the reverse of `AT-AbsAnno`'s `A ∼ P`.  The two cannot both
stand with the result `A → B`: soundness then owes `inh⌈A'⌉ ⊳ ⌈A⌉`, while a
consistency run transports the OTHER way (`inh⌈A⌉ ⊳` a colouring of `A'`), and
refinement is neither symmetric nor transitive
(`cex/cex_refine_not_transitive.v`).

`A' → B` resolves it, and is independently the right answer:

- the un-annotated `AT-AbsCheck` already returns the SPLIT's domain;
- it is exactly what the appendix's `≡ᵗ` premise on `sd-AbsAnnoCheck` is FOR
  ("the binding keeps the written annotation `A`; the conclusion's domain is
  any Θ-equivalent `A'`") — with `A → B` that premise is dead weight, with
  `A' → B` it is discharged by reading the consistency run as `Θ₂ ⊢ A ≡ᵗ A'`
  (`a_consis_chk_tyequiv`, prop_soundness_typing.v §3).

**Suggested action:** either change the conclusion to `∀ᾱ. A' → B`, or flip
the consistency to `A ∼ A'` and keep `A → B`.  The mechanization takes the
first (`a_typing__abs_anno_check_base`, algo/def_rules.v).

### 4. (already recorded) `sd-App`'s fourth `≡ᵗ`, and `a_split__flex`'s freshness

See the two entries above.

## ⭐⭐ WF-SIDE-CONDITION + PROSE-COMPLETION — the base rows of skeleton inference need the counterpart's wf, and the ALGORITHM's outputs must be proven well-formed to supply it (2026-08-07)

**Where.** `lemma:context-precision-skeleton` (proofs.tex, "Context precision
preserves skeleton inference") and `thm:complete-skeleton-inference`'s Sub
case; the declarative-in-algo skeleton-inference rules `P-Unit` / `P-Var` /
`P-Anno` (`ad_pat`'s base rows, algo_decl/def_typing.v).

**The gap.**  Both proofs invoke `lemma:precision-sub` at a base-term leaf,
whose external side condition (the paper's usual prose convention) is
well-formedness of the leaf's subtyping counterpart `bid{Q}`.  Nothing in the
rules supplies it:

- `ad_pat_sub_target_wf` gives only SCOPE — the leaf-valid join does not pin
  wf either (its leaf datum is a refinement, and refinement does not preserve
  wf: the capture configuration of `cex/cex_refine_not_transitive.v` has a
  wf source);
- it cannot be carried as a hypothesis of the lemma and propagated top-down:
  the descent dies at `P-App`, whose premise skeleton `P` and refined domain
  `Q1` are EXISTENTIAL in the rule — a first repair attempt put
  `Θ ⊢ P` on `P-App`, and the capture configuration sits inside `P-App`'s
  own refinement premise, so even that does not reach the function premise's
  domain.

**The repair** (WF-SIDE-CONDITIONS.md pattern, premise-on-the-rule): the
three base rows each carry `Θ ⊢ ⌊Q⌋` — the counterpart's disciplined wf —
which is exactly where the two proofs consume it, and nothing propagates.

**The soundness obligation this creates is a theorem about the ALGORITHM
the paper never states**: the outputs of the consistency and subtyping runs
are well-formed (`a_consis_output_wf` / `a_sub_output_wf`,
algo/prop_wf_preservation.v — both Qed, axiom-free).  The consistency induction is
where the content is: the run's `Δ1`/`Δ2` rigid-trackers and the Ghost /
GhostR rules' `Δ ∩ ftv` side conditions are PRECISELY what makes it go
through — the close-rows re-bind an opened rigid, which is sound only
because ghost fills avoid the tracked variables (the same asymmetry that
makes refinement non-transitive).  The paper's global "all types are
well-formed" convention silently assumes this result.

## ⭐⭐⭐ RULE REPAIRS on the four check rows of `TI-AbsCheck`/`TI-AbsAnnoCheck` — the figure's pinned body result is UNSATISFIABLE, and cofinite binder families break completeness (2026-08-08)

Found while proving `thm:complete-type-inference`.  Three related repairs to
the four suffix-discarding check rows (and, for uniformity, the two `AT-Abs`
rows), all now in `frost/algo/def_rules.v` with the mech following the
IMPLEMENTATION and the paper's own PROOF where they diverge from the figure.

### 1. The body premise's result must be FREE, and the conclusion's codomain is the BODY's result

The spec figure (full-algo-spec.tex:348-366) writes the `_base` body premise
as `Θ₁,ᾱ,x:A ⊢[TC;B] M ⦂ B ⊣ …` — input `B` (the split codomain), output
pinned to the SAME `B` — and concludes `∀ᾱ.A→B`.  The pin is unsatisfiable
whenever `B` is a flexible and the body is itself a lambda or an
application: a lambda checked against a flexible `β̂` concludes via its own
split with the arrow `γ̂→δ̂`, never with `β̂` itself, and an application
returns the function run's (possibly solved) codomain.  So e.g. checking
`λy.λz.e` against a flexible — reachable through `TI-App`'s argument checks
— has NO derivation under the figure's rules, while the reference
implementation accepts it: type.ml's I-AbsCheck never even looks at the
body's returned type (`let* _, m = finfer (Check b) m e` ... `end_rule (t, ...)`).
The paper's own completeness proof agrees: its AbsCheck case concludes
`⊢[TC;∀ᾱ.A'→B'] λx.M ⦂ ∀ᾱ.A'→B₁` with the BODY's `B₁` (proofs.tex, AbsCheck
subcase 1) — which is NOT an instance of the figure's rule.  The mech rules
now take a free `B1` in the body premise and conclude `A → B1`; the "`Ξ` not
in the result" side condition (entry `RULE-LEVEL SIDE CONDITIONS` §1,
2026-08-06) accordingly moves onto `B1`.

Soundness consequence: the split-refinement lemma generalizes to an
arbitrary refinement of the codomain painting
(`a_split_refines_gen`, algo/prop_soundness_typing.v) — at the flex row the
definition the split assigned is a monotype, so its consistency is an
equivalence and the refinement subject transports along it.

### 2. ALL SIX binder rows of `a_typing` are EXISTS-FRESH, not cofinite

Same repair, same reason, and same shape as `a_sub__forall_r`'s 2026-07-31
fix (entry `RESOLVED BY THE AUTHORS`, FINDING 3 area): the four check rows
DISCARD a suffix `Ξ` that may legitimately mention data specific to the one
binder the run actually used — the peeled `α` itself (an AbsAnnoCheck
body's consistency stage can solve a deposited flexible against it), or the
body's own result `B1` — so a COFINITE premise sharing `Ξ`/`B1`/the result
across a whole binder family is unsatisfiable in reachable configurations
and breaks completeness.  The locally-nameless rendering of the paper's
named rule therefore must be exists-fresh with a Barendregt side condition
(the paper's convention, prose-completed), not cofinite.  `AT-Abs` and
`AT-AbsAnno` were converted too, for uniformity.

Proof-machinery consequence: `thm:sound-type-inference` now receives ONE
binder instance and must rebuild the DECLARATIVE side's cofinite families
itself — term binders via the existing `ad_sd_typing_rename_tm`/wf-exp
renaming, type binders via NEW declarative-over-Θ renaming lemmas
(`ad_pat_rename_tvar` / `ad_sd_typing_rename_tvar` / `a_tyequiv_rename_tvar`,
algo/prop_rename_decl.v).

### 3. What did NOT change

The suffix-discard structure, the `uniq (Ξ ++ Θ)` Barendregt premise, the
`A' ∼ A` consistency orientation and the `A' → B1` result domain at
`AT-AbsAnnoCheck` (entry §3, 2026-08-06), and the declarative rules — all
stand.  The `_step` rows keep their result binder (`∀A` with the premise at
`A^α`); only the quantification of `α` changed.

## ⭐⭐⭐ `thm:complete-type-inference`, the AbsCheck case — THREE findings: the shape enumeration is incomplete, the subcase-2 metasubstitution extension is not well-typed, and two "we have" steps are theorems (2026-08-08)

Found while proving `thm:complete-type-inference` (proofs.tex:820-950).  The
theorem is now mechanized in full (`a_typing_complete`,
`algo/typing/prop_completeness_typing.v`, Qed and axiom-free), and the statement
stands unchanged; what follows are findings on its PROOF.

The case in question is `sd-AbsCheck`, whose paper proof opens

> We have $\Theta\vdash\inh{\theta A_p}\fillsyn\inh{\forall\ol\alpha.A\to B}$.
> By this refinement, the only possible shapes of $A_p$ are
> $\forall\ol\alpha.A'\to B'$ and $\forall\ol\alpha.\hat\alpha$.

and then splits into subcase 1 (the arrow — the identity split) and subcase 2
(the bare flexible).

### 1. The shape enumeration is INCOMPLETE — a RIGID variable has to be excluded separately, and a flexible's image is an arrow only UP TO flex-definition unfolding

`A_p` is a TYPE (`skmod[TY] A_p TC`), so after the `∀`s are peeled it can be
`1`, a variable, an arrow, or a `∀`.  `1` and `∀` die on the refinement
immediately.  A VARIABLE does not: the paper's `\hat\alpha` silently assumes
the variable is FLEXIBLE, and the rigid case has to be refuted, because the
split's flexible row is what the subcase is about and `a_split__flex` on a
rigid variable is absurd (`a_split_rigid_var_absurd`, `algo/typing/prop_rigidity.v`).
The refutation is short but is a lemma: a variable painting that refines to
an ARROW must be a *defined* flexible, since refinement's `__var` and
`__flex_r` rows both conclude at a VARIABLE target, so only `__flex_l` can
fire (`refine_var_arrow_flex_def`).  For a rigid `α` the metasubstitution is
the identity, and `binds α abind_tvar Θ` contradicts the `flex_mono_def`
binding `__flex_l` demands.

The flexible case needs a second observation the prose skips.  `θ\hat\alpha`
is a MONOTYPE (every metasubstitution image is), but it need not be a
syntactic arrow: it can be a chain of DEFINED flexibles that only bottoms out
in one.  So "θα̂ is equivalent to A→B" has to be produced, not read off.  The
mech proves it as `mono_refine_arrow_inv` — *a monotype painting that refines
to an arrow IS an arrow up to `≡ᵗ`* — by induction on the REFINEMENT, whose
`__flex_l` row unfolds the definition and recurses (the same shape as
`ad_pat_consis_mono_to_refine`).  It returns monotypes `τ1`, `τ2` with
`Θ ⊢ θα̂ ≡ᵗ τ1 → τ2` together with the two component refinements.

### 2. ⚠️ Subcase 2's step ⑯ extends the metasubstitution with `β̂ ↦ A` and `γ̂ ↦ B` — and those are NOT monotypes

The paper writes:

> By ⑫ and ⑬, we have a metasubstitution $\theta'$ extending $\theta$ with
> $\hat\beta\mapsto A$ and $\hat\gamma\mapsto B$ …

but a metasubstitution's images must be well-formed MONOTYPES in the target
— the paper's own prose side condition on `θ` (algorithmic.tex:123), and the
`mono` premise on the two flexible rows of the information-increase judgment.
`A` and `B` come from the DECLARATIVE arrow `∀ᾱ.A→B` and are arbitrary types,
so `θ' = θ, β̂↦A, γ̂↦B` is not an information increase as stated.

⭐ **The repair goes through the monotype decomposition of finding 1, and it
is the natural one**: extend with `β̂ ↦ τ1` and `γ̂ ↦ τ2` instead, where
`θα̂ ≡ᵗ τ1 → τ2` from `mono_refine_arrow_inv`.  Nothing downstream weakens:
the component refinements `inh⌈τ1⌉ ⊳ inh{A}` and `inh⌈τ2⌉ ⊳ inh{B}` are
refinements between paintings of PLAIN types, hence type EQUIVALENCES
(`ad_refine_syn_inh_tyequiv`), so `Θ ⊢ τ1 ≡ᵗ A` and `Θ ⊢ τ2 ≡ᵗ B` — which is
exactly what steps ⑮/⑭ use `β̂`'s and `γ̂`'s images for.  In other words the
paper's `A`/`B` may be read as "up to `≡ᵗ`", but then the witness has to be
the monotype, and the two equivalences become proof obligations rather than
definitional.

### 3. Subcase 2's ⑬ (the split RUN) and its scoping step are THEOREMS, not "we have"

> Assuming fresh $\hat\beta$ and $\hat\gamma$, we have
> ⑬ $\mov{\Theta_0,\ol\alpha}{\split[\hat\alpha][\hat\beta\to\hat\gamma]{}}{\Theta_1,\ol\alpha}$.

Splitting a bare flexible is not a syntactic step: `SplitFlex`'s premise is a
full CONSISTENCY run `α̂ ∼ (β̂ → γ̂)` in the extended context (which is what
solves `α̂`), so ⑬ must be BUILT, and its output context `Θ1` is that run's.
This is the one genuinely missing prerequisite of the theorem, mechanized as
**`a_split_complete_tc`** — *completeness of splitting at CHECK mode*.  (The
non-check modes need nothing: `skmod[TY]` leaves only the ghost and a
syntactic arrow there, so the split is the identity — the mech's
`a_split_complete`.  At TC the input is a TYPE painting, which is why the
flexible row is reachable at all.)  The run comes from
`thm:complete-consistency` at the reflexive declarative consistency of
`τ1 → τ2`, with the subject transported along `≡ᵗ`; the lemma returns the run
together with its own identity increase and a factoring witness, so the row
consumes it exactly like any other stage.

The same subcase then argues scoping in prose:

> Since $\theta\hat\alpha$ is equivalent to $A\to B$, and by definition of
> splitting $\hat\beta$ and $\hat\gamma$ are introduced immediately before the
> assignment for $\hat\alpha$, the components $A$ and $B$ are well-scoped at
> the positions of $\hat\beta$ and $\hat\gamma$ in $\Theta_1$.

and, throughout the four check rows, uses without proof that the DISCARDED
pending suffix `Ξ` does not occur in the run's result (the side condition
registered as `RULE-LEVEL SIDE CONDITIONS` §1, 2026-08-06, which the rules
now carry as a premise and which completeness has to DISCHARGE when it builds
those rows).  Both are consequences of one invariant, now proved in a
dedicated file `algo/typing/prop_scope.v`: a run's result is scoped in the region
at-or-below any marker of its input context, EXCEPT for atoms that are rigid
there.  It is a SCOPE-PROPAGATION statement over the subtyping and typing
towers plus a region walk over assignment/unification/consistency; naive
"core preservation" is FALSE at this granularity (both `a_sub_flex__assign`,
which substitutes the input skeleton, and the check `_base` rows, which reach
the flexible split at TC, are counterexamples recorded at the lemmas).  The
two `Ξ0 = nil` corollaries `a_typing_scope_tvar_nil` / `a_typing_scope_tm_nil`
are what the four check rows consume.

### 4. What did NOT change

The theorem's statement, the declarative rules, and the subcase-1 argument
all stand verbatim.  Subcase 1's steps ⑫/⑬ ("by the solution, `θA' ≡ᵗ A` and
`θB' ≡ᵗ B`") are read off the arrow refinement by `ad_refine_syn_inh_tyequiv`,
the same lemma `Freeze` uses.

## ⭐⭐⭐ MISSING ARGUMENT — the paper's central design principle is offered AGAINST an undecidability result, and the decidability it thereby claims is never discharged (filed 2026-08-14; found 2026-08-13, confirmed by the user)

**Status: GAP (missing theorem, not a broken step) — and the mechanization
has now DISCHARGED it for the subtyping walk** (see "Mechanized status"
below), so this entry is both the finding and the repair's location.

### The finding

The undecidability of impredicative polymorphic subtyping is the paper's own
stated motivation, cited twice as `\citep{chrzaszcz1998poly,tiuryn1996subtyping}`:

- `overview.tex:79` — "We cannot simply extend such systems with arbitrary
  implicit polymorphic instantiation as this is an undecidable problem";
- `introduction.tex:463` — "even implicit polymorphic instantiation itself
  (question ③) is undecidable".

The design principle offered in answer is `declarative.tex:856-860`:

> "A fundamental principle of \Calc is to **never guess polytypes out of
> thin air**.  Instead, we only guess polytypes that can be determined by
> inherited type information."

Read against the citations, this is an argument that the algorithm IS
decidable — the general problem is undecidable, *therefore* guessing is
restricted to what inherited information determines.  That argument is
nowhere discharged: the paper proves soundness and completeness, and a
derivation EXISTING is not a search TERMINATING.  A reader who reaches
`thm:complete-type-inference` having read `overview.tex:79` will read
decidability into it; nothing in the paper supports that reading.

### Mechanized status (frost/ext_algo/, 2026-08-13/14) — the argument, made and checked

The principle itself is now a theorem, in the exact currency the
termination argument needs (`frost/ext_algo/prop_termination.v`; all
axiom-free):

- `guess^TY` copies quantifiers and never invents one
  (`e_guess_mono_nall`): the guessed type carries no more `∀`s than the
  skeleton it was guessed from — the only inventing row maps a ghost to a
  fresh flexible, which is `∀`-free.
- Carried through SI-ForallL's whole extraction pipeline (collection →
  solving → `guess^N`): the instantiation `P₁` satisfies
  **`nall P₁ ≤ nall P₀`** — bounded by the INHERITED skeleton alone
  (`e_extract_nall`; the subject contributes nothing, because the
  collection only ever deposits counterpart fragments).  This is
  `declarative.tex:856-860` with "inherited type information" pinned to a
  single input of a single rule.
- The measure the principle buys: the subject's HEAD `∀`-chain strictly
  shrinks at every SI-ForallL (`e_extract_forall_l_hnall`), with the
  remaining lexicographic components the FN-depth of the mode (SI-Arrow),
  the pattern's `∀`-count (SI-ForallR), the defined-flexible count of the
  context (SI-Flex-Assign), and syntactic size.  ⚠️ Note for the authors:
  the naive "count `∀`s on the codomain spine" does NOT decrease — an
  eq-constraint can hand a counterpart fragment to the solving fold
  wholesale (SolE-GhostL), putting a `∀`-headed instantiation on the
  spine; the head-chain count is the one that works, and the case where
  the instantiation grafts onto the head chain is exactly the case where
  SI-ForallL's own guarded-or-ghost side condition forces the graft
  `∀`-free.
- Assembled: `e_sub_order_total` — the subtyping walk's search terminates
  on every locally-closed input whose context keeps monotype payloads.
  UNCONDITIONAL: the consistency block's own termination
  (`e_consis_order_total`) is proved by the measure (holes + undefined
  flexibles, then defined flexibles, then size) — holes are the only
  source of new flexibles (Assign-SolveM's guess block is exactly the
  pattern's holes), so any run that grows the context strictly consumed
  that fuel.  See docs/HANDOFF-extractable-algo-encoding.md §8b.

The paper could state this as a theorem ("the algorithm terminates on
well-formed inputs"), with the proof sketch: instantiations are bounded by
inherited information (the principle), inherited information is finite and
consumed (ForallR consumes the pattern's quantifiers, Arrow consumes the
mode, ForallL consumes the subject's head chain and cannot re-arm it), and
the flexible walks consume the context.

### ⭐⭐⭐ DISCHARGED (2026-08-19) — the decidability corollary is now Qed

Termination was only two thirds of the argument; the third is that the
runner's `None` MEANS something.  The completeness ladder is now finished —
campaign levels 1–8, every runner of `frost/ext_algo/` — and the corollary
is the two lines §5 of the hand-off predicted:

- `e_typing_dec` / `e_typing_dec_init`
  (`frost/ext_algo/prop_run_corollaries.v` §4, `Closed under the global
  context`, `README.v` §VI): at a locally-closed input skeleton and a
  locally-closed program, typability is DECIDED, and the decision procedure
  is the extracted function itself.

The three links, none re-derived there:

| link | file | what it gives |
|---|---|---|
| `e_typing_order_total` | def_typing_impl.v §2 | the search terminates, so `e_typing_run` is TOTAL and `None` is a REJECTION rather than exhausted fuel |
| `e_typing_run_sound` | def_typing_impl.v §5 | `Some r` is a derivation |
| `e_typing_run_complete` | prop_typing_complete.v §5 | a derivation makes it answer `Some` |

⚠️ **SCOPE, and it is part of the claim.**  What `None` refutes is a
derivation of the SUPPLY-THREADED relation `e_typing`, which is the relation
every rung of the ladder is stated over.  The POSITIVE branch composes all
the way down to the paper's own declarative judgement
(`e_typing_run_sound_infer` / `_check`); the NEGATIVE branch stops at
`e_typing`, because the converse of the bridge — `a_typing` ⟹ `e_typing` at
a covering supply — is not proved.  ⚙ That converse is not an oversight: a
derivation opens its binder wherever it likes and the threaded rules open at
the SUPPLY, so a structural induction on the `a_*` derivation needs its own
IH at a TRANSPOSED sub-derivation, which is not a subterm.  It is exactly the
obstruction that made the campaign quantify over `e_*` throughout
(docs/HANDOFF-extractable-algo-encoding.md §8c.3).  ⚙ It is now DESIGNED and
costed (§8c.24): induct on the e-side ORDER so the `a_*` derivation stays a
transposable hypothesis, and carry the `a_`-side blocks' freshness as a
premise the consumer discharges by pre-freshening.  120 rows across sixteen
judgements — its own campaign, not a corollary.
⚙ Nothing else is missing on the declarative side: `a_typing_complete` and
its closed-program corollaries are closed (README.v §III).

## ⭐ THE CONSISTENCY RULES ARE NON-DETERMINISTIC IN THEIR OUTPUT CONTEXT, and the implementation's rule ORDER is what resolves it (2026-08-16)

Machine-checked: `mechanization/cex/probe_consis_ghost_flex.v`
(five exhibits, assumptions-closed).

### The finding

`U-GhostR` and `U-FlexL` overlap, and their outputs differ.  At

    Θ ⊢[Δ1 | Δ2 | ◇]  α̂  ∼  ?  ⊣ ?          (α̂ an UNDEFINED flexible)

- `U-GhostR` needs only `Δ1 ∩ ftv(α̂) = ∅` (algorithmic.tex:782), which
  holds — `Δ1` collects the ∀-rows' RIGID openers, never a flexible —
  and answers `α̂ ⊣ Θ`, leaving the context alone.
- `U-FlexL` needs `\nonflex{P_0}` (:757).  `nonflex` rules out a
  flexible VARIABLE, not a hole, so it holds of `◇`, and the rule
  assigns `α̂ := ◇`.  Since `guess^TY(◇)` invents a fresh flexible, the
  output context is `Θ` with `α̂` SOLVED — `α̂ ↦ β̂`, `β̂` fresh.

So the same premises derive two different output contexts.  `U-Ghost`
and `U-FlexR` overlap the same way at the mirror node (pattern `α̂`,
subject `◇`).

Neither choice is wrong — the solution `α̂ ↦ β̂` with `β̂` fresh and
unconstrained is information-free, so the two answers are equi-general.
But they are not equal, and they are not related by a renaming: one
context has an entry the other does not.

### Why it matters

1. **`type.ml`'s clause order is load-bearing and unstated.**  The
   reference implementation matches the hole rows FIRST (`join_sk`,
   :143-262), so it always takes `U-GhostR` / `U-Ghost` and returns the
   more general answer.  The figure gives no priority, so a reader
   implementing the rules as written may solve the flexible instead and
   compute a strictly less general context.  Worth one sentence in the
   rule figure, or a `nonghost` side condition on `U-FlexL`/`U-FlexR`.

2. **It costs any "the implementation realizes the rules" proof a whole
   layer.**  `U-Arrow` runs its second premise at the first's OUTPUT
   context, so a completeness proof of the implementation against the
   rules must transport a derivation from the rules' output context to
   the implementation's.  Because the two differ by a solved-to-fresh
   flexible rather than by a renaming, that transport is a
   generalization (`κ ∷ Θ0 ⊑ Θ`) argument, not a bookkeeping one.  This
   is the obstacle recorded in
   `docs/HANDOFF-extractable-algo-encoding.md` §8c.10b.

### What is NOT affected

Soundness and completeness of consistency against the declarative
system (`a_consis_sound`, `a_consis_complete` / `complete_mu`) are
unaffected: they quantify over the derivations that exist, and the
optimality package is stated up to `⊑` precisely because the
algorithm's answers are only determined up to generality.
