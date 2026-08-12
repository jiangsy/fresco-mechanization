# Post-closure audit — deviations, redundancy, layout

Audited 2026-08-12, at `5e4ce58`, with every theorem closed.  Three questions:

1. are the current deviations from the paper's proofs **necessary**, and can the
   necessary ones be made cheaper?
2. what proof material is **redundant** and can go?
3. can the **file structure / naming / notations** be improved (paper-fidelity
   NOT required here)?

Method: mechanical name-and-reference index over all 78 non-generated `.v` files
(4094 top-level declarations), plus a read of every `[paper-gap]` site in the
four `def_*.v` rule files against `docs/PAPER-GAPS.md`.  Appendix:
[`AUDIT-dead-names.txt`](AUDIT-dead-names.txt).

## What has been DONE (2026-08-12, one commit, `make coq` green, 31/31 assumption reports clean)

Steps 2 and 3 of the suggested order below, plus the README indexing:

- **§3.1** — `README.v` §V now indexes the three terminal declarative results
  (`d_typing_order_irrel`, `d_shallow_sub_complete`,
  `mono_lambda_anno_redundant`), so `decl/prop_stability.v` and
  `decl/prop_shallow.v` are no longer compiled-but-invisible.  24 → 31 entries.
- **§2.3** — all ten duplicate top-level names resolved; the count is now **0**.
  Five were exact duplicates (deleted the copy in the file that already imported
  the other), five were different lemmas colliding (renamed).  Two facts turned
  out to exist **three** times: `a_wf_aenv_strip_prefix` (a `_local` copy, an
  `a_decls`-restricted one and a general one) and `a_wf_pskl_tophole_inv` (a
  strong form, a wf-only weak form, and an `_x` copy that existed only to escape
  the shadow).  Both now live once, in `algo/prop_flex.v`, which every user
  imports.
- **§2.1 (the clear orphans)** — `a_split_refines` (superseded by `_gen`), the
  four consumer-facing renaming corollaries in `prop_swap.v` §6, and five
  locally re-derived list/set utilities.  Zero-reference count 203 → 193.
- **§3.4 / §3.5** — the stale `}}t` delimiter in `CLAUDE.md` / `PROGRESS.md`,
  the `prop_etag*` paths in `PAPER-GAPS.md`, the `a_split_refines` citation at
  `algo/def_rules.v`, the false "`a_sub_complete_bundle_holds` is in `README.v`"
  claim, the `AGENTS.md` links, and the two dead design-spec references.  Every
  `[…](…)` link in `CLAUDE.md` now resolves.  `decl/prop_shallow.v`'s header
  described a `≤ₘ⟨n⟩` relation and a `d_shallow_sub_mono` that do not exist;
  it now describes what the file proves.

- **§3.2** — `decl/notations.v` is deleted.  It had **zero** `Notation`s: 35
  files imported it for two `Require Export`s, and all 35 already imported both
  targets directly.  The one live fact in its comment (why refinement's
  turnstile carries `ᵣ`) moved next to the relation in `decl/def_rules.v`.
- **§3.3** — the three `def_extra.v` files are renamed for what they hold:
  `frost/def_shapes.v`, `frost/decl/def_rules.v`, `frost/algo/def_rules.v`.
  120 files carried a reference.  ⚙ The historical `docs/DESIGN-*.md` and
  `docs/REPORT-remech-*.md` keep the old names on purpose — they are dated
  records with line-number citations, not current pointers.

- **§1.9** — `lc_exp e` is gone from `a_typing_complete` (statement and
  `README.v` entry): it follows from the theorem's own `ad_sd_typing` premise
  via `ad_sd_typing_wf_exp` + `a_wf_exp_lc`, which `prop_closed.v` was already
  computing by hand at the call site.

Not yet done: §1.1/§1.2 only — see the ⚠️ RE-SCOPE note under §1.1 below.

---

## Part 1 — deviations from the paper

The tree has exactly **seven** live deviation classes.  Four are necessary and
one is a correction of a paper bug; **two are avoidable**, and one of those two
is avoidable at a bounded cost.

### 1.1 ⭐ AVOIDABLE — the four check rows' premise (2) is now DERIVABLE

`algo/def_rules.v:1548,1561,1569,1584` — the four suffix-discarding check rows
of `a_typing` carry

```coq
(forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp B1)   (* (2) *)
```

When it was added (2026-08-06) the note read *"no scoping theorem local to the
rule supplies it, so it stays a premise"*.  **That is no longer true.**
`algo/typing/prop_scope.v` (2548 lines, closed 2026-08-08) proves
`a_typing_scope`, and its two corollaries `a_typing_scope_tvar_nil` /
`a_typing_scope_tm_nil` (`:2488`, `:2518`) derive *exactly premise (2)* from the
**run alone** plus wf of its input and output.  The premise has become a
restatement of a theorem the tree already has.

What blocks deleting it today is a **layering cycle**, not the mathematics:

- `prop_scope.v`'s own check-row cases still take the shortcut and consume the
  premise (`prop_scope.v:2262`, `exact (H2 γ Hc0 Hγ)`);
- `prop_soundness_typing.v` consumes it directly (`:2365`, `:2377`);
- the corollaries need the body run's **output well-formedness**, and for
  `a_typing` that is currently only available *inside* `a_typing_sound`.

⚠️ **RE-SCOPED 2026-08-12, after reading both proofs.**  The paragraph that
stood here proposed factoring `a_typing_output_wf` out of `a_typing_sound` into
`algo/prop_wf_preservation.v`, and called the cycle a layering accident.  Two
things are wrong with it.

**(a) `prop_scope.v` already imports `prop_soundness_typing.v`** (`:65`) and
calls `a_typing_sound` at seven sites.  The dependency runs
soundness → scope, not the other way, so soundness cannot reach the corollaries
without first removing that import.  ⚙ All seven sites destruct only the FIRST
THREE conjuncts (`Θ₀ ⊴ Θ₁`, `⊢ Θ₁`, `a_wf_ptyp Θ₁ A`) and never the declarative
existential — so the split is exactly along the line proposed, but it has to
happen *before* prop_scope, not after.

**(b) The wf conjunct itself needs the scope invariant.**  This is the real
obstruction.  In the check rows, `a_typing_sound` derives `a_wf_ptyp Θ₁ A` by
stripping `Ξ` off `a_wf_ptyp (Ξ ++ … ++ Θ₁) A` with `a_wf_ptyp_strip_prefix`
(`prop_soundness_typing.v:2372`), and the side condition it feeds that lemma IS
premise (2).  So an `a_typing_output_wf` that does not assume premise (2) cannot
be proved before `a_typing_scope`; and `a_typing_scope` needs output-wf.

**They have to become ONE mutual induction over `a_typing`**, concluding

```coq
Θ0 ⊴ Θ1  /\  {{ ⊢ Θ1 }}a  /\  a_wf_ptyp Θ1 A  /\  <typing_scope_concl …>
```

in `prop_scope.v`, whose check rows feed their own scope conjunct (at the nil
marker, exactly as the corollaries do) into the wf conjunct.  `prop_scope.v`
then drops its `prop_soundness_typing` import, and `a_typing_sound` imports
`prop_scope.v` and reads all four facts off it.

**Cost, honestly.**  It merges `a_typing_scope` (≈550 lines) with the wf third of
`a_typing_sound` (≈400), and every one of the twelve rows changes.  It is NOT
purely additional work — `a_typing_sound` currently proves those three conjuncts
inline and would stop, so the net line count is roughly flat — but it is a
restructuring of the two largest typing proofs, not the bounded extraction this
section originally described.  Worth doing; worth doing deliberately, on a
branch, not as part of a cleanup sweep.

Payoff: one of the four mech-only rule premises disappears, **and** the four
sites in `prop_completeness_typing.v` (`:2902`, `:3157`, `:3810`, `:4145`) that
exist only to discharge it when *building* those rows disappear with it.

### 1.2 ⭐ SAME REFACTOR — premise (1) `uniq (Ξ ++ Θ2)` also follows

Same four rows, `(1)`.  From the body run's output wf `⊢ Ξ ++ (x ~ A) ++ Θ3`
one gets `uniq Ξ` and `dom Ξ ∩ dom Θ3 = ∅`; the body run's `⊴` gives
`dom Θ2 ⊆ dom Θ3`; with `⊢ Θ2` that is `uniq (Ξ ++ Θ2)`.  So the *same*
`a_typing_output_wf` factoring retires **both** Barendregt premises, leaving the
four check rows with no mech-only side condition at all.

Recommendation: do 1.1 + 1.2 together.  It is the single highest-value change in
this audit — it removes half of the "FOUR side conditions the paper leaves to
prose" that `CLAUDE.md` and `README.v` currently advertise.

### 1.3 AVOIDABLE IN PRINCIPLE, NOT WORTH IT — `uniq (αs ++ Θ1)` on `AT-Abs`

`algo/def_rules.v:1476`.  The premise exists because `a_guess_mono__arrow`
(`:331`) runs both halves at the **same** `Θ`, so two independently invented
blocks may pick the same atom.  Every other generating judgement in the tree
threads instead (`a_sub`'s sibling premise `Ξ2 ++ Ξ1`, `def_extra.v:642`), and
threading `a_guess_mono` the same way

```coq
| a_guess_mono__arrow : forall Θ P Q Ξ1 Ξ2 A B,
    a_guess_mono Θ P Ξ1 A ->
    a_guess_mono (Ξ1 ++ Θ) Q Ξ2 B ->        (* threaded *)
    a_guess_mono Θ (pskl_arrow P Q) (Ξ2 ++ Ξ1) (ptyp_arrow A B)
```

would make `uniq` derivable and is *closer* to the implementation's global
counter, not further.  **But**: `a_guess_mono` has 316 occurrences across 19
files (`prop_flex.v` 42, `prop_completeness_typing.v` 37, `prop_solve_sub.v` 36,
…).  The premise costs one line; the faithful generator costs a tree-wide
re-proof.  **Keep the premise**; record the reason at the rule (it currently
says only that `uniq` is "NOT derivable", which is true of *this* `a_guess_mono`
and reads as a stronger claim than intended).

### 1.4 NECESSARY — `AT-AbsAnnoCheck`'s result domain `A'`

`algo/def_rules.v:1588`.  This is a **correction of the paper**, not a mech
artefact: the figure's `A → B` and its own consistency orientation `A' ∼ A`
cannot both hold (soundness would owe refinement symmetry).  Keep, and keep it
in PAPER-GAPS — it is a finding for the authors.

### 1.5 NECESSARY — the two prose presuppositions on the rules

`decl/def_rules.v:570,683`, `algo_decl/def_subtyping.v:70`,
`algo_decl/def_typing.v:95,180,258`.  These transcribe presuppositions the paper
*states* (declarative.tex:2074, :1595) and its figures then omit.  Carried on
the rules they make `d_pat` and `ad_pat` agree row for row, which is what closed
the declarative corollaries.  Necessary; and the alternative (hypotheses on
every lemma) is strictly more bookkeeping.

### 1.6 NECESSARY — the sort-discipline (`pskl_ghost_free`) premises

Eight sites in `algo/def_rules.v`.  They render the paper's *metavariable*
sorting (`A`/`B` type positions, `P`/`Q` skeleton positions), which a Coq
`Inductive` cannot express otherwise.  The three places where the paper sorts and
the mech deliberately does not are each argued in PAPER-GAPS.  No change.

### 1.7 NECESSARY BUT NON-UNIFORM — `a_pat`'s four cofinite binder rows

`algo/def_rules.v:1382`.  Still the one departure from the exists-fresh
discipline (`a_typing`'s six were converted at `7061d31`).  The note says
converting them would retire `prop_swap.v` §6's rename bridges.  **That is now
only half true**, and in a way that helps: three of the four bridges are already
dead (§2.1), so the block that conversion would retire is `a_pat_rename_tm`
alone.  The cost is unchanged — it re-opens theorems 1 and 3.  Verdict: leave it,
but correct the note, and delete the three dead bridges now (they are pure
carrying cost either way).

### 1.8 NOT A DEVIATION — the layer duplication is smaller than it looks

Worth recording, because it looks like the biggest redundancy in the tree and is
not.  `decl/` and `algo_decl/` duplicate **8 judgement `Inductive`s** (`d_pat`
/ `ad_pat`, `d_pat_sub` / `ad_pat_sub`, …) — but a name-level comparison shows
**zero** shared lemma suffixes between the 156 `d_*` and 346 `ad_*` lemmas: the
only overlap is the 13 rule-constructor names.  The two layers prove genuinely
different things (`decl/` the paper's declarative metatheory, `algo_decl/` the
precision/monotonicity machinery soundness and completeness need).  Collapsing
them — e.g. defining `d_X Γ := ad_X (denv_to_aenv Γ)` — would save the ~890
lines of `algo_decl/def_*.v` and much of `prop_conserv.v`, at the price of the
paper's declarative figure no longer being an `Inductive` a reader can match
line for line.  **Not recommended.**

### 1.9 Small: one redundant premise on a flagship theorem

`a_typing_complete` (and its `README.v` entry) takes `lc_exp e`.  It is
derivable from its own `{{ Θ ⊢ˢᵈ[M] e ⦂ B }}ad` premise, via
`ad_sd_typing_wf_exp` (`prop_soundness_typing.v:1686`) + `a_wf_exp_lc` (`:1729`)
— both already imported by `prop_completeness_typing.v`.  A one-line
`assert` at the top of the theorem removes it from the statement.

⚠️ The same does **not** hold for `a_pat_complete`: `ad_pat__anno`
(`algo_decl/def_typing.v:117`) has no premise about `e` at all, so no
`ad_pat_wf_exp` exists and `lc_exp e` is genuinely needed there.

---

## Part 2 — redundancy

### 2.1 203 zero-reference top-level names ≈ 3900 lines

Nothing in `frost/`, `README.v`, `cex/` or `test/` mentions them outside their
own declaration, and none is `Hint`-registered.  Full triaged list:
[`AUDIT-dead-names.txt`](AUDIT-dead-names.txt).  Distribution (top files):

| lines | file |
|---:|---|
| 392 | `algo/prop_swap.v` |
| 376 | `algo/consis/prop_consis_precise.v` |
| 307 | `algo/consis/prop_soundness_consis.v` |
| 219 | `algo/prop_suffix_erase.v` |
| 185 | `algo/sub/look/prop_rho_relation.v` |
| 180 | `algo/sub/look/prop_flex_apart.v` |
| 167 | `decl/prop_syntax_directed.v` |

⚠️ **Not all of it is deletable, and the distinction matters.**  Two kinds of
zero-reference name are *the point*, not waste:

- **Encoding-justification results.**  `prop_swap.v`'s eleven `*_no_loss`
  lemmas (`:1673`–`:1953`, ~250 lines) prove that the exists-fresh freshness
  premises lose no derivations — "the premise is an honest statement of the
  paper's Barendregt convention, not a strengthening of the algorithm".  They
  are consumed by *the reader*, not by a proof.
- **Terminal paper results.**  `decl/prop_shallow.v`'s
  `d_shallow_sub_complete` and `mono_lambda_anno_redundant`;
  `decl/prop_annotation.v`'s `freeze_no_infer`.

Both kinds should be **kept and indexed** (§3.1), not deleted.  Marked `[T]` in
the appendix.

The rest is genuinely orphan.  The clearest cases:

- `a_split_refines` (`typing/prop_soundness_typing.v:974`) — superseded by
  `a_split_refines_gen` (`:1069`), which is what the two real call sites use.
  ⚠️ `CLAUDE.md:34` still advertises `a_split_refines` as a prerequisite of
  `a_typing_sound`.  Delete the lemma, fix the doc.
- `a_sub_rename_tm` (`prop_swap.v:2555`), `a_consis_chk_rename_tm` (`:2618`),
  `a_split_rename_tm` (`:2665`) — three of the four "supporting bridges" for
  `a_pat_rename_tm`, dead since `a_typing`'s rows went exists-fresh.
- generic list/set utilities re-derived locally: `map_fst_combine` /
  `map_snd_combine` (`decl/prop_stability.v:328,336`), `app_mid_inv`
  (`consis/prop_consis_rename.v:718`), `eq_subset`
  (`decl/prop_syntax_directed.v:1164`), `lc_aenv_app` (`algo/prop_inc.v:110`).
- `decl/prop_annotation.v`'s `erase_lam_mono` kit (`:45`–`:95`) — orphan support
  for the `erase_lam_mono_typing` theorem that was aborted at `:97`.  Either
  re-prove the headline or drop the kit and keep `freeze_no_infer`.

### 2.2 Two files nothing imports

`decl/prop_stability.v` (754 lines) and `decl/prop_annotation.v` (120) have
**zero** consumers.  `prop_stability.v` is legitimately terminal
(`d_typing_order_irrel`); `prop_annotation.v` is the aborted-theorem residue
above.  Note `d_sub_prefix_spine_perm` (`prop_stability.v:460`) — cited in the
tag-hygiene write-up as one of CST's two call sites — is used only *within* its
own file; the dependency runs `prop_stability → prop_general_subsumption`, not
back.

### 2.3 Ten duplicate top-level names

`a_inc_equiv_lookup`, `a_wf_aenv_binds_def_mono`, `a_wf_aenv_strip_prefix`,
`a_wf_pskl_tophole_inv`, `ad_pat_sub_fuel_weaken`, `bskl_to_pskl_btyp_to_bskl`,
`bskl_to_pskl_subst_unit`, `guarded_pskl_subst`, `guarded_pskl_subst_var`,
`uskl_to_pskl_subst_unit`.  (Plus lngen's own `default_auto` /
`default_autorewrite`, which are generated and harmless.)

Per `CLAUDE.md`'s own rule this is a correctness hazard, not untidiness — one
added `Require Import` silently changes which one an unqualified `apply` means,
which has broken this build twice.  Three are clear merges into
`frost/prop_coercions.v` (`bskl_to_pskl_btyp_to_bskl`,
`bskl_to_pskl_subst_unit`, `uskl_to_pskl_subst_unit` — all four sites are the
coercion facts that file was created to own).  Note the tally is now **10**, not
the 39 recorded in `CLAUDE.md:352`.

---

## Part 3 — structure, naming, notations

### 3.1 `README.v` under-covers what the tree proves

28 entries (`CLAUDE.md:119` says 24).  Missing, and each is a claim someone will
want the `Print Assumptions` line for:

| result | file |
|---|---|
| `d_typing_order_irrel` (order irrelevance) | `decl/prop_stability.v:699` |
| `d_shallow_sub_complete` | `decl/prop_shallow.v:142` |
| `mono_lambda_anno_redundant` | `decl/prop_shallow.v:236` |
| `d_consis_sub_trans` (CST, paper B.3) | `decl/prop_general_subsumption.v` |
| `a_assign_sound` / `a_unify_sound` / `complete_mu` | `algo/consis/…` |
| `a_sub_complete_bundle_holds` | `algo/sub/prop_completeness_sub.v` |

The last is the sharpest: `CLAUDE.md:57` and `:139` both say it is "`Check`ed and
audited in `README.v`".  It is not in the file.

Separately, the eleven `*_no_loss` lemmas (§2.1) are the argument that the
encoding is admissible.  Suggest a short second index — `README.v` §V
"encoding justification", or a sibling `README-encoding.v` — so they are
`Print Assumptions`-checked rather than silently compiled.

### 3.2 `decl/notations.v` is an empty shell

37 lines, **zero** `Notation` declarations — its own header says every notation
moved inline to `decl/def_rules.v`.  What remains is two `Require Export`s and
four empty section headings.  Either delete it (and point its consumers at
`frost/notations.v` + `decl/def_rules.v`) or rename it to what it now is
(a re-export module).  It is currently the only reason a reader looks in two
places for declarative notations.

### 3.3 `def_extra.v` names three different things

`frost/def_shapes.v` (shape predicates), `decl/def_rules.v` (908 lines — *the
declarative rules*), `algo/def_rules.v` (1606 lines — *the algorithmic rules*).
The name is a leftover of the ott convention (`def_ott.v` + hand-written extra)
and now describes none of them.  `algo_decl/` was already fixed in this spirit at
`9402f3a` (`def_decl_algo*.v` → `def_{consis_refine,subtyping,typing}.v`).
Applying the same treatment finishes the job:

- `decl/def_rules.v` → `decl/def_rules.v`, or split by judgement as `algo_decl/`
  was (`def_wellformed.v` / `def_consis_refine.v` / `def_subtyping.v` /
  `def_typing.v` — the 17 `Inductive`s group cleanly along exactly those lines);
- `algo/def_rules.v` → `algo/def_rules.v` (a split is less attractive: the
  `a_assign`/`a_unify`/`a_consis` and `a_sub`/`a_sub_flex` mutual blocks and the
  `where`-clause notations pin large groups together);
- `frost/def_shapes.v` → `frost/def_shapes.v` (all 16 `Inductive`s there are
  shape/mode predicates).

Mechanical, `make quick`-checkable, and it removes the tree's worst
"which `def_extra.v`?" ambiguity.  Same argument, smaller: two files are named
`prop_stability.v` (`decl/`, `algo/`) and they are unrelated — the `algo/` one
has 18 consumers, the `decl/` one none.

### 3.4 Notations: the scheme is sound; the docs describe the previous one

The delimiter scheme (`}}d` / `}}ad` / `}}a` / `}}da`, four scopes declared and
opened together in `frost/notations.v:133–147`) is consistent in the code, and
the traps are correctly recorded.  No change recommended to the scheme itself.
But the retired `}}t` spelling still appears in `CLAUDE.md:503` and
`PROGRESS.md:531,538` (renamed to `}}da` at `93c3624`), so a reader following the
legend in `CLAUDE.md` gets a delimiter that no longer exists.

### 3.5 Doc → tree drift: 29 dead path references

Paths cited in `CLAUDE.md` / `README.v` / `docs/PAPER-GAPS.md` that do not exist.
Most are historical (retracted `cex/` files), but four are cited as *current
locations*:

- `frost/prop_etag.v` → `frost/prop_tag.v`  (PAPER-GAPS `:75`, `:99`)
- `frost/decl/prop_etag_swap.v` → `frost/decl/prop_tag_swap.v`  (`:99`, `:106`, `:112`)
- `frost/algo/prop_soundness_pat.v` → `frost/algo/pat/prop_soundness_pat.v`
- `frost/algo/prop_soundness_typing.v` → `frost/algo/typing/prop_soundness_typing.v`

Also: `CLAUDE.md`'s doc-index table links `AGENTS.md`, which the same file's
header says does not exist; and the References section points at two
`docs/superpowers/specs/*.md` design specs that are gone.

A `make check-doc-links` target over `*.md` + `README.v` would keep this from
recurring — the tree already has `make sync-paper-refs` for the analogous job on
paper labels.

---

## Suggested order

1. **§1.1 + §1.2** — factor `a_typing_output_wf` into `prop_wf_preservation.v`,
   retire both Barendregt premises on the four check rows.  The one change here
   that improves the *result*.
2. **§2.3** duplicate names, **§2.1** the clear orphans (`a_split_refines`, the
   three dead rename bridges, the local list utilities).  Mechanical, low risk.
3. **§3.1** index the missing claims in `README.v`; **§3.4/§3.5** the doc fixes.
   No build risk.
4. **§3.3** the `def_extra.v` renames, **§3.2** `decl/notations.v`.  Mechanical
   but touches every import list — do it as one commit.
5. **§1.9** drop `lc_exp e` from `a_typing_complete`.
6. Leave alone: §1.3 (`a_guess_mono`), §1.7 (`a_pat`'s cofinite rows), §1.8
   (the `d_`/`ad_` layers).
