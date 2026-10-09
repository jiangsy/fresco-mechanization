# REPORT — post-theorem-4 cleaning audit

**Date** 2026-08-08 · **Tree state** `8ec2af7`, 39/39 axiom-free, zero
`Admitted`, zero `Axiom` (verified: `grep -rn "^Admitted\|^Abort\|Axiom "
fresco/` is empty; the two `Admitted` hits in comments are HISTORY notes about
removed developments).

> ## ✅ PHASE 1 IS DONE (2026-08-09) — build green, 39/39 `Closed under the global context`
>
> Everything in §9's Phase 1 has landed, plus the file renames the audit did
> not originally propose.  What changed:
>
> | | |
> |---|---|
> | litter | 4 orphan `scratch_*.glob`, 11 `.aux`, `.DS_Store` removed; `make clean` extended to cover them |
> | docs | `HANDOFF-typ-all-plain-refactor.md`, `PROPOSAL-ln-idiomatic-tags.md`, `DESIGN-safe-pat-witness.md` banner-marked SUPERSEDED / NOT ADOPTED / STALE |
> | §1.4 | `prop_completeness_typing.v`'s pre-closure header rewritten (it advertised a phantom `a_typing_rename_tm` and an "⛔ Still owed" list for a closed theorem) |
> | §7.1 | inert `single e Xpt :: subst_typ_in` line removed from `language.ott` |
> | §5.2 | dead `pskl_to_dskl` + 2 lemmas deleted (RESTART NOTE left) |
> | §5.5 | dead `guarded_ptyp` deleted; **and its "3 remaining uses" turned out to be a verbatim duplicate lemma** — see correction (a) |
> | §6 | `fn_arrow_shape*` split out of the rigidity file |
> | §1.2 | the K6 block (**ten** items, not nine) moved into `prop_swap.v` as §6 |
> | §3(a) | cofinite/exists-fresh discipline documented in `CLAUDE.md` and at both `algo/def_rules.v` sites |
> | naming | four badly-named files renamed and clustered — see correction (c) |
> | archive | `algo/prop_symmetry.v.deferred` (1011 lines) deleted — see correction (d) |
>
> **Three corrections to what is written below:**
>
> **(a) §5.5 understated the find.**  `guarded_ptyp`'s three apparent uses were
> a name collision with `guarded_ptyp_to_uskl_syn` — and *that* lemma is a
> verbatim duplicate of `mono_ptyp_to_uskl_syn_guarded`
> (`algo/prop_pat_sub.v:845`), which both of its consumers already import.  So
> this was a duplicate-lemma find, not just a dead predicate: the copy is
> deleted and its call sites repointed.  ⚠️ **The §8.1 duplicate scan cannot see
> this class** — it keys on identical names, and these two differ.  The real
> duplicate count is therefore *higher* than 82.
>
> **(b) §6 was wrong about `a_assign_flex_tvar`.**  I called it "stranded" in
> `prop_ty_core.v`.  It is not: it is the direct helper for
> `a_split_rigid_var_absurd` 25 lines below it.  Left in place.
>
> **(c) The four files the audit discussed by name were themselves badly
> named** (`prop_ty_core`, `prop_ty_scope`, `prop_ty_shape`, `prop_wf_output`) —
> `prop_ty_*` in particular, since two of the three are not about types.  Three
> of them are consumed *only* by theorem 4, so they are now a directory,
> mirroring the existing `completeness_look/`:
>
> ```text
> algo/typing/
>   prop_typing.v      the theorem      (was algo/prop_completeness_typing.v)
>   prop_rigidity.v    rigid data survives a run          (was prop_ty_core.v)
>   prop_scope.v       a run's result never mentions the
>                      suffix it dropped                 (was prop_ty_scope.v)
>   prop_shape.v       an FN-mode run returns an arrow chain
> algo/prop_wf_preservation.v   (was prop_wf_output.v — NOT moved: it has five
>                                consumers, incl. soundness and README.v)
> ```
>
> **(d) `algo/prop_symmetry.v.deferred` is deleted.**  1011 lines, out of the
> build, and superseded three ways over: it never compiled, its own header calls
> its approach "the WRONG way around it", and 28 of its 65 definitions are now
> re-proved correctly by `prop_swap.v`.  Its entire content — the intended
> `a_consis_sym` statement, the `@eq_dec` hang and its fix, and the design
> verdict — is already in `PAPER-GAPS.md` §DEFERRED, which now records the
> deletion.
>
> **⚙ Two traps worth keeping** (both cost a build cycle):
> 1. Moving SIA-elaborated lemmas into `prop_swap.v`, which deliberately has no
>    `Set Implicit Arguments`, broke the block's own *internal* non-`@` call
>    (`a_split_swap x y Hrun`).  External call sites were all `@`-applied and
>    fine.  Fix: `Set`/`Unset Implicit Arguments` scoped to §6.
> 2. `Require Import` is **not** transitive for name visibility.  Moving
>    `a_pat_rename_tm` out of `prop_completeness_pat.v` broke `README.v`, which
>    imports that file but not `prop_swap.v`.

> ## ✅ PHASE 2 (dedupe) DONE — 82 → 53 duplicated names, **0** cluster-vs-outside collisions
>
> | | |
> |---|---|
> | deleted | **17** duplicate declarations — 6 exact, 9 alpha-variants, 2 (`a_inc_dom_flex`, `a_inc_lookup_mono`) after adding an explicit `prop_compose` import |
> | moved | `is_sskl_pskl_to_bskl_syn` → `fresco/prop_basic.v` (it was proved in two files that don't import each other, so it could not be deduped in place) |
> | renamed | **11** — the 10 where the two lemmas genuinely differ, plus `a_wf_aenv_def_ftv_dom` → `a_wf_aenv_def_ftv_dom_in` (below) |
> | result | `algo/prop_completeness_look.v`'s ⚠️⚠️ blocker is cleared; its header now records that flipping consumers onto the facade is safe. **The flip itself (§8.1d) is NOT done** — see Remaining. |
>
> ### ⚠️ The finding that justifies this whole item
>
> §8.1 argued the duplicates were a *maintenance* smell.  They are worse than
> that, and the cleanup itself proved it.  Adding one line —
> `Require Import prop_compose` to `prop_kit.v` — silently changed which copy
> of `a_wf_aenv_def_ftv_dom` four call sites resolved to, and broke the build.
> The two copies state the same fact in `[<=]` form and in pointwise form: they
> are logically equal but **not `apply`-compatible**, so the flip is invisible
> until the kernel rejects it.  With 53 duplicated names still in the tree,
> **any added import can do this again.**  That is the real cost, and it is why
> §8.1 is worth finishing rather than tolerating.
>
> ### Two more classes the original scan could not see
>
> - **Different names, same lemma.**  `guarded_ptyp_to_uskl_syn` vs
>   `mono_ptyp_to_uskl_syn_guarded` (Phase 1), and `a_wf_aenv_def_ftv_dom` vs
>   its pointwise twin.  A name-keyed scan is blind to these, so the true
>   duplicate count is above 82.
> - **Same name, incompatible *binder* names.**  Merging an alpha-variant
>   breaks `apply … with (Θ2 := …)` at call sites that named the deleted copy's
>   binders — 5 such sites had to be repointed.
>
> ### ⚙ Traps, all of which cost a build cycle
>
> 1. **`Require Import` is not transitive for name visibility.**  Bit me three
>    times: `README.v`, `prop_eq_var.v`, and a `cex/` probe.  Reachability in
>    the import graph is *not* the test — only a DIRECT import makes a name
>    visible, and my first over-rename check used reachability and passed
>    files it should have flagged.
> 2. **A blanket rename over-reaches.**  Renaming a cluster copy also rewrote
>    uses that resolved to the *outside* copy — 5 sites across 3 files.  The
>    correct predicate is "does this file DIRECTLY import the declaring file".
> 3. **zsh aborts a whole command on a non-matching glob.**  `rm -f a* b*` with
>    `a*` unmatched runs neither, so three probe `.v` files silently survived
>    into `test/` and broke the build twice (the Makefile globs `*.v`).  Keep
>    probes in the scratchpad.
> 4. **Piping `make` into `grep` masks its exit status** — `$?` is grep's.
>
> ## ✅ PERF — FIXED.  `test_examples.v` 467 s → 23.8 s (20×); one call 426 s → 0.09 s
>
> The build was slow for one reason: **`test/test_examples.v` was 467 s of a
> ~646 s wall-clock build** (`-j8`; total serial proof time ≈ 1229 s).  It is a
> leaf that depends on nearly everything, so it could not overlap — it *was*
> the tail of the critical path.
>
> ### How it was found
>
> 1. `.aux` files (they record `proof_build_time` per proof — no rebuild
>    needed) ranked the files and pointed at `ex_C2`: 442 s, 36% of the tree.
> 2. `Set Ltac Profiling` put 99.9% of that inside `crush_uniq` → `fsetdec` →
>    `tauto` → `simplif` (15.5 M `is_conj`, 13 M `is_disj`).
> 3. **Per-call `time "siteN"` was the step that actually cracked it**, and it
>    is the step I should have taken first.  Of the four `crush_uniq` calls:
>
>    | site1 | site2 | site3 | site4 |
>    |---|---|---|---|
>    | 0.00 s | 0.04 s | 1.92 s | **425.95 s** |
>
>    Everything before this was averaged over all four calls, which is what
>    made three different fixes look plausible and fail.
>
> ### The actual cause
>
> Site 4 is `AT-AbsCheck`'s base row at the innermost binder.  Its residual
> goals after `uniq_push` are **trivial**:
>
> ```text
> α ∉ dom Θlib        x ∉ {α} ∪ dom Θlib        β ∉ {x} ∪ {α} ∪ dom Θlib
> ```
>
> each a one-step weakening of the single hypothesis `atom_fresh` produced for
> that variable.  The cost was never the goal — it was that `fsetdec` also
> reads the *other three* freshness hypotheses (up to six leaves each), and its
> internal `tauto` is exponential in the leaves it can see.  Same cliff the
> 2026-08-06 pass recorded ("12-leaf avoid-set hypothesis ⟹ cliff").
>
> ### The fix
>
> `keep_only_subject` — for a goal `v ∉ S`, drop every `notin` hypothesis whose
> subject is not `v`, then `fsetdec`.  Unscoped `fsetdec` stays as a fallback
> for any goal genuinely needing two hypotheses; it is cheap to reach because
> the scoped attempt either succeeds in ~0.02 s or fails fast.
>
> ### ⛔ Five things that do NOT work (all measured; recorded at the tactic)
>
> 1. `solve_notin` — fails outright.
> 2. `destruct_notin` then `fsetdec` / `solve_notin` / `auto` — fail fast.
> 3. Adding disequality symmetry (`destruct_notin` never flips a `<>`) — fails.
> 4. **Clearing every non-atom-set hypothesis, or use-site
>    `clear - Hα Hx Hβ Hy …`** — no help, and this is the instructive one:
>    both keep all four freshness hypotheses, i.e. every leaf.  Scoping has to
>    be **by subject**, not by relevance-to-the-call.
> 5. Characterising `dom Θlib` as seven singletons + `Opaque Θlib` — no help.
>    (⚠️ `Opaque Θlib` *alone* makes `fsetdec` fail in 6 s, which shows it does
>    need to see the library — that is not where the blow-up came from.)
>
> ### End-to-end
>
> Full clean rebuild after the fix: **13:04** (`make NJOBS=8 coq`, exit 0,
> 39/39 closed).  I do not have a matched clean baseline from *before* the fix
> — the earlier 646 s figure was a partial rebuild that then failed at
> `README.v`, so it is not comparable.  But the inference is sound: the
> `.aux`-derived serial proof time was ≈1229 s and is now ≈786 s, and the
> measured wall clock is 784 s — i.e. **wall clock ≈ serial sum**, so the 443 s
> removed from the file comes off the wall clock essentially one-for-one.
> Pre-fix clean build would have been ≈20.5 min.
>
> ### ⚠️ SECOND FINDING — the build barely parallelises
>
> That last equality is not a coincidence, and it is a separate opportunity:
>
> ```text
> make NJOBS=8 coq   854.82s user  12.32s system  110% cpu  13:04.26 total
> ```
>
> **110% CPU on `-j8`** — an average of ~1.1 cores busy.  The tree is a nearly
> linear dependency chain, so eight jobs buy almost nothing.  Two consequences:
>
> - Any single slow proof is felt in full at the wall clock (which is why one
>   tactic could own 36% of the build).
> - There is a structural win available that is independent of any tactic:
>   breaking the chain.  The `completeness_look/` facade header already notes
>   the cluster is strictly linear "so the directory buys no build
>   parallelism".  Worth measuring where the chain is artificial (an import
>   kept for one lemma) versus real.
>
> ### Follow-up: the same cliff, a second shape, and one tactic for both
>
> The fix above exposed a *second* instance in the next hotspot,
> `a_pat_complete_abs_anno` (`prop_completeness_pat.v`, 248 s = 31% of the
> remaining tree).  Profiling: 99.3% inside one
> `rewrite (swap_aenv_tm_head …)` whose `ltac:(…)` side conditions call
> `fsetdec` four times, 187 s each.
>
> ⚠️ Those calls were **already** `clear - Hx`-scoped to a *single*
> hypothesis — so the standard `clear -` discipline had been applied and did
> not help.  The hypothesis itself is the rule's `L` avoid-set, a union of a
> dozen `dom`/`ftvar_in_aenv` terms.  **Two independent ways to hit the same
> cliff**, needing opposite fixes:
>
> | shape | context | fix |
> |---|---|---|
> | (a) | MANY small `notin` hypotheses | `keep_only_subject` — keep only the goal's own subject |
> | (b) | ONE huge hypothesis | `destruct_notin` — flatten it before `fsetdec` |
>
> A plain `first [...]` cascade cannot serve both, because in each case the
> *wrong* stage still **succeeds — just slowly** — so `first` commits to it:
> `keep_only_subject` first gives (a) 23.8 s but leaves (b) at 248 s;
> `destruct_notin` first gives (b) 0.9 s but pushes (a) to 142 s; both
> combined gives (a) 130 s.
>
> So `solve_notin_auto` **dispatches on the shape** — it tests whether the
> context holds two freshness hypotheses about atoms other than the goal's
> subject — and then applies the matching order.  It equals hand-picking at
> every site.  Promoted to `fresco/ltac_utils.v` and swept across **934**
> `ltac:(…fsetdec)` side conditions in 35 files.
>
> ### Result
>
> | | wall clock |
> |---|---|
> | before (inferred, see above) | ~20.5 min |
> | after the `crush_uniq` fix | 13:04 |
> | after the `solve_notin_auto` sweep | **9:44** |
>
> `test_examples.v` 467 s → 30.8 s.  Parallelism also improved (110% → 150%
> CPU at `-j8`) simply because the serial tail shrank.
>
> ### Lesson for the next perf pass
>
> Profile to the **individual call**, not the tactic.  An aggregate that says
> "this tactic is 99.9%" is compatible with three cheap calls and one
> catastrophic one, and the fixes those two situations need are different.
>
> ## ✅ PHASE 3 (2026-08-09) — §5.4 LANDED, duplicates **53 → 39**, `_thm` retired
>
> | | |
> |---|---|
> | §5.4 | **`fresco/prop_coercions.v` created** (409 lines, 38 lemmas) — the conversion property layer, gathered from ELEVEN files.  `coercions.v` is now definitions-only; `prop_basic.v` is the predicate layer and `Require Export`s the new file, so its ~99 consumers needed no change |
> | naming | the `_thm` suffix retired from all 5 names that carried it |
> | litter | 77 orphaned artifacts removed; **`make tidy`** added; `make clean`'s depth bug fixed |
> | dedupe | 53 → **39** duplicated names |
>
> ### The `_thm` suffix meant nothing
>
> `a_pat_sound` beside `a_sub_sound_thm` — the user flagged the inconsistency.
> It was not a distinction: for all four (`a_sub_sound_thm`,
> `a_sub_complete_thm`, `a_consis_complete_thm`, `a_sub_flex_sound_thm`, plus
> `a_sub_sound_thm_v`) **the bare name was unoccupied**.  Meanwhile
> `a_typing_complete` carries twelve row-siblings and no suffix, so the tree's
> own majority convention was already "no suffix".  Renamed; the rule is now in
> `CLAUDE.md`.
>
> ### §5.4 — what was actually wrong
>
> The report predicted a tidiness win.  It is bigger than that, because the
> same fact was proved **two, three and four times** under DIFFERENT names,
> which no name-keyed duplicate scan can see:
>
> | fact | copies | names it went under |
> |---|---|---|
> | `ftvar_in_pskl (ptyp_to_pskl A) [=] ftvar_in_ptyp A` | **4** | `ftvar_in_pskl_ptyp_to_pskl`, `ftvar_in_ptyp_to_pskl`, `ftvar_ptyp_to_pskl`, `ftvar_in_pskl_ptyp_to_pskl_local` |
> | `ftvar_in_btyp (ptyp_to_btyp_syn A) = ftvar_in_ptyp A` | **3** | twice as `ftvar_ptyp_to_btyp_syn` (once weakened to `[<=]`), once as `ftvar_paint_btyp_syn_eq` |
> | `ftvar_in_ptyp (btyp_to_ptyp B) = ftvar_in_btyp B` | **3** | `ftvar_btyp_to_ptyp` ×2 (`=` and `[<=]`), `ftvar_in_ptyp_btyp_to_ptyp` (`[=]`) |
> | `mono_ptyp_to_pskl_lc` / `mono_ptyp_lc` / `ptyp_to_pskl_lc` / `is_dskl_lc` | 3/3/2/2 | one name each |
>
> ⚠️ **The tree contained written proof that this is a correctness hazard.**
> `decl/prop_syntax_directed.v`'s `ftvar_paint_btyp_syn_eq` existed for no
> reason except to escape a name collision — its own comment said so: *"the
> imported `ftvar_ptyp_to_btyp_syn` is the weaker `[<=]` variant (it shadows
> the `=` one from prop_wellformed); we need both inclusions here."*  Someone
> re-proved a two-line induction rather than fight the shadow.  By the time it
> was found it had **zero uses** — dead code left behind by a name clash.
>
> ### The resolution rule: keep the STRONGEST form, derive the rest
>
> Three of the collisions were not duplicates — they were the same fact at
> different strengths (`=` vs `[=]` vs `[<=]`; general `open` vs its variable
> instance).  Keeping both under different names would have been the wrong
> fix.  Each is now stated ONCE in its strongest form and the weak uses
> `rewrite` with it.
>
> ⚠️ **But "strongest form" does NOT mean "most general statement".**  I first
> deleted the variable-instance `_open` lemmas outright, reasoning that the
> general form subsumes them — `decl/` files see only the general form and were
> already doing `rewrite <- ptyp_to_btyp_inh_open` against it successfully.
> `make coq` refuted that: `rewrite`'s matching is **syntactic**, so unifying
> the pattern's `ptyp_to_btyp_inh ?A2` against a bare `btyp_var_f α` in the goal
> would need the fixpoint unfolded, and it will not do that.  Logical
> subsumption is not rewrite-subsumption.
>
> The resolution keeps the spirit without the error: `_open_var` exists as a
> **one-line corollary** (`exact (…_open A (ptyp_var_f α))` — the two differ
> only up to conversion), not a second induction.  So there is still one proof,
> and the two names now make visible an asymmetry that used to be settled by
> import order: `decl/` goals want the general form, `algo/` goals want the
> variable one.
>
> ### ⚙ `make tidy`
>
> Phase 1 swept litter by hand; it came straight back (11 `.glob`, 66 `.aux`),
> because `clean` matched `*/.*.aux */*/.*.aux` and the tree is now THREE deep,
> and because it knew only the `scratch_*` prefix, not `probe_*` / `chk_*` /
> `zz_*`.  `make tidy` instead deletes an artifact iff its companion `.v` is
> gone — no name patterns to maintain, and unlike `clean` it PRESERVES the live
> `.aux` timing data that every perf pass starts from.
>
> ### ⚠️ The trap that cost the two failed `make coq` runs
>
> **`Set Implicit Arguments` is per-FILE, so moving a lemma silently
> re-elaborates its signature.**  `mono_ptyp_to_pskl_lc : forall τ, mono_ptyp τ
> -> …` has a STRICTLY implicit subject; it came from `algo/prop_flex.v`, which
> sets the flag, so three call sites wrote `mono_ptyp_to_pskl_lc Hm`.  In a file
> without the flag τ turns explicit and `Hm` is read as the `ptyp`.  Fix: the
> flag is now SCOPED to §3 of `prop_coercions.v`, which is exactly the block
> whose lemmas have the `forall x, Pred x -> Pred' (f x)` shape.  §1/§2/§4 must
> stay outside it — their arguments are explicit everywhere and are passed
> explicitly (`ftvar_ptyp_to_btyp_syn (btyp_to_ptyp B)`).
>
> ⚙ Same hazard as `prop_swap.v` §6, recorded in Phase 1, but in the opposite
> direction — that one moved SIA-elaborated lemmas INTO a non-SIA file.  The
> lesson generalises: **a cross-file lemma move is not signature-preserving.**
>
> ### ⚠️ `make quick` cannot verify a refactor of this kind
>
> `vos` mode skips everything between `Proof` and `Qed`, so it checks
> statements, imports and statement-level name visibility and nothing else.
> Three `make quick` runs went green on changes that `make coq` then rejected
> (a moved lemma used inside a proof body; the implicit-argument break above).
> A name-visibility scan over the import graph found the first class but is
> blind to the second.  **For a dedupe or a move, `make coq` is the only gate.**
> Related: `make coq > log; echo $?` reports the *echo's* status — a failed
> build reads as exit 0.
>
> ## ✅ PHASE 3c (2026-08-09) — FILE REORG: the "kit" is gone, `algo/` is grouped by judgement
>
> ### The `prop_kit.v` rename became a three-way split
>
> "kit" named nothing, and a rename alone could not be honest: the file was
> **6952 lines and three separable concerns**, and §8.3 had already called it
> "the grab-bag, and the source of most §8.1 duplicates".  Now:
>
> | file | lines | owns |
> |---|---|---|
> | `sub/look/prop_rho_relation.v` | 3286 | the ρ relation `uskl_rho`, its inversions by subject and by target, shielded ftv / `rho_fresh`, the solve-context transports |
> | `sub/look/prop_solve_ext.v` | 1692 | the flex-block extension algebra and the three packages P6 is stated over — `solve_ext`, `solve_sub_ext`, `cv_mono_concl` |
> | `sub/look/prop_flex_apart.v` | 2103 | `flex_apart` and the Arrow-case repair |
>
> ⚙ Cuts in a linear Coq file are always dependency-clean (nothing can use what
> is not yet defined), so the only question is COHERENCE.  The second seam took
> care: the ρ inversions appear at two separate points, so the cut is at the
> flex-block extension kit, which puts all three `solve_*` definitions on one
> side and all four ρ definitions on the other.
>
> ### `algo/` grouped BY JUDGEMENT — 35 flat files → 18 flat + 4 folders
>
> ```text
> algo/  def_extra def_meta + the shared machinery, deliberately FLAT
>        consis/  4    sub/  8 (+ look/ 8)    pat/  2    typing/  5
> ```
>
> ⚠️ **A `soundness/` vs `completeness/` split would have been a lie**, and the
> import graph says so: there is **no soundness-only file in the tree**.
> `prop_soundness_consis.v` is imported by 13 completeness files,
> `prop_soundness_subtag.v` by 6.  Soundness results ARE kit for completeness.
> Judgement is the axis that matches the dependencies.
>
> ⚠️ **No `kit/` folder either** — 9 files whose only shared property is
> "shared" would have repeated the `prop_kit.v` mistake at directory scale.
> The machinery stays flat until a real cluster emerges.
>
> `prop_sub_concrete_rhs.v` → `cex/probe_sub_concrete_rhs.v`: **zero
> consumers**, because it is a FINDING, not machinery — it proves the reading
> of the paper's `:3243` TODO that its two cases need, opposite
> `cex_p7_concrete_rhs.v` which refutes the reading the TODO states.
>
> ### ⚠️ Three traps, each one a failed build
>
> 1. **`Set Implicit Arguments` is per-FILE.**  It was line 84 of `prop_kit.v`,
>    so every split half needed its own copy; without it
>    `pskl_flex_free_arrow_inv Hff` reads `Hff` as the `aenv`.  Third
>    appearance today — after moving lemmas INTO a non-SIA file
>    (`prop_coercions.v`) and now after SPLITTING an SIA file.  **A cross-file
>    lemma move is not signature-preserving, in either direction.**
> 2. **The failure was SILENT inside `match goal`.**  The error read
>    `No matching clauses for match` and pointed at a pattern that — as the Coq
>    MCP confirmed against the live proof state — *did* match: the hypothesis
>    was right there.  When a branch's BODY fails to elaborate, `match goal`
>    reports only that no clause matched.  Read the error as "pattern matched
>    but body failed" before doubting the pattern.
> 3. **A stale `.vo` let a dead import resolve.**  Three `cex/` files still
>    imported `prop_kit` (I had grepped `fresco/` only), and the leftover
>    `prop_kit.vo` meant they *resolved* instead of failing cleanly — surfacing
>    much later as "makes inconsistent assumptions over library".  `make tidy`
>    removes exactly this; run it after ANY rename.
>
> ⚙ Verification for a path change: before building, check that every
> `Require`d `src.*` module resolves to a real file (73 of 73 here).  It costs
> a second and catches the whole class.
>
> ### ⛔ The three "small files that should be merged" must NOT be merged
>
> §5.3/§8.3 read `prop_inc_strengthen.v` (444), `prop_precise_sub.v` (269) and
> `prop_precise_recover.v` (313) as merge candidates — same topic as their
> base, small enough to fold in.  Measured against the import graph, all three
> are wrong:
>
> | merge | verdict |
> |---|---|
> | `prop_inc_strengthen` → `prop_inc` | **CYCLE** — needs `prop_flex`, `prop_compose`, `prop_normal`, all of which import `prop_inc` |
> | `prop_precise_sub` → `prop_precise` | **CYCLE** — context precision is stated over the SUBTYPING and PATTERN judgements, which reach back to `prop_precise` |
> | `prop_precise_recover` → `prop_precise` | no cycle, but it imports `consis/prop_soundness_consis.v` (5610 lines) and `prop_precise` has **24** consumers |
>
> **A `_<qualifier>` sibling is usually a LAYER, not a size accident.**  The
> suffix records that the file sits ABOVE its topical base in the dependency
> order.  The check before any same-topic merge is: does any extra dependency
> of the smaller file reach the larger (cycle), and what does the merged
> dependency surface cost the base's consumers?  Each of the three now carries
> a ⚠️ DO NOT MERGE header note, so the next audit does not re-propose them.
>
> ### ✅ §7.1 FIXED AT THE SOURCE — `subst_bskl_in_uskl` → `subst_uskl_in_uskl`
>
> `language.ott:156` read `single R Xus :: subst_bskl_in` — a copy of the line
> above it — where `R` is a **uskl**.  So lngen generated `subst_bskl_in_uskl`
> for what is uskl-INTO-uskl substitution (`def_ott.v`: `(R_5:uskl)
> (α5:usklvar) (R__6:uskl)`), the one sort named for the wrong source.  Fixed
> in the ott, regenerated, and swept: **707 occurrences**, 0 residual,
> `subst_bskl_in_bskl` (373 uses, the legitimate one) untouched.
>
> ⚙ **Verify generator reproducibility BEFORE editing an ott.**  `def_ott.v`
> and `prop_ln.v` are tracked, so a regeneration can smuggle in unrelated
> generator drift.  Regenerating them with the ott UNCHANGED first confirmed
> byte-identity with the committed versions — which is what made the post-edit
> diff checkable: 121 changed lines, every one containing only that identifier.
>
> ⚠️ **A trailing `\b` silently blocks a PREFIX rename.**  `_` is a word
> character, so `s/\bsubst_bskl_in_uskl\b/…/` matched none of the derived
> lngen names (`…_open_uskl_wrt_uskl`, `…_fresh_eq`, …) — and the per-file loop
> reported success for every file while changing nothing.  The trailing
> boundary that was REQUIRED for the `_thm` rename is the one that breaks this
> one; the difference is whether the target is a whole name or a prefix.
> **Check the residual count, never the exit status.**
> ⚙ Also: zsh does not word-split unquoted expansions, so `perl … $FILES`
> passes the entire newline-separated list as one filename.
>
> ### ⛔ §4(b) is a PAIRED change — do not do half of it
>
> `mod_comp_ty` / `mod_comp_sk` are SUBJECT-first; their algorithmic
> counterparts `a_ty_mode_compat` / `a_sk_mode_compat` are MODE-first, as are
> `fn_arrow_shape*` and `pskl_ty_core` / `ptyp_ty_core` (mode-first is 6 of the
> 8).  The report proposed renaming to unify the words.  **Renaming alone would
> make it worse**: same-shaped names taking their arguments in opposite orders
> is a sharper trap than two visibly different names.
>
> Cost of doing it properly: ~60 applications pass a compound first argument
> (`mod_comp_ty (btyp_arrow B1 B2) (mode_fn m)`), so the flip needs
> balanced-paren rewriting rather than a sed, plus 110 bare references and 58
> constructor references.  Both definition sites now carry a ⚠️ note so the
> halves are not separated.
>
> ## ✅ TIER 1 (2026-08-09) — 6 duplicated names resolved; `rename_aenv` out of the rules file
>
> | fact | resolution |
> |---|---|
> | `mod_comp_ty_tc_inv` | lifted to `fresco/prop_basic.v` (its predicate is declared in `fresco/def_shapes.v`) |
> | `a_wf_ptyp_ftv_dom`, `a_binds_tvar_in_dom`, `a_scope_pskl_ftv_dom` | lifted to `algo/prop_flex.v`, joining `a_wf_ptyp_ftv_tvarish` — they are ONE "wf/scope ⟹ ftvar ⊆ dom" family that had been split across four mutually-invisible files |
> | `ad_pat_sub_gv_psi_cong` | **could not be lifted** — see below; deduped by IMPORT instead |
> | `a_wf_aenv_uniq_local` ×2 | a THIRD copy of `prop_flex.v`'s `a_wf_aenv_uniq`, byte-identical, under a different name.  Deleted; 11 files repointed |
>
> ### ⭐ The lift test has THREE conditions, not two
>
> §8.1 and the phase-3b note gave two: (a) one declaring file already sees the
> other, or a shared ancestor exists; (b) every other consumer sees the
> survivor.  `ad_pat_sub_gv_psi_cong` shows a third is needed:
>
> > **(c) the host must see every prerequisite of the PROOF.**
>
> That lemma needs `ad_pat_sub_gv` (`algo_decl/def_decl_algo_sub_hyg.v`)
> AND `ad_pat_consis_psi_cong` (`algo/consis/prop_soundness_consis.v`) — from
> opposite sides of the tree.  Measured: **no** shared ancestor of the two
> declaring files sees both, so the pair is unliftable.  The dedupe is by
> IMPORT: keep it in `sub/prop_soundness_subtag.v`, the earliest file that sees
> both, and have `sub/prop_completeness_sub_precise.v` import that (verified
> cycle-free, 0 name collisions, 0 reroutes before adding the import).
>
> ⚙ And when a lemma moves WITHIN a file, it must land above its first use —
> appending to the end put it 380 lines after the consumer.
>
> ### §1.1 — the cheap half done, the retirement not
>
> `rename_abind` / `rename_aenv` moved out of `algo/def_rules.v` (which should
> hold RULES) into `prop_swap.v` next to `swap_aenv`, with a ⚠️ note on which to
> reach for; their bridge `swap_aenv_as_rename` was already there.  **Retiring
> `rename_aenv` outright is NOT a rename** — its 23 sites are
> `rewrite rename_aenv_cons_tvar_eq`-style, so it is a proof change.
>
> ### ⛔ §4(a) declined — the report's "low risk" is wrong
>
> Collapsing `fn_arrow_shape` into a transparent `Definition` over
> `fn_arrow_shape_pskl` would break `algo/typing/prop_typing.v:1006`, which
> pattern-matches `fn_arrow_shape M ?BB` inside a `match goal`.  Whether that
> still matches depends on how the hypothesis was built, and a failing branch
> reports as "No matching clauses for match" — the silent-failure mode that
> cost two builds this session.  Not worth it to remove one 9-line inductive.
>
> ## Remaining
>
> ### ⚙ "39 duplicated names" is not "39 deletions"
>
> The scan keys on NAMES, so its output mixes two unrelated problems.  Measured
> over the 39 that remain:
>
> | class | count | correct fix |
> |---|---|---|
> | identical statement | 12 | delete one copy |
> | alpha-variant | 1 | delete one copy |
> | **genuinely different statements** | **26** | **rename, or generalise one to subsume the other — merging would be WRONG** |
>
> So the floor is not zero deletions-to-go: only ~13 are true duplicates.  The
> 26 are *name collisions between different lemmas*, which is the more
> dangerous class (that is what silently reroutes an `apply`), and the fix is a
> rename or a generalisation, never a merge.  The target to drive to zero is
> **collisions**, not names.
>
> ### ✅ VERIFIED BY A CLEAN REBUILD — 108/108
>
> `make clean && make coq`, exit 0, 97 files: **every one of the 108
> `Print Assumptions` in the tree reports `Closed under the global context`**,
> with zero `Axioms:`/`Parameters:`/`Variables:` and zero `Admitted`/`Axiom`.
>
> ⚠️ Do this at the end of a refactor, and quote the clean figure.  An
> INCREMENTAL `make coq` only emits the reports of the files it happens to
> rebuild — 98 of 108 here — so "all reports closed" from an incremental run is
> a weaker claim than it looks, and the gap is invisible unless you count.
> (The "39/39" in the older banners is a smaller, earlier count; 108 is the
> whole tree.)
>
> ### ✅ §8.1d IS DONE, and six more duplicates went — 39 → **33**
>
> `prop_completeness_sub_gen.v`'s three piecewise imports are now one facade
> line.  Two checks were run first, and BOTH are needed — tree-wide
> collision-freedom is not sufficient: (1) the consumer must declare no name
> that a NEWLY-exposed cluster file declares (0 here), and (2) no cycle — safe
> because the three added files are EARLIER in the linear chain and so already
> transitively required.  Both are now recorded in the facade's header.
>
> ⚙ `prop_wf_preservation.v` and `prop_sub_msubst_equiv.v` stay piecewise
> deliberately: each wants one or two files, so the facade would buy them
> nothing but a wider name surface.
>
> Deleted (identical statements; the surviving copy verified visible at every
> consumer): `a_solve_cstr_decls`, `d_wf_ptyp_ftvar`, `d_wf_ptyp_lc_loc`,
> `guarded_pskl_lc`, `bskl_to_pskl_msubst_bskl`, `ptyp_to_uskl_syn_arrow`.
>
> ### ⚙ The visibility test that decides whether a pair CAN be deduped in place
>
> A pair is deletable-in-place only if **(a)** one declaring file already sees
> the other (via a direct import or an `Export` chain — reachability is the
> WRONG test), and **(b)** every OTHER consumer of the name sees the survivor.
> Computed over the 13 true duplicates, only 6 pass both.  The rest need a
> lemma LIFTED to a common ancestor, because the two declaring files do not see
> each other at all (`a_wf_ptyp_ftv_dom`, `a_wf_aenv_uniq_local`,
> `a_scope_pskl_ftv_dom`, `ad_pat_sub_gv_psi_cong`, `mod_comp_ty_tc_inv`) — the
> same situation that forced `is_sskl_pskl_to_bskl_syn` up to `prop_basic.v` in
> Phase 2.
>
> ⚠️ `guarded_pskl_subst_var` looks deletable and is not: 3 of its 4 consumers
> see the better survivor but `algo/prop_consis_rename.v` sees only the other
> copy.  Fixing it by ADDING an import is exactly the move that has broken this
> build before, so it is left alone.
> ⚠️ `a_wf_aenv_binds_def_mono` is the same shape at larger scale — 21 of 22
> consumers see one copy, 14 the other.
>
> ## Remaining
>
> - The 7 true duplicates that need a lift to a common ancestor (above).
> - `binds_insert_mid` is the instructive one in the "26": both copies are
>   stated over `abind` when the fact is **polymorphic in the payload**, so one
>   generic lemma subsumes both — but the two state their arguments in
>   DIFFERENT ORDERS and 13 call sites apply them positionally with `@`, so the
>   merge is not a rename.  Much of §8.2's list is the same shape.
> - §8.2 `prop_aenv.v`, §5.3 composite chains, §7.1 `subst_uskl_in_uskl`
>   rename, §4 the `mode_spine` work.
> - ⚙ Deliberately NOT done: renaming the five skeleton conversions' var-form
>   `_open` lemmas to `_open_var` for uniformity with the type conversions.
>   144 call sites, no collision to fix, no semantic change — churn.  The two
>   names that DID collide are resolved above.

**Scope** the eight aspects the user named.  Findings are graded

- **A** — zero risk to any proof: dead code, litter, doc drift, pure renames
  the compiler checks.
- **B** — mechanical but wide: touches many call sites, no rule or statement
  changes.  A failed edit fails loudly.
- **C** — touches a *rule* or a *statement*.  Re-proof cost is real; each one
  says which of the four section-D theorems it puts at risk.

Headline: the tree is in good shape (2945 top-level items, no admits).  The
debt is concentrated in four places — the **five-mirror `ad_pat_sub` family**,
the **eight mode-spine inductives**, the **82 duplicated names**, and the
**scattered coercion/utility layer**.

---

## 0. Summary table

| # | Aspect | Grade | Headline |
|---|---|---|---|
| 1 | rename / swap | B + C | swap kit is THE primitive by directive but covers 2 of 3 renaming idioms; its term-var half is stranded inside `prop_completeness_pat.v`; 59 `*_rename_*` lemmas across 20 files |
| 2 | `_gv` / `_g` | C | **five** mirrors of `ad_pat_sub` (~560 lines of duplicated rule text) + 25 lemma pairs proved twice |
| 3 | cofinite vs existential | C | ✅ **DONE 2026-08-13** — `a_pat`'s four binder rows were the last COFINITE algorithm rows and are now EXISTS-FRESH, uniformly with `a_typing`'s six.  Net −250 lines; theorems 1–4 all re-closed |
| 4 | `fn_arrow_shape` / `mode_compat` | C | **eight** inductives over the same arrow-spine-on-`mode` shape, in three files, with inconsistent argument order |
| 5 | coercions / predicates | A + B | 14 conversions in `coercions.v` + ≥4 more elsewhere; 2 dead; no composite names (35+32 raw nested chains); commuting squares scattered over 5 files |
| 6 | `ty_core` | A | `prop_ty_core.v` is coherent for 2 of its 3 clusters; `fn_arrow_shape*` (lines 1215-1300) does not belong there |
| 7 | metavar names | A + B | `subst_uskl_in_uskl` is misnamed at the **ott** level; `T`/`B` used for `uskl`/`pskl` inside rule definitions; ~34 annotated binders violate the letter convention |
| 8 | file / lemma names, restructure | A + B | **82 duplicated names** (28 in the `completeness_look/` cluster — this is what blocks the already-written facade); ~50 generic list/binds helpers with no home; build litter |

---

## 1. rename / swap

### 1.1 Three renaming operators on `aenv` coexist

| operator | where | shape | uses |
|---|---|---|---|
| `swap_aenv γ β Θ` | `algo/prop_swap.v:135` | transposition (bijection) | 143 |
| `rename_aenv γ β Θ` | `algo/def_rules.v:119` | directed rename, key + payload | 21 |
| `subst_aenv` | `algo/def_meta.v` | payload-only substitution | 34 |

`swap_aenv_as_rename` (`prop_swap.v:635`) bridges the first two, so this is
not a soundness issue — it is that a reader must learn three.  `rename_aenv`
survives in only 5 files (`prop_flex.v`, `prop_looksub.v`,
`deco_algo/prop_decorate_sub.v`, plus its own definition and the bridge).

**Recommendation (B).**  Retire `rename_aenv`/`rename_abind` in favour of
`swap_aenv` + the bridge, or — if the directed form is genuinely needed at
those 21 sites — keep it but move it next to `swap_aenv` in `prop_swap.v` and
say in one comment which to reach for.  Deleting it from `algo/def_rules.v`
also removes 20 lines of *definition* from a file that should hold rules.

### 1.2 The swap kit's term-variable half is stranded

`prop_swap.v` (2392 lines) is the type-variable equivariance kit.  The
**term**-variable half was built later and lives inside
[prop_completeness_pat.v:996-1330](../fresco/algo/prop_completeness_pat.v#L996-L1330)
under a `K6` banner — nine lemmas that are pure kit material:

```
swap_abind_fresh_eq   swap_aenv_fresh_eq   swap_aenv_tm_head   swap_aenv_one
a_split_swap          a_sub_rename_tm      a_consis_rename_tm
a_split_rename_tm     a_pat_rename_tm
```

`a_split_swap` in particular is a per-judgement equivariance lemma sitting in
a completeness file while its eleven siblings (`a_sub_swap`, `a_consis_swap`,
`a_assign_swap`, …) are in `prop_swap.v`.

**Recommendation (A/B).**  Move all nine to `prop_swap.v` (a new §6 "term
binders").  Pure relocation — `prop_completeness_pat.v` already imports
`prop_swap.v`, so the dependency direction is right and nothing else moves.

### 1.3 Swap coverage stops below the top two judgements

Equivariance lemmas exist for `a_guess_mono`, `a_guess`, `a_looksub`/
`a_lookeq`, `a_solve_sub`/`a_solve_eq`, `a_solve_cstr`, `a_extract`,
`a_assign`/`a_unify`/`a_consis`, `a_split`, `a_sub`/`a_sub_flex`, `a_inc`,
`a_wf_ptyp`, `a_wf_pskl`, `a_tyequiv`.

Missing: **`a_pat`** and **`a_typing`**.  Their renaming is done by the
substitution-shaped `a_pat_rename_tm` (term vars only) and, on the
declarative-in-algo side, by `prop_rename_decl.v` (712 lines, tvar).  So the
top of the tower is the one place the standing directive is not in force.

**Recommendation (C, low risk).**  Add `a_pat_swap` / `a_typing_swap`.  The
existing K6 comment (`prop_completeness_pat.v:961-976`) already sketches the
proof ("mirrors them row by row").  This is *additive* — no existing statement
changes — so no theorem is at risk; it just lets later work stop hand-rolling
renames.  Estimated ~250 lines.

### 1.4 Stale doc reference

`prop_completeness_typing.v:4` and `:32` both cite **`a_typing_rename_tm`** —
a lemma that does not exist anywhere in the tree.  (A) Fix the header to name
whatever actually discharges the binder rows.

---

## 2. `_gv`, `_g`

### 2.1 Five mirrors of one judgement

| mirror | file | rows | what it adds |
|---|---|---|---|
| `ad_pat_sub` | `def_subtyping.v:59` | 12 | the paper's box |
| `ad_pat_sub_n` | `def_subtyping.v:147` | 12 | + fuel |
| `ad_pat_sub_g` | `def_decl_algo_sub_hyg.v:48` | 12 | + fuel + tag hygiene |
| `ad_pat_sub_gv` | `def_decl_algo_sub_hyg.v:143` | 12 | + fuel + hygiene + leaf refinement |
| `ad_pat_sub_v` | `def_decl_algo_sub_hyg.v` (Definition) | — | `∃n, _gv` |

`_g` and `_gv` differ in **four** premises across three rows (`__infer`,
`__check`, `__univ_ghost_r` gain a `⊢ᵣₚᵃᵈ` premise; `__arrow` gains one on the
domain).  The other eight rows are character-for-character identical — 113
lines duplicated in `def_decl_algo_sub_hyg.v` alone, and ~560 lines of rule
text across the five mirrors.

The lemma families are duplicated to match.  **25 names appear in both an
`ad_pat_sub_g_*` and an `ad_pat_sub_gv_*` form** (12 constructor-shaped
`ad_pat_sub_{g,gv}__row`, 13 transports):

```
arrow_transport  flex_mono_transport  fold_flex  forall_l_tagged_transport
forall_l_untagged_transport  ghost_transport  ghostg_transport  ghost_intro
psi_cong  refl_transport  ughost_l_transport  ughost_lg_transport
ughost_r_transport  wrap_univ_ghost
```

`_g`-only: 10 (`of`, `ti_consis`, `concrete_target`, `ftag_sub`, …).
`_gv`-only: 13.

### 2.2 `_n` is now confined to one consumer

`ad_pat_sub_n` survives in 5 files but only *substantively* in
`prop_completeness_sub_precise.v` (64 uses, 3 lemmas: `_succ`, `_mono`,
`_rename_tvar`).  `prop_completeness_sub_gen.v:20` records that the
development "settled on the TAG-HYGIENIC fuel" `_g`, so `_n` is scaffolding
that outlived its plan.

### 2.3 Recommendation

Two options, both **C**:

- **(C-cheap) Parameterise the leaf datum.**  Replace `_g` and `_gv` with one
  inductive taking a `Prop`-valued flag, e.g.
  `ad_pat_sub_h (leaf : bool) : nat -> … -> Prop`, whose three leaf rows carry
  `leaf = true -> Θ ⨟ empty ⊢ᵣₚᵃᵈ … ⊳ …`.  Then `_g := _h false`,
  `_gv := _h true`, `_gv_forget` becomes a one-line monotonicity lemma, and the
  25 duplicated transports collapse to 25 single lemmas generic in `leaf`.
  **Risk:** every `induction H` on `_g`/`_gv` in
  `prop_completeness_sub_precise.v` (3075 lines) and
  `prop_completeness_sub_gen.v` (7536 lines) sees one extra hypothesis per leaf
  row.  Puts **thm:complete-subtyping** at risk, which theorems 3 and 4 sit on.
  I would not do this without a dedicated campaign.

- **(C-cheaper, recommended) Leave the inductives, kill `_n`.**  Check whether
  `ad_pat_sub_n`'s three lemmas can be restated on `_g` (they are `_succ`,
  `_mono`, `_rename_tvar` — all fuel bookkeeping that `_g` also needs and
  probably already has).  If so, delete the `_n` inductive (33 lines) and one
  bridge, and the mirror count drops 5 → 4 with **no** change to any live
  statement.  Start here; it is the only part of this aspect that is nearly
  free.

---

## 3. cofinite vs existential

Rule: **decl stays cofinite, algo goes full existential.**  Audit against it:

| file | layer | cofinite rows | verdict |
|---|---|---|---|
| `decl/def_rules.v` | decl | 36 | ✅ correct |
| `deco_algo/def_decorated.v` | decl-in-algo | 13 | ✅ correct |
| `algo_decl/def_typing.v` | decl-in-algo | 10 | ✅ correct |
| `algo_decl/def_consis_refine.v` | decl-in-algo | 9 | ✅ correct |
| `algo_decl/def_decl_algo_sub{,_hyg}.v` | decl-in-algo | 4 + 2 | ✅ correct |
| `algo/def_meta.v` | algo (meta) | 2 | see below |
| **`algo/def_rules.v`** | **algo** | **7** | **3 wf + 4 `a_pat` — see below** |

The seven in `algo/def_rules.v` split into two groups:

**(a) Well-formedness — `a_wf_ptyp:166`, `a_scope_pskl:181`, `a_wf_pskl:282`.**
These are static judgements, not algorithm runs.  Cofinite is the standard LN
idiom and buys the strong elimination the whole tree leans on.  **Leave them.**
Recommend adding one line to `algo/def_rules.v`'s header saying so, because a
reader applying the rule mechanically will otherwise "fix" them.

**(b) `a_pat`'s four binder rows — `a_pat__abs:1406`, `__abs_anno:1415`,
`__abs_check:1421`, `__abs_anno_check:1428`.**  These *are* algorithm runs, and
they are the one real violation.  `a_typing`'s six counterparts were converted
in `7061d31` and now carry
`x ∉ dom (Ξ ++ …) ∪ dom Θ2 ∪ fvar_in_exp e` with the comment "EXISTS-FRESH
binder, uniformly with the check rows below" — a uniformity `a_pat` never got.

The cost of the asymmetry is already paid and visible: because `a_pat` is
cofinite while the IH delivers one instance,
[prop_completeness_pat.v:961-976](../fresco/algo/prop_completeness_pat.v#L961-L976)
records a ⛔ block explaining that the four rows "need a kit piece that does not
exist yet" — the K6 rename kit (§1.2) exists *only* to rebuild the cofinite
family from an instance.  Going exists-fresh deletes that need on the
completeness side and moves it to soundness (which must then rebuild the family
— exactly what `prop_rename_decl.v` already does for `ad_pat`).

**Recommendation (C, expensive).**  Convert the four rows.  **Risk: puts
`a_pat_sound` (theorem 1) and `a_pat_complete` (theorem 3) both in play**, and
`a_typing`'s rules invoke `a_pat`, so theorems 2 and 4 see the shockwave.  The
`7061d31` precedent says this is a multi-day campaign, not a cleanup.

My honest read: **the asymmetry is a wart, not a defect.**  If the paper is
being written against this tree, the argument for converting is that the
*paper's* two figures should not disagree about what a binder rule means.  If
the mechanization is the deliverable, defer it and document the split at the
top of `a_pat`.  I would do the documentation now and hold the conversion for a
dedicated branch.

### ✅ DONE 2026-08-13 — and it was cheaper than this section priced it

The four rows are exists-fresh, with `a_typing`'s own side condition verbatim
(`x ∉ dom (Ξ ++ Θ1) ∪ dom Θ2 ∪ fvar_in_exp e`).  `make coq` green, all 32
`README.v` assumption reports still "Closed under the global context", so
theorems 1–4 all survived.  Three corrections to the estimate above:

- ⭐ **It was not a multi-day campaign.**  Eight files, and the net is
  **−250 lines**: `prop_completeness_pat.v` −102 and `prop_swap.v` −155
  against small additions elsewhere.  The `7061d31` precedent over-priced it
  because that pass ALSO changed what the rules mean (the discarded suffix,
  the free `B1`); this one changes only how the binder is quantified.
- ⭐ **The completeness side is where the saving is**, as predicted: the four
  ~30-line family-regeneration blocks became three lines each, and
  `a_pat_rename_tm` — the whole reason K6's last piece existed — is **gone**.
  ⚠️ It could not merely be left unreferenced: over exists-fresh rows it is
  not provable (its binder rows need `b <> x` for an `x` the statement cannot
  constrain).  The ⛔ note where it used to be, in `algo/prop_swap.v`, records
  that argument.
- ⚙ **The soundness side cost four `atom_fresh` blocks**, replaced by opening
  the `a_wf_exp` families at the row's own binder.  The two lemmas that does
  it (`a_wf_exp_abs_pick`, `a_wf_exp_abs_anno_pick`) already existed — built
  for `7061d31` — so this was substitution, not new mathematics.  The cofinite
  `a_wf_exp_abs_inv` was deleted as its last consumer went.

⚙ The §1.3 recommendation to add `a_pat_swap` (item 19 of the closing list)
is **not** affected: `a_pat_rename_tm` was the term-variable renaming, and the
type-variable equivariance it asks for was never written.

---

## 4. `fn_arrow_shape` and `mode_compat`

**Eight inductives share one shape:** "peel `FN`-depth(`M`) arrows off the
subject, then constrain what is left".  They differ only in the base rows.

| name | file:line | carrier | TI base | TC base |
|---|---|---|---|---|
| `mod_comp_ty` | `def_extra.v:230` | `btyp → mode` | `is_styp B` | `is_ityp B` |
| `mod_comp_sk` | `def_extra.v:243` | `bskl → mode` | `is_sskl Q` | `is_sskl Q` |
| `a_ty_mode_compat` | `algo/def_rules.v:227` | `mode → pskl` | `P = □` | `P = ⌊A⌋` |
| `a_sk_mode_compat` | `algo/def_rules.v:237` | `mode → pskl` | `P = □` | `P = □` |
| `pskl_ty_core` | `prop_ty_core.v:639` | `mode → pskl → ptyp` | — | `P = ⌊A⌋`, out `A` |
| `ptyp_ty_core` | `prop_ty_core.v:647` | `mode → ptyp → ptyp` | — | out `= A` |
| `fn_arrow_shape_pskl` | `prop_ty_core.v:1215` | `mode → pskl` | `True` | `True` |
| `fn_arrow_shape` | `prop_ty_core.v:1224` | `mode → ptyp` | `True` | `True` |

Every one of the eight repeats the same `__fn` row verbatim.

Three separate problems:

**(a) Argument order is inconsistent.**  `mod_comp_ty : btyp -> mode` puts the
subject first; every algorithmic counterpart puts the mode first.  Same concept,
opposite convention, 106 combined call sites.  Naming is inconsistent too:
`mod_comp_ty` / `mod_comp_sk` vs `a_ty_mode_compat` / `a_sk_mode_compat` — the
words are in the other order *and* the decl pair has no `d_` prefix while
living in the shared `fresco/def_shapes.v`.

**(b) `fn_arrow_shape` and `fn_arrow_shape_pskl` are the same relation.**
`fn_arrow_shape_of_pskl` (`prop_ty_core.v:1233`) proves one direction; the
converse is equally true.  Only 18 + 39 uses.

**(c) `fn_arrow_shape_pskl` is the *erasure* of both `mode_compat`s** — its base
rows are `True`.  So `a_ty_mode_compat M P → fn_arrow_shape_pskl M P` and
`a_sk_mode_compat M P → fn_arrow_shape_pskl M P` both hold and, from the lemma
names, are being re-derived where needed rather than stated once.

### Recommendation

**(A, do now)** Fix (b): delete `fn_arrow_shape` and define
`fn_arrow_shape M A := fn_arrow_shape_pskl M (ptyp_to_pskl A)`, keeping
`fn_arrow_shape_of_pskl` as the intro/elim pair.  57 call sites, all in
`prop_ty_core.v` + `prop_completeness_typing.v`.  Low risk.

**(B, worth it)** Fix (a): flip `mod_comp_ty`/`mod_comp_sk` to mode-first and
rename to `d_mod_comp_ty`/`d_mod_comp_sk`, or rename the algo pair to
`a_mod_comp_ty`/`a_mod_comp_sk`.  106 call sites, purely mechanical, the
compiler catches every miss.  Pick one word order and one argument order for
the whole tree.

**(C, only if you want the payoff)** Fix (c) by introducing the common core:

```coq
(* peel FN-depth(M) arrows off P, leaving P'. *)
Inductive mode_spine : mode -> pskl -> pskl -> Prop :=
| mode_spine__ti  : forall P,       mode_spine mode_ti P P
| mode_spine__tc  : forall P,       mode_spine mode_tc P P
| mode_spine__fn  : forall M P Q R, mode_spine M Q R ->
                    mode_spine (mode_fn M) (pskl_arrow P Q) R.
```

then `fn_arrow_shape_pskl M P := ∃P', mode_spine M P P'`,
`a_sk_mode_compat M P := mode_spine M P □`,
`a_ty_mode_compat M P := ∃P', mode_spine M P P' ∧ (base-of M = TI → P' = □) ∧
(base-of M = TC → ∃A, P' = ⌊A⌋)`, and
`pskl_ty_core M P A := mode_spine M P ⌊A⌋ ∧ base-of M = TC`.  Every `__fn`-row
induction in the tree collapses into one lemma about `mode_spine`.  **Risk:**
261 combined call sites and every `inversion` on the four algo predicates
changes shape.  Real payoff, real cost — schedule it, don't slip it in.

---

## 5. coercions, predicates — the canonical chain

### 5.1 The conversion functions are not all in `coercions.v`

`fresco/coercions.v` defines 14 conversions + `dbind_to_pskl` and declares 4
`Coercion`s (`utyp>->btyp`, `btyp>->ptyp`, `bskl>->pskl`, `uskl>->bskl`).  But:

| function | defined in | note |
|---|---|---|
| `ptyp_to_bskl_syn` | `algo_decl/def_consis_refine.v:38` | `= pskl_to_bskl_syn ∘ ptyp_to_pskl` |
| `ptyp_to_uskl_syn` | `algo_decl/def_consis_refine.v:40` | `= bskl_to_uskl ∘ ptyp_to_bskl_syn` |
| `pskl_to_uskl`, `uskl_to_pskl` | `algo_decl/` + `deco_algo/` | ~20 lemmas about them there |

So the canonical chain is split across `fresco/coercions.v` and
`fresco/algo_decl/def_consis_refine.v`, and a reader looking for "how do I get
from `ptyp` to `uskl`" finds two of the three answers in the wrong file.

### 5.2 Two conversions are dead

- **`pskl_to_dskl`** (`coercions.v:295`) — **zero** uses outside `coercions.v`,
  yet it carries two proved lemmas (`_open_rec`, `_open`).  Its docstring says
  it is "used to instantiate a poly source ∀ at the argument pattern"; whatever
  used it is gone.  (A) Delete, or say in the comment what it is being kept for.
- **`uskl_to_bskl`** — zero *explicit* uses, but it is a declared `Coercion`, so
  it fires implicitly.  Fine; flag only so nobody deletes it on a grep.

### 5.3 Composites are spelled out inline instead of named

| chain | inline occurrences | named composite? |
|---|---|---|
| `pskl_to_bskl_syn (ptyp_to_pskl A)` | **35** | yes — `ptyp_to_bskl_syn`, unused at those 35 sites |
| `pskl_to_bskl_inh (ptyp_to_pskl A)` | **32** | **no** |
| `btyp_to_bskl (ptyp_to_btyp_syn A)` | 16 | no (and see 5.4) |
| `bskl_to_uskl (pskl_to_bskl_* …)` | 11 | partly (`ptyp_to_uskl_syn`) |
| `bskl_to_pskl (pskl_to_bskl_* …)` | 11 | retraction, see 5.5 |

**Recommendation (B).**  Define the missing composites (`ptyp_to_bskl_inh` at
minimum), put all of them in `coercions.v`, and sweep the 90-odd inline chains
to the names.  Mechanical; makes the rule statements much shorter.

### 5.4 There are two routes `ptyp → bskl` and the square is proved twice, far apart

`btyp_to_bskl ∘ ptyp_to_btyp_syn` and `pskl_to_bskl_syn ∘ ptyp_to_pskl` are
equal, and the tree proves it — but the `syn` case lives at
`algo/prop_soundness_pat.v:900` and the `inh` case at
`algo/prop_soundness_typing.v:72`, two files that have no reason to own a
commuting square.  The retractions (`bskl_to_pskl_pskl_to_bskl_{syn,inh}`,
`btyp_to_ptyp_ptyp_to_btyp_{syn,inh}`) are in `fresco/prop_basic.v`; the
`_open`/`_open_rec` squares are split between `coercions.v` and `prop_basic.v`;
`uskl_to_pskl_pskl_to_uskl` is in `deco_algo/prop_decorate.v:50`.

**Recommendation (A/B).  This is the single best cleanup in the report.**
Create `fresco/prop_coercions.v` holding, for the six sorts, exactly:
retractions, `open`/`open_rec` commutations, `subst` commutations, `lc`
transport, `ftvar` transport, and the composite squares.  Then `coercions.v` is
definitions only and `prop_basic.v` is predicates only.  It also fixes five of
the duplicated names in §8 at the same time (`bskl_to_pskl_open{,_rec}`,
`ptyp_to_pskl_open_rec`, `pskl_to_bskl_syn_open_rec`, `btyp_to_ptyp_open{,_rec}`,
`ptyp_to_btyp_inh_open`, `ptyp_to_pskl_ghost_free`, `ptyp_to_pskl_lc`,
`mono_ptyp_to_pskl_lc`).

### 5.5 The predicate layer

`fresco/def_shapes.v` holds 6 `guarded_*` (one per sort), 5 `is_*` colour
predicates, `mono_ptyp`, `nonghost_pskl`, `is_value`, and 2 `*_ghost_free`
`Fixpoint`s.  This is well organised.  Two notes:

- **`guarded_ptyp` is dead** — its only occurrences are its own 4 definition
  lines (`def_extra.v:161-164`) and the `Hint Constructors` line at `:298`.
  The three apparent uses in `prop_sub_msubst_equiv.v` /
  `prop_completeness_sub_gen.v` are a **name collision**: the lemma
  `guarded_ptyp_to_uskl_syn` concludes `guarded_uskl (ptyp_to_uskl_syn τ)` and
  has nothing to do with the predicate.  (A) Delete `guarded_ptyp`, and rename
  that lemma to `ptyp_to_uskl_syn_guarded` — the current name reads as a fact
  *about* `guarded_ptyp`, which is exactly backwards.
- `pskl_no_ghost` is defined **twice** and neither copy is in `def_extra.v` where
  the other ghost predicates live — see §8.1.

---

## 6. `ty_core`

`algo/prop_ty_core.v` (1310 lines) declares itself as "two families".  It is
actually **four**:

| lines | cluster | belongs here? |
|---|---|---|
| 45-500 | `a_rigid_only` + its 12 structural lemmas + preservation through every judgement | ✅ yes, this is the file's thesis |
| 639-1100 | `pskl_ty_core` / `ptyp_ty_core` + `a_typing_ty_core` + `a_typing_tc_rigid_output` | ✅ yes — this is the "TY sort discipline pays out" claim |
| 1104-1210 | ghost-free-output kit (`a_consis_ghost_free_output`, `a_sub_ty_ghost_free_output`, `bskl_to_pskl_btyp`, `pskl_to_bskl_inh_ptyp`) | ~ acknowledged in the header as "also here, same theme"; defensible |
| **1215-1300** | **`fn_arrow_shape*`** | ❌ **no** — a pure arrow-spine shape fact with nothing to do with rigidity or the TY sort |

Also stranded here: `a_assign_flex_tvar:688` (a one-line fact about `a_assign`
that belongs in `prop_flex.v` or `prop_stability.v`) and
`a_split_rigid_var_absurd:713` (fine — it *is* about rigidity).

**Recommendation (A).**  Move `fn_arrow_shape*` out — into `prop_ty_shape.v`,
or, if §4's `mode_spine` refactor happens, straight into that file.  Move
`a_assign_flex_tvar` down to the flex layer.  Both are relocations with no
statement change.

---

## 7. metavar names (`ptyp` `btyp` `utyp` `pskl` `bskl` `uskl`)

The declared convention (`language.ott`) is `A : ptyp`, `B : btyp`, `C : utyp`,
`P : pskl`, `Q : bskl`, `R : uskl`, with `τ`/`σ` for monotypes and `ψ` for
instantiations.

### 7.1 ⚠ A generated name is wrong at the ott level

`language.ott` `substitutions` block:

```
  single Q Xbs  :: subst_bskl_in
  single R Xus  :: subst_bskl_in      <-- should be subst_uskl_in
```

so lngen generates **`subst_uskl_in_uskl`** — "substitute a *bskl* in a
`uskl`" — for what is `uskl`-into-`uskl` substitution
(`def_ott.v:487`: `(R_5:uskl) (α5:usklvar) (R__6:uskl)`).  Every other sort is
named correctly (`subst_ptyp_in_ptyp`, `subst_btyp_in_btyp`, …).

**Cost:** 661 occurrences tree-wide, 540 of them in hand-written files.  But the
name is unique, so it is a one-line ott edit + `make ott lngen` +
`sed -i 's/subst_uskl_in_uskl/subst_uskl_in_uskl/g'` over `fresco/`.  Grade **B**
— wide but the compiler verifies it completely.

Also in that block: `single e Xpt :: subst_typ_in` is **inert** — ott takes the
earlier `single A Xpt :: subst_ptyp_in` and generates `subst_ptyp_in_exp`
(`def_ott.v:544`); no `subst_typ_in*` constant exists.  (A) Delete the dead line
or rename it to `subst_ptyp_in` for honesty.

### 7.2 Wrong letters inside rule definitions

The worst offender is the `ad_pat_sub_{g,gv}` family, where the *rule text
itself* uses `T` for a `uskl` and `B` for a `pskl`:

```coq
| ad_pat_sub_g__check : forall n Ψ Θ T B,        (* T : uskl, B : pskl *)
    guarded_uskl T -> guarded_pskl B ->
    Ψ ⨟ Θ ⊢ᵃᵈ T ∼ (pskl_to_bskl_inh B) -> …
```

Tree-wide idiom counts against the convention:

| idiom | count | should be |
|---|---|---|
| `pskl_to_bskl_inh B` | 24 | `… P` |
| `ptyp_to_pskl B` | 20 | `… A` |
| `ptyp_to_pskl Bc` | 16 | `… A…` |
| `pskl_to_bskl_syn Q` | 9 | `… P` |
| `pskl_to_bskl_inh X` | 8 | `… P` |
| `bskl_to_pskl P`, `bskl_to_pskl B` | 4 | `… Q` |

Explicitly annotated binders that violate the convention: **34** (`b : uskl` ×8,
`ψa : uskl` ×5, `τ : ptyp` ×5, `q : pskl` ×3, `Q : pskl` ×3, `C : ptyp` ×2,
`Rt : utyp`, `Rint : ptyp`, `Rb : btyp`, `A : pskl`, …).

**Recommendation.**  Split by grade:
- **(A)** Fix the ~10 annotated binders that are outright wrong (`R : ptyp`,
  `C : ptyp`, `A : pskl`, `Rb : btyp`, `Rt : utyp`) — these actively mislead.
- **(B)** Rename `T`→`R` and `B`→`P` in the `ad_pat_sub_*` rule definitions and
  their lemma statements.  Alpha-renaming inside a definition is safe, but note
  that `ad_pat_sub_g__check`'s *constructor arguments* are positional, so
  `apply ad_pat_sub_g__check with (T := …)` call sites break loudly.
- Note `τ : ptyp` (×5) is **not** a violation — `τ` is the monotype convention.
  Worth one line in `AGENTS.md` so a future sweep does not "fix" it.

---

## 8. file / lemma names, restructure

### 8.1 ⚠ 82 duplicated top-level names (2.8% of 2945)

Coq permits this — each file is its own module — but it means `apply foo` can
resolve to a *different* `foo` depending on import order.  The full list is
reproducible with:

```sh
find fresco -name '*.v' ! -name 'prop_ln.v' ! -name 'def_ott.v' -exec \
  grep -HnE "^(Lemma|Theorem|Corollary|Definition|Fixpoint|Inductive) " {} + \
| sed -E 's/^([^:]+):([0-9]+):[A-Za-z ]+ +([A-Za-z_0-9'"'"']+).*/\3\t\1:\2/' \
| sort | awk -F'\t' '{c[$1]++; l[$1]=l[$1]" "$2} END{for(n in c) if(c[n]>1) print n, l[n]}'
```

Two are **duplicated definitions**, not just lemmas — the more serious case,
because lemmas proved about one copy do not `apply` to the other:

- **`pskl_no_ghost`** — the identical 9-line `Fixpoint` at
  `algo/prop_completeness_consis.v:1047` **and**
  `algo/sub/look/prop_kit.v:6381`, each with its own satellite lemmas
  (`ptyp_to_pskl_no_ghost` is duplicated too).  `prop_kit.v` **imports**
  `prop_completeness_consis.v`, so the second shadows the first.
- **`msubst_lc`** — `deco_algo/prop_decorate_sub.v:173` and
  `algo/prop_normal.v:143`.

**28 of the 82 involve the `completeness_look/` cluster**, and this is exactly
what blocks the facade that is already written.
[algo/prop_completeness_look.v](../fresco/algo/prop_completeness_look.v) says so
in its own header:

> ⚠️⚠️ **DO NOT point an existing consumer at this file yet.** … the algo layer
> currently has **20 names defined both inside this cluster and outside it** —
> 4 exact duplicates, ~9 alpha-variants, and ~5 that GENUINELY DIVERGE …
> `prop_completeness_sub_gen.v` broke exactly that way and is kept on piecewise
> imports.

My scan finds 28 rather than 20, and the header already names the five divergent
ones (`msubst_pskl_subst_var`, `a_wf_pskl_all_of_one`,
`pskl_to_bskl_inh_univ_ghost_inv`, `binds_weaken_mid`, `a_non_flex_rename`).

**Recommendation (B, highest value in this report).**  Work the 28.  For each:
identical → delete the later copy and import; alpha-variant → keep the stronger
and delete the weaker; divergent → **rename** so the difference is visible
(`…_paired` vs `…_curried`, etc.).  Payoff: `prop_completeness_look.v` becomes
the single import point it was written to be, and
`prop_completeness_sub_gen.v`'s 30-line piecewise import list collapses to one.
Then work the other 54 the same way.

### 8.2 ~50 generic helpers with no home

Metalib-shaped lemmas about `binds` / `uniq` / `dom` / `notin` / list `app` are
defined ad hoc in **20 different proof files**:

```
binds_insert_mid       ×2 (prop_soundness_consis.v, prop_completeness_sub_gen.v)
binds_weaken_mid       ×2 (prop_inc.v, sub/look/prop_kit.v)  ← different shapes
binds_strengthen_mid, binds_swap_mid, binds_swap_app, binds_rot_app,
binds_rot_app_rev, binds_app_perm5, binds_mid_drop, binds_mid_swap,
binds_permute_mid, binds_split_mid, binds_strip_mid, binds_app_mid,
binds_def_split, binds_strengthen, binds_sub_cons, uniq_app_of, uniq_mid_eq,
list_app_assoc, app_inj_tail_length, app_split_by_head_length, app_inj_prefix,
app_mid_inv, app_mid_uniq_split, in_dom_app_r, atoms_inter_empty_pointwise,
notin_add_atom, notin_union_both, notin_ftvar_* (×6), dom_* (×4), …
```

`fresco/ltac_utils.v` is 83 lines and holds only tactics; there is no
`fresco/prop_aenv.v`.

**Recommendation (B).**  Create `fresco/prop_aenv.v` (or extend `prop_basic.v`)
directly above the algo layer and move the sort-agnostic ones there.  This kills
3 more duplicated names and stops the next campaign from re-deriving
`binds_insert_mid` for the third time.

### 8.3 Large files that are already fusions

| file | lines | note |
|---|---|---|
| `algo/prop_completeness_consis.v` | 8830 | self-documented as PART A (ex-`prop_consis_exist.v`) + PART B (ex-`prop_consis_complete.v`) |
| `algo/prop_completeness_sub_gen.v` | 7536 | no internal PART banners at all |
| `sub/look/prop_kit.v` | 7030 | "the shared kit" — the grab-bag, and the source of most §8.1 duplicates |
| `algo/prop_completeness_typing.v` | 4638 | theorem 4 |
| `deco_algo/prop_soundness_sub.v` | 4208 | — |

**Recommendation (A).**  Do **not** split them for size — the facade file
already argues, correctly, that splitting a linear chain buys no parallelism and
costs rebuild granularity.  Instead: add PART banners to the two that lack them
(`prop_completeness_sub_gen.v`, `prop_kit.v`) so the fusion seams are visible.
`prop_kit.v` in particular should say which of its six consumers each block
serves — that is the information needed to eventually break it up.

### 8.4 Build litter and doc drift

**(A, five minutes.)**

- Orphan `.glob` with no `.v` in `mechanization/`: `scratch_audit.glob`,
  `scratch_dbg.glob`, `scratch_looksub.glob`, `scratch_mono.glob`.
- Hidden litter: `.probe1.aux` … `.probe9.aux`, `.scratch_thm4.aux`,
  `.scratch_chk.aux`, `.DS_Store`.
- These survive `make clean` (its `rm` list does not cover them).  Extend the
  `clean` target.
- Doc drift: `docs/HANDOFF-typ-all-plain-refactor.md` (May 17),
  `docs/PROPOSAL-ln-idiomatic-tags.md` (Jun 29),
  `docs/DESIGN-safe-pat-witness.md` (Jun 29) predate the type-hierarchy
  refactor.  Either mark them SUPERSEDED at the top or move them to
  `docs/archive/`.
- `paper/artifact/mechanisation/` carries a separate `fresco/` snapshot with its
  own `def_ott.v`, `predicates.v`, `coercions.v`, `decl/`.  Confirm it is a
  deliberate frozen artifact; if it is a stale copy it is a trap for grep.

---

## 9. Suggested order of work

**Phase 1 — free (grade A, no proof risk, ~half a day).**
1. §8.4 litter + `make clean` + mark 3 stale docs SUPERSEDED.
2. §1.4 delete the `a_typing_rename_tm` phantom from the header.
3. §5.2 delete `pskl_to_dskl` (+2 lemmas); check `guarded_ptyp`'s 3 uses.
4. §7.1 delete the inert `subst_typ_in` ott line.
5. §6 move `fn_arrow_shape*` and `a_assign_flex_tvar` out of `prop_ty_core.v`.
6. §1.2 move the nine K6 swap lemmas into `prop_swap.v`.
7. §3(a) + §7 add the two convention notes to `AGENTS.md` / `algo/def_rules.v`.

**Phase 2 — mechanical, compiler-verified (grade B, ~2-3 days).**
8. **§8.1 the 28 `completeness_look/` duplicates**, then flip
   `prop_completeness_sub_gen.v` to the facade.  Highest value.
9. §5.4 create `fresco/prop_coercions.v`; this closes ~8 more duplicates.
10. §8.2 create `fresco/prop_aenv.v`; closes 3 more.
11. §5.3 name the composite chains, sweep the ~90 inline uses.
12. §7.1 `subst_uskl_in_uskl` → `subst_uskl_in_uskl` (ott + sed, 540 sites).
13. §4(a) collapse `fn_arrow_shape` onto `fn_arrow_shape_pskl`.
14. §4(b) unify `mod_comp_*` / `*_mode_compat` naming and argument order.
15. §1.1 retire `rename_aenv`.
16. §7.2 `T`→`R`, `B`→`P` in the `ad_pat_sub_*` rules.

**Phase 3 — campaigns (grade C, schedule individually).**
17. §2.3 delete the `ad_pat_sub_n` mirror (cheapest C; try first).
18. §4(c) the `mode_spine` core.
19. §1.3 `a_pat_swap` / `a_typing_swap` (additive, so safe but not small).
20. §2.3 parameterise `_g`/`_gv` — **only** with thm:complete-subtyping in a
    branch.
21. §3(b) `a_pat` exists-fresh conversion — **only** with all four section-D
    theorems in a branch.

Nothing in Phase 1 or 2 changes a rule or a theorem statement.
