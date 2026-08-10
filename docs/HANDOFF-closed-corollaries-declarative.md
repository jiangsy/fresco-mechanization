Handover — Frost mechanization: state the CLOSED-PROGRAM COROLLARIES against
the PURELY DECLARATIVE system (`d_sd_typing` / `d_typing`), in BOTH
directions.  ⭐ THE GOAL IS FIXED BY THE USER: soundness *and* completeness
must read `Γ ⊢ˢ[ M ] e ⦂ B` (or `d_typing`), not `Θ ⊢ᵃᵈ[ M ] e ⦂ B`.  The
route is NOT fixed — the scouting below found one blocker, and finding a way
around it is the job.

READ FIRST: mechanization/CLAUDE.md (the turnstile legend, and the rule
"never change the paper's definitions… if the STATEMENT is genuinely false,
STOP and flag"); `frost/algo/typing/prop_closed.v` (the four corollaries as
they stand); `cex/cex_ad_pat_join_not_leaf_valid.v` END TO END — it is the
ground truth this hand-off is about; `paper/sections/appendices/full-algo-spec.tex`
§`app:decl-in-algo-context` (lines 95-128).

STATE.  Branch `remech`; `make coq` green, admit-free, axiom-free; 24/24
`Print Assumptions` closed.  `frost/algo/typing/prop_closed.v` holds

    a_typing_sound_infer / a_typing_sound_check
    a_typing_complete_infer / a_typing_complete_check

all four at the EMPTY context, with the declarative side stated as
`ad_sd_typing` (`Θ ⊢ᵃᵈ[ M ] e ⦂ B`, decorated_algo/def_decl_algo_typing.v).

## WHAT THE GOAL IS

Restate all four so the declarative side is `d_sd_typing` (`Γ ⊢ˢ[ M ] e ⦂ B`,
decl/def_extra.v:711) or `d_typing` (:643), over a DECLARATIVE context.  At
the empty context that means `· ⊢ˢ[ M ] e ⦂ B`.

## WHAT THE SCOUTING FOUND (2026-08-10) — read before choosing a route

### 1. The paper does NOT connect the two systems; it asserts the extension

`app:decl-in-algo-context`: *"Although all the declarative judgements … are
defined on declarative contexts Γ, **it is easy to extend them to algorithmic
contexts Θ**. For most rules we simply replace declarative contexts Γ with
algorithmic contexts Θ… other rules simply switch from Γ to Θ."*

There is **no conservativity lemma** in the paper — nothing says a derivation
over a flexible-free Θ corresponds to a declarative one over Γ, in either
direction.  So the mech's `⊢ᵃᵈ` statement IS the paper's statement, and what
this hand-off wants is the paper's own unstated "it is easy", made real.
⭐ Whatever comes out of this is a PROSE-COMPLETION for docs/PAPER-GAPS.md.

### 2. ⚠️ THE BLOCKER, completeness direction: the LEAF-VALID datum

`cex/cex_ad_pat_join_not_leaf_valid.v` (its own headline):

> THE EMBEDDED SUBTYPING PREMISE OF `ad_pat` / `ad_sd_typing` IS NOT
> LEAF-VALID, SO thm:complete-skeleton-inference AND
> thm:complete-type-inference CANNOT BE STATED OVER THE PLAIN JUDGEMENTS.

`ad_sd_typing`'s Unit/Var/Anno rows embed `ad_pat_sub_v` — the LEAF-VALID
join, carrying at every consistency leaf the subject-refinement datum
`Θ ⨟ ∅ ⊢ᵣₚᵃᵈ ⌊R⌋ˢ ⊳ ⌊Q⌋`.  `d_sd_typing`'s base rows embed plain `d_sub`,
which carries no such datum, and §1/§2 of that file machine-check that the
datum is NOT recoverable: at the capture configuration (subject `∀X.◇`,
counterpart `∀ˢX.X`) there is a plain join (`cap_plain`) and provably no
leaf-valid one (`cap_no_gv`; `cap_no_refine` is `forall Θ`, so it bites at
`nil` too).

Restating the COMPLETENESS premise needs exactly `d_sd_typing Γ e B →
ad_sd_typing ⌈Γ⌉ e B`, i.e. manufacturing leaf-valid joins from plain ones.
That is the refuted direction.

⭕ **OPEN, and the cheapest thing to settle first**: the cex's §3 reaches the
configuration through `ad_pat`'s P-Var at a SKELETON entry `x : ∀X.◇`.
`ad_sd_typing`'s Var rule reads `abind_var_typ A` — a `ptyp`, which has no
ghosts — so that witness does not transfer to TYPING directly.  Whether the
configuration is reachable for `ad_sd_typing` at an empty top-level context
(via App's `ad_pat` premise and the abs rows, which do push skeleton entries)
is NOT settled.  A witness kills route R1 below; failing to find one makes it
plausible.

### 3. Soundness has a SEPARATE obstacle: the output context keeps flexibles

`a_typing_sound_*`'s conclusion lives at the run's OUTPUT context `Θ1`, which
normally still holds flexibles — `fun x -> x` gives `Θ1 = α̂` and answer
`α̂ → α̂`.  So a declarative statement must close them off:

    forall ζ, ζ ∷ Θ1 ⊑ nil -> · ⊢ˢ[ m ] e ⦂ (msubst_btyp ζ Bt)

⭐ Head start: `algo/prop_suffix_erase.v` already pushes ONE flexible through
`ad_sd_typing` (`ad_sd_typing_subst_mid`, via `solves_flex`); iterating it
along an `a_inc` should give the closing.  This direction is `ad → d` at a
flex-free context and the cex does NOT touch it.

### 4. Changing the declarative system is expensive — know the price

If the leaf datum is put on `d_sd_typing`'s base rows, then

- `d_typing` must change too: it keeps `Sub` STANDALONE
  (`d_typing__sub`, decl/def_extra.v:652) where `d_sd_typing` folds it into
  the three base rows, and the two are proved equivalent
  (`d_sd_typing_complete`, prop_syntax_directed.v:1277; the
  `d_typing_general_subsumption` / `_spine` corollaries at :1361/:1369 are
  read off the sd side).  Strengthening only one breaks the equivalence.
- blast radius = all of `frost/decl/` (general subsumption + spine, the
  syntax-directed equivalence, order irrelevance, stability), i.e. Phase 2,
  currently admit-free — plus the paper's own §declarative figure.

### 5. The bridge itself does not exist AT ALL

- no `denv` ↔ `aenv` conversion anywhere (only `dbind_to_pskl`, coercions.v)
- no `d_wf_ptyp` ↔ `a_wf_ptyp` / `d_wf_pskl` ↔ `a_wf_pskl` bridges
- `Δ` is `list atom` on the `d` side and `atoms` on the `ad` side
  (`List.In α Δ` / `α :: Δ` vs `α ∈ Δ` / `add α Δ`)
- rule counts to translate: `d_refine_syn` 8 / `d_pat_consis` 13 /
  `d_pat_sub` 9 + `d_sub` 6 / `d_pat` 9 / `d_sd_typing` 11 ≈ 56 rows against
  `ad_refine_syn` 10 / `ad_pat_consis` 15 / `ad_pat_sub` 24 (ALL-IN-ONE — it
  covers both `d_sub` at TY and `d_pat_sub` at SK, dispatched on the `NM`
  index) / `ad_pat` 9 / `ad_sd_typing` 11 ≈ 69 rows
- ⭐ but the correspondence is RULE-FOR-RULE: the `ad` version is the `d`
  version plus the flexible-lookup rows, which are vacuous at a flex-free
  context.  Each translation should be a plain induction + binds transport.
- one more prerequisite either way: `a_tyequiv Θ A B → A = B` at a
  DEFINITION-FREE Θ (kills the four extra `≡ᵗ` premises `ad_sd_typing` has —
  Freeze, AbsAnnoCheck, AbsAnno, App).

## ROUTES TO TRY — the new session should re-think these, not just execute

**R0 (do this first, it is cheap).**  Settle §2's open question: is the
capture configuration reachable for `ad_sd_typing` at an empty top-level
context?  Either build the witness (a closed `e` and a `B` with
`nil ⊢ᵃᵈ[M] e ⦂ B` whose base row's join is not leaf-valid) or prove it is
not.  Everything below branches on the answer.

**R1 — restricted bridge.**  If R0 says unreachable at a closed program,
prove `d_sd_typing nil e B → ad_sd_typing nil e B` for CLOSED `e` only, and
both corollaries go through with no change to any system.  ⚠️ Watch the
sub-derivations: the abs rows push term entries and the ∀ rows push rigids,
so the induction hypothesis is at a NON-empty context — the statement will
have to be "at a context whose skeleton entries are ghost-free", or whatever
invariant actually makes the leaf datum derivable.  Finding that invariant IS
the interesting part.

**R2 — the leaf datum as a SIDE CONDITION, not a rule change.**  Keep
`d_sd_typing` exactly as the paper has it and state completeness as
`d_sd_typing Γ e B` PLUS a separate leaf-validity hypothesis, in the
WF-SIDE-CONDITIONS.md style the tree already uses for external conditions
(docs/WF-SIDE-CONDITIONS.md).  Cheapest route that keeps the paper's system
untouched; the cost is that the corollary carries one more premise, so weigh
it against R1.

**R3 — a leaf-valid declarative twin.**  Define `d_sd_typing_v` (the paper's
system with `d_pat_sub_gv`-style leaf data), prove `d_sd_typing_v ⇄
ad_sd_typing` at flex-free contexts, and state completeness over it.  Paper's
own system untouched; the extra judgement is explicit and its relation to
`d_sd_typing` is a separate, statable question.

**R4 — strengthen the paper's declarative system.**  §4's price.  Only if
R0-R3 all fail; and it is an author-facing decision, not a mech one.

**Soundness** is independent of all four: it needs `ad → d` at a flex-free
context plus §3's closing `ζ`, and can be landed FIRST, on its own.

## ACCEPTANCE

- all four corollaries in `frost/algo/typing/prop_closed.v` read `⊢ˢ` (or
  `d_typing`) on the declarative side
- `make coq` exit 0, every `Print Assumptions` "Closed under the global
  context", zero Axioms/Parameters/Variables/Admitted
- README.v's four `Check`s updated (it is the only consumer of prop_closed.v)
- whatever the bridge turns out to be, registered in docs/PAPER-GAPS.md as
  the prose-completion of `app:decl-in-algo-context`'s "it is easy to extend"
- ⚠️ if a route requires changing `d_sd_typing` / `d_typing`, STOP and ask —
  §4 shows it reaches the paper and all of Phase 2
