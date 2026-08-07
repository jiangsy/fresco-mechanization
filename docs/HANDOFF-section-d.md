# HANDOFF — section D (`proofs.tex`): soundness and completeness of skeleton and type inference

**Status 2026-08-06 (SEVENTH pass).**  Theorem 2
(`thm:sound-type-inference`) has FOUR of its five prerequisites CLOSED, all
Qed and axiom-free:

| # | prerequisite | where |
|---|---|---|
| 1 | `ad_sd_typing_mod_comp_ty` | `prop_soundness_typing.v` §8 |
| 2 | `lemma:suffix-erasure`, all six judgements | NEW `prop_suffix_erase.v` |
| 3 | `lemma:split-refine`, COLOURED | `prop_soundness_typing.v` §11 |
| 4a | `AT-App`'s `≡ᵗ` step | ✅ resolved by ADDING THE PREMISE |
| 4b | `AT-Abs`'s `guess^TY` refinement | `prop_soundness_typing.v` §9 |
| 5 | the eleven-row induction | ⛔ **THE ONE LEFT** |

⭐ **4a was a MISSING APPENDIX PREMISE, not a missing lemma.**
`ad_sd_typing__app` now carries `Θ ⊢ (btyp_to_ptyp B1) ≡ᵗ A2` beside
`Θ ⊢ˢᵃ[TC] e2 ⦂ inh{A2}` — the appendix's own idiom, applied to the fourth
rule that needs it (docs/PAPER-GAPS.md).  The mech's `AT-App` case will
discharge it from `ad_refine_syn_inh_tyequiv` (§2), the same lemma `Freeze`
uses.  ⚠️ This CHANGES A RULE; if the authors prefer `sd-App` unchanged,
the repair to revert to is the `ad_pat_consis` TARGET transport along `≡ᵗ`
(both directions at once, nested induction — the mirror of
`skl_tyequiv_consis_transport`) PLUS a mode-indexed generalization over a
new colour-preserving `btyp` equivalence, because `sd-App`'s conclusion
type is the function's CODOMAIN.


**Status 2026-08-06 (fifth pass).** The definitional layer is DONE
(`dd1f176`), suffix MOVING is closed (`prop_ctx_mono.v`), and ⭐⭐⭐
**thm:sound-skeleton-inference is CLOSED**: `a_pat_sound`
(`algo/prop_soundness_pat.v` §5) is Qed over all ten `a_pat` rows and *Closed
under the global context* — no admits, no axioms — and it is `Check`ed and
audited in `README.v`.  The last open piece, AbsAnno's refinement-target
transport, is now `a_consis_chk_annot_refine` (§4), which supplies a lemma the
paper asserts inline and never states (docs/PAPER-GAPS.md).  §7 records the
proved statement, the kit, and the design that made the transport go through.
Headlines discovered while building it:

- ⭐ **Theorem 1 needs NEITHER lemma:split-refine NOR refinement
  transitivity** (`a_split_sk_shape`, prop_soundness_pat.v §3b): under the
  judgement's own `skmod{SK}` side condition the split can only be the ARROW
  or HOLE row — `a_sk_mode_compat` has no rule for a flexible input, so the
  flex row (§2's hard case) is reachable only from TYPE inference.  At the
  arrow shape the composed refinement is one `__arrow` of a reflexivity and
  the IH; at the hole shape one `__hole` over the IH's syn-painting inversion
  (`ad_refine_syn_syn_l` at `P := pskl_hole` + `ad_refine_syn_hole_l_target_wf`).
- ⭐ **The paper's "stability" is not free, and the repair is the
  TM-VERBATIM invariant**: `⊴` preserves a term entry only up to `≡ᵗ`
  (`a_inc__var`), so `ad_pat` does not transport along `⊴` alone.  What the
  paper leaves implicit is that the algorithm NEVER rewrites a term entry;
  both directions are now proved for the whole cluster (forward
  `*_tm_le` in prop_stability.v; reverse `*_tm_ge` in prop_soundness_pat.v),
  and `ad_pat_isub_tm` = stability under `⊴` + tm-verbatim.
- ⚠️ **`a_wf_aenv` under-approximates the paper's `Θ ⊢ ctx` at skeleton
  term entries** (`a_wf_aenv__var` stores only `a_scope_pskl`, the paper's
  figure requires `Θ ⊢ P`).  The `AP-Var(skl)` case must feed the entry to
  `a_sub_sound_thm`, which demands the DISCIPLINED `⊢ₚₛᵃ` — so the theorem
  carries the paper's implicit condition as a hypothesis
  (`forall x P, binds x (abind_var_skl P) Θ0 -> Θ0 ⨟ ∅ ⊢ₚₛᵃ P`), sustained
  through the induction by tm_le/tm_ge + `a_wf_pskl_isub`.
  WF-SIDE-CONDITIONS.md pattern; do NOT change the `a_wf_aenv` rule
  mid-campaign.

⚠️ **The paper marks three of these lemmas "straightforward induction".  In the
mechanization they are not**, for reasons recorded per-lemma below.  Read those
before estimating.

---

## 0. What the layer gives you

| Coq | notation | paper |
|---|---|---|
| `ad_pat M Θ e Q` | `Θ ⊢ᵃ[ M ] e ⇨ Q` | `\patp[\M]{\Theta}{M}{\bid{Q}}` |
| `ad_sd_typing M Θ e B` | `Θ ⊢ˢᵃ[ M ] e ⦂ B` | `\typp[\M]{\Theta}{M}{\bid{A}}` |
| `a_pat m Θ0 P0 e P Θ1` | `Θ ⊢ₐ[ m ; P0 ] e ⇨ P ⊣ Θ'` | fig:alg-skeleton-inference |
| `a_typing m Θ0 P0 e A Θ1` | `Θ ⊢ₐ[ m ; P0 ] e ⦂ B ⊣ Θ'` | fig:alg-type-inference |
| `a_split Θ P0 P Q Θ'` | `Θ ⊲ P0 ▹ P ⇢ Q ⊣ Θ'` | `\split` |
| `ad_precise Θ Δ P Q` | `Θ ⨟ Δ ⊢ₚᵣᵃ P ⊑ Q` | `\precise{P}{Q}` — **LEFT is the more precise one** (checked against `ad_precise_preserves_refine`) |

The appendix's own reason for adding no new rule to either judgement: new rules
are needed only where a FLEXIBLE variable can appear, and neither judgement
looks a type variable up directly — every type-level lookup happens inside the
embedded subtyping / consistency / refinement premises, which already carry
their flexible rows.  What IS carried are the appendix's three explicit
`Θ ⊢ _ ≡ᵗ _` premises on `sd-Freeze`, `sd-AbsAnnoCheck`, `sd-AbsAnno`.

---

## 1. `lemma:suffix-moving` ✅ + `lemma:suffix-erasure` ⛔ — moving was free, ERASURE is the big one

    (* moving:  Θ1,Θ2,Ξ  ⟹  Θ1,Ξ,Θ2   — mech lists grow at the FRONT,
       so the paper's [Θ1,Θ2,Ξ] is [Ξ ++ Θ2 ++ Θ1] in Coq *)
    Lemma ad_sd_typing_suffix_moving : forall M Θ1 Θ2 Ξ e B,
      (Ξ ++ Θ2 ++ Θ1) ⊢ˢᵃ[ M ] e ⦂ B ->
      <Ξ does not depend on Θ2> ->
      (Θ2 ++ Ξ ++ Θ1) ⊢ˢᵃ[ M ] e ⦂ B.

    Lemma ad_sd_typing_suffix_erasure : forall M Θ Ξ e B,
      (Ξ ++ Θ) ⊢ˢᵃ[ M ] e ⦂ B ->
      <Ξ fresh for B> ->
      Θ ⊢ˢᵃ[ M ] e ⦂ B.

✅ **MOVING IS CLOSED** and cost almost nothing: `ad_sd_typing_suffix_moving`
/ `ad_pat_suffix_moving` (prop_ctx_mono.v) fall out of
`aenv_binds_le_perm3`, because permuting context BLOCKS changes no `binds`
fact at all — so no dependency relation is needed for it, and item 1 below
never bit.

⛔ **ERASURE IS THE OPEN ONE, and the paper's "straightforward induction on
the typing derivation" does not go through.**  Scouted 2026-08-06; see
docs/PAPER-GAPS.md, "`lemma:suffix-erasure` is NOT a straightforward
induction".

1. **The obstruction is `ad_pat_sub`'s `ForallL` row.**  It instantiates
   with a decorated skeleton `ψ` the rule chooses freely — the only
   conditions are `a_tags_sort NM Ψ' ψ` and `Θ ⨟ ∅ ⊢ₚₛᵃ ⌊ψ⌋ˢ`, and
   `is_tskl__var` admits a `ψ` that mentions `Ξ`.  The recursive premise is
   then at `open R ψ`, which is NOT Ξ-fresh, so the IH does not apply even
   though the conclusion is.  Reachable: with `α̂ ∈ Ξ` DEFINED (its
   definition is a monotype scoped in Θ by wf), `∀a. a → 1 ⩽ Q` goes
   through `ψ = α̂` with an entirely Ξ-free `Q`.  Every OTHER way into Ξ
   surfaces in the types — the FlexL/FlexR lookups and the rigid rows all
   put the variable in the subject or the target.
   ⚙ **The tree already knew this, one layer down.**
   `ad_pat_sub_strip_suffix` (algo/prop_pat_sub.v) IS this lemma for
   `ad_pat_sub`, and `ad_pat_sub_subst_flex`'s header says why in one line:
   "the ForallL witnesses are rewritten too, which is exactly why this is
   provable where naive strengthening is not".  ⭐ **REUSE IT**, and reuse
   its whole `_subst_mono` closure family (`is_tskl_subst_mono`,
   `a_tags_sort_subst_mono`, `uskl_ghost_free_subst_mono`,
   `mod_comp_sk_subst_mono`, `guarded_*_subst_mono`, `is_sskl_subst_mono`,
   `uskl_to_pskl_subst_mono`, `pskl_to_bskl_inh_subst_mono`).
2. **The route that works: erase by SOLVING, not by dropping** — 🟡 BUILT,
   `algo/prop_suffix_erase.v` (§1–§7, Qed, axiom-free).  A flexible suffix
   always admits a monotype per entry (undefined `α̂ ↦ 1`, defined `α̂ ↦`
   its own definition, which is tail-scoped by wf), so each judgement gets

       Θa,α̂,Θ0 ⊢ J   ⟹   [τ/α̂](Θa,Θ0) ⊢ [τ/α̂]J

   and the paper's form follows because the substitution is the identity on
   Ξ-free types.  At `ForallL` the instantiation becomes `[τ/α̂]ψ`, still
   `is_tskl` + ghost-free + same tags, because τ is a monotype.
   ⭐⭐ TWO DESIGN POINTS that make the rows COLLAPSE instead of needing
   transports: (a) `solves_flex` demands τ to BE the definition, not merely
   be equivalent to it — then the FlexL/FlexR/flex_def rows' subject and
   unfolding become the SAME term and the row disappears; (b) the
   substitution is applied to the WHOLE remaining context, not just the
   prefix above α̂ — leaving the tail alone is sound but needs an "α̂ does
   not occur here" argument at EVERY lookup row, whereas substituting
   uniformly is discharged ONCE, at the driver (`subst_aenv_fresh_eq` +
   `a_wf_aenv_ftv_dom`).
3. **The induction is not over one judgement.**  `ad_sd_typing` embeds SIX
   different premise forms — `ad_pat_sub` at `a_sub_mode_ty`, `ad_pat`,
   `ad_refine_syn`, `a_wf_ptyp`, `a_tyequiv`, `mod_comp_ty` — and each needs
   its OWN erasure lemma before the typing induction can close a single base
   rule.  `mod_comp_ty` is context-free, so five kits, not six.

   | judgement | transport | driver |
   |---|---|---|
   | `a_wf_ptyp` / `a_wf_pskl` | ✅ §3 | (used inline) |
   | `a_tyequiv` | ✅ §4 | ✅ §7 |
   | `ad_refine_syn` | ✅ §5 | ✅ §7 |
   | `ad_pat_consis` | ✅ §6 | (via `ad_pat_sub`'s) |
   | `ad_pat_sub` | ✅ prop_pat_sub.v | ✅ prop_pat_sub.v |
   | `ad_pat` | ⛔ | ⛔ |
   | `ad_sd_typing` | ⛔ | ⛔ |

   ⚠️ The two remaining ones need `ad_pat_sub_subst_mid` in the
   SUBSTITUTED-CONTEXT style: prop_pat_sub.v's `ad_pat_sub_subst_flex_def`
   concludes at the UN-substituted `Θ1 ++ Θ2` (with an extra "no definition
   in the tail mentions β" hypothesis), and that shape does not compose
   with `ad_pat`/`ad_sd_typing`, whose binder rows push TERM entries whose
   payloads the substitution changes (`ad_pat__abs_anno` pushes
   `x : A` for the term's own annotation, which the substitution rewrites).
   Also note the subject is an EXPRESSION, so `subst_ptyp_in_exp` enters.

---

## 2. `lemma:split-refine` — NOT a straightforward induction (⚠ now TYPE-inference-only: theorem 1 does not use it, see §7)

    Lemma a_split_refines : forall Θ0 P0 P Q Θ1,
      Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 ->
      Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->          (* EXTERNAL wf, see below *)
      Θ1 ⨟ empty ⊢ᵣₚᵃ P0 ⊳ (pskl_arrow P Q).

Two of the three rows are easy; the third is a genuine proof.

- `a_split__arrow` (`P0 = P → Q`, `Θ1 = Θ0`) — `ad_refine_pskl_refl`
  (prop_refine.v:177), whose premise `Θ ⨟ Δ ⊢ₚₛᵃ P` is why the statement needs
  the EXTERNAL wf side condition above.  That is the documented pattern, see
  `docs/WF-SIDE-CONDITIONS.md`; the paper supplies it in prose.
- `a_split__hole` (`□ ▹ □ ⇢ □`) — `ad_refine_pskl__hole` + `a_wf_pskl__arrow`
  of two `a_wf_pskl__hole`s.
- ⛔ `a_split__flex` — the row's premise is a **full `a_consis` run**, not a
  syntactic step.  (The paper writes it `unify{α̂}{β̂ → α1̂}`, but that `∼` is
  CONSISTENCY, not `unifyvar`: `unifyvar`'s subjects are hatted variables and
  the input here is an ARROW — see the `[paper-gap]` note on the rule in
  `algo/def_extra.v`.)  To reach `Θ1 ⨟ ∅ ⊢ᵣₚᵃ α̂ ⊳ (β̂ → α1̂)` you must

  1. invert that run.  Only `a_consis__flex_l` can fire (subject `α̂` flexible,
     `P0 = β̂ → α1̂` non-flex), which hands back
     `((α1~flex) ++ (β~flex) ++ Θ0) ⊲[nil] α ≔ (β̂ → α1̂) ⊣ Θ1`;
  2. read α's DEFINITION out of that assignment — `ad_refine_pskl__flex_l`
     needs exactly `binds α (abind_flex_mono_def τ) Θ1` together with
     `Θ1 ⨟ ∅ ⊢ᵣₚᵃ (ptyp_to_pskl τ) ⊳ (β̂ → α1̂)`.  ⚠️ τ is NOT syntactically
     `β̂ → α1̂`: the assign walk's skip rows may have moved/refreshed entries,
     and β̂ / α1̂ may themselves have been defined along the way.

  ⭐ **THE ROUTE FOR STEP 2, scouted 2026-08-06** — do not go via
  `a_consis_sound`'s refinement conjunct, which is useless here: at
  `a_consis__flex_l` the run's OUTPUT is the subject itself (`Q = α̂`), so that
  conjunct degenerates to `α̂ ⊳ α̂`.  Go through the ASSIGNMENT instead.

  `a_assign_sound` (prop_soundness_consis.v:4495) turns the row's
  `Θ0' ⊲[nil] α ≔ (β̂ → α1̂) ⊣ Θ1` into

      ad_pat_consis ∅ Θ1 (pskl_to_uskl (β̂ → α1̂)) (bskl_var_f α)

  and that consistency can only have come from `ad_pat_consis__flex_r`: the
  LHS is an ARROW so `__arrow` needs an arrow on the right, and `__var`
  demands `a_binds_tvar α Θ1`, i.e. a RIGID α, which it is not.  So inversion
  hands you exactly

      binds α (abind_flex_mono_def τ) Θ1                (* = premise 1 of
                                                           ad_refine_pskl__flex_l *)
      ∅ ⨟ Θ1 ⊢ₛᵃ (pskl_to_uskl (β̂ → α1̂)) ∼ (ptyp_to_bskl_syn τ)

  leaving one obligation: `Θ1 ⨟ ∅ ⊢ᵣₚᵃ (ptyp_to_pskl τ) ⊳ (β̂ → α1̂)`.  Both
  sides there are MONOTYPE-level (τ is a monotype by construction; `β̂ → α1̂` is
  an arrow of flexibles, hence ghost-free), so this is the mono bridge's
  territory — `consis_refine_mono_tyequiv` / `tyequiv_mono_consis` /
  `consis_mono_trans` (prop_mono_bridge.v) plus a
  `≡ˢ ⟹ ⊳` step.  That last step is the one genuinely new fact; check whether
  `a_pskl_tyequiv` already has a refinement corollary before proving it.

  Other handles if the above stalls: `a_assign_unify_subject_flex`
  (prop_consis_rename.v §4), `a_assign_subject_flex_local` (prop_metasubst.v).

---

## 3. `lemma:precision-sub` — ✅ CLOSED 2026-08-07 (`799b1a8`), as a COROLLARY of P5c

**DONE**: `ad_precise_extends_pat_sub_gv` / `_v`
(prop_completeness_sub_precise.v tail) — fuel preserved, both sorts.  P5c's
`ad_pat_sub_precise_upre_gv` already was the transport; the new content is
the bridge `uskl_precise_of_ad_precise` (pskl precision ⟹ `uskl_precise` at
`Ψrep = ∅`).  ⚠️ For §5: the corollary's `Θ ⨟ ∅ ⊢ₚₛᵃ ⌊Q⌋` hypothesis is NOT
derivable inside `ad_ctx_precise_pat` (target_wf gives only scope; wf does
not propagate past `ad_pat__app`'s existential P) — the WF-SIDE-CONDITIONS
route is to put `Θ ⨟ empty ⊢ₚₛᵃ P` ON `ad_pat__app`; take that rule change
deliberately, §6.2-style.  History below.

✅ **The transitivity engine landed** (`1a31643`, prop_precise.v tail, Qed +
axiom-free): `ad_refine_pskl_trans_gen` / `_trans`, `ad_refine_pskl_hole_l`,
`ad_refine_pskl_ftv_delta_free`, `ad_refine_pskl_of_inh_paintings`, and the
composition `ad_precise_preserves_refine_pskl` — the uncoloured
precision-preserves-refinement that transports the `_gv` LEAF datum.
⭐⭐ NOT a row-for-row mirror of `ad_refine_syn_trans`: the pskl `__all` row
fires (syn's dies on painting shape) and its inner `__tophole_fill`
composite needs the IH at a REASSOCIATED context (∀-witness moved Δ→Θ) —
solved by generalizing the statement over a context map (Hmap/Hsplit), NOT
by a fuel mirror.

⚠️⚠️ **The induction itself must NOT be stated naively.**  `_gv`'s ForallL
opens the subject with a ghost decoration ψ, leaving the `pskl_to_uskl`
image — the motive "subject is `⌈P⌉ᵘ`, precision `P' ⊑ P`" has no IH there
(the P7 lockstep problem again).  Mirror
`ad_pat_consis_subject_refine`'s statement shape
(prop_consis_precise.v:568) — consistency's version of the same transport —
and note its precision corollary `ad_pat_consis_subject_precise` (:692)
discharges the consis premises of `__infer`/`__check`/`__univ_ghost_r`/
`__arrow` directly.  Landing spot: NEW `algo/prop_precise_sub.v`
(needs prop_consis_precise + def_decl_algo_sub_hyg, which
prop_consis_precise does not import).  Full ingredient list:
memory `remech-pskl-trans-kit`.

### 3-history (scouting, 2026-08-06)

    Lemma ad_precise_extends_pat_sub : forall Θ Δ P' P Ψ M Q,
      Θ ⨟ Δ ⊢ₚᵣᵃ P' ⊑ P ->
      Ψ ⨟ Θ ⊢ₛᵃ[ a_sub_mode_sk | M ] (pskl_to_uskl P) ⩽ Q ->
      Ψ ⨟ Θ ⊢ₛᵃ[ a_sub_mode_sk | M ] (pskl_to_uskl P') ⩽ Q.

⚙ Probe: `cex/probe_precision_sub_ghost_row.v` (compiles).

⭐ **`P' = □` is not the problem — `□ ⊑ P` hands back exactly the Ghost row's
fill.**  `ad_precise P Q` is `inh{P} ⊳ inh{Q}`, so at `P' = □` the subject is
`◇` and only two refinement rows apply: `__hole`, whose fill is a
**SYNTHESISED** painting, and `__flex_r`.  Since `pskl_to_bskl_inh` paints ∀
as `bskl_all_inh` while `pskl_to_bskl_syn` paints it `bskl_all_syn`, the two
images meet exactly on the `pskl_all_syn`-free skeletons.  Hence

- `ad_precise_hole_inv` : `□ ⊑ P` ⟹ ∃ `P1`, `inh P = syn P1` and
  `Θ ⨟ ∅ ⊢ₚₛᵃ P1` — which IS `ad_pat_sub__ghost`'s target-and-wf obligation;
- `ad_precise_hole_all_absurd` : `□ ⊑ ∀X.P` is **FALSE**, so the Ghost row
  never faces a quantified counterpart.

⚠️ **A second candidate counterexample, also refuted** (recorded so it is not
re-tried).  `ad_pat_sub__flex_mono` is FUNCTION-mode only, so a DEFINED
flexible `α̂ ⊑ 1` looks like it should strand `α̂ ⩽ ∀◇.1` at `M = TC`.  It does
not: `ad_pat_sub__univ_ghost_r` takes ANY *guarded* subject and a variable is
guarded, so that row covers flexible subjects outside function mode
(`ps_concl` in the probe).

⛔ **What a full proof still owes** (neither is the flagged obstruction):

1. the Ghost row's `Ψ [=] ∅`.  Automatic, but it needs a lemma: a
   `pskl_to_uskl P` subject is TAG-FREE (`pskl_to_uskl` never builds
   `uskl_all_etag`), so no tag-introducing row can fire and the ROOT `Ψ` of
   any derivation over such a subject is empty.
2. a `mod_comp_sk` transport along the precision (Ghost / GhostG carry it).

---

## 4. `lemma:precision-preserves-refinement` — ✅ ALREADY DONE

`ad_precise_preserves_refine` (prop_precise.v:585), Qed and audited in
`README.v`.  It carries three external wf side conditions beyond the paper
(`a_wf_aenv Θ`, Δ-disjointness from `dom Θ`, wf of the target) — the
WF-SIDE-CONDITIONS pattern again.  Nothing to do.

---

## 5. Context precision — ✅ CLOSED 2026-08-07, on a NEW FOUNDATION

**DONE**: `ad_ctx_precise` (the paper's `⪯ctx`) + `ad_ctx_precise_pat`, NEW
`algo/prop_precise_sub.v`, Qed + axiom-free, audited in README.v.  The
"context-change lemma" the paper's sketch names turned out to ALREADY exist
as prop_ctx_mono.v's `aenv_tbinds_le` `_mono` family; `ad_ctx_precise_tbinds_le`
/`_ge` connect `⪯ctx` to it (same type-level entries, both directions), and
the binder rows extend `⪯ctx` reflexively (`ad_precise_refl`).

⭐⭐ **The flagged rule-change decision RESOLVED — but NOT as recorded.**  The
memory's route (put `Θ ⨟ ∅ ⊢ₚₛᵃ P` on `ad_pat__app`, propagate a top-level
target-wf hypothesis down) is REFUTED: the capture configuration of
`cex/cex_refine_not_transitive.v` sits inside `ad_pat__app`'s own refinement
premise, so wf CANNOT propagate into the function premise's domain `Q1` even
with that premise (refinement from a wf source can produce a nowhere-wf
target).  A first attempt with BOTH `wf P` and `wf ⌊Q1⌋` on the rule then
strands `a_pat_sound`'s App case (the run's arrow domain has no wf source
short of an output-wf conjunct through all ten rows).  The repair that
LANDED: `Θ ⨟ empty ⊢ₚₛᵃ ⌊Q⌋` on the three BASE rows of `ad_pat` — where the
consumers (this lemma's Var case, theorem 3's Sub case feeding
`a_sub_complete_thm`'s counterpart-wf) actually sit, and nothing needs to
propagate.  `ad_sd_typing`'s base rows are NOT changed: at TY, scope +
ghost-freeness already give wf (`a_wf_ptyp_of_scope_pskl`).

⭐⭐⭐ **The soundness supply is a NEW FOUNDATION — the algorithm's outputs are
well-formed** (`algo/prop_wf_output.v`, both Qed + axiom-free):
`a_consis_output_wf` (14-row induction over `a_consis`; motive = wf-at-∅ +
shielded-set avoidance of Δ1∪Δ2 + ftv provenance + guardedness propagation —
the run's Δ-trackers and the Ghost/GhostR `Δ ∩ ftv` side conditions exist
precisely to make the three close-rows' re-binding sound; the P6 kit's
`pskl_shielded_ftv` + `a_wf_pskl_tvar_to_delta` + `a_wf_pskl_all_of_one` are
the assembly) and `a_sub_output_wf` (mutual with the flex walk, context
surgeries cribbed row-for-row from `a_subtag_sound_bundle`).
`a_pat_sound`'s base rows supply the new premise via `a_sub_output_wf`;
consumer sweep = the §6.2 five files + `subst_bskl_to_pskl_eq`
(prop_suffix_erase.v §"target-shape rewrites").

---

## 6. The four theorems

Order them soundness-first; the two soundness theorems are independent of the
`ad_pat_sub_gv` question, the two completeness ones are not.

1. **Soundness of skeleton inference** — `a_pat` ⟹ information increase +
   `ad_pat` at the output context.  Consumes `a_sub_sound_thm`
   (prop_decorate_key.v; since `9189ba8` it concludes the PLAIN
   `Θ1 ⨟ ∅ ⊢ᵣᵃ … ⊳ …`) and §1's suffix kit.
2. **Soundness of type inference** — `a_typing` ⟹ increase + `ad_sd_typing`.
   Same shape; additionally needs `a_tyequiv` to discharge the appendix's three
   equivalence premises, which is where the algorithm's flexibles show up.
3. **Completeness + optimality of skeleton inference** — ⏳ IN PROGRESS
   (2026-08-07): the KIT and the THREE BASE ROWS are closed; the induction's
   six remaining cases are what is left.  See §6.4.
4. **Completeness + optimality of type inference**

### 6.4 thm:complete-skeleton-inference — the kit + the base rows are CLOSED (2026-08-07)

Everything lives in NEW `algo/prop_completeness_pat.v`; all Qed, axiom-free.

**The statement** is `pat_complete_concl`, factored exactly like
`a_sub_complete_thm`'s (prop_completeness_sub.v): the run, plus for EVERY
identity increase out of the question context a composing witness `ζ` that is
`a_inc_equiv` to the given solution and whose image is more precise than the
declarative target.

⭐ **No lexicographic measure, and no wf hypothesis.**  The mech FUSED the
paper's `P-Sub` into the three base rows, so every recursive premise is at a
strict subterm — `size_exp e` alone.  And `ad_pat_target_wf` (K1) is provable
BOTTOM-UP now that the base rows carry the counterpart's wf (§5), so the
theorem derives any sub-derivation's target wf on demand instead of assuming
it.

**The kit** (`K1` `ad_pat_target_wf`, `K7` `a_pat_output_wf`, `K2` the two
reverse term-entry lookups, `K3a/b` the painting bridges + the three slack
lemmas, `K4` the two-sided term-entry strip, `K5` split-completeness) and the
three base rows (`a_pat_complete_unit` / `_var` / `_anno`) are done.

⭐⭐ **The one design point the scouting had left open is settled**: `P-Anno`'s
slack is REFLEXIVE, because an annotation is SOURCE syntax — its type
variables are RIGID, and `a_inc`'s domain is exactly the source context's
FLEXIBLES (`a_inc_dom_flex`).  That rigidity is theorem 3's ONE side condition
about the term, and it threads through the induction.  ⚠️ The tempting
alternative `dom κ ∩ dom Θ = ∅` is FALSE — an identity increase PRESERVES
flexibles.

⛔ **What remains**: the `size_exp` induction.  `Freeze` is DONE
(`a_pat_complete_freeze`, step-lemma style: the IH is an explicit premise,
so the final induction is pure glue).  The five other rows need:

⛔⛔ **K6 — the gap the induction actually hit.**  The ALGORITHM's four
binder rules are COFINITE in the term variable and share their outputs
`Ξ`/`Θ1`/`Q` across the family, while the IH delivers ONE instance at one
fresh `x`.  So completeness needs the ALGORITHMIC twin of
`ad_pat_rename_tm` / `ad_pat_subst_tm` — theorem 1 built those for the
DECLARATIVE judgement only, and no `a_pat_rename_tm` exists.  Route
(standing directive: equivariance is THE renaming primitive): mirror
prop_swap.v's `a_sub_sub_flex_swap` / `a_assign_unify_consis_swap` /
`a_guess_mono_swap` into `a_pat_swap`, then derive the renaming from
equivariance + freshness.  ⚠️ Theorem 4's binder rows need the same thing —
build it once, for both `a_pat` and `a_typing`.

Order for the next session and the full per-case recipe: memory
`remech-theorem3-plan`.

### 6.1 ⭐ The `ad_pat_sub_gv` composition gap — SCOPED (2026-08-06), and the ~300-line "freshening bridge" is NOT part of it

**The finding: `a_subtag`'s ForallL rows are COFINITE in the tag set**
(`a_subtag__forall_l_{tagged,untagged}`, def_decorated.v: *"forall Ψg ψg,
Ψg ∩ L = ∅ → a_tags_sort NM Ψg ψg → ⌊ψg⌋ˢ = P1 → …"*), and
`a_subtag_sound_bundle` ALREADY instantiates that family with a freshly
chosen decoration —

    destruct (a_tags_sort_decorate_exists (Hex α Hα) HlcP1 (L ∪ Ψ)) …

So `ad_pat_sub_g`'s extra hygiene premise
`Ψ' ∩ ftag_in_uskl (subject) = ∅` costs **ONE WIDER AVOID-SET**,
`(L ∪ Ψ ∪ ftag_in_uskl (uskl_all_etag ε R))`, not a tag-RENAMING kit.  The
`_n → _g` bridge DESIGN §5.4 defers at ≈300 lines is only needed if you go
UP from `ad_pat_sub_n`; going down from the DECORATED system, the freshness
is available before the tags are ever chosen.  ⚙ Nothing else in the bundle
touches tags.

**The rest is threading, exactly as PROGRESS.md §4b predicted.**  Every
consistency-leaf row of the bundle already destructs
`a_consistag_sound_aux`'s conclusion as

    [Hle [Hwf1 [_ [_ [[Qt [HeQt [Hcons Hfill]]] _]]]]]

and that FINAL `_` **is** `ad_pat_sub_gv`'s leaf premise
(`ad_refine_pskl_f Δ2 Θ1 Δ2 ⌊R⌋ˢ P'`, plain at `Δ2 = ∅` via
`ad_refine_pskl_f_forget`).  It is being dropped, not missing.

**Row-by-row plan** (`frost/algo/prop_soundness_sub.v`, the ~820-line
bundle at :466–:1286):

| row | change |
|---|---|
✅ **§6.1 IS CLOSED (2026-08-07).**  `a_subtag_sound_bundle` now concludes the
LEAF-VALID join; `make coq` clean, all audits *Closed under the global
context*.  The table below is the record of what each row needed.

| row | change |
|---|---|
| `subtag_sound_concl` / `subtag_flex_sound_concl` | ✅ conclusion is now `exists n, ad_pat_sub_gv n NM M Ψ Θ1 R Qt` |
| `Infer`, `UnivGhostR` | leaf refinement = `ad_refine_pskl_refl` (prop_refine.v:177) at the wf subject — both rows already build their target as the subject's own erasure |
| `Arrow` (domain) | ⚙ DIRECT: `a_consistag_sound_aux`'s dropped conjunct IS `⌊R1⌋ˢ ⊳ P'1` and the row's `Q1` satisfies `bskl_to_pskl Q1 = P'1`.  `ad_refine_pskl_f_forget` then `ad_refine_pskl_f_isub` to reach Θ2 |
| `Check` | ✅ **its missing lemma is BUILT** (2026-08-06, prop_soundness_sub.v §1a–§1d, Qed and axiom-free).  §6.1 had under-estimated this row: the dropped conjunct gives `⌊T⌋ˢ ⊳ ⌊Qt⌋` for the CONSISTENCY's output `Qt`, but the row re-targets its conclusion to `inh B` (audit-F2: the output is not literally `B`), so the leaf needs `⌊T⌋ˢ ⊳ B`.  `ad_refine_pskl_refine_inh_target` supplies exactly that.  See below |
| `ForallR` | ⛔ **NEWLY FOUND (2026-08-06): needs `ad_pat_sub_gv_rename_tvar`, which does not exist.**  The algorithmic rule is exists-fresh (ONE α) while `_gv__forall_r` is cofinite, so the row must rename — exactly as the plain proof does with `ad_pat_sub_rename_tvar` (prop_pat_sub.v:1217, ~110 lines).  The `_gv` version must be FUEL-PRESERVING.  See the ingredient list below |
| `ForallL` ×2 | widen the avoid-set (above); the hygiene premise is then `Hint0` |
| `ForallR`, `UnivGhostL/LG`, `FlexMono`, ghosts | pass through |
| fuel | leaves take any `n` (use `0`); `ForallR`/`Arrow`/`ForallL` conclude at `S n`.  Each rule has ≤ 1 recursive `_gv` premise, so no `max` is needed |

✅ **(a) SETTLED 2026-08-06 — the dependency order.**  `ad_pat_sub_g_of` and
`ad_pat_sub_gv_fuel_weaken` MOVED to
`decorated_algo/def_decl_algo_sub_hyg.v` (they are plain inductions over the
mirrors and need nothing else), joined there by the composite
`ad_pat_sub_of_gv : ad_pat_sub_gv n … -> Ψ ⨟ Θ ⊢ₛᵃ[ NM | M ] R ⩽ Q`.  Both
old sites keep a pointer comment.

✅ **(b) DONE.**  Of the three positional consumers, one
(`prop_completeness_sub_gen.v:3165`) never touched the join; the other two
(`prop_decorate_key.v:4155`, `prop_completeness_sub_gen.v:3389`) recover the
plain form with `ad_pat_sub_of_gv`.  ⚙ `prop_decorate_key.v` needed
`Require Import …def_decl_algo_sub_hyg` added — a `Require Import` does not
re-export, so the name was not in scope through `prop_soundness_sub`.

⚙ **`a_sub_sound_thm`'s own statement is UNCHANGED** — it still concludes the
plain `ad_pat_sub`, recovered at the call site.  That is deliberate: its
consumers (`a_pat_sound`, `a_typing_sound`) still feed the plain join into
`ad_pat` / `ad_sd_typing`'s rules.

#### ✅ §6.2's RULE CHANGE — LANDED 2026-08-07 (second pass)

**DONE.**  The six base rows embed `ad_pat_sub_v`; `make coq` clean and every
`Print Assumptions` audit (including `a_pat_sound` / `a_typing_sound`) still
axiom-free.  The missing pair (`ad_refine_pskl_subst_mid` +
`ad_pat_sub_v_subst_mid`, prop_suffix_erase.v §5/§8) was built FIRST, then the
change went in one pass.  Two consumer triples the table below missed:
`ad_pat_sub_mod_comp_ty` (prop_soundness_typing.v §8e) and
`ad_pat_sub_target_wf` at `a_typing_sound`'s `a_wf_ptyp Θ1 A` conjunct — both
recover the plain premise with `ad_pat_sub_of_v`.  The cex's §3 is now
`cap_not_reachable`.  The subsection below is kept as the historical record.

The plumbing below IS in the tree and green; the rule change itself is not.

| in the tree | what it is |
|---|---|
| `ad_pat_sub_v` + `ad_pat_sub_of_v` (def_decl_algo_sub_hyg.v) | the leaf-valid join with the fuel forgotten — what the rules are to embed |
| `a_sub_sound_thm_v` (prop_decorate_key.v) | ⭐ the leaf-valid companion: hands the bundle's `_gv` ON instead of forgetting it.  The PLAIN version stays for its ~10 other consumers |
| `ad_pat_sub_gv_mono` / `_v_mono` (prop_ctx_mono.v) | context-monotonicity |
| `ad_pat_sub_v_isub` / `_v_weaken` (prop_soundness_sub.v §1f) | the fuel-forgotten wrappers |
| the cex's §1/§2 at an ARBITRARY Θ | the refutation never needed `Θ = ·` |

⛔ **What blocked it.**  Changing the six base rows breaks EVERY proof over
`ad_pat` / `ad_sd_typing` that REBUILDS a base row, and each needs a `_v`
mirror of the structural lemma it used.  The attempt found them one rebuild
at a time and built all but one:

| consumer | mirror | status |
|---|---|---|
| `ad_pat_mono` / `ad_sd_typing_mono` | `ad_pat_sub_v_mono` | ✅ |
| `ad_pat_isub_tm` / `ad_sd_typing_isub_tm` | `ad_pat_sub_v_isub` | ✅ |
| the tm-swap rows (prop_soundness_pat.v) | `ad_pat_sub_v_mono` | ✅ |
| `ad_pat_mod_comp_sk` | none — recover the plain premise with `ad_pat_sub_of_v` | ✅ |
| ⛔ `ad_pat_strip_suffix` / `ad_sd_typing_strip_suffix` (prop_suffix_erase.v) | `ad_pat_sub_v_subst_mid`, mirroring `ad_pat_sub_subst_mid` (:929) | **NOT built** |

⛔ The last one is where it stopped: its leaf needs
**`ad_refine_pskl_subst_mid`, which does not exist**.  prop_suffix_erase.v has
only the `bskl` form `ad_refine_syn_subst_mid` (:499, ~105 lines), and the two
judgements' `__hole` rows differ (the `bskl` one's fill is a SYNTHESISED
painting), so there is no bridge.  Budget: ~105 lines for the refinement
lemma + ~100 for the `_gv` mirror, and then the rule change lands.

⚙ **Then do the rule change in ONE go**: the six rows, the consumer mirrors
above, `a_sub_sound_thm_v` at the seven call sites in `a_pat_sound` /
`a_typing_sound`, and the cex's §3 — which becomes `cap_not_reachable`, the
change's own witness (the configuration is REJECTED once the rows embed
`ad_pat_sub_v`).  ⚙ Several files need `Require Import …def_decl_algo_sub_hyg`
added; a `Require Import` does not re-export.  ⚙ The reverted attempt is kept
at `scratchpad/section62-attempt.patch`.

#### ⛔ (c) THE CONVERSION IS BIGGER THAN "THREADING" — the rows consume FOUR structural lemmas over `ad_pat_sub`, each needing a `_gv` mirror

Discovered by surveying the 15 rows (2026-08-06).  A `_gv` mirror is the plain
lemma with the fuel carried UNCHANGED plus the LEAF datum transported by the
matching `ad_refine_pskl` lemma:

| used by row | mirror | status |
|---|---|---|
| `FlexMono` | `ad_pat_sub_gv_psi_cong` | ✅ §1f (leaf carries no Ψ) |
| `Flex-Skip` | `ad_pat_sub_gv_isub` | ✅ §1f (`ad_refine_pskl_isub`, prop_stability.v:121) |
| `Flex-Assign` | `ad_pat_sub_gv_weaken` | ✅ §1f (`ad_refine_pskl_weaken`, prop_refine.v:98) |
| `ForallR` | `ad_pat_sub_gv_strip_suffix` | ⛔ **NEXT — a two-lemma chain with a missing ingredient** |

⛔ **The `strip_suffix` chain — HALF BUILT (§1g).**  The plain
`ad_pat_sub_strip_suffix` (prop_pat_sub.v:1158) does not induct on the
judgement: it iterates a SUBSTITUTION strip head-first over Ξ, and its head
splits on whether the flexible is DEFINED.  So the mirror needs FIVE lemmas,
two per head plus the driver:

| # | lemma | status |
|---|---|---|
| 1 | `ad_refine_pskl_subst_flex` (undefined head, `β ↦ 1`) | ✅ §1g |
| 2 | `ad_pat_sub_gv_subst_flex` (mirrors prop_pat_sub.v:749) | ✅ §1g |
| 3 | `ad_refine_pskl_subst_flex_def` (DEFINED head, `β ↦ τ`) | ✅ §1h |
| 4 | `ad_pat_sub_gv_subst_flex_def` (mirrors prop_pat_sub.v:1031) | ✅ §1h |
| 5 | `ad_pat_sub_gv_strip_suffix` (mirrors prop_pat_sub.v:1158) | ✅ §1h |

✅ **ALL of §6.1's structural prerequisites are now in the tree.**  §1h also
adds `bskl_to_pskl_subst_mono` and ⭐ `ftag_in_uskl_subst_mono` (a MONOTYPE's
painting is tag-free, so substituting it cannot add tags — the `ForallL`
hygiene premise for the third time).  ⚠️ `guarded_pskl_subst` had to be
written FULLY QUALIFIED (`src.frost.algo.prop_pat_sub.guarded_pskl_subst`):
the bare name resolves to prop_looksub.v's homonym here.

⚙ Also landed in §1g: `bskl_to_pskl_subst_unit` and ⭐
`ftag_in_uskl_subst_unit` (substituting `1` cannot change TAGS either — the
`ForallL` hygiene premise again).  ⚠️ §1g forced
`Require Import src.frost.decl.prop_skeleton` into this file (for
`guarded_pskl_subst_unit`); it is placed EARLY on purpose, so the later
imports keep winning the homonym races §1e ran into.

⚙ Only then can `subtag_sound_concl` / `subtag_flex_sound_concl` change and
the 15 rows be rewritten — and that last step is ATOMIC (the file will not
compile until every row is converted; `git checkout` the file if it does not
converge).  Row-by-row leaf sources: `Infer`/`UnivGhostR` →
`ad_refine_pskl_refl` at the wf subject; `Check` → §1a–§1d's
`ad_refine_pskl_refine_inh_target`; `Arrow` (domain) →
`a_consistag_sound_aux`'s dropped conjunct via `ad_refine_pskl_f_forget`;
`Ghost`/`GhostG`/`ForallL`/`UnivGhostL(G)`/the flex walk → pass through.

#### ✅ The `Check` row's missing lemma — BUILT (2026-08-06)

`prop_soundness_sub.v` §1a–§1d, all **Qed and axiom-free**, ~180 lines:

| § | lemma | what it is |
|---|---|---|
| §1a | `ad_refine_pskl_unfold_def_target` | unfold a flexible DEFINITION on the TARGET of a refinement (the `flex_r` step) |
| §1b | `ad_refine_syn_f_inh_wf_transfer` | ⭐ the fill transfers Δ-RELATIVE well-formedness |
| §1c | `refine_transport_arrow` / `refine_transport_all` | the `consis_transport_*` mirrors |
| §1d | `ad_refine_pskl_refine_inh_gen` + `ad_refine_pskl_refine_inh_target` | the transport itself |

⭐ **The mirror needs TWO FEWER hypotheses than its consistency twin**, and
§1b is why.  `ad_pat_consis_refine_inh_gen` carries a Δ-free wf of the source
plus "every Δ-variable is Θ-visible"; neither survives the mirror, because
**refinement's `__all` extends Δ while consistency's ∀-rows extend Θ**.  §1b
replaces both: the ghost branch of each transport helper rebuilds its fill
from §1b at `Δ = ∅`, and the visibility premise turns out to have no consumer
on the refinement side at all.  ⚙ `refine_transport_all`'s per-binder
hypothesis is quantified over BOTH a Θ-extension and a Δ, because its two
∀-ish rows (`__all`, `__tophole_fill`) extend different contexts.

⚠️ **Three traps this cost time to** (all already in §7.4's spirit):

- `fsetdec` on an EVAR avoid-set **does not terminate** — 97 s, then the
  timeout.  `a_wf_pskl_delta_mono`'s `Δ0` is left an evar by the
  Δ-polymorphic `a_wf_pskl_mono_ptyp`, and the wrapper was not needed at all.
  ⚙ Profile-first paid: imports alone were 0.3 s, so it was never I/O; a
  `k`-live-cases bisect found the row in one pass.
- a `match goal` pattern `forall α, α ∉ ?L -> _` also matches a COFINITE
  HYPOTHESIS of the lemma itself (here the transport premise).  Fix: move the
  `α ∉ L` binder AFTER the others in that hypothesis so its head differs.
- `induction` renames the lemma's own `Θ'` to the branch's `Θ`, so any
  explicitly written `Θ'` term inside a branch is out of scope — let
  unification supply it.
- `ad_refine_syn_f__all` keeps `Q P` EXPLICIT while `F L Θ Δ` are implicit,
  so the family goes in THIRD (§7.4: read the arity, don't count
  underscores).

#### ✅ `ad_pat_sub_gv_rename_tvar` — BUILT (2026-08-06), `prop_soundness_sub.v` §1e

Qed and axiom-free, with the two bridges it needed:
`ad_refine_pskl_f_of_plain`, `ftag_in_uskl_subst_var` (⭐ renaming a TYPE
variable cannot change TAGS), `ad_refine_pskl_rename_ctx`, and the
fuel-preserving renaming itself.  The statement is the plain one
(`ad_pat_sub_rename_tvar`, prop_pat_sub.v:1217–1330) plus a fuel index
carried UNCHANGED:

    Lemma ad_pat_sub_gv_rename_tvar : forall n NM M Ψ Θ1 α Θ0 R Q β',
      ad_pat_sub_gv n NM M Ψ (Θ1 ++ (α ~ abind_tvar) ++ Θ0) R Q ->
      α `notin` dom (Θ1 ++ Θ0) ->
      (forall β τ, binds β (abind_flex_mono_def τ) (Θ1 ++ Θ0) ->
         α `notin` ftvar_in_ptyp τ) ->
      ad_pat_sub_gv n NM M Ψ (Θ1 ++ (β' ~ abind_tvar) ++ Θ0)
        (subst_bskl_in_uskl (uskl_var_f β') α R)
        (subst_bskl_in_bskl (bskl_var_f β') α Q).

**Ingredients — three of five are already in scope from `prop_soundness_sub.v`:**

| need | status |
|---|---|
| `ad_pat_consis_rename_tvar` | ✅ prop_pat_sub.v |
| `⌊subst R⌋ˢ = subst ⌊R⌋ˢ` | ✅ `uskl_to_pskl_subst_mono` (prop_pat_sub.v:1019), at `τ := ptyp_var_f β'` |
| `bskl_to_pskl` vs subst | ✅ `bskl_to_pskl_subst_var` (prop_completeness_consis.v:1590) |
| the LEAF refinement renamed | ✅ NEW `ad_refine_pskl_f_of_plain` + `ad_refine_pskl_rename_ctx` (§1e-i/ii), on top of `ad_refine_pskl_f_rename_ctx` at `F = Δ = ∅` |
| the ForallL hygiene premise under the rename | ✅ NEW `ftag_in_uskl_subst_var`: `ftag_in_uskl (subst_bskl_in_uskl (uskl_var_f β) α R) [=] ftag_in_uskl R`.  ⭐ Renaming a TYPE variable cannot change TAGS — an EQUALITY, so the local copy is 6 lines and the downstream `ftag_in_uskl_subst_bskl_in_uskl` was not needed |

⚠️ **Four more traps, all from moving scratch-proved script INTO the tree.**
A scratch file's hint context and name resolution are NOT the target file's:

- `; auto` closes a DIFFERENT NUMBER of goals in `prop_soundness_sub.v` than
  in a scratch file, and the bullets silently stop lining up ("Wrong bullet"
  pointing at the NEXT row, not the guilty one).  State every premise chain
  explicitly.
- **`guarded_pskl_subst` resolves to `prop_looksub.v:466`'s homonym here**
  (it is the last `Require`), and that one carries a DISEQUALITY premise.
  Use the unambiguous one-premise `guarded_pskl_subst_var`
  (prop_soundness_consis.v:541).  ⚙ Same hazard for `a_wf_pskl_rename_tvar`
  (prop_soundness_consis.v:553 vs prop_soundness_pat.v:1413) — the latter is
  not imported here, so it happens to be safe.
- `apply` does NOT present a lemma's premises in source order; use
  `first [ … ]` per goal rather than a positional `[ … | … ]` chain.
- ⭐ In the two ForallL rows the recursive premise must be discharged FIRST
  (`6: exact IH…`), because it is what fixes `ψ`; in a left-to-right chain
  `ψ` is still an evar at the `a_tags_sort` goal and `assumption` cannot
  instantiate it.

### 6.2 ⭐⭐ WHERE `ad_pat_sub_gv` ENTERS — SETTLED 2026-08-06 (scouting item 1)

**The answer: on the RULE.**  `ad_pat`'s and `ad_sd_typing`'s embedded
subtyping premise must be the LEAF-VALID mirror for the completeness
direction.  Machine-checked in `cex/cex_ad_pat_join_not_leaf_valid.v`.

**Why nothing cheaper works.**  `a_sub_complete_thm` takes its join as
`ad_pat_sub_gv`; `ad_pat` / `ad_sd_typing` embed the PLAIN `ad_pat_sub`.  The
gap is not bookkeeping — the CAPTURE configuration of DESIGN-subtyping.md
§3.1,

    subject  ∀X.◇      counterpart  ∀ˢX.X

has a plain join (`cap_plain`), has NO leaf-valid one (`cap_no_gv`), and is
REACHABLE from `ad_pat` as `P-Var` at an entry `x : ∀X.◇` (`cap_reachable`).
⭐ The mechanism: **consistency's ∀-rows push the rigid into `Θ`, refinement's
push it into `Δ`, and `ad_refine_pskl__hole`'s fill is Δ-free BY RULE** — so
the ghost may be filled with the bound variable in the consistency and never
in the refinement.

⚙ So this is NOT the same thing as §6.1: §6.1 makes SOUNDNESS *produce* `_gv`
(needed to keep theorems 1 and 2 once the rule changes); §6.2 is that the
completeness direction must be able to *consume* it, which only a rule change
supplies.  Both are now required, and §6.1 becomes a hard prerequisite.

⚙ **This is the paper's own augmentation, propagated one layer up.**  The
solution notion for CONSISTENCY already carries the subject-refinement
condition (`a_consis_complete_thm`'s
`ad_refine_pskl_f empty Θ empty (msubst_pskl κ P) (bskl_to_pskl Qb)`,
consistency-proofs.tex:2230-2242).  Subtyping carries the same datum at the
LEAVES rather than the root, because at the root it is vacuous
(`cex_p7_univ_ghost_r_vacuous.v`, `cex_p7_third_premise_forall.v`).  Skeleton
and type inference must therefore carry it at each embedded subtyping
premise's leaves.  Registered in docs/PAPER-GAPS.md.

**Shape to land** (`decorated_algo/def_decl_algo_typing.v`): replace the
`ad_pat_sub` premise of `ad_pat__{unit,var,anno}` and
`ad_sd_typing__{unit,var,anno}` with

    exists n, ad_pat_sub_gv n <NM> m empty Θ <R> <Q>

(a `Definition ad_pat_sub_v` wrapper keeps the rules readable).  Then:

- theorems 1 and 2 must produce it → **§6.1's bundle repair is mandatory**;
- every existing INVERSION consumer recovers the plain premise with
  `ad_pat_sub_gv_forget` then `ad_pat_sub_g_of` — the same dependency-order
  question §6.1(a) already raises.

### 6.3 The four rule-level side conditions, seen from COMPLETENESS (scouting item 2)

Theorem 2 put four conditions ON the rules (docs/PAPER-GAPS.md, 2026-08-06).
Completeness must now DISCHARGE them when it builds the `a_typing`
derivation.  Status after scouting — none is refuted, one needs a new
existence lemma, one needs a real invariant:

| # | condition | where | discharge |
|---|---|---|---|
| 1 | `uniq (Ξ ++ Θ)` | 4 CHECK rows | ✅ derivable: `a_typing_sound` on the body's run gives `a_wf_aenv (Ξ ++ …)` hence `uniq`; `Θ0 ⊴ Θ1` moves it down to the rule's own input |
| 2 | `dom Ξ` ∉ `ftvar_in_ptyp` (result) | 4 CHECK rows | ⚠️ **the one to watch.**  At the two `_base` rows it is easy — the result's `A`/`B` are the SPLIT's halves, scoped in the pre-body context, so #1 plus `a_wf_ptyp` closes it.  At the two `_step` rows the result is the body run's own output type and the argument has to be an INVARIANT ("a TC run's result type is scoped BELOW any suffix the run deposits"), which no lemma states yet |
| 3 | `uniq (αs ++ Θ1)` | `AT-Abs` | ✅ satisfiable, but needs a lemma the tree does not have: `a_guess_mono` EXISTENCE with an avoid set (`prop_flex.v` has only `_decls` / `_generated_fresh` / `_ftv` / `_open_at`).  Completeness CHOOSES this block, so an avoid-set-indexed generator settles it |
| 4 | `AT-AbsAnnoCheck`'s result domain is the split's `A'` | — | ✅ free: it is what `sd-AbsAnnoCheck`'s `≡ᵗ` premise is for, and the completeness side reads the domain off the split it performs |

⚙ Item 2's probe order when the induction reaches rows 7–10: build #3's
generator first (it is a plain structural existence proof), then #2's
invariant; if #2's `_step` case cannot be proved, machine-check the run in
`cex/` rather than weakening the rule.

⚠️ **3 and 4 will hit the `ad_pat_sub_gv` composition gap** (PROGRESS.md §4b):
they consume `a_sub_complete_thm`, which ASSUMES `ad_pat_sub_gv`, while
`a_sub_sound_thm` only CONCLUDES the plain `ad_pat_sub`.  The fix identified
there is to strengthen `a_subtag_sound_bundle` to conclude `_gv` — the content
is already proved (it is the last conjunct of `a_consis_sound` and
`a_consistag_sound_aux`), the only real cost being that `_gv` is fuel-indexed
so soundness must produce an `exists n` (`ad_pat_sub_to_n` is the precedent).
Do that between 2 and 3.

---

## 7. thm:sound-skeleton-inference — ✅ CLOSED (2026-08-06, fifth pass)

`a_pat_sound` (`frost/algo/prop_soundness_pat.v` §5) is **Qed** and *Closed
under the global context*; `make coq` clean; `Check`ed and audited in
`README.v`.  §7.3 records how its last piece — AbsAnno's refinement-target
transport — was closed.

### 7.1 The statement as proved

    Theorem a_pat_sound : forall m Θ0 P0 e P Θ1,
      Θ0 ⊢ₐ[ m ; P0 ] e ⇨ P ⊣ Θ1 ->
      a_wf_aenv Θ0 ->
      (forall x Ps, binds x (abind_var_skl Ps) Θ0 ->
         Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->                  (* the paper's Θ ⊢ ctx *)
      Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
      a_sk_mode_compat m P0 ->
      a_wf_exp Θ0 e ->                            (* "M is wf in Θ0" *)
      Θ0 ⊴ Θ1 /\ a_wf_aenv Θ1 /\
      exists Qt, bskl_to_pskl Qt = P /\
        (Θ1 ⊢ᵃ[ m ] e ⇨ Qt) /\
        (Θ1 ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh P0) ⊳ Qt).

⚠️ The two hypotheses beyond the paper's list are the WF-SIDE-CONDITIONS
pattern: `a_wf_aenv__var` stores only `a_scope_pskl` where the paper's
`Θ ⊢ ctx` figure requires `Θ ⊢ P`, and `AP-Var(skl)` feeds that entry to
`a_sub_sound_thm`, which demands the DISCIPLINED `⊢ₚₛᵃ`.  Do NOT change the
`a_wf_aenv` rule to fix this — it would ripple through the whole tree.

### 7.2 What was added to close it (all in `prop_soundness_pat.v` unless noted)

| lemma | role |
|---|---|
| `a_pat_tm_ge` (+ `aenv_tm_le_via_binder_ge`) | reverse tm-verbatim for `a_pat`; with `a_pat_tm_le` it says a run's term entries are unchanged, which sustains the skl-entry-wf hypothesis through App/AbsAnno |
| `a_wf_aenv_strip_tm_mid`, `a_scope_pskl_mono` (prop_ctx_mono.v) | drop the walked term entry from the middle of a wf context; payloads are term-blind |
| `uniq_mid_eq`, `a_inc_weaken_suffix_target`, `a_isub_peel_var_skl_mid`, `a_isub_peel_var_typ_mid` | the ⊴-peel at the four binder rows |
| `a_wf_aenv_binds_var_typ_wf` | the `a_wf_aenv_binds_def_wf` mirror, for `AP-Var(typ)` |
| `ad_pat_mod_comp_sk` | ⭐ provable STANDALONE — the theorem does NOT need a strengthened conclusion |
| `mod_comp_sk_{ti,tc,fn}_inv`, `bskl_to_pskl_arrow_inv`, `ad_refine_syn_arrow_inv`, `btyp_to_bskl_ptyp_to_btyp_syn`, `bskl_to_pskl_btyp_to_bskl`, `a_wf_pskl_scope`, `a_wf_{pskl,ptyp,exp}_weaken_cons`, `a_wf_exp_*_inv` | small inversions/coercions the rows quote |
| `a_consis_chk_sound` | `a_consis_sound_aux` in the output-suppressed form, keeping `a_wf_aenv Θ1` |

⭐ **The ⊴-peel must conclude at `Ξ ++ Θ2`, not at `Θ2`.** The
definition-preservation component of `⊴` maps into the WHOLE target, so a
definition of the source could a priori be matched inside the pending suffix;
at `Ξ,Θ2` the peeled entry drops by payload shape (a definition is never a
term entry) and no freshness is needed, whereas at `Θ2` it would need a
freshness fact the statement does not carry.

### 7.3 ✅ AbsAnno's refinement-target transport — CLOSED (fifth pass)

    Lemma a_consis_chk_annot_refine : forall Θ0 A P Θ1,
      a_consis_chk Θ0 (ptyp_to_pskl A) P Θ1 ->
      a_wf_aenv Θ0 -> a_wf_ptyp Θ0 A -> Θ0 ⨟ empty ⊢ₚₛᵃ P ->
      exists B, btyp_to_ptyp B = A /\
        Θ1 ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh P) ⊳ (btyp_to_bskl B).

Needed by `AP-AbsAnno` at the ARROW split shape (at the HOLE shape the row
answers with the all-synthesised painting and needs none of this).  It is the
paper's inline "preservation of refinement under type equivalence", which
exists nowhere as a lemma.

**⛔ The dead end, first.**  Do NOT prove it by induction on `a_consis`: its ∀
rows bind the fresh witness in **Θ** while refinement's `__all` binds it in
**Δ**, which is exactly what `ad_refine_syn_f`'s hygiene set exists to manage,
so that route re-does consistency soundness.

**The route that works** is a TARGET TRANSPORT on the declarative layer —
`a_consis_chk_sound` already hands back the consistency and the refinement at
one context, so only the target is wrong:

    Lemma ad_refine_syn_target_transport : forall Ψ Θc R Qt,
      Ψ ⨟ Θc ⊢ₛᵃ R ∼ Qt -> a_wf_aenv Θc ->
      forall A, R = ptyp_to_uskl_syn A -> lc_ptyp A ->
      forall Θr Δ Qb,
      a_wf_aenv Θr ->
      (forall β τ, binds β (abind_flex_mono_def τ) Θc ->
                   binds β (abind_flex_mono_def τ) Θr) ->        (* Hdefs *)
      (forall γ, a_flex_tvar Θc γ -> a_binds_tvar γ Θr) ->        (* Hflex *)
      (forall γ, γ `in` ftvar_in_ptyp A ->
                 γ `in` Δ \/ a_binds_tvar γ Θr) ->               (* Hvis  *)
      Θr ⨟ Δ ⊢ᵣᵃ Qb ⊳ Qt ->
      exists B, btyp_to_ptyp B = A /\ Θr ⨟ Δ ⊢ᵣᵃ Qb ⊳ (btyp_to_bskl B)

by a NESTED induction — outer on the consistency, inner (with `remember` on
the target) on the refinement, in the four rows whose target does not pin the
refinement's last rule.  Eight consistency rows are dead on the subject's
shape: a `ptyp` painting is never `uskl_hole` / `uskl_topholeg` /
`uskl_all_etag`.

#### ⭐⭐ The three things that made it go through

1. **The two contexts must be DECOUPLED.**  With one shared Θ the `__all` row
   cannot be closed in either direction: the consistency premise lives at
   `(α~tvar),Θ` and the refinement premise at `Θ ⨟ α,Δ`, and moving the
   CONSTRUCTED output back (Θ → Δ) is unsound — `ad_refine_syn__hole`'s fill
   is Δ-free BY RULE, while the transport's fills are `ptyp_to_pskl A` for the
   sub-annotations, which do mention α.  Decoupled, **both ∀ rows land exactly
   where their own rule puts the binder and no context move is needed
   anywhere**: `__all` recurses at `Θc' = (α~tvar),Θc`, `Θr' = Θr`,
   `Δ' = α,Δ`; `__tophole_fill` at `Θc' = (α~tvar),Θc`, `Θr' = (α~tvar),Θr`,
   `Δ' = Δ`.
2. **The `__hole` row needs an OCCURRENCE lemma**
   (`ad_pat_consis_subject_ftv`, §4d): a free variable of a type-painting
   subject either survives into the consistency's target, or is a flexible, or
   escapes into a definition's body.  The rule wants its fill well-formed at
   EMPTY Δ — A must be Δ-free — while `Hvis` only gives "in Δ or a tvar of
   Θr"; at `__hole` the target is a synthesised painting well-formed at empty
   Δ, so all three disjuncts land in `dom Θr` and a Δ-bound ∀ witness (fresh
   for Θr) is excluded.
3. **The two flexible rows are sound because a definition is a MONOTYPE**,
   hence uniquely coloured (`btyp_to_bskl_mono_syn`, §4a) — that is what makes
   the recursive answer be exactly the synthesised painting
   `ad_refine_syn__flex_l` / `__flex_r` demand.

#### The kit (all in `prop_soundness_pat.v`)

| § | contents |
|---|---|
| §4a | `ptyp_to_uskl_syn_via_pskl`, `ptyp_to_uskl_syn_open`, `btyp_to_{ptyp,bskl}_close`, `btyp_to_bskl_open`, ⭐ `btyp_to_bskl_mono_syn` |
| §4b | `a_wf_pskl_delta_to_ctx` — the Δ→Θ move for skeleton wf (safe direction; the refinement analogue is NOT sound) |
| §4c | ⭐ `ad_refine_syn_rename_delta` — renaming a Δ-member; supplies `__all`'s cofinite family from its one witness |
| §4d | ⭐ `ad_pat_consis_subject_ftv` — the occurrence lemma |
| §4e | ⭐ `ad_refine_syn_rename_tvar` (+ `a_wf_pskl_rename_tvar`, `a_tvar_block`, `binds_swap_mid_tvar`, `a_wf_aenv_strip_prefix`) — renaming a rigid Θ-variable, in MID-CONTEXT form because the rule stacks binders on Θ; supplies `__tophole_fill`'s family |
| §4f | `transport_hole_answer`, `ad_refine_syn_target_transport`, `a_consis_chk_annot_refine` |

⚙ Read as consis-to-`≡ᵗ`, the same fact is what thm:sound-type-inference's
`Freeze` case needs ("which further gives `Θ2 ⊢ B ≡ A`").  **Derive it from
this transport rather than rebuilding it.**

### 7.4 Traps these passes cost time to

- A bare `subst` consumes the erasure equation `bskl_to_pskl Qt = Q` — the RHS
  is a bare variable, so `subst` orients it and CLEARS the hypothesis.  Use
  `subst m` / `subst P0 P Q0` in the split-shape case splits.
- `eapply a_wf_aenv_strip_tm_mid` leaves the peeled binding an evar, so
  `intros []` on `~ abind_is_ty ?b` fails ("Not an inductive product").  Put
  the `a_wf_aenv` goal first: `eapply …; [ | exact H ]; intros []`.
- `simpl_env in H |- *` is a syntax error; write the two calls.
- `simpl in Heq` unfolds metalib's `one`, which then breaks any `match goal`
  pattern written with `~`.  Prove the shape facts with
  `inversion Heq; subst; first [ reflexivity | assumption ]` instead.
- Lemmas whose variables occur only under a function application (e.g.
  `bskl_to_pskl Q = …`, `Ξ1 ++ (x ~ b1) ++ Θ1 = …`) are NOT strict-implicit
  under `Set Implicit Arguments`; give them an `Arguments … : ` line rather
  than counting underscores at each call site.
- The converse also bites: under `Set Implicit Arguments` a lemma's LATER
  universals can silently become implicit while one of them stays explicit
  (`ad_refine_syn_rename_delta` made `α`/`Δ` implicit but not `β`).  At call
  sites inside a nested induction, use `@`-application with `_` for the
  inferable prefix — named arguments only work for the ones Coq kept.
- `induction Href` inside a case of an outer induction: `revert` every
  hypothesis mentioning the refinement's context/Δ FIRST, `remember` the
  target, `revert` its equation, and give an explicit `as [...]` pattern —
  otherwise the generated names (`Θ0`, `Q0`, `Q3`) drift every time the proof
  is edited.  And state any auxiliary fact (here the reconstructed
  consistency) AFTER the `remember`, so it does not pick up the abstracted
  target and end up as an extra premise of every inner IH.
- A `- bullet is not finished` with nothing focused means the previous bullet
  ended with an `auto` that could not apply a ∀-quantified IH whose first
  premise is a context EQUATION (higher-order unification); apply the IH
  explicitly.

### 7.5 thm:sound-type-inference — ✅ CLOSED (2026-08-06, eighth pass)

`a_typing_sound` (`frost/algo/prop_soundness_typing.v` §13) is **Qed and
axiom-free**, `Check`ed and `Print Assumptions`-audited in `README.v` beside
`a_pat_sound`.  The statement is §7.5's target plus ONE conjunct:

    Theorem a_typing_sound : forall m Θ0 P0 e A Θ1,
      Θ0 ⊢ₐ[ m ; P0 ] e ⦂ A ⊣ Θ1 ->
      a_wf_aenv Θ0 ->
      (forall x Ps, binds x (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
      Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
      a_ty_mode_compat m P0 ->
      a_wf_exp Θ0 e ->
      Θ0 ⊴ Θ1 /\ a_wf_aenv Θ1 /\ a_wf_ptyp Θ1 A /\
      exists Bt, btyp_to_ptyp Bt = A /\
        (Θ1 ⊢ˢᵃ[ m ] e ⦂ Bt) /\
        (Θ1 ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh P0) ⊳ (btyp_to_bskl Bt))

⚙ **Why the extra conjunct.**  `AT-App`'s third premise runs at input `⌈A⌉`,
and nothing else in the derivation says the FUNCTION's domain is scoped in the
context the argument is checked in.  It is the paper's ambient "all inputs are
well-formed", threaded — and the four CHECK rows can prove it only because of
the Barendregt premises below (`a_wf_ptyp_strip_mid` is the strip).

⚠️ **FOUR RULE CHANGES landed with it** (all `algo/def_extra.v`, all
INVERSION-only for existing consumers, all in docs/PAPER-GAPS.md, all cleanly
revertible; the benchmark derivations discharge each at `Ξ = ·`):

1. the four CHECK rows carry `uniq (Ξ ++ Θ)` and "`Ξ` does not occur in the
   RESULT type" — the two facts the paper's own proof of this theorem assumes
   when it invokes `lemma:suffix-erasure`, and ⛔ neither is derivable;
2. `AT-Abs` carries `uniq (αs ++ Θ1)`, the consumer-side filter for
   `guess^TY`'s block (`uniq αs` is not derivable — two independent
   generators — exactly as `Sub-ForallL` filters the collection walk's);
3. `AT-AbsAnnoCheck`'s result domain is the SPLIT's `A'`, not the annotation;
4. (previous pass) `sd-App`'s fourth `≡ᵗ` and `a_split__flex`'s freshness.

⚙ The §12 kit that closed it: `a_wf_ptyp_of_wf_pskl` / `_of_scope_pskl`,
`a_wf_exp_ftv_dom`, `btyp_of_erased_ptyp` (a ghost-free `bskl` IS a colouring
— the sort bridge the SK layer did not need), `a_ty_mode_compat_{hole,arrow}_inv`
+ `a_split_ty_shape`, `a_split_wf`, `a_guess_mono_wf`, `a_wf_aenv_decls_app`,
`a_isub_strip_var_typ_mid`, `a_wf_ptyp_strip_mid`.

⛔ **NEXT: the `ad_pat_sub_gv` composition gap (§6), then the two completeness
theorems.**

---

### 7.5-history What was next — thm:sound-type-inference (STARTED)

`frost/algo/prop_soundness_typing.v` (NEW) holds the kit so far, all Qed and
axiom-free.  The statement to aim at is theorem 1's mirror, one layer up
(paper: "our goal is to show `typp[M]{Θ1}{M}{bid A}` where
`Θ1 ⊢ inh{P} ⊳ bid{A}` and `inc{Θ0}{Θ1}`"):

    Theorem a_typing_sound : forall m Θ0 P0 e A Θ1,
      Θ0 ⊢ₐ[ m ; P0 ] e ⦂ A ⊣ Θ1 ->
      a_wf_aenv Θ0 ->
      (forall x Ps, binds x (abind_var_skl Ps) Θ0 -> Θ0 ⨟ empty ⊢ₚₛᵃ Ps) ->
      Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
      a_ty_mode_compat m P0 ->
      a_wf_exp Θ0 e ->
      Θ0 ⊴ Θ1 /\ a_wf_aenv Θ1 /\
      exists B, btyp_to_ptyp B = A /\
        (Θ1 ⊢ˢᵃ[ m ] e ⦂ B) /\
        (Θ1 ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh P0) ⊳ (btyp_to_bskl B))

**Banked (`prop_soundness_typing.v`):**

| § | contents |
|---|---|
| §1 | `btyp_to_bskl_ptyp_to_btyp_inh`, `btyp_to_ptyp_open`, `ptyp_to_btyp_inh_open`, and `btyp_syn_painting_inv` (a colouring whose painting is SYNTHESISED is the all-synthesised one — how `sd-Freeze`'s `ptyp_to_btyp_syn B` shape is read off the IH's `◇ ⊳ bid(B)` through `ad_refine_syn_syn_l`) |
| §2 | ⭐ `ad_refine_syn_inh_tyequiv` — **a refinement between two GHOST-FREE paintings IS a type equivalence**.  Refinement's job is filling ghosts; between paintings of plain types only the structural rows and the two flexible lookups can fire, which is exactly `≡ᵗ`'s generating set.  Δ plays no part, because `a_tyequiv__all` binds nothing in Θ |
| §3 | ⭐ `a_consis_chk_tyequiv` — **the `Freeze` ingredient**, i.e. the paper's "which further gives `Θ2 ⊢ B ≡ A`", DERIVED from §7.3's transport as prescribed |
| §4 | `a_typing_tm_ge` — reverse tm-verbatim for `a_typing` (the `AT-Abs` row additionally crosses the `guess^TY` block `αs`, which is flexible-only) |
| §5 | `a_tyequiv_isub_le`, `ad_sd_typing_isub_tm` — stability under `⊴` + tm-verbatim; the ∀-peeling rows push a RIGID entry, so they use `a_isub_cons_tvar` |
| §6 | `ad_sd_typing_subst_tm` / `ad_sd_typing_rename_tm` — term-variable renaming, the exists-fresh → cofinite bridge the SIX term-binder rows need.  Its App row substitutes into the embedded SKELETON-inference premise, which is what `ad_pat_subst_tm` is for |
| §7 | ⭐ `btyp_inh_painting_inv` / `btyp_check_colouring` — **in CHECK mode the colouring is FORCED** |
| §8 | ✅ `ad_sd_typing_mod_comp_ty` (item 1 of "left", below) + its kit |
| §9 | ✅ `a_guess_mono_refine` (item 4's second half) |

#### ✅ §8 — `ad_sd_typing_mod_comp_ty` (2026-08-06, sixth pass)

The `ad_pat_mod_comp_sk` mirror, Qed and axiom-free.  ⭐ **It is not that
proof one sort up.**  At the SK layer `mod_comp_sk` is stated on a `bskl` —
exactly what the subtyping premise's target IS — so the base rows read the
fact straight off the premise.  At the TY layer `mod_comp_ty` is stated on a
`btyp` while the premise's target is that `btyp`'s SKELETON, so two shape
bridges are needed:

| bridge | statement | needs lc? |
|---|---|---|
| `is_styp_of_is_sskl_erase` | `is_sskl (btyp_to_bskl B) -> is_styp B` | no — `is_sskl` carries it |
| `is_ityp_of_erase_inh` | `btyp_to_bskl B = pskl_to_bskl_inh P -> is_ityp B` | ⚠️ YES |

The CHECK bridge needs local closure because `btyp_to_bskl (btyp_var_b n)`
and `pskl_to_bskl_inh (pskl_var_b n)` agree while a BOUND variable is not
`is_ityp`.  It is supplied from the `Check` row's own consistency premise —
hence `ad_pat_consis_lc_r` (a consistency's target is locally closed; the
only non-immediate row is `__hole`, whose fill carries the skeleton wf) and
`lc_btyp_of_lc_bskl_erase` (erasure to the skeleton reflects lc, via
degree).

The other lc source is the appendix's `≡ᵗ` premises, at `Freeze` and
`AbsAnnoCheck(→)`: `a_tyequiv_lc` carries **`a_wf_aenv Θ`**, because the
`flex_def` row hands back a flexible's DEFINITION and only the context says
it is a monotype.  That is the same hypothesis `d_typing_skmod` carries as
`d_wf_denv`, so the statement matches the declarative one's shape.

⭐ The induction never goes under a binder: every row but `App` discharges
its goal from its own premises, and `App` recurses at the SAME context.

#### ✅ §9 — `a_guess_mono_refine` (2026-08-06, sixth pass)

    Corollary a_guess_mono_refine : forall Θ P Ξ A Θ1 Δ,
      a_guess_mono Θ P Ξ A ->
      (forall α, α `in` ftvar_in_pskl P -> α `in` Δ \/ a_binds_tvar α Θ1) ->
      (forall α1, binds α1 abind_flex_mono Ξ -> a_binds_tvar α1 Θ1) ->
      Θ1 ⨟ Δ ⊢ᵣᵃ (pskl_to_bskl_inh P) ⊳ (pskl_to_bskl_inh (ptyp_to_pskl A))

Filling a ghost with a fresh flexible IS a refinement step; a universal
ghost is DROPPED, so `⫯.P` is `__tophole_remove`, not `__tophole_keep`.
⚙ SIZE induction, exactly like `a_guess_mono_consis_size` (prop_flex.v):
the source is exists-fresh, the target cofinite, so the ∀ row turns ONE
guess instance into a family via `a_guess_mono_open_at`.  ⭐ The ∀ row puts
its witness in **Δ**, not Θ — the §7.3 decoupling — and that is sound here
for the reason it was unsound there: `__hole`'s fill is Δ-free BY RULE, and
guess^TY's fills are the generated flexibles, which live in Θ1.

⭐ **§7 removes an item this hand-off previously listed.**  The two ∀-peeling
rows (`AT-AbsCheck`/`AT-AbsAnnoCheck` `_step`) are cofinite in a RIGID α, so
the naive route to their declarative counterparts wants a type-variable
renaming for `ad_sd_typing` — which would mean renaming lemmas for every
judgement it embeds.  It is not needed: those rows run at TC, where
`mod_comp_ty B mode_tc` is `is_ityp B` and an inherited type has only ONE
colouring, so the IH's colouring at each α is already
`ptyp_to_btyp_inh` of its erasure — i.e. of the `open … (btyp_var_f α)`
shape the rule wants.  Only the TERM-binder rows need a renaming (§6).

#### ⭐ Consistency check against the paper's proof (2026-08-06)

Read `proofs.tex` app:proof-type-inference case by case.  The route matches;
the deviations are the ones already recorded, plus two NEW obligations the
paper asserts inline.

**Same route**: base rows via thm:sound-subtyping; `Freeze` via
thm:sound-consistency plus a `≡ᵗ` step; the Abs rows via
lemma:suffix-moving and the declarative Abs rule; `App` via
thm:sound-skeleton-inference plus stability; "refinement judgements are
stable under dropping term variables" = the `ad_refine_syn_strip_tm_*`
corollaries.

**⚠️ Suffix ERASURE really is needed here — the asymmetry is the paper's
own.**  Theorem 1 got away without it because `a_pat`'s check rows KEEP the
pending suffix in their output (`⊣ Ξ,Θ1`), so the theorem's conclusion
context already contains it.  `a_typing`'s four CHECK rows DROP it
(`abs_check_step ⊣ Θ1`, `abs_check_base ⊣ Θ2`, the two anno ones likewise),
exactly as the paper's rules do, and the paper's `AbsCheck` case discharges
the mismatch with lemma:suffix-erasure ("since all variables in Ξ do not
appear in `inh{B}`").  The two INFER-mode rows (`AT-Abs`, `AT-AbsAnno`) keep
the suffix and need no erasure.  So §1's erasure is now a REAL prerequisite,
for four rows only.

**⚠️ lemma:split-refine is needed here too, and only in the same four rows.**
`a_ty_mode_compat`'s TC row admits ANY `ptyp_to_pskl A`, so at
`abs_check_base` the split's input can be a flexible variable and
`a_split__flex` IS reachable — §2's hard row.  But at `AT-Abs` /
`AT-AbsAnno` the mode is not TC, so `a_ty_mode_compat` forces `□` or an
arrow and the theorem-1 dodge (`a_split_sk_shape`'s analogue) still applies:
NO split-refine and NO refinement transitivity there, even though the paper
invokes both.  ⚙ When you do build split-refine, state it COLOURED —
`Θ1 ⨟ ∅ ⊢ᵣᵃ (pskl_to_bskl_inh P0) ⊳ (pskl_to_bskl_inh (pskl_arrow P Q))` —
not in §2's uncoloured `ad_refine_pskl` form, which is not what the rows
consume.

**⛔ TWO NEW inline steps with no lemma** (candidates for PAPER-GAPS, same
species as thm:sound-skeleton-inference's AbsAnno step):

1. `AT-App`, "Thus by ⑧ and ⑬, we have `Θ3 ⊢ N ⦂ inh{A}`": the IH gives the
   argument checked at `inh{A'}` and the rule wants it at `inh{A}`, bridged
   by `Θ3 ⊢ A ≡ᵗ A'`.  That is a TYPING-under-`≡ᵗ` transport at TC, stated
   nowhere.  ⭐ Note `Θ3 ⊢ A ≡ᵗ A'` itself is §2's
   `ad_refine_syn_inh_tyequiv` again — a SECOND consumer of it, which is
   good evidence the lemma is the right shape.
2. `AT-Abs`, "By ⑯ and definition of `guess^TY`, we have
   `Θ1,ᾱ ⊢ inh{P} ⊳ inh{A}`": a refinement property of `a_guess_mono` that
   the mech has no lemma for (prop_flex.v has only its freshness / decls /
   ftv facts).

#### ⭐ THE ELEVEN-ROW INDUCTION — row-by-row plan (2026-08-06)

Model it on `a_pat_sound` (prop_soundness_pat.v:2034, ~420 lines): the
skeleton is identical, and eight of the eleven rows have a direct
counterpart there.  Statement: §7.5's `a_typing_sound`, with the SAME two
extra hypotheses theorem 1 carries (`a_wf_exp` + the disciplined skl-entry
wf), and `a_ty_mode_compat` in place of `a_sk_mode_compat`.

| # | `a_typing` row | theorem 1's counterpart | what is NEW |
|---|---|---|---|
| 1 | `AT-Unit` | `AP-Unit` | `a_sub_sound_thm` at the **TY** sort |
| 2 | `AT-Var` | `AP-Var(typ)` | — (no skeleton entry: `a_typing`'s Var reads `abind_var_typ` only) |
| 3 | `AT-Anno` | `AP-Anno` | ⚠️ TWO sequential premises — `a_pat`'s Anno does not recurse.  Chain Θ0→Θ1→Θ2 and sustain the skl-entry-wf hypothesis with `a_typing_tm_le`/`_tm_ge` (§4) |
| 4 | `AT-Freeze` | `AP-Freeze` | `a_consis_chk_sound` + ⭐ `a_consis_chk_tyequiv` (§3) for `sd-Freeze`'s `≡ᵗ`, and `btyp_syn_painting_inv` (§1) for its `syn` shape |
| 5 | `AT-Abs` | `AP-Abs` | ⭐⭐ the `guess^TY` block `αs` sits BETWEEN the binder and the context, so the ⊴-peel must cross it (`a_guess_mono_decls` says it is flexible-only — that is how `a_typing_tm_ge` crosses it).  Its refinement obligation is `a_guess_mono_refine` (§9) |
| 6 | `AT-AbsAnno` | `AP-AbsAnno` | split + `a_consis_chk` + body; the `≡ᵗ` of `sd-AbsAnno` from `a_consis_chk_tyequiv` |
| 7 | `AT-AbsCheck(∀)` | — | ⭐ `ad_sd_typing_strip_suffix` (the output DROPS Ξ) + `btyp_inh_painting_inv` (§7): at TC the colouring is forced, so the IH's `B` is already `open … α`-shaped |
| 8 | `AT-AbsCheck(→)` | — | ⭐ erasure + `a_split_refines` (§11) — here `a_ty_mode_compat`'s TC row admits any `ptyp_to_pskl A`, so `a_split__flex` IS reachable |
| 9 | `AT-AbsAnnoCheck(∀)` | — | erasure, as row 7 |
| 10 | `AT-AbsAnnoCheck(→)` | — | erasure + split-refine + `a_consis_chk_tyequiv` |
| 11 | `AT-App` | `AP-App` | `a_pat_sound` (theorem 1!) on premise 1; ⭐ invert the IH's arrow refinement (`ad_refine_syn_arrow_inv`) to get `sd-App`'s premise 2; the NEW fourth `≡ᵗ` premise from `ad_refine_syn_inh_tyequiv` (§2) |

⚙ Rows 7–10 are the four that need BOTH new lemmas (erasure and
split-refine), and they are the four whose output drops the pending suffix.
Rows 1–6 and 11 need neither — theorem 1's dodge (`a_split_sk_shape`)
applies at 5/6 because the mode is not TC there.

⚙ The `a_wf_exp` inversions (`a_wf_exp_abs_inv`, `_abs_anno_inv`, …) and
the ⊴-peel kit (`uniq_mid_eq`, `a_inc_weaken_suffix_target`,
`a_isub_peel_var_typ_mid`) are all in prop_soundness_pat.v §3–§4 already.

**Left for the theorem itself** (status 2026-08-06, SEVENTH pass):

1. ✅ **DONE** — `ad_sd_typing_mod_comp_ty` (§8 above).
2. ✅ **DONE** — §1's suffix ERASURE, all six judgements
   (`algo/prop_suffix_erase.v`, Qed and axiom-free).  The two the theorem
   quotes are `ad_pat_strip_suffix` and `ad_sd_typing_strip_suffix`.
3. ✅ **DONE** — §2's `lemma:split-refine`, COLOURED (`a_split_refines`,
   prop_soundness_typing.v §11).  ⭐ Its enabler is NOT the `≡ᵗ ⟹ ⊳`
   bridge this hand-off previously scouted: it is
   `ad_pat_consis_mono_to_refine` (§10) — **a monotype CONSISTENCY is a
   refinement** — because once the subject is a monotype painting the two
   judgements have the same five rows.  Going through the consistency needs
   neither refinement symmetry nor TRANSITIVITY (the latter is false:
   `cex/cex_refine_not_transitive.v`); `consis_mono_sym`
   (prop_mono_bridge.v) supplies the direction change that was the only
   reason the `≡ᵗ` route wanted symmetry.
   ⚠️ It carries a FRESHNESS side condition: `a_split__flex` invents two
   flexibles and the mech's rule records no freshness for them.
4. ✅ **DONE** (by adding the appendix's fourth premise) — `AT-App`'s
   typing-under-`≡ᵗ` transport at TC (PAPER-GAPS, WATCH 1).  Original note:
   — **the last missing ingredient**.  Its equivalence half is
   `ad_refine_syn_inh_tyequiv` (§2), already proved; what is missing is the
   transport itself, which bottoms out in an `ad_pat_consis` **TARGET**
   transport along `≡ᵗ` — the mirror of `skl_tyequiv_consis_transport`
   (prop_completeness_consis.v) and `ad_pat_consis_tyequiv_subject`
   (prop_sub_msubst_equiv.v), which exist only on the SUBJECT side.  ⚙ Do
   it in BOTH directions at once, the way `skl_tyequiv_consis_transport`
   does, so `≡ᵗ`'s `sym` row closes.  ⛔ There is no dodge: B1 is
   existentially chosen by `sd-App`, but every way of re-choosing it needs
   the same species of transport in the function's DOMAIN instead.
   ⚙ Cheaper alternative to raise with the authors first: `sd-App` may
   simply be MISSING the fourth `≡ᵗ` premise, the appendix already having
   added one to `sd-Freeze` / `sd-AbsAnnoCheck` / `sd-AbsAnno` for exactly
   this reason.
   ✅ **DONE** — the other half, `AT-Abs`'s `guess^TY` refinement (§9).
5. ✅ **DONE** — the eleven-row induction (see §7.5's header).  Original note:  ⭐ The one row with no counterpart in
   theorem 1 is `AT-Abs`: it deposits a `guess^TY` block `αs` BETWEEN the
   binder and the context, so the ⊴-peel has to cross it
   (`a_guess_mono_decls` says the block is flexible-only, which is also how
   `a_typing_tm_ge` crosses it).

⭐ **ALL FIVE ARE CLOSED, and so is the theorem** — see §7.5's header for the
statement as proved, the four rule changes it forced, and the §12 kit.

Then the `ad_pat_sub_gv` composition gap (§6) before the two completeness
theorems.
