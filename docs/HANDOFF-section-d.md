# HANDOFF — section D (`proofs.tex`): soundness and completeness of skeleton and type inference

**Status 2026-08-06.** The definitional layer is DONE and green (`dd1f176`):
`frost/decorated_algo/def_decl_algo_typing.v` defines `ad_pat` (skeleton
inference over Θ) and `ad_sd_typing` (syntax-directed typing over Θ), which is
what `PROGRESS.md`'s map had flagged as the one missing definitional piece.
Everything below is what remains: six support lemmas (one already proved) and
four theorems.

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

## 1. `lemma:suffix-moving` + `lemma:suffix-erasure` — the big one, do it FIRST

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

⛔ **Two things the paper's "straightforward induction on the typing
derivation" hides.**

1. **The dependency relation does not exist yet.**  Closest existing pieces:
   `a_suffix` (algo/def_extra.v — a block of flexible-only entries),
   `no_flex_dep Δ Θ` and `flex_above_free Δ Θ`
   (prop_soundness_consis.v:1452/1457).  Neither is the paper's "Ξ does not
   depend on entries in Θ₂".  Decide its shape ONCE — every later lemma quotes
   it.  Suggested: `forall β τ, binds β (abind_flex_mono_def τ) Ξ ->
   ftvar_in_ptyp τ ∩ dom Θ2 [=] empty`, plus `dom Ξ ∩ dom Θ2 [=] empty`.
2. **The induction is not over one judgement.**  `ad_sd_typing` embeds SIX
   different premise forms — `ad_pat_sub` at `a_sub_mode_ty`, `ad_pat`,
   `ad_refine_syn`, `a_wf_ptyp`, `a_tyequiv`, `mod_comp_ty` — and each needs
   its OWN moving/erasure lemma before the typing induction can close a single
   base rule.  That per-judgement kit is the bulk of the work; the typing
   induction on top of it really is routine.  `mod_comp_ty` is context-free, so
   five kits, not six.

Do these first: everything downstream in section D quotes them, and the kit is
reusable for the two soundness theorems.

---

## 2. `lemma:split-refine` — NOT a straightforward induction

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

## 3. `lemma:precision-sub` — check the Ghost row before believing the statement

    Lemma ad_precise_extends_pat_sub : forall Θ Δ P' P Ψ M Q,
      Θ ⨟ Δ ⊢ₚᵣᵃ P' ⊑ P ->
      Ψ ⨟ Θ ⊢ₛᵃ[ a_sub_mode_sk | M ] (pskl_to_uskl P) ⩽ Q ->
      Ψ ⨟ Θ ⊢ₛᵃ[ a_sub_mode_sk | M ] (pskl_to_uskl P') ⩽ Q.

⚠️ **Scout this one before committing to the statement.**  `P' ⊑ P` permits
`P' = □` (`ad_refine_pskl__hole`, which only needs `Q` well-formed) and
`P' = ⫯P''` (`__tophole_remove`) and `P' = α̂` (`__flex_l`).  At `P' = □` the
only applicable subtyping row is `ad_pat_sub__ghost`, whose target must be an
INHERITED PAINTING `pskl_to_bskl_inh P` and which carries `mod_comp_sk` — so
for an arbitrary `Q` produced by the `P` derivation the conclusion is not
immediate.  Either the paper's `precise` is implicitly restricted here, or the
statement needs a side condition.  Settle that with a small probe first (a
`cex/` file if it turns out false — the tree's standing rule).

---

## 4. `lemma:precision-preserves-refinement` — ✅ ALREADY DONE

`ad_precise_preserves_refine` (prop_precise.v:585), Qed and audited in
`README.v`.  It carries three external wf side conditions beyond the paper
(`a_wf_aenv Θ`, Δ-disjointness from `dom Θ`, wf of the target) — the
WF-SIDE-CONDITIONS pattern again.  Nothing to do.

---

## 5. Context precision — a new definition plus one lemma

The paper's `⪯ctx` (proofs.tex, "Definition (Context precision)"), three rules:
empty; a non-term-variable entry copied verbatim; a term-variable entry made
more precise.  In mech terms the third is
`Θ' ⨟ ∅ ⊢ₚᵣᵃ P' ⊑ P` over the two `abind` term forms (`abind_var_skl` directly,
`abind_var_typ` through `ptyp_to_pskl` — cf. the new `abind_to_pskl`).

    Inductive ad_ctx_precise : aenv -> aenv -> Prop := (* Θ' ⪯ctx Θ *) ...

    Lemma ad_ctx_precise_pat : forall Θ' Θ M e Q,
      ad_ctx_precise Θ' Θ ->
      Θ ⊢ᵃ[ M ] e ⇨ Q ->
      Θ' ⊢ᵃ[ M ] e ⇨ Q.

The paper's proof sketch names the load-bearing step: "refinement and subtyping
judgements that do not involve a term-variable lookup are preserved because the
contexts have the same non-variable entries".  That is a **context-change
lemma for `ad_pat_sub` and `ad_refine_syn`** which does not exist yet — the
closest existing shapes are `a_looksub_lookeq_ctx_ftv_mono` (prop_looksub.v)
and `a_solve_sub_eq_ctx_change`.  Prove it over "same non-variable entries"
(same `abind_tvar` / `abind_flex_mono` / `abind_flex_mono_def` entries at the
same positions) and the rest follows.

`ad_pat__var` is the only interesting row: it reads the bound skeleton through
`abind_to_pskl`, then runs `ad_pat_sub` on its painting — so it needs §3's
`lemma:precision-sub` to push the entry's precision through.  **§3 gates §5.**

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
3. **Completeness + optimality of skeleton inference**
4. **Completeness + optimality of type inference**

⚠️ **3 and 4 will hit the `ad_pat_sub_gv` composition gap** (PROGRESS.md §4b):
they consume `a_sub_complete_thm`, which ASSUMES `ad_pat_sub_gv`, while
`a_sub_sound_thm` only CONCLUDES the plain `ad_pat_sub`.  The fix identified
there is to strengthen `a_subtag_sound_bundle` to conclude `_gv` — the content
is already proved (it is the last conjunct of `a_consis_sound` and
`a_consistag_sound_aux`), the only real cost being that `_gv` is fuel-indexed
so soundness must produce an `exists n` (`ad_pat_sub_to_n` is the precedent).
Do that between 2 and 3.
