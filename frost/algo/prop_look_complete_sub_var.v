(** P6-Sv — completeness of constraint collection and solving FOR VARIABLES,
    subtyping side ([lemma:complete-constraint-collection-solving-var],
    subtyping-proofs.tex:1696).

    ⚠️  READ FIRST: the paper's statement is FALSE as given —
    `frost/algo/cex/cex_p6sv_forall_flex.v` refutes it (Qed, axiom-free) at
    ρ = IDENTITY, with the full premise set that closes the consistency twin
    P6-Cv.  This file builds the REPAIRED statement, whose one extra premise
    is [flex_shield] below.  Rationale, call-site analysis and the
    implementation experiments behind it: docs/PAPER-GAPS.md (final entries)
    and docs/DESIGN-completeness-subtyping.md §6 (x)/(y)/(z).

    THE REPAIR IN ONE LINE.  Wherever the constraint payload [P0] has a raw
    Θ0-FLEXIBLE, the facing part of the guess [ψa] must be Δρ-CLEAN *and*
    TAG-FREE.  The Δρ half is P6-Cv's [flex_apart] (a ρ-replaced rigid
    variable opposite a flexible payload is unreachable — LE-FlexR
    freshening).  The TAG half is what the subtyping level adds, and it is
    forced: [Sub-ForallL] turns a TAGGED quantifier of ψa into a ρ-replaced
    variable one step later, so "clean now" is worthless unless "no tags
    now" keeps it clean later.

    TWO FAILURE SHAPES (why the premise must be POSITIONAL and TAG-AWARE):

      (1) machine-checked, cex_p6sv_forall_flex.v — the payload is the whole
          flexible:  Pi = ∀β.β→β,  P0 = α̂,  ψa = ∀^ε β.β→β.
          SolS-ForallL, then SolE-FlexR at the body, gives Pa = ∀β.α̂ and
          the obligation ⟨⟩ ⊑ᵖ β.

      (2) hand-verified (NOT yet machine-checked) — the flexible sits at an
          ARROW-LEFT, i.e. at a CONSISTENCY position, under the same
          ForallL:  Pi = ∀β.((β→β)→⟨⟩),  P0 = α̂→⟨⟩,
          ψa = ∀^ε β.((β→β)→⟨⟩),  M = FN TC,  κα̂ = ⟨⟩→⟨⟩.
          SolS-ForallL, SolS-Arrow, then SolE-FlexR on the left (Pi's left
          component is an ARROW, so SolE-Var does not shield it) gives
          Pa = ∀β.(α̂→⟨⟩) and again ⟨⟩ ⊑ᵖ β.
          ⇒ a premise guarding only the RESULT SPINE of P0 is TOO WEAK, and
            a global "P0 flex-free ∨ ψa tag-free" is TOO STRONG (it would
            reject the legitimate arrow shape α̂→⟨⟩ against ⟨⟩→∀^ε β.…).

    …and one row in the OTHER direction, which keeps the premise from being
    too strong: a ρ-REPLACED RIGID VARIABLE ([fsh_rho_var]) is safe opposite
    ANY payload.  With [ψa = ∀^ε β.β] and [P0 = α̂] the algorithm SUCCEEDS
    (precision forces [Pi = ∀β.β]; SolS-ForallL then SolS-Var — the body is
    a VARIABLE — returns [Pa = ∀β.β]); it is only a COMPOUND body like the
    counterexample's [β→β] that sends the solve to SolE-FlexR.  See
    [flex_shield_excludes_cex]; this direction is recorded in
    [fsh_rho_var]'s own comment, which is what keeps the premise from
    being made too strong.

    Hence [flex_shield]: positional, with the non-aligned base case
    demanding BOTH conditions.  Its rules are chosen so that every descent
    of THIS induction (arrow = both sides, Sub-ForallR = P0 only,
    Sub-ForallL = ψa only, Sub-UnivGhostL/LG = ψa only) pushes it down —
    see the descent lemmas, whose one-sided cases go through precisely
    because the induction hypothesis re-derives the OPPOSITE-sided rule. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.def_tags.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_metasubst.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_consis_precise.  (* d_tags_skl_var_inv *)
Require Import src.frost.algo.prop_consis_sound.    (* a_wf_pskl_lc *)
Require Import src.frost.algo.prop_decorate_sub.    (* lc_uskl_to_pskl_local *)
Require Import src.frost.algo.prop_pat_sub.
Require Import src.frost.algo.prop_refine.       (* ad_refine_syn_weaken *)
Require Import src.frost.algo.prop_looksub.
Require Import src.frost.algo.prop_sub_sound.    (* a_wf_pskl_open *)
Require Import src.frost.algo.prop_solve_sub.
Require Import src.frost.algo.prop_consis_complete.  (* a_wf_pskl_ftv_dom *)
Require Import src.frost.algo.prop_sub_complete.
Require Import src.frost.algo.prop_look_complete.
Require Import src.frost.algo.prop_look_complete_var.
Require Import src.frost.algo.prop_look_complete_cstr.  (* the ∀-binder kit,
    [mono_ptyp_to_uskl_syn_tskl], [ftag_in_uskl_ptyp_to_uskl_syn], … *)

Set Implicit Arguments.

(* ===================================================================== *)
(*  Raw-flexible-freedom of a payload                                     *)
(* ===================================================================== *)

(** [pskl_flex_free] and its kit MOVED UP to prop_look_complete.v — it is
    now a base rule of [flex_apart] too ([fa_flexfree]), so it must be in
    scope before P6-Cv.  See DESIGN §10. *)

(* ===================================================================== *)
(*  ⭕⭕ [flex_shield] AND ITS KIT MOVED OUT (2026-08-05)                    *)
(*      → frost/algo/cex/def_flex_shield.v                                 *)
(*                                                                        *)
(*  It was P6-Sv's repair premise, invented against                        *)
(*  cex/cex_p6sv_forall_flex.v.  It has had NO consumer in this file since *)
(*  2026-08-03 (every use was a relay), and under the authors' repaired    *)
(*  [SolE-FlexR] that counterexample is retracted outright.  What still    *)
(*  refers to it is exactly the cex/ files that record the history —       *)
(*  which is where the definition, its transport kit and the regression    *)
(*  test [flex_shield_excludes_cex] now live.                              *)
(* ===================================================================== *)


(** A GUARDED payload skeleton is never precise to a dotted universal ghost:
    its κ-image is unit / a mono paint / an arrow, and the ∀◈ target has no
    matching rule (the mono-paint chain is [ad_ppre_mono_paint_topholeg_absurd]).
    This is what rules out [P-UnivGhostRemove] wherever well-formedness has
    already made the body guarded. *)
Lemma ad_ppre_guarded_topholeg_absurd : forall Θ0 Θ κ Δ Ψ P ψ0,
  a_wf_aenv Θ ->
  κ ∷ Θ0 ⊑ Θ ->
  guarded_pskl P ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ P) ⊑ᵖ[ Ψ ] (uskl_topholeg ψ0) ->
  False.
Proof.
  intros Θ0 Θ κ Δ Ψ P ψ0 HwfΘ Hκ Hg Hpre.
  destruct Hg as [ | α | P1 P2 Hlc1 Hlc2 ]; cbn [msubst_pskl] in Hpre.
  - inversion Hpre.
  - eapply ad_ppre_mono_paint_topholeg_absurd;
      [ exact HwfΘ | exact Hpre | reflexivity | reflexivity
      | eapply a_inc_lookup_mono; exact Hκ ].
  - inversion Hpre.
Qed.

(** ρ transports GUARDEDNESS of the erasure from the subject to the guess.
    The congruence rows need local closure of the guess — which is free:
    [is_tskl] gives it ([is_tskl_lc]).  The ∀/ghost congruences are vacuous,
    since their SUBJECT already erases to a non-guarded skeleton. *)
Lemma uskl_rho_guarded_erase : forall NM Θ Δρ Ψρ R' R,
  uskl_rho NM Θ Δρ Ψρ R' R ->
  lc_uskl R ->
  guarded_pskl ⌊ R' ⌋ˢ ->
  guarded_pskl ⌊ R ⌋ˢ.
Proof.
  intros NM Θ Δρ Ψρ R' R H Hlc Hg; destruct H; cbn [uskl_to_pskl] in Hg |- *;
    try assumption; try solve [ inversion Hg ].
  - (* leaf: the guess is a variable *) apply guarded_pskl__var.
  - (* arrow: both sides are arrows; lc comes from the guess *)
    inversion Hlc; subst.
    apply guarded_pskl__arrow; apply lc_uskl_to_pskl_local; assumption.
Qed.

(** A □ input skeleton solves to □ or to a universal ghost — the only rules
    with a [□] left-hand side are SolS-Vacuous, SolS-GhostL and
    SolS-GhostLF (SolS-ForallR just threads the output through). *)
Lemma a_solve_sub_hole_output : forall Θ0 m P0 Ξ Pa,
  Θ0 ⊢ₛ pskl_hole ≼[ m ] P0 ⤳ Ξ ⨾ Pa ->
  Pa = pskl_hole \/ exists B, Pa = pskl_tophole B.
Proof.
  intros Θ0 m P0 Ξ Pa H.
  remember pskl_hole as Ph eqn:HeqP.
  (* surviving rows: SolS-Vacuous (output = the □ input), SolS-Check (□ is
     not guarded), SolS-ForallR (output = the body's), SolS-GhostLF and
     SolS-GhostL (output = a ∀◇) *)
  induction H; try discriminate HeqP; subst;
    solve [ left; reflexivity
          | right; eexists; reflexivity
          | match goal with Hg : guarded_pskl pskl_hole |- _ => inversion Hg end
          | (* SolS-ForallR is exists-fresh now: ONE premise, one IH *)
            apply IHa_solve_sub; reflexivity ].
Qed.

(** A □ subject solves no tags: the only rules with a hole subject are
    [P-Ghost] and the target-side flexible unfolding. *)
Lemma ad_ppre_hole_subject_tags : forall Θ Δ Ψ ψ,
  Θ ⨟ Δ ⊢ pskl_hole ⊑ᵖ[ Ψ ] ψ ->
  Ψ [=] empty.
Proof.
  intros Θ Δ Ψ ψ H.
  remember pskl_hole as P eqn:HeqP.
  induction H; try discriminate HeqP; subst;
    solve [ assumption | apply IHad_partial_precise; reflexivity ].
Qed.

(** Stripping a ∀◇ from the SUBJECT against a GUARDED guess: only
    [P-UnivGhostRemove] applies — [Fill] and [Keep] need a ∀^ε / ∀◈ guess,
    whose erasure is not guarded — and the target-side flexible unfolding is
    rebuilt after recursing through the (monotype) definition. *)
Lemma ad_ppre_tophole_strip : forall Θ Δ Ψ B ψ,
  a_wf_aenv Θ ->
  Θ ⨟ Δ ⊢ (pskl_tophole B) ⊑ᵖ[ Ψ ] ψ ->
  guarded_pskl ⌊ ψ ⌋ˢ ->
  Θ ⨟ Δ ⊢ B ⊑ᵖ[ Ψ ] ψ.
Proof.
  intros Θ Δ Ψ B ψ HwfΘ H.
  remember (pskl_tophole B) as P eqn:HeqP.
  revert B HeqP; induction H; intros B' HeqP Hg;
    try discriminate HeqP; inversion HeqP; subst.
  - (* remove *) assumption.
  - (* fill: the guess is a ∀^ε, whose erasure is a ∀ — not guarded *)
    cbn [uskl_to_pskl] in Hg; inversion Hg.
  - (* keep: the guess is a ∀◈ — likewise *)
    cbn [uskl_to_pskl] in Hg; inversion Hg.
  - (* flex_r: recurse through the definition, then rebuild *)
    eapply ad_ppre__flex_r; [ eassumption | ].
    apply (IHad_partial_precise HwfΘ B' eq_refl).
    match goal with |- guarded_pskl ⌊ ptyp_to_uskl_syn ?τ ⌋ˢ =>
      replace (uskl_to_pskl (ptyp_to_uskl_syn τ)) with (ptyp_to_pskl τ)
        by (symmetry; apply uskl_to_pskl_ptyp)
    end.
    apply mono_ptyp_to_pskl_guarded.
    eapply a_wf_aenv_binds_def_mono; eassumption.
Qed.

(** Lifting a precision judgment under a dotted universal ghost on the
    TARGET.  Only the two subject shapes a □-input solve can produce are
    needed ([a_solve_sub_hole_output]). *)
Lemma ad_ppre_lift_topholeg : forall Θ Δ Ψ P ψ0,
  a_wf_aenv Θ ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ0 ->
  Δ ∩ ftvar_in_uskl ψ0 [=] empty ->
  guarded_pskl ⌊ ψ0 ⌋ˢ ->
  (P = pskl_hole \/ exists B, P = pskl_tophole B) ->
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] (uskl_topholeg ψ0).
Proof.
  intros Θ Δ Ψ P ψ0 HwfΘ Hpre HΔ Hg Hshape.
  destruct Hshape as [-> | (B & ->)].
  - (* □ : re-apply P-Ghost; the ghost adds no free variable *)
    apply ad_ppre__hole;
      [ eapply ad_ppre_hole_subject_tags; exact Hpre
      | cbn [ftvar_in_uskl]; exact HΔ ].
  - (* ∀◇B : strip the subject's ghost, then keep it against the ∀◈ *)
    apply ad_ppre__tophole_keep.
    eapply ad_ppre_tophole_strip; [ exact HwfΘ | exact Hpre | exact Hg ].
Qed.

(** The SUBJECT's free variables of a partial-precision derivation come from
    the guess, from Δ, or from Θ's own definitions.  This is what the ∀
    cases use to strip their binder from the OUTPUT — the paper's "by the
    precision conclusion, β ∉ ftv(κa P_a), and thus β ∉ ftv(P_a)"
    (subtyping-proofs.tex:1898). *)
(** A variable the GUESS avoids, that is not a Δ-binder, not a DEFINED
    flexible of Θ and not mentioned by any of Θ's definitions, is avoided by
    the precision's SUBJECT too.  This is what the ∀ cases use to strip
    their binder from the OUTPUT — the paper's "by the precision conclusion,
    β ∉ ftv(κa P_a), and thus β ∉ ftv(P_a)" (subtyping-proofs.tex:1898).
    NB the last two conditions are real: the [flex_l] row puts a defined
    flexible of Θ into the subject, and [flex_r] unfolds a definition, so a
    definition's own variables can surface there. *)
Lemma ad_partial_precise_src_ftv_avoid : forall Θ Δ Ψ P ψ,
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall α, α `notin` ftvar_in_uskl ψ ->
  α `notin` Δ ->
  (forall τ, ~ binds α (abind_flex_mono_def τ) Θ) ->
  α `notin` def_ftv Θ ->
  α `notin` ftvar_in_pskl P.
Proof.
  intros Θ Δ Ψ P ψ H; induction H; intros α0 Hψ HΔ Hnf Hdf;
    cbn [ftvar_in_pskl ftvar_in_uskl] in *.
  - clear; fsetdec.
  - (* var: the same variable on both sides *) clear - Hψ; fsetdec.
  - (* arrow *)
    pose proof (IHad_partial_precise1 α0 ltac:(clear - Hψ; fsetdec) HΔ Hnf Hdf).
    pose proof (IHad_partial_precise2 α0 ltac:(clear - Hψ; fsetdec) HΔ Hnf Hdf).
    clear - H2 H3; fsetdec.
  - (* ∀ *)
    pick fresh α for (L `union` ftvar_in_pskl P `union` ftvar_in_uskl ψ
                        `union` singleton α0).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α)) as Hup.
    cbn in Hup.
    assert (Hαα0 : α <> α0)
      by (apply not_eq_sym; apply notin_singleton_1; clear - Fr; solve_notin).
    pose proof (H0 α ltac:(clear - Fr; solve_notin) α0
                  ltac:(clear - Hup Hψ Hαα0; fsetdec)
                  ltac:(clear - HΔ Hαα0; fsetdec) Hnf Hdf) as Hα.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_lower P (pskl_var_f α)) as Hlo.
    clear - Hα Hlo; fsetdec.
  - (* □ *) clear; fsetdec.
  - apply IHad_partial_precise; assumption.
  - (* fill: the binder joins Θ as a TVAR, adding no definition *)
    pick fresh α for (L `union` ftvar_in_pskl P `union` ftvar_in_uskl ψ
                        `union` singleton α0 `union` dom Θ).
    pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_upper ψ (uskl_var_f α)) as Hup.
    cbn in Hup.
    assert (Hαα0 : α <> α0)
      by (apply not_eq_sym; apply notin_singleton_1; clear - Fr; solve_notin).
    pose proof (H0 α ltac:(clear - Fr; solve_notin) α0
                  ltac:(clear - Hup Hψ Hαα0; fsetdec)
                  HΔ
                  ltac:(intros τ0 Hb;
                        destruct (binds_cons_1 _ _ _ _ _ _ Hb)
                          as [[_ Habs] | Hb']; [ discriminate Habs | ];
                        exact (Hnf τ0 Hb'))
                  ltac:(cbn [def_ftv]; exact Hdf)) as Hα.
    cbn [ftvar_in_pskl] in Hα. clear - Hα; fsetdec.
  - apply IHad_partial_precise; assumption.
  - (* flex_l: the subject is a DEFINED flexible of Θ *)
    intros Hin.
    assert (Heq : α0 = α) by (clear - Hin; fsetdec); subst.
    exact (Hnf τ H).
  - (* flex_r: the guess unfolds to a definition, whose variables are
       covered by [def_ftv] *)
    apply IHad_partial_precise; try assumption.
    rewrite ftvar_in_uskl_ptyp_to_uskl_syn.
    intros Hin. apply Hdf.
    pose proof (@def_ftv_binds Θ α τ H) as Hsub. clear - Hsub Hin; fsetdec.
Qed.

(** Deciding [a_non_flex] on a GUARDED skeleton: it fails only for a
    flexible variable. *)
Lemma a_non_flex_guarded_dec : forall Θ0 P,
  guarded_pskl P ->
  a_non_flex Θ0 P \/ (exists α, P = pskl_var_f α /\ a_flex_tvar Θ0 α).
Proof.
  intros Θ0 P Hg; destruct Hg as [ | α | P1 P2 Hlc1 Hlc2 ].
  - left; split; [ apply lc_pskl_unit | intros Hf; inversion Hf ].
  - destruct (a_flex_tvar_dec Θ0 α) as [Hf | Hf];
      [ right; exists α; split; [ reflexivity | exact Hf ]
      | left; split;
          [ apply lc_pskl_var_f
          | intros Hfl; apply Hf; inversion Hfl; subst;
            [ left | right; eexists ]; eassumption ] ].
  - left; split;
      [ apply lc_pskl_arrow; assumption | intros Hf; inversion Hf ].
Qed.

(* ===================================================================== *)
(*  ρ-EXTENSION — what Sub-ForallL does to the ρ-relation                  *)
(* ===================================================================== *)

(** Sub-ForallL instantiates the guess's tagged quantifier, so the binder it
    opens becomes a ρ-REPLACED variable and the instantiation becomes its
    image: the paper's [ρ_b = ρ ∘ [ψ_b/β]] (subtyping-proofs.tex:1876).
    Mechanically that is a SUBSTITUTION on the subject side of [uskl_rho],
    which turns every β-position into a [urho__leaf].

    The tag set can only be bounded, not computed: if β does NOT occur in
    the guess, the instantiation contributes nothing, so the conclusion
    carries [Ψρ' ⊆ Ψρ ∪ Ψb] plus the two facts callers need — that Ψρ' still
    covers Ψρ, and that it covers Ψb whenever β really occurs.  (At the call
    site the missing case is harmless: [ad_pat_sub_g_ftag_sub] and the
    ForallL rule's hygiene premise force Ψb = ∅ when β is unused.) *)
(** Erasure preserves free variables. *)
Lemma uskl_to_pskl_ftv : forall R,
  ftvar_in_pskl ⌊ R ⌋ˢ [=] ftvar_in_uskl R.
Proof.
  induction R; cbn [uskl_to_pskl ftvar_in_pskl ftvar_in_uskl];
    solve [ clear; fsetdec | fsetdec ].
Qed.

(** Rigid renaming for [uskl_rho], applied to BOTH sides at once — the
    binder rows open both, so this is what turns a single fresh instance
    into a cofinite family (per the standing method rule: binder NAMES never
    obstruct anything).  [α1 ∉ dom Θ] is what keeps the ρ-images fixed: they
    are Θ-scoped, so they cannot mention α1. *)
Lemma uskl_rho_rename : forall NM Θ Δρ Ψρ R' R,
  uskl_rho NM Θ Δρ Ψρ R' R ->
  forall α1 α2,
  α1 `notin` dom Θ -> α1 `notin` Δρ ->
  uskl_rho NM Θ Δρ Ψρ (subst_bskl_in_uskl (uskl_var_f α2) α1 R')
                      (subst_bskl_in_uskl (uskl_var_f α2) α1 R).
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; intros α1 α2 HαΘ HαΔ.
  - (* refl *)
    apply urho__refl;
      [ apply subst_bskl_in_uskl_lc_uskl; [ exact H | apply lc_uskl_var_f ]
      | exact H0 ].
  - (* leaf: the replaced variable is in Δρ (so not α1), and the image is
       Θ-scoped (so α1-free) *)
    assert (Hne : α <> α1) by (intros ->; contradiction).
    assert (Hfr : α1 `notin` ftvar_in_uskl ψ'').
    { pose proof (a_wf_pskl_ftv_dom H1) as Hd.
      rewrite uskl_to_pskl_ftv in Hd. clear - Hd HαΘ; fsetdec. }
    rewrite (@subst_bskl_in_uskl_fresh_eq ψ'' (uskl_var_f α2) α1 Hfr).
    cbn [subst_bskl_in_uskl].
    match goal with |- context [if ?c then _ else _] =>
      destruct c as [Heq | _]; [ subst; contradiction | ] end.
    eapply urho__leaf; [ exact H | exact H0 | exact H1 | exact H2 ].
  - (* arrow *)
    cbn [subst_bskl_in_uskl].
    eapply urho__arrow; [ apply IHuskl_rho1 | apply IHuskl_rho2 | exact H1 ];
      assumption.
  - (* ∀ *)
    cbn [subst_bskl_in_uskl].
    apply urho__all_syn with (L := L `union` singleton α1); intros α Hα.
    assert (Hne : α1 <> α) by (apply notin_singleton_1; clear - Hα; solve_notin).
    repeat rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      solve [ apply H0; solve [ clear - Hα; solve_notin | assumption ]
            | exact Hne | apply lc_uskl_var_f ].
  - (* ∀^ε *)
    cbn [subst_bskl_in_uskl].
    apply urho__all_etag with (L := L `union` singleton α1) (ε := ε);
      intros α Hα.
    assert (Hne : α1 <> α) by (apply notin_singleton_1; clear - Hα; solve_notin).
    repeat rewrite subst_bskl_in_uskl_open_uskl_wrt_uskl_var;
      solve [ apply H0; solve [ clear - Hα; solve_notin | assumption ]
            | exact Hne | apply lc_uskl_var_f ].
  - (* ∀◇ *) cbn [subst_bskl_in_uskl]; apply urho__tophole; auto.
  - (* ∀◈ *) cbn [subst_bskl_in_uskl]; apply urho__topholeg; auto.
Qed.

Lemma uskl_rho_subst_refl : forall NM Θ Δρ R β ψb Ψb,
  lc_uskl R ->
  a_tags_sort NM Ψb ψb ->
  Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψb ⌋ˢ ->
  lc_uskl ψb ->
  exists Ψρ',
    Ψρ' [<=] Ψb /\
    (β `in` ftvar_in_uskl R -> Ψb [<=] Ψρ') /\
    uskl_rho NM Θ (add β Δρ) Ψρ' (subst_bskl_in_uskl ψb β R) R.
Proof.
  intros NM Θ Δρ R β ψb Ψb Hlc Htags Hwf Hlcb.
  induction Hlc; cbn [subst_bskl_in_uskl ftvar_in_uskl].
  - (* ⟨⟩ *)
    exists empty; repeat split;
      [ clear; fsetdec | intros Hin; clear - Hin; fsetdec
      | apply urho__refl; [ apply lc_uskl_unit | clear; fsetdec ] ].
  - (* a variable: the substituted one becomes a ρ-LEAF *)
    match goal with |- context [if ?c then _ else _] =>
      destruct c as [-> | Hne] end.
    + exists Ψb; repeat split;
        [ clear; fsetdec | intros _; clear; fsetdec
        | eapply urho__leaf;
            [ clear; fsetdec | exact Htags | exact Hwf | clear; fsetdec ] ].
    + exists empty; repeat split;
        [ clear; fsetdec
        | intros Hin; exfalso; clear - Hin Hne; fsetdec
        | apply urho__refl; [ apply lc_uskl_var_f | clear; fsetdec ] ].
  - (* arrow *)
    destruct IHHlc1 as (Ψ1 & Hs1 & Hocc1 & Hr1).
    destruct IHHlc2 as (Ψ2 & Hs2 & Hocc2 & Hr2).
    exists (Ψ1 `union` Ψ2); repeat split;
      [ clear - Hs1 Hs2; fsetdec
      | intros Hin;
        destruct (AtomSetProperties.In_dec β (ftvar_in_uskl R1)) as [Hi | Hi];
          [ pose proof (Hocc1 Hi); clear - H; fsetdec
          | assert (Hi2 : β `in` ftvar_in_uskl R2) by (clear - Hin Hi; fsetdec);
            pose proof (Hocc2 Hi2); clear - H; fsetdec ]
      | eapply urho__arrow; [ exact Hr1 | exact Hr2 | clear; fsetdec ] ].
  - (* ∀ (untagged): the IH at ONE fresh binder, renamed into the family *)
    match goal with IH : forall α, _ |- _ =>
      pick fresh α0 for (dom Θ `union` ftvar_in_uskl R `union` singleton β
                           `union` ftvar_in_uskl ψb `union` Δρ);
      destruct (IH α0) as (Ψ1 & Hs1 & Hocc1 & Hr1)
    end.
    exists Ψ1; repeat split.
    + exact Hs1.
    + (* β occurs in the ∀ iff it occurs in any opening *)
      intros Hin. apply Hocc1.
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                    (uskl_var_f α0)) as Hlo.
      clear - Hin Hlo; fsetdec.
    + apply urho__all_syn with (L := dom Θ `union` singleton α0
                                      `union` ftvar_in_uskl R
                                      `union` ftvar_in_uskl ψb
                                      `union` singleton β);
        intros α Hα.
      assert (Hα0 : α0 `notin` dom Θ) by (clear - Fr; solve_notin).
      assert (Hα0Δ : α0 `notin` add β Δρ)
        by (assert (Hd : α0 `notin` Δρ) by (clear - Fr; solve_notin);
            assert (Hb : α0 <> β)
              by (apply notin_singleton_1; clear - Fr; solve_notin);
            clear - Hd Hb; fsetdec).
      pose proof (uskl_rho_rename Hr1 (α1 := α0) α Hα0 Hα0Δ) as Hren.
      assert (Hα0ψb : α0 `notin` ftvar_in_uskl ψb)
        by (clear - Fr; solve_notin).
      assert (Hα0β : α0 <> β)
        by (apply notin_singleton_1; clear - Fr; solve_notin).
      assert (Hα0R : α0 `notin` ftvar_in_uskl R) by (clear - Fr; solve_notin).
      assert (Hβα : β <> α)
        by (apply not_eq_sym; apply notin_singleton_1;
            clear - Hα; solve_notin).
      (* push the rename PAST the instantiation (α0 avoids ψb), then read
         both sides back as openings at α *)
      rewrite (@subst_bskl_in_uskl_subst_bskl_in_uskl
                 (open_uskl_wrt_uskl R (uskl_var_f α0)) (uskl_var_f α) ψb
                 β α0
                 ltac:(cbn [ftvar_in_uskl]; clear - Hβα; fsetdec)
                 ltac:(apply not_eq_sym; exact Hα0β)) in Hren.
      rewrite (@subst_bskl_in_uskl_fresh_eq ψb (uskl_var_f α) α0 Hα0ψb)
        in Hren.
      rewrite <- (@subst_bskl_in_uskl_intro α0 R (uskl_var_f α) Hα0R)
        in Hren.
      rewrite (@subst_bskl_in_uskl_open_uskl_wrt_uskl_var R ψb β α Hβα Hlcb).
      exact Hren.
  - (* ∀^ε : the same, with the tag carried through *)
    match goal with IH : forall α, _ |- _ =>
      pick fresh α0 for (dom Θ `union` ftvar_in_uskl R `union` singleton β
                           `union` ftvar_in_uskl ψb `union` Δρ);
      destruct (IH α0) as (Ψ1 & Hs1 & Hocc1 & Hr1)
    end.
    exists Ψ1; repeat split.
    + exact Hs1.
    + (* β occurs in the ∀ iff it occurs in any opening *)
      intros Hin. apply Hocc1.
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                    (uskl_var_f α0)) as Hlo.
      clear - Hin Hlo; fsetdec.
    + apply urho__all_etag with (ε := ε) (L := dom Θ `union` singleton α0
                                      `union` ftvar_in_uskl R
                                      `union` ftvar_in_uskl ψb
                                      `union` singleton β);
        intros α Hα.
      assert (Hα0 : α0 `notin` dom Θ) by (clear - Fr; solve_notin).
      assert (Hα0Δ : α0 `notin` add β Δρ)
        by (assert (Hd : α0 `notin` Δρ) by (clear - Fr; solve_notin);
            assert (Hb : α0 <> β)
              by (apply notin_singleton_1; clear - Fr; solve_notin);
            clear - Hd Hb; fsetdec).
      pose proof (uskl_rho_rename Hr1 (α1 := α0) α Hα0 Hα0Δ) as Hren.
      assert (Hα0ψb : α0 `notin` ftvar_in_uskl ψb)
        by (clear - Fr; solve_notin).
      assert (Hα0β : α0 <> β)
        by (apply notin_singleton_1; clear - Fr; solve_notin).
      assert (Hα0R : α0 `notin` ftvar_in_uskl R) by (clear - Fr; solve_notin).
      assert (Hβα : β <> α)
        by (apply not_eq_sym; apply notin_singleton_1;
            clear - Hα; solve_notin).
      (* push the rename PAST the instantiation (α0 avoids ψb), then read
         both sides back as openings at α *)
      rewrite (@subst_bskl_in_uskl_subst_bskl_in_uskl
                 (open_uskl_wrt_uskl R (uskl_var_f α0)) (uskl_var_f α) ψb
                 β α0
                 ltac:(cbn [ftvar_in_uskl]; clear - Hβα; fsetdec)
                 ltac:(apply not_eq_sym; exact Hα0β)) in Hren.
      rewrite (@subst_bskl_in_uskl_fresh_eq ψb (uskl_var_f α) α0 Hα0ψb)
        in Hren.
      rewrite <- (@subst_bskl_in_uskl_intro α0 R (uskl_var_f α) Hα0R)
        in Hren.
      rewrite (@subst_bskl_in_uskl_open_uskl_wrt_uskl_var R ψb β α Hβα Hlcb).
      exact Hren.
  - (* ⟨⟩ hole *)
    exists empty; repeat split;
      [ clear; fsetdec | intros Hin; clear - Hin; fsetdec
      | apply urho__refl; [ apply lc_uskl_hole | clear; fsetdec ] ].
  - (* ∀◇ *)
    destruct IHHlc as (Ψ1 & Hs1 & Hocc1 & Hr1).
    exists Ψ1; repeat split;
      [ exact Hs1 | exact Hocc1 | apply urho__tophole; exact Hr1 ].
  - (* ◈ *)
    exists empty; repeat split;
      [ clear; fsetdec | intros Hin; clear - Hin; fsetdec
      | apply urho__refl; [ apply lc_uskl_holeg | clear; fsetdec ] ].
  - (* ∀◈ *)
    destruct IHHlc as (Ψ1 & Hs1 & Hocc1 & Hr1).
    exists Ψ1; repeat split;
      [ exact Hs1 | exact Hocc1 | apply urho__topholeg; exact Hr1 ].
Qed.

(** [uskl_rho_subst_refl] is the [ρ = id] component of the ρ-extension the
    ForallL case needs.  The general form recurses on the [uskl_rho]
    derivation and calls this at its [urho__refl] nodes, maps [urho__leaf]
    to itself (the images are Θ-scoped, hence β-free) and the congruences to
    themselves — with the same tag BOUND, since a binder the guess does not
    use contributes nothing. *)

(** The Arrow case's TAG SPLIT.  The guess's tags are partitioned by the
    arrow ([d_tags_skl__arrow] is a DISJOINT union), the already-solved ones
    split with the precision, and each branch's newly-solved set is then
    just the intersection — no choice is involved. *)
Lemma arrow_tag_split : forall Ψt Ψt1 Ψt2 Ψi Ψi1 Ψi2 Ψa,
  Ψt [=] Ψt1 `union` Ψt2 ->
  Ψt1 ∩ Ψt2 [=] empty ->
  Ψi [=] Ψi1 `union` Ψi2 ->
  Ψi1 [<=] Ψt1 -> Ψi2 [<=] Ψt2 ->
  Ψi `union` Ψa [=] Ψt ->
  Ψi1 `union` (Ψa ∩ Ψt1) [=] Ψt1 /\
  Ψi2 `union` (Ψa ∩ Ψt2) [=] Ψt2.
Proof.
  intros Ψt Ψt1 Ψt2 Ψi Ψi1 Ψi2 Ψa Ht Hd Hi Hs1 Hs2 Heq.
  split; clear - Ht Hd Hi Hs1 Hs2 Heq; fsetdec.
Qed.

(** ρ preserves decoratedness: images are tags-sorted and the congruences
    keep the shape. *)
(* [uskl_rho_is_tskl] MOVED to prop_look_complete.v (P6-Cs needs it under
   the ρ-generalization, and this file is downstream of P6-Cs). *)

(** THE ρ-EXTENSION.  Sub-ForallL's [ρ_b = ρ ∘ [ψ_b/β]] in full: recurse on
    the ρ-derivation, use the [ρ = id] lemma at its reflexive nodes, keep
    the leaves (their images are Θ-scoped, hence β-free) and the
    congruences.  The binder rows go through the same way as there — one
    fresh instance, renamed into the family. *)
Lemma uskl_rho_subst : forall NM Θ Δρ Ψρ R' R,
  uskl_rho NM Θ Δρ Ψρ R' R ->
  forall β ψb Ψb,
  a_tags_sort NM Ψb ψb ->
  Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψb ⌋ˢ ->
  lc_uskl ψb ->
  β `notin` dom Θ ->
  β `notin` Δρ ->
  exists Ψρ',
    Ψρ' [<=] Ψρ `union` Ψb /\
    Ψρ [<=] Ψρ' /\
    (β `in` ftvar_in_uskl R -> Ψb [<=] Ψρ') /\
    uskl_rho NM Θ (add β Δρ) Ψρ' (subst_bskl_in_uskl ψb β R') R.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H;
    intros β ψb Ψb Htags Hwfb Hlcb HβΘ HβΔ.
  - (* refl : the ρ = id lemma *)
    destruct (@uskl_rho_subst_refl NM Θ Δρ R β ψb Ψb H Htags Hwfb Hlcb)
      as (Ψ1 & Hs1 & Hocc1 & Hr1).
    exists Ψ1; repeat split;
      [ clear - Hs1; fsetdec | clear - H0; fsetdec | exact Hocc1 | exact Hr1 ].
  - (* leaf : the image is Θ-scoped, so β does not occur in it *)
    assert (Hfr : β `notin` ftvar_in_uskl ψ'').
    { pose proof (a_wf_pskl_ftv_dom H1) as Hd.
      rewrite uskl_to_pskl_ftv in Hd. clear - Hd HβΘ; fsetdec. }
    rewrite (@subst_bskl_in_uskl_fresh_eq ψ'' ψb β Hfr).
    exists Ψρ; repeat split;
      [ clear; fsetdec | clear; fsetdec
      | (* β is not a ρ-replaced variable, so it is not THIS one *)
        intros Hin; exfalso; cbn [ftvar_in_uskl] in Hin;
        assert (Heq : β = α) by (clear - Hin; fsetdec); subst;
        contradiction
      | eapply urho__leaf;
          [ clear - H; fsetdec | exact H0 | exact H1 | exact H2 ] ].
  - (* arrow *)
    destruct (IHuskl_rho1 β ψb Ψb Htags Hwfb Hlcb HβΘ HβΔ)
      as (Ψa1 & Hs1 & Hm1 & Hocc1 & Hr1).
    destruct (IHuskl_rho2 β ψb Ψb Htags Hwfb Hlcb HβΘ HβΔ)
      as (Ψa2 & Hs2 & Hm2 & Hocc2 & Hr2).
    exists (Ψa1 `union` Ψa2); repeat split.
    + clear - Hs1 Hs2 H1; fsetdec.
    + clear - Hm1 Hm2 H1; fsetdec.
    + intros Hin; cbn [ftvar_in_uskl] in Hin.
      destruct (AtomSetProperties.In_dec β (ftvar_in_uskl R1)) as [Hi | Hi];
        [ pose proof (Hocc1 Hi); clear - H2; fsetdec
        | assert (Hi2 : β `in` ftvar_in_uskl R2) by (clear - Hin Hi; fsetdec);
          pose proof (Hocc2 Hi2); clear - H2; fsetdec ].
    + cbn [subst_bskl_in_uskl].
      eapply urho__arrow; [ exact Hr1 | exact Hr2 | clear; fsetdec ].
  - (* ∀ : one fresh instance, renamed into the family *)
    pick fresh α0 for (L `union` dom Θ `union` Δρ `union` singleton β
                         `union` ftvar_in_uskl R `union` ftvar_in_uskl R'
                         `union` ftvar_in_uskl ψb).
    destruct (H0 α0 ltac:(clear - Fr; solve_notin) β ψb Ψb
                Htags Hwfb Hlcb HβΘ HβΔ) as (Ψ1 & Hs1 & Hm1 & Hocc1 & Hr1).
    exists Ψ1; repeat split.
    + exact Hs1.
    + exact Hm1.
    + intros Hin. apply Hocc1.
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                    (uskl_var_f α0)) as Hlo.
      cbn [ftvar_in_uskl] in Hin. clear - Hin Hlo; fsetdec.
    + cbn [subst_bskl_in_uskl].
      apply urho__all_syn with (L := L `union` dom Θ `union` Δρ
                                       `union` singleton α0
                                       `union` singleton β
                                       `union` ftvar_in_uskl R
                                       `union` ftvar_in_uskl R'
                                       `union` ftvar_in_uskl ψb);
        intros α Hα.
      assert (Hα0Θ : α0 `notin` dom Θ) by (clear - Fr; solve_notin).
      assert (Hα0Δ : α0 `notin` add β Δρ)
        by (assert (Hd : α0 `notin` Δρ) by (clear - Fr; solve_notin);
            assert (Hb : α0 <> β)
              by (apply notin_singleton_1; clear - Fr; solve_notin);
            clear - Hd Hb; fsetdec).
      pose proof (uskl_rho_rename Hr1 (α1 := α0) α Hα0Θ Hα0Δ) as Hren.
      assert (Hα0ψb : α0 `notin` ftvar_in_uskl ψb)
        by (clear - Fr; solve_notin).
      assert (Hα0β : α0 <> β)
        by (apply notin_singleton_1; clear - Fr; solve_notin).
      assert (Hβα : β <> α)
        by (apply not_eq_sym; apply notin_singleton_1;
            clear - Hα; solve_notin).
      rewrite (@subst_bskl_in_uskl_subst_bskl_in_uskl
                 (open_uskl_wrt_uskl R' (uskl_var_f α0)) (uskl_var_f α) ψb
                 β α0
                 ltac:(cbn [ftvar_in_uskl]; clear - Hβα; fsetdec)
                 ltac:(apply not_eq_sym; exact Hα0β)) in Hren.
      rewrite (@subst_bskl_in_uskl_fresh_eq ψb (uskl_var_f α) α0 Hα0ψb)
        in Hren.
      rewrite <- (@subst_bskl_in_uskl_intro α0 R' (uskl_var_f α)
                    ltac:(clear - Fr; solve_notin)) in Hren.
      rewrite <- (@subst_bskl_in_uskl_intro α0 R (uskl_var_f α)
                    ltac:(clear - Fr; solve_notin)) in Hren.
      rewrite (@subst_bskl_in_uskl_open_uskl_wrt_uskl_var R' ψb β α Hβα Hlcb).
      exact Hren.
  - (* ∀^ε : the same, with the tag carried through *)
    pick fresh α0 for (L `union` dom Θ `union` Δρ `union` singleton β
                         `union` ftvar_in_uskl R `union` ftvar_in_uskl R'
                         `union` ftvar_in_uskl ψb).
    destruct (H0 α0 ltac:(clear - Fr; solve_notin) β ψb Ψb
                Htags Hwfb Hlcb HβΘ HβΔ) as (Ψ1 & Hs1 & Hm1 & Hocc1 & Hr1).
    exists Ψ1; repeat split.
    + exact Hs1.
    + exact Hm1.
    + intros Hin. apply Hocc1.
      pose proof (ftvar_in_uskl_open_uskl_wrt_uskl_lower R
                    (uskl_var_f α0)) as Hlo.
      cbn [ftvar_in_uskl] in Hin. clear - Hin Hlo; fsetdec.
    + cbn [subst_bskl_in_uskl].
      apply urho__all_etag with (ε := ε)
        (L := L `union` dom Θ `union` Δρ `union` singleton α0
                `union` singleton β `union` ftvar_in_uskl R
                `union` ftvar_in_uskl R' `union` ftvar_in_uskl ψb);
        intros α Hα.
      assert (Hα0Θ : α0 `notin` dom Θ) by (clear - Fr; solve_notin).
      assert (Hα0Δ : α0 `notin` add β Δρ)
        by (assert (Hd : α0 `notin` Δρ) by (clear - Fr; solve_notin);
            assert (Hb : α0 <> β)
              by (apply notin_singleton_1; clear - Fr; solve_notin);
            clear - Hd Hb; fsetdec).
      pose proof (uskl_rho_rename Hr1 (α1 := α0) α Hα0Θ Hα0Δ) as Hren.
      assert (Hα0ψb : α0 `notin` ftvar_in_uskl ψb)
        by (clear - Fr; solve_notin).
      assert (Hα0β : α0 <> β)
        by (apply notin_singleton_1; clear - Fr; solve_notin).
      assert (Hβα : β <> α)
        by (apply not_eq_sym; apply notin_singleton_1;
            clear - Hα; solve_notin).
      rewrite (@subst_bskl_in_uskl_subst_bskl_in_uskl
                 (open_uskl_wrt_uskl R' (uskl_var_f α0)) (uskl_var_f α) ψb
                 β α0
                 ltac:(cbn [ftvar_in_uskl]; clear - Hβα; fsetdec)
                 ltac:(apply not_eq_sym; exact Hα0β)) in Hren.
      rewrite (@subst_bskl_in_uskl_fresh_eq ψb (uskl_var_f α) α0 Hα0ψb)
        in Hren.
      rewrite <- (@subst_bskl_in_uskl_intro α0 R' (uskl_var_f α)
                    ltac:(clear - Fr; solve_notin)) in Hren.
      rewrite <- (@subst_bskl_in_uskl_intro α0 R (uskl_var_f α)
                    ltac:(clear - Fr; solve_notin)) in Hren.
      rewrite (@subst_bskl_in_uskl_open_uskl_wrt_uskl_var R' ψb β α Hβα Hlcb).
      exact Hren.
  - (* ∀◇ *)
    destruct (IHuskl_rho β ψb Ψb Htags Hwfb Hlcb HβΘ HβΔ)
      as (Ψ1 & Hs1 & Hm1 & Hocc1 & Hr1).
    exists Ψ1; repeat split;
      [ exact Hs1 | exact Hm1 | exact Hocc1
      | cbn [subst_bskl_in_uskl]; apply urho__tophole; exact Hr1 ].
  - (* ∀◈ *)
    destruct (IHuskl_rho β ψb Ψb Htags Hwfb Hlcb HβΘ HβΔ)
      as (Ψ1 & Hs1 & Hm1 & Hocc1 & Hr1).
    exists Ψ1; repeat split;
      [ exact Hs1 | exact Hm1 | exact Hocc1
      | cbn [subst_bskl_in_uskl]; apply urho__topholeg; exact Hr1 ].
Qed.

(* [fa_step] / [fa_walk] / [flex_apart_walk] and its three lemmas MOVED to
   prop_look_complete.v, next to [flex_apart] itself: P6-Cs needs them too
   under the ρ-generalization, and this file is DOWNSTREAM of P6-Cs. *)

(* ===================================================================== *)
(*  The ρ-LEAF CLOSER — used by every case of the main induction           *)
(* ===================================================================== *)

(** When the guess at this position is a ρ-REPLACED RIGID VARIABLE, the
    freshness pack forces [Pi] to be that very variable, SolS-Var solves
    with [Pa := Pi], and the conclusion's precision is the var rule.  This
    is the subtyping twin of [p6cv_close_leaf] (prop_look_complete.v:1134):
    same argument, [a_solve_sub__var] in place of [a_solve_eq__var].

    It serves BOTH leaf sources: the [rho_leaf] disjunct of the [uskl_rho]
    inversions, and the [fsh_rho_var] branch of [flex_shield_flex_leaf]. *)
Lemma a_solve_sub_complete_rho_var :
  forall NM m Θ0 Θ Θw κ Δ Δρ Ψ' Ψi Ψa α Pi P0,
  a_wf_aenv Θ ->
  a_tags_sort NM Ψ' (uskl_var_f α) ->
  Ψi `union` Ψa [<=] Ψ' ->
  rho_fresh Δρ Θ κ ->
  Δρ [<=] Δ ->
  α `in` Δρ ->
  (forall α0, α0 `in` Δρ ->
     α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  Θ0 ⨟ empty ⊢ₚₛᵃ Pi ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_var_f α) ->
  (* SolS-Var GENERATES NOTHING, so the package is the trivial one: this is
     [solve_sub_ext_nil] with [Ξ := ·] and [κ' := ·], and [Θw] and [L] are
     therefore unconstrained. *)
  forall L,
  solve_sub_ext Θ0 Θw m Pi P0 L
    (fun κ' Pa =>
       Θ ⨟ Δ ⊢ (msubst_pskl (κ' ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] (uskl_var_f α)).
Proof.
  intros NM m Θ0 Θ Θw κ Δ Δρ Ψ' Ψi Ψa α Pi P0
    HwfΘ Htags Hsub Hfresh Hdelta HαΔρ Hapart HwfPi Hpre L.
  pose proof (Hfresh α HαΔρ) as (HXb & Hκav & Hdef).
  assert (HαΔ : α `in` Δ) by (clear - Hdelta HαΔρ; fsetdec).
  pose proof (Hapart α HαΔρ) as Hsh.
  destruct (ad_ppre_delta_var_inv Hpre eq_refl HwfΘ HαΔ HXb Hdef Hsh)
    as (Heqm & HΨie).
  assert (HeqPi : Pi = pskl_var_f α)
    by (eapply msubst_pskl_var_inv; eassumption).
  assert (HΨ'e : Ψ' [=] empty)
    by (exact (d_tags_skl_var_inv (a_tags_sort_d_tags Htags))).
  assert (HΨae : Ψa [=] empty) by (clear - Hsub HΨ'e; fsetdec).
  eapply solve_sub_ext_nil with (Pa := Pi);
    [ rewrite HeqPi; apply a_solve_sub__var
    | exact HwfPi
    | cbn [app]; rewrite Heqm;
      apply ad_ppre__var; [ clear - HΨie HΨae; fsetdec | left; exact HαΔ ] ].
Qed.

(* ===================================================================== *)
(*  Sub-ForallL kit                                                        *)
(* ===================================================================== *)

(** ρ only ever REPLACES a variable by a decorated skeleton, so the source's
    tags all survive into the image.  (The converse bound, with the
    replacement tags added, is [uskl_rho_ftag_sub].) *)
Lemma uskl_rho_ftag_target_sub : forall NM Θ Δρ Ψρ R' R,
  uskl_rho NM Θ Δρ Ψρ R' R ->
  ftag_in_uskl R [<=] ftag_in_uskl R'.
Proof.
  intros NM Θ Δρ Ψρ R' R H; induction H; cbn [ftag_in_uskl];
    try solve [ clear; fsetdec | clear - IHuskl_rho; fsetdec
              | clear - IHuskl_rho1 IHuskl_rho2; fsetdec ].
  - (* ∀ (untagged) : opening with a variable adds no tag *)
    pick fresh α for L.
    pose proof (H0 α ltac:(clear - Fr; solve_notin)) as Hα.
    rewrite (ftag_in_uskl_open_var R α) in Hα.
    rewrite (ftag_in_uskl_open_var R' α) in Hα.
    exact Hα.
  - (* ∀^ε *)
    pick fresh α for L.
    pose proof (H0 α ltac:(clear - Fr; solve_notin)) as Hα.
    rewrite (ftag_in_uskl_open_var R α) in Hα.
    rewrite (ftag_in_uskl_open_var R' α) in Hα.
    clear - Hα; fsetdec.
Qed.

(** The mirror of [uskl_rho_ftv_target_bound]: ρ's images are Θ-scoped, so
    the IMAGE's free variables are the source's plus the context's.  Sub-
    ForallL needs it to know that a source binder unused under ρ is unused
    in the image too. *)
(* [uskl_rho_ftv_subject_bound] MOVED to prop_look_complete.v — P6-Cs needs
   it under the ρ-generalization, and this file is downstream of P6-Cs. *)

(** A ∀◇ body is well-formed at the EMPTY Δ ([a_wf_pskl__tophole]), so no
    SHIELDED variable of a well-formed skeleton can be a locally bound one:
    they are all in [dom Θ].  This is the discipline DESIGN §7 names when it
    says the freshly opened binder "stays out of ∀◇ bodies" — it is what
    lets Sub-ForallL add its binder to Δρ. *)
Lemma a_wf_pskl_shielded_dom : forall Θ Δ P,
  Θ ⨟ Δ ⊢ₚₛᵃ P ->
  pskl_shielded_ftv P [<=] dom Θ.
Proof.
  intros Θ Δ P H; induction H; cbn [pskl_shielded_ftv];
    try solve [ clear; fsetdec | clear - IHa_wf_pskl1 IHa_wf_pskl2; fsetdec ].
  - (* ∀ : the shielded variables of a body are already the binder's *)
    pick fresh α for (L `union` pskl_shielded_ftv P).
    pose proof (H0 α ltac:(clear - Fr; solve_notin)) as Hα.
    pose proof (pskl_shielded_ftv_open_lower P (pskl_var_f α)) as Hlo.
    clear - Hα Hlo; fsetdec.
  - (* ∀◇ : the body is well-formed at Δ = ∅ *)
    pose proof (a_wf_pskl_ftv_dom H0) as Hd. clear - Hd; fsetdec.
Qed.

(** The converse of [a_wf_pskl_delta_to_tvar_mid], for PRECISION: a rigid
    binder that ALREADY sits in Δ may be dropped from the aenv.  Sub-ForallL
    needs exactly this — the recursive call runs at [Θ,β] because
    [rho_fresh] insists every ρ-replaced variable be a rigid of the context,
    while the precision the case must REBUILD lives at Θ with β only in Δ.
    (The [strip] version in prop_look_complete_cstr.v instead demands β free
    in NEITHER side; here β is free in both, and Δ-membership is what keeps
    the var rule alive.) *)
Lemma ad_partial_precise_tvar_to_delta_mid : forall Θf Δ Ψ P ψ,
  Θf ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  forall β Θ1 Θ2, Θf = Θ1 ++ (β ~ abind_tvar) ++ Θ2 ->
  β `notin` dom Θ1 -> β `notin` dom Θ2 ->
  β `in` Δ ->
  (Θ1 ++ Θ2) ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ.
Proof.
  intros Θf Δ Ψ P ψ H; induction H;
    intros β Θ1 Θ2 Heq Hd1 Hd2 HβΔ; subst.
  - apply ad_ppre__unit; assumption.
  - (* var : if the variable IS β, Δ-membership takes over *)
    match goal with Hor : _ \/ a_binds_tvar ?α0 _ |- _ =>
      destruct (α0 == β) as [-> | Hne];
        [ apply ad_ppre__var; [ assumption | left; exact HβΔ ] | ];
      apply ad_ppre__var; [ assumption | ];
      destruct Hor as [HΔ | Hb]; [ left; exact HΔ | right ];
      eapply a_binds_tvar_strip_mid;
        [ exact Hb | intro Hc; congruence | intro Hc; congruence
        | intros τ0 Hc; congruence ]
    end.
  - eapply ad_ppre__arrow;
      [ eapply IHad_partial_precise1 | eapply IHad_partial_precise2 | ];
      solve [ reflexivity | assumption ].
  - eapply ad_ppre__forall with (L := L `union` singleton β); [ | eassumption ].
    intros α0 Hα0.
    eapply H0;
      [ clear - Hα0; fsetdec | reflexivity | exact Hd1 | exact Hd2
      | clear - HβΔ; fsetdec ].
  - apply ad_ppre__hole; assumption.
  - apply ad_ppre__tophole_remove;
      eapply IHad_partial_precise; solve [ reflexivity | assumption ].
  - eapply ad_ppre__tophole_fill
      with (L := L `union` singleton β `union` dom Θ1 `union` dom Θ2).
    intros α0 Hα0.
    eapply (H0 α0 ltac:(clear - Hα0; fsetdec) β ((α0 ~ abind_tvar) ++ Θ1) Θ2);
      [ reflexivity
      | simpl; clear - Hα0 Hd1; solve_notin
      | exact Hd2 | exact HβΔ ].
  - apply ad_ppre__tophole_keep;
      eapply IHad_partial_precise; solve [ reflexivity | assumption ].
  - (* flex_l / flex_r : β is bound as a RIGID, so a defined variable of the
       context is never β (the context has no second β entry) *)
    match goal with Hb : binds ?α0 (abind_flex_mono_def ?τ0) _ |- _ =>
      assert (Hαβ : α0 <> β) by
        (intro Heqα; subst α0;
         destruct (binds_app_1 _ _ _ _ _ Hb) as [Hb1 | Hb2];
           [ apply Hd1; eapply binds_In; exact Hb1
           | destruct (binds_cons_1 _ _ _ _ _ _ Hb2) as [[_ Habs] | Hb3];
               [ discriminate Habs | apply Hd2; eapply binds_In; exact Hb3 ] ])
    end.
    eapply ad_ppre__flex_l;
      [ eapply binds_strengthen_mid;
          [ eassumption | simpl; clear - Hαβ; fsetdec ]
      | eapply IHad_partial_precise; solve [ reflexivity | assumption ] ].
  - match goal with Hb : binds ?α0 (abind_flex_mono_def ?τ0) _ |- _ =>
      assert (Hαβ : α0 <> β) by
        (intro Heqα; subst α0;
         destruct (binds_app_1 _ _ _ _ _ Hb) as [Hb1 | Hb2];
           [ apply Hd1; eapply binds_In; exact Hb1
           | destruct (binds_cons_1 _ _ _ _ _ _ Hb2) as [[_ Habs] | Hb3];
               [ discriminate Habs | apply Hd2; eapply binds_In; exact Hb3 ] ])
    end.
    eapply ad_ppre__flex_r;
      [ eapply binds_strengthen_mid;
          [ eassumption | simpl; clear - Hαβ; fsetdec ]
      | eapply IHad_partial_precise; solve [ reflexivity | assumption ] ].
Qed.

(** The ∀^ε analogue of [ad_ppre_guarded_topholeg_absurd]: no GUARDED input
    skeleton is partially precise to a tagged quantifier.  The variable row
    is the only live one, and there the κ-image is a MONOTYPE, whose target
    must therefore be tag-free — while a tagged ∀ carries ε. *)
Lemma ad_ppre_guarded_all_etag_absurd : forall Θ0 Θ κ Δ Ψ Ψd P ε ψ,
  a_wf_aenv Θ ->
  κ ∷ Θ0 ⊑ Θ ->
  guarded_pskl P ->
  d_tags_skl Ψd (uskl_all_etag ε ψ) ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ P) ⊑ᵖ[ Ψ ] (uskl_all_etag ε ψ) ->
  False.
Proof.
  intros Θ0 Θ κ Δ Ψ Ψd P ε ψ HwfΘ Hκ Hg Hd Hpre.
  destruct Hg as [ | α | P1 P2 Hlc1 Hlc2 ]; cbn [msubst_pskl] in Hpre.
  - inversion Hpre.
  - assert (HΨde : Ψd [=] empty)
      by (eapply ad_ppre_mono_subject_target_tags_empty;
            [ exact HwfΘ | exact Hpre | reflexivity
            | eapply a_inc_lookup_mono; exact Hκ | exact Hd ]).
    destruct (d_tags_skl_all_etag_inv Hd) as (Ld & Ψ0 & _ & _ & Heq).
    assert (Hin : ε `in` empty) by (clear - HΨde Heq; fsetdec).
    clear - Hin; fsetdec.
  - inversion Hpre.
Qed.

(** The Arrow case's Pi GRID.  Everything about the two branches is packed
    into the [KEY] hypothesis (the left premise's P6-Cv call and the right
    one's induction hypothesis), so this is purely the case analysis on the
    input skeleton: arrow / □ / ∀◇ / a variable, with unit and ∀ refuted by
    the precision against an arrow guess.  The ∀◇ row recurses STRUCTURALLY
    on Pi — no measure needed, since well-formedness makes the ghost's body
    guarded. *)
(** ⭐ THE KEY hypothesis now hands back the ARROW ROW's whole merged package
    (2026-08-04, the SolE-FlexR repair): the two halves THREAD — SS-Arrow and
    SS-GhostLF run their second premise at [Ξ1 ++ Θ0] — so the caller cannot
    give the two solves independently, and the block/extension it returns is
    already the merged [Ξ2 ++ Ξ1] / [κ2 ++ κ1].  Both outputs are well-formed
    at the MERGED block, which is what [a_wf_pskl__arrow] then lifts. *)
Lemma arrow_grid : forall NM M Θ0 Θ Θw κ Δ Δρ Ψt Ψi Ψa ψ1 ψ2 Pi P01 P02,
  a_wf_aenv Θ ->
  κ ∷ Θ0 ⊑ Θ ->
  a_tags_sort NM Ψt (uskl_arrow ψ1 ψ2) ->
  Ψi `union` Ψa [=] Ψt ->
  (* the two target components are well-formed — needed only to know the
     target is locally closed, which the guardedness of a ∀◇ output rests on *)
  Θ0 ⨟ empty ⊢ₚₛᵃ P01 -> Θ0 ⨟ empty ⊢ₚₛᵃ P02 ->
  (forall Pi1 Pi2 Ψi1 Ψi2 L,
     Θ0 ⨟ empty ⊢ₚₛᵃ Pi1 -> Θ0 ⨟ empty ⊢ₚₛᵃ Pi2 ->
     (forall α, α `in` Δρ ->
        α `notin` pskl_shielded_ftv (msubst_pskl κ Pi1)) ->
     (forall α, α `in` Δρ ->
        α `notin` pskl_shielded_ftv (msubst_pskl κ Pi2)) ->
     Ψi [=] Ψi1 `union` Ψi2 ->
     Θ ⨟ Δ ⊢ (msubst_pskl κ Pi1) ⊑ᵖ[ Ψi1 ] ψ1 ->
     Θ ⨟ Δ ⊢ (msubst_pskl κ Pi2) ⊑ᵖ[ Ψi2 ] ψ2 ->
     exists Ξ1 Ξ2 Pa1 Pa2 κ1 κ2,
       Θ0 ⊢ₑ Pi1 ∼ P01 ⤳ Ξ1 ⨾ Pa1 /\
       (Ξ1 ++ Θ0) ⊢ₛ Pi2 ≼[ M ] P02 ⤳ Ξ2 ⨾ Pa2 /\
       all_flex_mono (Ξ2 ++ Ξ1) /\
       uniq (Ξ2 ++ Ξ1) /\
       keys (κ2 ++ κ1) = keys (Ξ2 ++ Ξ1) /\
       (forall α, α `in` dom (Ξ2 ++ Ξ1) -> α `notin` L) /\
       Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) (κ2 ++ κ1) /\
       ((Ξ2 ++ Ξ1) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pa1 /\
       ((Ξ2 ++ Ξ1) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pa2 /\
       Θ ⨟ Δ ⊢ (msubst_pskl ((κ2 ++ κ1) ++ κ) (pskl_arrow Pa1 Pa2))
         ⊑ᵖ[ Ψi `union` Ψa ] (uskl_arrow ψ1 ψ2)) ->
  Θ0 ⨟ empty ⊢ₚₛᵃ Pi ->
  (forall α, α `in` Δρ -> α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_arrow ψ1 ψ2) ->
  forall L,
  solve_sub_ext Θ0 Θw (mode_fn M) Pi (pskl_arrow P01 P02) L
    (fun κ' Pa =>
       Θ ⨟ Δ ⊢ (msubst_pskl (κ' ++ κ) Pa)
         ⊑ᵖ[ Ψi `union` Ψa ] (uskl_arrow ψ1 ψ2)).
Proof.
  intros NM M Θ0 Θ Θw κ Δ Δρ Ψt Ψi Ψa ψ1 ψ2 Pi P01 P02
         HwfΘ Hκ Htags Htageq HwfP01 HwfP02 KEY.
  revert Ψi Ψa Htageq KEY.
  induction Pi as [ | nPi | β | Pi1 IH1 Pi2 IH2 | Pi0 IH0 | | Pi0 IH0 ];
    intros Ψi Ψa Htageq KEY HwfPi Hapart Hpre L;
    cbn [msubst_pskl] in Hpre.
  - (* ⟨⟩ : no rule targets an arrow from unit *) inversion Hpre.
  - (* a bound variable is not well-formed *) inversion HwfPi.
  - (* a variable : SolS-Var keeps it, and a MONOTYPE κ-image forces the
       guess to be tag-free, so there is nothing left to solve — and nothing
       generated, so the package is [solve_sub_ext_nil]'s *)
    assert (Hml : mono_ptyp (msubst_lookup κ β))
      by (eapply a_inc_lookup_mono; exact Hκ).
    assert (HΨte : Ψt [=] empty)
      by (eapply ad_ppre_mono_subject_target_tags_empty;
            [ exact HwfΘ | exact Hpre | reflexivity | exact Hml
            | exact (a_tags_sort_d_tags Htags) ]).
    eapply solve_sub_ext_nil with (Pa := pskl_var_f β);
      [ apply a_solve_sub__var
      | exact HwfPi
      | cbn [app msubst_pskl];
        eapply ad_partial_precise_psi_cong;
          [ exact Hpre | clear - Htageq HΨte; fsetdec ] ].
  - (* an arrow : both components recurse through KEY, which already merged
       the two blocks (SS-Arrow threads) *)
    inversion Hpre; subst.
    match goal with
      Hp1 : _ ⨟ _ ⊢ msubst_pskl κ Pi1 ⊑ᵖ[ ?Ψa1 ] ψ1,
      Hp2 : _ ⨟ _ ⊢ msubst_pskl κ Pi2 ⊑ᵖ[ ?Ψa2 ] ψ2,
      Hun : Ψi [=] _ |- _ =>
      destruct (KEY Pi1 Pi2 Ψa1 Ψa2 L
                  ltac:(inversion HwfPi; assumption)
                  ltac:(inversion HwfPi; assumption)
                  ltac:(intros α0 Hα0; pose proof (Hapart α0 Hα0) as Hs;
                        cbn [msubst_pskl pskl_shielded_ftv] in Hs;
                        clear - Hs; fsetdec)
                  ltac:(intros α0 Hα0; pose proof (Hapart α0 Hα0) as Hs;
                        cbn [msubst_pskl pskl_shielded_ftv] in Hs;
                        clear - Hs; fsetdec)
                  Hun Hp1 Hp2)
        as (Ξ1 & Ξ2 & Pa1 & Pa2 & κ1 & κ2
            & Hs1 & Hs2 & Hfm & Hu & Hk & Hfr & HF & Hw1 & Hw2 & Hp)
    end.
    exists (Ξ2 ++ Ξ1), (pskl_arrow Pa1 Pa2), (κ2 ++ κ1).
    repeat (split; [ solve [ apply a_solve_sub__arrow; [ exact Hs1 | exact Hs2 ]
                           | exact Hfm | exact Hu | exact Hk | exact Hfr
                           | exact HF
                           | apply a_wf_pskl__arrow; [ exact Hw1 | exact Hw2 ] ]
                   | ]).
    exact Hp.
  - (* ∀ : no rule targets an arrow from a quantifier *) inversion Hpre.
  - (* □ : SolS-GhostLF, with both branches run at input □ *)
    inversion Hpre; subst.
    match goal with Hd : Δ ∩ ftvar_in_uskl (uskl_arrow ψ1 ψ2) [=] empty,
                    He : Ψi [=] empty |- _ =>
      destruct (KEY pskl_hole pskl_hole empty empty L
                  (a_wf_pskl__hole Θ0 empty) (a_wf_pskl__hole Θ0 empty)
                  ltac:(intros α0 Hα0; cbn; clear; fsetdec)
                  ltac:(intros α0 Hα0; cbn; clear; fsetdec)
                  ltac:(clear - He; fsetdec)
                  ltac:(cbn [msubst_pskl]; apply ad_ppre__hole;
                        [ clear; fsetdec
                        | cbn [ftvar_in_uskl] in Hd; clear - Hd; fsetdec ])
                  ltac:(cbn [msubst_pskl]; apply ad_ppre__hole;
                        [ clear; fsetdec
                        | cbn [ftvar_in_uskl] in Hd; clear - Hd; fsetdec ]))
        as (Ξ1 & Ξ2 & Pa1 & Pa2 & κ1 & κ2
            & Hs1 & Hs2 & Hfm & Hu & Hk & Hfr & HF & Hw1 & Hw2 & Hp)
    end.
    exists (Ξ2 ++ Ξ1), (pskl_tophole (pskl_arrow Pa1 Pa2)), (κ2 ++ κ1).
    repeat (split;
      [ solve [ apply a_solve_sub__ghost_l_fn; [ exact Hs1 | exact Hs2 ]
              | exact Hfm | exact Hu | exact Hk | exact Hfr | exact HF
              | apply a_wf_pskl__tophole;
                  [ apply guarded_pskl__arrow;
                      [ eapply a_wf_pskl_lc; exact Hw1
                      | eapply a_wf_pskl_lc; exact Hw2 ]
                  | apply a_wf_pskl__arrow; [ exact Hw1 | exact Hw2 ] ] ]
      | ]).
    cbn [msubst_pskl] in Hp |- *.
    apply ad_ppre__tophole_remove; exact Hp.
  - (* ∀◇Pi0 : strip the ghost (the FILL and KEEP rows need a ∀^ε / ∀◈
       guess), recurse, and wrap the output — a PASS-THROUGH row, so the
       block and the extension come back unchanged *)
    inversion Hpre; subst.
    match goal with Hbody : _ ⨟ _ ⊢ msubst_pskl κ Pi0 ⊑ᵖ[ Ψi ] _ |- _ =>
      destruct (IH0 Ψi Ψa Htageq KEY
                  ltac:(eapply a_wf_pskl_tophole_inv; exact HwfPi)
                  ltac:(intros α0 Hα0; pose proof (Hapart α0 Hα0) as Hs;
                        cbn [msubst_pskl pskl_shielded_ftv] in Hs;
                        pose proof (pskl_shielded_ftv_sub_ftv
                                      (msubst_pskl κ Pi0)) as Hle;
                        clear - Hs Hle; fsetdec)
                  Hbody L)
        as (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & Hw & Hp)
    end.
    exists Ξ, (pskl_tophole Pa), κ'.
    repeat (split;
      [ solve [ apply a_solve_sub__univ_ghost_l; exact Hs
              | exact Hfm | exact Hu | exact Hk | exact Hfr | exact HF
              | apply a_wf_pskl__tophole;
                  [ eapply (proj1 a_solve_sub_eq_guarded);
                      [ exact Hs
                      | eapply a_wf_pskl_lc;
                        eapply a_wf_pskl_tophole_inv; exact HwfPi
                      | apply lc_pskl_arrow;
                          [ eapply a_wf_pskl_lc; exact HwfP01
                          | eapply a_wf_pskl_lc; exact HwfP02 ]
                      | inversion HwfPi; assumption ]
                  | exact Hw ] ]
      | ]).
    cbn [msubst_pskl]. apply ad_ppre__tophole_remove; exact Hp.
Qed.

(* ===================================================================== *)
(*  P6-Sv — THE REPAIRED STATEMENT                                        *)
(*  [lemma:complete-constraint-collection-solving-var]                    *)
(*  (subtyping-proofs.tex:1696)                                           *)
(* ===================================================================== *)

(** Premises are the paper's, threaded exactly as in the CLOSED consistency
    twin [a_solve_eq_complete_var] (prop_look_complete_var.v:3070) —
    ρ/[uskl_rho], the tag bookkeeping, the freshness pack, [flex_apart] —
    with three differences:

    1. the mode [M] and the paper's [skmod{N}{P0}{M}], in the two-implication
       form used by [a_sub_sound_thm] (prop_decorate_key.v:3331);
    2. the subtyping premise [ad_pat_sub_g] (the tag-hygienic fuel mirror)
       in place of consistency — the fuel rides inertly here, since ForallL's
       premise is a structural sub-derivation of [ad_pat_sub_g]; the fuel is
       what P7b's measure consumes;
    3. **[flex_shield] — the repair.**  Without it the statement is FALSE
       (cex_p6sv_forall_flex.v); [flex_shield_excludes_cex] above is the
       regression test that this premise rules the counterexample out.

    Also carried, as in P6-Cs: well-formedness of the consistency SUBJECT
    (⌊ψsub⌋ˢ), the premise whose absence made P6-Cs false.

    CASE MAP for the induction on [ad_pat_sub_g] (paper's own case list at
    :1749, plus the mech-only rows):
      infer/univ_ghost_r/ghostg  ↔ Infer / UnivGhostR / GhostG — leaves with
                                   Ψ = ∅, so Ψa = ∅ and Pa := Pi
      check                      ↔ Case Check — delegates to P6-Cv
                                   [a_solve_eq_complete_var] (flex_apart is
                                   passed straight through), then the four
                                   Pi-subcases guarded / □ / ∀ (impossible)
                                   / ∀◇ with SolS-Check / GhostL / UnivGhostL
      forall_r                   ↔ Case ForallR — refinement inversion gives
                                   P0 = ∀.P0', descend with
                                   [flex_shield_descend_l]; strip β from the
                                   outputs with P6-Cs's ∀-binder kit
      arrow                      ↔ Case Arrow — [flex_shield_arrow_inv];
                                   left premise → P6-Cv, right → IH
      forall_l_{tagged,untagged} ↔ Case ForallL — ε ∈ Ψi forces Pi = ∀β.P1;
                                   descend with [flex_shield_descend_r]
                                   (whose clean-rule exclusion is exactly
                                   the counterexample's death)
      univ_ghost_l/lg            ↔ Case UnivGhostLG — [flex_shield_tophole_l_inv]
                                   / [flex_shield_topholeg_r_inv]
      ghost                      ↔ Case Ghost — impossible (ψa has no □)
      flex_mono                  ↔ the mech's defined-flexible unfolding *)
(** Abstraction never shields more than the body already did. *)
Lemma pskl_shielded_ftv_close_rec_upper : forall P β k,
  pskl_shielded_ftv (close_pskl_wrt_pskl_rec k β P) [<=] pskl_shielded_ftv P.
Proof.
  induction P; intros β k; cbn [close_pskl_wrt_pskl_rec pskl_shielded_ftv];
    try solve [ clear; fsetdec ].
  - destruct (lt_ge_dec n k); cbn [pskl_shielded_ftv]; clear; fsetdec.
  - destruct (β == α); cbn [pskl_shielded_ftv]; clear; fsetdec.
  - specialize (IHP1 β k); specialize (IHP2 β k); fsetdec.
  - apply IHP.
  - pose proof (ftvar_in_pskl_close_pskl_wrt_pskl_rec P β k) as Hcl.
    clear - Hcl; fsetdec.
Qed.

Lemma pskl_shielded_ftv_close_upper : forall P β,
  pskl_shielded_ftv (close_pskl_wrt_pskl β P) [<=] pskl_shielded_ftv P.
Proof.
  intros P β; unfold close_pskl_wrt_pskl;
    apply pskl_shielded_ftv_close_rec_upper.
Qed.

(** SOLVING DOES NOT SHIELD A CONTEXT VARIABLE the subject leaves unshielded.
    Every ∀◇ the output grows has a body drawn from the INPUTS —
    SolS-GhostL / SolS-GhostLF copy the target, SolS-UnivGhostL re-wraps a
    body run whose own subject is already unshielded — and
    [a_solve_sub_ftv]'s escape disjunct is closed off by [β ∈ dom Θ]:
    SS-ForallR's leaked binder is fresh for the context, so it is never β.

    This is what the Sub-ForallL row needs in order to move its binder out of
    the context and into Δ ([a_wf_pskl_tvar_to_delta] below): the mech types
    a ∀◇ body at the EMPTY Δ, so only an UNSHIELDED variable may make that
    move — an asymmetry the paper's single-context [Θ ⊢ P] does not have. *)
(* ⭐ The five binder rows now avoid [ftvar_in_aenv Θ], not [dom Θ] (the
   SolE-FlexR repair, hand-off §2(3): a flexible's PAYLOAD may mention the
   witness).  So "a variable of the context is not this row's binder" needs
   one extra step, [dom_subset_ftvar_in_aenv]; it is the only thing the five
   binder cases of [a_solve_sub_eq_unshielded] had to change. *)
(** ⭐ [guess^TY]'s output is a PAINT, and a paint has no ghost — so it
    SHIELDS NOTHING.  This is the whole content of the new SE-FlexR case of
    [a_solve_sub_eq_unshielded] below: the repaired row returns the guessed
    pattern instead of the flexible, and that pattern can never put a context
    variable under a [∀◇]. *)
(** ⚙️ The binder rows and the THREADED rows now run their premise at a GROWN
    context ([(β ~ tvar) ++ Θ], [Ξ1 ++ Θ]), so "β0 is a variable of the
    context" has to be WEAKENED rather than passed through.  A one-step lemma,
    not [simpl; fsetdec]: the latter was tried at eleven sites and turned this
    file into a multi-minute build. *)
(** ⭐ A CONTEXT VARIABLE IS NEVER A GENERATED NAME.  [a_solve_*_ftv]'s bounds
    all grew a [dom Ξ] term under the repair — the solve invents flexibles now
    — and at every consumer below that term is ELIMINATED rather than absorbed:
    the block dodges everything the context MENTIONS
    ([a_solve_*_generated_fresh]), and [dom Θ ⊆ ftvar_in_aenv Θ]. *)
Lemma solve_eq_generated_not_dom : forall Θ P Q Ξ P' (β0 : atom),
  Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' -> β0 `in` dom Θ -> β0 `notin` dom Ξ.
Proof.
  intros Θ P Q Ξ P' β0 H Hdom Hc.
  assert (Hgf : β0 `notin` ftvar_in_aenv Θ)
    by (eapply a_solve_eq_generated_fresh; [ exact H | exact Hc ]).
  pose proof (dom_subset_ftvar_in_aenv Θ) as Hds.
  clear - Hgf Hds Hdom; fsetdec.
Qed.

Lemma in_dom_app_r : forall (x : atom) (E F : aenv),
  x `in` dom F -> x `in` dom (E ++ F).
Proof. intros x E F H; rewrite dom_app; clear - H; fsetdec. Qed.

Lemma pskl_shielded_ftv_ptyp_to_pskl : forall A,
  pskl_shielded_ftv (ptyp_to_pskl A) [=] empty.
Proof.
  induction A as [ | nA | αA | A1 IH1 A2 IH2 | A0 IH0 ];
    cbn [ptyp_to_pskl pskl_shielded_ftv];
    solve [ clear; fsetdec
          | rewrite IH1; rewrite IH2; clear; fsetdec
          | exact IH0 ].
Qed.

Lemma solve_binder_apart_dom : forall (b β0 : atom) (Θ : aenv) S,
  b `notin` S ->
  ftvar_in_aenv Θ [<=] S ->
  β0 `in` dom Θ ->
  β0 `notin` singleton b.
Proof.
  intros b β0 Θ S Hfr Hsub Hdom.
  pose proof (dom_subset_ftvar_in_aenv Θ) as Hds.
  clear - Hfr Hsub Hdom Hds; fsetdec.
Qed.

Lemma a_solve_sub_eq_unshielded :
  (forall Θ m P Q Ξ P', Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' ->
     forall β0, β0 `in` dom Θ ->
     β0 `notin` pskl_shielded_ftv P -> β0 `notin` ftvar_in_pskl Q ->
     β0 `notin` pskl_shielded_ftv P') /\
  (forall Θ P Q Ξ P', Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' ->
     forall β0, β0 `in` dom Θ ->
     β0 `notin` pskl_shielded_ftv P -> β0 `notin` ftvar_in_pskl Q ->
     β0 `notin` pskl_shielded_ftv P').
Proof.
  (* the three hypotheses about β0 are renamed BY SHAPE before any [cbn]:
     a [cbn] would turn [shielded (∀◇P)] into [ftv P] and make the two
     indistinguishable *)
  (* ⚙️ the THREADED rows (SS-Arrow, SS-GhostLF, SE-Arrow) run their second
     premise at [Ξ1 ++ Θ], so that IH's [β0 ∈ dom …] premise is about the
     GROWN context; [dom_app] discharges it from the incoming one, and the
     first [match] below must therefore accept either shape. *)
  apply a_solve_sub_eq_mutind; intros;
    match goal with Hd : _ `in` dom _ |- _ => rename Hd into Hdom end;
    match goal with Hs : _ `notin` pskl_shielded_ftv _ |- _ =>
      rename Hs into Hsh end;
    match goal with Hf : _ `notin` ftvar_in_pskl _ |- _ =>
      rename Hf into Hft end;
    cbn [pskl_shielded_ftv ftvar_in_pskl] in Hsh, Hft |- *;
    try solve [ clear; fsetdec ];
    try solve [ assumption ].
  - (* SS-ForallL : the closed output shields no more than its body, and the
       rule's binder is fresh for Θ, hence ≠ β0 *)
    match goal with
    | Hfr : ?b `notin` ?S,
      IH : forall b0, b0 `in` dom _ -> _ |- _ =>
      (* pick the FRESHNESS hypothesis, not one of the two [β0 ∉ …] ones *)
      match S with context [ftvar_in_aenv _] => idtac end;
      pose proof (pskl_shielded_ftv_close_upper P' b) as Hcl;
      pose proof (pskl_shielded_ftv_open_upper P (pskl_var_f b)) as Hop;
      cbn [ftvar_in_pskl] in Hop;
      assert (Hne : β0 `notin` singleton b)
        by (match goal with Hd : _ `in` dom ?T |- _ =>
              eapply (@solve_binder_apart_dom b β0 T S);
                [ exact Hfr | clear; fsetdec | exact Hd ] end);
      enough (Hbody : β0 `notin` pskl_shielded_ftv P')
        by (clear - Hbody Hcl; fsetdec);
      apply IH; [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | clear - Hsh Hop Hne; fsetdec | exact Hft ]
    end.
  - (* SS-UnivGhostL : the new ∀◇ body IS the premise's output, so its whole
       ftv is bounded by the inputs; [a_solve_sub_ftv]'s escape disjunct is
       closed off by [β0 ∈ dom Θ] *)
    match goal with Hp : _ ⊢ₛ _ ≼[ _ ] _ ⤳ _ ⨾ _ |- _ =>
      intro Hin; destruct (a_solve_sub_ftv Hp Hin) as [Hl | Hr];
        [ clear - Hl Hsh Hft; fsetdec | clear - Hr Hdom; fsetdec ]
    end.
  - (* SS-Check *)
    match goal with IH : forall b0, b0 `in` dom _ -> _ |- _ =>
      apply IH; [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | exact Hsh | exact Hft ] end.
  - (* SS-ForallR : the target opens at the rule's binder, again ≠ β0 *)
    match goal with
    | Hfr : ?b `notin` ?S,
      IH : forall b0, b0 `in` dom _ -> _ |- _ =>
      (* pick the FRESHNESS hypothesis, not one of the two [β0 ∉ …] ones *)
      match S with context [ftvar_in_aenv _] => idtac end;
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f b))
        as Hop;
      cbn [ftvar_in_pskl] in Hop;
      assert (Hne : β0 `notin` singleton b)
        by (match goal with Hd : _ `in` dom ?T |- _ =>
              eapply (@solve_binder_apart_dom b β0 T S);
                [ exact Hfr | clear; fsetdec | exact Hd ] end);
      apply IH; [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | exact Hsh | clear - Hft Hop Hne; fsetdec ]
    end.
  - (* SS-Arrow *)
    apply notin_union_3;
      [ match goal with
        | IH : forall b0, _ -> _ -> _ -> _ `notin` pskl_shielded_ftv ?X
          |- _ `notin` pskl_shielded_ftv ?X =>
          apply IH; [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | clear - Hsh; fsetdec | clear - Hft; fsetdec ]
        end
      | match goal with
        | IH : forall b0, _ -> _ -> _ -> _ `notin` pskl_shielded_ftv ?X
          |- _ `notin` pskl_shielded_ftv ?X =>
          apply IH; [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | clear - Hsh; fsetdec | clear - Hft; fsetdec ]
        end ].
  - (* SS-GhostLF : the new ∀◇ body is an arrow of two OUTPUTS, both bounded
       by β0-free inputs (a ◇ subject, and the target's two components) *)
    (* ⭐ TWO REPAIR EFFECTS HERE (2026-08-04).  [a_solve_eq_ftv]'s bound now
       carries a [dom Ξ1] term — the eq half GENERATES names — and it is
       eliminated, not absorbed: a generated name dodges everything the
       context MENTIONS ([a_solve_eq_generated_fresh]), and β0 is a variable
       of that context.  And the sub half runs THREADED, at [Ξ1 ++ Θ], so its
       escape disjunct is about the GROWN domain. *)
    match goal with
    | He : _ ⊢ₑ _ ∼ _ ⤳ ?X1 ⨾ _, Hs : _ ⊢ₛ _ ≼[ _ ] _ ⤳ _ ⨾ _ |- _ =>
      pose proof (a_solve_eq_ftv He) as Hfe;
      cbn [ftvar_in_pskl] in Hfe;
      assert (HβΞ1 : β0 `notin` dom X1)
        by (eapply solve_eq_generated_not_dom; [ exact He | exact Hdom ]);
      apply notin_union_3;
        [ clear - Hfe Hft HβΞ1; fsetdec
        | intro Hin; destruct (a_solve_sub_ftv Hs Hin) as [Hl | Hr];
            [ cbn [ftvar_in_pskl] in Hl; clear - Hl Hft; fsetdec
            | rewrite dom_app in Hr; clear - Hr Hdom; fsetdec ] ]
    end.
  - (* ⭐ SE-FlexR (2026-08-04, the repaired row): the output is [guess^TY]'s
       PAINT, which has no ghost at all, so it shields nothing. *)
    pose proof (pskl_shielded_ftv_ptyp_to_pskl A) as He.
    clear - He; fsetdec.
  - (* SE-GhostL : the output IS the target *)
    pose proof (pskl_shielded_ftv_sub_ftv Q) as Hle.
    clear - Hle Hft; fsetdec.
  - (* SE-Arrow *)
    apply notin_union_3;
      [ match goal with
        | IH : forall b0, _ -> _ -> _ -> _ `notin` pskl_shielded_ftv ?X
          |- _ `notin` pskl_shielded_ftv ?X =>
          apply IH; [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | clear - Hsh; fsetdec | clear - Hft; fsetdec ]
        end
      | match goal with
        | IH : forall b0, _ -> _ -> _ -> _ `notin` pskl_shielded_ftv ?X
          |- _ `notin` pskl_shielded_ftv ?X =>
          apply IH; [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | clear - Hsh; fsetdec | clear - Hft; fsetdec ]
        end ].
  - (* SE-Forall *)
    match goal with
    | Hfr : ?b `notin` ?S,
      IH : forall b0, b0 `in` dom _ -> _ |- _ =>
      (* pick the FRESHNESS hypothesis, not one of the two [β0 ∉ …] ones *)
      match S with context [ftvar_in_aenv _] => idtac end;
      pose proof (pskl_shielded_ftv_close_upper P' b) as Hcl;
      pose proof (pskl_shielded_ftv_open_upper P (pskl_var_f b)) as HopP;
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q (pskl_var_f b))
        as HopQ;
      cbn [ftvar_in_pskl] in HopP, HopQ;
      assert (Hne : β0 `notin` singleton b)
        by (match goal with Hd : _ `in` dom ?T |- _ =>
              eapply (@solve_binder_apart_dom b β0 T S);
                [ exact Hfr | clear; fsetdec | exact Hd ] end);
      enough (Hbody : β0 `notin` pskl_shielded_ftv P')
        by (clear - Hbody Hcl; fsetdec);
      apply IH;
        [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | clear - Hsh HopP Hne; fsetdec
        | clear - Hft HopQ Hne; fsetdec ]
    end.
  - (* SE-UnivGhost : as SS-UnivGhostL, but the eq half's bound is EXACT *)
    match goal with Hp : _ ⊢ₑ _ ∼ _ ⤳ ?X ⨾ _ |- _ =>
      pose proof (a_solve_eq_ftv Hp) as Hfe;
      assert (HβΞ : β0 `notin` dom X)
        by (eapply solve_eq_generated_not_dom; [ exact Hp | exact Hdom ]);
      clear - Hfe Hsh Hft HβΞ; fsetdec
    end.
  - (* SE-GhostForall : only the target opens *)
    match goal with
    | Hfr : ?b `notin` ?S,
      IH : forall b0, b0 `in` dom _ -> _ |- _ =>
      (* pick the FRESHNESS hypothesis, not one of the two [β0 ∉ …] ones *)
      match S with context [ftvar_in_aenv _] => idtac end;
      pose proof (pskl_shielded_ftv_close_upper P' b) as Hcl;
      pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q (pskl_var_f b))
        as HopQ;
      cbn [ftvar_in_pskl] in HopQ;
      assert (Hne : β0 `notin` singleton b)
        by (match goal with Hd : _ `in` dom ?T |- _ =>
              eapply (@solve_binder_apart_dom b β0 T S);
                [ exact Hfr | clear; fsetdec | exact Hd ] end);
      enough (Hbody : β0 `notin` pskl_shielded_ftv P')
        by (clear - Hbody Hcl; fsetdec);
      apply IH;
        [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | cbn [pskl_shielded_ftv]; exact Hsh
        | clear - Hft HopQ Hne; fsetdec ]
    end.
  - (* SE-GhostGuarded : the ∀◇ subject is dropped; its body is β0-free, so a
       fortiori β0-unshielded *)
    match goal with IH : forall b0, b0 `in` dom _ -> _ |- _ =>
      apply IH;
        [ exact Hdom
        | match goal with |- _ `notin` pskl_shielded_ftv ?X =>
            pose proof (pskl_shielded_ftv_sub_ftv X) as Hle;
            clear - Hsh Hle; fsetdec end
        | exact Hft ]
    end.
  - (* SE-ForallGhost : only the subject opens *)
    match goal with
    | Hfr : ?b `notin` ?S,
      IH : forall b0, b0 `in` dom _ -> _ |- _ =>
      (* pick the FRESHNESS hypothesis, not one of the two [β0 ∉ …] ones *)
      match S with context [ftvar_in_aenv _] => idtac end;
      pose proof (pskl_shielded_ftv_close_upper P' b) as Hcl;
      pose proof (pskl_shielded_ftv_open_upper P (pskl_var_f b)) as HopP;
      cbn [ftvar_in_pskl] in HopP;
      assert (Hne : β0 `notin` singleton b)
        by (match goal with Hd : _ `in` dom ?T |- _ =>
              eapply (@solve_binder_apart_dom b β0 T S);
                [ exact Hfr | clear; fsetdec | exact Hd ] end);
      enough (Hbody : β0 `notin` pskl_shielded_ftv P')
        by (clear - Hbody Hcl; fsetdec);
      apply IH;
        [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | clear - Hsh HopP Hne; fsetdec
        | cbn [ftvar_in_pskl]; exact Hft ]
    end.
  - (* SE-GuardedGhost *)
    match goal with IH : forall b0, b0 `in` dom _ -> _ |- _ =>
      apply IH; [ solve [ exact Hdom | apply in_dom_app_r; exact Hdom ] | exact Hsh | cbn [ftvar_in_pskl]; exact Hft ]
    end.
Qed.

(** Converse of [a_wf_pskl_delta_to_tvar], under the condition the mech's
    ∀◇ rule forces: its body is typed at the EMPTY Δ, so a rigid CONTEXT
    entry may be re-read as a Δ-variable only when it is UNSHIELDED. *)
Lemma a_wf_pskl_tvar_to_delta : forall Θ1 β Θ2 Δ P,
  (Θ1 ++ (β ~ abind_tvar) ++ Θ2) ⨟ Δ ⊢ₚₛᵃ P ->
  β `notin` pskl_shielded_ftv P ->
  (Θ1 ++ Θ2) ⨟ (add β Δ) ⊢ₚₛᵃ P.
Proof.
  intros Θ1 β Θ2 Δ P H.
  remember (Θ1 ++ (β ~ abind_tvar) ++ Θ2) as Θfull eqn:HeqΘ.
  revert Θ1 Θ2 HeqΘ; induction H; intros Θ1 Θ2 HeqΘ Hsh; subst;
    cbn [pskl_shielded_ftv] in Hsh.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var.
    destruct H as [HΔ | Hbt]; [ left; clear - HΔ; fsetdec | ].
    destruct (α == β) as [-> | Hne]; [ left; clear; fsetdec | ].
    right; destruct Hbt as [Hb | [Hb | [τ Hb]]];
      [ left | right; left | right; right; exists τ ];
      eapply binds_remove_mid; solve [ exact Hb | auto ].
  - apply a_wf_pskl__arrow;
      [ apply IHa_wf_pskl1; solve [ reflexivity | clear - Hsh; fsetdec ]
      | apply IHa_wf_pskl2; solve [ reflexivity | clear - Hsh; fsetdec ] ].
  - apply a_wf_pskl__all with (L := L `union` singleton β).
    intros α Hα.
    eapply a_wf_pskl_delta_mono;
      [ apply H0; [ clear - Hα; fsetdec | reflexivity
                  | pose proof (pskl_shielded_ftv_open_upper P (pskl_var_f α))
                      as Hop; cbn [ftvar_in_pskl] in Hop;
                    clear - Hsh Hop Hα; fsetdec ]
      | clear; fsetdec ].
  - apply a_wf_pskl__hole.
  - (* ∀◇ : the body is β-FREE (that is what unshielded says), so the entry
       is simply STRIPPED instead of moved *)
    apply a_wf_pskl__tophole; [ exact H | ].
    eapply (@a_wf_pskl_strip_tvar Θ1 β Θ2); [ exact H0 | exact Hsh ].
Qed.

(** A flexible entry is a context entry, so a flexible variable is wf.
    (The three [a_binds_tvar] disjuncts are tvar / flex / defined flex.) *)
Lemma a_wf_pskl_flex_var : forall Θ Δ α,
  a_flex_tvar Θ α -> Θ ⨟ Δ ⊢ₚₛᵃ (pskl_var_f α).
Proof.
  intros Θ Δ α Hf. apply a_wf_pskl__var. right.
  destruct Hf as [Hb | [τ Hb]];
    [ right; left; exact Hb | right; right; exists τ; exact Hb ].
Qed.

(* ⭐⭐ P6-Sv UNDER THE SolE-FlexR REPAIR — GREEN (2026-08-05).

   The conclusion is [solve_sub_ext] (prop_look_complete.v): the block [Ξ] the
   solve now generates, its aligned extension [κ'], the freshness against an
   avoid-set PARAMETER [L], the payloads' well-formedness at a FIXED [Θw], and
   the paper's [Θ0 ⊢ P_a] — restated at [Ξ ++ Θ0], since the repaired
   SolE-FlexR lets the output mention the generated block.

   ── the four things the conversion turned on ─────────────────────────────
   1. ⭐ THE CHECK ROW CALLS [a_solve_eq_complete_var_at], not the paper-facing
      [a_solve_eq_complete_var]: the latter pins [Θw := Θ] and this proof runs
      under Sub-ForallL / Sub-ForallR, which grow Θ.
   2. ⭐ THE ARROW ROW's two halves THREAD (SS-Arrow runs its second premise at
      [Ξ1 ++ Θ0]), so [KEY] cannot hand the two solves back independently — it
      returns the MERGED package, and the RIGHT IH runs at [Ξ1 ++ Θ0] under
      [κ1 ++ κ].  Everything that transport needs comes from ONE fact, the Ξ
      scoping kit's master invariant: a generated name dodges everything the
      context MENTIONS ([a_solve_eq_generated_fresh]).
   3. ⚠️ NO [ftvar_in_uskl ψa [<=] dom Θw] PREMISE, unlike P6-Cs.  It is NOT
      invariant here — the ForallL row runs its IH at the guess [open ψsrc β]
      with β a fresh rigid deliberately ABSENT from [Θw] — and it is not
      needed, since the only lemma this proof feeds a guess to is P6-Cv's
      [_at], which carries no guess-scope premise.  The ρ-side companion
      [Δρ ∩ dom Θw = ∅] IS invariant (Δρ grows only by such a fresh rigid) and
      is what makes the SOLVE block's payloads Δρ-clean.
   4. ⭐ THE ∀◇ SUBCASE OF THE CHECK ROW COLLAPSED.  The paper takes a WLOG
      there ("we ASSUME refb is derived by SolEq-GhostGuarded",
      subtyping-proofs.tex:1810) that the mech previously had to DISCHARGE,
      because the old SolEq-FlexR also accepted a ∀◇ subject.  The repaired
      row carries [nonghost_pskl], which has no [tophole] constructor, so
      SolEq-GhostGuarded is the only surviving row: the paper's WLOG is now a
      THEOREM of the rule shape, and ~50 lines of case analysis are gone.

   ⚙️ [L] is a BINDER NAME of the cofinite [ad_pat_sub_g] rules, so the
   avoid-set is introduced as [Lav] after [induction]. *)
Theorem a_solve_sub_complete_var :
  forall n NM M Θ0 Θs Θ Θw κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0,
  a_wf_aenv Θ -> a_wf_aenv Θ0 ->
  (* ⭐ THE Θw PACK (2026-08-04, the SolE-FlexR repair) — identical to P6-Cv's
     and P6-Cs's, and needed for the same reason: the SOLVE now emits a block,
     the ∀ rows run the IH at [Θ,β] and then STRIP β from the increase, and
     the block's payloads can only dodge β by being well-formed in a context
     that PREDATES the binder.  [Θw] is FIXED as the construction goes under
     binders; only the two [binds] conditions and the κ-image bound move.
     Vacuous at the top-level call ([Θw := Θ]). *)
  a_wf_aenv Θw ->
  (forall x b, binds x b Θw -> binds x b Θ) ->
  (forall x b, binds x b Θ -> binds x b Θw \/ b = abind_tvar) ->
  (forall α, a_flex_tvar Θ0 α ->
     ftvar_in_ptyp (msubst_lookup κ α) [<=] dom Θw) ->
  (* ⚠️ NO [ftvar_in_uskl ψa [<=] dom Θw] here, unlike P6-Cs.  It would NOT be
     invariant: the ForallL row runs its IH at the guess [open ψsrc β] with β a
     fresh rigid of Θ that is deliberately ABSENT from the fixed [Θw].  And it
     is not needed — the only lemma this proof feeds a guess to is P6-Cv's
     [a_solve_eq_complete_var_at], which carries no guess-scope premise.
     (P6-Cs needs it because ITS flexible-P0 row reads a κs payload off ψa.)
     The ρ-side companion below IS invariant: Δρ only ever grows by a rigid
     picked fresh for Θ ⊇ Θw. *)
  Δρ ∩ dom Θw [=] empty ->
  Θ0 ⨟ empty ⊢ₚₛᵃ Pi -> Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->   (* skmod[SK]{P0}{M} *)
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->   (* skmod[TY]{P0}{M} *)
  κ ∷ Θ0 ⊑ Θ ->
  uskl_rho NM Θ Δρ Ψρ ψsub ψa ->                    (* ψsub = ρ(ψa) *)
  a_tags_sort NM Ψ' ψa ->
  Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψsub ⌋ˢ ->                       (* subject wf (P6-Cs) *)
  Ψi `union` Ψa [=] Ψ' ->                           (* the paper's Ψi,Ψa = Ψ' *)
  Ψρ ∩ Ψ' [=] empty ->                              (* the paper's fresh{Ψ'} *)
  rho_fresh Δρ Θ κ -> Δρ [<=] Δ ->
  (forall α, α `in` Δρ ->
     α `notin` pskl_shielded_ftv (msubst_pskl κ Pi)) ->
  delta_def_fresh Δ Θ ->
  Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa ->
  Ψsub [<=] Ψρ `union` Ψa ->
  Ψa [<=] Ψsub ->
  (* the derivation lives in a SMALLER context [Θs]: Sub-ForallL must run
     the IH at [Θ,β] while the derivation's own context is an index and
     cannot move, so the context the rest of the premises talk about is
     generalized and only related to [Θs] by [binds]-monotonicity.  This is
     the mech's reading of the paper's "by weakening \refn[9] to Θ,β"
     (subtyping-proofs.tex:2153); at the top level [Θs = Θ]. *)
  (forall x b, binds x b Θs -> binds x b Θ) ->
  ad_pat_sub_g n NM M Ψsub Θs ψsub Q ->
  Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
  (* ⭐ THE AVOID-SET PARAMETER: the SOLVE generates its own block now, and at
     a binder row the witness has to be fixed BEFORE the block is picked. *)
  forall L, ftvar_in_aenv Θ0 [<=] L ->
  (* [solve_sub_ext] (prop_look_complete.v) packages the block [Ξ], its
     aligned extension [κ'], the freshness, the payloads' well-formedness at
     the FIXED [Θw], and the paper's [Θ0 ⊢ P_a] — which is a CONCLUSION of
     this lemma, not a consequence of a general "solving preserves
     well-formedness" (there is no such property once SS-ForallR is faithful,
     since its binder escapes into the output: cex/cex_solve_sub_wf_leak.v),
     and which is now stated at [Ξ ++ Θ0] because the repaired SolE-FlexR
     lets the output mention the generated block. *)
  solve_sub_ext Θ0 Θw M Pi P0 L
    (fun κ' Pa =>
       Θ ⨟ Δ ⊢ (msubst_pskl (κ' ++ κ) Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa).
Proof.
  intros n NM M Θ0 Θs Θ Θw κ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0.
  intros HwfΘ HwfΘ0 HwfΘw Hmon Hnr Hκw HΔρw
         HwfPi HwfP0 HmodSK HmodTY Hκ Hrho Htags HwfSub
         Htageq Hinter Hrhof Hdelta Hapart Hdfresh Hpre
         HΨs1 HΨs2 Hext Hsub Hrefine.
  (* everything except the derivation is generalized: ForallR/ForallL both
     extend Θ0 and Θ, ForallL grows Δρ/Δ and rewrites the tag split, and
     Arrow splits P0/Pi/ψa — so no premise may stay fixed *)
  (* ⚠️ [Θw] is NOT reverted — it is the FIXED well-formedness context, and
     keeping it fixed under the ∀ rows is exactly what lets β be stripped out
     of the increase.  Its five companion premises DO move, since each of them
     also mentions a reverted variable. *)
  revert Θ Θ0 κ Δ Δρ Ψρ Ψ' Ψi Ψa ψa Pi P0
         HwfΘ HwfΘ0 Hmon Hnr Hκw HΔρw
         HwfPi HwfP0 HmodSK HmodTY Hκ Hrho Htags HwfSub
         Htageq Hinter Hrhof Hdelta Hapart Hdfresh Hpre
         HΨs1 HΨs2 Hext Hrefine.
  (* the lemma's [Ψ'] is re-introduced as [Ψt]: [Ψ'] is a BINDER NAME of
     the ForallL rules, so [induction] has already claimed it *)
  induction Hsub; intros
    Θe Θ0 κ Δ Δρ Ψρ Ψt Ψi Ψa ψa Pi P0
    HwfΘ HwfΘ0 Hmon Hnr Hκw HΔρw
    HwfPi HwfP0 HmodSK HmodTY Hκ Hrho Htags HwfSub
    Htageq Hinter Hrhof Hdelta Hapart Hdfresh Hpre
    (* ⚠️ [L] is a BINDER NAME of the cofinite [ad_pat_sub_g] rules, which
       [induction] has already claimed — the avoid-set comes in as [Lav]. *)
    HΨs1 HΨs2 Hext Hrefine Lav HLav;
    (* the derivation's own context is the rule binder [Θ]; the generalized
       one comes back in as [Θe].  Renaming it back keeps every closed case
       textually unchanged: each rule premise that mentions the SMALL
       context is weakened on the spot. *)
    rename Θ into Θsm; rename Θe into Θ.
  (* each rule premise stated in the SMALL context is weakened on the spot,
     so every closed case below reads exactly as before *)
  all: match goal with
       | Hx : forall x b, binds x b ?S -> binds x b _ |- _ =>
         repeat match goal with
         | H : _ ⨟ S ⊢ₛᵃ _ ∼ _ |- _ =>
             let H' := fresh "Hw" in
             pose proof (ad_pat_consis_weaken H _ Hx) as H';
             clear H; rename H' into H
         | H : S ⨟ _ ⊢ₚₛᵃ _ |- _ =>
             let H' := fresh "Hw" in
             pose proof (a_wf_pskl_weaken Hx H) as H';
             clear H; rename H' into H
         | H : binds _ _ S |- _ => apply Hx in H
         end
       end.
  - (* Infer : M = TI, so [skmod] forces P0 = □ and SolS-Vacuous applies
       with Pa := Pi; the rule's [Ψ = ∅] collapses the tag conclusion *)
    assert (HP0 : P0 = pskl_hole).
    { destruct NM;
        [ pose proof (HmodTY eq_refl) as Hm | pose proof (HmodSK eq_refl) as Hm ];
        inversion Hm; reflexivity. }
    subst P0.
    (* SolS-Vacuous generates nothing *)
    eapply solve_sub_ext_nil with (Pa := Pi);
      [ apply a_solve_sub__vacuous | exact HwfPi | cbn [app] ].
    eapply ad_partial_precise_psi_cong; [ exact Hpre | ].
    assert (HPsiae : Ψa [=] empty) by (clear - HΨs2 H; fsetdec).
    clear - HPsiae; fsetdec.
  - (* Check (TY/TC).  The premise IS a consistency judgment, so P6-Cv
       ([a_solve_eq_complete_var]) applies verbatim — every premise of this
       lemma is one of its premises, with [flex_apart] read off the walk.
       It returns the EQUALITY solve; SolS-Check then lifts it, after a
       case analysis on Pi.  P0 is GUARDED here: [skmod{TY}] makes it a
       type, and a ∀ is excluded because a [bskl_all_inh] target cannot be
       the inherited painting of a GUARDED B. *)
    assert (HgP0 : guarded_pskl P0).
    { pose proof (HmodTY eq_refl) as Hmod.
      inversion Hmod as [ | A HeqA | ]; subst.
      destruct A as [ | nA | αA | A1 A2 | A0 ]; cbn [ptyp_to_pskl] in *.
      - apply guarded_pskl__unit.
      - inversion HwfP0.
      - apply guarded_pskl__var.
      - pose proof (a_wf_pskl_lc HwfP0) as Hlc; inversion Hlc; subst.
        apply guarded_pskl__arrow; assumption.
      - (* ∀ : its inherited painting is a [bskl_all_inh], and the target is
           the inherited painting of a GUARDED B — which is never one *)
        exfalso.
        assert (HgQ : guarded_bskl (pskl_to_bskl_inh B))
          by (apply guarded_pskl_to_bskl_inh; exact H0).
        cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
        (* [inversion] leaves the target as an EQUATION against
           [pskl_to_bskl_inh B]; expose B's shape first *)
        destruct B; cbn [pskl_to_bskl_inh] in Hrefine, HgQ;
          try solve [ inversion HgQ ];
          inversion Hrefine; subst;
          solve [ (* an inherited ∀ never refines to a monotype paint *)
                  eapply ad_refine_allinh_lhs_mono_absurd;
                    [ exact HwfΘ | eassumption | reflexivity | reflexivity
                    | eapply a_wf_aenv_binds_def_mono;
                        [ exact HwfΘ | eassumption ] ] ]. }
    (* the subject is the RULE's [T] here, not the statement's ψsub *)
    (* the subject is the RULE's [T] here, not the statement's ψsub.
       ⭐ [a_solve_eq_complete_var_at], NOT the paper-facing
       [a_solve_eq_complete_var]: the latter pins [Θw := Θ], and this proof
       runs under Sub-ForallL / Sub-ForallR, which grow Θ. *)
    destruct (@a_solve_eq_complete_var_at a_sub_mode_ty Θ0 Θ Θw κ Δ Δρ Ψρ Ψt
                Ψi Ψa Ψ T ψa (pskl_to_bskl_inh B) Pi P0
                HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfPi HwfP0 Hκ Hκw Hrho Htags
                ltac:(clear - Htageq; fsetdec) Hinter Hrhof Hdelta Hapart
                Hdfresh Hpre HΨs1 HΨs2 H1
                Hrefine Lav HLav)
      as (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & Hp).
    (* the paper's [Θ0 ⊢ P_a] for this row — at [Ξ ++ Θ0] now, since the
       repaired SolE-FlexR lets the output mention the block the solve
       generated.  The EQ half never leaks, so its wf preservation is still a
       real property ([a_solve_eq_wf], whose statement moved with it). *)
    assert (HwfPa : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pa)
      by (eapply a_solve_eq_wf; [ exact Hs | exact HwfPi | exact HwfP0 ]).
    (* now lift the equality solve to a subtyping one, by Pi's shape *)
    destruct Pi as [ | nPi | β | Pi1 Pi2 | Pi' | | Pi' ].
    + (* ⟨⟩ : guarded *)
      exists Ξ, Pa, κ'.
      repeat (split;
        [ solve [ apply a_solve_sub__check;
                    [ apply guarded_pskl__unit | exact HgP0 | exact Hs ]
                | exact Hfm | exact Hu | exact Hk | exact Hfr | exact HF
                | exact HwfPa ] | ]).
      exact Hp.
    + inversion HwfPi.
    + (* a variable : guarded *)
      exists Ξ, Pa, κ'.
      repeat (split;
        [ solve [ apply a_solve_sub__check;
                    [ apply guarded_pskl__var | exact HgP0 | exact Hs ]
                | exact Hfm | exact Hu | exact Hk | exact Hfr | exact HF
                | exact HwfPa ] | ]).
      exact Hp.
    + (* an arrow : guarded *)
      assert (Hg : guarded_pskl (pskl_arrow Pi1 Pi2)).
      { pose proof (a_wf_pskl_lc HwfPi) as Hlc; inversion Hlc; subst.
        apply guarded_pskl__arrow; assumption. }
      exists Ξ, Pa, κ'.
      repeat (split;
        [ solve [ apply a_solve_sub__check; [ exact Hg | exact HgP0 | exact Hs ]
                | exact Hfm | exact Hu | exact Hk | exact Hfr | exact HF
                | exact HwfPa ] | ]).
      exact Hp.
    + (* ∀ : IMPOSSIBLE — precision forces a ∀-shaped GUESS, and ρ maps a ∀
         to a ∀ (or to a variable at a leaf), never to the GUARDED subject
         this rule requires *)
      exfalso.
      cbn [msubst_pskl] in Hpre.
      inversion Hpre; subst.
      * (* P-Forall : the guess is a ∀^ε, so ρ makes the subject one too *)
        inversion Hrho; subst;
          match goal with Hg : guarded_uskl _ |- _ => inversion Hg end.
      * (* P-FlexR : the guess is a defined flexible; unfolding it leaves a
           ∀ subject against a MONOTYPE painting *)
        eapply ad_ppre_allsyn_subject_mono_absurd;
          [ exact HwfΘ | eassumption | reflexivity | reflexivity
          | eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | eassumption ] ].
    + (* □ : SolS-GhostL wraps P0.  A GHOST SUBJECT PINS THE BLOCK TO [nil]
         ([a_solve_eq_hole_subject_inv], true only because of the repair's
         [nonghost_pskl] side condition), so the extension is [nil] too — read
         off [keys κ' = keys nil]. *)
      destruct (a_solve_eq_hole_subject_inv Hs) as [-> ->].
      assert (Hκnil : κ' = nil)
        by (destruct κ' as [ | p κ0 ]; [ reflexivity | discriminate Hk ]).
      subst κ'. cbn [app] in Hp.
      eapply solve_sub_ext_nil with (Pa := pskl_tophole P0);
        [ apply a_solve_sub__ghost_l; exact HgP0
        | apply a_wf_pskl__tophole; [ exact HgP0 | exact HwfP0 ]
        | cbn [app msubst_pskl]; apply ad_ppre__tophole_remove; exact Hp ].
    + (* ∀◇Pi' : strip the ghost, solve the body, wrap the output.

         ⭐ THIS ROW COLLAPSED UNDER THE REPAIR (2026-08-05).  The paper says
         "by congruence of constraint solving, we ASSUME refb is derived by
         SolEq-GhostGuarded" (subtyping-proofs.tex:1810) — a WLOG the mech
         previously had to DISCHARGE, because the old SolEq-FlexR also
         accepted a ∀◇ subject and returned the flexible, so P6-Cv could hand
         back either derivation.  The repaired row carries [nonghost_pskl],
         which has no [tophole] constructor, so FlexR can no longer fire here:
         SolEq-GhostGuarded is the ONLY surviving row and the paper's WLOG is
         now a THEOREM of the rule shape.  (~50 lines of case analysis, and
         the [ptyp_to_bskl_inh_syn_eq] / [ad_pat_consis_monoish_counterpart]
         detour that went with it, are gone.) *)
      assert (HgPi' : guarded_pskl Pi') by (inversion HwfPi; assumption).
      assert (HwfPi' : Θ0 ⨟ empty ⊢ₚₛᵃ Pi')
        by (eapply a_wf_pskl_tophole_inv; exact HwfPi).
      (* the payload is GUARDED, which kills the □-, ∀◇- and ∀-payload rows;
         [nonghost_pskl] kills SolEq-FlexR *)
      inversion Hs; subst;
        try solve [ inversion HgP0
                  | match goal with Hng : nonghost_pskl _ |- _ =>
                      inversion Hng end ].
      match goal with Hbody : Θ0 ⊢ₑ Pi' ∼ _ ⤳ _ ⨾ _ |- _ =>
        exists Ξ, (pskl_tophole Pa), κ';
        repeat (split;
          [ solve [ apply a_solve_sub__univ_ghost_l;
                      apply a_solve_sub__check;
                        [ exact HgPi' | exact HgP0 | exact Hbody ]
                  | exact Hfm | exact Hu | exact Hk | exact Hfr | exact HF
                  | apply a_wf_pskl__tophole;
                      [ eapply (proj2 a_solve_sub_eq_guarded);
                          [ exact Hbody
                          | eapply a_wf_pskl_lc; exact HwfPi'
                          | eapply a_wf_pskl_lc; exact HwfP0
                          | exact HgPi' ]
                      | exact HwfPa ] ] | ])
      end.
      cbn [msubst_pskl]. apply ad_ppre__tophole_remove. exact Hp.
  - (* ForallR (TY/TC).  [skmod{TY}] makes P0 a TYPE, so the refinement's
       inherited-∀ target forces P0 = ∀.P0' (every other type shape is
       GUARDED, and a guarded source refines only to a guarded target).
       Then descend the payload — the guess is untouched — and strip the
       binder from the outputs with P6-Cs's ∀-kit. *)
    pose proof (HmodTY eq_refl) as Hmod.
    inversion Hmod as [ | A HeqA | ]; subst.
    destruct A as [ | nA | αA | A1 A2 | A0 ];
      cbn [ptyp_to_pskl] in HwfP0, Hrefine, Hapart, Hpre |- *.
    + (* ⟨⟩ : guarded *)
      exfalso;
        assert (Hbad : guarded_bskl (bskl_all_inh B));
        [ eapply ad_refine_syn_guarded_r;
            [ exact HwfΘ | exact Hrefine
            | apply guarded_pskl_to_bskl_inh;
              eapply guarded_pskl_msubst_inc;
                [ exact Hκ | apply guarded_pskl__unit ] ]
        | inversion Hbad ].
    + (* a bound variable is not well-formed *) inversion HwfP0.
    + (* a variable : guarded *)
      exfalso;
        assert (Hbad : guarded_bskl (bskl_all_inh B));
        [ eapply ad_refine_syn_guarded_r;
            [ exact HwfΘ | exact Hrefine
            | apply guarded_pskl_to_bskl_inh;
              eapply guarded_pskl_msubst_inc;
                [ exact Hκ | apply guarded_pskl__var ] ]
        | inversion Hbad ].
    + (* an arrow : guarded *)
      exfalso.
      assert (Hg : guarded_pskl (pskl_arrow (ptyp_to_pskl A1) (ptyp_to_pskl A2))).
      { pose proof (a_wf_pskl_lc HwfP0) as Hlc; inversion Hlc; subst.
        apply guarded_pskl__arrow; assumption. }
      assert (Hbad : guarded_bskl (bskl_all_inh B));
        [ eapply ad_refine_syn_guarded_r;
            [ exact HwfΘ | exact Hrefine
            | apply guarded_pskl_to_bskl_inh;
              eapply guarded_pskl_msubst_inc; [ exact Hκ | exact Hg ] ]
        | inversion Hbad ].
    + (* P0 = ∀.P0' : the real row *)
      cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
      inversion Hrefine; subst.
      match goal with Hr : forall α, α `notin` ?Lr -> _ ⨟ _ ⊢ᵣᵃ _ ⊳ _ |- _ =>
        rename Hr into Hrbody; remember Lr as Lr0 eqn:HeqLr; clear HeqLr end.
      inversion HwfP0; subst.
      match goal with Hw : forall α, α `notin` ?Lw -> _ ⨟ _ ⊢ₚₛᵃ _ |- _ =>
        rename Hw into Hw0body; remember Lw as Lw0 eqn:HeqLw; clear HeqLw end.
      (* ⭐ [ftvar_in_aenv Θ0], not just [dom Θ0]: SS-ForallR's freshness side
         condition moved there with the repair (§2(3) of the hand-off — a
         flexible's PAYLOAD may mention the witness). *)
      pick fresh β for
        (L `union` Lr0 `union` Lw0 `union` dom Θ `union` dom Θ0
           `union` ftvar_in_aenv Θ0
           `union` dom κ `union` ftvar_in_uskl ψa `union` ftvar_in_pskl Pi
           `union` ftvar_in_pskl (ptyp_to_pskl A0) `union` def_ftv Θ
           `union` Δ).
      assert (HβΘ : β `notin` dom Θ) by (clear - Fr; solve_notin).
      assert (HβΘ0 : β `notin` dom Θ0) by (clear - Fr; solve_notin).
      assert (Hβκ : β `notin` dom κ) by (clear - Fr; solve_notin).
      assert (Hβψa : β `notin` ftvar_in_uskl ψa) by (clear - Fr; solve_notin).
      assert (Hwfβ : a_wf_aenv ((β ~ abind_tvar) ++ Θ))
        by (apply a_wf_aenv__tvar; assumption).
      assert (Hwfβ0 : a_wf_aenv ((β ~ abind_tvar) ++ Θ0))
        by (apply a_wf_aenv__tvar; assumption).
      assert (Hweak : forall (x : atom) (b : abind),
                binds x b Θ0 -> binds x b ((β ~ abind_tvar) ++ Θ0))
        by (intros x b Hb; apply binds_app_3; exact Hb).
      (* the Θw pack under the binder: [Θw] itself does NOT move — keeping it
         fixed is what lets β be stripped out of the package's payloads *)
      assert (Hmonβ : forall x b, binds x b Θw ->
                binds x b ((β ~ abind_tvar) ++ Θ))
        by (intros x b Hb; apply binds_app_3; apply Hmon; exact Hb).
      assert (Hnrβ : forall x b, binds x b ((β ~ abind_tvar) ++ Θ) ->
                binds x b Θw \/ b = abind_tvar).
      { intros x b Hb.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heq] | Hb'];
          [ right; exact Heq | exact (Hnr _ _ Hb') ]. }
      assert (Hκwβ : forall α0, a_flex_tvar ((β ~ abind_tvar) ++ Θ0) α0 ->
                ftvar_in_ptyp (msubst_lookup κ α0) [<=] dom Θw)
        by (intros α0 Hf; apply Hκw; eapply a_flex_tvar_strip_tvar; exact Hf).
      assert (HβΘw : β `notin` dom Θw)
        by (pose proof (@aenv_binds_dom_sub Θw Θ Hmon) as Hdw;
            clear - Hdw HβΘ; fsetdec).
      (* the IH's avoid-set is [add β Lav]: the block is emitted OUTSIDE the ∀
         and the rule LEAKS β, so [β ∉ dom Ξ] is what removes β from the
         output's ftv bound *)
      assert (HLavβ : ftvar_in_aenv ((β ~ abind_tvar) ++ Θ0) [<=] add β Lav)
        by (rewrite ftvar_in_aenv_cons_tvar; clear - HLav; fsetdec).
      assert (HwfP0β : ((β ~ abind_tvar) ++ Θ0) ⨟ empty
                ⊢ₚₛᵃ (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f β))).
      { eapply a_wf_pskl_delta_to_tvar_mid
          with (α1 := β) (Θ1 := nil) (Θ2 := Θ0) (Δ' := empty);
          [ apply (Hw0body β ltac:(clear - Fr; solve_notin))
          | reflexivity | clear; fsetdec ]. }
      assert (HwfPiβ : ((β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pi)
        by (eapply a_wf_pskl_weaken; [ exact Hweak | exact HwfPi ]).
      assert (Hκβ : κ ∷ ((β ~ abind_tvar) ++ Θ0) ⊑ ((β ~ abind_tvar) ++ Θ))
        by (apply a_inc_cons_tvar; exact Hκ).
      assert (Hdfreshβ : delta_def_fresh Δ ((β ~ abind_tvar) ++ Θ)).
      { intros β0 α0 τ0 Hβ0 Hb. eapply Hdfresh; [ exact Hβ0 | ].
        destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
          [ discriminate Habs | exact Hb' ]. }
      assert (Hrhofβ : rho_fresh Δρ ((β ~ abind_tvar) ++ Θ) κ).
      { intros α0 Hα0. destruct (Hrhof α0 Hα0) as (Hb & Him & Hdf).
        repeat split;
          [ apply binds_app_3; exact Hb | exact Him | ].
        intros α1 τ1 Hb1. eapply Hdf.
        destruct (binds_cons_1 _ _ _ _ _ _ Hb1) as [[_ Habs] | Hb'];
          [ discriminate Habs | exact Hb' ]. }
      assert (Hpreβ : ((β ~ abind_tvar) ++ Θ) ⨟ Δ
                ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] ψa)
        by (eapply ad_partial_precise_weaken;
              [ exact Hpre | intros x b Hb; apply binds_app_3; exact Hb ]).
      assert (Hrefβ : ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣᵃ
                (pskl_to_bskl_inh
                   (msubst_pskl κ (open_pskl_wrt_pskl (ptyp_to_pskl A0)
                                     (pskl_var_f β))))
                ⊳ (open_bskl_wrt_bskl B (bskl_var_f β))).
      { rewrite (@msubst_pskl_open Θ0 κ Θ (ptyp_to_pskl A0) β Hκ Hβκ).
        rewrite pskl_to_bskl_inh_open.
        eapply ad_refine_syn_delta_to_tvar_mid
          with (α1 := β) (Θ1 := nil) (Θ2 := Θ) (Δ' := empty);
          [ apply (Hrbody β ltac:(clear - Fr; solve_notin))
          | reflexivity | clear; fsetdec ]. }
      edestruct (H0 β ltac:(clear - Fr; solve_notin)
                   ((β ~ abind_tvar) ++ Θ)
                   ((β ~ abind_tvar) ++ Θ0) κ Δ Δρ Ψρ Ψt Ψi Ψa ψa Pi
                   (open_pskl_wrt_pskl (ptyp_to_pskl A0) (pskl_var_f β))
                   Hwfβ Hwfβ0 Hmonβ Hnrβ Hκwβ HΔρw HwfPiβ HwfP0β
                   ltac:(intro Hc; discriminate Hc)
                   ltac:(intros _;
                         rewrite <- ptyp_to_pskl_open;
                         apply a_ty_mode_compat__tc)
                   Hκβ
                   ltac:(eapply uskl_rho_weaken;
                         [ exact Hrho
                         | intros x b Hb; apply binds_app_3; exact Hb ])
                   Htags
                   ltac:(eapply a_wf_pskl_weaken;
                         [ intros x b Hb; apply binds_app_3; exact Hb
                         | exact HwfSub ])
                   Htageq Hinter Hrhofβ Hdelta Hapart Hdfreshβ
                   Hpreβ HΨs1 HΨs2
                   ltac:(intros x b Hb;
                         unfold binds in Hb |- *; simpl in Hb |- *;
                         destruct Hb as [Heqb | Hb'];
                           [ left; exact Heqb | right; apply Hext; exact Hb' ])
                   Hrefβ (add β Lav) HLavβ)
        as (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & HwfPaβ & Hp).
      (* --- strip β from every output --- *)
      assert (HβΞ : β `notin` dom Ξ)
        by (intro Hc; pose proof (Hfr β Hc) as Hf; clear - Hf; fsetdec).
      assert (Hdκ : dom κ' [=] dom Ξ) by (apply keys_eq_dom; exact Hk).
      (* β is not free in the output — read off the PRECISION conclusion, as
         the paper does (subtyping-proofs.tex:1898): its subject's variables
         come from the guess (β-free by choice), from Δ (β is fresh) or from
         Θ (β is not there); and β is in NEITHER metasubstitution's domain —
         not κ's by choice, not the SOLVE BLOCK's because the IH was run at
         an avoid-set containing β. *)
      assert (HβPa : β `notin` ftvar_in_pskl Pa).
      { assert (HβΔ : β `notin` Δ) by (clear - Fr; solve_notin).
        assert (Hβdef : β `notin` def_ftv Θ) by (clear - Fr; solve_notin).
        assert (Hsrc : β `notin` ftvar_in_pskl (msubst_pskl (κ' ++ κ) Pa)).
        { eapply ad_partial_precise_src_ftv_avoid;
            [ exact Hp | exact Hβψa | exact HβΔ
            | (* β is bound as a rigid tvar, never as a definition *)
              intros τ0 Hb;
              destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
                [ discriminate Habs
                | apply HβΘ; eapply binds_In; exact Hb' ]
            | cbn [def_ftv]; exact Hβdef ]. }
        pose proof (msubst_pskl_ftv_dom_lower (κ' ++ κ) Pa) as Hlo.
        rewrite dom_app in Hlo.
        clear - Hsrc Hlo Hβκ HβΞ Hdκ; fsetdec. }
      (* … and THAT is what removes β from the paper's [Θ0,β ⊢ P_a]
         (subtyping-proofs.tex:1897-1900), verbatim — at [Ξ ++ Θ0] now *)
      assert (HwfPa0 : (Ξ ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pa)
        by (eapply (@a_wf_pskl_strip_tvar Ξ β Θ0); [ exact HwfPaβ | exact HβPa ]).
      (* ⭐ the SOLVE BLOCK's payloads dodge β because they are well-formed in
         the FIXED [Θw], which predates the binder *)
      assert (Hβκ' : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κ').
      { rewrite Forall_forall. intros p Hp0.
        pose proof (forall_wf_mono_images_dom HF p Hp0) as Hb.
        clear - Hb HβΘw; fsetdec. }
      exists Ξ, Pa, κ'.
      repeat (split;
        [ solve [ (* rebuild SolS-ForallR.  The rule is EXISTS-FRESH and LEAKS
                     its binder, and — since the repair — it runs its premise
                     at [(β ~ tvar) ++ Θ0], so the IH's output IS the premise:
                     no strengthening, no family to manufacture. *)
                  apply a_solve_sub__forall_r with (β := β);
                    [ clear - Fr; solve_notin | exact Hs ]
                | exact Hfm | exact Hu | exact Hk
                | intros α0 Hα0; pose proof (Hfr α0 Hα0) as Hf;
                  clear - Hf; fsetdec
                | exact HF | exact HwfPa0 ] | ]).
      eapply ad_partial_precise_strip_tvar_mid
        with (β := β) (Θ1 := nil) (Θ2 := Θ);
        [ exact Hp | reflexivity
        | intros α0 τ0 Hb;
          assert (Hb' : binds α0 (abind_flex_mono_def τ0) Θ)
            by (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
                  [ discriminate Habs | exact Hb' ]);
          pose proof (@a_wf_aenv_binds_def_wf Θ α0 τ0 HwfΘ Hb') as Hwfτ;
          pose proof (a_wf_ptyp_ftv_dom Hwfτ) as Hftd;
          clear - Hftd HβΘ; fsetdec
        | apply msubst_pskl_ftv_avoid;
            [ intros pp Hpp; apply in_app_or in Hpp; destruct Hpp as [Hpp | Hpp];
                [ rewrite Forall_forall in Hβκ'; apply Hβκ'; exact Hpp
                | pose proof (a_inc_image_ftv_dom Hκ pp Hpp) as Hb;
                  clear - Hb HβΘ; fsetdec ]
            | exact HβPa ]
        | exact Hβψa ].
  - (* UnivGhostR (SK) : M = TC at sort SK, so [skmod] again forces P0 = □
       and the case closes exactly like Infer *)
    assert (HP0 : P0 = pskl_hole)
      by (pose proof (HmodSK eq_refl) as Hm; inversion Hm; reflexivity).
    subst P0.
    (* SolS-Vacuous generates nothing *)
    eapply solve_sub_ext_nil with (Pa := Pi);
      [ apply a_solve_sub__vacuous | exact HwfPi | cbn [app] ].
    eapply ad_partial_precise_psi_cong; [ exact Hpre | ].
    assert (HPsiae : Ψa [=] empty) by (clear - HΨs2 H; fsetdec).
    clear - HPsiae; fsetdec.
  - (* Arrow.  [skmod] forces P0 = P01→P02, the refinement splits, and the
       ρ-relation splits (or is a leaf).  The LEFT premise is a consistency
       judgment and goes to P6-Cv exactly as in Check; the RIGHT one is the
       IH.  Tags split by [arrow_tag_split]; the per-branch flow facts are
       P6-Cv's own arrow recipe ([ad_pat_sub_g_ftag_sub] /
       [ad_pat_consis_ftag_sub] + [uskl_rho_ftag_sub] + [d_tags_skl_ftag]). *)
    match goal with Hc : _ ⨟ Θ ⊢ₛᵃ R1 ∼ Q1 |- _ => rename Hc into Hcons end.
    match goal with Hu : Ψ [=] _ `union` _ |- _ => rename Hu into Hun end.
    assert (HP0 : exists P01 P02, P0 = pskl_arrow P01 P02 /\
                    (NM = a_sub_mode_sk -> a_sk_mode_compat M P02) /\
                    (NM = a_sub_mode_ty -> a_ty_mode_compat M P02)).
    { destruct NM.
      - pose proof (HmodTY eq_refl) as Hm; inversion Hm; subst.
        match goal with Hc : a_ty_mode_compat M ?Q0 |- _ =>
          exists P, Q0; repeat split;
            [ intro Hd; discriminate Hd | intros _; exact Hc ] end.
      - pose proof (HmodSK eq_refl) as Hm; inversion Hm; subst.
        match goal with Hc : a_sk_mode_compat M ?Q0 |- _ =>
          exists P, Q0; repeat split;
            [ intros _; exact Hc | intro Hd; discriminate Hd ] end. }
    destruct HP0 as (P01 & P02 & -> & HmodSK2 & HmodTY2).
    assert (HwfP01 : Θ0 ⨟ empty ⊢ₚₛᵃ P01) by (inversion HwfP0; assumption).
    assert (HwfP02 : Θ0 ⨟ empty ⊢ₚₛᵃ P02) by (inversion HwfP0; assumption).
    cbn [msubst_pskl pskl_to_bskl_inh] in Hrefine.
    inversion Hrefine; subst.
    match goal with
      Hr1 : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P01) ⊳ _,
      Hr2 : _ ⨟ _ ⊢ᵣᵃ pskl_to_bskl_inh (msubst_pskl κ P02) ⊳ _ |- _ =>
      rename Hr1 into Href1; rename Hr2 into Href2
    end.
    (* the two branches, once the guess is known to be an arrow.
       ⭐ THE TWO HALVES THREAD (2026-08-05): SS-Arrow runs its second premise
       at [Ξ1 ++ Θ0], because both halves may now GENERATE names and a guess
       avoids only what its OWN context mentions.  So [KEY] cannot hand the
       two solves back independently — it returns the MERGED package, exactly
       as P6-Cs's arrow merge does. *)
    assert (KEY : forall ψ1 ψ2 Ψρ1 Ψρ2,
      uskl_rho NM Θ Δρ Ψρ1 R1 ψ1 ->
      uskl_rho NM Θ Δρ Ψρ2 R2 ψ2 ->
      Ψρ [=] Ψρ1 `union` Ψρ2 ->
      a_tags_sort NM Ψt (uskl_arrow ψ1 ψ2) ->
      forall Pi1 Pi2 Ψi1 Ψi2 L0,
      Θ0 ⨟ empty ⊢ₚₛᵃ Pi1 -> Θ0 ⨟ empty ⊢ₚₛᵃ Pi2 ->
      (forall α, α `in` Δρ ->
         α `notin` pskl_shielded_ftv (msubst_pskl κ Pi1)) ->
      (forall α, α `in` Δρ ->
         α `notin` pskl_shielded_ftv (msubst_pskl κ Pi2)) ->
      Ψi [=] Ψi1 `union` Ψi2 ->
      Θ ⨟ Δ ⊢ (msubst_pskl κ Pi1) ⊑ᵖ[ Ψi1 ] ψ1 ->
      Θ ⨟ Δ ⊢ (msubst_pskl κ Pi2) ⊑ᵖ[ Ψi2 ] ψ2 ->
      exists Ξ1 Ξ2 Pa1 Pa2 κ1 κ2,
        Θ0 ⊢ₑ Pi1 ∼ P01 ⤳ Ξ1 ⨾ Pa1 /\
        (Ξ1 ++ Θ0) ⊢ₛ Pi2 ≼[ M ] P02 ⤳ Ξ2 ⨾ Pa2 /\
        all_flex_mono (Ξ2 ++ Ξ1) /\
        uniq (Ξ2 ++ Ξ1) /\
        keys (κ2 ++ κ1) = keys (Ξ2 ++ Ξ1) /\
        (forall α, α `in` dom (Ξ2 ++ Ξ1) -> α `notin` L0) /\
        Forall (fun p => a_wf_ptyp Θw (snd p) /\ mono_ptyp (snd p)) (κ2 ++ κ1) /\
        ((Ξ2 ++ Ξ1) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pa1 /\
        ((Ξ2 ++ Ξ1) ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pa2 /\
        Θ ⨟ Δ ⊢ (msubst_pskl ((κ2 ++ κ1) ++ κ) (pskl_arrow Pa1 Pa2))
          ⊑ᵖ[ Ψi `union` Ψa ] (uskl_arrow ψ1 ψ2)).
    { intros ψ1 ψ2 Ψρ1 Ψρ2 Hrho1 Hrho2 HΨρs Htags0 Pi1 Pi2 Ψi1 Ψi2 L0 HwfPi1 HwfPi2 Hsh1 Hsh2 HΨis Hpre1 Hpre2.
      destruct (a_tags_sort_arrow_inv Htags0)
        as (Ψt1 & Ψt2 & Htags1 & Htags2 & Htdisj & Htun).
      (* per-branch tag flow, exactly P6-Cv's arrow recipe *)
      assert (Hft1 : Ψ1 [<=] Ψρ1 `union` Ψt1).
      { pose proof (ad_pat_consis_ftag_sub Hcons) as Ha.
        pose proof (uskl_rho_ftag_sub Hrho1) as Hb.
        pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags1)) as Hc.
        clear - Ha Hb Hc; fsetdec. }
      assert (Hft2 : Ψ2 [<=] Ψρ2 `union` Ψt2).
      { pose proof (ad_pat_sub_g_ftag_sub Hsub) as Ha.
        pose proof (uskl_rho_ftag_sub Hrho2) as Hb.
        pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htags2)) as Hc.
        clear - Ha Hb Hc; fsetdec. }
      assert (Hi1 : Ψi1 [<=] Ψt1)
        by (eapply ad_partial_precise_tags_sub;
              [ exact HwfΘ | exact Hpre1
              | exact (a_tags_sort_d_tags Htags1) ]).
      assert (Hi2 : Ψi2 [<=] Ψt2)
        by (eapply ad_partial_precise_tags_sub;
              [ exact HwfΘ | exact Hpre2
              | exact (a_tags_sort_d_tags Htags2) ]).
      destruct (arrow_tag_split Htun Htdisj HΨis Hi1 Hi2 Htageq)
        as (Hsp1 & Hsp2).
      (* LEFT: the consistency premise goes to P6-Cv, AT [Θw] *)
      destruct (@a_solve_eq_complete_var_at NM Θ0 Θ Θw κ Δ Δρ Ψρ1 Ψt1 Ψi1
                  (Ψa ∩ Ψt1) Ψ1 R1 ψ1 Q1 Pi1 P01
                  HwfΘ HwfΘ0 HwfΘw Hmon Hnr HwfPi1 HwfP01 Hκ Hκw Hrho1 Htags1
                  ltac:(clear - Hsp1; fsetdec)
                  ltac:(clear - Hinter HΨρs Htun; fsetdec)
                  Hrhof Hdelta Hsh1 Hdfresh
                  Hpre1
                  ltac:(clear - Hft1 HΨs1 Hinter Htun Htdisj Hun HΨρs; fsetdec)
                  ltac:(clear - HΨs2 Hun Htun Hft2 Hinter HΨρs Htdisj; fsetdec)
                  Hcons Href1 (union L0 (ftvar_in_aenv Θ0))
                  ltac:(clear; fsetdec))
        as (Ξ1 & Pa1 & κ1 & Hs1 & Hfm1 & Hu1 & Hk1 & Hfr1 & HF1 & Hp1).
      (* the LEFT branch's [Θ0 ⊢ P_a1] — at [Ξ1 ++ Θ0]: the EQ half never
         leaks, so its wf preservation is still a real property *)
      assert (Hw1 : (Ξ1 ++ Θ0) ⨟ empty ⊢ₚₛᵃ Pa1)
        by (eapply a_solve_eq_wf; [ exact Hs1 | exact HwfPi1 | exact HwfP01 ]).
      (* ⭐ EVERYTHING THE RIGHT BRANCH NEEDS AT [Ξ1 ++ Θ0].  The one fact
         doing the work is the Ξ scoping kit's master invariant: a generated
         name dodges everything the context MENTIONS. *)
      assert (Hfr1c : forall x, x `in` dom Ξ1 -> x `notin` ftvar_in_aenv Θ0)
        by (intros x Hx; eapply a_solve_eq_generated_fresh;
              [ exact Hs1 | exact Hx ]).
      pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdf0.
      assert (Hd1 : dom κ1 [=] dom Ξ1) by (apply keys_eq_dom; exact Hk1).
      assert (HwfΞ1 : a_wf_aenv (Ξ1 ++ Θ0)).
      { apply a_wf_aenv_flex_prefix; [ exact Hfm1 | | exact HwfΘ0 ].
        assert (Hdd : dom Ξ1 ∩ dom Θ0 [<=] empty).
        { intros x Hx.
          assert (Hx1 : x `in` dom Ξ1) by (clear - Hx; fsetdec).
          assert (Hx2 : x `in` dom Θ0) by (clear - Hx; fsetdec).
          pose proof (Hfr1c x Hx1) as Hf. exfalso; clear - Hf Hdf0 Hx2; fsetdec. }
        apply uniq_app_4;
          [ exact Hu1 | eapply a_wf_aenv_uniq_local; exact HwfΘ0 | exact Hdd ]. }
      assert (HF1Θ : Forall (fun p => a_wf_ptyp Θ (snd p) /\ mono_ptyp (snd p)) κ1)
        by (eapply forall_wf_mono_weaken; [ exact Hmon | exact HF1 ]).
      assert (Hκ1 : (κ1 ++ κ) ∷ (Ξ1 ++ Θ0) ⊑ Θ)
        by (apply a_inc_flex_prefix_build;
              [ exact Hfm1 | exact Hk1 | exact HF1Θ | exact Hκ ]).
      pose proof (forall_wf_mono_images_dom HF1) as HF1d.
      assert (Hκw1 : forall α0, a_flex_tvar (Ξ1 ++ Θ0) α0 ->
                ftvar_in_ptyp (msubst_lookup (κ1 ++ κ) α0) [<=] dom Θw).
      { intros α0 Hf. apply msubst_lookup_ftv_app; [ exact HF1d | ].
        intros Hn1. apply Hκw.
        assert (Hns : α0 `notin` dom Ξ1) by (clear - Hn1 Hd1; fsetdec).
        destruct Hf as [Hb | (τ0 & Hb)]; [ left | right; exists τ0 ];
          (apply binds_app_1 in Hb; destruct Hb as [Hb | Hb];
           [ exfalso; apply binds_In in Hb; clear - Hb Hns; fsetdec
           | exact Hb ]). }
      (* the LEFT block misses Pi2 and P02 (both Θ0-scoped), so prefixing κ1
         moves neither the precision nor the refinement premise *)
      assert (Htr2 : msubst_pskl (κ1 ++ κ) Pi2 = msubst_pskl κ Pi2).
      { apply msubst_pskl_prepend_fresh. intros α0 Hα0.
        assert (Hin : α0 `in` dom Ξ1) by (clear - Hα0 Hd1; fsetdec).
        pose proof (Hfr1c α0 Hin) as Hf.
        pose proof (a_wf_pskl_ftv_dom HwfPi2) as Hfd.
        clear - Hf Hfd Hdf0; fsetdec. }
      assert (Htr0 : msubst_pskl (κ1 ++ κ) P02 = msubst_pskl κ P02).
      { apply msubst_pskl_prepend_fresh. intros α0 Hα0.
        assert (Hin : α0 `in` dom Ξ1) by (clear - Hα0 Hd1; fsetdec).
        pose proof (Hfr1c α0 Hin) as Hf.
        pose proof (a_wf_pskl_ftv_dom HwfP02) as Hfd.
        clear - Hf Hfd Hdf0; fsetdec. }
      assert (HΔρΘ0 : Δρ [<=] dom Θ0).
      { intros α0 Hα0. destruct (Hrhof α0 Hα0) as (Hb & _ & _).
        apply binds_In with (a := abind_tvar).
        eapply a_inc_binds_tvar_rev; [ exact Hκ | exact Hb ]. }
      assert (Hrhof1 : rho_fresh Δρ Θ (κ1 ++ κ)).
      { intros α0 Hα0. destruct (Hrhof α0 Hα0) as (Hb & Him & Hdf).
        repeat split; [ exact Hb | | exact Hdf ].
        intros p Hp0. apply in_app_or in Hp0; destruct Hp0 as [Hp0 | Hp0];
          [ pose proof (HF1d p Hp0) as Hbd; clear - Hbd HΔρw Hα0; fsetdec
          | apply Him; exact Hp0 ]. }
      (* RIGHT: the subtyping premise goes to the IH, at [Ξ1 ++ Θ0] under
         [κ1 ++ κ] — the LEFT SOLVE's block is in scope for it *)
      destruct (IHHsub Θ (Ξ1 ++ Θ0) (κ1 ++ κ) Δ Δρ Ψρ2 Ψt2 Ψi2 (Ψa ∩ Ψt2)
                  ψ2 Pi2 P02
                  HwfΘ HwfΞ1 Hmon Hnr Hκw1 HΔρw
                  ltac:(eapply a_wf_pskl_weaken;
                        [ intros x b Hb; apply binds_app_3; exact Hb
                        | exact HwfPi2 ])
                  ltac:(eapply a_wf_pskl_weaken;
                        [ intros x b Hb; apply binds_app_3; exact Hb
                        | exact HwfP02 ])
                  HmodSK2 HmodTY2 Hκ1 Hrho2 Htags2
                  ltac:(inversion HwfSub; assumption)
                  ltac:(clear - Hsp2; fsetdec)
                  ltac:(clear - Hinter HΨρs Htun; fsetdec)
                  Hrhof1 Hdelta
                  ltac:(rewrite Htr2; exact Hsh2)
                  Hdfresh
                  ltac:(rewrite Htr2; exact Hpre2)
                  ltac:(clear - Hft2 HΨs1 Hinter Htun Htdisj Hun HΨρs; fsetdec)
                  ltac:(clear - HΨs2 Hun Htun Hft1 Hinter HΨρs Htdisj; fsetdec)
                  Hext
                  ltac:(rewrite Htr0; exact Href2)
                  (union L0 (union (dom Ξ1) (ftvar_in_aenv Θ0)))
                  ltac:(repeat rewrite ftvar_in_aenv_app;
                        pose proof (all_flex_mono_ftvar_in_aenv Hfm1) as Hs1f;
                        clear - Hs1f; fsetdec))
        as (Ξ2 & Pa2 & κ2 & Hs2 & Hfm2 & Hu2 & Hk2 & Hfr2 & HF2 & Hw2 & Hp2).
      (* --- the merge --- *)
      assert (Hd2 : dom κ2 [=] dom Ξ2) by (apply keys_eq_dom; exact Hk2).
      assert (H21 : forall x, x `in` dom Ξ2 -> x `notin` dom Ξ1)
        by (intros x Hx; pose proof (Hfr2 x Hx) as Hf; clear - Hf; fsetdec).
      exists Ξ1, Ξ2, Pa1, Pa2, κ1, κ2.
      split; [ exact Hs1 | ]. split; [ exact Hs2 | ].
      split; [ apply all_flex_mono_app; assumption | ].
      split; [ apply uniq_app_4;
                 [ exact Hu2 | exact Hu1
                 | intros x Hx;
                   assert (Hx2 : x `in` dom Ξ2) by (clear - Hx; fsetdec);
                   assert (Hx1 : x `in` dom Ξ1) by (clear - Hx; fsetdec);
                   pose proof (H21 x Hx2) as Hf; exfalso; clear - Hf Hx1; fsetdec ]
             | ].
      split; [ rewrite !keys_app; rewrite Hk1, Hk2; reflexivity | ].
      split; [ intros α0 Hα0; rewrite dom_app in Hα0;
               apply union_1 in Hα0; destruct Hα0 as [Hα0 | Hα0];
                 [ pose proof (Hfr2 α0 Hα0) as Hf; clear - Hf; fsetdec
                 | pose proof (Hfr1 α0 Hα0) as Hf; clear - Hf; fsetdec ] | ].
      split; [ apply Forall_app; split; assumption | ].
      split; [ (* wf Pa1 at the merged block *)
               eapply a_wf_pskl_weaken; [ | exact Hw1 ];
               intros x b Hb; rewrite (aenv_app_assoc Ξ2 Ξ1 Θ0);
               apply binds_app_3; exact Hb | ].
      split; [ rewrite (aenv_app_assoc Ξ2 Ξ1 Θ0); exact Hw2 | ].
      (* the precision.  [Pa2]'s is [Hp2] modulo associativity; [Pa1]'s needs
         the RIGHT block peeled off, and it peels because [Ξ2] was generated
         at [Ξ1 ++ Θ0], which MENTIONS every variable of [Pa1]. *)
      assert (Htr1 : msubst_pskl ((κ2 ++ κ1) ++ κ) Pa1
                     = msubst_pskl (κ1 ++ κ) Pa1).
      { rewrite (list_app_assoc κ2 κ1 κ).
        apply msubst_pskl_prepend_fresh. intros α0 Hα0.
        assert (Hin : α0 `in` dom Ξ2) by (clear - Hα0 Hd2; fsetdec).
        assert (Hf : α0 `notin` ftvar_in_aenv (Ξ1 ++ Θ0))
          by (eapply a_solve_sub_generated_fresh; [ exact Hs2 | exact Hin ]).
        pose proof (a_wf_pskl_ftv_dom Hw1) as Hfd.
        pose proof (dom_subset_ftvar_in_aenv (Ξ1 ++ Θ0)) as Hds.
        clear - Hf Hfd Hds; fsetdec. }
      cbn [msubst_pskl].
      eapply ad_ppre__arrow;
        [ rewrite Htr1; exact Hp1
        | rewrite (list_app_assoc κ2 κ1 κ); exact Hp2
        | clear - HΨis Htun Htdisj Htageq; fsetdec ]. }
    (* now the guess: a ρ-leaf, or an arrow (reflexively or by congruence) *)
    assert (Htsk : is_tskl ψa) by (inversion Htags; assumption).
    destruct (uskl_rho_arrow_l_inv Hrho) as [[Heq HΨρe] | [Hleaf | Hcong]];
      [ | (* ρ-leaf *)
        destruct Hleaf as (α0 & Ψ'' & Heq & HαΔρ & _ & _ & _); subst ψa;
        eapply a_solve_sub_complete_rho_var;
          solve [ exact HwfΘ | exact Htags | clear - Htageq; fsetdec
                | exact Hrhof | exact Hdelta | exact HαΔρ | exact Hapart
                | exact HwfPi | exact Hpre ]
      | ].
    (* REFL: ρ is the identity here, so the guess IS the subject *)
    { subst ψa.
      assert (Hlc1 : lc_uskl R1) by (inversion Htsk; apply is_tskl_lc; assumption).
      assert (Hlc2 : lc_uskl R2) by (inversion Htsk; apply is_tskl_lc; assumption).
      assert (Hrho1 : uskl_rho NM Θ Δρ empty R1 R1)
        by (apply urho__refl; [ exact Hlc1 | clear; fsetdec ]).
      assert (Hrho2 : uskl_rho NM Θ Δρ empty R2 R2)
        by (apply urho__refl; [ exact Hlc2 | clear; fsetdec ]).
      pose proof (KEY R1 R2 empty empty Hrho1 Hrho2
                    ltac:(clear - HΨρe; fsetdec) Htags ) as KEY'.
      eapply arrow_grid;
        [ exact HwfΘ | exact Hκ | exact Htags | exact Htageq
        | exact HwfP01 | exact HwfP02 | exact KEY'
        | exact HwfPi | exact Hapart | exact Hpre ]. }
    (* CONGRUENCE *)
    { destruct Hcong as (ψ1 & ψ2 & Ψρ1 & Ψρ2 & Heq & Hrho1 & Hrho2 & HΨρs);
        subst ψa.
      pose proof (KEY ψ1 ψ2 Ψρ1 Ψρ2 Hrho1 Hrho2 HΨρs Htags ) as KEY'.
      eapply arrow_grid;
        [ exact HwfΘ | exact Hκ | exact Htags | exact Htageq
        | exact HwfP01 | exact HwfP02 | exact KEY'
        | exact HwfPi | exact Hapart | exact Hpre ]. }
  - (* ForallL, tagged (subtyping-proofs.tex:2086).  ψa = ∀^ε β.ψ'; the
       instantiation the rule performs is ABSORBED INTO ρ as the paper's
       ρ_b = ρ ∘ [ψ_b/β] ([uskl_rho_subst]), so the recursive call runs at
       Δρ,β — β is the one variable ρ_b replaces and ρ did not, and it is
       the SAME β the precision premise pairs Pi's binder with. *)
    match goal with
      Hd : ad_pat_sub_g _ _ _ _ _ (open_uskl_wrt_uskl R ψ) _ |- _ =>
      rename Hd into Hprem end.
    match goal with Ht : a_tags_sort _ _ ψ |- _ => rename Ht into Htagsg end.
    match goal with Hw : _ ⨟ _ ⊢ₚₛᵃ ⌊ ψ ⌋ˢ |- _ => rename Hw into Hwfg0 end.
    assert (Hwfg : Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψ ⌋ˢ)
      by (eapply a_wf_pskl_weaken; [ exact Hext | exact Hwfg0 ]).
    match goal with
      Hf : _ ∩ (ftag_in_uskl (uskl_all_etag _ R)) [=] empty |- _ =>
      rename Hf into Hgfresh end.
    assert (Hlcg : lc_uskl ψ)
      by (apply is_tskl_lc; inversion Htagsg; assumption).
    (* the ∀^ε-shaped rows share a body; state it once, then dispatch *)
    assert (MAIN : forall L0 ψsrc,
      (forall α, α `notin` L0 ->
         uskl_rho NM Θ Δρ Ψρ (open_uskl_wrt_uskl R (uskl_var_f α))
                             (open_uskl_wrt_uskl ψsrc (uskl_var_f α))) ->
      a_tags_sort NM Ψt (uskl_all_etag ε ψsrc) ->
      Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_all_etag ε ψsrc) ->
      solve_sub_ext Θ0 Θw M Pi P0 Lav
        (fun κ' Pa =>
           Θ ⨟ Δ ⊢ (msubst_pskl (κ' ++ κ) Pa)
             ⊑ᵖ[ Ψi `union` Ψa ] (uskl_all_etag ε ψsrc))).
    { intros L0 ψsrc Hfam Htags0 Hpre0.
      destruct (a_tags_sort_all_etag_inv Htags0)
        as (Lt & Ψt0 & Htbody & Hεt0 & HΨteq).
      (* --- ε is solved by the INPUT, never by the premise --- *)
      assert (HftagR : ftag_in_uskl ψsrc [<=] ftag_in_uskl R).
      { pick fresh α1 for L0.
        pose proof (uskl_rho_ftag_target_sub
                      (Hfam α1 ltac:(clear - Fr; solve_notin))) as Hb.
        rewrite (ftag_in_uskl_open_var R α1) in Hb.
        rewrite (ftag_in_uskl_open_var ψsrc α1) in Hb. exact Hb. }
      assert (HRtag : ftag_in_uskl R [<=] Ψρ `union` ftag_in_uskl ψsrc).
      { pick fresh α1 for L0.
        pose proof (uskl_rho_ftag_sub
                      (Hfam α1 ltac:(clear - Fr; solve_notin))) as Hb.
        rewrite (ftag_in_uskl_open_var R α1) in Hb.
        rewrite (ftag_in_uskl_open_var ψsrc α1) in Hb. exact Hb. }
      assert (HΨt0eq : Ψt0 [=] ftag_in_uskl ψsrc).
      { pick fresh α1 for Lt.
        pose proof (d_tags_skl_ftag (a_tags_sort_d_tags
                      (Htbody α1 ltac:(clear - Fr; solve_notin)))) as Hb.
        rewrite (ftag_in_uskl_open_var ψsrc α1) in Hb. exact Hb. }
      assert (HεΨt : ε `in` Ψt) by (clear - HΨteq; fsetdec).
      assert (HεR : ε `notin` ftag_in_uskl R)
        by (clear - HRtag Hinter HεΨt HΨt0eq Hεt0; fsetdec).
      (* the guess's own tags are Ψ', which the rule keeps off ∀^ε R, and the
         premise's solved tags are bounded by ITS subject's — so ε ∉ Ψsub *)
      assert (HεΨsub : ε `notin` Ψ).
      { pose proof (ad_pat_sub_g_ftag_sub Hprem) as Hb.
        pose proof (ftag_in_uskl_open_upper R ψ) as Hup.
        pose proof (d_tags_skl_ftag (a_tags_sort_d_tags Htagsg)) as Hg.
        cbn [ftag_in_uskl] in Hgfresh.
        clear - Hb Hup Hg Hgfresh HεR; fsetdec. }
      assert (HεΨi : ε `in` Ψi)
        by (clear - Htageq HΨteq HεΨsub HΨs2; fsetdec).
      (* Pi's shape is pinned by the precision premise: only a ∀ survives —
         every other row would have to solve ε, and ε is already in Ψi *)
      destruct Pi as [ | nPi | β0 | Pi1 Pi2 | Pi0 | | Pi0 ];
        cbn [msubst_pskl] in Hpre0.
      - (* ⟨⟩ *) inversion Hpre0.
      - (* a bound variable is not well-formed *) inversion HwfPi.
      - (* a variable : its κ-image is a MONOTYPE, whose target is tag-free *)
        exfalso.
        assert (HΨte : Ψt [=] empty)
          by (eapply ad_ppre_mono_subject_target_tags_empty;
                [ exact HwfΘ | exact Hpre0 | reflexivity
                | eapply a_inc_lookup_mono; exact Hκ
                | exact (a_tags_sort_d_tags Htags0) ]).
        clear - HΨte HεΨt; fsetdec.
      - (* an arrow *) inversion Hpre0.
      - (* Pi = ∀.Pi0 : THE ROW *)
        assert (Hex : exists Lp Ψi0,
                  (forall α, α `notin` Lp ->
                     Θ ⨟ (add α Δ)
                       ⊢ (open_pskl_wrt_pskl (msubst_pskl κ Pi0)
                            (pskl_var_f α))
                       ⊑ᵖ[ Ψi0 ] (open_uskl_wrt_uskl ψsrc (uskl_var_f α)))
                  /\ Ψi [=] add ε Ψi0).
        { inversion Hpre0; subst; eexists; eexists; split; eassumption. }
        destruct Hex as (Lp & Ψi0 & Hpbody & HΨieq).
        assert (Hexw : exists Lw,
                  forall α, α `notin` Lw ->
                    Θ0 ⨟ (add α empty)
                      ⊢ₚₛᵃ (open_pskl_wrt_pskl Pi0 (pskl_var_f α))).
        { inversion HwfPi; subst; eexists; eassumption. }
        destruct Hexw as (Lw & Hwbody).
        (* ⭐ [ftvar_in_aenv Θ0], not just [dom Θ0]: SolS-ForallL's freshness
           side condition moved there with the repair (hand-off §2(3)). *)
        pick fresh β for
          (L0 `union` Lt `union` Lp `union` Lw `union` dom Θ `union` dom Θ0
             `union` ftvar_in_aenv Θ0
             `union` dom κ `union` Δ `union` Δρ `union` def_ftv Θ
             `union` ftvar_in_uskl ψsrc `union` ftvar_in_uskl R
             `union` ftvar_in_uskl ψ `union` ftvar_in_pskl Pi0
             `union` ftvar_in_pskl P0).
        assert (HβΘ : β `notin` dom Θ) by (clear - Fr; solve_notin).
        assert (HβΘ0 : β `notin` dom Θ0) by (clear - Fr; solve_notin).
        assert (Hβκ : β `notin` dom κ) by (clear - Fr; solve_notin).
        assert (HβΔ : β `notin` Δ) by (clear - Fr; solve_notin).
        assert (HβΔρ : β `notin` Δρ) by (clear - Fr; solve_notin).
        assert (HβR : β `notin` ftvar_in_uskl R) by (clear - Fr; solve_notin).
        (* --- ρ_b = ρ ∘ [ψ/β] --- *)
        destruct (@uskl_rho_subst NM Θ Δρ Ψρ
                    (open_uskl_wrt_uskl R (uskl_var_f β))
                    (open_uskl_wrt_uskl ψsrc (uskl_var_f β))
                    (Hfam β ltac:(clear - Fr; solve_notin))
                    β ψ Ψ' Htagsg Hwfg Hlcg HβΘ HβΔρ)
          as (Ψρ' & HΨρ'sub & HΨρ'mono & HΨρ'occ & Hrho').
        rewrite <- (@subst_bskl_in_uskl_intro β R ψ) in Hrho';
          [ | exact HβR ].
        (* the instantiation's tags are ρ-dirt — unless the binder is UNUSED,
           in which case the instantiation solves nothing at all *)
        assert (HΨ'sub : Ψ' [<=] Ψρ').
        { destruct (AtomSetProperties.In_dec β
                      (ftvar_in_uskl (open_uskl_wrt_uskl ψsrc (uskl_var_f β))))
            as [Hin | Hni]; [ exact (HΨρ'occ Hin) | ].
          assert (HβRo : β `notin` ftvar_in_uskl
                           (open_uskl_wrt_uskl R (uskl_var_f β))).
          { pose proof (uskl_rho_ftv_subject_bound
                          (Hfam β ltac:(clear - Fr; solve_notin))) as Hb.
            clear - Hb Hni HβΘ; fsetdec. }
          assert (Heqo : open_uskl_wrt_uskl R ψ
                         = open_uskl_wrt_uskl R (uskl_var_f β)).
          { rewrite (@subst_bskl_in_uskl_intro β R ψ); [ | exact HβR ].
            apply subst_bskl_in_uskl_fresh_eq; exact HβRo. }
          pose proof (ad_pat_sub_g_ftag_sub Hprem) as Hb.
          rewrite Heqo in Hb. rewrite (ftag_in_uskl_open_var R β) in Hb.
          cbn [ftag_in_uskl] in Hgfresh.
          clear - Hb Hgfresh; fsetdec. }
        (* --- the recursive call's premises at Θ0,β / Θ,β --- *)
        assert (Hwfβ : a_wf_aenv ((β ~ abind_tvar) ++ Θ))
          by (apply a_wf_aenv__tvar; assumption).
        assert (Hwfβ0 : a_wf_aenv ((β ~ abind_tvar) ++ Θ0))
          by (apply a_wf_aenv__tvar; assumption).
        assert (Hweak0 : forall (x : atom) (b : abind),
                  binds x b Θ0 -> binds x b ((β ~ abind_tvar) ++ Θ0))
          by (intros x b Hb; apply binds_app_3; exact Hb).
        assert (Hweak : forall (x : atom) (b : abind),
                  binds x b Θ -> binds x b ((β ~ abind_tvar) ++ Θ))
          by (intros x b Hb; apply binds_app_3; exact Hb).
        assert (HwfPiβ : ((β ~ abind_tvar) ++ Θ0) ⨟ empty
                  ⊢ₚₛᵃ (open_pskl_wrt_pskl Pi0 (pskl_var_f β))).
        { eapply a_wf_pskl_delta_to_tvar_mid
            with (α1 := β) (Θ1 := nil) (Θ2 := Θ0) (Δ' := empty);
            [ apply (Hwbody β ltac:(clear - Fr; solve_notin))
            | reflexivity | clear; fsetdec ]. }
        assert (HwfP0β : ((β ~ abind_tvar) ++ Θ0) ⨟ empty ⊢ₚₛᵃ P0)
          by (eapply a_wf_pskl_weaken; [ exact Hweak0 | exact HwfP0 ]).
        assert (Hκβ : κ ∷ ((β ~ abind_tvar) ++ Θ0) ⊑ ((β ~ abind_tvar) ++ Θ))
          by (apply a_inc_cons_tvar; exact Hκ).
        assert (Hrhoβ : uskl_rho NM ((β ~ abind_tvar) ++ Θ) (add β Δρ) Ψρ'
                  (open_uskl_wrt_uskl R ψ)
                  (open_uskl_wrt_uskl ψsrc (uskl_var_f β)))
          by (eapply uskl_rho_weaken; [ exact Hrho' | exact Hweak ]).
        assert (Htagsβ : a_tags_sort NM Ψt0
                  (open_uskl_wrt_uskl ψsrc (uskl_var_f β)))
          by (apply Htbody; clear - Fr; solve_notin).
        assert (HwfSubβ : ((β ~ abind_tvar) ++ Θ) ⨟ empty
                  ⊢ₚₛᵃ ⌊ open_uskl_wrt_uskl R ψ ⌋ˢ).
        { assert (Hexs : exists Lb, forall α, α `notin` Lb ->
                    Θ ⨟ (add α empty) ⊢ₚₛᵃ
                      (open_pskl_wrt_pskl ⌊ R ⌋ˢ (pskl_var_f α))).
          { cbn [uskl_to_pskl] in HwfSub;
            inversion HwfSub; subst; eexists; eassumption. }
          destruct Hexs as (Lb & Hbody).
          rewrite uskl_to_pskl_open_gen.
          eapply a_wf_pskl_weaken; [ exact Hweak | ].
          eapply a_wf_pskl_open; [ exact Hbody | exact Hwfg ]. }
        assert (HΨi0sub : Ψi0 [<=] Ψt0)
          by (eapply ad_partial_precise_tags_sub;
                [ exact HwfΘ | apply (Hpbody β ltac:(clear - Fr; solve_notin))
                | exact (a_tags_sort_d_tags Htagsβ) ]).
        assert (Htageqβ : Ψi0 `union` Ψa [=] Ψt0)
          by (clear - Htageq HΨteq HΨieq HΨi0sub Hεt0 HεΨsub HΨs2; fsetdec).
        assert (Hinterβ : Ψρ' ∩ Ψt0 [=] empty).
        { cbn [ftag_in_uskl] in Hgfresh.
          clear - HΨρ'sub Hinter HΨteq HΨt0eq HftagR Hgfresh; fsetdec. }
        assert (Hrhofβ : rho_fresh (add β Δρ) ((β ~ abind_tvar) ++ Θ) κ).
        { intros α0 Hα0.
          destruct (AtomSetProperties.In_dec α0 Δρ) as [Hin | Hni].
          - destruct (Hrhof α0 Hin) as (Hb & Him & Hdf).
            repeat split; [ apply binds_app_3; exact Hb | exact Him | ].
            intros α3 τ3 Hb3. eapply Hdf.
            destruct (binds_cons_1 _ _ _ _ _ _ Hb3) as [[_ Habs] | Hb'];
              [ discriminate Habs | exact Hb' ].
          - assert (Heqβ : α0 = β) by (clear - Hα0 Hni; fsetdec); subst α0.
            repeat split.
            + unfold binds; left; reflexivity.
            + intros pp Hpp.
              pose proof (a_inc_image_ftv_dom Hκ pp Hpp) as Hb.
              clear - Hb HβΘ; fsetdec.
            + intros α3 τ3 Hb3.
              assert (Hb' : binds α3 (abind_flex_mono_def τ3) Θ)
                by (destruct (binds_cons_1 _ _ _ _ _ _ Hb3)
                      as [[_ Habs] | Hb']; [ discriminate Habs | exact Hb' ]).
              pose proof (a_wf_ptyp_ftv_dom
                            (@a_wf_aenv_binds_def_wf Θ α3 τ3 HwfΘ Hb')) as Hd.
              clear - Hd HβΘ; fsetdec. }
        assert (Hdeltaβ : add β Δρ [<=] add β Δ)
          by (clear - Hdelta; fsetdec).
        assert (Hapartβ : forall α0, α0 `in` (add β Δρ) ->
                  α0 `notin` pskl_shielded_ftv
                    (msubst_pskl κ (open_pskl_wrt_pskl Pi0 (pskl_var_f β)))).
        { intros α0 Hα0.
          destruct (AtomSetProperties.In_dec α0 Δρ) as [Hin | Hni].
          - rewrite (@msubst_pskl_open Θ0 κ Θ Pi0 β Hκ Hβκ).
            pose proof (Hapart α0 Hin) as Hs.
            cbn [msubst_pskl pskl_shielded_ftv] in Hs.
            pose proof (pskl_shielded_ftv_open_upper (msubst_pskl κ Pi0)
                          (pskl_var_f β)) as Hup.
            cbn [ftvar_in_pskl] in Hup.
            assert (Hne : α0 <> β) by (clear - Hin HβΔρ; fsetdec).
            clear - Hs Hup Hne; fsetdec.
          - (* the ∀◇-body discipline: a well-formed skeleton's SHIELDED
               variables all live in the aenv, never in Δ — so the freshly
               opened binder is not one of them (DESIGN §7) *)
            assert (Heqβ : α0 = β) by (clear - Hα0 Hni; fsetdec); subst α0.
            apply msubst_pskl_shielded_avoid.
            + intros pp Hpp.
              pose proof (a_inc_image_ftv_dom Hκ pp Hpp) as Hb.
              clear - Hb HβΘ; fsetdec.
            + pose proof (a_wf_pskl_shielded_dom
                            (Hwbody β ltac:(clear - Fr; solve_notin))) as Hd.
              clear - Hd HβΘ0; fsetdec. }
        assert (Hdfreshβ : delta_def_fresh (add β Δ) ((β ~ abind_tvar) ++ Θ)).
        { intros β0 α3 τ3 Hβ0 Hb.
          assert (Hb' : binds α3 (abind_flex_mono_def τ3) Θ)
            by (destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Habs] | Hb'];
                  [ discriminate Habs | exact Hb' ]).
          destruct (AtomSetProperties.In_dec β0 Δ) as [Hin | Hni];
            [ eapply Hdfresh; [ exact Hin | exact Hb' ] | ].
          assert (Heqβ : β0 = β) by (clear - Hβ0 Hni; fsetdec); subst β0.
          pose proof (a_wf_ptyp_ftv_dom
                        (@a_wf_aenv_binds_def_wf Θ α3 τ3 HwfΘ Hb')) as Hd.
          clear - Hd HβΘ; fsetdec. }
        assert (Hpreβ : ((β ~ abind_tvar) ++ Θ) ⨟ (add β Δ)
                  ⊢ (msubst_pskl κ (open_pskl_wrt_pskl Pi0 (pskl_var_f β)))
                  ⊑ᵖ[ Ψi0 ] (open_uskl_wrt_uskl ψsrc (uskl_var_f β))).
        { rewrite (@msubst_pskl_open Θ0 κ Θ Pi0 β Hκ Hβκ).
          eapply ad_partial_precise_weaken;
            [ apply (Hpbody β ltac:(clear - Fr; solve_notin)) | exact Hweak ]. }
        assert (Hrefβ : ((β ~ abind_tvar) ++ Θ) ⨟ empty ⊢ᵣᵃ
                  (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q)
          by (eapply ad_refine_syn_weaken; [ exact Hrefine | exact Hweak ]).
        (* the Θw pack under the binder: [Θw] itself does NOT move, and the
           only condition Δρ's growth touches is [HΔρw] — β is a rigid picked
           fresh for Θ ⊇ Θw *)
        assert (HβΘw : β `notin` dom Θw)
          by (pose proof (@aenv_binds_dom_sub Θw Θ Hmon) as Hdw;
              clear - Hdw HβΘ; fsetdec).
        assert (Hmonβ : forall x b, binds x b Θw ->
                  binds x b ((β ~ abind_tvar) ++ Θ))
          by (intros x b Hb; apply binds_app_3; apply Hmon; exact Hb).
        assert (Hnrβ : forall x b, binds x b ((β ~ abind_tvar) ++ Θ) ->
                  binds x b Θw \/ b = abind_tvar).
        { intros x b Hb.
          destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[_ Heq] | Hb'];
            [ right; exact Heq | exact (Hnr _ _ Hb') ]. }
        assert (Hκwβ : forall α0, a_flex_tvar ((β ~ abind_tvar) ++ Θ0) α0 ->
                  ftvar_in_ptyp (msubst_lookup κ α0) [<=] dom Θw)
          by (intros α0 Hf; apply Hκw; eapply a_flex_tvar_strip_tvar; exact Hf).
        assert (HΔρwβ : (add β Δρ) ∩ dom Θw [=] empty)
          by (clear - HΔρw HβΘw; fsetdec).
        assert (HLavβ : ftvar_in_aenv ((β ~ abind_tvar) ++ Θ0) [<=] add β Lav)
          by (rewrite ftvar_in_aenv_cons_tvar; clear - HLav; fsetdec).
        edestruct (IHHsub ((β ~ abind_tvar) ++ Θ) ((β ~ abind_tvar) ++ Θ0) κ
                     (add β Δ) (add β Δρ) Ψρ' Ψt0 Ψi0 Ψa
                     (open_uskl_wrt_uskl ψsrc (uskl_var_f β))
                     (open_pskl_wrt_pskl Pi0 (pskl_var_f β)) P0
                     Hwfβ Hwfβ0 Hmonβ Hnrβ Hκwβ HΔρwβ
                     HwfPiβ HwfP0β HmodSK HmodTY Hκβ Hrhoβ
                     Htagsβ HwfSubβ Htageqβ Hinterβ Hrhofβ Hdeltaβ Hapartβ
                     Hdfreshβ Hpreβ
                     ltac:(clear - HΨs1 HΨρ'mono HΨ'sub; fsetdec)
                     ltac:(clear - HΨs2; fsetdec)
                     ltac:(intros x b Hb; apply binds_app_3; apply Hext;
                           exact Hb)
                     Hrefβ (add β Lav) HLavβ)
          as (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & HwfPaβ & Hp).
        assert (HβΞ : β `notin` dom Ξ)
          by (intro Hc; pose proof (Hfr β Hc) as Hf; clear - Hf; fsetdec).
        assert (Hdκ : dom κ' [=] dom Ξ) by (apply keys_eq_dom; exact Hk).
        (* ⭐ the SOLVE BLOCK's payloads dodge β because they are well-formed
           in the FIXED [Θw], which predates the binder *)
        assert (Hβκ' : Forall (fun p => β `notin` ftvar_in_ptyp (snd p)) κ').
        { rewrite Forall_forall. intros p Hp0.
          pose proof (forall_wf_mono_images_dom HF p Hp0) as Hb.
          clear - Hb HβΘw; fsetdec. }
        (* --- re-abstract β --- *)
        remember (close_pskl_wrt_pskl β Pa) as Pb eqn:HeqPb.
        assert (HopenPb : open_pskl_wrt_pskl Pb (pskl_var_f β) = Pa)
          by (subst Pb; apply open_pskl_wrt_pskl_close_pskl_wrt_pskl).
        assert (HβPb : β `notin` ftvar_in_pskl Pb)
          by (subst Pb; rewrite ftvar_in_pskl_close_pskl_wrt_pskl;
              clear; fsetdec).
        (* [HeqPb] is KEPT now: SolS-ForallL closes its output itself, so
           the reconstruction needs [Pb = close β Pa] literally. *)
        assert (HβPbκ : β `notin` ftvar_in_pskl (msubst_pskl (κ' ++ κ) Pb)).
        { apply msubst_pskl_ftv_avoid;
            [ intros pp Hpp; apply in_app_or in Hpp;
              destruct Hpp as [Hpp | Hpp];
                [ rewrite Forall_forall in Hβκ'; apply Hβκ'; exact Hpp
                | pose proof (a_inc_image_ftv_dom Hκ pp Hpp) as Hb;
                  clear - Hb HβΘ; fsetdec ]
            | exact HβPb ]. }
        (* --- the paper's [Θ0,β ⊢ P_a] ⟹ [Θ0 ⊢ ∀β.P_b].  The mech's Δ makes
           this a real step rather than the ∀ wf rule: a ∀◇ body is typed at
           the EMPTY Δ, so β may only move from the CONTEXT into Δ when the
           run left it UNSHIELDED — which it did, because the SUBJECT does
           ([a_wf_pskl_shielded_dom] on the Δ-form) and solving preserves it
           ([a_solve_sub_eq_unshielded]). --- *)
        assert (HshPiβ : β `notin` pskl_shielded_ftv
                           (open_pskl_wrt_pskl Pi0 (pskl_var_f β))).
        { pose proof (a_wf_pskl_shielded_dom
                        (Hwbody β ltac:(clear - Fr; solve_notin))) as Hsd.
          clear - Hsd HβΘ0; fsetdec. }
        assert (HshPa : β `notin` pskl_shielded_ftv Pa).
        { eapply (proj1 a_solve_sub_eq_unshielded);
            [ exact Hs
            | simpl; clear; fsetdec
            | exact HshPiβ
            | pose proof (a_wf_pskl_ftv_dom HwfP0) as Hfd;
              clear - Hfd HβΘ0; fsetdec ]. }
        assert (HwfPaΔ : (Ξ ++ Θ0) ⨟ (add β empty) ⊢ₚₛᵃ Pa)
          by (eapply (@a_wf_pskl_tvar_to_delta Ξ β Θ0);
                [ exact HwfPaβ | exact HshPa ]).
        exists Ξ, (pskl_all_syn Pb), κ'.
        split; [ | split; [ exact Hfm | split; [ exact Hu
                 | split; [ exact Hk | split; [ | split; [ exact HF
                 | split ] ] ] ] ] ].
        + (* SolS-ForallL, exists-fresh + CLOSE (DESIGN §4.3).  ⭐ Since the
             repair the rule runs its premise at [(β ~ tvar) ++ Θ0], so the
             IH's output IS the premise — the old [a_solve_sub_strengthen_tvar]
             step is gone — and it re-binds the output itself, so [Pb] is
             exactly the rule's [close β Pa]. *)
          rewrite HeqPb.
          apply a_solve_sub__forall_l with (β := β);
            [ clear - Fr; solve_notin | exact Hs ].
        + (* the block dodges the caller's avoid-set a fortiori *)
          intros α0 Hα0; pose proof (Hfr α0 Hα0) as Hf; clear - Hf; fsetdec.
        + (* wf: re-bind the Δ-form at the rule's own binder *)
          apply (@a_wf_pskl_all_of_one (Ξ ++ Θ0) empty Pb β);
            [ rewrite HopenPb; exact HwfPaΔ
            | rewrite dom_app; clear - HβΘ0 HβΞ; fsetdec | exact HβPb ].
        + (* precision: β lives in Δ, so it can leave the aenv
             ([ad_partial_precise_tvar_to_delta_mid]); then rename it into
             P-Forall's family *)
          assert (Hp' : Θ ⨟ (add β Δ) ⊢ (msubst_pskl (κ' ++ κ) Pa)
                    ⊑ᵖ[ Ψi0 `union` Ψa ]
                    (open_uskl_wrt_uskl ψsrc (uskl_var_f β)))
            by (eapply ad_partial_precise_tvar_to_delta_mid
                  with (β := β) (Θ1 := nil) (Θ2 := Θ);
                  [ exact Hp | reflexivity | clear; fsetdec | exact HβΘ
                  | clear; fsetdec ]).
          assert (Hκa : (κ' ++ κ) ∷ (Ξ ++ (β ~ abind_tvar) ++ Θ0)
                          ⊑ ((β ~ abind_tvar) ++ Θ))
            by (apply a_inc_flex_prefix_build;
                  [ exact Hfm | exact Hk
                  | eapply forall_wf_mono_weaken; [ exact Hmonβ | exact HF ]
                  | exact Hκβ ]).
          assert (Hβκa : β `notin` dom (κ' ++ κ))
            by (rewrite dom_app; clear - HβΞ Hβκ Hdκ; fsetdec).
          assert (Heqsub : msubst_pskl (κ' ++ κ) Pa
                    = open_pskl_wrt_pskl (msubst_pskl (κ' ++ κ) Pb)
                        (pskl_var_f β)).
          { rewrite <- HopenPb at 1.
            apply (@msubst_pskl_open (Ξ ++ (β ~ abind_tvar) ++ Θ0) (κ' ++ κ)
                     ((β ~ abind_tvar) ++ Θ) Pb β Hκa Hβκa). }
          rewrite Heqsub in Hp'.
          cbn [msubst_pskl].
          (* [Ψ0] must be PINNED: leaving it an evar sends the tag side
             condition's [fsetdec] into a non-terminating search *)
          eapply ad_ppre__forall
            with (L := dom Θ `union` Δ `union` singleton β
                        `union` ftvar_in_uskl ψsrc
                        `union` ftvar_in_pskl (msubst_pskl (κ' ++ κ) Pb))
                 (Ψ0 := Ψi0 `union` Ψa);
            [ | clear - HΨieq; fsetdec ].
          intros α Hα.
          (* split the pick-fresh union ONCE: a [fsetdec] that has to walk a
             six-way union under a [⊆] hypothesis does not terminate here *)
          assert (HαΘ : α `notin` dom Θ) by (clear - Hα; solve_notin).
          assert (HαΔ : α `notin` Δ) by (clear - Hα; solve_notin).
          assert (Hαβ : α `notin` singleton β) by (clear - Hα; solve_notin).
          assert (Hαψ : α `notin` ftvar_in_uskl ψsrc)
            by (clear - Hα; solve_notin).
          assert (HαPb : α `notin` ftvar_in_pskl (msubst_pskl (κ' ++ κ) Pb))
            by (clear - Hα; solve_notin).
          assert (Hdefs : forall α3 τ3, binds α3 (abind_flex_mono_def τ3) Θ ->
                    β `notin` ftvar_in_ptyp τ3 /\ α `notin` ftvar_in_ptyp τ3).
          { intros α3 τ3 Hb.
            pose proof (a_wf_ptyp_ftv_dom
                          (@a_wf_aenv_binds_def_wf Θ α3 τ3 HwfΘ Hb)) as Hd.
            split; [ clear - Hd HβΘ; fsetdec | clear - Hd HαΘ; fsetdec ]. }
          pose proof (@ad_partial_precise_rename Θ (add β Δ)
                        (Ψi0 `union` Ψa)
                        (open_pskl_wrt_pskl (msubst_pskl (κ' ++ κ) Pb)
                           (pskl_var_f β))
                        (open_uskl_wrt_uskl ψsrc (uskl_var_f β)) Hp' β α
                        ltac:(clear; fsetdec) HβΘ HαΘ
                        ltac:(clear - HαΔ Hαβ; fsetdec)
                        ltac:(pose proof
                                (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                                   (msubst_pskl (κ' ++ κ) Pb)
                                   (pskl_var_f β)) as Hup;
                              cbn [ftvar_in_pskl] in Hup;
                              clear - HαPb Hαβ Hup; fsetdec)
                        ltac:(pose proof
                                (ftvar_in_uskl_open_uskl_wrt_uskl_upper
                                   ψsrc (uskl_var_f β)) as Hup;
                              cbn [ftvar_in_uskl] in Hup;
                              clear - Hαψ Hαβ Hup; fsetdec)
                        Hdefs) as Hrn.
          rewrite <- (@subst_pskl_in_pskl_intro β (msubst_pskl (κ' ++ κ) Pb)
                        (pskl_var_f α)) in Hrn; [ | exact HβPbκ ].
          rewrite <- (@subst_bskl_in_uskl_intro β ψsrc (uskl_var_f α))
            in Hrn; [ | clear - Fr; solve_notin ].
          eapply ad_partial_precise_delta_cong;
            [ exact Hrn | clear - HβΔ; fsetdec ].
      - (* □ : P-Ghost solves no tag, but ε is already in Ψi *)
        exfalso.
        pose proof (ad_ppre_hole_subject_tags Hpre0) as HΨie.
        clear - HΨie HεΨi; fsetdec.
      - (* ∀◇Pi0 : both rules that could reach a ∀^ε are refuted *)
        exfalso.
        assert (HgPi0 : guarded_pskl Pi0) by (inversion HwfPi; assumption).
        inversion Hpre0; subst.
        + (* P-UnivGhostRemove: wf makes the ∀◇-body guarded *)
          eapply ad_ppre_guarded_all_etag_absurd;
            [ exact HwfΘ | exact Hκ | exact HgPi0
            | exact (a_tags_sort_d_tags Htags0) | eassumption ].
        + (* P-UnivGhostFill: the body carries no ε, so Ψi cannot either *)
          assert (Hexf : exists Lf Pf, forall α, α `notin` Lf ->
                    ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ Pf ⊑ᵖ[ Ψi ]
                      (open_uskl_wrt_uskl ψsrc (uskl_var_f α)))
            by (eexists; eexists; eassumption).
          destruct Hexf as (Lf & Pf & Hfill).
          pick fresh α2 for (Lf `union` Lt `union` dom Θ).
          (* the wf must be BUILT FIRST: as an [eapply] side goal its context
             is still an evar and the freshness cannot be shown *)
          assert (Hwf2 : a_wf_aenv ((α2 ~ abind_tvar) ++ Θ))
            by (apply a_wf_aenv__tvar; [ clear - Fr; solve_notin | exact HwfΘ ]).
          assert (HΨisub : Ψi [<=] Ψt0)
            by (eapply ad_partial_precise_tags_sub;
                  [ exact Hwf2
                  | apply (Hfill α2 ltac:(clear - Fr; solve_notin))
                  | exact (a_tags_sort_d_tags
                             (Htbody α2 ltac:(clear - Fr; solve_notin))) ]).
          clear - HΨisub HεΨi Hεt0; fsetdec. }
    (* dispatch: ψa is ∀^ε itself (ρ = id or a congruence) or a ρ-leaf *)
    destruct (uskl_rho_all_etag_l_inv Hrho) as [[Heq HΨρe] | [Hleaf | Hcong]].
    + (* refl: ρ is the identity here, so ψ' := R *)
      subst ψa.
      assert (Htsk : is_tskl (uskl_all_etag ε R))
        by (inversion Htags; assumption).
      destruct (is_tskl_all_etag_inv Htsk) as (Li & Hti).
      eapply MAIN;
        solve [ intros α Hα; apply urho__refl;
                  [ apply is_tskl_lc; apply Hti; exact Hα
                  | clear - HΨρe; fsetdec ]
              | exact Htags | exact Hpre ].
    + (* ρ-leaf: the guess is a replaced rigid variable *)
      destruct Hleaf as (α0 & Ψ'' & Heq & HαΔρ & _ & _ & _); subst ψa.
      eapply a_solve_sub_complete_rho_var;
        solve [ exact HwfΘ | exact Htags | clear - Htageq; fsetdec
              | exact Hrhof | exact Hdelta | exact HαΔρ | exact Hapart
              | exact HwfPi | exact Hpre ].
    + (* congruence *)
      destruct Hcong as (L0 & ψsrc & Heq & Hfam); subst ψa.
      eapply MAIN;
        solve [ exact Hfam | exact Htags | exact Hpre ].
  - (* ForallL, untagged : IMPOSSIBLE.  The subject is an UNTAGGED ∀, and a
       decorated skeleton carries a tag on EVERY quantifier ([is_tskl] has
       only [all_etag]) — so neither ψa nor a ρ-image has this shape.  This
       is the mech's second constructor for the paper's single ForallL rule
       (its ∀^β1 subject has a POTENTIAL tag, declarative.tex:884); the
       tags-sorted target forces β1 = ε, i.e. the tagged row. *)
    exfalso.
    assert (Htsk : is_tskl ψa) by (inversion Htags; assumption).
    destruct (uskl_rho_all_syn_l_inv Hrho) as [[Heq _] | [Hleaf | Hcong]].
    + subst ψa; inversion Htsk.
    + destruct Hleaf as (α0 & Ψ'' & _ & _ & Htagsub & _ & _).
      assert (Htsk' : is_tskl (uskl_all_syn R)) by (inversion Htagsub; assumption).
      inversion Htsk'.
    + destruct Hcong as (L0 & R0 & Heq & _); subst ψa; inversion Htsk.
  - (* Ghost (SK) : IMPOSSIBLE — ψa cannot contain a plain □.
       The subject is [uskl_hole]; [uskl_rho_hole_l_inv] leaves either
       ψa = □ (refuted by [is_tskl], which admits only the DOTTED ◈) or a
       ρ-leaf whose image □ would have to be tags-sorted (same refutation). *)
    exfalso.
    assert (Htsk : is_tskl ψa) by (inversion Htags; assumption).
    destruct (uskl_rho_hole_l_inv Hrho) as [[Heq _] | Hleaf].
    + subst ψa; inversion Htsk.
    + destruct Hleaf as (α0 & Ψ'' & _ & _ & Htagsub & _ & _).
      assert (Htsk' : is_tskl uskl_hole) by (inversion Htagsub; assumption).
      inversion Htsk'.
  - (* GhostG (SK) : the dotted ◈ subject.  [mod_comp_sk ⟨⟩ M] rules out
       [FN], so M ∈ {TI, TC} and [skmod{SK}] forces P0 = □ once more *)
    assert (HP0 : P0 = pskl_hole).
    { pose proof (HmodSK eq_refl) as Hm; inversion Hm; subst;
        solve [ reflexivity | inversion H0 ]. }
    subst P0.
    (* SolS-Vacuous generates nothing *)
    eapply solve_sub_ext_nil with (Pa := Pi);
      [ apply a_solve_sub__vacuous | exact HwfPi | cbn [app] ].
    eapply ad_partial_precise_psi_cong; [ exact Hpre | ].
    assert (HPsiae : Ψa [=] empty) by (clear - HΨs2 H; fsetdec).
    clear - HPsiae; fsetdec.
  - (* UnivGhostL (SK) : IMPOSSIBLE for the same reason as Ghost — the
       subject is a PLAIN ∀◇, and [is_tskl] admits only the DOTTED ∀◈, so
       neither ψa itself nor a ρ-image can have this shape *)
    exfalso.
    assert (Htsk : is_tskl ψa) by (inversion Htags; assumption).
    destruct (uskl_rho_tophole_l_inv Hrho) as [[Heq _] | [Hleaf | Hcong]].
    + subst ψa; inversion Htsk.
    + destruct Hleaf as (α0 & Ψ'' & _ & _ & Htagsub & _ & _).
      assert (Htsk' : is_tskl (uskl_tophole R)) by (inversion Htagsub; assumption).
      inversion Htsk'.
    + destruct Hcong as (R0 & Heq & _); subst ψa; inversion Htsk.
  - (* UnivGhostLG (SK) : the DOTTED ∀◈ subject.  ψa is either a ρ-leaf
       (closed by [a_solve_sub_complete_rho_var]) or itself a ∀◈; in the
       latter case the precision premise forces Pi = ∀◇Pi' or Pi = □, and
       the ∀◇ row is IH + SolS-UnivGhostL + P-UnivGhostKeep. *)
    assert (Htsk : is_tskl ψa) by (inversion Htags; assumption).
    (* the ∀◈-shaped rows share a body; state it once, then dispatch *)
    assert (KEY : forall ψ0,
      uskl_rho a_sub_mode_sk Θ Δρ Ψρ R ψ0 ->
      a_tags_sort a_sub_mode_sk Ψt (uskl_topholeg ψ0) ->
      Θ ⨟ Δ ⊢ (msubst_pskl κ Pi) ⊑ᵖ[ Ψi ] (uskl_topholeg ψ0) ->
      solve_sub_ext Θ0 Θw M Pi P0 Lav
        (fun κ' Pa =>
           Θ ⨟ Δ ⊢ (msubst_pskl (κ' ++ κ) Pa)
             ⊑ᵖ[ Ψi `union` Ψa ] (uskl_topholeg ψ0))).
    { intros ψ0 Hrho0 Htags0 Hpre0.
      assert (Htags0' : a_tags_sort a_sub_mode_sk Ψt ψ0)
        by (eapply a_tags_sort_topholeg_inv; exact Htags0).
      assert (HwfSub' : Θ ⨟ empty ⊢ₚₛᵃ ⌊ R ⌋ˢ)
        by (cbn [uskl_to_pskl] in HwfSub;
            eapply a_wf_pskl_tophole_inv; exact HwfSub).
      (* Pi's shape is pinned by the precision premise: only a ∀◇ or a □
         can be precise to a dotted universal ghost *)
      destruct Pi as [ | nPi | β | Pi1 Pi2 | Pi' | | Pi' ].
      - exfalso; eapply ad_ppre_guarded_topholeg_absurd;
          [ exact HwfΘ | exact Hκ | apply guarded_pskl__unit | exact Hpre0 ].
      - inversion HwfPi.
      - exfalso; eapply ad_ppre_guarded_topholeg_absurd;
          [ exact HwfΘ | exact Hκ | apply guarded_pskl__var | exact Hpre0 ].
      - exfalso.
        assert (Hg : guarded_pskl (pskl_arrow Pi1 Pi2)).
        { pose proof (a_wf_pskl_lc HwfPi) as Hlcarr.
          inversion Hlcarr; subst; apply guarded_pskl__arrow; assumption. }
        eapply ad_ppre_guarded_topholeg_absurd;
          [ exact HwfΘ | exact Hκ | exact Hg | exact Hpre0 ].
      - (* ∀: no precision rule reaches a ∀◈ from a quantifier *)
        cbn [msubst_pskl] in Hpre0; inversion Hpre0.
      - (* □ : the ghost row.  [paper-gap] The paper's UnivGhostLG case says
           "we know that P_i must have a top-level ∀◇" (subtyping-proofs.tex
           :2196), reading the precision premise as if only P-UnivGhostKeep
           could target a ∀◈.  But P-Ghost is TARGET-AGNOSTIC — [□ ⊑ᵖ[∅] ψ]
           for any ψ — so a hole input is precise to a ∀◈ too, and this row
           is real.  The consistency twin's proof DOES spell out its
           "Subcase P_i = □"; the subtyping write-up simply omits it.
           Nothing is decomposed here (a □ input stays □), so the IH's own
           solve is the one we need; only its precision has to be lifted
           back under the ghost. *)
        cbn [msubst_pskl] in Hpre0.
        pose proof (ad_ppre_hole_subject_tags Hpre0) as HΨie.
        (* the Δ-disjointness the IH needs, read off the SAME premise: the
           ∀◈ adds no free variable, so [P-Ghost]'s side condition at
           [∀◈ψ0] IS the one at ψ0 *)
        assert (HΔψ0 : Δ ∩ ftvar_in_uskl ψ0 [=] empty).
        { (* only [P-Ghost] can conclude with a ∀◈ target from a □ subject:
             the target-side flexible unfolding needs a VARIABLE target *)
          inversion Hpre0; subst; cbn [ftvar_in_uskl] in *; assumption. }
        assert (Hpre0' : Θ ⨟ Δ ⊢ (msubst_pskl κ pskl_hole) ⊑ᵖ[ Ψi ] ψ0)
          by (cbn [msubst_pskl]; apply ad_ppre__hole; assumption).
        edestruct (IHHsub Θ Θ0 κ Δ Δρ Ψρ Ψt Ψi Ψa ψ0 pskl_hole P0
                     HwfΘ HwfΘ0 Hmon Hnr Hκw HΔρw
                     HwfPi HwfP0 HmodSK HmodTY Hκ Hrho0
                     Htags0' HwfSub' Htageq Hinter Hrhof Hdelta Hapart
                     Hdfresh Hpre0' HΨs1 HΨs2 Hext Hrefine Lav HLav)
          as (Ξ & Pa' & κ' & Hs' & Hfm & Hu & Hk & Hfr & HF & Hw' & Hp').
        exists Ξ, Pa', κ'.
        repeat (split; [ solve [ exact Hs' | exact Hfm | exact Hu | exact Hk
                               | exact Hfr | exact HF | exact Hw' ] | ]).
        eapply ad_ppre_lift_topholeg;
          [ exact HwfΘ | exact Hp' | exact HΔψ0
          | (* the guess erases to a guarded skeleton: ρ transports it from
               the subject, whose ∀◈-body wf makes it guarded *)
            eapply uskl_rho_guarded_erase;
              [ exact Hrho0
              | apply is_tskl_lc; inversion Htags0'; assumption
              | cbn [uskl_to_pskl] in HwfSub;
                inversion HwfSub; assumption ]
          | (* the shape of the output, pushed through the metasubstitution *)
            destruct (a_solve_sub_hole_output Hs') as [-> | (B & ->)];
              [ left; reflexivity
              | right; eexists; cbn [msubst_pskl]; reflexivity ] ].
      - (* ∀◇Pi' : the main row — IH, then SolS-UnivGhostL *)
        assert (HwfPi' : Θ0 ⨟ empty ⊢ₚₛᵃ Pi')
          by (eapply a_wf_pskl_tophole_inv; exact HwfPi).
        assert (HgPi' : guarded_pskl Pi') by (inversion HwfPi; assumption).
        cbn [msubst_pskl] in Hpre0.
        inversion Hpre0; subst.
        + (* P-UnivGhostRemove: EXCLUDED — wf makes the ∀◇-body guarded *)
          exfalso; eapply ad_ppre_guarded_topholeg_absurd;
            [ exact HwfΘ | exact Hκ | exact HgPi' | eassumption ].
        + (* P-UnivGhostKeep *)
          match goal with Hbody : _ ⨟ _ ⊢ _ ⊑ᵖ[ _ ] ψ0 |- _ =>
            rename Hbody into Hpre' end.
          assert (Hapart' : forall α0, α0 `in` Δρ ->
                    α0 `notin` pskl_shielded_ftv (msubst_pskl κ Pi')).
          { intros α0 Hα0. pose proof (Hapart α0 Hα0) as Hsh.
            cbn [msubst_pskl pskl_shielded_ftv] in Hsh.
            pose proof (pskl_shielded_ftv_sub_ftv (msubst_pskl κ Pi')) as Hle.
            clear - Hsh Hle; fsetdec. }
          edestruct (IHHsub Θ Θ0 κ Δ Δρ Ψρ Ψt Ψi Ψa ψ0 Pi' P0
                       HwfΘ HwfΘ0 Hmon Hnr Hκw HΔρw
                       HwfPi' HwfP0 HmodSK HmodTY Hκ Hrho0
                       Htags0' HwfSub' Htageq Hinter Hrhof Hdelta Hapart'
                       Hdfresh Hpre' HΨs1 HΨs2 Hext Hrefine Lav HLav)
            as (Ξ & Pa' & κ' & Hs' & Hfm & Hu & Hk & Hfr & HF & Hw' & Hp').
          exists Ξ, (pskl_tophole Pa'), κ'.
          repeat (split;
            [ solve [ apply a_solve_sub__univ_ghost_l; exact Hs'
                    | exact Hfm | exact Hu | exact Hk | exact Hfr | exact HF
                    | apply a_wf_pskl__tophole;
                        [ eapply (proj1 a_solve_sub_eq_guarded);
                            [ exact Hs' | eapply a_wf_pskl_lc; exact HwfPi'
                            | eapply a_wf_pskl_lc; exact HwfP0 | exact HgPi' ]
                        | exact Hw' ] ] | ]).
          cbn [msubst_pskl]; apply ad_ppre__tophole_keep; exact Hp'. }
    destruct (uskl_rho_topholeg_l_inv Hrho) as [[Heq HΨρe] | [Hleaf | Hcong]].
    + (* refl: ρ is the identity here, so ψ0 := R *)
      subst ψa.
      assert (Hlc : lc_uskl R) by (inversion Htsk; apply is_tskl_lc; assumption).
      apply KEY; solve [ apply urho__refl; assumption | assumption ].
    + (* ρ-leaf: ψa is a replaced rigid variable *)
      destruct Hleaf as (α0 & Ψ'' & Heq & HαΔρ & _ & _ & _); subst ψa.
      eapply a_solve_sub_complete_rho_var;
        solve [ exact HwfΘ | exact Htags | clear - Htageq; fsetdec
              | exact Hrhof | exact Hdelta | exact HαΔρ | exact Hapart
              | exact HwfPi | exact Hpre ].
    + (* congruence: ψa = ∀◈ψ0 with R ρ-related to ψ0 *)
      destruct Hcong as (ψ0 & Heq & Hrho0); subst ψa.
      apply KEY; assumption.
  - (* FlexMono : the subject is a DEFINED flexible.  The guess is either
       that same flexible — unfold it on BOTH sides and rebuild the
       precision with P-FlexR — or a ρ-leaf. *)
    destruct (uskl_rho_var_l_inv Hrho) as [[Heq HΨρe] | Hleaf].
    + (* the guess is the same defined flexible *)
      subst ψa.
      assert (HΨte : Ψt [=] empty)
        by (exact (d_tags_skl_var_inv (a_tags_sort_d_tags Htags))).
      assert (Hmono : mono_ptyp τ)
        by (eapply a_wf_aenv_binds_def_mono; [ exact HwfΘ | exact H ]).
      assert (Hwfτ : a_wf_ptyp Θ τ)
        by (eapply a_wf_aenv_binds_def_wf; [ exact HwfΘ | exact H ]).
      (* the unfolded guess: a monotype painting, hence tag-free, and
         Δ-clean because a definition never mentions a Δ-variable *)
      assert (Hclean : (ftvar_in_uskl (ptyp_to_uskl_syn τ)) ∩ Δρ [=] empty).
      { rewrite ftvar_in_uskl_ptyp_to_uskl_syn.
        intros α0; split; intros Hin; [ | clear - Hin; fsetdec ].
        exfalso.
        assert (Hα0Δ : α0 `in` Δ) by (clear - Hin Hdelta; fsetdec).
        pose proof (Hdfresh α0 α τ Hα0Δ H) as Hbad.
        clear - Hin Hbad; fsetdec. }
      assert (Hrho' : uskl_rho NM Θ Δρ Ψρ
                        (ptyp_to_uskl_syn τ) (ptyp_to_uskl_syn τ))
        by (apply urho__refl;
            [ apply is_tskl_lc; apply mono_ptyp_to_uskl_syn_tskl; exact Hmono
            | exact HΨρe ]).
      edestruct (IHHsub Θ Θ0 κ Δ Δρ Ψρ Ψt Ψi Ψa (ptyp_to_uskl_syn τ) Pi P0
                   HwfΘ HwfΘ0 Hmon Hnr Hκw HΔρw
                   HwfPi HwfP0 HmodSK HmodTY Hκ Hrho')
        as (Ξ & Pa & κ' & Hs & Hfm & Hu & Hk & Hfr & HF & Hw & Hp).
      * (* the painting is tags-sorted, with NO tags *)
        eapply a_tags_sort_psi_cong;
          [ apply a_tags_sort_mono_paint; exact Hmono | clear - HΨte; fsetdec ].
      * (* its erasure is well-formed *)
        match goal with |- _ ⨟ _ ⊢ₚₛᵃ ⌊ ptyp_to_uskl_syn ?τ0 ⌋ˢ =>
          replace (uskl_to_pskl (ptyp_to_uskl_syn τ0)) with (ptyp_to_pskl τ0)
            by (symmetry; apply uskl_to_pskl_ptyp)
        end.
        apply mono_ptyp_wf_to_pskl_wf; assumption.
      * exact Htageq.
      * exact Hinter.
      * exact Hrhof.
      * exact Hdelta.
      * exact Hapart.
      * exact Hdfresh.
      * (* precision: unfold the definition on the TARGET *)
        eapply ad_ppre_flexdef_target_unfold;
          [ exact HwfΘ | exact Hdfresh | exact Hpre | reflexivity | exact H ].
      * exact HΨs1.
      * exact HΨs2.
      * exact Hext.
      * exact Hrefine.
      * exact HLav.
      * (* rebuild: the guess is the flexible whose definition we unfolded *)
        exists Ξ, Pa, κ'.
        repeat (split; [ solve [ exact Hs | exact Hfm | exact Hu | exact Hk
                               | exact Hfr | exact HF | exact Hw ] | ]).
        eapply ad_ppre__flex_r; [ exact H | exact Hp ].
    + (* ρ-leaf: the guess is a replaced rigid variable *)
      destruct Hleaf as (α0 & Ψ'' & Heq & HαΔρ & _ & _ & _); subst ψa.
      eapply a_solve_sub_complete_rho_var;
        solve [ exact HwfΘ | exact Htags | clear - Htageq; fsetdec
              | exact Hrhof | exact Hdelta | exact HαΔρ | exact Hapart
              | exact HwfPi | exact Hpre ].
Qed.

Print Assumptions a_solve_sub_complete_var.
