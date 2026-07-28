(** COUNTEREXAMPLE — P6-Sv ("Completeness of constraint collection and
    solving for variables", subtyping-proofs.tex:1696) is FALSE with the
    premise set that closes its CONSISTENCY twin P6-Cv
    ([a_solve_eq_complete_var], prop_look_complete_var.v) — including the
    mech-only [flex_apart] freshening invariant.

    The witness is the SIMPLEST possible ρ-configuration — ρ is the IDENTITY
    ([Δρ = ∅], [urho__refl]) — so no reformulation of the ρ-machinery can
    repair it:

      Θ₀ = α̂            Θ = α̂ := ⟨⟩→⟨⟩         θ = [α̂ ↦ ⟨⟩→⟨⟩]
      N = TY   M = TC   Pi = ∀β. β→β           P₀ = α̂
      ψa = ψsub = ∀^ε β. β→β                   Q  = inh{⟨⟩→⟨⟩}
      Ψ' = Ψi = {ε}     Ψa = Ψsub = Ψρ = ∅     Δ = Δρ = ∅

    Every premise holds: the subtyping premise is [Sub-ForallL] instantiating
    β := ⟨⟩ followed by [Sub-Check]; the refinement is a mono paint refining
    itself; the precision is [P-Forall] over the identity.  But the algorithm
    is FORCED: [SS-ForallL] (the only rule with a ∀ subject — a ∀ is not
    [guarded_pskl], so [SS-Check] cannot fire) and then, on the body
    [β→β ≼ α̂], [SS-Check] + [SE-FlexR], giving [Pa = ∀β. α̂].  Its precision
    obligation is [∀β.(⟨⟩→⟨⟩) ⊑ᵖ ∀^ε β.(β→β)], i.e. [⟨⟩ ⊑ᵖ β] — no rule.

    WHY THIS MATTERS.  The failing configuration is the one
    [cex_p6_flex_counterpart.v] exhibits and [cex_p6_flex_freshened.v]
    declares UNREACHABLE: a raw Θ₀-flexible payload facing a ρ-substituted
    part of ψa.  The freshening argument there covers only the
    CONSTRAINT-COLLECTION route ([LE-FlexR] freshens a flexible counterpart
    at an arrow node).  It does NOT cover the SUBTYPING route: here ρ is
    created by the DECLARATIVE [Sub-ForallL] instantiation inside the
    completeness proof itself (the paper's own ρ_b = ρ ∘ [ψ_b/β]), starting
    from ρ = id, while the raw flexible payload arrives from [LS-Var] (the
    [a_looksub] judgment has no [FlexR] rule at all).  So P6-Sv's induction
    manufactures the "unreachable" configuration out of innocent inputs, and
    [flex_apart] — which is stated at the CURRENT ψa and is destroyed by the
    ForallL descent [Δρ := Δρ ∪ {β}] — cannot exclude it.

    The paper's own side condition ("for every rigid variable in ψa
    substituted by ρ, Pi has the same rigid variable in the same position",
    subtyping-proofs.tex:1730) is SATISFIED all the way down here: at the
    recursive call ψa = β→β, ρ_b substitutes β, and Pi = β→β does have β in
    exactly those positions.  So this is not a mech artefact.

    [paper-gap] — see docs/PAPER-GAPS.md. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.def_decl_algo.
Require Import src.frost.algo.def_decorated.
Require Import src.frost.algo.def_decl_algo_sub.
Require Import src.frost.algo.def_decl_algo_sub_hyg.
Require Import src.frost.def_tags.
Require Import src.frost.algo.prop_compose.       (* msubst_pskl_open *)
Require Import src.frost.algo.prop_mono_bridge.   (* a_wf_aenv_binds_def_mono *)
Require Import src.frost.algo.prop_looksub.       (* ptyp_to_pskl_ftv *)
Require Import src.frost.algo.prop_metasubst.     (* a_wf_ptyp_ftv_dom *)
Require Import src.frost.algo.prop_look_complete. (* uskl_rho, flex_apart, … *)

Set Implicit Arguments.

(* ===================================================================== *)
(*  The witness                                                           *)
(* ===================================================================== *)

Definition cex_τ : ptyp := ptyp_arrow ptyp_unit ptyp_unit.
Definition cex_Θ0 (f : atom) : aenv := (f ~ abind_flex_mono).
Definition cex_Θ (f : atom) : aenv := (f ~ abind_flex_mono_def cex_τ).
Definition cex_θ (f : atom) : metasubst := (f, cex_τ) :: nil.

(* ψa = ψsub = ∀^ε β. β → β *)
Definition cex_ψa (e : atom) : uskl :=
  uskl_all_etag e (uskl_arrow (uskl_var_b 0) (uskl_var_b 0)).
(* Pi = ∀β. β → β *)
Definition cex_Pi : pskl :=
  pskl_all_syn (pskl_arrow (pskl_var_b 0) (pskl_var_b 0)).
(* P0 = α̂ *)
Definition cex_P0 (f : atom) : pskl := pskl_var_f f.
(* Q = inh{⟨⟩ → ⟨⟩} *)
Definition cex_Q : bskl := bskl_arrow bskl_unit bskl_unit.

(* ===================================================================== *)
(*  (1)  the algorithm's answer is FORCED to [∀β. α̂]                       *)
(* ===================================================================== *)

(** The body solve [β→β ≼[TC] α̂] can only be [SS-Check] + [SE-FlexR]. *)
Lemma cex_body_solve_forced : forall Θ0 f β P',
  Θ0 ⊢ₛ (pskl_arrow (pskl_var_f β) (pskl_var_f β)) ≼[ mode_tc ] (pskl_var_f f)
       ⤳ P' ->
  P' = pskl_var_f f.
Proof.
  intros Θ0 f β P' H.
  inversion H; subst; try discriminate.
  (* SS-Check: the equality solve *)
  match goal with Heq : _ ⊢ₑ _ ∼ _ ⤳ _ |- _ =>
    inversion Heq; subst; try discriminate; reflexivity end.
Qed.

(** [Pi = ∀β.β→β] against [P0 = α̂] can only be [SS-ForallL]. *)
Lemma cex_solve_forall_shape : forall Θ0 f Pa,
  Θ0 ⊢ₛ cex_Pi ≼[ mode_tc ] (cex_P0 f) ⤳ Pa ->
  exists L P', Pa = pskl_all_syn P' /\
    (forall β, β `notin` L ->
       Θ0 ⊢ₛ (open_pskl_wrt_pskl (pskl_arrow (pskl_var_b 0) (pskl_var_b 0))
                (pskl_var_f β))
            ≼[ mode_tc ] (pskl_var_f f)
            ⤳ (open_pskl_wrt_pskl P' (pskl_var_f β))).
Proof.
  intros Θ0 f Pa H. unfold cex_Pi, cex_P0 in H.
  inversion H; subst; try discriminate.
  - (* SS-ForallL *)
    match goal with L : atoms, Hfam : forall β, β `notin` ?L0 -> _ |- _ =>
      exists L0; eexists; split; [ reflexivity | exact Hfam ] end.
  - (* SS-Check: a ∀ is not guarded *)
    match goal with Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg end.
Qed.

(** A MONO-PAINT subject can never be precise to a target mentioning a
    variable outside the context: the only rules that introduce a target
    variable are [P-Var] (same variable on both sides) and [P-FlexR] (the
    variable is a definition of Θ), and the definition chains stay inside
    Θ's own images.  This is what refutes the conclusion for EVERY [θa],
    not merely for [θa := θ]. *)
Lemma mono_paint_ppre_target_ftv : forall Θ Δ Ψ P ψ,
  Θ ⨟ Δ ⊢ P ⊑ᵖ[ Ψ ] ψ ->
  a_wf_aenv Θ ->
  (exists τ, mono_ptyp τ /\ P = ptyp_to_pskl τ) ->
  ftvar_in_pskl P [<=] dom Θ ->
  ftvar_in_uskl ψ [<=] dom Θ.
Proof.
  intros Θ Δ Ψ P ψ H; induction H;
    intros HwfΘ Hpaint Hdom; simpl in Hdom |- *.
  - (* unit *) clear; fsetdec.
  - (* var *) exact Hdom.
  - (* arrow *)
    destruct Hpaint as (τ & Hmτ & Heq); destruct τ; simpl in Heq;
      try discriminate Heq.
    inversion Heq; subst; inversion Hmτ; subst.
    assert (Hs1 : ftvar_in_uskl ψ1 [<=] dom Θ)
      by (apply IHad_partial_precise1;
            [ exact HwfΘ | eexists; split; [ | reflexivity ]; assumption
            | clear - Hdom; fsetdec ]).
    assert (Hs2 : ftvar_in_uskl ψ2 [<=] dom Θ)
      by (apply IHad_partial_precise2;
            [ exact HwfΘ | eexists; split; [ | reflexivity ]; assumption
            | clear - Hdom; fsetdec ]).
    clear - Hs1 Hs2; fsetdec.
  - (* forall: a monotype paint has no quantifier *)
    destruct Hpaint as (τ & Hmτ & Heq); destruct τ; simpl in Heq;
      try discriminate Heq.
    inversion Hmτ.
  - (* hole *)
    destruct Hpaint as (τ & Hmτ & Heq); destruct τ; simpl in Heq;
      discriminate Heq.
  - (* tophole_remove *)
    destruct Hpaint as (τ & Hmτ & Heq); destruct τ; simpl in Heq;
      discriminate Heq.
  - (* tophole_fill *)
    destruct Hpaint as (τ & Hmτ & Heq); destruct τ; simpl in Heq;
      discriminate Heq.
  - (* tophole_keep *)
    destruct Hpaint as (τ & Hmτ & Heq); destruct τ; simpl in Heq;
      discriminate Heq.
  - (* flex_l: unfold the definition — its image is a Θ-scoped monotype *)
    apply IHad_partial_precise; [ exact HwfΘ | | ].
    + exists τ; split;
        [ eapply a_wf_aenv_binds_def_mono; eassumption | reflexivity ].
    + rewrite ptyp_to_pskl_ftv.
      intros α0 Hα0. eapply a_wf_aenv_def_ftv_dom; eassumption.
  - (* flex_r: the target variable IS a definition of Θ *)
    pose proof (binds_In _ _ _ _ H) as Hin. clear - Hin; fsetdec.
Qed.

(* ===================================================================== *)
(*  (2)  P6-Sv with P6-Cv's premise set is FALSE                           *)
(* ===================================================================== *)

Theorem p6sv_with_p6cv_premises_is_false :
  ~ (forall n NM M Θ0 Θ θ Δ Δρ Ψρ Ψ' Ψi Ψa Ψsub ψsub ψa Q Pi P0,
       a_wf_aenv Θ -> a_wf_aenv Θ0 ->
       Θ0 ⨟ empty ⊢ₚₛᵃ Pi -> Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
       (* the paper's [skmod{N}{P0}{M}] *)
       (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
       (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
       θ ∷ Θ0 ⊑ Θ ->
       (* ρ and its tags *)
       uskl_rho NM Θ Δρ Ψρ ψsub ψa ->
       a_tags_sort NM Ψ' ψa ->
       lc_uskl ψa ->
       (* the SUBJECT is well-formed (the premise that made P6-Cs true) *)
       Θ ⨟ empty ⊢ₚₛᵃ ⌊ ψsub ⌋ˢ ->
       (* the paper's subtyping-side tag equation [Ψi, Ψa = Ψ'] *)
       Ψi `union` Ψa [=] Ψ' ->
       Ψρ ∩ Ψ' [=] empty ->                       (* the paper's fresh{Ψ'} *)
       rho_fresh Δρ Θ θ -> Δρ [<=] Δ ->
       (forall α, α `in` Δρ ->
          α `notin` pskl_shielded_ftv (msubst_pskl θ Pi)) ->
       delta_def_fresh Δ Θ ->
       flex_apart Θ0 Δρ P0 ψa ->                  (* the mech-only invariant *)
       Θ ⨟ Δ ⊢ (msubst_pskl θ Pi) ⊑ᵖ[ Ψi ] ψa ->
       Ψsub [<=] Ψρ `union` Ψa ->
       Ψa [<=] Ψsub ->
       ad_pat_sub_g n NM M Ψsub Θ ψsub Q ->
       Θ ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh (msubst_pskl θ P0)) ⊳ Q ->
       (* the conclusion is the PAPER's, with its own output metasubstitution
          [θa] (only [θa : Θ0 ⊑ Θ] is kept — dropping the [θ ≡ θa] conjunct
          only makes the refuted statement weaker, hence the refutation
          stronger) *)
       exists Pa θa, Θ0 ⊢ₛ Pi ≼[ M ] P0 ⤳ Pa /\
                     θa ∷ Θ0 ⊑ Θ /\
                     Θ ⨟ Δ ⊢ (msubst_pskl θa Pa) ⊑ᵖ[ Ψi `union` Ψa ] ψa).
Proof.
  intros Hthm.
  pick fresh f. pick fresh e for (singleton f).
  destruct (Hthm 1 a_sub_mode_ty mode_tc (cex_Θ0 f) (cex_Θ f) (cex_θ f)
              empty empty empty (singleton e) (singleton e) empty empty
              (cex_ψa e) (cex_ψa e) cex_Q cex_Pi (cex_P0 f))
    as (Pa & θa & Hsolve & Hinca & Hprec).
  - (* a_wf_aenv Θ *)
    unfold cex_Θ. apply a_wf_aenv__flex_def;
      [ simpl; clear; fsetdec
      | apply a_wf_ptyp__arrow; apply a_wf_ptyp__unit
      | apply mono_ptyp__arrow; apply mono_ptyp__unit
      | apply a_wf_aenv__nil ].
  - (* a_wf_aenv Θ0 *)
    unfold cex_Θ0. apply a_wf_aenv__flex;
      [ simpl; clear; fsetdec | apply a_wf_aenv__nil ].
  - (* Θ0 ⊢ Pi *)
    unfold cex_Pi. apply a_wf_pskl__all with (L := empty).
    intros α Hα. unfold open_pskl_wrt_pskl; simpl.
    apply a_wf_pskl__arrow; apply a_wf_pskl__var; left; clear; fsetdec.
  - (* Θ0 ⊢ P0 *)
    unfold cex_P0, cex_Θ0. apply a_wf_pskl__var; right; right; left.
    unfold binds; simpl; left; reflexivity.
  - (* skmod[SK] : vacuous *) intro Hc; discriminate Hc.
  - (* skmod[TY] : P0 is the type α̂ *)
    intros _. exact (a_ty_mode_compat__tc (ptyp_var_f f)).
  - (* θ ∷ Θ0 ⊑ Θ *)
    unfold cex_θ, cex_Θ0, cex_Θ.
    apply a_inc__flex;
      [ apply a_inc__empty; apply a_suffix__cons;
          [ apply a_suffix__nil | apply a_suffix_binding__flex_mono_def ]
      | apply a_wf_ptyp__arrow; apply a_wf_ptyp__unit
      | apply mono_ptyp__arrow; apply mono_ptyp__unit ].
  - (* ρ = identity *)
    apply urho__refl; [ | clear; fsetdec ].
    unfold cex_ψa. apply lc_uskl_all_etag. intros α.
    unfold open_uskl_wrt_uskl; simpl.
    apply lc_uskl_arrow; apply lc_uskl_var_f.
  - (* tags-sorted ψa *)
    unfold cex_ψa. apply a_tags_sort__ty.
    + apply is_tskl__all_etag with (L := empty). intros α Hα.
      unfold open_uskl_wrt_uskl; simpl.
      apply is_tskl__arrow; apply is_tskl__var.
    + apply d_tags_skl__all_etag with (L := empty) (Ψ0 := empty);
        [ intros α Hα; unfold open_uskl_wrt_uskl; simpl;
          apply d_tags_skl__arrow with (Ψ1 := empty) (Ψ2 := empty);
            [ apply d_tags_skl__var; clear; fsetdec
            | apply d_tags_skl__var; clear; fsetdec
            | clear; fsetdec | clear; fsetdec ]
        | clear; fsetdec
        | clear; fsetdec ].
    + apply uskl_ghost_free__all_etag with (L := empty). intros α Hα.
      unfold open_uskl_wrt_uskl; simpl.
      apply uskl_ghost_free__arrow; apply uskl_ghost_free__var.
  - (* lc ψa *)
    unfold cex_ψa. apply lc_uskl_all_etag. intros α.
    unfold open_uskl_wrt_uskl; simpl.
    apply lc_uskl_arrow; apply lc_uskl_var_f.
  - (* the subject is well-formed *)
    unfold cex_ψa; simpl. apply a_wf_pskl__all with (L := empty).
    intros α Hα. unfold open_pskl_wrt_pskl; simpl.
    apply a_wf_pskl__arrow; apply a_wf_pskl__var; left; clear; fsetdec.
  - (* Ψi, Ψa = Ψ' *) clear; fsetdec.
  - (* Ψρ ⊥ Ψ' *) clear; fsetdec.
  - (* rho_fresh, vacuous *) intros α0 Hα0; exfalso; clear - Hα0; fsetdec.
  - (* Δρ ⊆ Δ *) clear; fsetdec.
  - (* shielded, vacuous *) intros α0 Hα0; exfalso; clear - Hα0; fsetdec.
  - (* delta_def_fresh, vacuous *)
    intros β α0 τ0 Hβ Hb; exfalso; clear - Hβ; fsetdec.
  - (* flex_apart: Δρ = ∅ *) apply fa_clean; clear; fsetdec.
  - (* precision of the INPUT: ∀β.β→β ⊑ᵖ[{ε}] ∀^ε β.β→β *)
    unfold cex_Pi, cex_ψa; simpl.
    apply ad_ppre__forall with (L := empty) (Ψ0 := empty).
    + intros α Hα. unfold open_pskl_wrt_pskl, open_uskl_wrt_uskl; simpl.
      apply ad_ppre__arrow with (Ψ1 := empty) (Ψ2 := empty);
        [ apply ad_ppre__var; [ clear; fsetdec | left; clear; fsetdec ]
        | apply ad_ppre__var; [ clear; fsetdec | left; clear; fsetdec ]
        | clear; fsetdec ].
    + clear; fsetdec.
  - (* Ψsub ⊆ Ψρ ∪ Ψa *) clear; fsetdec.
  - (* Ψa ⊆ Ψsub *) clear; fsetdec.
  - (* the SUBTYPING premise: Sub-ForallL (β := ⟨⟩) then Sub-Check *)
    unfold cex_ψa.
    apply ad_pat_sub_g__forall_l_tagged with (Ψ' := empty) (ψ := uskl_unit);
      [ intro Hc; discriminate Hc
      | clear; fsetdec
      | clear; fsetdec
      | apply a_tags_sort__ty;
          [ apply is_tskl__unit
          | apply d_tags_skl__unit; clear; fsetdec
          | apply uskl_ghost_free__unit ]
      | simpl; apply a_wf_pskl__unit
      | ].
    unfold open_uskl_wrt_uskl; simpl.
    change cex_Q with (pskl_to_bskl_inh (pskl_arrow pskl_unit pskl_unit)).
    apply ad_pat_sub_g__check;
      [ apply guarded_uskl__arrow; apply lc_uskl_unit
      | apply guarded_pskl__arrow; apply lc_pskl_unit
      | ].
    apply ad_pat_consis__arrow with (Ψ1 := empty) (Ψ2 := empty);
      [ apply ad_pat_consis__unit; clear; fsetdec
      | apply ad_pat_consis__unit; clear; fsetdec
      | clear; fsetdec ].
  - (* the REFINEMENT premise: a mono paint refines itself *)
    unfold cex_P0, cex_θ, cex_Q; simpl.
    match goal with |- context [if ?c then _ else _] => destruct c end;
      [ | contradiction ].
    unfold cex_τ; simpl.
    apply ad_refine_syn__arrow; apply ad_refine_syn__unit.
  - (* … and now the conclusion is refuted, for EVERY output θa *)
    destruct (cex_solve_forall_shape Hsolve) as (L & P' & -> & Hfam).
    simpl in Hprec. unfold cex_ψa in Hprec.
    inversion Hprec as [ | | | L2 ? ? ? Ψ0 ? ? ? Hpfam Heq | | | | | | ]; subst.
    destruct (atom_fresh (L `union` L2 `union` singleton f
                            `union` singleton e `union` ftvar_in_pskl P'
                            `union` dom (cex_Θ f) `union` dom θa))
      as [β Hβfr].
    (* the algorithm's body output is FORCED to the raw flexible α̂ *)
    assert (HP'β : open_pskl_wrt_pskl P' (pskl_var_f β) = pskl_var_f f).
    { eapply cex_body_solve_forced.
      pose proof (Hfam β ltac:(clear - Hβfr; fsetdec)) as Hβ.
      unfold open_pskl_wrt_pskl in Hβ; simpl in Hβ. exact Hβ. }
    (* … so the precision obligation is [θa α̂ ⊑ᵖ β→β] — a mono paint against
       a target mentioning the fresh rigid β *)
    pose proof (Hpfam β ltac:(clear - Hβfr; fsetdec)) as Hpβ.
    rewrite <- (@msubst_pskl_open (cex_Θ0 f) θa (cex_Θ f) P' β Hinca
                 ltac:(clear - Hβfr; fsetdec)) in Hpβ.
    rewrite HP'β in Hpβ.
    simpl in Hpβ.
    unfold open_uskl_wrt_uskl in Hpβ; simpl in Hpβ.
    assert (Hbad : ftvar_in_uskl (uskl_arrow (uskl_var_f β) (uskl_var_f β))
                     [<=] dom (cex_Θ f)).
    { eapply mono_paint_ppre_target_ftv;
        [ exact Hpβ
        | unfold cex_Θ; apply a_wf_aenv__flex_def;
            [ simpl; clear; fsetdec
            | apply a_wf_ptyp__arrow; apply a_wf_ptyp__unit
            | apply mono_ptyp__arrow; apply mono_ptyp__unit
            | apply a_wf_aenv__nil ]
        | eexists; split;
            [ eapply a_inc_lookup_mono; exact Hinca | reflexivity ]
        | rewrite ptyp_to_pskl_ftv;
          apply a_wf_ptyp_ftv_dom;
          eapply a_inc_lookup_wf;
            [ exact Hinca
            | unfold cex_Θ0; apply a_wf_aenv__flex;
                [ simpl; clear; fsetdec | apply a_wf_aenv__nil ]
            | unfold cex_Θ0; right; left; unfold binds; simpl; left;
              reflexivity ] ]. }
    simpl in Hbad. unfold cex_Θ in Hbad; simpl in Hbad.
    clear - Hbad Hβfr. simpl in Hβfr. fsetdec.
Qed.

Print Assumptions p6sv_with_p6cv_premises_is_false.
