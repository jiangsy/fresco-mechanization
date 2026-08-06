(** SOUNDNESS OF TYPE INFERENCE — section D, thm:sound-type-inference
    (paper proofs.tex, app:proof-type-inference).

    An [a_typing] run yields a solution to its type inference problem: the
    output context is an information increase of the input, and in it the
    SYNTAX-DIRECTED declarative judgement [ad_sd_typing] holds at a
    colouring of the inferred type, which refines the inherited painting of
    the input skeleton.  The exact mirror of [a_pat_sound]
    (algo/prop_soundness_pat.v), one layer up.

    ⭐ THIS FILE STARTS WITH THE [Freeze] INGREDIENT, because it is the one
    piece thm:sound-skeleton-inference already paid for.  The appendix's
    [sd-Freeze] carries an explicit [Θ ⊢ B ≡ᵗ A] premise, and the paper
    discharges it with one clause — "which further gives [Θ2 ⊢ B ≡ A]" —
    off thm:sound-consistency.  In the mechanization consistency soundness
    hands back a REFINEMENT into the run's own output colouring, so the
    equivalence is recovered as

      transport (prop_soundness_pat.v §4) : the output colouring becomes a
        colouring of the SUBJECT, giving [inh(A) ⊳ bid(B)]
      §2 below                            : a refinement between two
        GHOST-FREE paintings IS a type equivalence

    which is the "derive it from the transport, do not rebuild it" the
    hand-off asks for (docs/HANDOFF-section-d.md §7.3). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.decorated_algo.def_decl_algo_sub.
Require Import src.frost.decorated_algo.def_decl_algo_typing.
Require Import src.frost.decorated_algo.def_decorated.
Require Import src.frost.decorated_algo.prop_ctx_mono.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_compose.
Require Import src.frost.algo.prop_mono_bridge.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.prop_pat_sub.
Require Import src.frost.algo.prop_soundness_consis.
Require Import src.frost.algo.prop_soundness_pat.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  Coercion identities for the INHERITED painting                    *)
(* ===================================================================== *)

Lemma btyp_to_bskl_ptyp_to_btyp_inh : forall A,
  btyp_to_bskl (ptyp_to_btyp_inh A) = pskl_to_bskl_inh (ptyp_to_pskl A).
Proof. induction A; simpl; congruence. Qed.

Lemma btyp_to_ptyp_open : forall B α,
  btyp_to_ptyp (open_btyp_wrt_btyp B (btyp_var_f α))
  = open_ptyp_wrt_ptyp (btyp_to_ptyp B) (ptyp_var_f α).
Proof.
  intros. unfold open_btyp_wrt_btyp, open_ptyp_wrt_ptyp.
  apply (btyp_to_ptyp_open_rec B (btyp_var_f α) 0).
Qed.

Lemma ptyp_to_btyp_inh_open : forall A α,
  ptyp_to_btyp_inh (open_ptyp_wrt_ptyp A (ptyp_var_f α))
  = open_btyp_wrt_btyp (ptyp_to_btyp_inh A) (btyp_var_f α).
Proof.
  intros A α. unfold open_ptyp_wrt_ptyp, open_btyp_wrt_btyp.
  generalize 0 as k. induction A; intros k; default_simp.
Qed.

(** A colouring whose painting is SYNTHESISED is the all-synthesised one —
    the [Freeze] premise's [ptyp_to_btyp_syn B] shape, read off the IH's
    [◇ ⊳ bid(B)] refinement through [ad_refine_syn_syn_l]. *)
Lemma btyp_syn_painting_inv : forall B P,
  btyp_to_bskl B = pskl_to_bskl_syn P ->
  B = ptyp_to_btyp_syn (btyp_to_ptyp B).
Proof.
  intros B; induction B; intros P Heq; destruct P; simpl in Heq;
    try discriminate; simpl; try reflexivity.
  - inversion Heq. erewrite <- IHB1 by eassumption.
    erewrite <- IHB2 by eassumption. reflexivity.
  - inversion Heq. erewrite <- IHB by eassumption. reflexivity.
Qed.

(* ===================================================================== *)
(*  §2  A refinement between two GHOST-FREE paintings IS an equivalence   *)
(* ===================================================================== *)

(** ⭐ Refinement's whole job is to FILL ghosts; between two paintings of
    plain types there is nothing to fill, so the only rows that can fire
    are the structural ones and the two flexible lookups — which is exactly
    the generating set of [≡ᵗ].  (Δ plays no part: [a_tyequiv__all] binds
    nothing in Θ, so the ∀ row goes straight through.) *)
Lemma ad_refine_syn_inh_tyequiv : forall Θ Δ Qs Qt,
  Θ ⨟ Δ ⊢ᵣᵃ Qs ⊳ Qt ->
  a_wf_aenv Θ ->
  forall A B,
  Qs = pskl_to_bskl_inh (ptyp_to_pskl A) ->
  Qt = btyp_to_bskl B ->
  Θ ⊢ A ≡ᵗ (btyp_to_ptyp B).
Proof.
  intros Θ Δ Qs Qt H; induction H; intros Hwf A B HeqS HeqT.
  - (* unit *)
    destruct A; simpl in HeqS; try discriminate.
    destruct B; simpl in HeqT; try discriminate.
    apply a_tyequiv__refl. apply lc_ptyp_unit.
  - (* var *)
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqS; try discriminate.
    destruct B as [ | n | α2 | B1 B2 | B0 | B0 ]; simpl in HeqT;
      try discriminate.
    assert (Hα1 : α1 = α) by (inversion HeqS; reflexivity).
    assert (Hα2 : α2 = α) by (inversion HeqT; reflexivity).
    subst. apply a_tyequiv__refl. apply lc_ptyp_var_f.
  - (* arrow *)
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqS; try discriminate.
    destruct B as [ | n | α2 | B1 B2 | B0 | B0 ]; simpl in HeqT;
      try discriminate.
    inversion HeqS; inversion HeqT; subst.
    apply a_tyequiv__arrow;
      [ apply IHad_refine_syn1 | apply IHad_refine_syn2 ];
      solve [ exact Hwf | reflexivity ].
  - (* all : the binder enters Δ, which [≡ᵗ] does not have *)
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqS; try discriminate.
    destruct B as [ | n | α2 | B1 B2 | B0 | B0 ]; simpl in HeqT;
      try discriminate.
    inversion HeqS; inversion HeqT; subst.
    apply a_tyequiv__all with (L := L). intros α Hα.
    rewrite <- btyp_to_ptyp_open.
    apply (H0 α Hα Hwf (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))
             (open_btyp_wrt_btyp B0 (btyp_var_f α)));
      [ rewrite ptyp_to_pskl_open, pskl_to_bskl_inh_open; reflexivity
      | rewrite btyp_to_bskl_open; reflexivity ].
  - (* hole : an inherited painting of a TYPE has no ghost *)
    destruct A; simpl in HeqS; discriminate.
  - (* tophole_remove *)
    destruct A; simpl in HeqS; discriminate.
  - (* tophole_fill *)
    destruct A; simpl in HeqS; discriminate.
  - (* tophole_keep *)
    destruct A; simpl in HeqS; discriminate.
  - (* flex_l : unfold the definition on the left *)
    destruct A as [ | n | α1 | A1 A2 | A0 ]; simpl in HeqS; try discriminate.
    assert (Hα1 : α1 = α) by (inversion HeqS; reflexivity). subst α1.
    assert (Hmono : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eassumption).
    eapply a_tyequiv__trans; [ apply a_tyequiv__flex_def; exact H | ].
    apply IHad_refine_syn;
      [ exact Hwf
      | unfold ptyp_to_bskl_syn in *;
        rewrite (ptyp_to_bskl_inh_syn_eq Hmono); reflexivity
      | exact HeqT ].
  - (* flex_r : unfold the definition on the right *)
    destruct B as [ | n | α2 | B1 B2 | B0 | B0 ]; simpl in HeqT;
      try discriminate.
    assert (Hα2 : α2 = α) by (inversion HeqT; reflexivity). subst α2.
    assert (Hmono : mono_ptyp τ)
      by (eapply a_wf_aenv_binds_def_mono; eassumption).
    assert (IH2 : Θ ⊢ A ≡ᵗ (btyp_to_ptyp (ptyp_to_btyp_inh τ))).
    { apply (IHad_refine_syn Hwf A (ptyp_to_btyp_inh τ)); [ exact HeqS | ].
      rewrite btyp_to_bskl_ptyp_to_btyp_inh.
      symmetry; apply (ptyp_to_bskl_inh_syn_eq Hmono). }
    rewrite btyp_to_ptyp_ptyp_to_btyp_inh in IH2.
    simpl. eapply a_tyequiv__trans;
      [ exact IH2 | apply a_tyequiv__sym; apply a_tyequiv__flex_def; exact H ].
Qed.

(* ===================================================================== *)
(*  §3  The [Freeze] ingredient: an annotation check yields [≡ᵗ]          *)
(* ===================================================================== *)

(** ⭐ The paper's "which further gives [Θ2 ⊢ B ≡ A]" (proofs.tex,
    thm:sound-type-inference, Freeze).  DERIVED, not rebuilt: the
    refinement-target transport of prop_soundness_pat.v §4 turns the
    consistency run's own output colouring into a colouring of the SUBJECT,
    and §2 reads the resulting ghost-free refinement as an equivalence. *)
Lemma a_consis_chk_tyequiv : forall Θ0 A B Θ1,
  a_consis_chk Θ0 (ptyp_to_pskl B) (ptyp_to_pskl A) Θ1 ->
  a_wf_aenv Θ0 ->
  a_wf_ptyp Θ0 A ->
  a_wf_ptyp Θ0 B ->
  Θ1 ⊢ B ≡ᵗ A.
Proof.
  intros Θ0 A B Θ1 Hchk Hwf HwfA HwfB.
  destruct (a_consis_chk_annot_refine Hchk Hwf HwfB
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA))
    as [Bt [HeqBt Href]].
  destruct (a_consis_chk_sound Hchk Hwf
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfA)
              ltac:(apply a_wf_ptyp_to_wf_pskl; exact HwfB))
    as [Hle [Hwf1 _]].
  apply a_tyequiv__sym.
  rewrite <- HeqBt.
  eapply ad_refine_syn_inh_tyequiv;
    [ exact Href | exact Hwf1 | reflexivity | reflexivity ].
Qed.

(* ===================================================================== *)
(*  §4  The tm-verbatim invariant for [a_typing]                          *)
(* ===================================================================== *)

(** Reverse tm-verbatim for type-inference runs — the mirror of
    [a_pat_tm_ge] (prop_soundness_pat.v §3a) one layer up.  With
    [a_typing_tm_le] (prop_stability.v) it says a run's term entries are
    the SAME at input and output, which is what sustains a context
    invariant about term entries through the sequential premises of
    [AT-Anno], [AT-Freeze] and [AT-App].  The [AT-Abs] row additionally
    crosses the [guess^TY] block [αs], which is flexible-only. *)
Lemma a_typing_tm_ge : forall m Θ0 P0 e A Θ1,
  Θ0 ⊢ₐ[ m ; P0 ] e ⦂ A ⊣ Θ1 -> aenv_tm_le Θ1 Θ0.
Proof.
  intros m Θ0 P0 e A Θ1 H; induction H.
  - (* unit *) eapply a_sub_tm_ge; eassumption.
  - (* var *) eapply a_sub_tm_ge; eassumption.
  - (* anno *)
    eapply aenv_tm_le_trans; [ eapply a_sub_tm_ge; eassumption | assumption ].
  - (* freeze *)
    eapply aenv_tm_le_trans;
      [ eapply a_consis_chk_tm_ge; eassumption | assumption ].
  - (* abs — the body also sits under the [a_guess_mono] flexibles [αs] *)
    intros y b Htm Hb.
    apply a_split_tm_ge in H0.
    destruct (atom_fresh (L `union` singleton y)) as [x Hx].
    apply H0; [ exact Htm | ].
    eapply binds_tm_strip_suffix;
      [ apply a_decls_suffix; eapply a_guess_mono_decls; eassumption
      | exact Htm | ].
    eapply aenv_tm_le_via_binder_ge with (x := x);
      [ apply H4; clear - Hx; fsetdec | exact Htm
      | intros Heq; subst; clear - Hx; fsetdec | exact Hb ].
  - (* abs_anno *)
    intros y b Htm Hb.
    apply a_split_tm_ge in H0. apply a_consis_chk_tm_ge in H1.
    destruct (atom_fresh (L `union` singleton y)) as [x Hx].
    apply H0; [ exact Htm | ]. apply H1; [ exact Htm | ].
    eapply aenv_tm_le_via_binder_ge with (x := x);
      [ apply H4; clear - Hx; fsetdec | exact Htm
      | intros Heq; subst; clear - Hx; fsetdec | exact Hb ].
  - (* abs_check_step : the peeled entry is a rigid variable *)
    intros y b Htm Hb.
    destruct (atom_fresh (L `union` singleton y)) as [α Hα].
    eapply aenv_tm_le_via_binder_ge with (x := α);
      [ apply H1; clear - Hα; fsetdec | exact Htm
      | intros Heq; subst; clear - Hα; fsetdec
      | apply binds_app_3; exact Hb ].
  - (* abs_check_base *)
    intros y b Htm Hb.
    apply a_split_tm_ge in H.
    destruct (atom_fresh (L `union` singleton y)) as [x Hx].
    apply H; [ exact Htm | ].
    eapply aenv_tm_le_via_binder_ge with (x := x);
      [ apply H2; clear - Hx; fsetdec | exact Htm
      | intros Heq; subst; clear - Hx; fsetdec
      | apply binds_app_3; exact Hb ].
  - (* abs_anno_check_step *)
    intros y b Htm Hb.
    destruct (atom_fresh (L `union` singleton y)) as [α Hα].
    eapply aenv_tm_le_via_binder_ge with (x := α);
      [ apply H1; clear - Hα; fsetdec | exact Htm
      | intros Heq; subst; clear - Hα; fsetdec
      | apply binds_app_3; exact Hb ].
  - (* abs_anno_check_base *)
    intros y b Htm Hb.
    apply a_split_tm_ge in H. apply a_consis_chk_tm_ge in H0.
    destruct (atom_fresh (L `union` singleton y)) as [x Hx].
    apply H; [ exact Htm | ]. apply H0; [ exact Htm | ].
    eapply aenv_tm_le_via_binder_ge with (x := x);
      [ apply H3; clear - Hx; fsetdec | exact Htm
      | intros Heq; subst; clear - Hx; fsetdec
      | apply binds_app_3; exact Hb ].
  - (* app *)
    eapply aenv_tm_le_trans; [ exact IHa_typing2 | ].
    eapply aenv_tm_le_trans;
      [ exact IHa_typing1 | eapply a_pat_tm_ge; eassumption ].
Qed.

(* ===================================================================== *)
(*  §5  Stability of [ad_sd_typing] under the algorithm's increases       *)
(* ===================================================================== *)

(** [≡ᵗ] transports along [⊴] — the [a_inc]-shaped [a_tyequiv_isub]
    (prop_inc.v) at the identity witness. *)
Lemma a_tyequiv_isub_le : forall Θ Θ' A A',
  Θ ⊴ Θ' -> Θ ⊢ A ≡ᵗ A' -> Θ' ⊢ A ≡ᵗ A'.
Proof.
  intros Θ Θ' A A' [[κ [Hid Hinc]] _] Heq.
  eapply a_tyequiv_isub; eassumption.
Qed.

(** The [ad_pat_isub_tm] of the typing layer: [⊴] rewrites a term entry
    only up to [≡ᵗ], so the Var row needs the tm-verbatim invariant beside
    the increase.  Everything else is the embedded judgements' own
    transports; the [∀]-peeling rows push a RIGID entry, so they use
    [a_isub_cons_tvar]. *)
Lemma ad_sd_typing_isub_tm : forall M Θ e B,
  Θ ⊢ˢᵃ[ M ] e ⦂ B ->
  forall Θ', Θ ⊴ Θ' -> aenv_tm_le Θ Θ' ->
  Θ' ⊢ˢᵃ[ M ] e ⦂ B.
Proof.
  intros M Θ e B H; induction H; intros Θ' Hle Htm.
  - (* unit *) apply ad_sd_typing__unit. eapply ad_pat_sub_isub; eauto.
  - (* var *)
    eapply ad_sd_typing__var;
      [ apply Htm; [ exact I | exact H ] | eapply ad_pat_sub_isub; eauto ].
  - (* anno *)
    eapply ad_sd_typing__anno;
      [ apply IHad_sd_typing; assumption | eapply ad_pat_sub_isub; eauto ].
  - (* freeze *)
    eapply ad_sd_typing__freeze;
      [ apply IHad_sd_typing; assumption | eapply a_tyequiv_isub_le; eauto ].
  - (* abs_check_step *)
    apply ad_sd_typing__abs_check_step with (L := L); [ assumption | ].
    intros α Hα. apply H1;
      [ exact Hα | apply a_isub_cons_tvar; exact Hle
      | apply aenv_tm_le_cons; exact Htm ].
  - (* abs_check_base *)
    apply ad_sd_typing__abs_check_base with (L := L);
      [ eapply a_wf_ptyp_isub; eauto | assumption | ].
    intros x Hx. apply H2;
      [ exact Hx
      | apply a_isub_cons_var_typ; [ eapply a_wf_ptyp_lc; eauto | exact Hle ]
      | apply aenv_tm_le_cons; exact Htm ].
  - (* abs_anno_check_step *)
    apply ad_sd_typing__abs_anno_check_step with (L := L); [ assumption | ].
    intros α Hα. apply H1;
      [ exact Hα | apply a_isub_cons_tvar; exact Hle
      | apply aenv_tm_le_cons; exact Htm ].
  - (* abs_anno_check_base *)
    apply ad_sd_typing__abs_anno_check_base with (L := L) (A' := A');
      [ eapply a_wf_ptyp_isub; eauto | eapply a_tyequiv_isub_le; eauto
      | assumption | ].
    intros x Hx. apply H3;
      [ exact Hx
      | apply a_isub_cons_var_typ; [ eapply a_wf_ptyp_lc; eauto | exact Hle ]
      | apply aenv_tm_le_cons; exact Htm ].
  - (* abs *)
    apply ad_sd_typing__abs with (L := L);
      [ assumption | eapply a_wf_ptyp_isub; eauto | assumption | ].
    intros x Hx. apply H3;
      [ exact Hx
      | apply a_isub_cons_var_typ; [ eapply a_wf_ptyp_lc; eauto | exact Hle ]
      | apply aenv_tm_le_cons; exact Htm ].
  - (* abs_anno *)
    eapply ad_sd_typing__abs_anno with (L := L) (A' := A');
      [ assumption | eapply a_wf_ptyp_isub; eauto
      | eapply a_tyequiv_isub_le; eauto | eassumption | assumption | ].
    intros x Hx. apply H5;
      [ exact Hx
      | apply a_isub_cons_var_typ; [ eapply a_wf_ptyp_lc; eauto | exact Hle ]
      | apply aenv_tm_le_cons; exact Htm ].
  - (* app *)
    eapply ad_sd_typing__app;
      [ eapply ad_pat_isub_tm; eauto | eapply ad_refine_syn_isub; eauto
      | apply IHad_sd_typing1; assumption
      | apply IHad_sd_typing2; assumption ].
Qed.

(* ===================================================================== *)
(*  §6  Term-variable renaming for [ad_sd_typing]                         *)
(* ===================================================================== *)

(** The [ad_pat_subst_tm] mirror one layer up: types and skeletons contain
    no term variables, so only the subject and the renamed KEY move, and
    every type-level premise transports along the term-blind relation.
    The App row substitutes into its SKELETON-inference premise too, which
    is exactly what [ad_pat_subst_tm] is for. *)
Lemma ad_sd_typing_subst_tm : forall M Θ' e B,
  Θ' ⊢ˢᵃ[ M ] e ⦂ B ->
  forall Θa x (b : abind) Θ0 y,
  Θ' = Θa ++ (x ~ b) ++ Θ0 ->
  abind_is_tm b ->
  x `notin` dom Θa `union` dom Θ0 ->
  (Θa ++ (y ~ b) ++ Θ0) ⊢ˢᵃ[ M ] (subst_exp_in_exp (exp_var_f y) x e) ⦂ B.
Proof.
  intros M Θ' e B H; induction H;
    intros Θa x0 b0 Θb y Heq Htm Hx0; subst; simpl.
  - (* unit *)
    apply ad_sd_typing__unit.
    eapply ad_pat_sub_mono;
      [ eassumption | apply aenv_tbinds_le_rename_tm;
                      apply abind_is_tm_not_ty; exact Htm ].
  - (* var *)
    destruct_if as [Heqx | Hne].
    + subst x.
      assert (Hb0 : abind_var_typ A = b0).
      { apply binds_app_1 in H as [Hb | Hb];
          [ exfalso; apply binds_In in Hb; clear - Hb Hx0; fsetdec | ].
        apply binds_app_1 in Hb as [Hb | Hb];
          [ | exfalso; apply binds_In in Hb; clear - Hb Hx0; fsetdec ].
        destruct Hb as [Hp | []]. inversion Hp; reflexivity. }
      eapply ad_sd_typing__var;
        [ rewrite Hb0; apply binds_app_3;
          unfold binds; simpl; left; reflexivity
        | eapply ad_pat_sub_mono;
            [ eassumption | apply aenv_tbinds_le_rename_tm;
                            apply abind_is_tm_not_ty; exact Htm ] ].
    + eapply ad_sd_typing__var;
        [ | eapply ad_pat_sub_mono;
              [ eassumption | apply aenv_tbinds_le_rename_tm;
                              apply abind_is_tm_not_ty; exact Htm ] ].
      apply binds_app_1 in H as [Hb | Hb];
        [ apply binds_app_2; exact Hb | ].
      apply binds_app_1 in Hb as [Hb | Hb];
        [ destruct Hb as [Hp | []]; inversion Hp; subst; exfalso; auto | ].
      apply binds_app_3; unfold binds; simpl; right; exact Hb.
  - (* anno *)
    eapply ad_sd_typing__anno;
      [ apply IHad_sd_typing; auto
      | eapply ad_pat_sub_mono;
          [ eassumption | apply aenv_tbinds_le_rename_tm;
                          apply abind_is_tm_not_ty; exact Htm ] ].
  - (* freeze *)
    eapply ad_sd_typing__freeze;
      [ apply IHad_sd_typing; auto
      | eapply a_tyequiv_mono;
          [ eassumption | apply aenv_tbinds_le_rename_tm;
                          apply abind_is_tm_not_ty; exact Htm ] ].
  - (* abs_check_step : a RIGID binder joins the prefix *)
    apply ad_sd_typing__abs_check_step
      with (L := L `union` singleton x0 `union` singleton y);
      [ assumption | ].
    intros α Hα.
    apply (H1 α ltac:(clear - Hα; fsetdec)
             ((α ~ abind_tvar) ++ Θa) x0 b0 Θb y);
      [ reflexivity | exact Htm | simpl; clear - Hx0 Hα; fsetdec ].
  - (* abs_check_base *)
    apply ad_sd_typing__abs_check_base
      with (L := L `union` singleton x0 `union` singleton y);
      [ eapply a_wf_ptyp_mono;
          [ eassumption | apply aenv_tbinds_le_rename_tm;
                          apply abind_is_tm_not_ty; exact Htm ]
      | assumption | ].
    intros z Hz.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hz; fsetdec | apply lc_exp_var_f ].
    apply (H2 z ltac:(clear - Hz; fsetdec)
             ((z ~ abind_var_typ A) ++ Θa) x0 b0 Θb y);
      [ reflexivity | exact Htm | simpl; clear - Hx0 Hz; fsetdec ].
  - (* abs_anno_check_step *)
    apply ad_sd_typing__abs_anno_check_step
      with (L := L `union` singleton x0 `union` singleton y);
      [ assumption | ].
    intros α Hα.
    apply (H1 α ltac:(clear - Hα; fsetdec)
             ((α ~ abind_tvar) ++ Θa) x0 b0 Θb y);
      [ reflexivity | exact Htm | simpl; clear - Hx0 Hα; fsetdec ].
  - (* abs_anno_check_base *)
    apply ad_sd_typing__abs_anno_check_base
      with (L := L `union` singleton x0 `union` singleton y) (A' := A');
      [ eapply a_wf_ptyp_mono;
          [ eassumption | apply aenv_tbinds_le_rename_tm;
                          apply abind_is_tm_not_ty; exact Htm ]
      | eapply a_tyequiv_mono;
          [ eassumption | apply aenv_tbinds_le_rename_tm;
                          apply abind_is_tm_not_ty; exact Htm ]
      | assumption | ].
    intros z Hz.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hz; fsetdec | apply lc_exp_var_f ].
    apply (H3 z ltac:(clear - Hz; fsetdec)
             ((z ~ abind_var_typ A) ++ Θa) x0 b0 Θb y);
      [ reflexivity | exact Htm | simpl; clear - Hx0 Hz; fsetdec ].
  - (* abs *)
    apply ad_sd_typing__abs
      with (L := L `union` singleton x0 `union` singleton y);
      [ assumption
      | eapply a_wf_ptyp_mono;
          [ eassumption | apply aenv_tbinds_le_rename_tm;
                          apply abind_is_tm_not_ty; exact Htm ]
      | assumption | ].
    intros z Hz.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hz; fsetdec | apply lc_exp_var_f ].
    apply (H3 z ltac:(clear - Hz; fsetdec)
             ((z ~ abind_var_typ A) ++ Θa) x0 b0 Θb y);
      [ reflexivity | exact Htm | simpl; clear - Hx0 Hz; fsetdec ].
  - (* abs_anno *)
    eapply ad_sd_typing__abs_anno
      with (L := L `union` singleton x0 `union` singleton y);
      try assumption; try reflexivity;
      try (eapply a_wf_ptyp_mono;
           [ eassumption | apply aenv_tbinds_le_rename_tm;
                           apply abind_is_tm_not_ty; exact Htm ]);
      try (eapply a_tyequiv_mono;
           [ eassumption | apply aenv_tbinds_le_rename_tm;
                           apply abind_is_tm_not_ty; exact Htm ]).
    intros z Hz.
    rewrite subst_exp_in_exp_open_exp_wrt_exp_var;
      [ | clear - Hz; fsetdec | apply lc_exp_var_f ].
    apply (H5 z ltac:(clear - Hz; fsetdec)
             ((z ~ abind_var_typ A) ++ Θa) x0 b0 Θb y);
      [ reflexivity | exact Htm | simpl; clear - Hx0 Hz; fsetdec ].
  - (* app : the skeleton-inference premise is substituted too *)
    eapply ad_sd_typing__app;
      [ eapply ad_pat_subst_tm; [ eassumption | reflexivity | exact Htm
                                | exact Hx0 ]
      | eapply ad_refine_syn_mono;
          [ eassumption | apply aenv_tbinds_le_rename_tm;
                          apply abind_is_tm_not_ty; exact Htm ]
      | apply IHad_sd_typing1; auto
      | apply IHad_sd_typing2; auto ].
Qed.

(** The exists-fresh → cofinite bridge the six term-binder rows need. *)
Corollary ad_sd_typing_rename_tm : forall M x (b : abind) Θ0 e B y,
  ((x ~ b) ++ Θ0) ⊢ˢᵃ[ M ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ B ->
  abind_is_tm b ->
  x `notin` dom Θ0 `union` fvar_in_exp e ->
  ((y ~ b) ++ Θ0) ⊢ˢᵃ[ M ] (open_exp_wrt_exp e (exp_var_f y)) ⦂ B.
Proof.
  intros * Hd Htm Hx.
  rewrite (subst_exp_in_exp_intro x); [ | clear - Hx; fsetdec ].
  change ((y ~ b) ++ Θ0) with (nil ++ (y ~ b) ++ Θ0).
  eapply ad_sd_typing_subst_tm;
    [ exact Hd | reflexivity | exact Htm | simpl; clear - Hx; fsetdec ].
Qed.

(* ===================================================================== *)
(*  §7  ⭐ In CHECK mode the colouring is FORCED                          *)
(* ===================================================================== *)

(** [mod_comp_ty B mode_tc] is [is_ityp B], and an inherited type has only
    one colouring — so at TC the declarative judgement's [btyp] is a
    FUNCTION of its erasure.

    ⭐ WHY THIS MATTERS.  The two [∀]-peeling rows of [a_typing]
    ([AT-AbsCheck]/[AT-AbsAnnoCheck] `_step`) are cofinite in a RIGID α, so
    the naive route to their declarative counterparts needs a
    type-variable renaming for [ad_sd_typing] — which would mean renaming
    lemmas for every judgement it embeds.  It is not needed: those rows run
    at TC, where the IH's colouring at each α is forced to be
    [ptyp_to_btyp_inh] of the erasure, hence already of the
    [open … (btyp_var_f α)] shape the rule wants.  Only the TERM-binder
    rows need a renaming (§6). *)
Lemma btyp_inh_painting_inv : forall B,
  is_ityp B -> B = ptyp_to_btyp_inh (btyp_to_ptyp B).
Proof.
  intros B H; induction H; simpl; try reflexivity.
  - f_equal; assumption.
  - f_equal.
    destruct (atom_fresh (L `union` ftvar_in_btyp A
                            `union` ftvar_in_btyp
                                      (ptyp_to_btyp_inh (btyp_to_ptyp A))))
      as [α Hα].
    apply (open_btyp_wrt_btyp_inj _ _ α);
      [ clear - Hα; fsetdec | clear - Hα; fsetdec | ].
    rewrite <- ptyp_to_btyp_inh_open, <- btyp_to_ptyp_open.
    apply H0. clear - Hα; fsetdec.
Qed.

Corollary btyp_check_colouring : forall B A,
  is_ityp B -> btyp_to_ptyp B = A -> B = ptyp_to_btyp_inh A.
Proof. intros B A Hi Heq. subst A. apply btyp_inh_painting_inv; exact Hi. Qed.
