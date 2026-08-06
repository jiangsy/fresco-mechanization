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
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
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
      | eapply a_tyequiv_isub_le; eauto
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
      | eapply a_tyequiv_mono;
          [ eassumption | apply aenv_tbinds_le_rename_tm;
                          apply abind_is_tm_not_ty; exact Htm ]
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

(* ===================================================================== *)
(*  §8  [ad_sd_typing] respects the colour/mode discipline [skmod{TY}]     *)
(* ===================================================================== *)

(** The [ad_pat_mod_comp_sk] mirror one layer up (prop_soundness_pat.v §5),
    and the algorithmic-context reading of [d_typing_skmod]
    (decl/prop_wellformed.v).  Where the SK layer could read
    [mod_comp_sk] straight off its subtyping premise — the premise's target
    IS a [bskl] — the TY layer's [mod_comp_ty] is stated on a [btyp] while
    the premise's target is that [btyp]'s SKELETON, so the two shapes have
    to be bridged, and the bridge at CHECK mode needs local closure. *)

(* --- §8a  local closure of a consistency's target -------------------- *)

(** Every row builds its target from locally-closed pieces; the only row
    that is not immediate is [__hole], whose fill carries the skeleton
    well-formedness that supplies it. *)
Lemma ad_pat_consis_lc_r : forall Ψ Θ R Q,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Q -> lc_bskl Q.
Proof.
  intros Ψ Θ R Q H; induction H.
  - (* unit *) apply lc_bskl_unit.
  - (* var *) apply lc_bskl_var_f.
  - (* arrow *) apply lc_bskl_arrow; assumption.
  - (* forall_inh_tagged *)
    destruct (atom_fresh L) as [α Hα].
    apply lc_bskl_all_inh_exists with (α1 := α); auto.
  - (* forall_inh_untagged *)
    destruct (atom_fresh L) as [α Hα].
    apply lc_bskl_all_inh_exists with (α1 := α); auto.
  - (* forall_syn_tagged *)
    destruct (atom_fresh L) as [α Hα].
    apply lc_bskl_all_syn_exists with (α1 := α); auto.
  - (* forall_syn *)
    destruct (atom_fresh L) as [α Hα].
    apply lc_bskl_all_syn_exists with (α1 := α); auto.
  - (* ghostg *) apply lc_bskl_hole.
  - (* topholeg *) apply lc_bskl_tophole; assumption.
  - (* hole : the fill's well-formedness is the local closure *)
    apply lc_pskl_to_bskl_inh. eapply a_wf_pskl_lc; eassumption.
  - (* tophole *) apply lc_bskl_tophole; assumption.
  - (* tophole_inh *)
    destruct (atom_fresh L) as [α Hα].
    apply lc_bskl_all_inh_exists with (α1 := α); auto.
  - (* tophole_drop *) assumption.
  - (* flex_l *) assumption.
  - (* flex_r *) apply lc_bskl_var_f.
Qed.

(* --- §8b  the two [btyp] / [bskl] shape bridges ---------------------- *)

(** Erasing to the skeleton reflects local closure. *)
Lemma degree_btyp_of_degree_bskl_erase : forall B k,
  degree_bskl_wrt_bskl k (btyp_to_bskl B) -> degree_btyp_wrt_btyp k B.
Proof.
  induction B; intros k H; simpl in H; inversion H; subst; constructor; auto.
Qed.

Lemma lc_btyp_of_lc_bskl_erase : forall B,
  lc_bskl (btyp_to_bskl B) -> lc_btyp B.
Proof.
  intros B H. apply lc_btyp_of_degree.
  apply degree_btyp_of_degree_bskl_erase.
  apply degree_bskl_wrt_bskl_of_lc_bskl; exact H.
Qed.

(** ⭐ Bridge 1 (INFER mode): a [btyp] whose skeleton is SYNTHESISED is
    itself all-synthesised.  No local closure needed — [is_sskl] carries
    it, and its [hole] / [tophole] rows are unreachable because a [btyp]
    has no ghost. *)
Lemma is_styp_of_is_sskl_erase : forall Q,
  is_sskl Q -> forall B0, Q = btyp_to_bskl B0 -> is_styp B0.
Proof.
  (* [B0], not [B]: [is_sskl__arrow]'s own binders are [A] and [B]. *)
  intros Q H; induction H; intros B0 Heq;
    destruct B0; simpl in Heq; try discriminate.
  - (* unit *) apply is_styp__unit.
  - (* var *) inversion Heq; subst. apply is_styp__var.
  - (* arrow *)
    inversion Heq; subst.
    apply is_styp__arrow; [ apply IHis_sskl1 | apply IHis_sskl2 ]; reflexivity.
  - (* all *)
    inversion Heq; subst.
    apply is_styp__all with (L := L). intros α Hα.
    apply (H0 α Hα). rewrite btyp_to_bskl_open. reflexivity.
Qed.

(** ⭐ Bridge 2 (CHECK mode): a [btyp] whose skeleton is an INHERITED
    painting is itself all-inherited.  ⚠️ Unlike bridge 1 this one DOES
    need local closure — [btyp_to_bskl (btyp_var_b n)] and
    [pskl_to_bskl_inh (pskl_var_b n)] agree, and a bound variable is not
    [is_ityp]. *)
Lemma is_ityp_of_erase_inh : forall B,
  lc_btyp B -> forall P, btyp_to_bskl B = pskl_to_bskl_inh P -> is_ityp B.
Proof.
  intros B H; induction H; intros P Heq;
    destruct P; simpl in Heq; try discriminate.
  - (* unit *) apply is_ityp__unit.
  - (* var *) apply is_ityp__var.
  - (* arrow *)
    inversion Heq. apply is_ityp__arrow;
      [ eapply IHlc_btyp1 | eapply IHlc_btyp2 ]; eassumption.
  - (* all_inh : the only [pskl_to_bskl_inh] row that yields a quantifier *)
    inversion Heq.
    apply is_ityp__all with (L := empty). intros α _.
    apply (H0 α (open_pskl_wrt_pskl P (pskl_var_f α))).
    rewrite btyp_to_bskl_open, pskl_to_bskl_inh_open. simpl.
    rewrite H2. reflexivity.
Qed.

(* --- §8c  the SK-sorted [ad_pat_sub_mod_comp_sk]'s TY analogue -------- *)

Lemma mod_comp_ty_fn_inv : forall B1 B2 m,
  mod_comp_ty (btyp_arrow B1 B2) (mode_fn m) -> mod_comp_ty B2 m.
Proof. intros * H; inversion H; subst; assumption. Qed.

Lemma mod_comp_ty_tc_inv : forall B, mod_comp_ty B mode_tc -> is_ityp B.
Proof. intros * H; inversion H; subst; assumption. Qed.

(** The TY-sorted all-in-one subtyping run's target is mode-compatible —
    the paper's (commented-out) "refinement preserves correspondence" for
    TYPES.  [Infer] and [Check] are the two leaves; [Check]'s local
    closure comes off its own consistency premise (§8a). *)
Lemma ad_pat_sub_mod_comp_ty : forall M Ψ Θ R Q,
  Ψ ⨟ Θ ⊢ₛᵃ[ a_sub_mode_ty | M ] R ⩽ Q ->
  forall Bt, Q = btyp_to_bskl Bt -> mod_comp_ty Bt M.
Proof.
  (* [Bt] for the colouring the target erases from — [B] is [Check]'s and
     [ForallR]'s own binder. *)
  intros M Ψ Θ R Q H.
  remember a_sub_mode_ty as NM eqn:HNM.
  induction H; subst; try discriminate; intros Bt HeqB.
  - (* infer *)
    apply mod_comp_ty__ti. eapply is_styp_of_is_sskl_erase; eassumption.
  - (* check *)
    apply mod_comp_ty__tc.
    eapply is_ityp_of_erase_inh; [ | symmetry; exact HeqB ].
    apply lc_btyp_of_lc_bskl_erase. rewrite <- HeqB.
    eapply ad_pat_consis_lc_r; eassumption.
  - (* forall_r *)
    destruct Bt as [ | n | α | B1 B2 | B0 | B0 ]; simpl in HeqB;
      try discriminate.
    inversion HeqB; subst.
    apply mod_comp_ty__tc. apply is_ityp__all with (L := L). intros α Hα.
    apply mod_comp_ty_tc_inv.
    apply (H0 α Hα eq_refl (open_btyp_wrt_btyp B0 (btyp_var_f α))).
    rewrite btyp_to_bskl_open. reflexivity.
  - (* arrow *)
    destruct Bt as [ | n | α | B1 B2 | B0 | B0 ]; simpl in HeqB;
      try discriminate.
    inversion HeqB; subst.
    apply mod_comp_ty__fn. apply (IHad_pat_sub eq_refl B2). reflexivity.
  - (* forall_l_tagged *) apply (IHad_pat_sub eq_refl Bt); exact HeqB.
  - (* forall_l_untagged *) apply (IHad_pat_sub eq_refl Bt); exact HeqB.
  - (* flex_mono *) apply (IHad_pat_sub eq_refl Bt); exact HeqB.
Qed.

(* --- §8d  local closure off an equivalence --------------------------- *)

(** [≡ᵗ]'s [flex_def] row hands back a flexible's DEFINITION, whose local
    closure is only available from the context — hence the [a_wf_aenv]
    hypothesis, exactly as [d_typing_skmod] carries [d_wf_denv]. *)
Lemma a_tyequiv_lc : forall Θ A A',
  Θ ⊢ A ≡ᵗ A' -> a_wf_aenv Θ -> lc_ptyp A /\ lc_ptyp A'.
Proof.
  intros Θ A A' H; induction H; intros Hwf.
  - (* refl *) split; assumption.
  - (* sym *) destruct (IHa_tyequiv Hwf); split; assumption.
  - (* trans *)
    destruct (IHa_tyequiv1 Hwf); destruct (IHa_tyequiv2 Hwf);
      split; assumption.
  - (* flex_def : a definition is a MONOTYPE *)
    split; [ apply lc_ptyp_var_f | ].
    apply mono_ptyp_lc. eapply a_wf_aenv_binds_def_mono; eassumption.
  - (* arrow *)
    destruct (IHa_tyequiv1 Hwf); destruct (IHa_tyequiv2 Hwf).
    split; apply lc_ptyp_arrow; assumption.
  - (* all *)
    destruct (atom_fresh L) as [α Hα].
    destruct (H0 α Hα Hwf) as [Hl Hr].
    split; eapply lc_ptyp_all_exists; eassumption.
Qed.

Corollary a_tyequiv_lc_r : forall Θ A A',
  Θ ⊢ A ≡ᵗ A' -> a_wf_aenv Θ -> lc_ptyp A'.
Proof. intros * H Hwf. apply (proj2 (a_tyequiv_lc H Hwf)). Qed.

(* --- §8e  the theorem of this section --------------------------------- *)

(** ⭐ The [ad_pat_mod_comp_sk] mirror: a type-inference colouring is
    mode-compatible.  The two Abs rows carry it outright, the three base
    rows read it off their subtyping premise (§8c), the two check-Abs
    pairs rebuild it from [is_ityp], [Freeze] and [AbsAnnoCheck] take
    their local closure off the appendix's [≡ᵗ] premise (§8d), and [App]
    inverts its function premise's. *)
Lemma ad_sd_typing_mod_comp_ty : forall M Θ e B,
  Θ ⊢ˢᵃ[ M ] e ⦂ B -> a_wf_aenv Θ -> mod_comp_ty B M.
Proof.
  intros M Θ e B H; induction H; intros Hwf.
  - (* unit *) eapply ad_pat_sub_mod_comp_ty; [ eassumption | reflexivity ].
  - (* var *) eapply ad_pat_sub_mod_comp_ty; [ eassumption | reflexivity ].
  - (* anno *) eapply ad_pat_sub_mod_comp_ty; [ eassumption | reflexivity ].
  - (* freeze *)
    apply mod_comp_ty__tc. apply is_ityp_paint.
    eapply a_tyequiv_lc_r; eassumption.
  - (* abs_check_step *) apply mod_comp_ty__tc; assumption.
  - (* abs_check_base *)
    apply mod_comp_ty__tc. apply is_ityp__arrow;
      [ apply is_ityp_paint; eapply a_wf_ptyp_lc; eassumption | assumption ].
  - (* abs_anno_check_step *) apply mod_comp_ty__tc; assumption.
  - (* abs_anno_check_base *)
    apply mod_comp_ty__tc. apply is_ityp__arrow;
      [ apply is_ityp_paint; eapply a_tyequiv_lc_r; eassumption
      | assumption ].
  - (* abs *) assumption.
  - (* abs_anno *) assumption.
  - (* app *)
    eapply mod_comp_ty_fn_inv. apply IHad_sd_typing1; exact Hwf.
Qed.

(* ===================================================================== *)
(*  §9  guess^TY REFINES its input skeleton                               *)
(* ===================================================================== *)

(** ⭐ The paper asserts this inline, with no lemma: [AT-Abs]'s case reads
    "By ⑯ and definition of [guess^TY], we have [Θ1,ᾱ ⊢ inh{P} ⊳ inh{A}]"
    (proofs.tex, thm:sound-type-inference).  [prop_flex.v] has [guess^TY]'s
    freshness / decls / ftv facts and its CONSISTENCY
    ([a_guess_mono_consis]) but no refinement one — see docs/PAPER-GAPS.md.

    The content is that filling a ghost with a fresh flexible IS a
    refinement step: [ad_refine_syn__hole]'s fill may be any well-formed
    skeleton, and a bare flexible is one.  Universal ghosts are dropped by
    [__tophole_remove], and the concrete rows are congruences.

    ⚙ SIZE INDUCTION, not derivation induction — for the same reason
    [a_guess_mono_consis_size] is one: the source [a_guess_mono] is
    exists-fresh while the target [ad_refine_syn] is cofinite, so the ∀
    row turns ONE guess instance into a family through
    [a_guess_mono_open_at], whose output is no sub-derivation.

    ⭐ Note the ∀ row puts its witness in [Δ], not in [Θ1] — which is why
    the statement carries a [Δ] at all.  The two contexts must be
    DECOUPLED here exactly as in [ad_refine_syn_target_transport]
    (prop_soundness_pat.v §4f): [ad_refine_syn__hole]'s fill is Δ-free BY
    RULE, and here it is — the fills are the generated flexibles, which
    live in [Θ1]. *)
Lemma a_guess_mono_refine_size : forall n Θ P Ξ A,
  size_pskl P <= n ->
  a_guess_mono Θ P Ξ A ->
  forall Θ1 Δ,
  (forall α, α `in` ftvar_in_pskl P -> α `in` Δ \/ a_binds_tvar α Θ1) ->
  (forall α1, binds α1 abind_flex_mono Ξ -> a_binds_tvar α1 Θ1) ->
  Θ1 ⨟ Δ ⊢ᵣᵃ (pskl_to_bskl_inh P) ⊳ (pskl_to_bskl_inh (ptyp_to_pskl A)).
Proof.
  induction n as [| n IHn]; intros Θ P Ξ A Hsz H;
    [ destruct H; cbn in Hsz; lia | ].
  destruct H as [ Θ α Hα | Θ P Ξ A Hg | Θ α | Θ
                | Θ P Q Ξ1 Ξ2 A B Hg1 Hg2
                | Θ P Ξ A β Hfr Hg ];
    cbn in Hsz; intros Θ1 Δ Hvars HΞ.
  - (* hole ↦ fresh flexible : the FILL of [__hole], Δ-free by construction *)
    replace (pskl_to_bskl_inh (ptyp_to_pskl (ptyp_var_f α)))
      with (pskl_to_bskl_syn (pskl_var_f α)) by reflexivity.
    apply ad_refine_syn__hole.
    apply a_wf_pskl__var. right. apply HΞ.
    unfold binds; left; reflexivity.
  - (* ∀◇P : the universal ghost is DROPPED, so the row is [tophole_remove] *)
    apply ad_refine_syn__tophole_remove.
    eapply IHn; [ lia | exact Hg | exact Hvars | exact HΞ ].
  - (* variable *)
    apply ad_refine_syn__var. apply Hvars. simpl. fsetdec.
  - (* unit *) apply ad_refine_syn__unit.
  - (* arrow *)
    apply ad_refine_syn__arrow;
      [ eapply IHn with (P := P) | eapply IHn with (P := Q) ];
      solve [ lia | eassumption
            | intros α Hα; apply Hvars; simpl; clear - Hα; fsetdec
            | intros α1 Hb; apply HΞ; unfold binds in *;
              apply in_or_app; auto ].
  - (* ∀ : exists-fresh source, cofinite target *)
    apply ad_refine_syn__all
      with (L := dom Ξ `union` dom Θ1 `union` Δ `union` ftvar_in_aenv Θ
                   `union` ftvar_in_pskl P `union` ftvar_in_ptyp A
                   `union` singleton β).
    intros α Hα.
    repeat rewrite <- pskl_to_bskl_inh_open.
    rewrite <- ptyp_to_pskl_open.
    eapply IHn with (P := open_pskl_wrt_pskl P (pskl_var_f α))
                    (Θ := (α ~ abind_tvar) ++ Θ);
      [ rewrite size_pskl_open_pskl_wrt_pskl_var; lia | | | ].
    + apply a_guess_mono_open_at;
        [ apply a_guess_mono__forall with (β := β); [ exact Hfr | exact Hg ]
        | clear - Hα; fsetdec ].
    + intros β0 Hβ0.
      apply ftvar_in_pskl_open_pskl_wrt_pskl_upper in Hβ0.
      simpl in Hβ0.
      destruct (union_1 Hβ0) as [HY' | HY'].
      * apply singleton_1 in HY'; subst. left. clear; fsetdec.
      * destruct (Hvars _ HY') as [HΔ | Htv];
          [ left; clear - HΔ; fsetdec | right; exact Htv ].
    + exact HΞ.
Qed.

(** The paper's inline step, in the shape [AT-Abs] consumes it. *)
Corollary a_guess_mono_refine : forall Θ P Ξ A Θ1 Δ,
  a_guess_mono Θ P Ξ A ->
  (forall α, α `in` ftvar_in_pskl P -> α `in` Δ \/ a_binds_tvar α Θ1) ->
  (forall α1, binds α1 abind_flex_mono Ξ -> a_binds_tvar α1 Θ1) ->
  Θ1 ⨟ Δ ⊢ᵣᵃ (pskl_to_bskl_inh P) ⊳ (pskl_to_bskl_inh (ptyp_to_pskl A)).
Proof. intros. eapply a_guess_mono_refine_size; eauto. Qed.

(* ===================================================================== *)
(*  §10  A MONOTYPE consistency IS a refinement                          *)
(* ===================================================================== *)

(** ⭐ The two judgements have the SAME five rows once the subject is a
    monotype painting — [unit], [var], [arrow] and the two flexible
    lookups — so the derivation maps across one row at a time.  Everything
    that distinguishes them (refinement's ghost-filling, consistency's
    quantifier rows) is unreachable from a monotype subject.

    This is the fact `lemma:split-refine`'s flexible row needs, and it is
    the one the hand-off flagged as genuinely new.  ⛔ Note it is NOT
    proved by induction on `≡ᵗ`: that route would need refinement's
    symmetry and TRANSITIVITY, and transitivity is FALSE in the mech
    (cex/cex_refine_not_transitive.v).  Going through the CONSISTENCY
    instead needs neither — `consis_mono_sym` (prop_mono_bridge.v) supplies
    the direction change. *)
Lemma ad_pat_consis_mono_to_refine : forall Ψ Θ R Qt,
  Ψ ⨟ Θ ⊢ₛᵃ R ∼ Qt ->
  a_wf_aenv Θ ->
  forall A Δ, R = ptyp_to_uskl_syn A -> mono_ptyp A ->
  Θ ⨟ Δ ⊢ᵣᵃ (ptyp_to_bskl_syn A) ⊳ Qt.
Proof.
  intros Ψ Θ R Qt Hc Hwf; induction Hc; intros A0 Δ HeqS HmA0;
    unfold ptyp_to_uskl_syn, ptyp_to_bskl_syn in *.
  - (* unit *)
    destruct HmA0; simpl in HeqS; try discriminate.
    simpl. apply ad_refine_syn__unit.
  - (* var *)
    destruct HmA0 as [ | α0 | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst. simpl. apply ad_refine_syn__var. right; assumption.
  - (* arrow *)
    destruct HmA0 as [ | | A1 A2 Hm1 Hm2 ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    simpl. apply ad_refine_syn__arrow; [ eapply IHHc1 | eapply IHHc2 ];
      solve [ reflexivity | assumption ].
  - (* forall_inh_tagged *) destruct HmA0; simpl in HeqS; discriminate.
  - (* forall_inh_untagged *) destruct HmA0; simpl in HeqS; discriminate.
  - (* forall_syn_tagged *) destruct HmA0; simpl in HeqS; discriminate.
  - (* forall_syn *) destruct HmA0; simpl in HeqS; discriminate.
  - (* ghostg *) destruct HmA0; simpl in HeqS; discriminate.
  - (* topholeg *) destruct HmA0; simpl in HeqS; discriminate.
  - (* hole *) destruct HmA0; simpl in HeqS; discriminate.
  - (* tophole *) destruct HmA0; simpl in HeqS; discriminate.
  - (* tophole_inh *) destruct HmA0; simpl in HeqS; discriminate.
  - (* tophole_drop *) destruct HmA0; simpl in HeqS; discriminate.
  - (* flex_l : the lookup is refinement's own [flex_l] *)
    destruct HmA0 as [ | α0 | ]; simpl in HeqS; try discriminate.
    inversion HeqS; subst.
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    simpl. eapply ad_refine_syn__flex_l; [ eassumption | ].
    eapply IHHc; solve [ reflexivity | assumption ].
  - (* flex_r : and the mirror *)
    assert (Hmτ : mono_ptyp τ) by (eapply a_wf_aenv_binds_def_mono; eauto).
    eapply ad_refine_syn__flex_r; [ eassumption | ].
    eapply IHHc; solve [ reflexivity | assumption ].
Qed.

(* ===================================================================== *)
(*  §11  lemma:split-refine, COLOURED                                    *)
(* ===================================================================== *)

(** The paper's `lemma:split-refine` (proofs.tex): a split refines.  Stated
    COLOURED — the shape `a_typing`'s four CHECK rows consume — rather than
    in the uncoloured `ad_refine_pskl` form.

    ⚠️ THE FRESHNESS SIDE CONDITION.  `a_split__flex` invents two flexible
    variables and the mech's rule records NO freshness for them (the paper
    says "fresh" in prose).  `a_assign_sound` needs the extended context
    well-formed, so the condition is carried as a hypothesis in the only
    shape the statement can express it — quantified over the row's own
    outputs.  WF-SIDE-CONDITIONS pattern. *)
Lemma a_split_refines : forall Θ0 P0 P Q Θ1,
  Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 ->
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  (forall β α1, P = pskl_var_f β -> Q = pskl_var_f α1 ->
     β `notin` dom Θ0 /\ α1 `notin` (dom Θ0 `union` singleton β)) ->
  Θ1 ⨟ empty ⊢ᵣᵃ (pskl_to_bskl_inh P0)
                ⊳ (pskl_to_bskl_inh (pskl_arrow P Q)).
Proof.
  intros Θ0 P0 P Q Θ1 Hs Hwf HwfP Hfresh; inversion Hs; subst.
  - (* arrow : reflexivity at the inherited painting *)
    apply ad_refine_syn_refl_inh. exact HwfP.
  - (* hole : the fill is [□ → □] *)
    simpl.
    replace (bskl_arrow bskl_hole bskl_hole)
      with (pskl_to_bskl_syn (pskl_arrow pskl_hole pskl_hole)) by reflexivity.
    apply ad_refine_syn__hole.
    apply a_wf_pskl__arrow; apply a_wf_pskl__hole.
  - (* flex : the row's premise is a full consistency run *)
    destruct (Hfresh _ _ eq_refl eq_refl) as [Hfrβ Hfrα1].
    assert (HwfX : a_wf_aenv ((α1 ~ abind_flex_mono)
                               ++ (β ~ abind_flex_mono) ++ Θ0)).
    { apply a_wf_aenv__flex;
        [ simpl_env; repeat rewrite dom_app; simpl;
          clear - Hfrα1; fsetdec | ].
      apply a_wf_aenv__flex; [ clear - Hfrβ; fsetdec | exact Hwf ]. }
    assert (HwfArr : ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono) ++ Θ0)
                       ⨟ empty ⊢ₚₛᵃ (pskl_arrow (pskl_var_f β)
                                                (pskl_var_f α1))).
    { apply a_wf_pskl__arrow; apply a_wf_pskl__var; right; right; left;
        [ unfold binds; simpl; right; left; reflexivity
        | unfold binds; simpl; left; reflexivity ]. }
    (* ⭐ ONLY FlexL can fire: the subject is a VARIABLE and the input an
       ARROW, and no other row admits that pair. *)
    match goal with
    | Hc : a_consis _ _ _ _ _ _ _ |- _ => inversion Hc; subst
    end.
    match goal with
    | Ha : _ ⊲[ nil ] _ ≔ _ ⊣ _ |- _ =>
        pose proof (a_assign_sound Ha a_decls__nil
                      ltac:(simpl_env; exact HwfX)
                      ltac:(simpl_env; exact HwfArr)) as [Hle Hcons];
        pose proof (a_assign_preserves_wf Ha a_decls__nil
                      ltac:(simpl_env; exact HwfX)
                      ltac:(simpl_env; exact HwfArr)) as Hwf1
    end.
    (* the run's own consistency can only be FlexR: an ARROW subject
       against a bare variable target *)
    inversion Hcons; subst.
    match goal with
    | Hb : binds _ (abind_flex_mono_def ?τ0) Θ1,
      Hc2 : _ ⨟ Θ1 ⊢ₛᵃ _ ∼ (ptyp_to_bskl_syn ?τ0) |- _ =>
        assert (Hmτ : mono_ptyp τ0)
          by (eapply a_wf_aenv_binds_def_mono; eassumption);
        eapply ad_refine_syn__flex_l; [ exact Hb | ];
        eapply ad_pat_consis_mono_to_refine with (A := τ0);
          [ eapply consis_mono_sym with
              (A := ptyp_arrow (ptyp_var_f β) (ptyp_var_f α1)) (A' := τ0);
              [ exact Hc2 | exact Hwf1 | reflexivity | reflexivity
              | repeat constructor | exact Hmτ ]
          | exact Hwf1 | reflexivity | exact Hmτ ]
    end.
Qed.
