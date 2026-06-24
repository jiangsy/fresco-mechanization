(** Equivalence of the full declarative typing [d_typing] (paper [dtylab],
    Fig. decl-typing) and the syntax-directed typing [sd_typing] (paper
    [sdtylab], Fig. syntax-directed-typing).

    Paper Lemmas: Soundness / Completeness of the syntax-directed rules.
    The only structural difference between the two systems is the standalone
    type-abstraction rule [dtylab{Forall}]: [sd_typing] folds it into the
    checked-lambda rules ([__abs_check_step] / [__abs_anno_check_step], a
    [∀]-peel restricted to [λ]-values).  Soundness replays each peel as a
    [Forall]; completeness case-splits the [Forall] value on whether it is a
    lambda (peel) or a base term (re-routed through [Sub]+[ForallR]). *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_weakening.
Require Import src.frost.decl.prop_stability.

(* ===================================================================== *)
(*  Soundness:  sd_typing ⊆ d_typing                                      *)
(* ===================================================================== *)

Theorem sd_typing_sound : forall M Γ e A,
    sd_typing M Γ e A -> d_typing M Γ e A.
Proof.
  intros M Γ e A H. induction H.
  - apply d_typing__unit.
  - apply d_typing__var; assumption.
  - apply d_typing__anno; assumption.
  - eapply d_typing__sub; eassumption.
  - apply d_typing__freeze; assumption.
  - (* abs (m ≠ tc) *)
    apply d_typing__abs with (L := L); assumption.
  - (* abs_anno (m ≠ tc) *)
    apply d_typing__abs_anno with (L := L); assumption.
  - (* abs_check_step → Forall over the lambda *)
    apply d_typing__forall with (L := L); [ apply is_value__abs | assumption ].
  - (* abs_check_base → AbsCheck (ᾱ = ·) *)
    apply d_typing__abs_check with (L := L); assumption.
  - (* abs_anno_check_step → Forall over the annotated lambda *)
    apply d_typing__forall with (L := L); [ apply is_value__abs_anno | assumption ].
  - (* abs_anno_check_base → AbsAnnoCheck (ᾱ = ·) *)
    apply d_typing__abs_anno_check with (L := L); assumption.
  - (* app *)
    eapply d_typing__app; eassumption.
Qed.

(* ===================================================================== *)
(*  tvar-strengthening cascade (for the completeness Forall/anno case).   *)
(*  Each judgment drops an unused tvar binding [X ∉ ftvar(type)].         *)
(* ===================================================================== *)

Lemma d_wf_utyp_strengthen : forall Γ C,
    Γ ⊢ᵤ C ->
    forall Γ1 X Γ2, Γ = Γ1 ++ (X ~ dbind_tvar) ++ Γ2 ->
    X `notin` ftvar_in_utyp C ->
    (Γ1 ++ Γ2) ⊢ᵤ C.
Proof.
  intros Γ C H. induction H; intros Γ1 X0 Γ2 Heq HX; subst.
  - apply d_wf_utyp__unit.
  - simpl in HX. apply d_wf_utyp__var. analyze_binds H; try (exfalso; fsetdec); auto.
  - simpl in HX. apply d_wf_utyp__arrow; [ eapply IHd_wf_utyp1 | eapply IHd_wf_utyp2 ]; eauto.
  - simpl in HX. apply d_wf_utyp__all_syn with (L := L `union` {{X0}}).
    intros Y HY. rewrite_env (((Y ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 Y ltac:(auto) ((Y ~ dbind_tvar) ++ Γ1) X0 Γ2); [ simpl_env; reflexivity | ].
    pose proof (ftvar_in_utyp_open_utyp_wrt_utyp_upper C (utyp_var_f Y)) as Hup.
    simpl in Hup. fsetdec.
  - simpl in HX. apply d_wf_utyp__all_etag with (L := L `union` {{X0}}).
    intros Y HY. rewrite_env (((Y ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 Y ltac:(auto) ((Y ~ dbind_tvar) ++ Γ1) X0 Γ2); [ simpl_env; reflexivity | ].
    pose proof (ftvar_in_utyp_open_utyp_wrt_utyp_upper C (utyp_var_f Y)) as Hup.
    simpl in Hup. fsetdec.
Qed.

Lemma d_consis_strengthen : forall Δ Γ C B,
    Δ ⨟ Γ ⊨ C ≈ B ->
    forall Γ1 X Γ2, Γ = Γ1 ++ (X ~ dbind_tvar) ++ Γ2 ->
    X `notin` ftvar_in_utyp C ->
    Δ ⨟ (Γ1 ++ Γ2) ⊨ C ≈ B.
Proof.
  intros Δ Γ C B H. induction H; intros Γ1 X0 Γ2 Heq HX; subst.
  - apply d_consis__unit; assumption.
  - simpl in HX. apply d_consis__var; [ | assumption ]. analyze_binds H; try (exfalso; fsetdec); auto.
  - simpl in HX. eapply d_consis__arrow;
      [ eapply IHd_consis1 | eapply IHd_consis2 | eassumption ]; eauto.
  - simpl in HX. apply d_consis__forall_inh_tagged with (L := L `union` {{X0}}) (Δ0 := Δ0).
    2: eassumption.
    intros Y HY. rewrite_env (((Y ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 Y ltac:(auto) ((Y ~ dbind_tvar) ++ Γ1) X0 Γ2); [ simpl_env; reflexivity | ].
    pose proof (ftvar_in_utyp_open_utyp_wrt_utyp_upper C (utyp_var_f Y)) as Hup.
    simpl in Hup. fsetdec.
  - simpl in HX. apply d_consis__forall_inh_untagged with (L := L `union` {{X0}}).
    intros Y HY. rewrite_env (((Y ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 Y ltac:(auto) ((Y ~ dbind_tvar) ++ Γ1) X0 Γ2); [ simpl_env; reflexivity | ].
    pose proof (ftvar_in_utyp_open_utyp_wrt_utyp_upper C (utyp_var_f Y)) as Hup.
    simpl in Hup. fsetdec.
  - simpl in HX. apply d_consis__forall_syn_tagged with (L := L `union` {{X0}}).
    intros Y HY. rewrite_env (((Y ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 Y ltac:(auto) ((Y ~ dbind_tvar) ++ Γ1) X0 Γ2); [ simpl_env; reflexivity | ].
    pose proof (ftvar_in_utyp_open_utyp_wrt_utyp_upper C (utyp_var_f Y)) as Hup.
    simpl in Hup. fsetdec.
  - simpl in HX. apply d_consis__forall_syn with (L := L `union` {{X0}}).
    intros Y HY. rewrite_env (((Y ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 Y ltac:(auto) ((Y ~ dbind_tvar) ++ Γ1) X0 Γ2); [ simpl_env; reflexivity | ].
    pose proof (ftvar_in_utyp_open_utyp_wrt_utyp_upper C (utyp_var_f Y)) as Hup.
    simpl in Hup. fsetdec.
Qed.

(* NOTE on [d_sub]: a conclusion-only tvar-strengthening ([X ∉ ftvar C] ⇒
   drop X) is FALSE — [d_sub__forall_l] may instantiate with the witness
   [ph = X], which the conclusion does not expose.  The robust replacement is
   type-substitution [X := unit] (rewriting the witnesses too); the pieces
   [d_consis_subst_tvar], [d_wf_utyp_subst_tvar], [d_tags_subst_tvar],
   [d_pat_consis_subst_unit], [d_pat_sub_subst_unit] already exist, and the
   remaining [d_sub] / [d_pat] / [sd_typing] subst lemmas are the content of
   [sd_typing_forall_admissible]'s base-term cases below. *)

(* ===================================================================== *)
(*  Completeness:  d_typing ⊆ sd_typing                                   *)
(* ===================================================================== *)

(** The paper's "interesting case" [dtylab{Forall}]: a [∀]-generalised value
    [V] is admissible in [sd_typing].  For [λ]-values the [∀] is the folded
    [abs_check_step] / [abs_anno_check_step] (proved here).  For base-term
    values it is re-routed through [Sub] + [d_sub__forall_r], which needs the
    synthesis re-established at [Γ] (the fresh [∀]-var dropped) — an
    [sd_typing] tvar-strengthening provided by type-substitution [X := unit]
    (see the [d_sub] note above).  Those three base-term subcases are the only
    remaining holes. *)
Lemma sd_typing_forall_admissible : forall L Γ V B,
    is_value V ->
    (forall X, X `notin` L ->
       sd_typing mode_tc ((X ~ dbind_tvar) ++ Γ) V (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    sd_typing mode_tc Γ V (btyp_all_inh B).
Proof.
  intros L Γ V B Hv IH. inversion Hv; subst.
  - (* unit: base term — Sub + ForallR + (X := unit) strengthening *) admit.
  - (* var: base term — likewise *) admit.
  - (* λx.M : the folded ∀-peel *)
    apply sd_typing__abs_check_step with (L := L); assumption.
  - (* λxᴬ.M : the folded ∀-peel *)
    apply sd_typing__abs_anno_check_step with (L := L); assumption.
  - (* (M : A) : base term — likewise *) admit.
Admitted.

Theorem sd_typing_complete : forall M Γ e A,
    d_typing M Γ e A -> sd_typing M Γ e A.
Proof.
  intros M Γ e A H. induction H.
  - apply sd_typing__unit.
  - apply sd_typing__var; assumption.
  - apply sd_typing__anno; assumption.
  - eapply sd_typing__sub; eassumption.
  - apply sd_typing__freeze; assumption.
  - (* forall *) eapply sd_typing_forall_admissible; eassumption.
  - (* abs (m ≠ tc) *) apply sd_typing__abs with (L := L); assumption.
  - (* abs_check → abs_check_base *)
    apply sd_typing__abs_check_base with (L := L); assumption.
  - (* abs_anno (m ≠ tc) *) apply sd_typing__abs_anno with (L := L); assumption.
  - (* abs_anno_check → abs_anno_check_base *)
    apply sd_typing__abs_anno_check_base with (L := L); assumption.
  - (* app *) eapply sd_typing__app; eassumption.
Qed.
