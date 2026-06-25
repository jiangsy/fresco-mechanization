(** Equivalence of the full declarative typing [d_typing] (paper [dtylab],
    Fig. decl-typing) and the syntax-directed typing [d_syn_typing] (paper
    [sdtylab], Fig. syntax-directed-typing).

    Paper Lemmas: Soundness / Completeness of the syntax-directed rules.
    The only structural difference between the two systems is the standalone
    type-abstraction rule [dtylab{Forall}]: [d_syn_typing] folds it into the
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
Require Import src.frost.prop_basic.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_weakening.
Require Import src.frost.decl.prop_stability.

(* Inversions of the colour predicates / [skmod_ty] at [tc]. *)
Lemma is_ityp_arrow_l : forall B1 B2, is_ityp (btyp_arrow B1 B2) -> is_ityp B1.
Proof. intros B1 B2 H. inversion H; assumption. Qed.
Lemma is_ityp_arrow_r : forall B1 B2, is_ityp (btyp_arrow B1 B2) -> is_ityp B2.
Proof. intros B1 B2 H. inversion H; assumption. Qed.
Lemma skmod_ty_tc_inv : forall B, skmod_ty B mode_tc -> is_ityp B.
Proof. intros B H. inversion H; subst; assumption. Qed.

(* ===================================================================== *)
(*  Soundness:  d_syn_typing ⊆ d_typing                                      *)
(* ===================================================================== *)

Theorem d_syn_typing_sound : forall M Γ e A,
    d_syn_typing M Γ e A -> d_typing M Γ e A.
Proof.
  intros M Γ e A H. induction H.
  - apply d_typing__unit.
  - apply d_typing__var; assumption.
  - apply d_typing__anno; assumption.
  - eapply d_typing__sub; eassumption.
  - apply d_typing__freeze; assumption.
  - (* abs_check_step: peel one inherited ∀ via d_typing__forall.  The result
       body [B] is fully inherited ([is_ityp (btyp_all_inh B)]), hence equal to
       its own inh-repainting, which is what d_typing__forall demands. *)
    pose proof (is_ityp_ptyp_to_btyp_inh H) as Hrt. simpl in Hrt. injection Hrt as Hrt.
    rewrite <- Hrt. apply d_typing__forall with (L := L) (A := btyp_to_ptyp B).
    + apply is_value__abs.
    + intros X HX. rewrite Hrt. apply H1; assumption.
  - (* abs_check_base (ᾱ = ·): the standalone check rule was removed from
       d_typing, so use the GENERAL d_typing__abs at [tc].  Its [skmod_ty]
       premise at [tc] is [is_ityp (inh A → B)] — domain inherited (lc [A] from
       [Γ⊢ₚA]), codomain inherited by the rule's [is_ityp B]. *)
    apply d_typing__abs with (L := L) (A := A);
      [ assumption
      | apply skmod_ty__tc; apply is_ityp__arrow;
          [ apply is_ityp_paint; eapply d_wf_ptyp_lc; eassumption | assumption ]
      | assumption ].
  - (* abs_anno_check_step: as abs_check_step, over the annotated lambda. *)
    pose proof (is_ityp_ptyp_to_btyp_inh H) as Hrt. simpl in Hrt. injection Hrt as Hrt.
    rewrite <- Hrt. apply d_typing__forall with (L := L) (A := btyp_to_ptyp B).
    + apply is_value__abs_anno.
    + intros X HX. rewrite Hrt. apply H1; assumption.
  - (* abs_anno_check_base (ᾱ = ·): general d_typing__abs_anno at [tc], domain
       [inh A] (so [B1 = ptyp_to_btyp_inh A], erasing to [A]). *)
    apply d_typing__abs_anno with (L := L) (A := A) (B1 := ptyp_to_btyp_inh A).
    + assumption.
    + apply btyp_to_ptyp_ptyp_to_btyp_inh.
    + apply skmod_ty__tc; apply is_ityp__arrow;
        [ apply is_ityp_paint; eapply d_wf_ptyp_lc; eassumption | assumption ].
    + assumption.
  - (* abs (m ≠ tc) *)
    apply d_typing__abs with (L := L) (A := A); assumption.
  - (* abs_anno (m ≠ tc) *)
    apply d_typing__abs_anno with (L := L) (A := A) (B1 := B1); assumption.
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
  - simpl in HX. apply d_consis__forall_inh_tagged with (L := L `union` {{X0}}) (Ψ0 := Ψ0).
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
   remaining [d_sub] / [d_pat] / [d_syn_typing] subst lemmas are the content of
   [d_syn_typing_forall_admissible]'s base-term cases below. *)

(** A [tc]-checked lambda is typed only by the [abs_check] rules, which carry
    the body-inheritance side condition — so its type is fully inherited.
    (No [sub] interference: a lambda is not [is_base_term]; no [app]: it is not
    an application.)  This recovers the [is_ityp] obligation that the folded
    [abs_check_step] / [abs_anno_check_step] demand. *)
Lemma d_syn_typing_tc_abs_is_ityp : forall Γ e B,
    d_syn_typing mode_tc Γ (exp_abs e) B -> is_ityp B.
Proof.
  intros Γ e B H. dependent induction H.
  - match goal with Hb : is_base_term (exp_abs _) |- _ => inversion Hb end.
  - assumption.
  - apply is_ityp__arrow;
      [ apply is_ityp_paint; eapply d_wf_ptyp_lc; eassumption | assumption ].
  - exfalso; match goal with Hne : _ <> mode_tc |- _ => apply Hne; reflexivity end.
Qed.

Lemma d_syn_typing_tc_abs_anno_is_ityp : forall Γ A0 e B,
    d_syn_typing mode_tc Γ (exp_abs_anno A0 e) B -> is_ityp B.
Proof.
  intros Γ A0 e B H. dependent induction H.
  - match goal with Hb : is_base_term (exp_abs_anno _ _) |- _ => inversion Hb end.
  - assumption.
  - apply is_ityp__arrow;
      [ apply is_ityp_paint; eapply d_wf_ptyp_lc; eassumption | assumption ].
  - exfalso; match goal with Hne : _ <> mode_tc |- _ => apply Hne; reflexivity end.
Qed.

(* ===================================================================== *)
(*  [X := unit] type-substitution strengthening (for the base-term anno    *)
(*  ∀-case of completeness): a derivation under a fresh tvar [X] survives   *)
(*  substituting [X := unit], which (as [X ∉ ftvar]) drops [X].             *)
(* ===================================================================== *)

(* btyp_unit is BOTH synthesised and inherited, so colour predicates are
   preserved by [X := unit]. *)
Lemma is_ityp_subst_unit : forall B X, is_ityp B -> is_ityp (subst_btyp_in_btyp btyp_unit X B).
Proof.
  intros B X H. induction H; simpl.
  - apply is_ityp__unit.
  - destruct (X0 == X); [ apply is_ityp__unit | apply is_ityp__var ].
  - apply is_ityp__arrow; assumption.
  - apply is_ityp__all with (L := L `union` {{X}}). intros Y HY.
    rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (first [ apply lc_btyp_unit | fsetdec ]). auto.
Qed.

Lemma is_styp_subst_unit : forall B X, is_styp B -> is_styp (subst_btyp_in_btyp btyp_unit X B).
Proof.
  intros B X H. induction H; simpl.
  - apply is_styp__unit.
  - destruct (X0 == X); [ apply is_styp__unit | apply is_styp__var ].
  - apply is_styp__arrow; assumption.
  - apply is_styp__all with (L := L `union` {{X}}). intros Y HY.
    rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (first [ apply lc_btyp_unit | fsetdec ]). auto.
Qed.

Lemma guarded_btyp_subst_unit : forall B X, guarded_btyp B -> guarded_btyp (subst_btyp_in_btyp btyp_unit X B).
Proof.
  intros B X H. induction H; simpl.
  - apply guarded_btyp__unit.
  - destruct (X0 == X); [ apply guarded_btyp__unit | apply guarded_btyp__var ].
  - apply guarded_btyp__arrow;
      apply subst_btyp_in_btyp_lc_btyp; solve [ apply lc_btyp_unit | assumption ].
Qed.

Lemma guarded_utyp_subst_unit : forall C X, guarded_utyp C -> guarded_utyp (subst_utyp_in_utyp utyp_unit X C).
Proof.
  intros C X H. induction H; simpl.
  - apply guarded_utyp__unit.
  - destruct (X0 == X); [ apply guarded_utyp__unit | apply guarded_utyp__var ].
  - apply guarded_utyp__arrow;
      apply subst_utyp_in_utyp_lc_utyp; solve [ apply lc_utyp_unit | assumption ].
Qed.

Lemma is_ttyp_subst_unit : forall C X, is_ttyp C -> is_ttyp (subst_utyp_in_utyp utyp_unit X C).
Proof.
  intros C X H. induction H; simpl.
  - apply is_ttyp__unit.
  - destruct (X0 == X); [ apply is_ttyp__unit | apply is_ttyp__var ].
  - apply is_ttyp__arrow; assumption.
  - apply is_ttyp__all_etag with (L := L `union` {{X}}). intros Y HY.
    rewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (first [ apply lc_utyp_unit | fsetdec ]). auto.
Qed.

(* ===================================================================== *)
(*  Completeness:  d_typing ⊆ d_syn_typing                                   *)
(* ===================================================================== *)

(** The paper's "interesting case" [dtylab{Forall}]: a [∀]-generalised value
    [V] is admissible in [d_syn_typing].  For [λ]-values the [∀] is the folded
    [abs_check_step] / [abs_anno_check_step] (proved here).  For base-term
    values it is re-routed through [Sub] + [d_sub__forall_r], which needs the
    synthesis re-established at [Γ] (the fresh [∀]-var dropped) — an
    [d_syn_typing] tvar-strengthening provided by type-substitution [X := unit]
    (see the [d_sub] note above).  Those three base-term subcases are the only
    remaining holes. *)
Lemma d_syn_typing_forall_admissible : forall L Γ V B,
    is_value V ->
    (forall X, X `notin` L ->
       d_syn_typing mode_tc ((X ~ dbind_tvar) ++ Γ) V (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    d_syn_typing mode_tc Γ V (btyp_all_inh B).
Proof.
  intros L Γ V B Hv IH. inversion Hv; subst.
  - (* unit: base term — Sub + ForallR + (X := unit) strengthening *) admit.
  - (* var: base term — likewise *) admit.
  - (* λx.M : the folded ∀-peel.  [is_ityp (btyp_all_inh B)] is recovered from
       the per-instance typings: each [open B X] types the lambda at [tc], so is
       inherited ([d_syn_typing_tc_abs_is_ityp]). *)
    apply d_syn_typing__abs_check_step with (L := L);
      [ apply is_ityp__all with (L := L); intros X HX;
        exact (d_syn_typing_tc_abs_is_ityp _ _ _ (IH X HX))
      | assumption ].
  - (* λxᴬ.M : the folded ∀-peel (as above). *)
    apply d_syn_typing__abs_anno_check_step with (L := L);
      [ apply is_ityp__all with (L := L); intros X HX;
        exact (d_syn_typing_tc_abs_anno_is_ityp _ _ _ _ (IH X HX))
      | assumption ].
  - (* (M : A) : base term — likewise *) admit.
Admitted.

Theorem d_syn_typing_complete : forall M Γ e A,
    d_typing M Γ e A -> d_syn_typing M Γ e A.
Proof.
  intros M Γ e A H. induction H.
  - apply d_syn_typing__unit.
  - apply d_syn_typing__var; assumption.
  - apply d_syn_typing__anno; assumption.
  - eapply d_syn_typing__sub; eassumption.
  - apply d_syn_typing__freeze; assumption.
  - (* forall: folded ∀ via the admissibility bridge *)
    eapply d_syn_typing_forall_admissible; eassumption.
  - (* abs: d_typing's Abs is general; d_syn splits on the mode — [m≠tc] is
       [__abs], the [tc] case folds into [__abs_check_base].  The latter needs
       the body inherited ([is_ityp B]); since a [tc]-checked body is inherited
       (the same recovery as the forall/lambda cases) this is not a real gap. *)
    destruct m as [ | | m' ].
    + apply d_syn_typing__abs with (L := L);
        [ discriminate | assumption | assumption | assumption ].
    + apply d_syn_typing__abs_check_base with (L := L);
        [ assumption
        | apply is_ityp_arrow_r with (B1 := ptyp_to_btyp_inh A);
          apply skmod_ty_tc_inv; assumption
        | assumption ].
    + apply d_syn_typing__abs with (L := L);
        [ discriminate | assumption | assumption | assumption ].
  - (* abs_anno: as [abs]; the [tc] case is [__abs_anno_check_base].  The skmod
       premise forces the domain inherited at [tc]: [is_ityp B1] + [erase B1 = A]
       give [B1 = inh A], so the d_typing type [B1→B2] IS the [inh A → B2] that
       [__abs_anno_check_base] produces. *)
    destruct m as [ | | m' ].
    + apply d_syn_typing__abs_anno with (L := L) (B1 := B1);
        [ discriminate | assumption | assumption | assumption | assumption ].
    + assert (Hia : is_ityp (btyp_arrow B1 B2)) by (apply skmod_ty_tc_inv; assumption).
      assert (HB1 : ptyp_to_btyp_inh A = B1).
      { pose proof (is_ityp_ptyp_to_btyp_inh (is_ityp_arrow_l _ _ Hia)) as HR.
        rewrite H0 in HR. exact HR. }
      rewrite <- HB1.
      apply d_syn_typing__abs_anno_check_base with (L := L);
        [ assumption | exact (is_ityp_arrow_r _ _ Hia) | assumption ].
    + apply d_syn_typing__abs_anno with (L := L) (B1 := B1);
        [ discriminate | assumption | assumption | assumption | assumption ].
  - (* app *) eapply d_syn_typing__app; eassumption.
Qed.
