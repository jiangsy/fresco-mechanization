(** Equivalence of the full declarative typing [d_typing] (paper [dtylab],
    Fig. decl-typing) and the syntax-directed typing [d_sd_typing] (paper
    [sdtylab], Fig. syntax-directed-typing).

    Paper Lemmas: Soundness / Completeness of the syntax-directed rules.
    The only structural difference between the two systems is the standalone
    type-abstraction rule [dtylab{Forall}]: [d_sd_typing] folds it into the
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
Require Import src.frost.decl.prop_renaming.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.decl.prop_general_subsumption.
Require Import src.frost.decl.prop_stability.

(* Inversions of the colour predicates / [skmod_ty] at [tc]. *)
Lemma is_ityp_arrow_l : forall B1 B2, is_ityp (btyp_arrow B1 B2) -> is_ityp B1.
Proof. intros B1 B2 H. inversion H; assumption. Qed.
Lemma is_ityp_arrow_r : forall B1 B2, is_ityp (btyp_arrow B1 B2) -> is_ityp B2.
Proof. intros B1 B2 H. inversion H; assumption. Qed.
Lemma skmod_ty_tc_inv : forall B, skmod_ty B mode_tc -> is_ityp B.
Proof. intros B H. inversion H; subst; assumption. Qed.

(* ===================================================================== *)
(*  Soundness:  d_sd_typing ⊆ d_typing                                      *)
(* ===================================================================== *)

Theorem d_sd_typing_sound : forall M Γ e A,
    d_sd_typing M Γ e A -> d_typing M Γ e A.
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
   remaining [d_sub] / [d_pat] / [d_sd_typing] subst lemmas are the content of
   [d_sd_typing_forall_admissible]'s base-term cases below. *)

(** A [tc]-checked lambda is typed only by the [abs_check] rules, which carry
    the body-inheritance side condition — so its type is fully inherited.
    (No [sub] interference: a lambda is not [is_base_term]; no [app]: it is not
    an application.)  This recovers the [is_ityp] obligation that the folded
    [abs_check_step] / [abs_anno_check_step] demand. *)
Lemma d_sd_typing_tc_abs_is_ityp : forall Γ e B,
    d_sd_typing mode_tc Γ (exp_abs e) B -> is_ityp B.
Proof.
  intros Γ e B H. dependent induction H.
  - match goal with Hb : is_base_term (exp_abs _) |- _ => inversion Hb end.
  - assumption.
  - apply is_ityp__arrow;
      [ apply is_ityp_paint; eapply d_wf_ptyp_lc; eassumption | assumption ].
  - exfalso; match goal with Hne : _ <> mode_tc |- _ => apply Hne; reflexivity end.
Qed.

Lemma d_sd_typing_tc_abs_anno_is_ityp : forall Γ A0 e B,
    d_sd_typing mode_tc Γ (exp_abs_anno A0 e) B -> is_ityp B.
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

(* [d_tags] is insensitive to a tvar:=unit substitution — the ε-tags it counts
   are unaffected (unit carries none, and the substituted var is a tvar). *)
Lemma d_tags_subst_unit : forall Δ C X,
    d_tags Δ C ->
    d_tags Δ (subst_utyp_in_utyp utyp_unit X C).
Proof.
  intros Δ C X H. induction H; simpl.
  - apply d_tags__unit; assumption.
  - match goal with |- context [ if ?d then _ else _ ] => destruct d end;
      [ apply d_tags__unit | apply d_tags__var ]; assumption.
  - eapply d_tags__arrow; [ eassumption | eassumption | assumption | assumption ].
  - apply d_tags__all_etag with (L := L `union` {{X}}) (Δ0 := Δ0).
    + intros Z HZ.
      erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var
        by (solve [ fsetdec | apply lc_utyp_unit ]).
      apply H0; auto.
    + assumption.
    + assumption.
Qed.

(* Mid-context tvar:=unit strengthening for [d_wf_utyp] (the head-only
   [d_wf_utyp_subst_tvar] does not reach a [Γ1 ++ X0 :: Γ2] split). *)
Lemma d_wf_utyp_subst_unit : forall Γ C,
    Γ ⊢ᵤ C ->
    forall Γ1 X0 Γ2, Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
    (Γ1 ++ Γ2) ⊢ᵤ (subst_utyp_in_utyp utyp_unit X0 C).
Proof.
  intros Γ C H. induction H; intros Γ1 X0 Γ2 Heq; subst; simpl.
  - apply d_wf_utyp__unit.
  - match goal with |- context [ if ?d then _ else _ ] => destruct d end;
      [ apply d_wf_utyp__unit | apply d_wf_utyp__var; analyze_binds H ].
  - apply d_wf_utyp__arrow; [ eapply IHd_wf_utyp1 | eapply IHd_wf_utyp2 ]; reflexivity.
  - apply d_wf_utyp__all_syn with (L := L `union` dom (Γ1 ++ Γ2) `union` {{X0}}).
    intros Z HZ.
    rewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (first [ apply lc_utyp_unit | fsetdec ]).
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 Z); [ fsetdec | simpl_env; reflexivity ].
  - apply d_wf_utyp__all_etag with (L := L `union` dom (Γ1 ++ Γ2) `union` {{X0}}).
    intros Z HZ.
    rewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (first [ apply lc_utyp_unit | fsetdec ]).
    rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 Z); [ fsetdec | simpl_env; reflexivity ].
Qed.

(* tvar:=unit substitution for subtyping.  Tag context [Ψ] is untouched (tags,
   not tvars); [Γ] loses the substituted tvar; types are substituted.  Consis
   premises go through [d_consis_subst_tvar] with [ph := utyp_unit]. *)
Lemma d_sub_subst_unit : forall m Ψ Γ C B,
    Ψ ⨟ Γ ⊢[ m ] C ⊑ B ->
    forall Γ1 Γ2 X0,
      Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
      Ψ ⨟ (Γ1 ++ Γ2) ⊢[ m ]
        (subst_utyp_in_utyp utyp_unit X0 C) ⊑ (subst_btyp_in_btyp btyp_unit X0 B).
Proof.
  intros m Ψ Γ C B H. induction H; intros Γ1 Γ2 X0 Heq; subst; simpl.
  - (* infer *)
    apply d_sub__infer; [ | apply is_styp_subst_unit; assumption | assumption ].
    change btyp_unit with (utyp_to_btyp utyp_unit).
    eapply d_consis_subst_tvar;
      [ eassumption | reflexivity | apply d_wf_utyp__unit | apply is_ttyp__unit ].
  - (* check *)
    apply d_sub__check;
      [ apply guarded_utyp_subst_unit; assumption
      | apply guarded_btyp_subst_unit; assumption
      | change btyp_unit with (utyp_to_btyp utyp_unit);
        eapply d_consis_subst_tvar;
          [ eassumption | reflexivity | apply d_wf_utyp__unit | apply is_ttyp__unit ]
      | apply is_ityp_subst_unit; assumption ].
  - (* forall_r *)
    apply d_sub__forall_r with (L := L `union` dom (Γ1 ++ Γ2) `union` singleton X0).
    + change (btyp_all_inh (subst_btyp_in_btyp btyp_unit X0 B))
        with (subst_btyp_in_btyp btyp_unit X0 (btyp_all_inh B)).
      apply is_ityp_subst_unit; assumption.
    + intros Z HZ.
      rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
        by (first [ apply lc_btyp_unit | fsetdec ]).
      rewrite_env (((Z ~ dbind_tvar) ++ Γ1) ++ Γ2).
      eapply (H1 Z); [ fsetdec | simpl_env; reflexivity ].
  - (* arg *)
    eapply d_sub__arg.
    + change btyp_unit with (utyp_to_btyp utyp_unit).
      eapply d_consis_subst_tvar;
        [ eassumption | reflexivity | apply d_wf_utyp__unit | apply is_ttyp__unit ].
    + eapply IHd_sub; reflexivity.
    + assumption.
  - (* forall_l_tagged *)
    eapply d_sub__forall_l_tagged with
      (Ψ' := Ψ') (ph := subst_utyp_in_utyp utyp_unit X0 ph);
      [ assumption | assumption
      | apply d_tags_subst_unit; assumption
      | eapply d_wf_utyp_subst_unit; [ eassumption | reflexivity ]
      | apply is_ttyp_subst_unit; assumption
      | ].
    rewrite <- subst_utyp_in_utyp_open_utyp_wrt_utyp by (apply lc_utyp_unit).
    eapply IHd_sub; reflexivity.
  - (* forall_l_untagged *)
    eapply d_sub__forall_l_untagged with
      (Ψ' := Ψ') (ph := subst_utyp_in_utyp utyp_unit X0 ph);
      [ assumption | assumption
      | apply d_tags_subst_unit; assumption
      | eapply d_wf_utyp_subst_unit; [ eassumption | reflexivity ]
      | apply is_ttyp_subst_unit; assumption
      | ].
    rewrite <- subst_utyp_in_utyp_open_utyp_wrt_utyp by (apply lc_utyp_unit).
    eapply IHd_sub; reflexivity.
Qed.

(* [pskl_to_bskl_syn] commutes with tvar:=unit (companion to the existing
   [pskl_to_bskl_inh_subst_unit]). *)
Lemma pskl_to_bskl_syn_subst_unit : forall P X,
    subst_bskl_in_bskl bskl_unit X (pskl_to_bskl_syn P)
    = pskl_to_bskl_syn (subst_pskl_in_pskl pskl_unit X P).
Proof.
  induction P; intros X; simpl; try reflexivity;
    try (rewrite IHP1, IHP2; reflexivity); try (rewrite IHP; reflexivity).
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; reflexivity.
Qed.

(* tvar:=unit substitution for skeleton refinement (mirrors
   [d_refine_syn_strengthen], but substitutes the var instead of requiring it
   absent).  [Δs]/[Δi] are refinement-local ∀-vars, disjoint from the Γ-tvar
   [X0], so they are untouched. *)
Lemma d_refine_syn_subst_unit : forall Γ Δs Δi Q P,
    Γ ⨟ Δs ⨟ Δi ⊢ᵣ Q ⊳ P ->
    forall Γ1 X0 Γ2, Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
    (Γ1 ++ Γ2) ⨟ Δs ⨟ Δi ⊢ᵣ
      (subst_bskl_in_bskl bskl_unit X0 Q) ⊳ (subst_bskl_in_bskl bskl_unit X0 P).
Proof.
  intros Γ Δs Δi Q P H. induction H; intros Γ1 X0 Γ2 Heq; subst; simpl.
  - apply d_refine_syn__unit.
  - match goal with |- context [ if ?d then _ else _ ] => destruct d end.
    + apply d_refine_syn__unit.
    + apply d_refine_syn__var. destruct H as [HS | [HI | Hb]];
        [ left; assumption | right; left; assumption | right; right; analyze_binds Hb ].
  - apply d_refine_syn__arrow;
      [ eapply IHd_refine_syn1 | eapply IHd_refine_syn2 ]; reflexivity.
  - apply d_refine_syn__all with (L := L `union` dom (Γ1 ++ Γ2) `union` {{X0}}).
    intros Z HZ.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var
      by (first [ apply lc_bskl_unit | fsetdec ]).
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var
      by (first [ apply lc_bskl_unit | fsetdec ]).
    eapply (H0 Z); [ fsetdec | reflexivity ].
  - rewrite pskl_to_bskl_syn_subst_unit. apply d_refine_syn__hole.
    eapply d_wf_pskl_subst_unit; [ eassumption | reflexivity ].
  - apply d_refine_syn__tophole_remove. eapply IHd_refine_syn; reflexivity.
  - apply d_refine_syn__tophole_fill with (L := L `union` dom (Γ1 ++ Γ2) `union` {{X0}}).
    intros Z HZ.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var
      by (first [ apply lc_bskl_unit | fsetdec ]).
    eapply (H0 Z); [ fsetdec | reflexivity ].
  - apply d_refine_syn__tophole_keep;
      [ apply guarded_bskl_subst_unit; assumption | eapply IHd_refine_syn; reflexivity ].
Qed.

(* ===================================================================== *)
(*  Direct tvar-strengthening for [d_pat] and [d_sd_typing].             *)
(*                                                                         *)
(*  Conclusion-only tvar-strengthening is FALSE for the subtyping         *)
(*  judgments ([d_sub] / [d_pat_sub] may instantiate a [forall_l] witness *)
(*  with the dropped var), so those embedded premises are discharged by   *)
(*  the [*_subst_unit] lemmas followed by a "subst-is-identity-when-fresh" *)
(*  rewrite ([*_fresh_eq]).  Every OTHER judgment strengthens directly.    *)
(* ===================================================================== *)

(* [btyp_to_bskl] / [bskl_to_uskl] preserve free tvars (only repaint). *)
Lemma ftvar_btyp_to_bskl : forall B,
    ftvar_in_bskl (btyp_to_bskl B) = ftvar_in_btyp B.
Proof.
  induction B; simpl; try reflexivity;
    try (rewrite IHB1, IHB2; reflexivity); try (rewrite IHB; reflexivity).
Qed.

Lemma ftvar_bskl_to_uskl : forall Q,
    ftvar_in_uskl (bskl_to_uskl Q) = ftvar_in_bskl Q.
Proof.
  induction Q; simpl; try reflexivity;
    try (rewrite IHQ1, IHQ2; reflexivity); try (rewrite IHQ; reflexivity).
Qed.

(* [bskl_to_uskl] commutes with the tvar→unit substitution (the [d_pat_sub]
   premise of [d_pat__sub] is over the [uskl]-erasure of the syn skeleton). *)
Lemma bskl_to_uskl_subst_unit : forall Q X,
    subst_bskl_in_uskl uskl_unit X (bskl_to_uskl Q)
    = bskl_to_uskl (subst_bskl_in_bskl bskl_unit X Q).
Proof.
  induction Q; intros X; simpl; try reflexivity;
    try (rewrite IHQ1, IHQ2; reflexivity); try (rewrite IHQ; reflexivity).
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; reflexivity.
Qed.

(** A context is [tvar_clean] for [X0] when no term-/skl-binding carries [X0]
    in its type.  (tvar bindings carry no type, so they are irrelevant.)  This
    is the invariant that lets a term-var lookup survive dropping [X0]. *)
Definition tvar_clean (X0 : atom) (Γ : list (atom * dbind)) : Prop :=
  (forall x A, binds x (dbind_typ A) Γ -> X0 `notin` ftvar_in_ptyp A) /\
  (forall x P, binds x (dbind_skl P) Γ -> X0 `notin` ftvar_in_pskl P).

Lemma tvar_clean_cons_typ : forall X0 x A Γ,
    X0 `notin` ftvar_in_ptyp A -> tvar_clean X0 Γ ->
    tvar_clean X0 ((x ~ dbind_typ A) ++ Γ).
Proof.
  intros X0 x A Γ HA [Ht Hs]. split; intros y T Hb; analyze_binds Hb.
  - inversion BindsTacVal; subst; assumption.
  - eapply Ht; eassumption.
  - eapply Hs; eassumption.
Qed.

Lemma tvar_clean_cons_skl : forall X0 x P Γ,
    X0 `notin` ftvar_in_pskl P -> tvar_clean X0 Γ ->
    tvar_clean X0 ((x ~ dbind_skl P) ++ Γ).
Proof.
  intros X0 x P Γ HP [Ht Hs]. split; intros y T Hb; analyze_binds Hb.
  - eapply Ht; eassumption.
  - inversion BindsTacVal; subst; assumption.
  - eapply Hs; eassumption.
Qed.

(** Paintings commute with the [X0 := unit] substitution (the unit witness on
    each side is the unit of that sort).  Needed because the embedded skeletons /
    types in a [d_pat] / [d_sd_typing] derivation are produced by paintings, and
    we strengthen by substituting [X0 := unit]. *)
Lemma ptyp_to_pskl_subst_unit : forall A X,
    subst_pskl_in_pskl pskl_unit X (ptyp_to_pskl A)
    = ptyp_to_pskl (subst_ptyp_in_ptyp ptyp_unit X A).
Proof.
  induction A; intros X; simpl; try reflexivity;
    try (rewrite IHA1, IHA2; reflexivity); try (rewrite IHA; reflexivity).
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; reflexivity.
Qed.

Lemma ptyp_to_btyp_syn_subst_unit : forall A X,
    subst_btyp_in_btyp btyp_unit X (ptyp_to_btyp_syn A)
    = ptyp_to_btyp_syn (subst_ptyp_in_ptyp ptyp_unit X A).
Proof.
  induction A; intros X; simpl; try reflexivity;
    try (rewrite IHA1, IHA2; reflexivity); try (rewrite IHA; reflexivity).
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; reflexivity.
Qed.

Lemma ptyp_to_btyp_inh_subst_unit : forall A X,
    subst_btyp_in_btyp btyp_unit X (ptyp_to_btyp_inh A)
    = ptyp_to_btyp_inh (subst_ptyp_in_ptyp ptyp_unit X A).
Proof.
  induction A; intros X; simpl; try reflexivity;
    try (rewrite IHA1, IHA2; reflexivity); try (rewrite IHA; reflexivity).
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; reflexivity.
Qed.

Lemma ptyp_to_utyp_syn_subst_unit : forall A X,
    subst_utyp_in_utyp utyp_unit X (ptyp_to_utyp_syn A)
    = ptyp_to_utyp_syn (subst_ptyp_in_ptyp ptyp_unit X A).
Proof.
  induction A; intros X; simpl; try reflexivity;
    try (rewrite IHA1, IHA2; reflexivity); try (rewrite IHA; reflexivity).
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; reflexivity.
Qed.

Lemma btyp_to_bskl_subst_unit : forall B X,
    subst_bskl_in_bskl bskl_unit X (btyp_to_bskl B)
    = btyp_to_bskl (subst_btyp_in_btyp btyp_unit X B).
Proof.
  induction B; intros X; simpl; try reflexivity;
    try (rewrite IHB1, IHB2; reflexivity); try (rewrite IHB; reflexivity).
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; reflexivity.
Qed.

Lemma btyp_to_ptyp_subst_unit : forall B X,
    subst_ptyp_in_ptyp ptyp_unit X (btyp_to_ptyp B)
    = btyp_to_ptyp (subst_btyp_in_btyp btyp_unit X B).
Proof.
  induction B; intros X; simpl; try reflexivity;
    try (rewrite IHB1, IHB2; reflexivity); try (rewrite IHB; reflexivity).
  - match goal with |- context [ if ?b then _ else _ ] => destruct b end; reflexivity.
Qed.

(* [is_value] / [is_base_term] are stable under any [ptyp]-substitution. *)
Lemma is_value_subst_ptyp : forall A X e,
    is_value e -> is_value (subst_ptyp_in_exp A X e).
Proof.
  intros A X e H. induction H; simpl; constructor; assumption.
Qed.

Lemma is_base_term_subst_ptyp : forall A X e,
    is_base_term e -> is_base_term (subst_ptyp_in_exp A X e).
Proof.
  intros A X e H. induction H; simpl; constructor.
Qed.


(* ===================================================================== *)
(*  Tvar-binding congruence for the auxiliary judgments.                   *)
(*                                                                         *)
(*  The [*_subst_unit] lemmas above strengthen a [d_pat] / [d_sd_typing]  *)
(*  derivation by [X0 := unit], but their embedded subtyping / wf premises *)
(*  ([d_sub], [d_pat_sub], [d_refine_syn], [d_wf_*]) come back over the    *)
(*  context [Γ1 ++ Γ2], whereas [d_pat_subst_unit] / [d_sd_typing_subst_unit]  *)
(*  must place every binding over the MAPPED context [map (subst_unit) Γ1 ++ Γ2].*)
(*  All of these judgments consult [Γ] only through [binds X dbind_tvar Γ] *)
(*  (tvar bindings carry no type), and the map ([subst_unit_dbind]) is the *)
(*  identity on tvar bindings — so swapping [Γ1 ++ Γ2] for the mapped      *)
(*  context is sound.  [same_tvar] captures exactly that agreement.        *)
(* ===================================================================== *)

Definition same_tvar (Γ Γ' : list (atom * dbind)) : Prop :=
  forall X, binds X dbind_tvar Γ <-> binds X dbind_tvar Γ'.

Lemma same_tvar_cons : forall Γ Γ' a,
    same_tvar Γ Γ' -> same_tvar (a ++ Γ) (a ++ Γ').
Proof.
  intros Γ Γ' a H X. split; intro Hb; apply binds_app_iff in Hb; apply binds_app_iff;
    (destruct Hb as [Hb | Hb]; [ left; assumption | right; apply H; assumption ]).
Qed.

Lemma d_wf_ptyp_same_tvar : forall Γ A,
    Γ ⊢ₚ A -> forall Γ', same_tvar Γ Γ' -> Γ' ⊢ₚ A.
Proof.
  intros Γ A H. induction H; intros Γ' Hst.
  - apply d_wf_ptyp__unit.
  - apply d_wf_ptyp__var. apply Hst. assumption.
  - apply d_wf_ptyp__arrow; [ apply IHd_wf_ptyp1 | apply IHd_wf_ptyp2 ]; assumption.
  - apply d_wf_ptyp__all with (L := L). intros X HX.
    apply H0; [ assumption | apply same_tvar_cons; assumption ].
Qed.

Lemma d_wf_utyp_same_tvar : forall Γ C,
    Γ ⊢ᵤ C -> forall Γ', same_tvar Γ Γ' -> Γ' ⊢ᵤ C.
Proof.
  intros Γ C H. induction H; intros Γ' Hst.
  - apply d_wf_utyp__unit.
  - apply d_wf_utyp__var. apply Hst. assumption.
  - apply d_wf_utyp__arrow; [ apply IHd_wf_utyp1 | apply IHd_wf_utyp2 ]; assumption.
  - apply d_wf_utyp__all_syn with (L := L). intros X HX.
    apply H0; [ assumption | apply same_tvar_cons; assumption ].
  - apply d_wf_utyp__all_etag with (L := L). intros X HX.
    apply H0; [ assumption | apply same_tvar_cons; assumption ].
Qed.

Lemma d_wf_pskl_same_tvar : forall Ψ Γ P,
    Ψ ⨟ Γ ⊢ₚₛ P -> forall Γ', same_tvar Γ Γ' -> Ψ ⨟ Γ' ⊢ₚₛ P.
Proof.
  intros Ψ Γ P H. induction H; intros Γ' Hst.
  - apply d_wf_pskl__unit.
  - apply d_wf_pskl__var. destruct H as [HΨ | Hb]; [ left; assumption | right; apply Hst; assumption ].
  - apply d_wf_pskl__arrow; [ apply IHd_wf_pskl1 | apply IHd_wf_pskl2 ]; assumption.
  - apply d_wf_pskl__all with (L := L). intros X HX.
    apply H0; assumption.
  - apply d_wf_pskl__hole.
  - apply d_wf_pskl__tophole; [ assumption | apply IHd_wf_pskl; assumption ].
Qed.

Lemma d_wf_uskl_same_tvar : forall Ψ Γ R,
    Ψ ⨟ Γ ⊢ᵤₛ R -> forall Γ', same_tvar Γ Γ' -> Ψ ⨟ Γ' ⊢ᵤₛ R.
Proof.
  intros Ψ Γ R H. induction H; intros Γ' Hst.
  - apply d_wf_uskl__unit.
  - apply d_wf_uskl__var. destruct H as [HΨ | Hb]; [ left; assumption | right; apply Hst; assumption ].
  - apply d_wf_uskl__arrow; [ apply IHd_wf_uskl1 | apply IHd_wf_uskl2 ]; assumption.
  - apply d_wf_uskl__all_syn with (L := L). intros X HX.
    apply H0; assumption.
  - apply d_wf_uskl__all_etag with (L := L). intros X HX.
    apply H0; assumption.
  - apply d_wf_uskl__hole.
  - apply d_wf_uskl__tophole; [ assumption | apply IHd_wf_uskl; assumption ].
  - apply d_wf_uskl__holeg.
  - apply d_wf_uskl__topholeg; [ assumption | apply IHd_wf_uskl; assumption ].
Qed.

Lemma d_consis_same_tvar : forall Ψ Γ C B,
    Ψ ⨟ Γ ⊨ C ≈ B -> forall Γ', same_tvar Γ Γ' -> Ψ ⨟ Γ' ⊨ C ≈ B.
Proof.
  intros Ψ Γ C B H. induction H; intros Γ' Hst.
  - apply d_consis__unit; assumption.
  - apply d_consis__var; [ apply Hst; assumption | assumption ].
  - eapply d_consis__arrow; [ apply IHd_consis1 | apply IHd_consis2 | eassumption ]; assumption.
  - apply d_consis__forall_inh_tagged with (L := L) (Ψ0 := Ψ0); [ | assumption ].
    intros X HX. apply H0; [ assumption | apply same_tvar_cons; assumption ].
  - apply d_consis__forall_inh_untagged with (L := L). intros X HX.
    apply H0; [ assumption | apply same_tvar_cons; assumption ].
  - apply d_consis__forall_syn_tagged with (L := L). intros X HX.
    apply H0; [ assumption | apply same_tvar_cons; assumption ].
  - apply d_consis__forall_syn with (L := L). intros X HX.
    apply H0; [ assumption | apply same_tvar_cons; assumption ].
Qed.

Lemma d_pat_consis_same_tvar : forall Δ Γ R Q,
    Δ ⨟ Γ ⊨ₛ R ≈ Q -> forall Γ', same_tvar Γ Γ' -> Δ ⨟ Γ' ⊨ₛ R ≈ Q.
Proof.
  intros Δ Γ R Q H. induction H; intros Γ' Hst.
  - apply d_pat_consis__unit; assumption.
  - apply d_pat_consis__var; [ assumption | apply Hst; assumption ].
  - eapply d_pat_consis__arrow; [ apply IHd_pat_consis1 | apply IHd_pat_consis2 | eassumption ]; assumption.
  - apply d_pat_consis__forall_inh_tagged with (L := L) (Δ0 := Δ0); [ | assumption ].
    intros X HX. apply H0; [ assumption | apply same_tvar_cons; assumption ].
  - apply d_pat_consis__forall_inh_untagged with (L := L). intros X HX.
    apply H0; [ assumption | apply same_tvar_cons; assumption ].
  - apply d_pat_consis__forall_syn_tagged with (L := L). intros X HX.
    apply H0; [ assumption | apply same_tvar_cons; assumption ].
  - apply d_pat_consis__forall_syn with (L := L). intros X HX.
    apply H0; [ assumption | apply same_tvar_cons; assumption ].
  - apply d_pat_consis__ghostg; assumption.
  - apply d_pat_consis__topholeg with (Δ0 := Δ0);
      [ apply IHd_pat_consis; assumption | eassumption ].
  - apply d_pat_consis__hole; [ assumption | eapply d_wf_pskl_same_tvar; eassumption ].
  - apply d_pat_consis__tophole; apply IHd_pat_consis; assumption.
  - apply d_pat_consis__tophole_inh with (L := L). intros X HX.
    apply H0; [ assumption | apply same_tvar_cons; assumption ].
  - apply d_pat_consis__tophole_drop. apply IHd_pat_consis; assumption.
Qed.

Lemma d_sub_same_tvar : forall m Ψ Γ C B,
    Ψ ⨟ Γ ⊢[ m ] C ⊑ B -> forall Γ', same_tvar Γ Γ' -> Ψ ⨟ Γ' ⊢[ m ] C ⊑ B.
Proof.
  intros m Ψ Γ C B H. induction H; intros Γ' Hst.
  - apply d_sub__infer; [ eapply d_consis_same_tvar; eassumption | assumption | assumption ].
  - apply d_sub__check; [ assumption | assumption | eapply d_consis_same_tvar; eassumption | assumption ].
  - apply d_sub__forall_r with (L := L); [ assumption | ]. intros X HX.
    apply H1; [ assumption | apply same_tvar_cons; assumption ].
  - eapply d_sub__arg; [ eapply d_consis_same_tvar; eassumption | apply IHd_sub; eassumption | eassumption ].
  - eapply d_sub__forall_l_tagged;
      [ eassumption | eassumption | eassumption
      | eapply d_wf_utyp_same_tvar; eassumption | assumption | apply IHd_sub; assumption ].
  - eapply d_sub__forall_l_untagged;
      [ eassumption | eassumption | eassumption
      | eapply d_wf_utyp_same_tvar; eassumption | assumption | apply IHd_sub; assumption ].
Qed.

Lemma d_pat_sub_same_tvar : forall m Δ Γ R Q,
    Δ ⨟ Γ ⊢ₛ[ m ] R ⊑ Q -> forall Γ', same_tvar Γ Γ' -> Δ ⨟ Γ' ⊢ₛ[ m ] R ⊑ Q.
Proof.
  intros m Δ Γ R Q H. induction H; intros Γ' Hst.
  - apply d_pat_sub__infer; [ assumption | eapply d_pat_consis_same_tvar; eassumption | assumption ].
  - apply d_pat_sub__univ_ghost_r;
      [ assumption | assumption | assumption | assumption | eapply d_pat_consis_same_tvar; eassumption ].
  - eapply d_pat_sub__arg; [ eapply d_pat_consis_same_tvar; eassumption | apply IHd_pat_sub; eassumption | eassumption ].
  - eapply d_pat_sub__forall_l_tagged;
      [ eassumption | eassumption | eassumption
      | eapply d_wf_uskl_same_tvar; eassumption | assumption | apply IHd_pat_sub; assumption ].
  - eapply d_pat_sub__forall_l_untagged;
      [ eassumption | eassumption | eassumption
      | eapply d_wf_uskl_same_tvar; eassumption | assumption | apply IHd_pat_sub; assumption ].
  - apply d_pat_sub__ghost; [ assumption | eapply d_wf_pskl_same_tvar; eassumption ].
  - apply d_pat_sub__univ_ghost_l; [ assumption | apply IHd_pat_sub; assumption ].
  - apply d_pat_sub__ghostg; assumption.
  - apply d_pat_sub__univ_ghost_lg; [ assumption | apply IHd_pat_sub; assumption ].
Qed.

Lemma d_refine_syn_same_tvar : forall Γ Δs Δi Q P,
    Γ ⨟ Δs ⨟ Δi ⊢ᵣ Q ⊳ P -> forall Γ', same_tvar Γ Γ' -> Γ' ⨟ Δs ⨟ Δi ⊢ᵣ Q ⊳ P.
Proof.
  intros Γ Δs Δi Q P H. induction H; intros Γ' Hst.
  - apply d_refine_syn__unit.
  - apply d_refine_syn__var. destruct H as [HS | [HI | Hb]];
      [ left; assumption | right; left; assumption | right; right; apply Hst; assumption ].
  - apply d_refine_syn__arrow; [ apply IHd_refine_syn1 | apply IHd_refine_syn2 ]; assumption.
  - apply d_refine_syn__all with (L := L). intros X HX. apply H0; assumption.
  - apply d_refine_syn__hole. eapply d_wf_pskl_same_tvar; eassumption.
  - apply d_refine_syn__tophole_remove. apply IHd_refine_syn; assumption.
  - apply d_refine_syn__tophole_fill with (L := L). intros X HX. apply H0; assumption.
  - apply d_refine_syn__tophole_keep; [ assumption | apply IHd_refine_syn; assumption ].
Qed.

(* ===================================================================== *)
(*  [X0 := unit] context-substitution for [d_pat] / [d_sd_typing].       *)
(* ===================================================================== *)

Definition subst_unit_dbind (X0 : atom) (d : dbind) : dbind :=
  match d with
  | dbind_tvar => dbind_tvar
  | dbind_typ A => dbind_typ (subst_ptyp_in_ptyp ptyp_unit X0 A)
  | dbind_skl P => dbind_skl (subst_pskl_in_pskl pskl_unit X0 P)
  end.

Lemma map_subst_unit_dbind_cons : forall x d X0 Γ1,
    (x ~ subst_unit_dbind X0 d) ++ map (subst_unit_dbind X0) Γ1
    = map (subst_unit_dbind X0) ((x ~ d) ++ Γ1).
Proof. intros. simpl_env. reflexivity. Qed.

(* The mapped context [map (subst_unit_dbind X0) Γ1 ++ Γ2] has the SAME tvar
   bindings as [Γ1 ++ Γ2] (the map fixes tvar bindings; [Γ2] is untouched). *)
Lemma same_tvar_map_subst_unit : forall X0 Γ1 Γ2,
    same_tvar (Γ1 ++ Γ2) (map (subst_unit_dbind X0) Γ1 ++ Γ2).
Proof.
  intros X0 Γ1 Γ2 X. split; intro Hb; apply binds_app_iff in Hb; apply binds_app_iff;
    destruct Hb as [Hb | Hb].
  - left. change dbind_tvar with (subst_unit_dbind X0 dbind_tvar). apply binds_map_2. assumption.
  - right. assumption.
  - left. apply binds_map_3 in Hb as [b [Heq Hb']]. destruct b; inversion Heq; subst.
    assumption.
  - right. assumption.
Qed.

(* binds for a term-binding survives the map+drop, with its type substituted. *)
Lemma binds_typ_subst_unit_dbind : forall x A X0 Γ1 Γ2,
    binds x (dbind_typ A) (Γ1 ++ Γ2) -> tvar_clean X0 Γ2 ->
    binds x (dbind_typ (subst_ptyp_in_ptyp ptyp_unit X0 A))
          (map (subst_unit_dbind X0) Γ1 ++ Γ2).
Proof.
  intros x A X0 Γ1 Γ2 Hb [Ht Hs]. apply binds_app_iff in Hb. destruct Hb as [Hb | Hb].
  - apply binds_app_2.
    change (dbind_typ (subst_ptyp_in_ptyp ptyp_unit X0 A))
      with (subst_unit_dbind X0 (dbind_typ A)).
    apply binds_map_2. assumption.
  - apply binds_app_3.
    rewrite (subst_ptyp_in_ptyp_fresh_eq _ _ _ (Ht _ _ Hb)). assumption.
Qed.

Lemma binds_skl_subst_unit_dbind : forall x P X0 Γ1 Γ2,
    binds x (dbind_skl P) (Γ1 ++ Γ2) -> tvar_clean X0 Γ2 ->
    binds x (dbind_skl (subst_pskl_in_pskl pskl_unit X0 P))
          (map (subst_unit_dbind X0) Γ1 ++ Γ2).
Proof.
  intros x P X0 Γ1 Γ2 Hb [Ht Hs]. apply binds_app_iff in Hb. destruct Hb as [Hb | Hb].
  - apply binds_app_2.
    change (dbind_skl (subst_pskl_in_pskl pskl_unit X0 P))
      with (subst_unit_dbind X0 (dbind_skl P)).
    apply binds_map_2. assumption.
  - apply binds_app_3.
    rewrite (subst_pskl_in_pskl_fresh_eq _ _ _ (Hs _ _ Hb)). assumption.
Qed.

(* Map-context [d_wf_ptyp] strengthening: combine the existing drop-context
   [d_wf_ptyp_subst_tvar]-style substitution with the [same_tvar] swap to the
   mapped context.  Done from scratch via [d_wf_ptyp_of_lc_ftvar]. *)
Lemma d_wf_ptyp_subst_unit_ctx : forall Γ A,
    Γ ⊢ₚ A -> forall Γ1 X0 Γ2, Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
    (map (subst_unit_dbind X0) Γ1 ++ Γ2) ⊢ₚ (subst_ptyp_in_ptyp ptyp_unit X0 A).
Proof.
  intros Γ A H Γ1 X0 Γ2 Heq.
  apply d_wf_ptyp_of_lc_ftvar.
  - apply subst_ptyp_in_ptyp_lc_ptyp; [ eapply d_wf_ptyp_lc; eassumption | apply lc_ptyp_unit ].
  - intros Y HY.
    pose proof (ftvar_in_ptyp_subst_ptyp_in_ptyp_upper A ptyp_unit X0) as Hup.
    simpl in Hup.
    assert (HYA : Y `in` ftvar_in_ptyp A) by (clear - HY Hup; fsetdec).
    assert (HYne : Y <> X0).
    { clear - HY Hup. intro; subst. assert (X0 `notin` (remove X0 (ftvar_in_ptyp A))) by fsetdec. fsetdec. }
    assert (Hbnd : binds Y dbind_tvar Γ) by (eapply d_wf_ptyp_ftvar; eassumption).
    subst Γ.
    (* Y is a tvar of [Γ1 ++ X0 :: Γ2], distinct from X0 → survives the map. *)
    assert (Hbnd' : binds Y dbind_tvar (Γ1 ++ Γ2)).
    { analyze_binds Hbnd. }
    eapply (same_tvar_map_subst_unit X0 Γ1 Γ2). assumption.
Qed.

Lemma d_pat_subst_unit : forall m Γ e R,
    Γ ⊢[ m ] e ⇨ R ->
    forall Γ1 X0 Γ2, Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
    tvar_clean X0 Γ2 ->
    (map (subst_unit_dbind X0) Γ1 ++ Γ2) ⊢[ m ]
      (subst_ptyp_in_exp ptyp_unit X0 e) ⇨ (subst_bskl_in_bskl bskl_unit X0 R).
Proof.
  intros m Γ e R H. induction H; intros Γ1 X0 Γ2 Heq Hclean; subst; simpl.
  - apply d_pat__unit.
  - (* var: lookup survives, painted output repaints. *)
    rewrite pskl_to_bskl_syn_subst_unit.
    destruct d as [ | A | P0 ]; simpl in H0.
    + discriminate.
    + injection H0 as H0. subst P. rewrite ptyp_to_pskl_subst_unit.
      assert (Hb : binds x (dbind_typ A) (Γ1 ++ Γ2)) by (analyze_binds H).
      eapply d_pat__var;
        [ apply binds_typ_subst_unit_dbind; eassumption | reflexivity ].
    + injection H0 as H0. subst P.
      assert (Hb : binds x (dbind_skl P0) (Γ1 ++ Γ2)) by (analyze_binds H).
      eapply d_pat__var;
        [ apply binds_skl_subst_unit_dbind; eassumption | reflexivity ].
  - (* anno *)
    rewrite pskl_to_bskl_syn_subst_unit. rewrite ptyp_to_pskl_subst_unit.
    apply d_pat__anno. eapply d_wf_ptyp_subst_unit_ctx; [ eassumption | reflexivity ].
  - (* sub: embedded [d_pat_sub] over [Γ1++Γ2] → swap to mapped context. *)
    eapply d_pat__sub.
    + apply is_base_term_subst_ptyp. assumption.
    + rewrite <- pskl_to_bskl_syn_subst_unit. eapply IHd_pat; [ reflexivity | assumption ].
    + rewrite <- pskl_to_bskl_syn_subst_unit. rewrite <- bskl_to_uskl_subst_unit.
      eapply d_pat_sub_same_tvar;
        [ eapply d_pat_sub_subst_unit; [ eassumption | reflexivity ]
        | apply same_tvar_map_subst_unit ].
  - (* freeze *)
    rewrite pskl_to_bskl_syn_subst_unit.
    apply d_pat__freeze. rewrite <- pskl_to_bskl_syn_subst_unit.
    eapply IHd_pat; [ reflexivity | assumption ].
  - (* abs (cofinite) *)
    rewrite pskl_to_bskl_inh_subst_unit.
    apply d_pat__abs with (L := L `union` {{X0}}) (P := subst_pskl_in_pskl pskl_unit X0 P).
    + assumption.
    + eapply d_wf_pskl_same_tvar;
        [ eapply d_wf_pskl_subst_unit; [ eassumption | reflexivity ]
        | apply same_tvar_map_subst_unit ].
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
      rewrite_env (((x ~ subst_unit_dbind X0 (dbind_skl P)) ++ map (subst_unit_dbind X0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H2 x ltac:(fsetdec) ((x ~ dbind_skl P) ++ Γ1) X0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  - (* abs_anno (cofinite) *)
    rewrite btyp_to_bskl_subst_unit.
    eapply d_pat__abs_anno with (L := L `union` {{X0}}).
    + assumption.
    + eapply d_wf_ptyp_subst_unit_ctx; [ eassumption | reflexivity ].
    + symmetry. apply btyp_to_ptyp_subst_unit.
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
      rewrite_env (((x ~ subst_unit_dbind X0 (dbind_typ (btyp_to_ptyp B))) ++ map (subst_unit_dbind X0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H3 x ltac:(fsetdec) ((x ~ dbind_typ (btyp_to_ptyp B)) ++ Γ1) X0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  - (* app *)
    eapply d_pat__app.
    + rewrite <- pskl_to_bskl_syn_subst_unit. eapply IHd_pat1; [ reflexivity | assumption ].
    + rewrite <- pskl_to_bskl_inh_subst_unit.
      eapply d_refine_syn_same_tvar;
        [ eapply d_refine_syn_subst_unit; [ eassumption | reflexivity ]
        | apply same_tvar_map_subst_unit ].
    + change (bskl_arrow (subst_bskl_in_bskl bskl_unit X0 Q1) (subst_bskl_in_bskl bskl_unit X0 Q2))
        with (subst_bskl_in_bskl bskl_unit X0 (bskl_arrow Q1 Q2)).
      eapply IHd_pat2; [ reflexivity | assumption ].
  - (* abs_check (cofinite) *)
    rewrite pskl_to_bskl_syn_subst_unit.
    apply d_pat__abs_check with (L := L `union` {{X0}}) (P := subst_pskl_in_pskl pskl_unit X0 P).
    intros x Hx.
    rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
    rewrite_env (((x ~ subst_unit_dbind X0 (dbind_skl pskl_hole)) ++ map (subst_unit_dbind X0) Γ1) ++ Γ2).
    rewrite map_subst_unit_dbind_cons.
    rewrite <- pskl_to_bskl_syn_subst_unit.
    eapply (H0 x ltac:(fsetdec) ((x ~ dbind_skl pskl_hole) ++ Γ1) X0 Γ2);
      [ simpl_env; reflexivity | assumption ].
  - (* abs_anno_check (cofinite) *)
    rewrite btyp_to_bskl_subst_unit. rewrite ptyp_to_btyp_syn_subst_unit.
    rewrite pskl_to_bskl_syn_subst_unit.
    apply d_pat__abs_anno_check with (L := L `union` {{X0}})
      (A := subst_ptyp_in_ptyp ptyp_unit X0 A) (P := subst_pskl_in_pskl pskl_unit X0 P).
    + eapply d_wf_ptyp_subst_unit_ctx; [ eassumption | reflexivity ].
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
      rewrite_env (((x ~ subst_unit_dbind X0 (dbind_typ A)) ++ map (subst_unit_dbind X0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      rewrite <- pskl_to_bskl_syn_subst_unit.
      eapply (H1 x ltac:(fsetdec) ((x ~ dbind_typ A) ++ Γ1) X0 Γ2);
        [ simpl_env; reflexivity | assumption ].
Qed.

(* [skmod_ty] is the colour/mode discipline on the type only; it depends on the
   type via [is_styp] / [is_ityp], both preserved by [X0 := unit]. *)
Lemma skmod_ty_subst_unit : forall B m X0,
    skmod_ty B m -> skmod_ty (subst_btyp_in_btyp btyp_unit X0 B) m.
Proof.
  intros B m X0 H. induction H.
  - apply skmod_ty__ti. apply is_styp_subst_unit. assumption.
  - apply skmod_ty__tc. apply is_ityp_subst_unit. assumption.
  - simpl. apply skmod_ty__fn. assumption.
Qed.

Lemma d_sd_typing_subst_unit : forall m Γ e B,
    d_sd_typing m Γ e B ->
    forall Γ1 X0 Γ2, Γ = Γ1 ++ (X0 ~ dbind_tvar) ++ Γ2 ->
    tvar_clean X0 Γ2 ->
    d_sd_typing m (map (subst_unit_dbind X0) Γ1 ++ Γ2)
      (subst_ptyp_in_exp ptyp_unit X0 e) (subst_btyp_in_btyp btyp_unit X0 B).
Proof.
  intros m Γ e B H. induction H; intros Γ1 X0 Γ2 Heq Hclean; subst; simpl.
  - apply d_sd_typing__unit.
  - rewrite ptyp_to_btyp_syn_subst_unit.
    apply d_sd_typing__var.
    assert (Hb : binds x (dbind_typ A) (Γ1 ++ Γ2)) by (analyze_binds H).
    apply binds_typ_subst_unit_dbind; assumption.
  - rewrite ptyp_to_btyp_syn_subst_unit.
    apply d_sd_typing__anno. rewrite <- ptyp_to_btyp_inh_subst_unit.
    eapply IHd_sd_typing; [ reflexivity | assumption ].
  - (* sub *)
    eapply d_sd_typing__sub.
    + apply is_base_term_subst_ptyp. assumption.
    + rewrite <- ptyp_to_btyp_syn_subst_unit. eapply IHd_sd_typing; [ reflexivity | assumption ].
    + rewrite <- ptyp_to_utyp_syn_subst_unit.
      eapply d_sub_same_tvar;
        [ eapply d_sub_subst_unit; [ eassumption | reflexivity ]
        | apply same_tvar_map_subst_unit ].
  - (* freeze *)
    rewrite ptyp_to_btyp_inh_subst_unit.
    apply d_sd_typing__freeze. rewrite <- ptyp_to_btyp_syn_subst_unit.
    eapply IHd_sd_typing; [ reflexivity | assumption ].
  - (* abs_check_step *)
    apply d_sd_typing__abs_check_step with (L := L `union` {{X0}}).
    + pose proof (is_ityp_subst_unit (btyp_all_inh B) X0 H) as Hi. simpl in Hi. exact Hi.
    + intros X HX.
      rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (first [ apply lc_btyp_unit | fsetdec ]).
      rewrite_env (((X ~ subst_unit_dbind X0 dbind_tvar) ++ map (subst_unit_dbind X0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H1 X ltac:(fsetdec) ((X ~ dbind_tvar) ++ Γ1) X0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  - (* abs_check_base *)
    rewrite ptyp_to_btyp_inh_subst_unit.
    apply d_sd_typing__abs_check_base with (L := L `union` {{X0}}).
    + eapply d_wf_ptyp_subst_unit_ctx; [ eassumption | reflexivity ].
    + apply is_ityp_subst_unit. assumption.
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
      rewrite_env (((x ~ subst_unit_dbind X0 (dbind_typ A)) ++ map (subst_unit_dbind X0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H2 x ltac:(fsetdec) ((x ~ dbind_typ A) ++ Γ1) X0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  - (* abs_anno_check_step *)
    apply d_sd_typing__abs_anno_check_step with (L := L `union` {{X0}}).
    + pose proof (is_ityp_subst_unit (btyp_all_inh B) X0 H) as Hi. simpl in Hi. exact Hi.
    + intros X HX.
      rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (first [ apply lc_btyp_unit | fsetdec ]).
      rewrite_env (((X ~ subst_unit_dbind X0 dbind_tvar) ++ map (subst_unit_dbind X0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H1 X ltac:(fsetdec) ((X ~ dbind_tvar) ++ Γ1) X0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  - (* abs_anno_check_base *)
    rewrite ptyp_to_btyp_inh_subst_unit.
    apply d_sd_typing__abs_anno_check_base with (L := L `union` {{X0}}).
    + eapply d_wf_ptyp_subst_unit_ctx; [ eassumption | reflexivity ].
    + apply is_ityp_subst_unit. assumption.
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
      rewrite_env (((x ~ subst_unit_dbind X0 (dbind_typ A)) ++ map (subst_unit_dbind X0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H2 x ltac:(fsetdec) ((x ~ dbind_typ A) ++ Γ1) X0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  - (* abs (m ≠ tc, cofinite) *)
    rewrite ptyp_to_btyp_inh_subst_unit.
    apply d_sd_typing__abs with (L := L `union` {{X0}}).
    + assumption.
    + eapply d_wf_ptyp_subst_unit_ctx; [ eassumption | reflexivity ].
    + rewrite <- ptyp_to_btyp_inh_subst_unit.
      change (btyp_arrow (subst_btyp_in_btyp btyp_unit X0 (ptyp_to_btyp_inh A))
                         (subst_btyp_in_btyp btyp_unit X0 B))
        with (subst_btyp_in_btyp btyp_unit X0 (btyp_arrow (ptyp_to_btyp_inh A) B)).
      apply skmod_ty_subst_unit. assumption.
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
      rewrite_env (((x ~ subst_unit_dbind X0 (dbind_typ A)) ++ map (subst_unit_dbind X0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H3 x ltac:(fsetdec) ((x ~ dbind_typ A) ++ Γ1) X0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  - (* abs_anno (m ≠ tc, cofinite) *)
    apply d_sd_typing__abs_anno with (L := L `union` {{X0}})
      (B1 := subst_btyp_in_btyp btyp_unit X0 B1).
    + assumption.
    + eapply d_wf_ptyp_subst_unit_ctx; [ eassumption | reflexivity ].
    + symmetry. apply btyp_to_ptyp_subst_unit.
    + pose proof (skmod_ty_subst_unit (btyp_arrow B1 B2) m X0 H2) as Hsk. simpl in Hsk. exact Hsk.
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
      rewrite_env (((x ~ subst_unit_dbind X0 (dbind_typ (btyp_to_ptyp B1))) ++ map (subst_unit_dbind X0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H4 x ltac:(fsetdec) ((x ~ dbind_typ (btyp_to_ptyp B1)) ++ Γ1) X0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  - (* app *)
    eapply d_sd_typing__app.
    + rewrite <- pskl_to_bskl_syn_subst_unit.
      eapply d_pat_subst_unit; [ eassumption | reflexivity | assumption ].
    + rewrite <- btyp_to_bskl_subst_unit. rewrite <- pskl_to_bskl_inh_subst_unit.
      eapply d_refine_syn_same_tvar;
        [ eapply d_refine_syn_subst_unit; [ eassumption | reflexivity ]
        | apply same_tvar_map_subst_unit ].
    + change (btyp_arrow (subst_btyp_in_btyp btyp_unit X0 B1)
                         (subst_btyp_in_btyp btyp_unit X0 B2))
        with (subst_btyp_in_btyp btyp_unit X0 (btyp_arrow B1 B2)).
      eapply IHd_sd_typing1; [ reflexivity | assumption ].
    + rewrite <- btyp_to_ptyp_subst_unit. rewrite <- ptyp_to_btyp_inh_subst_unit.
      eapply IHd_sd_typing2; [ reflexivity | assumption ].
Qed.

(* ===================================================================== *)
(*  Completeness:  d_typing ⊆ d_sd_typing                                   *)
(* ===================================================================== *)

(** Free type-variables of all binding types in a context.  Used to pick a
    [∀]-var fresh enough that the context is [tvar_clean] for it (the [anno]
    base-term case of [forall_admissible] strengthens through it via
    [d_sd_typing_subst_unit], which needs the [∀]-var absent from the context's
    binding types). *)
Definition ftvar_in_dbind (d : dbind) : atoms :=
  match d with
  | dbind_tvar => empty
  | dbind_typ A => ftvar_in_ptyp A
  | dbind_skl P => ftvar_in_pskl P
  end.

Fixpoint ftvar_in_denv (Γ : list (atom * dbind)) : atoms :=
  match Γ with
  | nil => empty
  | (_, d) :: Γ' => ftvar_in_dbind d `union` ftvar_in_denv Γ'
  end.

Lemma ftvar_in_denv_binds_typ : forall x A Γ,
    binds x (dbind_typ A) Γ -> ftvar_in_ptyp A [<=] ftvar_in_denv Γ.
Proof.
  induction Γ as [ | [y d] Γ' IH ]; intros Hb; simpl.
  - analyze_binds Hb.
  - analyze_binds Hb.
    + simpl. fsetdec.
    + apply IH in BindsTac. fsetdec.
Qed.

Lemma ftvar_in_denv_binds_skl : forall x P Γ,
    binds x (dbind_skl P) Γ -> ftvar_in_pskl P [<=] ftvar_in_denv Γ.
Proof.
  induction Γ as [ | [y d] Γ' IH ]; intros Hb; simpl.
  - analyze_binds Hb.
  - analyze_binds Hb.
    + simpl. fsetdec.
    + apply IH in BindsTac. fsetdec.
Qed.

Lemma tvar_clean_fresh : forall X Γ,
    X `notin` ftvar_in_denv Γ -> tvar_clean X Γ.
Proof.
  intros X Γ HX. split; intros y T Hb.
  - apply ftvar_in_denv_binds_typ in Hb. fsetdec.
  - apply ftvar_in_denv_binds_skl in Hb. fsetdec.
Qed.

(* [ptyp_to_btyp_syn] is injective (it only repaints / structurally embeds);
   used to recover the unique synthesised source type of a base term. *)
Lemma ptyp_to_btyp_syn_inj : forall A A',
    ptyp_to_btyp_syn A = ptyp_to_btyp_syn A' -> A = A'.
Proof.
  induction A; intros A' Heq; destruct A'; simpl in Heq; try discriminate;
    inversion Heq; subst; try reflexivity.
  - f_equal; [ apply IHA1 | apply IHA2 ]; assumption.
  - f_equal. apply IHA. assumption.
Qed.

(* A Leibniz equality of atom-sets yields subset both ways (lets us thread the
   painting-ftvar equalities through [subset_trans] without setoid rewriting,
   which is awkward over the [atoms] setoid). *)
Lemma eq_subset : forall (s t : atoms), s = t -> s [<=] t.
Proof. intros s t Heq; subst; reflexivity. Qed.

(* Leibniz [=] form of [ftvar_in_btyp ∘ ptyp_to_btyp_syn] — the imported
   [ftvar_ptyp_to_btyp_syn] is the weaker [<=] variant (it shadows the [=] one
   from prop_wellformed); we need both inclusions here. *)
Lemma ftvar_paint_btyp_syn_eq : forall A,
    ftvar_in_btyp (ptyp_to_btyp_syn A) = ftvar_in_ptyp A.
Proof.
  induction A; simpl; try reflexivity;
    try (rewrite IHA1, IHA2; reflexivity); try (rewrite IHA; reflexivity).
Qed.

(* Consistency only relates types with the same free variables (it never
   instantiates), so [B]'s ftvars are bounded by [C]'s. *)
Lemma d_consis_ftvar_gen : forall Δ Γ C B,
    Δ ⨟ Γ ⊨ C ≈ B -> ftvar_in_btyp B [<=] ftvar_in_utyp C.
Proof.
  intros Δ Γ C B H. induction H; simpl; try fsetdec.
  - (* forall_inh_tagged *)
    pick fresh X for (L `union` ftvar_in_btyp B `union` ftvar_in_utyp C).
    specialize (H0 X ltac:(fsetdec)).
    pose proof (ftvar_in_btyp_open_btyp_wrt_btyp_lower B (btyp_var_f X)) as HL.
    pose proof (ftvar_in_utyp_open_utyp_wrt_utyp_upper C (utyp_var_f X)) as HU.
    simpl in HU. fsetdec.
  - (* forall_inh_untagged *)
    pick fresh X for (L `union` ftvar_in_btyp B `union` ftvar_in_utyp C).
    specialize (H0 X ltac:(fsetdec)).
    pose proof (ftvar_in_btyp_open_btyp_wrt_btyp_lower B (btyp_var_f X)) as HL.
    pose proof (ftvar_in_utyp_open_utyp_wrt_utyp_upper C (utyp_var_f X)) as HU.
    simpl in HU. fsetdec.
  - (* forall_syn_tagged *)
    pick fresh X for (L `union` ftvar_in_btyp B `union` ftvar_in_utyp C).
    specialize (H0 X ltac:(fsetdec)).
    pose proof (ftvar_in_btyp_open_btyp_wrt_btyp_lower B (btyp_var_f X)) as HL.
    pose proof (ftvar_in_utyp_open_utyp_wrt_utyp_upper C (utyp_var_f X)) as HU.
    simpl in HU. fsetdec.
  - (* forall_syn *)
    pick fresh X for (L `union` ftvar_in_btyp B `union` ftvar_in_utyp C).
    specialize (H0 X ltac:(fsetdec)).
    pose proof (ftvar_in_btyp_open_btyp_wrt_btyp_lower B (btyp_var_f X)) as HL.
    pose proof (ftvar_in_utyp_open_utyp_wrt_utyp_upper C (utyp_var_f X)) as HU.
    simpl in HU. fsetdec.
Qed.

(* A [ti]-synthesised BASE term's type mentions only the context's binding-type
   ftvars and the term's own ftvars — no spurious tvars (no [∀] instantiation at
   [ti]: [Sub] there is [Infer], which keeps variables).  This lets us choose a
   fresh [∀]-var absent from the synthesised source, so the synthesis survives
   dropping it ([subst_unit]) AND the per-[X] subtyping survives renaming. *)
Lemma d_sd_typing_ti_base_ftvar : forall Γ e B,
    is_base_term e ->
    d_sd_typing mode_ti Γ e B ->
    ftvar_in_btyp B [<=] ftvar_in_denv Γ `union` ftvar_in_exp e.
Proof.
  intros Γ e B Hbase H. dependent induction H;
    try solve [ inversion Hbase ].
  - (* unit *) simpl. fsetdec.
  - (* var *) rewrite ftvar_ptyp_to_btyp_syn.
    apply ftvar_in_denv_binds_typ in H. fsetdec.
  - (* anno *) rewrite ftvar_ptyp_to_btyp_syn. simpl. fsetdec.
  - (* sub (m = ti): the embedded [d_sub] is [Infer] = consistency, which keeps
       variables ([d_consis_ftvar_gen]); recurse on the [ti] base synthesis.
       (The [forall_l] inversions carry [mode_ti <> mode_ti] — impossible.) *)
    inversion H1; subst; try (match goal with
      | [ Hne : mode_ti <> mode_ti |- _ ] => exfalso; apply Hne; reflexivity end).
    match goal with
    | [ Hc : empty ⨟ Γ ⊨ ptyp_to_utyp_syn A ≈ B |- _ ] =>
        pose proof (d_consis_ftvar_gen _ _ _ _ Hc) as Hcf
    end.
    specialize (IHd_sd_typing Hbase eq_refl).
    assert (HcfA : ftvar_in_btyp B [<=] ftvar_in_ptyp A).
    { transitivity (ftvar_in_utyp (ptyp_to_utyp_syn A));
        [ exact Hcf | exact (eq_subset _ _ (ftvar_ptyp_to_utyp_syn A)) ]. }
    assert (HihA : ftvar_in_ptyp A [<=] ftvar_in_denv Γ `union` ftvar_in_exp e).
    { transitivity (ftvar_in_btyp (ptyp_to_btyp_syn A));
        [ exact (eq_subset _ _ (eq_sym (ftvar_paint_btyp_syn_eq A))) | exact IHd_sd_typing ]. }
    transitivity (ftvar_in_ptyp A); assumption.
Qed.

(* Shared closing tactic for the three base-term cases of
   [d_sd_typing_forall_admissible].  [X0] is a pre-chosen fresh [∀]-var and
   [Hbt] a proof that the current value [V] is a base term. *)
Ltac base_term_admissible_tac IH Γ B X0 Hbt :=
  let IH0 := fresh "IH0" in
  let A := fresh "A" in
  let Hsyn := fresh "Hsyn" in
  let Hs0 := fresh "Hs0" in
  let HX0A := fresh "HX0A" in
  let Hbnd := fresh "Hbnd" in
  let Hia := fresh "Hia" in
  pose proof (IH X0 ltac:(fsetdec)) as IH0;
  inversion IH0; subst;
  match goal with
  | [ HS : d_sd_typing mode_ti _ ?V0 (ptyp_to_btyp_syn ?A0),
      HR : empty ⨟ _ ⊢[ mode_tc ]
             ptyp_to_utyp_syn ?A0 ⊑ _ |- _ ] =>
      rename HS into Hsyn; rename HR into Hs0;
      (* [A0] is [X0]-free *)
      assert (HX0A : X0 `notin` ftvar_in_ptyp A0);
      [ pose proof (d_sd_typing_ti_base_ftvar _ _ _ Hbt Hsyn) as Hbnd;
        simpl in Hbnd;
        let Hin := fresh "Hin" in intro Hin;
        rewrite <- (ftvar_paint_btyp_syn_eq A0) in Hin;
        specialize (Hbnd _ Hin); fsetdec
      | ];
      (* [is_ityp (btyp_all_inh B)] by renaming the [X0]-instance subtyping. *)
      assert (Hia : is_ityp (btyp_all_inh B));
      [ apply is_ityp__all with (L := {{X0}} `union` ftvar_in_btyp B); intros Y HY;
        pose proof (is_ityp_rename X0 Y (skmod_ty_tc_inv _ (d_sub_skmod Hs0))) as Hir;
        rewrite <- (subst_btyp_in_btyp_intro X0 B (btyp_var_f Y)) in Hir by fsetdec;
        exact Hir
      | ];
      apply d_sd_typing__sub with (A := A0);
      [ exact Hbt
      | (* synthesis at [Γ]: drop [X0] from [Hsyn] via [subst_unit] (identity). *)
        pose proof (d_sd_typing_subst_unit _ _ _ _ Hsyn nil X0 Γ
                      ltac:(reflexivity) ltac:(apply tvar_clean_fresh; fsetdec)) as Hsg;
        rewrite subst_ptyp_in_exp_fresh_eq in Hsg by fsetdec;
        rewrite subst_btyp_in_btyp_fresh_eq in Hsg
          by (rewrite ftvar_paint_btyp_syn_eq; exact HX0A);
        exact Hsg
      | (* per-[X] subtyping: rename [Hs0] from [X0] to [X]. *)
        apply d_sub__forall_r with (L := dom Γ `union` {{X0}} `union` ftvar_in_ptyp A0 `union` ftvar_in_btyp B);
        [ exact Hia | ];
        intros X HX;
        let Hren := fresh "Hren" in
        pose proof (d_sub_rename (Y := X) Hs0 nil Γ X0
                      ltac:(reflexivity) ltac:(simpl; fsetdec)) as Hren;
        simpl in Hren;
        rewrite (subst_utyp_in_utyp_fresh_eq (ptyp_to_utyp_syn A0) (utyp_var_f X) X0)
          in Hren by (rewrite ftvar_ptyp_to_utyp_syn; exact HX0A);
        rewrite <- (subst_btyp_in_btyp_intro X0 B (btyp_var_f X)) in Hren by fsetdec;
        exact Hren ]
  end.

(** The paper's "interesting case" [dtylab{Forall}]: a [∀]-generalised value
    [V] is admissible in [d_sd_typing].  For [λ]-values the [∀] is the folded
    [abs_check_step] / [abs_anno_check_step] (proved here).  For base-term
    values it is re-routed through [Sub] + [d_sub__forall_r], which needs the
    synthesis re-established at [Γ] (the fresh [∀]-var dropped) — an
    [d_sd_typing] tvar-strengthening provided by type-substitution [X := unit]
    (see the [d_sub] note above).  Those three base-term subcases are the only
    remaining holes. *)
Lemma d_sd_typing_forall_admissible : forall L Γ V B,
    is_value V ->
    (forall X, X `notin` L ->
       d_sd_typing mode_tc ((X ~ dbind_tvar) ++ Γ) V (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    d_sd_typing mode_tc Γ V (btyp_all_inh B).
Proof.
  intros L Γ V B Hv IH.
  inversion Hv; subst.
  (* Unified base-term tactic: pick one fresh [X0], invert [IH X0] to a [Sub]
     ([Hbase]/[H0] synthesis/[H1] subtyping over source [A]); the source [A] is
     [X0]-free ([d_sd_typing_ti_base_ftvar], [X0] picked fresh for the context's
     binding ftvars and [V]'s ftvars), so the synthesis survives DROPPING [X0]
     ([subst_unit], identity on [V] and [A]) and the per-[X] subtyping survives
     RENAMING [X0→X] ([d_sub_rename], identity on the [X0]-free LHS). *)
  - (* unit *)
    pick fresh X0 for
      (L `union` dom Γ `union` ftvar_in_btyp B `union` ftvar_in_denv Γ `union` ftvar_in_exp exp_unit).
    pose proof (IH X0 ltac:(fsetdec)) as IH0. inversion IH0; subst.
    assert (HX0A : X0 `notin` ftvar_in_ptyp A).
    { pose proof (d_sd_typing_ti_base_ftvar _ _ _ is_base_term__unit H0) as Hbnd.
      simpl in Hbnd. intro Hin.
      rewrite <- (ftvar_paint_btyp_syn_eq A) in Hin.
      specialize (Hbnd _ Hin). fsetdec. }
    assert (Hia : is_ityp (btyp_all_inh B)).
    { apply is_ityp__all with (L := {{X0}} `union` ftvar_in_btyp B). intros Y HY.
      pose proof (is_ityp_rename X0 Y (skmod_ty_tc_inv _ (d_sub_skmod H1))) as Hir.
      rewrite <- (subst_btyp_in_btyp_intro X0 B (btyp_var_f Y)) in Hir by fsetdec.
      exact Hir. }
    apply d_sd_typing__sub with (A := A).
    + exact is_base_term__unit.
    + pose proof (d_sd_typing_subst_unit _ _ _ _ H0 nil X0 Γ
                    ltac:(reflexivity) ltac:(apply tvar_clean_fresh; fsetdec)) as Hsg.
      rewrite subst_ptyp_in_exp_fresh_eq in Hsg by fsetdec.
      rewrite subst_btyp_in_btyp_fresh_eq in Hsg
        by (rewrite ftvar_paint_btyp_syn_eq; exact HX0A).
      exact Hsg.
    + apply d_sub__forall_r with
        (L := dom Γ `union` {{X0}} `union` ftvar_in_ptyp A `union` ftvar_in_btyp B).
      * exact Hia.
      * intros X HX.
        pose proof (d_sub_rename (Y := X) H1 nil Γ X0
                      ltac:(reflexivity) ltac:(simpl; fsetdec)) as Hren.
        simpl in Hren.
        rewrite (subst_utyp_in_utyp_fresh_eq (ptyp_to_utyp_syn A) (utyp_var_f X) X0)
          in Hren by (rewrite ftvar_ptyp_to_utyp_syn; exact HX0A).
        rewrite <- (subst_btyp_in_btyp_intro X0 B (btyp_var_f X)) in Hren by fsetdec.
        exact Hren.
  - (* var *)
    pick fresh X0 for
      (L `union` dom Γ `union` ftvar_in_btyp B `union` ftvar_in_denv Γ `union` ftvar_in_exp (exp_var_f x)).
    base_term_admissible_tac IH Γ B X0 (is_base_term__var x).
  - (* λx.M : the folded ∀-peel.  [is_ityp (btyp_all_inh B)] is recovered from
       the per-instance typings: each [open B X] types the lambda at [tc], so is
       inherited ([d_sd_typing_tc_abs_is_ityp]). *)
    apply d_sd_typing__abs_check_step with (L := L);
      [ apply is_ityp__all with (L := L); intros X HX;
        exact (d_sd_typing_tc_abs_is_ityp _ _ _ (IH X HX))
      | assumption ].
  - (* λxᴬ.M : the folded ∀-peel (as above). *)
    apply d_sd_typing__abs_anno_check_step with (L := L);
      [ apply is_ityp__all with (L := L); intros X HX;
        exact (d_sd_typing_tc_abs_anno_is_ityp _ _ _ _ (IH X HX))
      | assumption ].
  - (* (M : A) : base term — likewise *)
    pick fresh X0 for
      (L `union` dom Γ `union` ftvar_in_btyp B `union` ftvar_in_denv Γ `union` ftvar_in_exp (exp_anno e A)).
    pose proof (IH X0 ltac:(fsetdec)) as IH0. inversion IH0; subst.
    assert (HX0A : X0 `notin` ftvar_in_ptyp A0).
    { pose proof (d_sd_typing_ti_base_ftvar _ _ _ (is_base_term__anno e A) H1) as Hbnd.
      simpl in Hbnd, Fr. intro Hin.
      rewrite <- (ftvar_paint_btyp_syn_eq A0) in Hin.
      specialize (Hbnd _ Hin). fsetdec. }
    assert (Hia : is_ityp (btyp_all_inh B)).
    { apply is_ityp__all with (L := {{X0}} `union` ftvar_in_btyp B). intros Y HY.
      pose proof (is_ityp_rename X0 Y (skmod_ty_tc_inv _ (d_sub_skmod H2))) as Hir.
      rewrite <- (subst_btyp_in_btyp_intro X0 B (btyp_var_f Y)) in Hir by fsetdec.
      exact Hir. }
    apply d_sd_typing__sub with (A := A0).
    + exact (is_base_term__anno e A).
    + pose proof (d_sd_typing_subst_unit _ _ _ _ H1 nil X0 Γ
                    ltac:(reflexivity) ltac:(apply tvar_clean_fresh; fsetdec)) as Hsg.
      rewrite subst_ptyp_in_exp_fresh_eq in Hsg by fsetdec.
      rewrite subst_btyp_in_btyp_fresh_eq in Hsg
        by (rewrite ftvar_paint_btyp_syn_eq; exact HX0A).
      exact Hsg.
    + apply d_sub__forall_r with
        (L := dom Γ `union` {{X0}} `union` ftvar_in_ptyp A0 `union` ftvar_in_btyp B).
      * exact Hia.
      * intros X HX.
        pose proof (d_sub_rename (Y := X) H2 nil Γ X0
                      ltac:(reflexivity) ltac:(simpl; fsetdec)) as Hren.
        simpl in Hren.
        rewrite (subst_utyp_in_utyp_fresh_eq (ptyp_to_utyp_syn A0) (utyp_var_f X) X0)
          in Hren by (rewrite ftvar_ptyp_to_utyp_syn; exact HX0A).
        rewrite <- (subst_btyp_in_btyp_intro X0 B (btyp_var_f X)) in Hren by fsetdec.
        exact Hren.
Qed.

Theorem d_sd_typing_complete : forall M Γ e A,
    d_typing M Γ e A -> d_sd_typing M Γ e A.
Proof.
  intros M Γ e A H. induction H.
  - apply d_sd_typing__unit.
  - apply d_sd_typing__var; assumption.
  - apply d_sd_typing__anno; assumption.
  - eapply d_sd_typing__sub; eassumption.
  - apply d_sd_typing__freeze; assumption.
  - (* forall: folded ∀ via the admissibility bridge *)
    eapply d_sd_typing_forall_admissible; eassumption.
  - (* abs: d_typing's Abs is general; d_syn splits on the mode — [m≠tc] is
       [__abs], the [tc] case folds into [__abs_check_base].  The latter needs
       the body inherited ([is_ityp B]); since a [tc]-checked body is inherited
       (the same recovery as the forall/lambda cases) this is not a real gap. *)
    destruct m as [ | | m' ].
    + apply d_sd_typing__abs with (L := L);
        [ discriminate | assumption | assumption | assumption ].
    + apply d_sd_typing__abs_check_base with (L := L);
        [ assumption
        | apply is_ityp_arrow_r with (B1 := ptyp_to_btyp_inh A);
          apply skmod_ty_tc_inv; assumption
        | assumption ].
    + apply d_sd_typing__abs with (L := L);
        [ discriminate | assumption | assumption | assumption ].
  - (* abs_anno: as [abs]; the [tc] case is [__abs_anno_check_base].  The skmod
       premise forces the domain inherited at [tc]: [is_ityp B1] + [erase B1 = A]
       give [B1 = inh A], so the d_typing type [B1→B2] IS the [inh A → B2] that
       [__abs_anno_check_base] produces. *)
    destruct m as [ | | m' ].
    + apply d_sd_typing__abs_anno with (L := L) (B1 := B1);
        [ discriminate | assumption | assumption | assumption | assumption ].
    + assert (Hia : is_ityp (btyp_arrow B1 B2)) by (apply skmod_ty_tc_inv; assumption).
      assert (HB1 : ptyp_to_btyp_inh A = B1).
      { pose proof (is_ityp_ptyp_to_btyp_inh (is_ityp_arrow_l _ _ Hia)) as HR.
        rewrite H0 in HR. exact HR. }
      rewrite <- HB1.
      apply d_sd_typing__abs_anno_check_base with (L := L);
        [ assumption | exact (is_ityp_arrow_r _ _ Hia) | assumption ].
    + apply d_sd_typing__abs_anno with (L := L) (B1 := B1);
        [ discriminate | assumption | assumption | assumption | assumption ].
  - (* app *) eapply d_sd_typing__app; eassumption.
Qed.
