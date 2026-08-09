(** Equivalence of the full declarative typing [d_typing] (paper [dtylab],
    Fig. decl-typing) and the syntax-directed typing [d_sd_typing] (paper
    [sdtylab], Fig. syntax-directed-typing).

    Paper Lemmas: Soundness / Completeness of the syntax-directed rules.
    Two structural differences ("Removed base terms" rework):
    (1) [d_typing]'s [Sub] applies to ANY term; [d_sd_typing] has NO [Sub] —
        its subtyping premise is embedded in the three base rules [__unit] /
        [__var] / [__anno].  Soundness re-splits each embedded rule into
        base-rule + [Sub]; completeness discharges [Sub] by the sd-side
        general subsumption [d_sd_typing_general_subsumption] and the base
        rules by reflexive [ti]-subtyping (whence the [d_wf_denv] premise).
    (2) the standalone [dtylab{Forall}]: [d_sd_typing] folds it into the
        checked-lambda rules ([__abs_check_step] / [__abs_anno_check_step], a
        [∀]-peel restricted to [λ]-values).  Soundness replays each peel as a
        [Forall]; completeness case-splits the [Forall] value on whether it is
        a lambda (peel) or a base term (re-routed through the embedded
        subtyping + [ForallR]). *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.prop_basic.
Require Import src.frost.def_extra.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_weakening.
Require Import src.frost.decl.prop_renaming.
Require Import src.frost.decl.prop_skeleton.
Require Import src.frost.decl.prop_general_subsumption.

(* Inversions of the colour predicates / [mod_comp_ty] at [tc]. *)
Lemma is_ityp_arrow_l : forall B1 B2, is_ityp (btyp_arrow B1 B2) -> is_ityp B1.
Proof. intros B1 B2 H. inversion H; assumption. Qed.
Lemma is_ityp_arrow_r : forall B1 B2, is_ityp (btyp_arrow B1 B2) -> is_ityp B2.
Proof. intros B1 B2 H. inversion H; assumption. Qed.
Lemma mod_comp_ty_tc_inv : forall B, mod_comp_ty B mode_tc -> is_ityp B.
Proof. intros B H. inversion H; subst; assumption. Qed.

(* ===================================================================== *)
(*  Soundness:  d_sd_typing ⊆ d_typing                                      *)
(* ===================================================================== *)

Theorem d_sd_typing_sound : forall M Γ e B',
    d_sd_typing M Γ e B' -> d_typing M Γ e B'.
Proof.
  intros M Γ e B' H. induction H.
  - (* unit: embedded subtyping = [Unit] + [Sub]. *)
    apply d_typing__sub with (A := ptyp_unit);
      [ apply d_typing__unit | assumption ].
  - (* var: [Var] + [Sub]. *)
    apply d_typing__sub with (A := A);
      [ apply d_typing__var; assumption | assumption ].
  - (* anno: [Anno] + [Sub]. *)
    apply d_typing__sub with (A := A);
      [ apply d_typing__anno; assumption | assumption ].
  - apply d_typing__freeze; assumption.
  - (* abs_check_step: peel one inherited ∀ via d_typing__forall.  The result
       body [B] is fully inherited ([is_ityp (btyp_all_inh B)]), hence equal to
       its own inh-repainting, which is what d_typing__forall demands. *)
    pose proof (is_ityp_ptyp_to_btyp_inh H) as Hrt. simpl in Hrt. injection Hrt as Hrt.
    rewrite <- Hrt. apply d_typing__forall with (L := L) (A := btyp_to_ptyp B).
    + apply is_value__abs.
    + intros α Hα. rewrite Hrt. apply H1; assumption.
  - (* abs_check_base (ᾱ = ·): the standalone check rule was removed from
       d_typing, so use the GENERAL d_typing__abs at [tc].  Its [mod_comp_ty]
       premise at [tc] is [is_ityp (inh A → B)] — domain inherited (lc [A] from
       [Γ⊢ₚA]), codomain inherited by the rule's [is_ityp B]. *)
    apply d_typing__abs with (L := L) (A := A);
      [ assumption
      | apply mod_comp_ty__tc; apply is_ityp__arrow;
          [ apply is_ityp_paint; eapply d_wf_ptyp_lc; eassumption | assumption ]
      | assumption ].
  - (* abs_anno_check_step: as abs_check_step, over the annotated lambda. *)
    pose proof (is_ityp_ptyp_to_btyp_inh H) as Hrt. simpl in Hrt. injection Hrt as Hrt.
    rewrite <- Hrt. apply d_typing__forall with (L := L) (A := btyp_to_ptyp B).
    + apply is_value__abs_anno.
    + intros α Hα. rewrite Hrt. apply H1; assumption.
  - (* abs_anno_check_base (ᾱ = ·): general d_typing__abs_anno at [tc], domain
       [inh A] (so [B1 = ptyp_to_btyp_inh A], erasing to [A]). *)
    apply d_typing__abs_anno with (L := L) (A := A) (B1 := ptyp_to_btyp_inh A).
    + assumption.
    + apply btyp_to_ptyp_ptyp_to_btyp_inh.
    + apply mod_comp_ty__tc; apply is_ityp__arrow;
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
(*  Each judgment drops an unused tvar binding [α ∉ ftvar(type)].         *)
(* ===================================================================== *)

Lemma d_wf_utyp_strengthen : forall Γ C,
    Γ ⊢ᵤ C ->
    forall Γ1 α Γ2, Γ = Γ1 ++ (α ~ dbind_tvar) ++ Γ2 ->
    α `notin` ftvar_in_utyp C ->
    (Γ1 ++ Γ2) ⊢ᵤ C.
Proof.
  intros Γ C H. induction H; intros Γ1 α0 Γ2 Heq Hα; subst.
  - apply d_wf_utyp__unit.
  - simpl in Hα. apply d_wf_utyp__var. analyze_binds H; try (exfalso; fsetdec); auto.
  - simpl in Hα. apply d_wf_utyp__arrow; [ eapply IHd_wf_utyp1 | eapply IHd_wf_utyp2 ]; eauto.
  - simpl in Hα. apply d_wf_utyp__all_syn with (L := L `union` {{α0}}).
    intros β Hβ. rewrite_env (((β ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 β ltac:(auto) ((β ~ dbind_tvar) ++ Γ1) α0 Γ2); [ simpl_env; reflexivity | ].
    pose proof (ftvar_in_utyp_open_utyp_wrt_utyp_upper C (utyp_var_f β)) as Hup.
    simpl in Hup. fsetdec.
  - simpl in Hα. apply d_wf_utyp__all_etag with (L := L `union` {{α0}}).
    intros β Hβ. rewrite_env (((β ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 β ltac:(auto) ((β ~ dbind_tvar) ++ Γ1) α0 Γ2); [ simpl_env; reflexivity | ].
    pose proof (ftvar_in_utyp_open_utyp_wrt_utyp_upper C (utyp_var_f β)) as Hup.
    simpl in Hup. fsetdec.
Qed.

Lemma d_consis_strengthen : forall Δ Γ C B,
    Δ ⨟ Γ ⊢ C ∼ B ->
    forall Γ1 α Γ2, Γ = Γ1 ++ (α ~ dbind_tvar) ++ Γ2 ->
    α `notin` ftvar_in_utyp C ->
    Δ ⨟ (Γ1 ++ Γ2) ⊢ C ∼ B.
Proof.
  intros Δ Γ C B H. induction H; intros Γ1 α0 Γ2 Heq Hα; subst.
  - apply d_consis__unit; assumption.
  - simpl in Hα. apply d_consis__var; [ | assumption ]. analyze_binds H; try (exfalso; fsetdec); auto.
  - simpl in Hα. eapply d_consis__arrow;
      [ eapply IHd_consis1 | eapply IHd_consis2 | eassumption ]; eauto.
  - simpl in Hα. apply d_consis__forall_inh_tagged with (L := L `union` {{α0}}) (Ψ0 := Ψ0).
    2: eassumption.
    intros β Hβ. rewrite_env (((β ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 β ltac:(auto) ((β ~ dbind_tvar) ++ Γ1) α0 Γ2); [ simpl_env; reflexivity | ].
    pose proof (ftvar_in_utyp_open_utyp_wrt_utyp_upper C (utyp_var_f β)) as Hup.
    simpl in Hup. fsetdec.
  - simpl in Hα. apply d_consis__forall_inh_untagged with (L := L `union` {{α0}}).
    intros β Hβ. rewrite_env (((β ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 β ltac:(auto) ((β ~ dbind_tvar) ++ Γ1) α0 Γ2); [ simpl_env; reflexivity | ].
    pose proof (ftvar_in_utyp_open_utyp_wrt_utyp_upper C (utyp_var_f β)) as Hup.
    simpl in Hup. fsetdec.
  - simpl in Hα. apply d_consis__forall_syn_tagged with (L := L `union` {{α0}}).
    intros β Hβ. rewrite_env (((β ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 β ltac:(auto) ((β ~ dbind_tvar) ++ Γ1) α0 Γ2); [ simpl_env; reflexivity | ].
    pose proof (ftvar_in_utyp_open_utyp_wrt_utyp_upper C (utyp_var_f β)) as Hup.
    simpl in Hup. fsetdec.
  - simpl in Hα. apply d_consis__forall_syn with (L := L `union` {{α0}}).
    intros β Hβ. rewrite_env (((β ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 β ltac:(auto) ((β ~ dbind_tvar) ++ Γ1) α0 Γ2); [ simpl_env; reflexivity | ].
    pose proof (ftvar_in_utyp_open_utyp_wrt_utyp_upper C (utyp_var_f β)) as Hup.
    simpl in Hup. fsetdec.
Qed.

(* NOTE on [d_sub]: a conclusion-only tvar-strengthening ([α ∉ ftvar C] ⇒
   drop α) is FALSE — [d_sub__forall_l] may instantiate with the witness
   [ph = α], which the conclusion does not expose.  The robust replacement is
   type-substitution [α := unit] (rewriting the witnesses too); the pieces
   [d_consis_subst_tvar], [d_wf_utyp_subst_tvar], [d_tags_subst_tvar],
   [d_pat_consis_subst_unit], [d_pat_sub_subst_unit] already exist, and the
   remaining [d_sub] / [d_pat] / [d_sd_typing] subst lemmas are the content of
   [d_sd_typing_forall_admissible]'s base-term cases below. *)

(** A [tc]-checked lambda is typed only by the [abs_check] rules, which carry
    the body-inheritance side condition — so its type is fully inherited.
    (No [sub] interference: [d_sd_typing] has no [Sub] rule, and the embedded
    base rules match only unit/var/anno; no [app]: it is not an application.)
    This recovers the [is_ityp] obligation that the folded [abs_check_step] /
    [abs_anno_check_step] demand. *)
Lemma d_sd_typing_tc_abs_is_ityp : forall Γ e B,
    d_sd_typing mode_tc Γ (exp_abs e) B -> is_ityp B.
Proof.
  intros Γ e B H. dependent induction H.
  - assumption.
  - apply is_ityp__arrow;
      [ apply is_ityp_paint; eapply d_wf_ptyp_lc; eassumption | assumption ].
  - exfalso; match goal with Hne : _ <> mode_tc |- _ => apply Hne; reflexivity end.
Qed.

Lemma d_sd_typing_tc_abs_anno_is_ityp : forall Γ A0 e B,
    d_sd_typing mode_tc Γ (exp_abs_anno A0 e) B -> is_ityp B.
Proof.
  intros Γ A0 e B H. dependent induction H.
  - assumption.
  - apply is_ityp__arrow;
      [ apply is_ityp_paint; eapply d_wf_ptyp_lc; eassumption | assumption ].
  - exfalso; match goal with Hne : _ <> mode_tc |- _ => apply Hne; reflexivity end.
Qed.

(* ===================================================================== *)
(*  [α := unit] type-substitution strengthening (for the base-term anno    *)
(*  ∀-case of completeness): a derivation under a fresh tvar [α] survives   *)
(*  substituting [α := unit], which (as [α ∉ ftvar]) drops [α].             *)
(* ===================================================================== *)

(* btyp_unit is BOTH synthesised and inherited, so colour predicates are
   preserved by [α := unit]. *)
Lemma is_ityp_subst_unit : forall B α, is_ityp B -> is_ityp (subst_btyp_in_btyp btyp_unit α B).
Proof.
  intros B α H. induction H; simpl.
  - auto with frost.
  (* [α] is the var rule's own binder; the lemma's variable is α.  (It read
     [α0] before the rename, when the lemma binder was itself called α.) *)
  - destruct (α0 == α); auto with frost.
  - auto with frost.
  - apply is_ityp__all with (L := L `union` {{α}}). intros β Hβ.
    rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (first [ apply lc_btyp_unit | fsetdec ]). auto.
Qed.

Lemma is_styp_subst_unit : forall B α, is_styp B -> is_styp (subst_btyp_in_btyp btyp_unit α B).
Proof.
  intros B α H. induction H; simpl.
  - auto with frost.
  (* [α] is the var rule's own binder; the lemma's variable is α. *)
  - destruct (α0 == α); auto with frost.
  - auto with frost.
  - apply is_styp__all with (L := L `union` {{α}}). intros β Hβ.
    rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (first [ apply lc_btyp_unit | fsetdec ]). auto.
Qed.

Lemma guarded_btyp_subst_unit : forall B α, guarded_btyp B -> guarded_btyp (subst_btyp_in_btyp btyp_unit α B).
Proof.
  intros B α H. induction H; simpl.
  - auto with frost.
  - destruct (α0 == α); auto with frost.
  - apply guarded_btyp__arrow;
      apply subst_btyp_in_btyp_lc_btyp; solve [ apply lc_btyp_unit | assumption ].
Qed.

Lemma guarded_utyp_subst_unit : forall C α, guarded_utyp C -> guarded_utyp (subst_utyp_in_utyp utyp_unit α C).
Proof.
  intros C α H. induction H; simpl.
  - auto with frost.
  - destruct (α0 == α); auto with frost.
  - apply guarded_utyp__arrow;
      apply subst_utyp_in_utyp_lc_utyp; solve [ apply lc_utyp_unit | assumption ].
Qed.

Lemma is_ttyp_subst_unit : forall C α, is_ttyp C -> is_ttyp (subst_utyp_in_utyp utyp_unit α C).
Proof.
  intros C α H. induction H; simpl.
  - auto with frost.
  - destruct (α0 == α); auto with frost.
  - auto with frost.
  - apply is_ttyp__all_etag with (L := L `union` {{α}}). intros β Hβ.
    rewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (first [ apply lc_utyp_unit | fsetdec ]). auto.
Qed.

(* [d_tags] is insensitive to a tvar:=unit substitution — the ε-tags it counts
   are unaffected (unit carries none, and the substituted var is a tvar). *)
Lemma d_tags_subst_unit : forall Δ C α,
    d_tags Δ C ->
    d_tags Δ (subst_utyp_in_utyp utyp_unit α C).
Proof.
  intros Δ C α H. induction H; simpl.
  - auto with frost.
  - destruct_if; auto with frost.
  - eauto with frost.
  - apply d_tags__all_etag with (L := L `union` {{α}}) (Ψ0 := Ψ0).
    + intros α2 Hα2.
      erewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var
        by (solve [ fsetdec | apply lc_utyp_unit ]).
      apply H0; auto.
    + assumption.
    + assumption.
Qed.

(* Mid-context tvar:=unit strengthening for [d_wf_utyp] (the head-only
   [d_wf_utyp_subst_tvar] does not reach a [Γ1 ++ α0 :: Γ2] split). *)
Lemma d_wf_utyp_subst_unit : forall Γ C,
    Γ ⊢ᵤ C ->
    forall Γ1 α0 Γ2, Γ = Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2 ->
    (Γ1 ++ Γ2) ⊢ᵤ (subst_utyp_in_utyp utyp_unit α0 C).
Proof.
  intros Γ C H. induction H; intros Γ1 α0 Γ2 Heq; subst; simpl.
  - apply d_wf_utyp__unit.
  - destruct_if;
      [ apply d_wf_utyp__unit | apply d_wf_utyp__var; analyze_binds H ].
  - apply d_wf_utyp__arrow; [ eapply IHd_wf_utyp1 | eapply IHd_wf_utyp2 ]; reflexivity.
  - apply d_wf_utyp__all_syn with (L := L `union` dom (Γ1 ++ Γ2) `union` {{α0}}).
    intros α2 Hα2.
    rewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (first [ apply lc_utyp_unit | fsetdec ]).
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 α2); [ fsetdec | simpl_env; reflexivity ].
  - apply d_wf_utyp__all_etag with (L := L `union` dom (Γ1 ++ Γ2) `union` {{α0}}).
    intros α2 Hα2.
    rewrite subst_utyp_in_utyp_open_utyp_wrt_utyp_var by (first [ apply lc_utyp_unit | fsetdec ]).
    rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2).
    eapply (H0 α2); [ fsetdec | simpl_env; reflexivity ].
Qed.

(* tvar:=unit substitution for subtyping.  Tag context [Ψ] is untouched (tags,
   not tvars); [Γ] loses the substituted tvar; types are substituted.  Consis
   premises go through [d_consis_subst_tvar] with [ph := utyp_unit]. *)
Lemma d_sub_subst_unit : forall m Ψ Γ C B,
    Ψ ⨟ Γ ⊢[ m ] C ⩽ B ->
    forall Γ1 Γ2 α0,
      Γ = Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2 ->
      Ψ ⨟ (Γ1 ++ Γ2) ⊢[ m ]
        (subst_utyp_in_utyp utyp_unit α0 C) ⩽ (subst_btyp_in_btyp btyp_unit α0 B).
Proof.
  intros m Ψ Γ C B H. induction H; intros Γ1 Γ2 α0 Heq; subst; simpl.
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
    apply d_sub__forall_r with (L := L `union` dom (Γ1 ++ Γ2) `union` singleton α0).
    + change (btyp_all_inh (subst_btyp_in_btyp btyp_unit α0 B))
        with (subst_btyp_in_btyp btyp_unit α0 (btyp_all_inh B)).
      apply is_ityp_subst_unit; assumption.
    + intros α2 Hα2.
      rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var
        by (first [ apply lc_btyp_unit | fsetdec ]).
      rewrite_env (((α2 ~ dbind_tvar) ++ Γ1) ++ Γ2).
      eapply (H1 α2); [ fsetdec | simpl_env; reflexivity ].
  - (* arg *)
    eapply d_sub__arg.
    + change btyp_unit with (utyp_to_btyp utyp_unit).
      eapply d_consis_subst_tvar;
        [ eassumption | reflexivity | apply d_wf_utyp__unit | apply is_ttyp__unit ].
    + eapply IHd_sub; reflexivity.
    + assumption.
  - (* forall_l_tagged *)
    eapply d_sub__forall_l_tagged with
      (Ψ' := Ψ') (ph := subst_utyp_in_utyp utyp_unit α0 ph);
      [ assumption | assumption
      | apply d_tags_subst_unit; assumption
      | eapply d_wf_utyp_subst_unit; [ eassumption | reflexivity ]
      | apply is_ttyp_subst_unit; assumption
      | ].
    rewrite <- subst_utyp_in_utyp_open_utyp_wrt_utyp by (apply lc_utyp_unit).
    eapply IHd_sub; reflexivity.
  - (* forall_l_untagged *)
    eapply d_sub__forall_l_untagged with
      (Ψ' := Ψ') (ph := subst_utyp_in_utyp utyp_unit α0 ph);
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
Lemma pskl_to_bskl_syn_subst_unit : forall P α',
    subst_bskl_in_bskl bskl_unit α' (pskl_to_bskl_syn P)
    = pskl_to_bskl_syn (subst_pskl_in_pskl pskl_unit α' P).
Proof.
  induction P; intros α'; simpl; try reflexivity;
    try (rewrite IHP1, IHP2; reflexivity); try (rewrite IHP; reflexivity).
  - destruct_if; reflexivity.
Qed.

(* tvar:=unit substitution for skeleton refinement (mirrors
   [d_refine_syn_strengthen], but substitutes the var instead of requiring it
   absent).  [Δs]/[Δi] are refinement-local ∀-vars, disjoint from the Γ-tvar
   [α0], so they are untouched. *)
Lemma d_refine_syn_subst_unit : forall Γ Δi Q Q',
    Γ ⨟ Δi ⊢ᵣ Q ⊳ Q' ->
    forall Γ1 α0 Γ2, Γ = Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2 ->
    (Γ1 ++ Γ2) ⨟ Δi ⊢ᵣ
      (subst_bskl_in_bskl bskl_unit α0 Q) ⊳ (subst_bskl_in_bskl bskl_unit α0 Q').
Proof.
  intros Γ Δi Q Q' H. induction H; intros Γ1 α0 Γ2 Heq; subst; simpl.
  - apply d_refine_syn__unit.
  - destruct_if.
    + apply d_refine_syn__unit.
    + apply d_refine_syn__var. destruct H as [HI | Hb];
        [ left; assumption | right; analyze_binds Hb ].
  - apply d_refine_syn__arrow;
      [ eapply IHd_refine_syn1 | eapply IHd_refine_syn2 ]; reflexivity.
  - apply d_refine_syn__all with (L := L `union` dom (Γ1 ++ Γ2) `union` {{α0}}).
    intros α2 Hα2.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var
      by (first [ apply lc_bskl_unit | fsetdec ]).
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var
      by (first [ apply lc_bskl_unit | fsetdec ]).
    eapply (H0 α2); [ fsetdec | reflexivity ].
  - rewrite pskl_to_bskl_syn_subst_unit. apply d_refine_syn__hole.
    eapply d_wf_pskl_subst_unit; [ eassumption | reflexivity ].
  - apply d_refine_syn__tophole_remove. eapply IHd_refine_syn; reflexivity.
  - apply d_refine_syn__tophole_fill with (L := L `union` dom (Γ1 ++ Γ2) `union` {{α0}}).
    intros α2 Hα2.
    rewrite subst_bskl_in_bskl_open_bskl_wrt_bskl_var
      by (first [ apply lc_bskl_unit | fsetdec ]).
    eapply (H0 α2 ltac:(solve_notin_auto) ((α2 ~ dbind_tvar) ++ Γ1) α0 Γ2);
      simpl_env; reflexivity.
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
Lemma bskl_to_uskl_subst_unit : forall Q α',
    subst_bskl_in_uskl uskl_unit α' (bskl_to_uskl Q)
    = bskl_to_uskl (subst_bskl_in_bskl bskl_unit α' Q).
Proof.
  induction Q; intros α'; simpl; try reflexivity;
    try (rewrite IHQ1, IHQ2; reflexivity); try (rewrite IHQ; reflexivity).
  - destruct_if; reflexivity.
Qed.

(** A context is [tvar_clean] for [α0] when no term-/skl-binding carries [α0]
    in its type.  (tvar bindings carry no type, so they are irrelevant.)  This
    is the invariant that lets a term-var lookup survive dropping [α0]. *)
Definition tvar_clean (α0 : atom) (Γ : list (atom * dbind)) : Prop :=
  (forall x A, binds x (dbind_typ A) Γ -> α0 `notin` ftvar_in_ptyp A) /\
  (forall x P, binds x (dbind_skl P) Γ -> α0 `notin` ftvar_in_pskl P).

Lemma tvar_clean_cons_typ : forall α0 x A Γ,
    α0 `notin` ftvar_in_ptyp A -> tvar_clean α0 Γ ->
    tvar_clean α0 ((x ~ dbind_typ A) ++ Γ).
Proof.
  intros α0 x A Γ HA [Ht Hs]. split; intros y T Hb; analyze_binds Hb.
  - inversion BindsTacVal; subst; assumption.
  - eapply Ht; eassumption.
  - eapply Hs; eassumption.
Qed.

Lemma tvar_clean_cons_skl : forall α0 x P Γ,
    α0 `notin` ftvar_in_pskl P -> tvar_clean α0 Γ ->
    tvar_clean α0 ((x ~ dbind_skl P) ++ Γ).
Proof.
  intros α0 x P Γ HP [Ht Hs]. split; intros y T Hb; analyze_binds Hb.
  - eapply Ht; eassumption.
  - inversion BindsTacVal; subst; assumption.
  - eapply Hs; eassumption.
Qed.

(** Paintings commute with the [α0 := unit] substitution (the unit witness on
    each side is the unit of that sort).  Needed because the embedded skeletons /
    types in a [d_pat] / [d_sd_typing] derivation are produced by paintings, and
    we strengthen by substituting [α0 := unit]. *)
Lemma ptyp_to_pskl_subst_unit : forall A α',
    subst_pskl_in_pskl pskl_unit α' (ptyp_to_pskl A)
    = ptyp_to_pskl (subst_ptyp_in_ptyp ptyp_unit α' A).
Proof.
  induction A; intros α'; simpl; try reflexivity;
    try (rewrite IHA1, IHA2; reflexivity); try (rewrite IHA; reflexivity).
  - destruct_if; reflexivity.
Qed.

Lemma ptyp_to_btyp_syn_subst_unit : forall A α',
    subst_btyp_in_btyp btyp_unit α' (ptyp_to_btyp_syn A)
    = ptyp_to_btyp_syn (subst_ptyp_in_ptyp ptyp_unit α' A).
Proof.
  induction A; intros α'; simpl; try reflexivity;
    try (rewrite IHA1, IHA2; reflexivity); try (rewrite IHA; reflexivity).
  - destruct_if; reflexivity.
Qed.

Lemma ptyp_to_btyp_inh_subst_unit : forall A α',
    subst_btyp_in_btyp btyp_unit α' (ptyp_to_btyp_inh A)
    = ptyp_to_btyp_inh (subst_ptyp_in_ptyp ptyp_unit α' A).
Proof.
  induction A; intros α'; simpl; try reflexivity;
    try (rewrite IHA1, IHA2; reflexivity); try (rewrite IHA; reflexivity).
  - destruct_if; reflexivity.
Qed.

Lemma ptyp_to_utyp_syn_subst_unit : forall A α',
    subst_utyp_in_utyp utyp_unit α' (ptyp_to_utyp_syn A)
    = ptyp_to_utyp_syn (subst_ptyp_in_ptyp ptyp_unit α' A).
Proof.
  induction A; intros α'; simpl; try reflexivity;
    try (rewrite IHA1, IHA2; reflexivity); try (rewrite IHA; reflexivity).
  - destruct_if; reflexivity.
Qed.

Lemma btyp_to_bskl_subst_unit : forall B α',
    subst_bskl_in_bskl bskl_unit α' (btyp_to_bskl B)
    = btyp_to_bskl (subst_btyp_in_btyp btyp_unit α' B).
Proof.
  induction B; intros α'; simpl; try reflexivity;
    try (rewrite IHB1, IHB2; reflexivity); try (rewrite IHB; reflexivity).
  - destruct_if; reflexivity.
Qed.

Lemma btyp_to_ptyp_subst_unit : forall B α',
    subst_ptyp_in_ptyp ptyp_unit α' (btyp_to_ptyp B)
    = btyp_to_ptyp (subst_btyp_in_btyp btyp_unit α' B).
Proof.
  induction B; intros α'; simpl; try reflexivity;
    try (rewrite IHB1, IHB2; reflexivity); try (rewrite IHB; reflexivity).
  - destruct_if; reflexivity.
Qed.

(* [is_value] is stable under any [ptyp]-substitution. *)
Lemma is_value_subst_ptyp : forall A α e,
    is_value e -> is_value (subst_ptyp_in_exp A α e).
Proof.
  intros A α e H. induction H; simpl; constructor; assumption.
Qed.



(* ===================================================================== *)
(*  Tvar-binding congruence for the auxiliary judgments.                   *)
(*                                                                         *)
(*  The [*_subst_unit] lemmas above strengthen a [d_pat] / [d_sd_typing]  *)
(*  derivation by [α0 := unit], but their embedded subtyping / wf premises *)
(*  ([d_sub], [d_pat_sub], [d_refine_syn], [d_wf_*]) come back over the    *)
(*  context [Γ1 ++ Γ2], whereas [d_pat_subst_unit] / [d_sd_typing_subst_unit]  *)
(*  must place every binding over the MAPPED context [map (subst_unit) Γ1 ++ Γ2].*)
(*  All of these judgments consult [Γ] only through [binds α dbind_tvar Γ] *)
(*  (tvar bindings carry no type), and the map ([subst_unit_dbind]) is the *)
(*  identity on tvar bindings — so swapping [Γ1 ++ Γ2] for the mapped      *)
(*  context is sound.  [same_tvar] captures exactly that agreement.        *)
(* ===================================================================== *)

Definition same_tvar (Γ Γ' : list (atom * dbind)) : Prop :=
  forall α, binds α dbind_tvar Γ <-> binds α dbind_tvar Γ'.

Lemma same_tvar_cons : forall Γ Γ' a,
    same_tvar Γ Γ' -> same_tvar (a ++ Γ) (a ++ Γ').
Proof.
  intros Γ Γ' a H α. split; intro Hb; apply binds_app_iff in Hb; apply binds_app_iff;
    (destruct Hb as [Hb | Hb]; [ left; assumption | right; apply H; assumption ]).
Qed.

Lemma d_wf_ptyp_same_tvar : forall Γ A,
    Γ ⊢ₚ A -> forall Γ', same_tvar Γ Γ' -> Γ' ⊢ₚ A.
Proof.
  intros Γ A H. induction H; intros Γ' Hst.
  - apply d_wf_ptyp__unit.
  - apply d_wf_ptyp__var. apply Hst. assumption.
  - apply d_wf_ptyp__arrow; [ apply IHd_wf_ptyp1 | apply IHd_wf_ptyp2 ]; assumption.
  - apply d_wf_ptyp__all with (L := L). intros α Hα.
    apply H0; [ assumption | apply same_tvar_cons; assumption ].
Qed.

Lemma d_wf_utyp_same_tvar : forall Γ C,
    Γ ⊢ᵤ C -> forall Γ', same_tvar Γ Γ' -> Γ' ⊢ᵤ C.
Proof.
  intros Γ C H. induction H; intros Γ' Hst.
  - apply d_wf_utyp__unit.
  - apply d_wf_utyp__var. apply Hst. assumption.
  - apply d_wf_utyp__arrow; [ apply IHd_wf_utyp1 | apply IHd_wf_utyp2 ]; assumption.
  - apply d_wf_utyp__all_syn with (L := L). intros α Hα.
    apply H0; [ assumption | apply same_tvar_cons; assumption ].
  - apply d_wf_utyp__all_etag with (L := L). intros α Hα.
    apply H0; [ assumption | apply same_tvar_cons; assumption ].
Qed.

Lemma d_wf_pskl_same_tvar : forall Ψ Γ P,
    Γ ⨟ Ψ ⊢ₚₛ P -> forall Γ', same_tvar Γ Γ' -> Γ' ⨟ Ψ ⊢ₚₛ P.
Proof.
  intros Ψ Γ P H. induction H; intros Γ' Hst.
  - apply d_wf_pskl__unit.
  - apply d_wf_pskl__var. destruct H as [HΨ | Hb]; [ left; assumption | right; apply Hst; assumption ].
  - apply d_wf_pskl__arrow; [ apply IHd_wf_pskl1 | apply IHd_wf_pskl2 ]; assumption.
  - apply d_wf_pskl__all with (L := L). intros α Hα.
    apply H0; assumption.
  - apply d_wf_pskl__hole.
  - apply d_wf_pskl__tophole; [ assumption | apply IHd_wf_pskl; assumption ].
Qed.

Lemma d_wf_uskl_same_tvar : forall Ψ Γ R,
    Γ ⨟ Ψ ⊢ᵤₛ R -> forall Γ', same_tvar Γ Γ' -> Γ' ⨟ Ψ ⊢ᵤₛ R.
Proof.
  intros Ψ Γ R H. induction H; intros Γ' Hst.
  - apply d_wf_uskl__unit.
  - apply d_wf_uskl__var. destruct H as [HΨ | Hb]; [ left; assumption | right; apply Hst; assumption ].
  - apply d_wf_uskl__arrow; [ apply IHd_wf_uskl1 | apply IHd_wf_uskl2 ]; assumption.
  - apply d_wf_uskl__all_syn with (L := L). intros α Hα.
    apply H0; assumption.
  - apply d_wf_uskl__all_etag with (L := L). intros α Hα.
    apply H0; assumption.
  - apply d_wf_uskl__hole.
  - apply d_wf_uskl__tophole; [ assumption | apply IHd_wf_uskl; assumption ].
  - apply d_wf_uskl__holeg.
  - apply d_wf_uskl__topholeg; [ assumption | apply IHd_wf_uskl; assumption ].
Qed.

Lemma d_consis_same_tvar : forall Ψ Γ C B,
    Ψ ⨟ Γ ⊢ C ∼ B -> forall Γ', same_tvar Γ Γ' -> Ψ ⨟ Γ' ⊢ C ∼ B.
Proof.
  intros Ψ Γ C B H. induction H; intros Γ' Hst.
  - apply d_consis__unit; assumption.
  - apply d_consis__var; [ apply Hst; assumption | assumption ].
  - eapply d_consis__arrow; [ apply IHd_consis1 | apply IHd_consis2 | eassumption ]; assumption.
  - apply d_consis__forall_inh_tagged with (L := L) (Ψ0 := Ψ0); [ | assumption ].
    intros α Hα. apply H0; [ assumption | apply same_tvar_cons; assumption ].
  - apply d_consis__forall_inh_untagged with (L := L). intros α Hα.
    apply H0; [ assumption | apply same_tvar_cons; assumption ].
  - apply d_consis__forall_syn_tagged with (L := L). intros α Hα.
    apply H0; [ assumption | apply same_tvar_cons; assumption ].
  - apply d_consis__forall_syn with (L := L). intros α Hα.
    apply H0; [ assumption | apply same_tvar_cons; assumption ].
Qed.

Lemma d_pat_consis_same_tvar : forall Δ Γ R Q,
    Δ ⨟ Γ ⊢ₛ R ∼ Q -> forall Γ', same_tvar Γ Γ' -> Δ ⨟ Γ' ⊢ₛ R ∼ Q.
Proof.
  intros Δ Γ R Q H. induction H; intros Γ' Hst.
  - apply d_pat_consis__unit; assumption.
  - apply d_pat_consis__var; [ assumption | apply Hst; assumption ].
  - eapply d_pat_consis__arrow; [ apply IHd_pat_consis1 | apply IHd_pat_consis2 | eassumption ]; assumption.
  - apply d_pat_consis__forall_inh_tagged with (L := L) (Ψ0 := Ψ0); [ | assumption ].
    intros α Hα. apply H0; [ assumption | apply same_tvar_cons; assumption ].
  - apply d_pat_consis__forall_inh_untagged with (L := L). intros α Hα.
    apply H0; [ assumption | apply same_tvar_cons; assumption ].
  - apply d_pat_consis__forall_syn_tagged with (L := L). intros α Hα.
    apply H0; [ assumption | apply same_tvar_cons; assumption ].
  - apply d_pat_consis__forall_syn with (L := L). intros α Hα.
    apply H0; [ assumption | apply same_tvar_cons; assumption ].
  - apply d_pat_consis__ghostg; assumption.
  - apply d_pat_consis__topholeg. apply IHd_pat_consis; assumption.
  - apply d_pat_consis__hole; [ assumption | eapply d_wf_pskl_same_tvar; eassumption ].
  - apply d_pat_consis__tophole; apply IHd_pat_consis; assumption.
  - apply d_pat_consis__tophole_inh with (L := L). intros α Hα.
    apply H0; [ assumption | apply same_tvar_cons; assumption ].
  - apply d_pat_consis__tophole_drop. apply IHd_pat_consis; assumption.
Qed.

Lemma d_sub_same_tvar : forall m Ψ Γ C B,
    Ψ ⨟ Γ ⊢[ m ] C ⩽ B -> forall Γ', same_tvar Γ Γ' -> Ψ ⨟ Γ' ⊢[ m ] C ⩽ B.
Proof.
  intros m Ψ Γ C B H. induction H; intros Γ' Hst.
  - apply d_sub__infer; [ eapply d_consis_same_tvar; eassumption | assumption | assumption ].
  - apply d_sub__check; [ assumption | assumption | eapply d_consis_same_tvar; eassumption | assumption ].
  - apply d_sub__forall_r with (L := L); [ assumption | ]. intros α Hα.
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
    Δ ⨟ Γ ⊢ₛ[ m ] R ⩽ Q -> forall Γ', same_tvar Γ Γ' -> Δ ⨟ Γ' ⊢ₛ[ m ] R ⩽ Q.
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
  - apply d_pat_sub__ghost; [ assumption | eapply d_wf_pskl_same_tvar; eassumption | assumption ].
  - apply d_pat_sub__univ_ghost_l; [ assumption | apply IHd_pat_sub; assumption ].
  - apply d_pat_sub__ghostg; assumption.
  - apply d_pat_sub__univ_ghost_lg; [ assumption | apply IHd_pat_sub; assumption ].
Qed.

Lemma d_refine_syn_same_tvar : forall Γ Δi Q Q',
    Γ ⨟ Δi ⊢ᵣ Q ⊳ Q' -> forall Γ', same_tvar Γ Γ' -> Γ' ⨟ Δi ⊢ᵣ Q ⊳ Q'.
Proof.
  intros Γ Δi Q Q' H. induction H; intros Γ' Hst.
  - apply d_refine_syn__unit.
  - apply d_refine_syn__var. destruct H as [HI | Hb];
      [ left; assumption | right; apply Hst; assumption ].
  - apply d_refine_syn__arrow; [ apply IHd_refine_syn1 | apply IHd_refine_syn2 ]; assumption.
  - apply d_refine_syn__all with (L := L). intros α Hα. apply H0; assumption.
  - apply d_refine_syn__hole. eapply d_wf_pskl_same_tvar; eassumption.
  - apply d_refine_syn__tophole_remove. apply IHd_refine_syn; assumption.
  - apply d_refine_syn__tophole_fill with (L := L). intros α Hα.
    apply (H0 α Hα ((α ~ dbind_tvar) ++ Γ')). apply same_tvar_cons. assumption.
  - apply d_refine_syn__tophole_keep; [ assumption | apply IHd_refine_syn; assumption ].
Qed.

(* ===================================================================== *)
(*  [α0 := unit] context-substitution for [d_pat] / [d_sd_typing].       *)
(* ===================================================================== *)

Definition subst_unit_dbind (α0 : atom) (d : dbind) : dbind :=
  match d with
  | dbind_tvar => dbind_tvar
  | dbind_typ A => dbind_typ (subst_ptyp_in_ptyp ptyp_unit α0 A)
  | dbind_skl P => dbind_skl (subst_pskl_in_pskl pskl_unit α0 P)
  end.

Lemma map_subst_unit_dbind_cons : forall x d α0 Γ1,
    (x ~ subst_unit_dbind α0 d) ++ map (subst_unit_dbind α0) Γ1
    = map (subst_unit_dbind α0) ((x ~ d) ++ Γ1).
Proof. intros. simpl_env. reflexivity. Qed.

(* The mapped context [map (subst_unit_dbind α0) Γ1 ++ Γ2] has the SAME tvar
   bindings as [Γ1 ++ Γ2] (the map fixes tvar bindings; [Γ2] is untouched). *)
Lemma same_tvar_map_subst_unit : forall α0 Γ1 Γ2,
    same_tvar (Γ1 ++ Γ2) (map (subst_unit_dbind α0) Γ1 ++ Γ2).
Proof.
  intros α0 Γ1 Γ2 α. split; intro Hb; apply binds_app_iff in Hb; apply binds_app_iff;
    destruct Hb as [Hb | Hb].
  - left. change dbind_tvar with (subst_unit_dbind α0 dbind_tvar). apply binds_map_2. assumption.
  - right. assumption.
  - left. apply binds_map_3 in Hb as [b [Heq Hb']]. destruct b; inversion Heq; subst.
    assumption.
  - right. assumption.
Qed.

(* binds for a term-binding survives the map+drop, with its type substituted. *)
Lemma binds_typ_subst_unit_dbind : forall x A α0 Γ1 Γ2,
    binds x (dbind_typ A) (Γ1 ++ Γ2) -> tvar_clean α0 Γ2 ->
    binds x (dbind_typ (subst_ptyp_in_ptyp ptyp_unit α0 A))
          (map (subst_unit_dbind α0) Γ1 ++ Γ2).
Proof.
  intros x A α0 Γ1 Γ2 Hb [Ht Hs]. apply binds_app_iff in Hb. destruct Hb as [Hb | Hb].
  - apply binds_app_2.
    change (dbind_typ (subst_ptyp_in_ptyp ptyp_unit α0 A))
      with (subst_unit_dbind α0 (dbind_typ A)).
    apply binds_map_2. assumption.
  - apply binds_app_3.
    rewrite (subst_ptyp_in_ptyp_fresh_eq _ _ _ (Ht _ _ Hb)). assumption.
Qed.

Lemma binds_skl_subst_unit_dbind : forall x P α0 Γ1 Γ2,
    binds x (dbind_skl P) (Γ1 ++ Γ2) -> tvar_clean α0 Γ2 ->
    binds x (dbind_skl (subst_pskl_in_pskl pskl_unit α0 P))
          (map (subst_unit_dbind α0) Γ1 ++ Γ2).
Proof.
  intros x P α0 Γ1 Γ2 Hb [Ht Hs]. apply binds_app_iff in Hb. destruct Hb as [Hb | Hb].
  - apply binds_app_2.
    change (dbind_skl (subst_pskl_in_pskl pskl_unit α0 P))
      with (subst_unit_dbind α0 (dbind_skl P)).
    apply binds_map_2. assumption.
  - apply binds_app_3.
    rewrite (subst_pskl_in_pskl_fresh_eq _ _ _ (Hs _ _ Hb)). assumption.
Qed.

(* Map-context [d_wf_ptyp] strengthening: combine the existing drop-context
   [d_wf_ptyp_subst_tvar]-style substitution with the [same_tvar] swap to the
   mapped context.  Done from scratch via [d_wf_ptyp_of_lc_ftvar]. *)
Lemma d_wf_ptyp_subst_unit_ctx : forall Γ A,
    Γ ⊢ₚ A -> forall Γ1 α0 Γ2, Γ = Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2 ->
    (map (subst_unit_dbind α0) Γ1 ++ Γ2) ⊢ₚ (subst_ptyp_in_ptyp ptyp_unit α0 A).
Proof.
  intros Γ A H Γ1 α0 Γ2 Heq.
  apply d_wf_ptyp_of_lc_ftvar.
  - apply subst_ptyp_in_ptyp_lc_ptyp; [ eapply d_wf_ptyp_lc; eassumption | apply lc_ptyp_unit ].
  - intros β Hβ.
    pose proof (ftvar_in_ptyp_subst_ptyp_in_ptyp_upper A ptyp_unit α0) as Hup.
    simpl in Hup.
    assert (HYA : β `in` ftvar_in_ptyp A) by (clear - Hβ Hup; fsetdec).
    assert (HYne : β <> α0).
    { clear - Hβ Hup. intro; subst. assert (α0 `notin` (remove α0 (ftvar_in_ptyp A))) by fsetdec. fsetdec. }
    assert (Hbnd : binds β dbind_tvar Γ) by (eapply d_wf_ptyp_ftvar; eassumption).
    subst Γ.
    (* β is a tvar of [Γ1 ++ α0 :: Γ2], distinct from α0 → survives the map. *)
    assert (Hbnd' : binds β dbind_tvar (Γ1 ++ Γ2)).
    { analyze_binds Hbnd. }
    eapply (same_tvar_map_subst_unit α0 Γ1 Γ2). assumption.
Qed.

Lemma d_pat_subst_unit : forall m Γ e Q,
    Γ ⊢[ m ] e ⇨ Q ->
    forall Γ1 α0 Γ2, Γ = Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2 ->
    tvar_clean α0 Γ2 ->
    (map (subst_unit_dbind α0) Γ1 ++ Γ2) ⊢[ m ]
      (subst_ptyp_in_exp ptyp_unit α0 e) ⇨ (subst_bskl_in_bskl bskl_unit α0 Q).
Proof.
  intros m Γ e Q H. induction H; intros Γ1 α0 Γ2 Heq Hclean; subst; simpl.
  - (* unit: embedded [d_pat_sub] over [Γ1++Γ2] → swap to mapped context. *)
    apply d_pat__unit.
    change uskl_unit with (subst_bskl_in_uskl uskl_unit α0 uskl_unit).
    eapply d_pat_sub_same_tvar;
      [ eapply d_pat_sub_subst_unit; [ eassumption | reflexivity ]
      | apply same_tvar_map_subst_unit ].
  - (* var: lookup survives; embedded sub premise as in unit. *)
    destruct d as [ | A | P0 ]; simpl in H0.
    + discriminate.
    + injection H0 as H0. subst P.
      assert (Hb : binds x (dbind_typ A) (Γ1 ++ Γ2)) by (analyze_binds H).
      eapply d_pat__var with (d := dbind_typ (subst_ptyp_in_ptyp ptyp_unit α0 A));
        [ apply binds_typ_subst_unit_dbind; eassumption
        | reflexivity | ].
      rewrite <- ptyp_to_pskl_subst_unit.
      rewrite <- pskl_to_bskl_syn_subst_unit.
      rewrite <- bskl_to_uskl_subst_unit.
      eapply d_pat_sub_same_tvar;
        [ eapply d_pat_sub_subst_unit; [ eassumption | reflexivity ]
        | apply same_tvar_map_subst_unit ].
    + injection H0 as H0. subst P.
      assert (Hb : binds x (dbind_skl P0) (Γ1 ++ Γ2)) by (analyze_binds H).
      eapply d_pat__var with (d := dbind_skl (subst_pskl_in_pskl pskl_unit α0 P0));
        [ apply binds_skl_subst_unit_dbind; eassumption
        | reflexivity | ].
      rewrite <- pskl_to_bskl_syn_subst_unit.
      rewrite <- bskl_to_uskl_subst_unit.
      eapply d_pat_sub_same_tvar;
        [ eapply d_pat_sub_subst_unit; [ eassumption | reflexivity ]
        | apply same_tvar_map_subst_unit ].
  - (* anno: embedded sub premise as in unit. *)
    apply d_pat__anno.
    + eapply d_wf_ptyp_subst_unit_ctx; [ eassumption | reflexivity ].
    + rewrite <- ptyp_to_pskl_subst_unit.
      rewrite <- pskl_to_bskl_syn_subst_unit.
      rewrite <- bskl_to_uskl_subst_unit.
      eapply d_pat_sub_same_tvar;
        [ eapply d_pat_sub_subst_unit; [ eassumption | reflexivity ]
        | apply same_tvar_map_subst_unit ].
  - (* freeze *)
    rewrite pskl_to_bskl_syn_subst_unit.
    apply d_pat__freeze. rewrite <- pskl_to_bskl_syn_subst_unit.
    eapply IHd_pat; [ reflexivity | assumption ].
  - (* abs (cofinite) *)
    rewrite pskl_to_bskl_inh_subst_unit.
    apply d_pat__abs with (L := L `union` {{α0}}) (P := subst_pskl_in_pskl pskl_unit α0 P).
    + assumption.
    + eapply d_wf_pskl_same_tvar;
        [ eapply d_wf_pskl_subst_unit; [ eassumption | reflexivity ]
        | apply same_tvar_map_subst_unit ].
    + (* [mod_comp_sk] preserved under [α0 := unit]. *)
      pose proof (mod_comp_sk_subst_unit α0 H1) as Hm.
      cbn [subst_bskl_in_bskl] in Hm.
      rewrite pskl_to_bskl_inh_subst_unit in Hm. exact Hm.
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
      rewrite_env (((x ~ subst_unit_dbind α0 (dbind_skl P)) ++ map (subst_unit_dbind α0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H3 x ltac:(solve_notin_auto) ((x ~ dbind_skl P) ++ Γ1) α0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  - (* abs_anno (cofinite) *)
    rewrite btyp_to_bskl_subst_unit.
    eapply d_pat__abs_anno with (L := L `union` {{α0}}).
    + assumption.
    + eapply d_wf_ptyp_subst_unit_ctx; [ eassumption | reflexivity ].
    + symmetry. apply btyp_to_ptyp_subst_unit.
    + (* [mod_comp_sk] preserved under [α0 := unit]. *)
      pose proof (mod_comp_sk_subst_unit α0 H2) as Hm.
      cbn [subst_bskl_in_bskl] in Hm.
      rewrite btyp_to_bskl_subst_unit in Hm. exact Hm.
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
      rewrite_env (((x ~ subst_unit_dbind α0 (dbind_typ (btyp_to_ptyp B))) ++ map (subst_unit_dbind α0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H4 x ltac:(solve_notin_auto) ((x ~ dbind_typ (btyp_to_ptyp B)) ++ Γ1) α0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  - (* app *)
    eapply d_pat__app.
    + rewrite <- pskl_to_bskl_syn_subst_unit. eapply IHd_pat1; [ reflexivity | assumption ].
    + rewrite <- pskl_to_bskl_inh_subst_unit.
      eapply d_refine_syn_same_tvar;
        [ eapply d_refine_syn_subst_unit; [ eassumption | reflexivity ]
        | apply same_tvar_map_subst_unit ].
    + change (bskl_arrow (subst_bskl_in_bskl bskl_unit α0 Q1) (subst_bskl_in_bskl bskl_unit α0 Q2))
        with (subst_bskl_in_bskl bskl_unit α0 (bskl_arrow Q1 Q2)).
      eapply IHd_pat2; [ reflexivity | assumption ].
  - (* abs_check (cofinite) *)
    rewrite pskl_to_bskl_syn_subst_unit.
    apply d_pat__abs_check with (L := L `union` {{α0}}) (P := subst_pskl_in_pskl pskl_unit α0 P).
    intros x Hx.
    rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
    rewrite_env (((x ~ subst_unit_dbind α0 (dbind_skl pskl_hole)) ++ map (subst_unit_dbind α0) Γ1) ++ Γ2).
    rewrite map_subst_unit_dbind_cons.
    rewrite <- pskl_to_bskl_syn_subst_unit.
    eapply (H0 x ltac:(solve_notin_auto) ((x ~ dbind_skl pskl_hole) ++ Γ1) α0 Γ2);
      [ simpl_env; reflexivity | assumption ].
  - (* abs_anno_check (cofinite) *)
    rewrite btyp_to_bskl_subst_unit. rewrite ptyp_to_btyp_syn_subst_unit.
    rewrite pskl_to_bskl_syn_subst_unit.
    apply d_pat__abs_anno_check with (L := L `union` {{α0}})
      (A := subst_ptyp_in_ptyp ptyp_unit α0 A) (P := subst_pskl_in_pskl pskl_unit α0 P).
    + eapply d_wf_ptyp_subst_unit_ctx; [ eassumption | reflexivity ].
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
      rewrite_env (((x ~ subst_unit_dbind α0 (dbind_typ A)) ++ map (subst_unit_dbind α0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      rewrite <- pskl_to_bskl_syn_subst_unit.
      eapply (H1 x ltac:(solve_notin_auto) ((x ~ dbind_typ A) ++ Γ1) α0 Γ2);
        [ simpl_env; reflexivity | assumption ].
Qed.

(* [mod_comp_ty] is the colour/mode discipline on the type only; it depends on the
   type via [is_styp] / [is_ityp], both preserved by [α0 := unit]. *)
Lemma mod_comp_ty_subst_unit : forall B m α0,
    mod_comp_ty B m -> mod_comp_ty (subst_btyp_in_btyp btyp_unit α0 B) m.
Proof.
  intros B m α0 H. induction H.
  - apply mod_comp_ty__ti. apply is_styp_subst_unit. assumption.
  - apply mod_comp_ty__tc. apply is_ityp_subst_unit. assumption.
  - simpl. apply mod_comp_ty__fn. assumption.
Qed.

Lemma d_sd_typing_subst_unit : forall m Γ e B,
    d_sd_typing m Γ e B ->
    forall Γ1 α0 Γ2, Γ = Γ1 ++ (α0 ~ dbind_tvar) ++ Γ2 ->
    tvar_clean α0 Γ2 ->
    d_sd_typing m (map (subst_unit_dbind α0) Γ1 ++ Γ2)
      (subst_ptyp_in_exp ptyp_unit α0 e) (subst_btyp_in_btyp btyp_unit α0 B).
Proof.
  intros m Γ e B H. induction H; intros Γ1 α0 Γ2 Heq Hclean; subst; simpl.
  - (* unit: substitute through the embedded subtyping ([unit] is [α0]-free). *)
    apply d_sd_typing__unit.
    change (ptyp_to_utyp_syn ptyp_unit)
      with (subst_utyp_in_utyp utyp_unit α0 (ptyp_to_utyp_syn ptyp_unit)).
    eapply d_sub_same_tvar;
      [ eapply d_sub_subst_unit; [ eassumption | reflexivity ]
      | apply same_tvar_map_subst_unit ].
  - (* var: binding type substituted; embedded subtyping substituted. *)
    apply d_sd_typing__var with (A := subst_ptyp_in_ptyp ptyp_unit α0 A).
    + assert (Hb : binds x (dbind_typ A) (Γ1 ++ Γ2)) by (analyze_binds H).
      apply binds_typ_subst_unit_dbind; assumption.
    + rewrite <- ptyp_to_utyp_syn_subst_unit.
      eapply d_sub_same_tvar;
        [ eapply d_sub_subst_unit; [ eassumption | reflexivity ]
        | apply same_tvar_map_subst_unit ].
  - (* anno *)
    eapply d_sd_typing__anno.
    + rewrite <- ptyp_to_btyp_inh_subst_unit.
      eapply IHd_sd_typing; [ reflexivity | assumption ].
    + rewrite <- ptyp_to_utyp_syn_subst_unit.
      eapply d_sub_same_tvar;
        [ eapply d_sub_subst_unit; [ eassumption | reflexivity ]
        | apply same_tvar_map_subst_unit ].
  - (* freeze *)
    rewrite ptyp_to_btyp_inh_subst_unit.
    apply d_sd_typing__freeze. rewrite <- ptyp_to_btyp_syn_subst_unit.
    eapply IHd_sd_typing; [ reflexivity | assumption ].
  - (* abs_check_step *)
    apply d_sd_typing__abs_check_step with (L := L `union` {{α0}}).
    + pose proof (is_ityp_subst_unit (btyp_all_inh B) α0 H) as Hi. simpl in Hi. exact Hi.
    + intros α Hα.
      rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (first [ apply lc_btyp_unit | fsetdec ]).
      rewrite_env (((α ~ subst_unit_dbind α0 dbind_tvar) ++ map (subst_unit_dbind α0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H1 α ltac:(solve_notin_auto) ((α ~ dbind_tvar) ++ Γ1) α0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  - (* abs_check_base *)
    rewrite ptyp_to_btyp_inh_subst_unit.
    apply d_sd_typing__abs_check_base with (L := L `union` {{α0}}).
    + eapply d_wf_ptyp_subst_unit_ctx; [ eassumption | reflexivity ].
    + apply is_ityp_subst_unit. assumption.
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
      rewrite_env (((x ~ subst_unit_dbind α0 (dbind_typ A)) ++ map (subst_unit_dbind α0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H2 x ltac:(solve_notin_auto) ((x ~ dbind_typ A) ++ Γ1) α0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  - (* abs_anno_check_step *)
    apply d_sd_typing__abs_anno_check_step with (L := L `union` {{α0}}).
    + pose proof (is_ityp_subst_unit (btyp_all_inh B) α0 H) as Hi. simpl in Hi. exact Hi.
    + intros α Hα.
      rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp_var by (first [ apply lc_btyp_unit | fsetdec ]).
      rewrite_env (((α ~ subst_unit_dbind α0 dbind_tvar) ++ map (subst_unit_dbind α0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H1 α ltac:(solve_notin_auto) ((α ~ dbind_tvar) ++ Γ1) α0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  - (* abs_anno_check_base *)
    rewrite ptyp_to_btyp_inh_subst_unit.
    apply d_sd_typing__abs_anno_check_base with (L := L `union` {{α0}}).
    + eapply d_wf_ptyp_subst_unit_ctx; [ eassumption | reflexivity ].
    + apply is_ityp_subst_unit. assumption.
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
      rewrite_env (((x ~ subst_unit_dbind α0 (dbind_typ A)) ++ map (subst_unit_dbind α0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H2 x ltac:(solve_notin_auto) ((x ~ dbind_typ A) ++ Γ1) α0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  - (* abs (m ≠ tc, cofinite) *)
    rewrite ptyp_to_btyp_inh_subst_unit.
    apply d_sd_typing__abs with (L := L `union` {{α0}}).
    + assumption.
    + eapply d_wf_ptyp_subst_unit_ctx; [ eassumption | reflexivity ].
    + rewrite <- ptyp_to_btyp_inh_subst_unit.
      change (btyp_arrow (subst_btyp_in_btyp btyp_unit α0 (ptyp_to_btyp_inh A))
                         (subst_btyp_in_btyp btyp_unit α0 B))
        with (subst_btyp_in_btyp btyp_unit α0 (btyp_arrow (ptyp_to_btyp_inh A) B)).
      apply mod_comp_ty_subst_unit. assumption.
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
      rewrite_env (((x ~ subst_unit_dbind α0 (dbind_typ A)) ++ map (subst_unit_dbind α0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H3 x ltac:(solve_notin_auto) ((x ~ dbind_typ A) ++ Γ1) α0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  - (* abs_anno (m ≠ tc, cofinite) *)
    apply d_sd_typing__abs_anno with (L := L `union` {{α0}})
      (B1 := subst_btyp_in_btyp btyp_unit α0 B1).
    + assumption.
    + eapply d_wf_ptyp_subst_unit_ctx; [ eassumption | reflexivity ].
    + symmetry. apply btyp_to_ptyp_subst_unit.
    + pose proof (mod_comp_ty_subst_unit (btyp_arrow B1 B2) m α0 H2) as Hsk. simpl in Hsk. exact Hsk.
    + intros x Hx.
      rewrite subst_ptyp_in_exp_open_exp_wrt_exp_var by (first [ apply lc_ptyp_unit | fsetdec ]).
      rewrite_env (((x ~ subst_unit_dbind α0 (dbind_typ (btyp_to_ptyp B1))) ++ map (subst_unit_dbind α0) Γ1) ++ Γ2).
      rewrite map_subst_unit_dbind_cons.
      eapply (H4 x ltac:(solve_notin_auto) ((x ~ dbind_typ (btyp_to_ptyp B1)) ++ Γ1) α0 Γ2);
        [ simpl_env; reflexivity | assumption ].
  - (* app *)
    eapply d_sd_typing__app.
    + rewrite <- pskl_to_bskl_syn_subst_unit.
      eapply d_pat_subst_unit; [ eassumption | reflexivity | assumption ].
    + rewrite <- btyp_to_bskl_subst_unit. rewrite <- pskl_to_bskl_inh_subst_unit.
      eapply d_refine_syn_same_tvar;
        [ eapply d_refine_syn_subst_unit; [ eassumption | reflexivity ]
        | apply same_tvar_map_subst_unit ].
    + change (btyp_arrow (subst_btyp_in_btyp btyp_unit α0 B1)
                         (subst_btyp_in_btyp btyp_unit α0 B2))
        with (subst_btyp_in_btyp btyp_unit α0 (btyp_arrow B1 B2)).
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

Lemma tvar_clean_fresh : forall α Γ,
    α `notin` ftvar_in_denv Γ -> tvar_clean α Γ.
Proof.
  intros α Γ Hα. split; intros y T Hb.
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
(* Consistency only relates types with the same free variables (it never
   instantiates), so [B]'s ftvars are bounded by [C]'s. *)
Lemma d_consis_ftvar_gen : forall Δ Γ C B,
    Δ ⨟ Γ ⊢ C ∼ B -> ftvar_in_btyp B [<=] ftvar_in_utyp C.
Proof.
  intros Δ Γ C B H. induction H; simpl; try fsetdec.
  - (* forall_inh_tagged *)
    pick fresh α for (L `union` ftvar_in_btyp B `union` ftvar_in_utyp C).
    specialize (H0 α ltac:(solve_notin_auto)).
    pose proof (ftvar_in_btyp_open_btyp_wrt_btyp_lower B (btyp_var_f α)) as HL.
    pose proof (ftvar_in_utyp_open_utyp_wrt_utyp_upper C (utyp_var_f α)) as HU.
    simpl in HU. fsetdec.
  - (* forall_inh_untagged *)
    pick fresh α for (L `union` ftvar_in_btyp B `union` ftvar_in_utyp C).
    specialize (H0 α ltac:(solve_notin_auto)).
    pose proof (ftvar_in_btyp_open_btyp_wrt_btyp_lower B (btyp_var_f α)) as HL.
    pose proof (ftvar_in_utyp_open_utyp_wrt_utyp_upper C (utyp_var_f α)) as HU.
    simpl in HU. fsetdec.
  - (* forall_syn_tagged *)
    pick fresh α for (L `union` ftvar_in_btyp B `union` ftvar_in_utyp C).
    specialize (H0 α ltac:(solve_notin_auto)).
    pose proof (ftvar_in_btyp_open_btyp_wrt_btyp_lower B (btyp_var_f α)) as HL.
    pose proof (ftvar_in_utyp_open_utyp_wrt_utyp_upper C (utyp_var_f α)) as HU.
    simpl in HU. fsetdec.
  - (* forall_syn *)
    pick fresh α for (L `union` ftvar_in_btyp B `union` ftvar_in_utyp C).
    specialize (H0 α ltac:(solve_notin_auto)).
    pose proof (ftvar_in_btyp_open_btyp_wrt_btyp_lower B (btyp_var_f α)) as HL.
    pose proof (ftvar_in_utyp_open_utyp_wrt_utyp_upper C (utyp_var_f α)) as HU.
    simpl in HU. fsetdec.
Qed.

(* ===================================================================== *)
(*  The Forall admissibility bridge                                        *)
(* ===================================================================== *)

(** The paper's "interesting case" [dtylab{Forall}]: a [∀]-generalised value
    [V] is admissible in [d_sd_typing].  For [λ]-values the [∀] is the folded
    [abs_check_step] / [abs_anno_check_step] (proved here).  For base-term
    values the [∀] is re-wrapped around the embedded subtyping of the
    per-instance rule by [d_sub__forall_r]: the subtyping SOURCE is [α0]-free
    (unit: closed; var: bound in [Γ]; anno: syntactic in [V]), so the per-[α]
    subtyping is the [α0]-instance renamed ([d_sub_rename_tvar]) and the anno
    rule's checked premise survives dropping [α0] ([d_sd_typing_subst_unit],
    an identity substitution). *)
Lemma d_sd_typing_forall_admissible : forall L Γ V B,
    is_value V ->
    (forall α, α `notin` L ->
       d_sd_typing mode_tc ((α ~ dbind_tvar) ++ Γ) V (open_btyp_wrt_btyp B (btyp_var_f α))) ->
    d_sd_typing mode_tc Γ V (btyp_all_inh B).
Proof.
  intros L Γ V B Hv IH.
  inversion Hv; subst.
  - (* unit *)
    pick fresh α0 for (L `union` dom Γ `union` ftvar_in_btyp B).
    pose proof (IH α0 ltac:(solve_notin_auto)) as IH0. inversion IH0; subst.
    match goal with
    | Hs : empty ⨟ _ ⊢[ mode_tc ] ptyp_to_utyp_syn ptyp_unit ⩽ _ |- _ =>
        rename Hs into Hs0
    end.
    assert (Hia : is_ityp (btyp_all_inh B)).
    { apply is_ityp__all with (L := {{α0}} `union` ftvar_in_btyp B). intros β Hβ.
      pose proof (is_ityp_rename_tvar α0 β (mod_comp_ty_tc_inv _ (d_sub_skmod Hs0))) as Hir.
      rewrite <- (subst_btyp_in_btyp_intro α0 B (btyp_var_f β)) in Hir by fsetdec.
      exact Hir. }
    apply d_sd_typing__unit.
    apply d_sub__forall_r with (L := dom Γ `union` {{α0}} `union` ftvar_in_btyp B);
      [ exact Hia | ].
    intros α Hα.
    pose proof (d_sub_rename_tvar (β := α) Hs0 nil Γ α0
                  ltac:(reflexivity) ltac:(simpl; solve_notin_auto)) as Hren.
    simpl in Hren.
    (* [simpl] already reduced the [α0 := α] substitution on the closed LHS. *)
    rewrite <- (subst_btyp_in_btyp_intro α0 B (btyp_var_f α)) in Hren by fsetdec.
    exact Hren.
  - (* var *)
    pick fresh α0 for (L `union` dom Γ `union` ftvar_in_btyp B `union` ftvar_in_denv Γ).
    pose proof (IH α0 ltac:(solve_notin_auto)) as IH0. inversion IH0; subst.
    match goal with
    | Hb : binds _ (dbind_typ _) ((α0 ~ dbind_tvar) ++ Γ),
      Hs : empty ⨟ _ ⊢[ mode_tc ] ptyp_to_utyp_syn _ ⩽ _ |- _ =>
        rename Hb into Hb0; rename Hs into Hs0
    end.
    match goal with
    | Hb0' : binds _ (dbind_typ ?AA) ((α0 ~ dbind_tvar) ++ Γ) |- _ =>
        assert (HbΓ : binds x (dbind_typ AA) Γ) by (analyze_binds Hb0');
        assert (HX0A : α0 `notin` ftvar_in_ptyp AA)
          by (pose proof (ftvar_in_denv_binds_typ _ _ _ HbΓ); fsetdec)
    end.
    assert (Hia : is_ityp (btyp_all_inh B)).
    { apply is_ityp__all with (L := {{α0}} `union` ftvar_in_btyp B). intros β Hβ.
      pose proof (is_ityp_rename_tvar α0 β (mod_comp_ty_tc_inv _ (d_sub_skmod Hs0))) as Hir.
      rewrite <- (subst_btyp_in_btyp_intro α0 B (btyp_var_f β)) in Hir by fsetdec.
      exact Hir. }
    eapply d_sd_typing__var; [ exact HbΓ | ].
    apply d_sub__forall_r with (L := dom Γ `union` {{α0}} `union` ftvar_in_btyp B);
      [ exact Hia | ].
    intros α Hα.
    pose proof (d_sub_rename_tvar (β := α) Hs0 nil Γ α0
                  ltac:(reflexivity) ltac:(simpl; solve_notin_auto)) as Hren.
    simpl in Hren.
    rewrite (subst_utyp_in_utyp_fresh_eq _ (utyp_var_f α) α0)
      in Hren by (rewrite ftvar_ptyp_to_utyp_syn; exact HX0A).
    rewrite <- (subst_btyp_in_btyp_intro α0 B (btyp_var_f α)) in Hren by fsetdec.
    exact Hren.
  - (* λx.M : the folded ∀-peel.  [is_ityp (btyp_all_inh B)] is recovered from
       the per-instance typings: each [open B α] types the lambda at [tc], so is
       inherited ([d_sd_typing_tc_abs_is_ityp]). *)
    apply d_sd_typing__abs_check_step with (L := L);
      [ apply is_ityp__all with (L := L); intros α Hα;
        exact (d_sd_typing_tc_abs_is_ityp _ _ _ (IH α Hα))
      | assumption ].
  - (* λxᴬ.M : the folded ∀-peel (as above). *)
    apply d_sd_typing__abs_anno_check_step with (L := L);
      [ apply is_ityp__all with (L := L); intros α Hα;
        exact (d_sd_typing_tc_abs_anno_is_ityp _ _ _ _ (IH α Hα))
      | assumption ].
  - (* (M : A) : the checked premise is strengthened to [Γ] by [α0 := unit]
       (identity: [α0] fresh for [e] and [A]); the subtyping is re-wrapped. *)
    pick fresh α0 for (L `union` dom Γ `union` ftvar_in_btyp B `union` ftvar_in_denv Γ
                         `union` ftvar_in_exp (exp_anno e A)).
    pose proof (IH α0 ltac:(solve_notin_auto)) as IH0. inversion IH0; subst.
    match goal with
    | Hp : d_sd_typing mode_tc ((α0 ~ dbind_tvar) ++ Γ) e (ptyp_to_btyp_inh A),
      Hs : empty ⨟ _ ⊢[ mode_tc ] ptyp_to_utyp_syn A ⩽ _ |- _ =>
        rename Hp into Hp0; rename Hs into Hs0
    end.
    assert (HX0A : α0 `notin` ftvar_in_ptyp A) by (simpl in Fr; fsetdec).
    assert (Hia : is_ityp (btyp_all_inh B)).
    { apply is_ityp__all with (L := {{α0}} `union` ftvar_in_btyp B). intros β Hβ.
      pose proof (is_ityp_rename_tvar α0 β (mod_comp_ty_tc_inv _ (d_sub_skmod Hs0))) as Hir.
      rewrite <- (subst_btyp_in_btyp_intro α0 B (btyp_var_f β)) in Hir by fsetdec.
      exact Hir. }
    eapply d_sd_typing__anno.
    + pose proof (d_sd_typing_subst_unit _ _ _ _ Hp0 nil α0 Γ
                    ltac:(reflexivity) ltac:(apply tvar_clean_fresh; solve_notin_auto)) as Hsg.
      simpl in Hsg.
      rewrite subst_ptyp_in_exp_fresh_eq in Hsg by (simpl in Fr; fsetdec).
      rewrite ptyp_to_btyp_inh_subst_unit in Hsg.
      rewrite (subst_ptyp_in_ptyp_fresh_eq A ptyp_unit α0) in Hsg by exact HX0A.
      exact Hsg.
    + apply d_sub__forall_r with
        (L := dom Γ `union` {{α0}} `union` ftvar_in_ptyp A `union` ftvar_in_btyp B);
        [ exact Hia | ].
      intros α Hα.
      pose proof (d_sub_rename_tvar (β := α) Hs0 nil Γ α0
                    ltac:(reflexivity) ltac:(simpl; solve_notin_auto)) as Hren.
      simpl in Hren.
      rewrite (subst_utyp_in_utyp_fresh_eq (ptyp_to_utyp_syn A) (utyp_var_f α) α0)
        in Hren by (rewrite ftvar_ptyp_to_utyp_syn; exact HX0A).
      rewrite <- (subst_btyp_in_btyp_intro α0 B (btyp_var_f α)) in Hren by fsetdec.
      exact Hren.
Qed.

(* ===================================================================== *)
(*  Completeness                                                          *)
(* ===================================================================== *)

(** Completeness needs [d_wf_denv Γ]: the embedded base rules demand a
    REFLEXIVE [ti]-subtyping [syn{A} ⩽ syn{A}] ([d_sub__infer] over
    [d_consis_syn_refl]), which requires the binding / annotation type
    well-formed; and the [Sub] case consumes the sd-side general
    subsumption. *)
Theorem d_sd_typing_complete : forall M Γ e B,
    Γ ⊢[ M ] e ⦂ B -> d_wf_denv Γ -> Γ ⊢ˢ[ M ] e ⦂ B.
Proof.
  intros M Γ e B H. induction H; intros Hwf.
  - (* unit *)
    apply d_sd_typing__unit.
    apply d_sub__infer;
      [ apply d_consis__unit; fsetdec | apply is_styp__unit | fsetdec ].
  - (* var: reflexive subtyping over the binding painting. *)
    assert (HwfA : d_wf_ptyp Γ A) by (eapply d_wf_denv_binds_ptyp; eauto).
    eapply d_sd_typing__var; [ eassumption | ].
    apply d_sub__infer;
      [ apply d_consis_syn_refl; exact HwfA
      | apply is_styp_ptyp_to_btyp_syn; eapply d_wf_ptyp_lc; exact HwfA
      | fsetdec ].
  - (* anno: the annotation is well-formed by regularity of the tc premise. *)
    assert (HwfA : d_wf_ptyp Γ A).
    { apply d_wf_ptyp_of_btyp_inh. eapply d_typing_wf_btyp; eassumption. }
    eapply d_sd_typing__anno; [ apply IHd_typing; exact Hwf | ].
    apply d_sub__infer;
      [ apply d_consis_syn_refl; exact HwfA
      | apply is_styp_ptyp_to_btyp_syn; eapply d_wf_ptyp_lc; exact HwfA
      | fsetdec ].
  - (* sub: the sd-side general subsumption (the headline) discharges the
       UNRESTRICTED [Sub] rule. *)
    eapply d_sd_typing_general_subsumption;
      [ exact Hwf | apply IHd_typing; exact Hwf | assumption ].
  - (* freeze *)
    apply d_sd_typing__freeze. apply IHd_typing; exact Hwf.
  - (* forall: folded ∀ via the admissibility bridge *)
    apply d_sd_typing_forall_admissible with (L := L `union` dom Γ);
      [ assumption | ].
    intros α Hα. apply H1;
      [ fsetdec | apply d_wf_denv__tvar; [ exact Hwf | fsetdec ] ].
  - (* abs: d_typing's Abs is general; d_syn splits on the mode — [m≠tc] is
       [__abs], the [tc] case folds into [__abs_check_base]. *)
    destruct m as [ | | m' ].
    + apply d_sd_typing__abs with (L := L `union` dom Γ);
        [ discriminate | assumption | assumption | ].
      intros x Hx. apply H2;
        [ fsetdec | apply d_wf_denv__typ; [ exact Hwf | fsetdec | assumption ] ].
    + apply d_sd_typing__abs_check_base with (L := L `union` dom Γ);
        [ assumption
        | apply is_ityp_arrow_r with (B1 := ptyp_to_btyp_inh A);
          apply mod_comp_ty_tc_inv; assumption
        | ].
      intros x Hx. apply H2;
        [ fsetdec | apply d_wf_denv__typ; [ exact Hwf | fsetdec | assumption ] ].
    + apply d_sd_typing__abs with (L := L `union` dom Γ);
        [ discriminate | assumption | assumption | ].
      intros x Hx. apply H2;
        [ fsetdec | apply d_wf_denv__typ; [ exact Hwf | fsetdec | assumption ] ].
  - (* abs_anno: as [abs]; the [tc] case is [__abs_anno_check_base].  The skmod
       premise forces the domain inherited at [tc]: [is_ityp B1] + [erase B1 = A]
       give [B1 = inh A]. *)
    destruct m as [ | | m' ].
    + apply d_sd_typing__abs_anno with (L := L `union` dom Γ) (B1 := B1);
        [ discriminate | assumption | assumption | assumption | ].
      intros x Hx. apply H3;
        [ fsetdec | apply d_wf_denv__typ; [ exact Hwf | fsetdec | assumption ] ].
    + assert (Hia : is_ityp (btyp_arrow B1 B2)) by (apply mod_comp_ty_tc_inv; assumption).
      assert (HB1 : ptyp_to_btyp_inh A = B1).
      { pose proof (is_ityp_ptyp_to_btyp_inh (is_ityp_arrow_l _ _ Hia)) as HR.
        rewrite H0 in HR. exact HR. }
      rewrite <- HB1.
      apply d_sd_typing__abs_anno_check_base with (L := L `union` dom Γ);
        [ assumption | exact (is_ityp_arrow_r _ _ Hia) | ].
      intros x Hx. apply H3;
        [ fsetdec | apply d_wf_denv__typ; [ exact Hwf | fsetdec | assumption ] ].
    + apply d_sd_typing__abs_anno with (L := L `union` dom Γ) (B1 := B1);
        [ discriminate | assumption | assumption | assumption | ].
      intros x Hx. apply H3;
        [ fsetdec | apply d_wf_denv__typ; [ exact Hwf | fsetdec | assumption ] ].
  - (* app *)
    eapply d_sd_typing__app;
      [ eassumption | eassumption
      | apply IHd_typing1; exact Hwf | apply IHd_typing2; exact Hwf ].
Qed.

(* ===================================================================== *)
(*  [d_typing]-side corollaries via the equivalence                       *)
(* ===================================================================== *)

(** On [d_typing], general subsumption is now the (unrestricted) [Sub] RULE. *)
Corollary d_typing_general_subsumption : forall Γ e A B m,
    Γ ⊢[ mode_ti ] e ⦂ ptyp_to_btyp_syn A ->
    empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⩽ B ->
    Γ ⊢[ m ] e ⦂ B.
Proof. intros. eapply d_typing__sub; eassumption. Qed.

(** The [FN^n] spine general subsumption, transported back to [d_typing]
    through the equivalence (the sd-side spine lemma carries the proof). *)
Corollary d_typing_general_subsumption_spine : forall m1 Γ e Bfull,
    d_wf_denv Γ ->
    Γ ⊢[ m1 ] e ⦂ Bfull ->
    forall n B' M B Bres,
      is_fn_n n m1 ->
      btyp_spine n Bfull B' B Bres ->
      empty ⨟ Γ ⊢[ M ] (btyp_to_utyp_syn B') ⩽ B ->
      Γ ⊢[ mode_fn_n_subst m1 M ] e ⦂ Bres.
Proof.
  intros m1 Γ e Bfull Hwf Hty n B' M B Bres Hfn Hspine Htail.
  apply d_sd_typing_sound.
  eapply d_sd_typing_general_subsumption_spine;
    [ apply d_sd_typing_complete; [ exact Hty | exact Hwf ]
    | apply ctx_weaken_refl
    | eassumption | eassumption | eassumption ].
Qed.
