(** ⚠️ DO NOT MERGE THIS INTO [prop_precise.v] — import CYCLE.  Context
    precision is stated over the SUBTYPING and PATTERN judgements, so this file
    sits above [algo/sub/] and [algo/pat/], both of which reach back to
    [prop_precise].  Checked 2026-08-09 during the file-reorg pass. *)

(** CONTEXT PRECISION (hand-off section D §5) — the paper's [⪯ctx]
    ("Definition (Context precision)", proofs.tex) and
    lemma:context-precision-skeleton ("Context precision preserves skeleton
    inference").

    ⭐ THE VAR ROW IS THE WHOLE LEMMA.  Every other row either ignores the
    context's term entries (the type-level premises transport by the
    [aenv_tbinds_le] [_mono] family of prop_ctx_mono.v — the "context-change
    lemma" the paper's proof sketch names) or extends both contexts with the
    SAME entry (precision is reflexive).  [P-Var] alone reads a term entry,
    and its counterpart transport is lemma:precision-sub
    ([ad_precise_extends_pat_sub], prop_completeness_sub_precise.v) — whose
    external wf side condition is discharged by the counterpart-wf premise
    the base rows now carry (hand-off §5; supplied from the algorithm by
    prop_wf_preservation.v). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo.def_meta.
Require Import src.frost.deco_algo.def_decorated.
Require Import src.frost.algo_decl.def_consis_refine.
Require Import src.frost.algo_decl.def_subtyping.
Require Import src.frost.algo_decl.def_typing.
Require Import src.frost.algo_decl.prop_ctx_mono.
Require Import src.frost.algo.prop_stability.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.algo.prop_refine.
Require Import src.frost.algo.prop_precise.
Require Import src.frost.algo.consis.prop_completeness_consis.
Require Import src.frost.algo.sub.prop_completeness_sub_precise.
Require Import src.frost.algo.pat.prop_soundness_pat.

Set Implicit Arguments.

(* the judgement notations below live in this scope; `Open Scope` is not
   transitive through `Require Import`, so the DECLARING file must open it *)
Open Scope frost_ad_scope.

Reserved Notation "{{ Θ' ⪯ᶜᵗˣ Θ }}ad" (at level 0, Θ at level 74,
   format "'{{'  Θ'  ⪯ᶜᵗˣ  Θ  '}}ad'").

(* ===================================================================== *)
(*  §1  The definition (paper's ⪯ctx, three rules)                        *)
(* ===================================================================== *)

(** [Θ' ⪯ctx Θ]: same non-term entries, term entries more precise.  The
    paper's single [x : P] entry covers the mech's two term [abind] forms
    through [abind_to_pskl] (a type binding reads as its skeleton). *)
Inductive ad_ctx_precise : aenv -> aenv -> Prop :=
| ad_ctx_precise__nil :
    {{ nil ⪯ᶜᵗˣ nil }}ad
| ad_ctx_precise__copy : forall Θ' Θ x (b : abind),
    ~ abind_is_tm b ->
    {{ Θ' ⪯ᶜᵗˣ Θ }}ad ->
    {{ ((x ~ b) ++ Θ') ⪯ᶜᵗˣ ((x ~ b) ++ Θ) }}ad
| ad_ctx_precise__tm : forall Θ' Θ x (b' b : abind) (P' P : pskl),
    abind_to_pskl b' = Some P' ->
    abind_to_pskl b = Some P ->
    {{ Θ' ⨟ empty ⊢ₚᵣ P' ⊑ P }}ad ->
    {{ Θ' ⪯ᶜᵗˣ Θ }}ad ->
    {{ ((x ~ b') ++ Θ') ⪯ᶜᵗˣ ((x ~ b) ++ Θ) }}ad
where "{{ Θ' ⪯ᶜᵗˣ Θ }}ad" := (ad_ctx_precise Θ' Θ) : frost_ad_scope.

(* ===================================================================== *)
(*  §2  Structure: domains agree, non-term entries agree                  *)
(* ===================================================================== *)

Lemma ad_ctx_precise_dom : forall Θ' Θ,
  {{ Θ' ⪯ᶜᵗˣ Θ }}ad -> dom Θ' [=] dom Θ.
Proof.
  intros Θ' Θ H; induction H; simpl; fsetdec.
Qed.

(** The type-level entries are the SAME — the [_mono] family's hypothesis,
    in both directions. *)
Lemma ad_ctx_precise_tbinds_le : forall Θ' Θ,
  {{ Θ' ⪯ᶜᵗˣ Θ }}ad -> aenv_tbinds_le Θ Θ'.
Proof.
  intros Θ' Θ H; induction H; intros α b0 Hty Hb.
  - exact Hb.
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> ->] | Hb'];
      [ unfold binds; simpl; left; reflexivity
      | apply binds_cons_3; apply IHad_ctx_precise; assumption ].
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> ->] | Hb'].
    + exfalso. destruct b; simpl in *; solve [ contradiction | congruence ].
    + apply binds_cons_3; apply IHad_ctx_precise; assumption.
Qed.

(** The Var inversion: a term entry of [Θ] has a more precise counterpart
    in [Θ'].  Needs [uniq Θ] — [binds] is positional only up to
    duplicates. *)
Lemma ad_ctx_precise_binds_tm : forall Θ' Θ x (b : abind) (P : pskl),
  {{ Θ' ⪯ᶜᵗˣ Θ }}ad ->
  uniq Θ ->
  binds x b Θ ->
  abind_to_pskl b = Some P ->
  exists (b' : abind) (P' : pskl),
    binds x b' Θ' /\ abind_to_pskl b' = Some P' /\
    {{ Θ' ⨟ empty ⊢ₚᵣ P' ⊑ P }}ad.
Proof.
  intros Θ' Θ x b P H; induction H; intros Huq Hb HP.
  - inversion Hb.
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> ->] | Hb'].
    + (* the rule's entry shadows the lemma's [b]: it is [b0] here *)
      exfalso. apply H. destruct b0; simpl in *; try congruence; exact I.
    + inversion Huq; subst.
      destruct (IHad_ctx_precise ltac:(assumption) Hb' HP)
        as [b'' [P'' [Hb'' [HP'' Hprec]]]].
      exists b'', P''. split; [ apply binds_cons_3; exact Hb'' | ].
      split; [ exact HP'' | ].
      (* the precision was stated at the TAIL Θ'; weaken to the cons *)
      eapply ad_refine_syn_mono;
        [ exact Hprec
        | intros α b1 Hty Hb1; apply binds_cons_3; exact Hb1 ].
  - destruct (binds_cons_1 _ _ _ _ _ _ Hb) as [[-> ->] | Hb'].
    + rewrite H0 in HP. inversion HP; subst.
      exists b', P'. split; [ unfold binds; simpl; left; reflexivity | ].
      split; [ exact H | ].
      eapply ad_refine_syn_mono;
        [ exact H1
        | intros α b1 Hty Hb1; apply binds_cons_3; exact Hb1 ].
    + inversion Huq; subst.
      destruct (IHad_ctx_precise ltac:(assumption) Hb' HP)
        as [b'' [P'' [Hb'' [HP'' Hprec]]]].
      exists b'', P''. split; [ apply binds_cons_3; exact Hb'' | ].
      split; [ exact HP'' | ].
      eapply ad_refine_syn_mono;
        [ exact Hprec
        | intros α b1 Hty Hb1; apply binds_cons_3; exact Hb1 ].
Qed.

(* ===================================================================== *)
(*  §3  lemma:context-precision-skeleton                                  *)
(* ===================================================================== *)

Theorem ad_ctx_precise_pat : forall M Θ e Q,
  {{ Θ ⊢ˢ[ M ] e ⦂ Q }}ad ->
  forall Θ',
  {{ Θ' ⪯ᶜᵗˣ Θ }}ad ->
  {{ ⊢ Θ }}a ->
  {{ ⊢ Θ' }}a ->
  {{ Θ' ⊢ˢ[ M ] e ⦂ Q }}ad.
Proof.
  intros M Θ e Q H; induction H; intros Θ' Hctx HwfΘ HwfΘ';
    pose proof (ad_ctx_precise_tbinds_le Hctx) as Htle.
  - (* unit *)
    apply ad_pat__unit;
      [ eapply a_wf_pskl_mono; eauto | eapply ad_pat_sub_mono; eauto ].
  - (* var — THE row: transport the counterpart by lemma:precision-sub *)
    destruct (@ad_ctx_precise_binds_tm Θ' Θ x b P Hctx
                ltac:(apply a_wf_aenv_uniq; exact HwfΘ) H H0)
      as [b' [P' [Hb' [HP' Hprec]]]].
    assert (HwfQ' : {{ Θ' ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a)
      by (eapply a_wf_pskl_mono; eauto).
    eapply ad_pat__var with (b := b');
      [ exact Hb' | exact HP' | exact HwfQ' | ].
    rewrite pskl_to_uskl_via_bskl_syn.
    eapply ad_precise_extends_pat_sub with (Δ := empty) (P := P);
      [ exact Hprec
      | rewrite <- pskl_to_uskl_via_bskl_syn;
        eapply ad_pat_sub_mono; eauto
      | exact HwfΘ'
      | exact HwfQ'
      | intros Hd; discriminate ].
  - (* anno *)
    apply ad_pat__anno;
      [ eapply a_wf_ptyp_mono; eauto | eapply a_wf_pskl_mono; eauto
      | eapply ad_pat_sub_mono; eauto ].
  - (* freeze *)
    apply ad_pat__freeze; auto.
  - (* abs — extend both contexts with the SAME entry (precision refl) *)
    assert (HwfP' : {{ Θ' ⨟ empty ⊢ₚₛ P }}a)
      by (eapply a_wf_pskl_mono; eauto).
    apply ad_pat__abs with (L := L `union` dom Θ');
      [ assumption | exact HwfP' | assumption | ].
    intros x Hx.
    apply H3;
      [ clear - Hx; fsetdec
      | apply ad_ctx_precise__tm with (P' := P) (P := P);
          [ reflexivity | reflexivity | apply ad_precise_refl; exact HwfP'
          | exact Hctx ]
      | apply a_wf_aenv__var;
          [ pose proof (ad_ctx_precise_dom Hctx) as Hd;
            clear - Hx Hd; fsetdec
          | exact H0
          | exact HwfΘ ]
      | apply a_wf_aenv__var;
          [ clear - Hx; fsetdec
          | exact HwfP'
          | exact HwfΘ' ] ].
  - (* abs_anno *)
    assert (HwfA' : a_wf_ptyp Θ' A)
      by (eapply a_wf_ptyp_mono; eauto).
    apply ad_pat__abs_anno with (L := L `union` dom Θ') (B := B);
      [ assumption | exact HwfA' | assumption | assumption | ].
    intros x Hx.
    apply H4;
      [ clear - Hx; fsetdec
      | apply ad_ctx_precise__tm
          with (P' := ptyp_to_pskl A) (P := ptyp_to_pskl A);
          [ reflexivity | reflexivity
          | apply ad_precise_refl; apply a_wf_ptyp_to_wf_pskl; exact HwfA'
          | exact Hctx ]
      | apply a_wf_aenv__var_typ;
          [ pose proof (ad_ctx_precise_dom Hctx) as Hd;
            clear - Hx Hd; fsetdec
          | exact H0
          | exact HwfΘ ]
      | apply a_wf_aenv__var_typ;
          [ clear - Hx; fsetdec | exact HwfA' | exact HwfΘ' ] ].
  - (* app *)
    eapply ad_pat__app;
      [ auto | eapply ad_refine_syn_mono; eauto | auto ].
  - (* abs_check *)
    apply ad_pat__abs_check with (L := L `union` dom Θ').
    intros x Hx.
    apply H0;
      [ clear - Hx; fsetdec
      | apply ad_ctx_precise__tm with (P' := pskl_hole) (P := pskl_hole);
          [ reflexivity | reflexivity
          | apply ad_precise_refl; apply a_wf_pskl__hole | exact Hctx ]
      | apply a_wf_aenv__var;
          [ pose proof (ad_ctx_precise_dom Hctx) as Hd;
            clear - Hx Hd; fsetdec
          | apply a_wf_pskl__hole | exact HwfΘ ]
      | apply a_wf_aenv__var;
          [ clear - Hx; fsetdec | apply a_wf_pskl__hole | exact HwfΘ' ] ].
  - (* abs_anno_check *)
    assert (HwfA' : a_wf_ptyp Θ' A)
      by (eapply a_wf_ptyp_mono; eauto).
    apply ad_pat__abs_anno_check with (L := L `union` dom Θ') (P := P);
      [ exact HwfA' | ].
    intros x Hx.
    apply H1;
      [ clear - Hx; fsetdec
      | apply ad_ctx_precise__tm
          with (P' := ptyp_to_pskl A) (P := ptyp_to_pskl A);
          [ reflexivity | reflexivity
          | apply ad_precise_refl; apply a_wf_ptyp_to_wf_pskl; exact HwfA'
          | exact Hctx ]
      | apply a_wf_aenv__var_typ;
          [ pose proof (ad_ctx_precise_dom Hctx) as Hd;
            clear - Hx Hd; fsetdec
          | exact H
          | exact HwfΘ ]
      | apply a_wf_aenv__var_typ;
          [ clear - Hx; fsetdec | exact HwfA' | exact HwfΘ' ] ].
Qed.
