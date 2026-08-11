(** CONTEXT MONOTONICITY of the [ad_*] layer, and section D's SUFFIX MOVING
    (paper proofs.tex, lemma:suffix-moving).

    ⭐ THE OBSERVATION THAT MAKES THIS ONE LEMMA INSTEAD OF FIVE.  Every
    declarative-judgement-over-Θ reads its context in exactly two ways: a
    [binds] (a flexible's definition, a term variable's entry) and
    [a_binds_tvar] — which is itself a three-way disjunction of [binds]
    (algo/def_extra.v:145).  Nothing in the layer is ANTI-monotone: the
    negative side conditions that do appear ([a_non_flex], [a_flex_tvar]) live
    in the ALGORITHMIC judgments, not here.  So each judgement is stable under
    ANY context change that preserves [binds], and one relation
    ([aenv_binds_le]) discharges weakening, exchange and block-permutation at
    once, for all of them.

    ⚙ CONSEQUENCE FOR THE PAPER'S STATEMENT.  lemma:suffix-moving reads

        if [typp[M]{Θ1,Θ2,Ξ}{M}{bid A}] where Ξ does not depend on entries in
        Θ2, then [typp[M]{Θ1,Ξ,Θ2}{M}{bid A}]

    and the mechanized version needs NO side condition at all: a permutation
    of context BLOCKS preserves [binds] in both directions, so the typing
    judgement transports outright.  The paper's "Ξ does not depend on Θ2" is
    what keeps the RESULT well-formed ([Θ ⊢ ctx] orders definitions), which is
    a separate obligation from the judgement moving — see
    [ad_sd_typing_suffix_moving] below.  Dropping a premise only strengthens
    the lemma, so nothing downstream is at risk.

    ⛔ NOT here: lemma:suffix-erasure.  Erasure goes the other way — it must
    show the derivation never LOOKED into Ξ — so it is not a [binds]-monotone
    statement and needs the freshness invariant the paper states.  It is the
    next item in docs/HANDOFF-section-d.md §1. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_extra.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo_decl.def_decl_algo.
Require Import src.frost.algo_decl.def_decl_algo_sub.
Require Import src.frost.algo_decl.def_decl_algo_typing.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  The relation                                                      *)
(* ===================================================================== *)

(** [Θ'] sees every entry [Θ] sees.  Deliberately NOT [uniq]-aware: [binds]
    is plain list membership, so this is exactly "no lookup is lost", which is
    all any [ad_*] rule needs. *)
Definition aenv_binds_le (Θ Θ' : aenv) : Prop :=
  forall x b, binds x b Θ -> binds x b Θ'.

Lemma aenv_binds_le_refl : forall Θ, aenv_binds_le Θ Θ.
Proof. intros Θ x b H; exact H. Qed.

Lemma aenv_binds_le_trans : forall Θ1 Θ2 Θ3,
  aenv_binds_le Θ1 Θ2 -> aenv_binds_le Θ2 Θ3 -> aenv_binds_le Θ1 Θ3.
Proof. intros * H12 H23 x b H; auto. Qed.

(** The shape every binder row needs: pushing the SAME entry on both sides. *)
Lemma aenv_binds_le_cons : forall Θ Θ' x (b : abind),
  aenv_binds_le Θ Θ' -> aenv_binds_le ((x ~ b) ++ Θ) ((x ~ b) ++ Θ').
Proof.
  intros Θ Θ' x b Hle y c Hy.
  apply binds_app_1 in Hy as [Hy | Hy]; [ apply binds_app_2 | ]; auto.
Qed.

(** Weakening at the front — the [Ξ ++ Θ] shape the algorithm produces. *)
Lemma aenv_binds_le_weaken_l : forall Ξ Θ, aenv_binds_le Θ (Ξ ++ Θ).
Proof. intros Ξ Θ x b H; auto. Qed.

(** ⭐ Permuting context BLOCKS is [binds]-invariant in BOTH directions —
    [binds] over an append is plain membership, so a block permutation is a
    membership-preserving bijection.  This is what makes suffix moving free. *)
Lemma aenv_binds_le_perm3 : forall (Θa Θb Θc : aenv),
  aenv_binds_le (Θa ++ Θb ++ Θc) (Θb ++ Θa ++ Θc).
Proof.
  intros Θa Θb Θc x b H.
  apply binds_app_1 in H as [H | H].
  - apply binds_app_3; apply binds_app_2; exact H.
  - apply binds_app_1 in H as [H | H].
    + apply binds_app_2; exact H.
    + apply binds_app_3; apply binds_app_3; exact H.
Qed.

(* ===================================================================== *)
(*  §1b  The TYPE-LEVEL restriction of the relation                       *)
(*                                                                        *)
(*  The paper's soundness proofs say refinement judgements are stable     *)
(*  under dropping term variables (proofs.tex, Abs cases).  Dropping an   *)
(*  entry is NOT [binds]-monotone, but every judgement in §2–§4 except     *)
(*  [ad_pat] / [ad_sd_typing] reads the context ONLY at type-level         *)
(*  entries ([a_binds_tvar], a flexible's definition) — term entries are   *)
(*  invisible to them.  So those lemmas take the weaker premise below,     *)
(*  and "drop a term variable" ([aenv_tbinds_le_strip_tm]) is one          *)
(*  instance of it, alongside everything [aenv_binds_le] already gave.     *)
(* ===================================================================== *)

(** Type-level entries: what [a_binds_tvar] and the FlexL/FlexR lookups
    can see.  The two term forms are the invisible ones. *)
Definition abind_is_ty (b : abind) : Prop :=
  match b with
  | abind_tvar | abind_flex_mono | abind_flex_mono_def _ => True
  | abind_var_typ _ | abind_var_skl _ => False
  end.

(** [Θ'] sees every TYPE-LEVEL entry [Θ] sees. *)
Definition aenv_tbinds_le (Θ Θ' : aenv) : Prop :=
  forall α b, abind_is_ty b -> binds α b Θ -> binds α b Θ'.

Lemma aenv_tbinds_le_of_binds_le : forall Θ Θ',
  aenv_binds_le Θ Θ' -> aenv_tbinds_le Θ Θ'.
Proof. intros Θ Θ' Hle α b _ H; auto. Qed.

Lemma aenv_tbinds_le_cons : forall Θ Θ' x (b : abind),
  aenv_tbinds_le Θ Θ' -> aenv_tbinds_le ((x ~ b) ++ Θ) ((x ~ b) ++ Θ').
Proof.
  intros Θ Θ' x b Hle y c Hc Hy.
  apply binds_app_1 in Hy as [Hy | Hy]; [ apply binds_app_2 | ]; auto.
Qed.

(** ⭐ Dropping a TERM entry loses no type-level lookup. *)
Lemma aenv_tbinds_le_strip_tm : forall Θ1 x (b : abind) Θ2,
  ~ abind_is_ty b ->
  aenv_tbinds_le (Θ1 ++ (x ~ b) ++ Θ2) (Θ1 ++ Θ2).
Proof.
  intros Θ1 x b Θ2 Htm y c Hc Hy.
  apply binds_app_1 in Hy as [Hy | Hy]; [ apply binds_app_2; exact Hy | ].
  apply binds_app_1 in Hy as [Hy | Hy]; [ | apply binds_app_3; exact Hy ].
  apply binds_one_1 in Hy as Heq. destruct Hy as [Hpair | []].
  inversion Hpair; subst. contradiction.
Qed.

(** The two lookup shapes the judgements actually perform. *)
Lemma aenv_tbinds_le_flex_def : forall Θ Θ' α τ,
  aenv_tbinds_le Θ Θ' ->
  binds α (abind_flex_mono_def τ) Θ ->
  binds α (abind_flex_mono_def τ) Θ'.
Proof. intros Θ Θ' α τ Hle H; apply Hle; [ exact I | exact H ]. Qed.

(* ===================================================================== *)
(*  §2  The syntactic / well-formedness layer                             *)
(*                                                                        *)
(*  ⚙ Every proof below is EXPLICIT per constructor rather than            *)
(*  [econstructor; eauto].  Not style: [econstructor] on a cofinite rule   *)
(*  SHELVES the avoid-set evar [?L], so the premise goal never reaches the *)
(*  following tactic and resurfaces at [Qed] as "incomplete proof".        *)
(*  Supplying [L] by hand is also what keeps these cheap — the whole file  *)
(*  is well under a second.                                               *)
(* ===================================================================== *)

Lemma a_binds_tvar_mono : forall Θ Θ' α,
  aenv_tbinds_le Θ Θ' -> a_binds_tvar α Θ -> a_binds_tvar α Θ'.
Proof.
  intros Θ Θ' α Hle [H | [H | [τ H]]];
    [ left | right; left | right; right; exists τ ];
    apply Hle; solve [ exact I | exact H ].
Qed.

Lemma a_wf_ptyp_mono : forall Θ A,
  a_wf_ptyp Θ A ->
  forall Θ', aenv_tbinds_le Θ Θ' -> a_wf_ptyp Θ' A.
Proof.
  intros Θ A H; induction H; intros Θ' Hle.
  - apply a_wf_ptyp__unit.
  - apply a_wf_ptyp__var. eapply a_binds_tvar_mono; eauto.
  - apply a_wf_ptyp__arrow; auto.
  - apply a_wf_ptyp__all with (L := L). intros α Hα.
    apply H0; [ exact Hα | apply aenv_tbinds_le_cons; exact Hle ].
Qed.

Lemma a_wf_pskl_mono : forall Θ Δ P,
  a_wf_pskl Θ Δ P ->
  forall Θ', aenv_tbinds_le Θ Θ' -> a_wf_pskl Θ' Δ P.
Proof.
  intros Θ Δ P H; induction H; intros Θ' Hle.
  - apply a_wf_pskl__unit.
  - apply a_wf_pskl__var.
    destruct H as [HΔ | Htv]; [ left; exact HΔ | right ].
    eapply a_binds_tvar_mono; eauto.
  - apply a_wf_pskl__arrow; auto.
  - (* ∀ : the binder goes into Δ, NOT into Θ *)
    apply a_wf_pskl__all with (L := L). intros α Hα. apply H0; auto.
  - apply a_wf_pskl__hole.
  - apply a_wf_pskl__tophole; auto.
Qed.

(** The Δ-free scoping judgement — same proof as [a_wf_pskl_mono], except
    that here the ∀-binder enters the CONTEXT rather than Δ.  Needed to
    transport a term entry's payload when a term entry is dropped from the
    middle of a well-formed context ([a_wf_aenv_strip_tm_mid]). *)
Lemma a_scope_pskl_mono : forall Θ P,
  a_scope_pskl Θ P ->
  forall Θ', aenv_tbinds_le Θ Θ' -> a_scope_pskl Θ' P.
Proof.
  intros Θ P H; induction H; intros Θ' Hle.
  - apply a_scope_pskl__unit.
  - apply a_scope_pskl__var. eapply a_binds_tvar_mono; eauto.
  - apply a_scope_pskl__arrow; auto.
  - apply a_scope_pskl__all with (L := L). intros α Hα.
    apply H0; [ exact Hα | apply aenv_tbinds_le_cons; exact Hle ].
  - apply a_scope_pskl__hole.
  - apply a_scope_pskl__tophole; auto.
Qed.

Lemma a_tyequiv_ctx_mono : forall Θ A B,
  {{ Θ ⊢ A ≡ᵗ B }}a ->
  forall Θ', aenv_tbinds_le Θ Θ' -> {{ Θ' ⊢ A ≡ᵗ B }}a.
Proof.
  intros Θ A B H; induction H; intros Θ' Hle.
  - apply a_tyequiv__refl; assumption.
  - apply a_tyequiv__sym; auto.
  - eapply a_tyequiv__trans; eauto.
  - eapply a_tyequiv__flex_def. eapply aenv_tbinds_le_flex_def; eauto.
  - apply a_tyequiv__arrow; auto.
  - (* ∀ : the equational theory does not bind into Θ *)
    apply a_tyequiv__all with (L := L). intros α Hα. apply H0; auto.
Qed.

(* ===================================================================== *)
(*  §3  Consistency and refinement over Θ                                 *)
(* ===================================================================== *)

Lemma ad_pat_consis_mono : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  forall Θ', aenv_tbinds_le Θ Θ' -> {{ Ψ ⨟ Θ' ⊢ˢ R ∼ Q }}ad.
Proof.
  intros Ψ Θ R Q H; induction H; intros Θ' Hle.
  - apply ad_pat_consis__unit; assumption.
  - apply ad_pat_consis__var; [ assumption | eapply a_binds_tvar_mono; eauto ].
  - eapply ad_pat_consis__arrow; eauto.
  - eapply ad_pat_consis__forall_inh_tagged with (L := L);
      [ intros α Hα; apply H0; [ exact Hα | apply aenv_tbinds_le_cons; exact Hle ]
      | eassumption ].
  - eapply ad_pat_consis__forall_inh_untagged with (L := L).
    intros α Hα; apply H0; [ exact Hα | apply aenv_tbinds_le_cons; exact Hle ].
  - eapply ad_pat_consis__forall_syn_tagged with (L := L).
    intros α Hα; apply H0; [ exact Hα | apply aenv_tbinds_le_cons; exact Hle ].
  - eapply ad_pat_consis__forall_syn with (L := L).
    intros α Hα; apply H0; [ exact Hα | apply aenv_tbinds_le_cons; exact Hle ].
  - apply ad_pat_consis__ghostg; assumption.
  - apply ad_pat_consis__topholeg; auto.
  - apply ad_pat_consis__hole; [ assumption | eapply a_wf_pskl_mono; eauto ].
  - apply ad_pat_consis__tophole; auto.
  - eapply ad_pat_consis__tophole_inh with (L := L).
    intros α Hα; apply H0; [ exact Hα | apply aenv_tbinds_le_cons; exact Hle ].
  - apply ad_pat_consis__tophole_drop; auto.
  - eapply ad_pat_consis__flex_l;
      [ eapply aenv_tbinds_le_flex_def; eauto | auto ].
  - eapply ad_pat_consis__flex_r;
      [ eapply aenv_tbinds_le_flex_def; eauto | auto ].
Qed.

Lemma ad_refine_syn_mono : forall Θ Δ Q P,
  {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ P }}ad ->
  forall Θ', aenv_tbinds_le Θ Θ' -> {{ Θ' ⨟ Δ ⊢ᵣ Q ⊳ P }}ad.
Proof.
  intros Θ Δ Q P H; induction H; intros Θ' Hle.
  - apply ad_refine_syn__unit.
  - apply ad_refine_syn__var.
    destruct H as [HΔ | Htv]; [ left; exact HΔ | right ].
    eapply a_binds_tvar_mono; eauto.
  - apply ad_refine_syn__arrow; auto.
  - (* ∀ : binds into Δ *)
    apply ad_refine_syn__all with (L := L). intros α Hα. apply H0; auto.
  - apply ad_refine_syn__hole. eapply a_wf_pskl_mono; eauto.
  - apply ad_refine_syn__tophole_remove; auto.
  - (* tophole_fill : binds into Θ *)
    apply ad_refine_syn__tophole_fill with (L := L). intros α Hα.
    apply H0; [ exact Hα | apply aenv_tbinds_le_cons; exact Hle ].
  - apply ad_refine_syn__tophole_keep; auto.
  - eapply ad_refine_syn__flex_l;
      [ eapply aenv_tbinds_le_flex_def; eauto | auto ].
  - eapply ad_refine_syn__flex_r;
      [ eapply aenv_tbinds_le_flex_def; eauto | auto ].
Qed.

Lemma ad_refine_pskl_mono : forall Θ Δ P Q,
  {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ Q }}ad ->
  forall Θ', aenv_tbinds_le Θ Θ' -> {{ Θ' ⨟ Δ ⊢ᵣₚ P ⊳ Q }}ad.
Proof.
  intros Θ Δ P Q H; induction H; intros Θ' Hle.
  - apply ad_refine_pskl__unit.
  - apply ad_refine_pskl__var.
    destruct H as [HΔ | Htv]; [ left; exact HΔ | right ].
    eapply a_binds_tvar_mono; eauto.
  - apply ad_refine_pskl__arrow; auto.
  - apply ad_refine_pskl__all with (L := L). intros α Hα. apply H0; auto.
  - apply ad_refine_pskl__hole. eapply a_wf_pskl_mono; eauto.
  - apply ad_refine_pskl__tophole_remove; auto.
  - apply ad_refine_pskl__tophole_fill with (L := L). intros α Hα.
    apply H0; [ exact Hα | apply aenv_tbinds_le_cons; exact Hle ].
  - apply ad_refine_pskl__tophole_keep; auto.
  - eapply ad_refine_pskl__flex_l;
      [ eapply aenv_tbinds_le_flex_def; eauto | auto ].
  - eapply ad_refine_pskl__flex_r;
      [ eapply aenv_tbinds_le_flex_def; eauto | auto ].
Qed.

(* ===================================================================== *)
(*  §4  Subtyping, skeleton inference, typing                             *)
(* ===================================================================== *)

Lemma ad_pat_sub_mono : forall NM M Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ[ NM | M ] R ⩽ Q }}ad ->
  forall Θ', aenv_tbinds_le Θ Θ' -> {{ Ψ ⨟ Θ' ⊢ˢ[ NM | M ] R ⩽ Q }}ad.
Proof.
  intros NM M Ψ Θ R Q H; induction H; intros Θ' Hle.
  - apply ad_pat_sub__infer;
      [ assumption | eapply ad_pat_consis_mono; eauto | assumption ].
  - apply ad_pat_sub__check;
      [ assumption | assumption | eapply ad_pat_consis_mono; eauto ].
  - apply ad_pat_sub__forall_r with (L := L). intros α Hα.
    apply H0; [ exact Hα | apply aenv_tbinds_le_cons; exact Hle ].
  - apply ad_pat_sub__univ_ghost_r;
      [ assumption | assumption | assumption | assumption
      | eapply ad_pat_consis_mono; eauto ].
  - eapply ad_pat_sub__arrow;
      [ eapply ad_pat_consis_mono; eauto | auto | eassumption ].
  - eapply ad_pat_sub__forall_l_tagged;
      [ assumption | eassumption | eassumption | eassumption
      | eapply a_wf_pskl_mono; eauto | auto ].
  - eapply ad_pat_sub__forall_l_untagged;
      [ assumption | eassumption | eassumption | eassumption
      | eapply a_wf_pskl_mono; eauto | auto ].
  - apply ad_pat_sub__ghost;
      [ assumption | eapply a_wf_pskl_mono; eauto | assumption ].
  - apply ad_pat_sub__ghostg; assumption.
  - apply ad_pat_sub__univ_ghost_l; auto.
  - apply ad_pat_sub__univ_ghost_lg; auto.
  - eapply ad_pat_sub__flex_mono;
      [ eapply aenv_tbinds_le_flex_def; eauto | auto ].
Qed.

(** The LEAF-VALID mirror, fuel carried unchanged: the four leaf rows'
    refinement datum travels by [ad_refine_pskl_mono]. *)
Lemma ad_pat_sub_gv_mono : forall n NM M Ψ Θ R Q,
  ad_pat_sub_gv n NM M Ψ Θ R Q ->
  forall Θ', aenv_tbinds_le Θ Θ' -> ad_pat_sub_gv n NM M Ψ Θ' R Q.
Proof.
  intros n NM M Ψ Θ R Q H; induction H; intros Θ' Hle.
  - apply ad_pat_sub_gv__infer;
      [ assumption | eapply ad_pat_consis_mono; eauto | assumption
      | eapply ad_refine_pskl_mono; eauto ].
  - apply ad_pat_sub_gv__check;
      [ assumption | assumption | eapply ad_pat_consis_mono; eauto
      | eapply ad_refine_pskl_mono; eauto ].
  - apply ad_pat_sub_gv__forall_r with (L := L). intros α Hα.
    apply H0; [ exact Hα | apply aenv_tbinds_le_cons; exact Hle ].
  - apply ad_pat_sub_gv__univ_ghost_r;
      [ assumption | assumption | assumption | assumption
      | eapply ad_pat_consis_mono; eauto
      | eapply ad_refine_pskl_mono; eauto ].
  - eapply ad_pat_sub_gv__arrow;
      [ eapply ad_pat_consis_mono; eauto
      | eapply ad_refine_pskl_mono; eauto
      | apply IHad_pat_sub_gv; exact Hle | eassumption ].
  - eapply ad_pat_sub_gv__forall_l_tagged;
      [ assumption | eassumption | eassumption | eassumption
      | eapply a_wf_pskl_mono; eauto | apply IHad_pat_sub_gv; exact Hle ].
  - eapply ad_pat_sub_gv__forall_l_untagged;
      [ assumption | eassumption | eassumption | eassumption
      | eapply a_wf_pskl_mono; eauto | apply IHad_pat_sub_gv; exact Hle ].
  - apply ad_pat_sub_gv__ghost;
      [ assumption | eapply a_wf_pskl_mono; eauto | assumption ].
  - apply ad_pat_sub_gv__ghostg; assumption.
  - apply ad_pat_sub_gv__univ_ghost_l;
      [ assumption | apply IHad_pat_sub_gv; exact Hle ].
  - apply ad_pat_sub_gv__univ_ghost_lg;
      [ assumption | apply IHad_pat_sub_gv; exact Hle ].
  - eapply ad_pat_sub_gv__flex_mono;
      [ eapply aenv_tbinds_le_flex_def; eauto
      | apply IHad_pat_sub_gv; exact Hle ].
Qed.

Lemma ad_pat_sub_v_mono : forall NM M Ψ Θ R Q,
  ad_pat_sub_v NM M Ψ Θ R Q ->
  forall Θ', aenv_tbinds_le Θ Θ' -> ad_pat_sub_v NM M Ψ Θ' R Q.
Proof.
  intros NM M Ψ Θ R Q [n H] Θ' Hle.
  exists n. eapply ad_pat_sub_gv_mono; eauto.
Qed.

(** [ad_pat] / [ad_sd_typing] DO read term entries (their Var rules), so
    these two keep the full [aenv_binds_le]; the embedded type-level
    premises go through [aenv_tbinds_le_of_binds_le]. *)
Lemma ad_pat_mono : forall M Θ e Q,
  {{ Θ ⊢ˢ[ M ] e ⦂ Q }}ad ->
  forall Θ', aenv_binds_le Θ Θ' -> {{ Θ' ⊢ˢ[ M ] e ⦂ Q }}ad.
Proof.
  intros M Θ e Q H; induction H; intros Θ' Hle;
    pose proof (aenv_tbinds_le_of_binds_le Hle) as Htle.
  - apply ad_pat__unit;
      [ eapply a_wf_pskl_mono; eauto | eapply ad_pat_sub_v_mono; eauto ].
  - eapply ad_pat__var;
      [ eauto | eassumption | eapply a_wf_pskl_mono; eauto
      | eapply ad_pat_sub_v_mono; eauto ].
  - apply ad_pat__anno;
      [ eapply a_wf_ptyp_mono; eauto | eapply a_wf_pskl_mono; eauto
      | eapply ad_pat_sub_v_mono; eauto ].
  - apply ad_pat__freeze; auto.
  - apply ad_pat__abs with (L := L);
      [ assumption | eapply a_wf_pskl_mono; eauto | assumption | ].
    intros x Hx. apply H3; [ exact Hx | apply aenv_binds_le_cons; exact Hle ].
  - eapply ad_pat__abs_anno with (L := L);
      [ assumption | eapply a_wf_ptyp_mono; eauto | eassumption | assumption | ].
    intros x Hx. apply H4; [ exact Hx | apply aenv_binds_le_cons; exact Hle ].
  - eapply ad_pat__app;
      [ auto | eapply ad_refine_syn_mono; eauto | auto ].
  - apply ad_pat__abs_check with (L := L). intros x Hx.
    apply H0; [ exact Hx | apply aenv_binds_le_cons; exact Hle ].
  - apply ad_pat__abs_anno_check with (L := L);
      [ eapply a_wf_ptyp_mono; eauto | ].
    intros x Hx. apply H1; [ exact Hx | apply aenv_binds_le_cons; exact Hle ].
Qed.

Lemma ad_sd_typing_mono : forall M Θ e B,
  {{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad ->
  forall Θ', aenv_binds_le Θ Θ' -> {{ Θ' ⊢ˢᵈ[ M ] e ⦂ B }}ad.
Proof.
  intros M Θ e B H; induction H; intros Θ' Hle;
    pose proof (aenv_tbinds_le_of_binds_le Hle) as Htle.
  - apply ad_sd_typing__unit. eapply ad_pat_sub_v_mono; eauto.
  - eapply ad_sd_typing__var; [ eauto | eapply ad_pat_sub_v_mono; eauto ].
  - eapply ad_sd_typing__anno;
      [ eapply a_wf_ptyp_mono; eauto | auto
      | eapply ad_pat_sub_v_mono; eauto ].
  - eapply ad_sd_typing__freeze; [ auto | eapply a_tyequiv_ctx_mono; eauto ].
  - apply ad_sd_typing__abs_check_step with (L := L); [ assumption | ].
    intros α Hα. apply H1; [ exact Hα | apply aenv_binds_le_cons; exact Hle ].
  - apply ad_sd_typing__abs_check_base with (L := L);
      [ eapply a_wf_ptyp_mono; eauto | assumption | ].
    intros x Hx. apply H2; [ exact Hx | apply aenv_binds_le_cons; exact Hle ].
  - apply ad_sd_typing__abs_anno_check_step with (L := L); [ assumption | ].
    intros α Hα. apply H1; [ exact Hα | apply aenv_binds_le_cons; exact Hle ].
  - apply ad_sd_typing__abs_anno_check_base with (L := L);
      [ eapply a_wf_ptyp_mono; eauto | eapply a_tyequiv_ctx_mono; eauto
      | assumption | ].
    intros x Hx. apply H3; [ exact Hx | apply aenv_binds_le_cons; exact Hle ].
  - apply ad_sd_typing__abs with (L := L);
      [ assumption | eapply a_wf_ptyp_mono; eauto | assumption | ].
    intros x Hx. apply H3; [ exact Hx | apply aenv_binds_le_cons; exact Hle ].
  - eapply ad_sd_typing__abs_anno with (L := L);
      [ assumption | eapply a_wf_ptyp_mono; eauto
      | eapply a_tyequiv_ctx_mono; eauto | eassumption | assumption | ].
    intros x Hx. apply H5; [ exact Hx | apply aenv_binds_le_cons; exact Hle ].
  - eapply ad_sd_typing__app;
      [ eapply ad_pat_mono; eauto | eapply ad_refine_syn_mono; eauto
      | auto | eapply a_tyequiv_ctx_mono; eauto | auto ].
Qed.

(* ===================================================================== *)
(*  §5  Lemma [Suffix moving]  (proofs.tex, lemma:suffix-moving)          *)
(* ===================================================================== *)

(** The paper's [Θ1,Θ2,Ξ] is [Ξ ++ Θ2 ++ Θ1] here: the mechanization's
    contexts grow at the FRONT (every algorithmic rule pushes with [++]).

    ⚙ NO SIDE CONDITION.  The paper requires "Ξ does not depend on entries in
    Θ2"; the judgement does not need it, because the move is a permutation of
    BLOCKS and [binds] is invariant under it.  That condition belongs to the
    well-formedness of the moved context ([Θ ⊢ ctx] orders definitions before
    their uses), which is a separate obligation a caller discharges where it
    needs [a_wf_aenv].  A dropped premise only strengthens the lemma. *)
Corollary ad_sd_typing_suffix_moving : forall M Θ1 Θ2 Ξ e B,
  {{ (Ξ ++ Θ2 ++ Θ1) ⊢ˢᵈ[ M ] e ⦂ B }}ad ->
  {{ (Θ2 ++ Ξ ++ Θ1) ⊢ˢᵈ[ M ] e ⦂ B }}ad.
Proof.
  intros M Θ1 Θ2 Ξ e B H.
  eapply ad_sd_typing_mono; [ exact H | apply aenv_binds_le_perm3 ].
Qed.

(** Same for skeleton inference — the App rule of typing needs it there. *)
Corollary ad_pat_suffix_moving : forall M Θ1 Θ2 Ξ e Q,
  {{ (Ξ ++ Θ2 ++ Θ1) ⊢ˢ[ M ] e ⦂ Q }}ad ->
  {{ (Θ2 ++ Ξ ++ Θ1) ⊢ˢ[ M ] e ⦂ Q }}ad.
Proof.
  intros M Θ1 Θ2 Ξ e Q H.
  eapply ad_pat_mono; [ exact H | apply aenv_binds_le_perm3 ].
Qed.

(** And the two the paper calls "stability": a judgement survives any context
    that only ADDS entries — the [Ξ ++ Θ] shape every algorithmic step
    produces. *)
Corollary ad_sd_typing_weaken_suffix : forall M Θ Ξ e B,
  {{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad -> {{ (Ξ ++ Θ) ⊢ˢᵈ[ M ] e ⦂ B }}ad.
Proof.
  intros M Θ Ξ e B H.
  eapply ad_sd_typing_mono; [ exact H | apply aenv_binds_le_weaken_l ].
Qed.

Corollary ad_pat_weaken_suffix : forall M Θ Ξ e Q,
  {{ Θ ⊢ˢ[ M ] e ⦂ Q }}ad -> {{ (Ξ ++ Θ) ⊢ˢ[ M ] e ⦂ Q }}ad.
Proof.
  intros M Θ Ξ e Q H.
  eapply ad_pat_mono; [ exact H | apply aenv_binds_le_weaken_l ].
Qed.

(* ===================================================================== *)
(*  §6  Dropping a term variable                                          *)
(*                                                                        *)
(*  The paper's phrase — refinement judgements are stable under dropping   *)
(*  term variables (proofs.tex, the Abs cases of both soundness proofs) —  *)
(*  instances of the §1b relation.  Stated in the [Ξ ++ (x~b) ++ Θ] shape  *)
(*  the algorithmic Abs rows produce.                                      *)
(* ===================================================================== *)

Corollary ad_refine_syn_strip_tm_typ : forall Ξ x A Θ Δ Q P,
  {{ (Ξ ++ (x ~ abind_var_typ A) ++ Θ) ⨟ Δ ⊢ᵣ Q ⊳ P }}ad ->
  {{ (Ξ ++ Θ) ⨟ Δ ⊢ᵣ Q ⊳ P }}ad.
Proof.
  intros * H. eapply ad_refine_syn_mono;
    [ exact H | apply aenv_tbinds_le_strip_tm; intros [] ].
Qed.

Corollary ad_refine_syn_strip_tm_skl : forall Ξ x P0 Θ Δ Q P,
  {{ (Ξ ++ (x ~ abind_var_skl P0) ++ Θ) ⨟ Δ ⊢ᵣ Q ⊳ P }}ad ->
  {{ (Ξ ++ Θ) ⨟ Δ ⊢ᵣ Q ⊳ P }}ad.
Proof.
  intros * H. eapply ad_refine_syn_mono;
    [ exact H | apply aenv_tbinds_le_strip_tm; intros [] ].
Qed.

Corollary ad_refine_pskl_strip_tm_typ : forall Ξ x A Θ Δ P Q,
  {{ (Ξ ++ (x ~ abind_var_typ A) ++ Θ) ⨟ Δ ⊢ᵣₚ P ⊳ Q }}ad ->
  {{ (Ξ ++ Θ) ⨟ Δ ⊢ᵣₚ P ⊳ Q }}ad.
Proof.
  intros * H. eapply ad_refine_pskl_mono;
    [ exact H | apply aenv_tbinds_le_strip_tm; intros [] ].
Qed.

Corollary ad_refine_pskl_strip_tm_skl : forall Ξ x P0 Θ Δ P Q,
  {{ (Ξ ++ (x ~ abind_var_skl P0) ++ Θ) ⨟ Δ ⊢ᵣₚ P ⊳ Q }}ad ->
  {{ (Ξ ++ Θ) ⨟ Δ ⊢ᵣₚ P ⊳ Q }}ad.
Proof.
  intros * H. eapply ad_refine_pskl_mono;
    [ exact H | apply aenv_tbinds_le_strip_tm; intros [] ].
Qed.
