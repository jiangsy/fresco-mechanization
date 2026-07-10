(** Information-increase (metasubstitution) algebra.

    Basic properties of [a_inc] / [⊴] (paper fig:information-increase) that
    every appendix-B/C soundness case threads: identity metasubstitutions
    are reflexive, and the target may grow by a fresh flexible suffix.
    Both come out of one generalized induction ([a_inc_refl_gen]). *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.

Set Implicit Arguments.

(* ===================================================================== *)
(*  Identity substitutions are identities                                 *)
(* ===================================================================== *)

Lemma subst_ptyp_in_ptyp_self : forall α A,
  subst_ptyp_in_ptyp (ptyp_var_f α) α A = A.
Proof.
  induction A; simpl; f_equal; auto.
  destruct (eq_var Xpt α); subst; auto.
Qed.

Lemma subst_pskl_in_pskl_self : forall α P,
  subst_pskl_in_pskl (ptyp_to_pskl (ptyp_var_f α)) α P = P.
Proof.
  induction P; simpl; f_equal; auto.
  destruct (eq_var Xps α); subst; auto.
Qed.

Lemma msubst_ptyp_id : forall θ A,
  is_id_msubst θ ->
  msubst_ptyp θ A = A.
Proof.
  induction θ as [ | [α τ] θ' IH ]; intros A Hid; simpl; auto.
  inversion Hid as [ | ? ? He Hid' ]; subst.
  unfold is_id_entry in He; simpl in He; subst.
  rewrite subst_ptyp_in_ptyp_self. auto.
Qed.

Lemma msubst_pskl_id : forall θ P,
  is_id_msubst θ ->
  msubst_pskl θ P = P.
Proof.
  induction θ as [ | [α τ] θ' IH ]; intros P Hid; simpl; auto.
  inversion Hid as [ | ? ? He Hid' ]; subst.
  unfold is_id_entry in He; simpl in He; subst.
  rewrite subst_pskl_in_pskl_self. auto.
Qed.

(* ===================================================================== *)
(*  Suffix bookkeeping                                                    *)
(* ===================================================================== *)

Lemma a_suffix_app : forall Ξ1 Ξ2,
  a_suffix Ξ1 -> a_suffix Ξ2 -> a_suffix (Ξ1 ++ Ξ2).
Proof.
  intros Ξ1 Ξ2 H1 H2; induction H1; simpl; auto.
  apply (a_suffix__cons a (b := b)); auto.
Qed.

(* ===================================================================== *)
(*  Reflexivity, generalized with a fresh-suffix target extension:        *)
(*  Θ ⊑[ι] Ξ0 ++ Θ  for any flexible suffix Ξ0.                           *)
(* ===================================================================== *)

Lemma a_inc_refl_gen : forall Θ Ξ0,
  a_suffix Ξ0 ->
  exists θ, is_id_msubst θ /\ Θ ≤[ θ ] (Ξ0 ++ Θ).
Proof.
  induction Θ as [ | [a b] Θ0 IH ]; intros Ξ0 HΞ.
  - exists nil. split; [ constructor | ].
    rewrite app_nil_r. apply a_inc__empty; auto.
  - destruct b.
    + (* abind_tvar : Θ,α ⊑ Ξ0,α,Θ — a_inc__tvar with Ξ := Ξ0 *)
      destruct (IH nil) as [θ0 [Hid Hinc]]; [ constructor | ].
      simpl in Hinc.
      exists θ0. split; auto.
      apply (a_inc__tvar (Ξ := Ξ0)); auto.
    + (* abind_var_typ A : entry carried over, type metasubstituted *)
      destruct (IH nil) as [θ0 [Hid Hinc]]; [ constructor | ].
      simpl in Hinc.
      exists θ0. split; auto.
      replace ((a, abind_var_typ p) :: Θ0)
        with ((a ~ abind_var_typ p) ++ Θ0) by reflexivity.
      replace (Ξ0 ++ (a ~ abind_var_typ p) ++ Θ0)
        with (Ξ0 ++ (a ~ abind_var_typ (msubst_ptyp θ0 p)) ++ Θ0)
        by (rewrite msubst_ptyp_id; auto).
      apply a_inc__var; auto.
    + (* abind_var_skl P *)
      destruct (IH nil) as [θ0 [Hid Hinc]]; [ constructor | ].
      simpl in Hinc.
      exists θ0. split; auto.
      replace ((a, abind_var_skl p) :: Θ0)
        with ((a ~ abind_var_skl p) ++ Θ0) by reflexivity.
      replace (Ξ0 ++ (a ~ abind_var_skl p) ++ Θ0)
        with (Ξ0 ++ (a ~ abind_var_skl (msubst_pskl θ0 p)) ++ Θ0)
        by (rewrite msubst_pskl_id; auto).
      apply a_inc__var_skl; auto.
    + (* abind_flex_mono : solve α̂ with itself; α̂ sits inside the target *)
      destruct (IH (Ξ0 ++ (a ~ abind_flex_mono)))
        as [θ0 [Hid Hinc]].
      { apply a_suffix_app; auto.
        apply (a_suffix__cons a (b := abind_flex_mono)); constructor. }
      first [ rewrite <- app_assoc in Hinc | rewrite app_assoc in Hinc ]; simpl in Hinc.
      exists ((a, ptyp_var_f a) :: θ0). split.
      { constructor; auto. unfold is_id_entry; reflexivity. }
      replace ((a, abind_flex_mono) :: Θ0)
        with ((a ~ abind_flex_mono) ++ Θ0) by reflexivity.
      apply a_inc__flex; auto.
      * constructor. auto.
      * constructor.
    + (* abind_flex_mono_def τ : α̂:=τ, entry looked up in the target *)
      destruct (IH (Ξ0 ++ (a ~ abind_flex_mono_def p)))
        as [θ0 [Hid Hinc]].
      { apply a_suffix_app; auto.
        apply (a_suffix__cons a (b := abind_flex_mono_def p)); constructor. }
      first [ rewrite <- app_assoc in Hinc | rewrite app_assoc in Hinc ]; simpl in Hinc.
      exists ((a, ptyp_var_f a) :: θ0). split.
      { constructor; auto. unfold is_id_entry; reflexivity. }
      replace ((a, abind_flex_mono_def p) :: Θ0)
        with ((a ~ abind_flex_mono_def p) ++ Θ0) by reflexivity.
      apply a_inc__flex_def; auto.
      rewrite msubst_ptyp_id; auto.
      apply a_tyequiv__flex_def.
      unfold binds; apply in_or_app; right; left; reflexivity.
Qed.

(** [Θ ⊴ Θ] — reflexivity of information increase. *)
Lemma a_isub_refl : forall Θ, Θ ⊴ Θ.
Proof.
  intros Θ. destruct (a_inc_refl_gen Θ (Ξ0 := nil)) as [θ [Hid Hinc]];
    [ constructor | ].
  exists θ. simpl in Hinc. auto.
Qed.

(** [Θ ⊴ Ξ ++ Θ] — the target may grow by a fresh flexible suffix. *)
Lemma a_isub_weaken_suffix : forall Θ Ξ,
  a_suffix Ξ ->
  Θ ⊴ (Ξ ++ Θ).
Proof.
  intros Θ Ξ HΞ. destruct (a_inc_refl_gen Θ (Ξ0 := Ξ)) as [θ [Hid Hinc]]; auto.
  exists θ. auto.
Qed.
