(** Frost — well-formedness preservation lemmas (Phase 2.B). *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.

Set Implicit Arguments.

(** * Declarative context well-formedness.
    A [denv] is well-formed iff every binding's payload is well-formed
    in the prefix preceding it. The paper treats this as implicit; we
    state it explicitly to ground preservation proofs. *)

Inductive d_wf_denv : list (atom * dbind) -> Prop :=
| d_wf_denv__nil : d_wf_denv nil
| d_wf_denv__tvar : forall Γ X,
    d_wf_denv Γ ->
    X `notin` dom Γ ->
    d_wf_denv ((X ~ dbind_tvar) ++ Γ)
| d_wf_denv__typ : forall Γ x A,
    d_wf_denv Γ ->
    x `notin` dom Γ ->
    d_wf_typ Γ A ->
    d_wf_denv ((x ~ dbind_typ A) ++ Γ)
| d_wf_denv__skel : forall Γ x P,
    d_wf_denv Γ ->
    x `notin` dom Γ ->
    d_wf_skel nil Γ P ->
    d_wf_denv ((x ~ dbind_skel P) ++ Γ).

(** ** Inversion lemmas. *)

Lemma d_wf_denv_inv_tvar : forall Γ X,
    d_wf_denv ((X ~ dbind_tvar) ++ Γ) ->
    d_wf_denv Γ /\ X `notin` dom Γ.
Proof. intros Γ X H. inversion H; subst; split; auto. Qed.

Lemma d_wf_denv_inv_typ : forall Γ x A,
    d_wf_denv ((x ~ dbind_typ A) ++ Γ) ->
    d_wf_denv Γ /\ x `notin` dom Γ /\ d_wf_typ Γ A.
Proof. intros Γ x A H. inversion H; subst; auto. Qed.

Lemma d_wf_denv_inv_skel : forall Γ x P,
    d_wf_denv ((x ~ dbind_skel P) ++ Γ) ->
    d_wf_denv Γ /\ x `notin` dom Γ /\ d_wf_skel nil Γ P.
Proof. intros Γ x P H. inversion H; subst; auto. Qed.
