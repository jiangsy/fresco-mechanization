(** Auxiliary facts for declarative general subsumption, stated over the
    current split syntax. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_subtyping.
Require Import src.frost.decl.typing.prop_weakening.
Require Import src.frost.decl.typing.def_gen.

Set Implicit Arguments.

Lemma d_sub_gen_weakening_head : forall Γ Γ' m Δ B1 B2,
    Γ ⊢ᵍ[ m ; Δ ] B1 ⊑ B2 ->
    Γ' ++ Γ ⊢ᵍ[ m ; Δ ] B1 ⊑ B2.
Proof.
Admitted.

Lemma d_sub_gen_trans : forall m1 Γ B1 B2 B3 m2,
    Γ ⊢ᵍ[ m1 ; nil ] B1 ⊑ B2 ->
    Γ ⊢ᵍ[ mode_fn_n_subst m1 m2 ; nil ] B2 ⊑ B3 ->
    Γ ⊢ᵍ[ mode_fn_n_subst m1 m2 ; nil ] B1 ⊑ B3.
Proof.
Admitted.

Lemma d_typing_gen_lift_plain : forall Γ e A m,
    Γ ⊢ᵍ[ mode_ti ] e ⇒ ptyp_to_btyp_syn A ->
    d_wf_ptyp Γ A ->
    Γ ⊢ᵍ[ m ] e ⇒ ptyp_to_btyp_syn A.
Proof.
Admitted.

