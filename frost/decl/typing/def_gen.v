(** Frost declarative typing metatheory: generalised relations in the
    current split syntax.

    The generalised left-hand side is a [btyp]: this is the smallest
    native category that contains both ordinary synthesised unresolved
    types via [utyp_to_btyp] and the extra inherited-forall shape needed
    by the paper's D12/generalised-subsumption argument. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_subtyping.
Require Import src.frost.decl.typing.prop_weakening.

Set Implicit Arguments.

Reserved Notation "Δ ⨟ Γ ⊨ᵍ B1 ≈ B2"
  (at level 75, Γ at level 75, B1 at level 74, B2 at level 74, no associativity).
Reserved Notation "Γ ⊢ᵍ[ M ; Δ ] B1 ⊑ B2"
  (at level 75, M at level 0, Δ at level 0, B1 at level 74, B2 at level 74,
   no associativity).
Reserved Notation "Γ ⊢ᵍ[ M ] e ⇒ B"
  (at level 75, M at level 0, e at level 74, B at level 74, no associativity).

Inductive d_consis_gen : list atom -> list (atom * dbind) -> btyp -> btyp -> Prop :=
| d_consis_gen__embed : forall Δ Γ C B,
    Δ ⨟ Γ ⊨ C ≈ B ->
    Δ ⨟ Γ ⊨ᵍ (utyp_to_btyp C) ≈ B
| d_consis_gen__forall_inh : forall L Δ Γ B1 B2,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨ᵍ
         (open_btyp_wrt_btyp B1 (btyp_var_f X)) ≈
         (open_btyp_wrt_btyp B2 (btyp_var_f X))) ->
    Δ ⨟ Γ ⊨ᵍ (btyp_all_inh B1) ≈ (btyp_all_inh B2)
| d_consis_gen__refl_plain : forall Γ A,
    d_wf_ptyp Γ A ->
    nil ⨟ Γ ⊨ᵍ (ptyp_to_btyp_syn A) ≈ (ptyp_to_btyp_syn A)
where "Δ ⨟ Γ ⊨ᵍ B1 ≈ B2" := (d_consis_gen Δ Γ B1 B2) : type_scope.

Inductive d_sub_gen : mode -> list atom -> list (atom * dbind) -> btyp -> btyp -> Prop :=
| d_sub_gen__embed : forall m Δ Γ C B,
    Γ ⊢[ m ; Δ ] C ⊑ B ->
    Γ ⊢ᵍ[ m ; Δ ] (utyp_to_btyp C) ⊑ B
| d_sub_gen__infer_gen : forall Γ B1 B2,
    nil ⨟ Γ ⊨ᵍ B1 ≈ B2 ->
    Γ ⊢ᵍ[ mode_ti ; nil ] B1 ⊑ B2
| d_sub_gen__check_gen : forall Δ Γ B1 B2,
    Δ ⨟ Γ ⊨ᵍ B1 ≈ B2 ->
    Γ ⊢ᵍ[ mode_tc ; Δ ] B1 ⊑ B2
| d_sub_gen__refl_plain : forall Γ m A,
    d_wf_ptyp Γ A ->
    Γ ⊢ᵍ[ m ; nil ] (ptyp_to_btyp_syn A) ⊑ (ptyp_to_btyp_syn A)
| d_sub_gen__forall_r : forall L Δ Γ B1 B2,
    (forall X, X `notin` L ->
       ((X ~ dbind_tvar) ++ Γ) ⊢ᵍ[ mode_tc ; Δ ]
         B1 ⊑ open_btyp_wrt_btyp B2 (btyp_var_f X)) ->
    Γ ⊢ᵍ[ mode_tc ; Δ ] B1 ⊑ btyp_all_inh B2
| d_sub_gen__arg : forall Δ1 Δ2 Γ m B11 B12 B21 B22,
    Δ1 ⨟ Γ ⊨ᵍ B21 ≈ B11 ->
    Γ ⊢ᵍ[ m ; Δ2 ] B12 ⊑ B22 ->
    list_disjoint Δ1 Δ2 ->
    Γ ⊢ᵍ[ mode_fn m ; (Δ1 ++ Δ2) ]
      (btyp_arrow B11 B12) ⊑ (btyp_arrow B21 B22)
where "Γ ⊢ᵍ[ M ; Δ ] B1 ⊑ B2" := (d_sub_gen M Δ Γ B1 B2) : type_scope.

Inductive d_typing_gen : mode -> list (atom * dbind) -> exp -> btyp -> Prop :=
| d_typing_gen__embed : forall m Γ e B,
    d_typing m Γ e B ->
    Γ ⊢ᵍ[ m ] e ⇒ B
| d_typing_gen__sub : forall Γ m e B1 B2,
    d_typing_gen mode_ti Γ e B1 ->
    d_sub_gen m nil Γ B1 B2 ->
    Γ ⊢ᵍ[ m ] e ⇒ B2
where "Γ ⊢ᵍ[ M ] e ⇒ B" := (d_typing_gen M Γ e B) : type_scope.

Inductive is_fn_n_ti : mode -> Prop :=
| is_fn_n_ti__ti : is_fn_n_ti mode_ti
| is_fn_n_ti__fn : forall m, is_fn_n_ti m -> is_fn_n_ti (mode_fn m).

Fixpoint mode_fn_n_subst (m_orig m_new : mode) : mode :=
  match m_orig with
  | mode_ti => m_new
  | mode_tc => mode_tc
  | mode_fn m => mode_fn (mode_fn_n_subst m m_new)
  end.

Lemma d_typing_embed_gen : forall m Γ e B,
    d_typing m Γ e B ->
    Γ ⊢ᵍ[ m ] e ⇒ B.
Proof.
  intros. apply d_typing_gen__embed. exact H.
Qed.

Lemma d_typing_gen_collapse : forall m Γ e B,
    Γ ⊢ᵍ[ m ] e ⇒ B ->
    Γ ⊢[ m ] e ⇒ B.
Proof.
Admitted.

Lemma d_sub_gen_to_d_sub : forall m Δ Γ B1 B2,
    Γ ⊢ᵍ[ m ; Δ ] B1 ⊑ B2 ->
    exists C, B1 = utyp_to_btyp C /\ Γ ⊢[ m ; Δ ] C ⊑ B2.
Proof.
Admitted.
