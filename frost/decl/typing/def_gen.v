(** Frost declarative typing metatheory: generalised relations in the
    current split syntax.

    The generalised left-hand side is a [btyp]: this is the smallest
    native category that contains both ordinary synthesised unresolved
    types via [utyp_to_btyp] and the extra inherited-forall shape needed
    by the paper's D12/generalised-subsumption argument. *)

Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
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
Reserved Notation "Δ ⨟ Γ ⊢ᵍ[ M ] B1 ⊑ B2"
  (at level 75, Γ at level 75, M at level 0, B1 at level 74, B2 at level 74,
   no associativity).
Reserved Notation "Γ ⊢ᵍ[ M ] e ⦂ B"
  (at level 100, M at level 0, e at level 75, B at level 75, no associativity).

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
    Δ ⨟ Γ ⊢[ m ] C ⊑ B ->
    Δ ⨟ Γ ⊢ᵍ[ m ] (utyp_to_btyp C) ⊑ B
| d_sub_gen__infer_gen : forall Γ C B,
    nil ⨟ Γ ⊨ᵍ (utyp_to_btyp C) ≈ B ->
    nil ⨟ Γ ⊢ᵍ[ mode_ti ] (utyp_to_btyp C) ⊑ B
| d_sub_gen__check_gen : forall Δ Γ C B,
    Δ ⨟ Γ ⊨ᵍ (utyp_to_btyp C) ≈ B ->
    Δ ⨟ Γ ⊢ᵍ[ mode_tc ] (utyp_to_btyp C) ⊑ B
| d_sub_gen__refl_plain : forall Γ m A,
    d_wf_ptyp Γ A ->
    nil ⨟ Γ ⊢ᵍ[ m ] (ptyp_to_btyp_syn A) ⊑ (ptyp_to_btyp_syn A)
| d_sub_gen__forall_r : forall L Δ Γ C B,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊢ᵍ[ mode_tc ]
         (utyp_to_btyp (open_utyp_wrt_utyp C (utyp_var_f X)))
         ⊑ open_btyp_wrt_btyp B (btyp_var_f X)) ->
    Δ ⨟ Γ ⊢ᵍ[ mode_tc ] (utyp_to_btyp C) ⊑ btyp_all_inh B
| d_sub_gen__arg : forall Δ1 Δ2 Γ m B11 B12 B21 B22,
    Δ1 ⨟ Γ ⊨ᵍ B21 ≈ B11 ->
    Δ2 ⨟ Γ ⊢ᵍ[ m ] B12 ⊑ B22 ->
    list_disjoint Δ1 Δ2 ->
    (Δ1 ++ Δ2) ⨟ Γ ⊢ᵍ[ mode_fn m ]
      (btyp_arrow B11 B12) ⊑ (btyp_arrow B21 B22)
where "Δ ⨟ Γ ⊢ᵍ[ M ] B1 ⊑ B2" := (d_sub_gen M Δ Γ B1 B2) : type_scope.

Inductive d_typing_gen : mode -> list (atom * dbind) -> exp -> btyp -> Prop :=
| d_typing_gen__embed : forall m Γ e B,
    d_typing m Γ e B ->
    Γ ⊢ᵍ[ m ] e ⦂ B
| d_typing_gen__sub : forall Γ m e B1 B2,
    d_typing_gen mode_ti Γ e B1 ->
    d_sub_gen m nil Γ B1 B2 ->
    Γ ⊢ᵍ[ m ] e ⦂ B2
where "Γ ⊢ᵍ[ M ] e ⦂ B" := (d_typing_gen M Γ e B) : type_scope.

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
    Γ ⊢ᵍ[ m ] e ⦂ B.
Proof.
  intros. apply d_typing_gen__embed. exact H.
Qed.

Lemma d_typing_gen_collapse : forall m Γ e B,
    Γ ⊢ᵍ[ m ] e ⦂ B ->
    Γ ⊢[ m ] e ⦂ B.
Proof.
Admitted.

Lemma d_sub_gen_top_inherited_lhs_impossible : forall Γ m Δ B,
    ~ Δ ⨟ Γ ⊢ᵍ[ m ] (btyp_all_inh btyp_unit) ⊑ B.
Proof.
  intros Γ m Δ B H.
  dependent destruction H; simpl in *; try discriminate;
    match goal with
    | C : utyp |- _ => destruct C; simpl in *; discriminate
    | A : ptyp |- _ => destruct A; simpl in *; discriminate
    end.
Qed.
