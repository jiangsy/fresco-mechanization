(** Frost declarative-system definitions for the current split syntax.

    This file follows [language.ott]'s latest categories directly:
    [ptyp], [btyp], [utyp], [pskl], [bskl], [uskl]. Here [pskl] is the
    plain skeleton category; synthesised/inherited colours belong to
    [bskl]. It intentionally does
    not reintroduce the removed legacy unified type layer. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.
Require Import src.frost.coercions.
Require Import src.frost.predicates.

Set Implicit Arguments.

Reserved Notation "Ψ ⨟ Γ ⊢ₚₛ P"
  (at level 75, Γ at level 75, P at level 75, no associativity).
Reserved Notation "Γ ⊢ᵦ B"
  (at level 75, B at level 75, no associativity).
Reserved Notation "Δ ⨟ Γ ⊢ᵤ C"
  (at level 75, Γ at level 75, C at level 75, no associativity).
Reserved Notation "Δ ⨟ Γ ⊢ᵤₛ R"
  (at level 75, Γ at level 75, R at level 75, no associativity).
Reserved Notation "Δ ⨟ Γ ⊨ C ≈ B"
  (at level 75, Γ at level 75, C at level 74, B at level 74, no associativity).
Reserved Notation "Δ ⨟ Γ ⊢[ M ] C ⊑ B"
  (at level 75, Γ at level 75, M at level 0, C at level 74, B at level 74,
   no associativity).
Reserved Notation "Ψ ⨟ Γ ⊢ᵣ P ▸ Q"
  (at level 75, Γ at level 75, P at level 74, Q at level 74, no associativity).
Reserved Notation "Ψ ⨟ Γ ⊢ᵣ Q ⊳ P"
  (at level 75, Γ at level 75, Q at level 74, P at level 74, no associativity).
Reserved Notation "Δ ⨟ Γ ⊨ₛ R ≈ Q"
  (at level 75, Γ at level 75, R at level 74, Q at level 74, no associativity).
Reserved Notation "Δ ⨟ Γ ⊢ₛ[ M ] R ⊑ Q"
  (at level 75, Γ at level 75, M at level 0, R at level 74, Q at level 74,
   no associativity).

(* ===================================================================== *)
(*  Well-formedness                                                       *)
(* ===================================================================== *)

Inductive d_wf_ptyp : list (atom * dbind) -> ptyp -> Prop :=
| d_wf_ptyp__unit : forall Γ,
    d_wf_ptyp Γ ptyp_unit
| d_wf_ptyp__var : forall Γ X,
    binds X dbind_tvar Γ ->
    d_wf_ptyp Γ (ptyp_var_f X)
| d_wf_ptyp__arrow : forall Γ A1 A2,
    d_wf_ptyp Γ A1 ->
    d_wf_ptyp Γ A2 ->
    d_wf_ptyp Γ (ptyp_arrow A1 A2)
| d_wf_ptyp__all : forall L Γ A,
    (forall X, X `notin` L ->
       d_wf_ptyp ((X ~ dbind_tvar) ++ Γ)
         (open_ptyp_wrt_ptyp A (ptyp_var_f X))) ->
    d_wf_ptyp Γ (ptyp_all A).

Inductive d_wf_btyp : list (atom * dbind) -> btyp -> Prop :=
| d_wf_btyp__unit : forall Γ,
    Γ ⊢ᵦ btyp_unit
| d_wf_btyp__var : forall Γ X,
    binds X dbind_tvar Γ ->
    Γ ⊢ᵦ (btyp_var_f X)
| d_wf_btyp__arrow : forall Γ B1 B2,
    Γ ⊢ᵦ B1 ->
    Γ ⊢ᵦ B2 ->
    Γ ⊢ᵦ (btyp_arrow B1 B2)
| d_wf_btyp__all_syn : forall L Γ B,
    (forall X, X `notin` L ->
       ((X ~ dbind_tvar) ++ Γ) ⊢ᵦ (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Γ ⊢ᵦ (btyp_all_syn B)
| d_wf_btyp__all_inh : forall L Γ B,
    (forall X, X `notin` L ->
       ((X ~ dbind_tvar) ++ Γ) ⊢ᵦ (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Γ ⊢ᵦ (btyp_all_inh B)
where "Γ ⊢ᵦ B" := (d_wf_btyp Γ B) : type_scope.

Inductive d_wf_utyp : list atom -> list (atom * dbind) -> utyp -> Prop :=
| d_wf_utyp__unit : forall Γ,
    nil ⨟ Γ ⊢ᵤ utyp_unit
| d_wf_utyp__var : forall Γ X,
    binds X dbind_tvar Γ ->
    nil ⨟ Γ ⊢ᵤ (utyp_var_f X)
| d_wf_utyp__arrow : forall Δ1 Δ2 Γ C1 C2,
    Δ1 ⨟ Γ ⊢ᵤ C1 ->
    Δ2 ⨟ Γ ⊢ᵤ C2 ->
    list_disjoint Δ1 Δ2 ->
    (Δ1 ++ Δ2) ⨟ Γ ⊢ᵤ (utyp_arrow C1 C2)
| d_wf_utyp__all_syn : forall L Δ Γ C,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊢ᵤ
         (open_utyp_wrt_utyp C (utyp_var_f X))) ->
    Δ ⨟ Γ ⊢ᵤ (utyp_all_syn C)
| d_wf_utyp__all_etag : forall L Δ Γ ε C,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊢ᵤ
         (open_utyp_wrt_utyp C (utyp_var_f X))) ->
    ~ List.In ε Δ ->
    (ε :: Δ) ⨟ Γ ⊢ᵤ (utyp_all_etag ε C)
where "Δ ⨟ Γ ⊢ᵤ C" := (d_wf_utyp Δ Γ C) : type_scope.

Inductive d_wf_pskl : list atom -> list (atom * dbind) -> pskl -> Prop :=
| d_wf_pskl__unit : forall Ψ Γ,
    Ψ ⨟ Γ ⊢ₚₛ pskl_unit
| d_wf_pskl__var : forall Ψ Γ X,
    List.In X Ψ \/ binds X dbind_tvar Γ ->
    Ψ ⨟ Γ ⊢ₚₛ (pskl_var_f X)
| d_wf_pskl__arrow : forall Ψ Γ P1 P2,
    Ψ ⨟ Γ ⊢ₚₛ P1 ->
    Ψ ⨟ Γ ⊢ₚₛ P2 ->
    Ψ ⨟ Γ ⊢ₚₛ (pskl_arrow P1 P2)
| d_wf_pskl__all : forall L Ψ Γ P,
    (forall X, X `notin` L ->
       (X :: Ψ) ⨟ Γ ⊢ₚₛ (open_pskl_wrt_pskl P (pskl_var_f X))) ->
    Ψ ⨟ Γ ⊢ₚₛ (pskl_all_syn P)
| d_wf_pskl__hole : forall Ψ Γ,
    Ψ ⨟ Γ ⊢ₚₛ pskl_hole
| d_wf_pskl__tophole : forall Γ P,
    guarded_pskl P ->
    nil ⨟ Γ ⊢ₚₛ P ->
    nil ⨟ Γ ⊢ₚₛ (pskl_tophole P)
where "Ψ ⨟ Γ ⊢ₚₛ P" := (d_wf_pskl Ψ Γ P) : type_scope.

Inductive d_wf_uskl : list atom -> list (atom * dbind) -> uskl -> Prop :=
| d_wf_uskl__unit : forall Γ,
    nil ⨟ Γ ⊢ᵤₛ uskl_unit
| d_wf_uskl__var : forall Γ X,
    binds X dbind_tvar Γ ->
    nil ⨟ Γ ⊢ᵤₛ (uskl_var_f X)
| d_wf_uskl__arrow : forall Δ1 Δ2 Γ R1 R2,
    Δ1 ⨟ Γ ⊢ᵤₛ R1 ->
    Δ2 ⨟ Γ ⊢ᵤₛ R2 ->
    list_disjoint Δ1 Δ2 ->
    (Δ1 ++ Δ2) ⨟ Γ ⊢ᵤₛ (uskl_arrow R1 R2)
| d_wf_uskl__all_syn : forall L Δ Γ R,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊢ᵤₛ
         (open_uskl_wrt_uskl R (uskl_var_f X))) ->
    Δ ⨟ Γ ⊢ᵤₛ (uskl_all_syn R)
| d_wf_uskl__all_etag : forall L Δ Γ ε R,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊢ᵤₛ
         (open_uskl_wrt_uskl R (uskl_var_f X))) ->
    ~ List.In ε Δ ->
    (ε :: Δ) ⨟ Γ ⊢ᵤₛ (uskl_all_etag ε R)
| d_wf_uskl__hole : forall Γ,
    nil ⨟ Γ ⊢ᵤₛ uskl_hole
| d_wf_uskl__tophole : forall Δ Γ R,
    Δ ⨟ Γ ⊢ᵤₛ R ->
    Δ ⨟ Γ ⊢ᵤₛ (uskl_tophole R)
where "Δ ⨟ Γ ⊢ᵤₛ R" := (d_wf_uskl Δ Γ R) : type_scope.

(* ===================================================================== *)
(*  Type consistency and subtyping                                        *)
(* ===================================================================== *)

Inductive d_consis : list atom -> list (atom * dbind) -> utyp -> btyp -> Prop :=
| d_consis__unit : forall Γ,
    nil ⨟ Γ ⊨ utyp_unit ≈ btyp_unit
| d_consis__var : forall Γ X,
    binds X dbind_tvar Γ ->
    nil ⨟ Γ ⊨ (utyp_var_f X) ≈ (btyp_var_f X)
| d_consis__arrow : forall Δ1 Δ2 Γ C1 C2 B1 B2,
    (* Paper [Arrow]: the tag context is the SET UNION [Δ₁,Δ₂]
       (declarative.tex:967, with Δ a set), not a disjoint union — so we
       neither require nor record [list_disjoint Δ1 Δ2].  This faithfulness
       is what makes consistency transitivity (B.2) provable: composing two
       derivations may legitimately reuse a tag, which a set absorbs. *)
    Δ1 ⨟ Γ ⊨ C1 ≈ B1 ->
    Δ2 ⨟ Γ ⊨ C2 ≈ B2 ->
    (Δ1 ++ Δ2) ⨟ Γ ⊨ (utyp_arrow C1 C2) ≈ (btyp_arrow B1 B2)
| d_consis__forall_inh_tagged : forall L Δ Γ ε C B,
    (* Paper [ForallInh] with δ=ε: output is [Δ,ε] = Δ ∪ {ε}, the
       idempotent set union (declarative.tex:950) — no [~ In ε Δ] freshness
       side condition (a singleton union is idempotent, not a cons). *)
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨
         (open_utyp_wrt_utyp C (utyp_var_f X)) ≈
         (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    (ε :: Δ) ⨟ Γ ⊨ (utyp_all_etag ε C) ≈ (btyp_all_inh B)
| d_consis__forall_inh_untagged : forall L Δ Γ C B,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨
         (open_utyp_wrt_utyp C (utyp_var_f X)) ≈
         (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Δ ⨟ Γ ⊨ (utyp_all_syn C) ≈ (btyp_all_inh B)
| d_consis__forall_syn_tagged : forall L Δ Γ ε C B,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨
         (open_utyp_wrt_utyp C (utyp_var_f X)) ≈
         (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Δ ⨟ Γ ⊨ (utyp_all_etag ε C) ≈ (btyp_all_syn B)
| d_consis__forall_syn : forall L Δ Γ C B,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨
         (open_utyp_wrt_utyp C (utyp_var_f X)) ≈
         (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Δ ⨟ Γ ⊨ (utyp_all_syn C) ≈ (btyp_all_syn B)
where "Δ ⨟ Γ ⊨ C ≈ B" := (d_consis Δ Γ C B) : type_scope.

Inductive d_sub : mode -> list atom -> list (atom * dbind) -> utyp -> btyp -> Prop :=
| d_sub__infer : forall Γ C B,
    nil ⨟ Γ ⊨ C ≈ B ->
    is_styp B ->
    nil ⨟ Γ ⊢[ mode_ti ] C ⊑ B
| d_sub__check : forall Δ Γ C B,
    guarded_utyp C ->
    Δ ⨟ Γ ⊨ C ≈ B ->
    is_ityp B ->
    Δ ⨟ Γ ⊢[ mode_tc ] C ⊑ B
| d_sub__forall_r : forall L Δ Γ C B,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊢[ mode_tc ] C ⊑
         (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    Δ ⨟ Γ ⊢[ mode_tc ] C ⊑ (btyp_all_inh B)
| d_sub__arg : forall Δ1 Δ2 Γ m C1 C2 B1 B2,
    Δ1 ⨟ Γ ⊨ C1 ≈ B1 ->
    Δ2 ⨟ Γ ⊢[ m ] C2 ⊑ B2 ->
    (Δ1 ++ Δ2) ⨟ Γ ⊢[ mode_fn m ] (utyp_arrow C1 C2) ⊑ (btyp_arrow B1 B2)
| d_sub__forall_l_tagged : forall Δ Δ' Γ m ε C ph B,
    m <> mode_ti ->
    list_disjoint Δ' Δ ->
    Δ' ⨟ Γ ⊢ᵤ ph ->
    is_ttyp ph ->
    (Δ ++ Δ') ⨟ Γ ⊢[ m ] (open_utyp_wrt_utyp C ph) ⊑ B ->
    Δ ⨟ Γ ⊢[ m ] (utyp_all_etag ε C) ⊑ B
| d_sub__forall_l_untagged : forall Δ Δ' Γ m C ph B,
    m <> mode_ti ->
    list_disjoint Δ' Δ ->
    Δ' ⨟ Γ ⊢ᵤ ph ->
    is_ttyp ph ->
    (Δ ++ Δ') ⨟ Γ ⊢[ m ] (open_utyp_wrt_utyp C ph) ⊑ B ->
    Δ ⨟ Γ ⊢[ m ] (utyp_all_syn C) ⊑ B
where "Δ ⨟ Γ ⊢[ M ] C ⊑ B" := (d_sub M Δ Γ C B) : type_scope.

Inductive d_shallow_sub : list (atom * dbind) -> ptyp -> ptyp -> Prop :=
| d_shallow_sub__refl : forall Γ A,
    d_wf_ptyp Γ A ->
    d_shallow_sub Γ A A
| d_shallow_sub__arrow : forall Γ A1 A2 A1' A2',
    d_shallow_sub Γ A1' A1 ->
    d_shallow_sub Γ A2 A2' ->
    d_shallow_sub Γ (ptyp_arrow A1 A2) (ptyp_arrow A1' A2')
| d_shallow_sub__forall_r : forall L Γ A1 A2,
    (forall X, X `notin` L ->
       d_shallow_sub ((X ~ dbind_tvar) ++ Γ) A1
         (open_ptyp_wrt_ptyp A2 (ptyp_var_f X))) ->
    d_shallow_sub Γ A1 (ptyp_all A2)
| d_shallow_sub__forall_l : forall Γ A1 A2 I,
    d_wf_ptyp Γ I ->
    d_shallow_sub Γ (open_ptyp_wrt_ptyp A1 I) A2 ->
    d_shallow_sub Γ (ptyp_all A1) A2.

(* ===================================================================== *)
(*  Skeleton refinement, consistency, and subtyping                       *)
(* ===================================================================== *)

Inductive d_refine_syn : list atom -> list (atom * dbind) -> bskl -> pskl -> Prop :=
| d_refine_syn__unit : forall Ψ Γ,
    Ψ ⨟ Γ ⊢ᵣ bskl_unit ⊳ pskl_unit
| d_refine_syn__var : forall Ψ Γ X,
    List.In X Ψ \/ binds X dbind_tvar Γ ->
    Ψ ⨟ Γ ⊢ᵣ (bskl_var_f X) ⊳ (pskl_var_f X)
| d_refine_syn__arrow : forall Ψ Γ Q1 Q2 P1 P2,
    Ψ ⨟ Γ ⊢ᵣ Q1 ⊳ P1 ->
    Ψ ⨟ Γ ⊢ᵣ Q2 ⊳ P2 ->
    Ψ ⨟ Γ ⊢ᵣ (bskl_arrow Q1 Q2) ⊳ (pskl_arrow P1 P2)
| d_refine_syn__all : forall L Ψ Γ Q P,
    (forall X, X `notin` L ->
       (X :: Ψ) ⨟ Γ ⊢ᵣ
         (open_bskl_wrt_bskl Q (bskl_var_f X)) ⊳
         (open_pskl_wrt_pskl P (pskl_var_f X))) ->
    Ψ ⨟ Γ ⊢ᵣ (bskl_all_syn Q) ⊳ (pskl_all_syn P)
| d_refine_syn__hole : forall Ψ Γ P,
    Ψ ⨟ Γ ⊢ₚₛ P ->
    Ψ ⨟ Γ ⊢ᵣ bskl_hole ⊳ P
| d_refine_syn__tophole : forall Ψ Γ Q P,
    nil ⨟ Γ ⊢ᵣ Q ⊳ P ->
    Ψ ⨟ Γ ⊢ᵣ (bskl_tophole Q) ⊳ (pskl_tophole P)
where "Ψ ⨟ Γ ⊢ᵣ Q ⊳ P" := (d_refine_syn Ψ Γ Q P) : type_scope.

Inductive d_refine : list atom -> list (atom * dbind) -> pskl -> pskl -> Prop :=
| d_refine__unit : forall Ψ Γ,
    Ψ ⨟ Γ ⊢ᵣ pskl_unit ▸ pskl_unit
| d_refine__var : forall Ψ Γ X,
    List.In X Ψ \/ binds X dbind_tvar Γ ->
    Ψ ⨟ Γ ⊢ᵣ (pskl_var_f X) ▸ (pskl_var_f X)
| d_refine__arrow : forall Ψ Γ P1 P2 Q1 Q2,
    Ψ ⨟ Γ ⊢ᵣ P1 ▸ Q1 ->
    Ψ ⨟ Γ ⊢ᵣ P2 ▸ Q2 ->
    Ψ ⨟ Γ ⊢ᵣ (pskl_arrow P1 P2) ▸ (pskl_arrow Q1 Q2)
| d_refine__all : forall L Ψ Γ P1 P2,
    (forall X, X `notin` L ->
       (X :: Ψ) ⨟ Γ ⊢ᵣ
         (open_pskl_wrt_pskl P1 (pskl_var_f X)) ▸
         (open_pskl_wrt_pskl P2 (pskl_var_f X))) ->
    Ψ ⨟ Γ ⊢ᵣ (pskl_all_syn P1) ▸ (pskl_all_syn P2)
| d_refine__hole : forall Ψ Γ P,
    Ψ ⨟ Γ ⊢ₚₛ P ->
    Ψ ⨟ Γ ⊢ᵣ pskl_hole ▸ P
| d_refine__tophole : forall Ψ Γ P1 P2,
    nil ⨟ Γ ⊢ᵣ P1 ▸ P2 ->
    Ψ ⨟ Γ ⊢ᵣ (pskl_tophole P1) ▸ (pskl_tophole P2)
where "Ψ ⨟ Γ ⊢ᵣ P ▸ Q" := (d_refine Ψ Γ P Q) : type_scope.

Inductive d_pat_consis : list atom -> list (atom * dbind) -> uskl -> bskl -> Prop :=
| d_pat_consis__unit : forall Γ,
    nil ⨟ Γ ⊨ₛ uskl_unit ≈ bskl_unit
| d_pat_consis__var : forall Γ X,
    binds X dbind_tvar Γ ->
    nil ⨟ Γ ⊨ₛ (uskl_var_f X) ≈ (bskl_var_f X)
| d_pat_consis__arrow : forall Δ1 Δ2 Γ R1 R2 Q1 Q2,
    Δ1 ⨟ Γ ⊨ₛ R1 ≈ Q1 ->
    Δ2 ⨟ Γ ⊨ₛ R2 ≈ Q2 ->
    list_disjoint Δ1 Δ2 ->
    (Δ1 ++ Δ2) ⨟ Γ ⊨ₛ (uskl_arrow R1 R2) ≈ (bskl_arrow Q1 Q2)
| d_pat_consis__forall_inh_tagged : forall L Δ Γ ε R Q,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨ₛ
         (open_uskl_wrt_uskl R (uskl_var_f X)) ≈
         (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    ~ List.In ε Δ ->
    (ε :: Δ) ⨟ Γ ⊨ₛ (uskl_all_etag ε R) ≈ (bskl_all_inh Q)
| d_pat_consis__forall_inh_untagged : forall L Δ Γ R Q,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨ₛ
         (open_uskl_wrt_uskl R (uskl_var_f X)) ≈
         (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    Δ ⨟ Γ ⊨ₛ (uskl_all_syn R) ≈ (bskl_all_inh Q)
| d_pat_consis__forall_syn_tagged : forall L Δ Γ ε R Q,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨ₛ
         (open_uskl_wrt_uskl R (uskl_var_f X)) ≈
         (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    Δ ⨟ Γ ⊨ₛ (uskl_all_etag ε R) ≈ (bskl_all_syn Q)
| d_pat_consis__forall_syn : forall L Δ Γ R Q,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊨ₛ
         (open_uskl_wrt_uskl R (uskl_var_f X)) ≈
         (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    Δ ⨟ Γ ⊨ₛ (uskl_all_syn R) ≈ (bskl_all_syn Q)
| d_pat_consis__hole : forall Γ P,
    d_wf_pskl nil Γ P ->
    nil ⨟ Γ ⊨ₛ uskl_hole ≈ (pskl_to_bskl_syn P)
| d_pat_consis__tophole : forall Δ Γ R Q,
    Δ ⨟ Γ ⊨ₛ R ≈ Q ->
    Δ ⨟ Γ ⊨ₛ (uskl_tophole R) ≈ (bskl_tophole Q)
where "Δ ⨟ Γ ⊨ₛ R ≈ Q" := (d_pat_consis Δ Γ R Q) : type_scope.

Inductive d_pat_sub : mode -> list atom -> list (atom * dbind) -> uskl -> bskl -> Prop :=
| d_pat_sub__infer : forall Γ R Q,
    nil ⨟ Γ ⊨ₛ R ≈ Q ->
    is_sskl Q ->
    nil ⨟ Γ ⊢ₛ[ mode_ti ] R ⊑ Q
| d_pat_sub__check : forall Δ Γ R Q,
    guarded_uskl R ->
    Δ ⨟ Γ ⊨ₛ R ≈ Q ->
    is_iskl Q ->
    Δ ⨟ Γ ⊢ₛ[ mode_tc ] R ⊑ Q
| d_pat_sub__forall_r : forall L Δ Γ R Q,
    (forall X, X `notin` L ->
       Δ ⨟ ((X ~ dbind_tvar) ++ Γ) ⊢ₛ[ mode_tc ] R ⊑
         (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    Δ ⨟ Γ ⊢ₛ[ mode_tc ] R ⊑ (bskl_all_inh Q)
| d_pat_sub__arg : forall Δ1 Δ2 Γ m R1 R2 Q1 Q2,
    Δ1 ⨟ Γ ⊨ₛ R1 ≈ Q1 ->
    Δ2 ⨟ Γ ⊢ₛ[ m ] R2 ⊑ Q2 ->
    (Δ1 ++ Δ2) ⨟ Γ ⊢ₛ[ mode_fn m ] (uskl_arrow R1 R2) ⊑ (bskl_arrow Q1 Q2)
| d_pat_sub__forall_l_tagged : forall Δ Δ' Γ m ε R psi Q,
    m <> mode_ti ->
    list_disjoint Δ' Δ ->
    Δ' ⨟ Γ ⊢ᵤₛ psi ->
    is_tskl psi ->
    (Δ ++ Δ') ⨟ Γ ⊢ₛ[ m ] (open_uskl_wrt_uskl R psi) ⊑ Q ->
    Δ ⨟ Γ ⊢ₛ[ m ] (uskl_all_etag ε R) ⊑ Q
| d_pat_sub__forall_l_untagged : forall Δ Δ' Γ m R psi Q,
    m <> mode_ti ->
    list_disjoint Δ' Δ ->
    Δ' ⨟ Γ ⊢ᵤₛ psi ->
    is_tskl psi ->
    (Δ ++ Δ') ⨟ Γ ⊢ₛ[ m ] (open_uskl_wrt_uskl R psi) ⊑ Q ->
    Δ ⨟ Γ ⊢ₛ[ m ] (uskl_all_syn R) ⊑ Q
where "Δ ⨟ Γ ⊢ₛ[ M ] R ⊑ Q" := (d_pat_sub M Δ Γ R Q) : type_scope.

(* ===================================================================== *)
(*  Typing and pattern inference                                          *)
(* ===================================================================== *)

Inductive is_base_term : exp -> Prop :=
| is_base_term__unit : is_base_term exp_unit
| is_base_term__var  : forall x, is_base_term (exp_var_f x)
| is_base_term__anno : forall e A, is_base_term (exp_anno e A).

Inductive d_typing : mode -> list (atom * dbind) -> exp -> btyp -> Prop :=
| d_typing__unit : forall Γ,
    d_typing mode_ti Γ exp_unit btyp_unit
| d_typing__var : forall Γ x A,
    binds x (dbind_typ A) Γ ->
    d_typing mode_ti Γ (exp_var_f x) (ptyp_to_btyp_syn A)
| d_typing__anno : forall Γ e A,
    d_typing mode_tc Γ e (ptyp_to_btyp_inh A) ->
    d_typing mode_ti Γ (exp_anno e A) (ptyp_to_btyp_syn A)
| d_typing__sub : forall Γ m e B1 B2,
    is_base_term e ->
    d_typing mode_ti Γ e B1 ->
    d_sub m nil Γ (ptyp_to_utyp_syn B1) B2 ->
    d_typing m Γ e B2
| d_typing__freeze : forall Γ e B,
    d_typing mode_ti Γ e B ->
    d_typing mode_tc Γ (exp_freeze e) B
| d_typing__forall : forall L Γ e B,
    is_value e ->
    (forall X, X `notin` L ->
       d_typing mode_tc ((X ~ dbind_tvar) ++ Γ) e
         (open_btyp_wrt_btyp B (btyp_var_f X))) ->
    d_typing mode_tc Γ e (btyp_all_inh B)
| d_typing__abs : forall L Γ m e A B,
    d_wf_ptyp Γ A ->
    (forall x, x `notin` L ->
       d_typing (decr_mode m) ((x ~ dbind_typ A) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) B) ->
    d_typing m Γ (exp_abs e) (btyp_arrow (ptyp_to_btyp_inh A) B)
| d_typing__abs_anno : forall L Γ m e A B,
    d_wf_ptyp Γ A ->
    (forall x, x `notin` L ->
       d_typing (decr_mode m) ((x ~ dbind_typ A) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) B) ->
    d_typing m Γ (exp_abs_anno A e) (btyp_arrow (ptyp_to_btyp_syn A) B)
| d_typing__app : forall Γ m e1 e2 P A B,
    d_pat mode_tc Γ e2 (pskl_to_bskl_syn P) ->
    d_refine_syn nil Γ (pskl_to_bskl_syn P) (ptyp_to_pskl A) ->
    d_typing (mode_fn m) Γ e1 (btyp_arrow (ptyp_to_btyp_inh A) B) ->
    d_typing mode_tc Γ e2 (ptyp_to_btyp_inh A) ->
    d_typing m Γ (exp_app e1 e2) B

with d_pat : mode -> list (atom * dbind) -> exp -> bskl -> Prop :=
| d_pat__unit : forall Γ,
    d_pat mode_ti Γ exp_unit bskl_unit
| d_pat__var : forall Γ x P,
    binds x (dbind_skl P) Γ ->
    d_pat mode_ti Γ (exp_var_f x) (pskl_to_bskl_syn P)
| d_pat__anno : forall Γ e A,
    d_wf_ptyp Γ A ->
    d_pat mode_ti Γ (exp_anno e A) (pskl_to_bskl_syn (ptyp_to_pskl A))
| d_pat__sub : forall Γ m e Q1 Q2,
    is_base_term e ->
    d_pat mode_ti Γ e Q1 ->
    d_pat_sub m nil Γ (bskl_to_uskl Q1) Q2 ->
    d_pat m Γ e Q2
| d_pat__freeze : forall Γ e Q,
    d_pat mode_ti Γ e Q ->
    d_pat mode_tc Γ (exp_freeze e) Q
| d_pat__abs : forall L Γ m e P Q,
    m <> mode_tc ->
    d_wf_pskl nil Γ P ->
    (forall x, x `notin` L ->
       d_pat (decr_mode m) ((x ~ dbind_skl P) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) Q) ->
    d_pat m Γ (exp_abs e) (bskl_arrow (pskl_to_bskl_syn P) Q)
| d_pat__abs_check : forall L Γ e Q,
    (forall x, x `notin` L ->
       d_pat mode_tc ((x ~ dbind_skl pskl_hole) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) Q) ->
    d_pat mode_tc Γ (exp_abs e)
      (bskl_tophole (bskl_arrow bskl_hole Q))
| d_pat__abs_anno : forall L Γ m e A Q,
    m <> mode_tc ->
    d_wf_ptyp Γ A ->
    (forall x, x `notin` L ->
       d_pat (decr_mode m) ((x ~ dbind_typ A) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) Q) ->
    d_pat m Γ (exp_abs_anno A e)
      (bskl_arrow (pskl_to_bskl_syn (ptyp_to_pskl A)) Q)
| d_pat__abs_anno_check : forall L Γ e A Q,
    d_wf_ptyp Γ A ->
    (forall x, x `notin` L ->
       d_pat mode_tc ((x ~ dbind_typ A) ++ Γ)
         (open_exp_wrt_exp e (exp_var_f x)) Q) ->
    d_pat mode_tc Γ (exp_abs_anno A e)
      (bskl_tophole (bskl_arrow (pskl_to_bskl_syn (ptyp_to_pskl A)) Q))
| d_pat__app : forall Γ m e1 e2 P A1 A2,
    d_pat mode_tc Γ e2 (pskl_to_bskl_syn P) ->
    d_refine_syn nil Γ (pskl_to_bskl_syn P) (ptyp_to_pskl A1) ->
    d_typing (mode_fn m) Γ e1
      (btyp_arrow (ptyp_to_btyp_inh A1) (ptyp_to_btyp_inh A2)) ->
    d_pat m Γ (exp_app e1 e2) (pskl_to_bskl_syn (ptyp_to_pskl A2)).
