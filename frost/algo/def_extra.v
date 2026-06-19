(** Frost algorithmic-system definitions for the current split syntax.

    The algorithmic system is UNCOLOURED: every judgment ranges over
    [ptyp] / [pskl] (and [uskl] where needed) — never the coloured
    [btyp] / [bskl], which belong to the declarative system.  Painting to
    the coloured sorts happens only at the soundness/completeness bridge
    (see [algo/def_question.v]). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.

Set Implicit Arguments.

Inductive abind : Set :=
| abind_tvar : abind
| abind_var_typ : ptyp -> abind
| abind_flex_mono : abind
| abind_flex_mono_def : ptyp -> abind
| abind_flex_poly_def : pskl -> abind
| abind_marker : abind.

Definition aenv : Set := list (atom * abind).

Inductive a_suffix_binding : abind -> Prop :=
| a_suffix_binding__flex_mono :
    a_suffix_binding abind_flex_mono
| a_suffix_binding__flex_mono_def : forall A,
    a_suffix_binding (abind_flex_mono_def A)
| a_suffix_binding__flex_poly_def : forall P,
    a_suffix_binding (abind_flex_poly_def P).

Inductive a_suffix : aenv -> Prop :=
| a_suffix__nil : a_suffix nil
| a_suffix__cons : forall a b Ξ,
    a_suffix Ξ ->
    a_suffix_binding b ->
    a_suffix ((a ~ b) ++ Ξ).

Inductive a_mono_aenv : aenv -> Prop :=
| a_mono_aenv__nil : a_mono_aenv nil
| a_mono_aenv__cons : forall a b Θ,
    b <> abind_marker ->
    a_mono_aenv Θ ->
    a_mono_aenv ((a ~ b) ++ Θ)
| a_mono_aenv__marker : forall a Θ,
    a_mono_aenv Θ ->
    a_mono_aenv ((a ~ abind_marker) ++ Θ).

Inductive aenv_extends : aenv -> aenv -> Prop :=
| aenv_extends__refl : forall Θ, aenv_extends Θ Θ
| aenv_extends__suffix : forall Θ Ξ,
    a_suffix Ξ ->
    aenv_extends Θ (Ξ ++ Θ).

Inductive a_wf_aenv : aenv -> Prop :=
| a_wf_aenv__nil : a_wf_aenv nil
| a_wf_aenv__cons : forall a b Θ,
    a_wf_aenv Θ ->
    a `notin` dom Θ ->
    a_wf_aenv ((a ~ b) ++ Θ).

Inductive a_wf_ptyp : aenv -> ptyp -> Prop :=
| a_wf_ptyp__decl : forall Θ A,
    lc_ptyp A ->
    a_wf_ptyp Θ A.

Inductive a_wf_pskl : aenv -> pskl -> Prop :=
| a_wf_pskl__decl : forall Θ P,
    lc_pskl P ->
    a_wf_pskl Θ P.

Inductive a_guarded : aenv -> ptyp -> Prop :=
| a_guarded__ptyp : forall Θ A, a_wf_ptyp Θ A -> a_guarded Θ A.

(* [skmod_TY P M] / [skmod_SK P M] : P is a skeleton compatible with mode
   [M] for type / skeleton inference (paper [\skmod], algorithmic.tex).
   Uncoloured: over [pskl].  PLACEHOLDER bodies retained pending the full
   [\skmod] rules. *)
Inductive a_ty_mode_compat : mode -> ptyp -> Prop :=
| a_ty_mode_compat__any : forall m A, a_ty_mode_compat m A.

Inductive a_sk_mode_compat : mode -> pskl -> Prop :=
| a_sk_mode_compat__any : forall m P, a_sk_mode_compat m P.

Inductive a_sub_mode : Set :=
| a_sub_mode_ty : a_sub_mode
| a_sub_mode_sk : a_sub_mode.

Inductive a_non_flex_poly : aenv -> ptyp -> Prop :=
| a_non_flex_poly__ptyp : forall Θ A, a_wf_ptyp Θ A -> a_non_flex_poly Θ A.

(* [a_flex Θ P]: [P] is a (bound) flexible variable [α̂].  [a_non_flex Θ P]
   (paper [\nonflex{P}]): [P] is well-formed and NOT a flexible variable. *)
Inductive a_flex : aenv -> pskl -> Prop :=
| a_flex__var : forall Θ α,
    binds α abind_flex_mono Θ ->
    a_flex Θ (pskl_var_f α).

Definition a_non_flex (Θ : aenv) (P : pskl) : Prop :=
  lc_pskl P /\ ~ a_flex Θ P.

(* [guessMono P = (Ξ; A)] (paper algorithmic.tex): fill the holes of a
   skeleton [P] with fresh flexible variables [Ξ], yielding a type [A].
   Uncoloured: [pskl] in, [ptyp] out.  ([guess_SK P = (·; P)] is the
   identity and is inlined at the [N = SK] call sites.) *)
Inductive a_guess_mono : aenv -> pskl -> aenv -> ptyp -> Prop :=
| a_guess_mono__hole : forall Θ α,                            (* □ ↦ fresh α̂ *)
    a_guess_mono Θ pskl_hole ((α ~ abind_flex_mono) ++ nil) (ptyp_var_f α)
| a_guess_mono__tophole : forall Θ P Ξ A,                     (* ⫯.P ↦ guess P *)
    a_guess_mono Θ P Ξ A ->
    a_guess_mono Θ (pskl_tophole P) Ξ A
| a_guess_mono__var : forall Θ α,                             (* α / α̂ ↦ (·; α) *)
    a_guess_mono Θ (pskl_var_f α) nil (ptyp_var_f α)
| a_guess_mono__unit : forall Θ,
    a_guess_mono Θ pskl_unit nil ptyp_unit
| a_guess_mono__arrow : forall Θ P Q Ξ1 Ξ2 A B,
    a_guess_mono Θ P Ξ1 A ->
    a_guess_mono Θ Q Ξ2 B ->
    a_guess_mono Θ (pskl_arrow P Q) (Ξ1 ++ Ξ2) (ptyp_arrow A B)
| a_guess_mono__forall : forall L Θ P Ξ A,
    (forall α, α `notin` L ->
       a_guess_mono Θ (open_pskl_wrt_pskl P (pskl_var_f α)) Ξ
         (open_ptyp_wrt_ptyp A (ptyp_var_f α))) ->
    a_guess_mono Θ (pskl_all_syn P) Ξ (ptyp_all A).

(* (Dead [a_pre_sub]/[a_pre_join] bskl machinery removed — superseded by
   the uncoloured constraint-based [a_solve_*] judgments below.) *)

(* ===================================================================== *)
(*  Polymorphic information extraction (paper Fig. 10): constraint-based  *)
(*  algorithmic subtyping / consistency over plain (uncoloured) skeletons *)
(*  [pskl].  Hat-variables [α̂] are flexible variables ([pskl_var_f] bound  *)
(*  [abind_flex_mono] in [Θ]); [⫮] is [pskl_tophole], [□] is [pskl_hole].  *)
(* ===================================================================== *)

(* Constraints  [C ::= · | sub_m(P) | eq(P), C] *)
Inductive a_cstr : Set :=
| a_cstr_sub : mode -> pskl -> a_cstr
| a_cstr_eq : pskl -> a_cstr.
Definition a_cstrs : Set := list a_cstr.

(* [refresh(P) = (Ξ; P')]: instantiate [P]'s leading quantifiers with fresh
   flexible variables [Ξ], yielding the body [P']. *)
Inductive a_refresh : pskl -> aenv -> pskl -> Prop :=
| a_refresh__base : forall P,
    a_refresh P nil P
| a_refresh__all : forall L P Ξ P',
    (forall α, α `notin` L ->
       a_refresh (open_pskl_wrt_pskl P (pskl_var_f α)) Ξ P') ->
    a_refresh (pskl_all_syn P) Ξ P'.

Reserved Notation "P ≼[ α , m ] P' ⤳ Ξ ⨾ C"
  (at level 75, α at level 0, m at level 0, P' at level 74, Ξ at level 0,
   C at level 74, no associativity).
Reserved Notation "P ∼[ α ] P' ⤳ Ξ ⨾ C"
  (at level 75, α at level 0, P' at level 74, Ξ at level 0, C at level 74,
   no associativity).

(* Constraint collection: [P ≤_m P' ⤳^α Ξ; C] and [P ~ P' ⤳^α Ξ; C], where
   [α] is the flexible variable being solved for. *)
Inductive a_looksub : atom -> mode -> pskl -> pskl -> aenv -> a_cstrs -> Prop :=
| a_looksub__var : forall α m P Ξ P',           (* LS-Var *)
    a_refresh P Ξ P' ->
    (pskl_var_f α) ≼[ α , m ] P ⤳ Ξ ⨾ (a_cstr_sub m P' :: nil)
| a_looksub__absent : forall α m P P',           (* LS-Absent *)
    α `notin` ftvar_in_pskl P ->
    P ≼[ α , m ] P' ⤳ nil ⨾ nil
| a_looksub__vacuous : forall α m P P',          (* LS-Vacuous *)
    P ≼[ α , m ] (pskl_tophole P') ⤳ nil ⨾ nil
| a_looksub__check : forall α A B Ξ C,           (* LS-Check *)
    guarded_pskl A ->
    guarded_pskl B ->
    A ∼[ α ] B ⤳ Ξ ⨾ C ->
    A ≼[ α , mode_tc ] B ⤳ Ξ ⨾ C
| a_looksub__forall_r : forall L α A B Ξ C,      (* LS-ForallR *)
    (forall β, β `notin` L ->
       A ≼[ α , mode_tc ] (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ C) ->
    A ≼[ α , mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ C
| a_looksub__arrow : forall α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2,   (* LS-Arrow *)
    P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 ->
    P2 ≼[ α , m ] P2' ⤳ Ξ2 ⨾ C2 ->
    (pskl_arrow P1 P2) ≼[ α , (mode_fn m) ] (pskl_arrow P1' P2')
        ⤳ (Ξ1 ++ Ξ2) ⨾ (C1 ++ C2)
| a_looksub__forall_l : forall L α m P P' Ξ C,   (* LS-ForallL *)
    (forall β, β `notin` L ->
       (open_pskl_wrt_pskl P (pskl_var_f β)) ≼[ α , m ] P' ⤳ Ξ ⨾ C) ->
    (pskl_all_syn P) ≼[ α , m ] P' ⤳ Ξ ⨾ C
| a_looksub__univ_ghost_l : forall α m P P' Ξ C, (* LS-UnivGhostL *)
    P ≼[ α , m ] P' ⤳ Ξ ⨾ C ->
    (pskl_tophole P) ≼[ α , m ] P' ⤳ Ξ ⨾ C

with a_lookeq : atom -> pskl -> pskl -> aenv -> a_cstrs -> Prop :=
| a_lookeq__var : forall α P Ξ P',               (* LE-Var *)
    a_refresh P Ξ P' ->
    (pskl_var_f α) ∼[ α ] P ⤳ Ξ ⨾ (a_cstr_eq P' :: nil)
| a_lookeq__absent : forall α P P',              (* LE-Absent *)
    α `notin` ftvar_in_pskl P ->
    P ∼[ α ] P' ⤳ nil ⨾ nil
| a_lookeq__vacuous : forall α P P',             (* LE-Vacuous *)
    P ∼[ α ] (pskl_tophole P') ⤳ nil ⨾ nil
| a_lookeq__flex_r : forall α P β γ,             (* LE-FlexR (β̂ a flex var) *)
    P <> pskl_var_f α ->
    α `in` ftvar_in_pskl P ->
    P ∼[ α ] (pskl_var_f β) ⤳ ((γ ~ abind_flex_mono) ++ nil)
        ⨾ (a_cstr_eq (pskl_var_f γ) :: nil)
| a_lookeq__arrow : forall α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2,      (* LE-Arrow *)
    P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 ->
    P2 ∼[ α ] P2' ⤳ Ξ2 ⨾ C2 ->
    (pskl_arrow P1 P2) ∼[ α ] (pskl_arrow P1' P2') ⤳ (Ξ1 ++ Ξ2) ⨾ (C1 ++ C2)
| a_lookeq__forall_inh : forall L α P P' Ξ C,    (* LE-ForallInh *)
    (forall β, β `notin` L ->
       (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ]
         (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ ⨾ C) ->
    (pskl_all_syn P) ∼[ α ] (pskl_all_syn P') ⤳ Ξ ⨾ C
| a_lookeq__forall_syn : forall L α P P' Ξ C,    (* LE-ForallSyn *)
    (forall β, β `notin` L ->
       (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ] (pskl_tophole P') ⤳ Ξ ⨾ C) ->
    (pskl_all_syn P) ∼[ α ] (pskl_tophole P') ⤳ Ξ ⨾ C
| a_lookeq__univ_ghost : forall α P P' Ξ C,      (* LE-UnivGhost *)
    P ∼[ α ] P' ⤳ Ξ ⨾ C ->
    (pskl_tophole P) ∼[ α ] (pskl_tophole P') ⤳ Ξ ⨾ C
| a_lookeq__univ_ghost1 : forall L α P P' Ξ C,   (* LE-UnivGhost1 *)
    (forall β, β `notin` L ->
       (pskl_tophole P) ∼[ α ] (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ ⨾ C) ->
    (pskl_tophole P) ∼[ α ] (pskl_all_syn P') ⤳ Ξ ⨾ C
| a_lookeq__univ_ghost2 : forall α P P' Ξ C,     (* LE-UnivGhost2 *)
    guarded_pskl P' ->
    P ∼[ α ] P' ⤳ Ξ ⨾ C ->
    (pskl_tophole P) ∼[ α ] P' ⤳ Ξ ⨾ C
| a_lookeq__univ_ghost_r : forall α P P' Ξ C,    (* LE-UnivGhostR *)
    P <> pskl_var_f α ->
    guarded_pskl P ->
    P ∼[ α ] P' ⤳ Ξ ⨾ C ->
    P ∼[ α ] (pskl_tophole P') ⤳ Ξ ⨾ C
where "P ≼[ α , m ] P' ⤳ Ξ ⨾ C" := (a_looksub α m P P' Ξ C) : type_scope
  and "P ∼[ α ] P' ⤳ Ξ ⨾ C" := (a_lookeq α P P' Ξ C) : type_scope.

Reserved Notation "Θ ⊢ₛ P ≼[ m ] Q ⤳ P'"
  (at level 75, P at level 74, m at level 0, Q at level 74, P' at level 74,
   no associativity).
Reserved Notation "Θ ⊢ₑ P ∼ Q ⤳ P'"
  (at level 75, P at level 74, Q at level 74, P' at level 74, no associativity).

(* [solve(P ≤_m Q) = P'] / [solve(P ~ Q) = P'] (paper Fig. 10), as relations.
   [Θ] lets the flex-variable rules ([α̂] absorbs) check [abind_flex_mono]. *)
Inductive a_solve_sub : aenv -> mode -> pskl -> pskl -> pskl -> Prop :=
| a_solve_sub__var : forall Θ m X Q,
    Θ ⊢ₛ (pskl_var_f X) ≼[ m ] Q ⤳ (pskl_var_f X)
| a_solve_sub__forall_l : forall L Θ m P Q P',
    (forall β, β `notin` L ->
       Θ ⊢ₛ (open_pskl_wrt_pskl P (pskl_var_f β)) ≼[ m ] Q
            ⤳ (open_pskl_wrt_pskl P' (pskl_var_f β))) ->
    Θ ⊢ₛ (pskl_all_syn P) ≼[ m ] Q ⤳ (pskl_all_syn P')
| a_solve_sub__univ_ghost_l : forall Θ m P Q P',
    Θ ⊢ₛ P ≼[ m ] Q ⤳ P' ->
    Θ ⊢ₛ (pskl_tophole P) ≼[ m ] Q ⤳ (pskl_tophole P')
| a_solve_sub__top_r : forall Θ m P P',
    Θ ⊢ₛ P ≼[ m ] (pskl_tophole P') ⤳ P
| a_solve_sub__check : forall Θ P Q P',
    guarded_pskl P ->
    guarded_pskl Q ->
    Θ ⊢ₑ P ∼ Q ⤳ P' ->
    Θ ⊢ₛ P ≼[ mode_tc ] Q ⤳ P'
| a_solve_sub__forall_r : forall Θ A B P',
    Θ ⊢ₛ A ≼[ mode_tc ] (open_pskl_wrt_pskl B (pskl_tophole pskl_hole)) ⤳ P' ->
    Θ ⊢ₛ A ≼[ mode_tc ] (pskl_all_syn B) ⤳ P'
| a_solve_sub__arrow : forall Θ m P1 P2 Q1 Q2 P1' P2',
    Θ ⊢ₑ P1 ∼ Q1 ⤳ P1' ->
    Θ ⊢ₛ P2 ≼[ m ] Q2 ⤳ P2' ->
    Θ ⊢ₛ (pskl_arrow P1 P2) ≼[ (mode_fn m) ] (pskl_arrow Q1 Q2)
         ⤳ (pskl_arrow P1' P2')

with a_solve_eq : aenv -> pskl -> pskl -> pskl -> Prop :=
| a_solve_eq__flex_l : forall Θ α Q,
    binds α abind_flex_mono Θ ->
    Θ ⊢ₑ (pskl_var_f α) ∼ Q ⤳ (pskl_var_f α)
| a_solve_eq__flex_r : forall Θ α P,
    binds α abind_flex_mono Θ ->
    Θ ⊢ₑ P ∼ (pskl_var_f α) ⤳ (pskl_var_f α)
| a_solve_eq__unit : forall Θ,
    Θ ⊢ₑ pskl_unit ∼ pskl_unit ⤳ pskl_unit
| a_solve_eq__var : forall Θ X,
    Θ ⊢ₑ (pskl_var_f X) ∼ (pskl_var_f X) ⤳ (pskl_var_f X)
| a_solve_eq__hole_l : forall Θ Q,
    Θ ⊢ₑ pskl_hole ∼ Q ⤳ Q
| a_solve_eq__hole_r : forall Θ P,
    Θ ⊢ₑ P ∼ pskl_hole ⤳ P
| a_solve_eq__arrow : forall Θ P1 P2 Q1 Q2 P1' P2',
    Θ ⊢ₑ P1 ∼ Q1 ⤳ P1' ->
    Θ ⊢ₑ P2 ∼ Q2 ⤳ P2' ->
    Θ ⊢ₑ (pskl_arrow P1 P2) ∼ (pskl_arrow Q1 Q2) ⤳ (pskl_arrow P1' P2')
| a_solve_eq__forall : forall L Θ P Q P',
    (forall β, β `notin` L ->
       Θ ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f β))
            ∼ (open_pskl_wrt_pskl Q (pskl_var_f β))
            ⤳ (open_pskl_wrt_pskl P' (pskl_var_f β))) ->
    Θ ⊢ₑ (pskl_all_syn P) ∼ (pskl_all_syn Q) ⤳ (pskl_all_syn P')
| a_solve_eq__tophole_both : forall Θ P Q P',
    Θ ⊢ₑ P ∼ Q ⤳ P' ->
    Θ ⊢ₑ (pskl_tophole P) ∼ (pskl_tophole Q) ⤳ (pskl_tophole P')
| a_solve_eq__tophole_l_all : forall L Θ P Q P',
    (forall β, β `notin` L ->
       Θ ⊢ₑ (pskl_tophole P) ∼ (open_pskl_wrt_pskl Q (pskl_var_f β))
            ⤳ (open_pskl_wrt_pskl P' (pskl_var_f β))) ->
    Θ ⊢ₑ (pskl_tophole P) ∼ (pskl_all_syn Q) ⤳ (pskl_all_syn P')
| a_solve_eq__all_l_tophole : forall L Θ P Q P',
    (forall β, β `notin` L ->
       Θ ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼ (pskl_tophole Q)
            ⤳ (open_pskl_wrt_pskl P' (pskl_var_f β))) ->
    Θ ⊢ₑ (pskl_all_syn P) ∼ (pskl_tophole Q) ⤳ (pskl_all_syn P')
| a_solve_eq__tophole_l_guarded : forall Θ P Q P',
    guarded_pskl Q ->
    Θ ⊢ₑ P ∼ Q ⤳ P' ->
    Θ ⊢ₑ (pskl_tophole P) ∼ Q ⤳ P'
| a_solve_eq__tophole_r_guarded : forall Θ P Q P',
    guarded_pskl P ->
    Θ ⊢ₑ P ∼ Q ⤳ P' ->
    Θ ⊢ₑ P ∼ (pskl_tophole Q) ⤳ P'
where "Θ ⊢ₛ P ≼[ m ] Q ⤳ P'" := (a_solve_sub Θ m P Q P') : type_scope
  and "Θ ⊢ₑ P ∼ Q ⤳ P'" := (a_solve_eq Θ P Q P') : type_scope.

Reserved Notation "Θ ⊩ C ⨾ P ⤳ Q"
  (at level 75, C at level 74, P at level 74, Q at level 74, no associativity).
(* Constraint solving  [C; P ⤳ Q] (paper Fig. 10). *)
Inductive a_solve_cstr : aenv -> a_cstrs -> pskl -> pskl -> Prop :=
| a_solve_cstr__empty : forall Θ P,
    Θ ⊩ nil ⨾ P ⤳ P
| a_solve_cstr__sub : forall Θ m Q P P',
    Θ ⊢ₛ P ≼[ m ] Q ⤳ P' ->
    Θ ⊩ (a_cstr_sub m Q :: nil) ⨾ P ⤳ P'
| a_solve_cstr__eq : forall Θ Q C P P' P'',
    Θ ⊢ₑ P ∼ Q ⤳ P'' ->
    Θ ⊩ C ⨾ P'' ⤳ P' ->
    Θ ⊩ (a_cstr_eq Q :: C) ⨾ P ⤳ P'
where "Θ ⊩ C ⨾ P ⤳ Q" := (a_solve_cstr Θ C P Q) : type_scope.

Reserved Notation "P ⊳[ α , m ] P' ⤳ Ξ ↪ Q"
  (at level 75, α at level 0, m at level 0, P' at level 74, Ξ at level 0,
   Q at level 74, no associativity).
(* Top-level information extraction  [P ≤_m P' ⤳^α Ξ; Q]: collect, then solve
   the constraints from the universal ghost (paper Fig. 10). *)
Inductive a_extract : atom -> mode -> pskl -> pskl -> aenv -> pskl -> Prop :=
| a_extract__solve : forall α m P P' Ξ C Q,
    P ≼[ α , m ] P' ⤳ Ξ ⨾ C ->
    Ξ ⊩ C ⨾ (pskl_tophole pskl_hole) ⤳ Q ->
    P ⊳[ α , m ] P' ⤳ Ξ ↪ Q
where "P ⊳[ α , m ] P' ⤳ Ξ ↪ Q" := (a_extract α m P P' Ξ Q) : type_scope.

(* ----- Flexible-variable solving (move judgments), paper fig:alg-consistency.
   [a_unify Θ0 α̂ β̂ Θ1] = [Θ0 ⊲ α̂ ≈ β̂ ⊣ Θ1]; the two arguments are [ptyp]
   so that [Flex-Flex-Assign]'s forward substitution [α̂[τ/γ̂]] stays in-sort.
   [a_assign Θ0 Ξ α̂ P Θ1] = [Θ0 | Ξ ⊲ α̂ := P ⊣ Θ1]; [Ξ] is the pending-suffix
   accumulator.  Both judgments peel the list HEAD — the rightmost (most
   recent) entry in the paper's [Θ0, e].  Substitution [P[τ/β̂]] over a
   skeleton is [subst_pskl_in_pskl (ptyp_to_pskl τ) β P] (a monotype [τ]
   embedded into [pskl]); see DESIGN/spec for the in-sort argument. ----- *)
Inductive a_unify : aenv -> ptyp -> ptyp -> aenv -> Prop :=
| a_unify__flex_id : forall Θ0 α,                          (* Flex-Flex-Id *)
    binds α abind_flex_mono Θ0 ->
    a_unify Θ0 (ptyp_var_f α) (ptyp_var_f α) Θ0
| a_unify__flex_l : forall Θ0 α β,                         (* Flex-Flex-L *)
    α <> β ->
    a_unify ((α ~ abind_flex_mono) ++ Θ0) (ptyp_var_f α) (ptyp_var_f β)
      ((α ~ abind_flex_mono_def (ptyp_var_f β)) ++ Θ0)
| a_unify__flex_r : forall Θ0 α β,                         (* Flex-Flex-R *)
    α <> β ->
    a_unify ((β ~ abind_flex_mono) ++ Θ0) (ptyp_var_f α) (ptyp_var_f β)
      ((β ~ abind_flex_mono_def (ptyp_var_f α)) ++ Θ0)
| a_unify__flex_assign : forall Θ0 Θ1 γ τ A B,             (* Flex-Flex-Assign *)
    a_unify Θ0 (subst_ptyp_in_ptyp τ γ A) (subst_ptyp_in_ptyp τ γ B) Θ1 ->
    a_unify ((γ ~ abind_flex_mono_def τ) ++ Θ0) A B
      ((γ ~ abind_flex_mono_def τ) ++ Θ1)
| a_unify__flex_skip : forall Θ0 Θ1 γ A B,                 (* Flex-Flex-Skip (flex γ̂) *)
    γ `notin` (ftvar_in_ptyp A `union` ftvar_in_ptyp B) ->
    a_unify Θ0 A B Θ1 ->
    a_unify ((γ ~ abind_flex_mono) ++ Θ0) A B ((γ ~ abind_flex_mono) ++ Θ1)
| a_unify__skip_other : forall Θ0 Θ1 c b A B,              (* Flex-Flex-Skip (rigid γ / x:Q) *)
    (b = abind_tvar \/ (exists Q, b = abind_var_typ Q)) ->
    a_unify Θ0 A B Θ1 ->
    a_unify ((c ~ b) ++ Θ0) A B ((c ~ b) ++ Θ1).

(* [a_assign].  NB (Finding F10): the paper's [Assign-Assign] premise is
   written [unify(S[τ/β̂])(α̂[τ/β̂])] over a merged context [Θ0,Ξ], but the
   assigned object [P] is a general skeleton (only monotype-ified later, in
   [Assign-SolveM] via [guessMono]), so [unify] (monotype-level) does not
   apply to it.  We mechanize the coherent reading: CONTINUE the assignment
   on [P[τ/β̂]] (keeping the [Θ0 | Ξ] split), since [α̂ ≠ β̂] makes
   [α̂[τ/β̂] = α̂].  Flagged for back-port. *)
Inductive a_assign : aenv -> aenv -> atom -> pskl -> aenv -> Prop :=
| a_assign__solve_m : forall Θ0 Ξ α P βs τ,               (* Assign-SolveM *)
    α `notin` ftvar_in_pskl P ->
    a_guess_mono Θ0 P βs τ ->
    a_assign ((α ~ abind_flex_mono) ++ Θ0) Ξ α P
      ((α ~ abind_flex_mono_def τ) ++ βs ++ Ξ ++ Θ0)
| a_assign__assign : forall Θ0 Θ1 Ξ α β τ P,              (* Assign-Assign (see F10) *)
    a_assign Θ0 Ξ α (subst_pskl_in_pskl (ptyp_to_pskl τ) β P) Θ1 ->
    a_assign ((β ~ abind_flex_mono_def τ) ++ Θ0) Ξ α P
      ((β ~ abind_flex_mono_def τ) ++ Θ1)
| a_assign__depend : forall Θ0 Θ1 Ξ α β P,                (* Assign-Depend *)
    α <> β ->
    β `in` ftvar_in_pskl P ->
    a_assign Θ0 ((β ~ abind_flex_mono) ++ Ξ) α P Θ1 ->
    a_assign ((β ~ abind_flex_mono) ++ Θ0) Ξ α P Θ1
| a_assign__skip : forall Θ0 Θ1 Ξ α β P,                  (* Assign-Skip *)
    α <> β ->
    β `notin` ftvar_in_pskl P ->
    a_assign Θ0 Ξ α P Θ1 ->
    a_assign ((β ~ abind_flex_mono) ++ Θ0) Ξ α P ((β ~ abind_flex_mono) ++ Θ1)
| a_assign__skip_rigid : forall Θ0 Θ1 Ξ α β P,            (* Assign-SkipRigid *)
    β `notin` ftvar_in_pskl P ->
    a_assign Θ0 Ξ α P Θ1 ->
    a_assign ((β ~ abind_tvar) ++ Θ0) Ξ α P ((β ~ abind_tvar) ++ Θ1)
| a_assign__skip_tm_var : forall Θ0 Θ1 Ξ α x Q P,         (* Assign-SkipTmVar *)
    a_assign Θ0 Ξ α P Θ1 ->
    a_assign ((x ~ abind_var_typ Q) ++ Θ0) Ξ α P ((x ~ abind_var_typ Q) ++ Θ1).

(* ===================================================================== *)
(*  Algorithmic consistency  [Θ0 ⊢ P ~ Q ⊣ Θ1] with inherited skeleton    *)
(*  [P0]  (paper fig:alg-consistency).  Uncoloured: over [pskl].          *)
(*  [□]=[pskl_hole], [⫯.P]=[pskl_tophole P], [∀α.P]=[pskl_all_syn P].      *)
(*  Flex rules (Flex/FlexL/FlexR) are DEFERRED with the move machinery.    *)
(* ===================================================================== *)
Inductive a_consis : aenv -> pskl -> pskl -> pskl -> aenv -> Prop :=
| a_consis__ghost : forall Θ0 P,                              (* Ghost *)
    a_consis Θ0 P pskl_hole P Θ0
| a_consis__unit : forall Θ0,                                 (* Unit *)
    a_consis Θ0 pskl_unit pskl_unit pskl_unit Θ0
| a_consis__rigid : forall Θ0 α,                              (* Rigid *)
    binds α abind_tvar Θ0 ->
    a_consis Θ0 (pskl_var_f α) (pskl_var_f α) (pskl_var_f α) Θ0
| a_consis__arrow : forall Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2,      (* Arrow *)
    a_consis Θ0 P0a P1 Q1 Θ1 ->
    a_consis Θ1 P0b P2 Q2 Θ2 ->
    a_consis Θ0 (pskl_arrow P0a P0b) (pskl_arrow P1 P2) (pskl_arrow Q1 Q2) Θ2
| a_consis__forall_inh : forall L Θ0 Θ1 P0 P Q,              (* ForallInh *)
    (forall α, α `notin` L ->
       a_consis ((α ~ abind_tvar) ++ Θ0)
         (open_pskl_wrt_pskl P0 (pskl_var_f α))
         (open_pskl_wrt_pskl P (pskl_var_f α))
         (open_pskl_wrt_pskl Q (pskl_var_f α))
         ((α ~ abind_tvar) ++ Θ1)) ->
    a_consis Θ0 (pskl_all_syn P0) (pskl_all_syn P) (pskl_all_syn Q) Θ1
| a_consis__forall_syn : forall L Θ0 Θ1 P0 P Q,             (* ForallSyn *)
    (forall α, α `notin` L ->
       a_consis ((α ~ abind_tvar) ++ Θ0)
         (pskl_tophole P0)
         (open_pskl_wrt_pskl P (pskl_var_f α))
         (open_pskl_wrt_pskl Q (pskl_var_f α))
         ((α ~ abind_tvar) ++ Θ1)) ->
    a_consis Θ0 (pskl_tophole P0) (pskl_all_syn P) (pskl_all_syn Q) Θ1
| a_consis__univ_ghost : forall Θ0 Θ1 P0 P Q,               (* UnivGhost *)
    a_consis Θ0 P0 P Q Θ1 ->
    a_consis Θ0 (pskl_tophole P0) (pskl_tophole P) (pskl_tophole Q) Θ1
| a_consis__univ_ghost1 : forall L Θ0 Θ1 P0 P Q,            (* UnivGhost1 *)
    (forall α, α `notin` L ->
       a_consis ((α ~ abind_tvar) ++ Θ0)
         (open_pskl_wrt_pskl P0 (pskl_var_f α))
         (pskl_tophole P)
         (open_pskl_wrt_pskl Q (pskl_var_f α))
         ((α ~ abind_tvar) ++ Θ1)) ->
    a_consis Θ0 (pskl_all_syn P0) (pskl_tophole P) (pskl_all_syn Q) Θ1
| a_consis__univ_ghost2 : forall Θ0 Θ1 P0 P Q,             (* UnivGhost2 *)
    guarded_pskl P0 ->
    (forall β, P0 <> pskl_var_f β) ->
    a_consis Θ0 P0 P Q Θ1 ->
    a_consis Θ0 P0 (pskl_tophole P) Q Θ1
| a_consis__ghost_r : forall Θ0 P,                          (* GhostR *)
    a_consis Θ0 pskl_hole P P Θ0
| a_consis__univ_ghost_r : forall Θ0 Θ1 P0 P Q,            (* UnivGhostR *)
    guarded_pskl P ->
    (forall β, P <> pskl_var_f β) ->
    a_consis Θ0 P0 P Q Θ1 ->
    a_consis Θ0 (pskl_tophole P0) P Q Θ1
| a_consis__flex : forall Θ0 Θ1 α β,                       (* Flex *)
    a_unify Θ0 (ptyp_var_f α) (ptyp_var_f β) Θ1 ->
    a_consis Θ0 (pskl_var_f β) (pskl_var_f α) (pskl_var_f α) Θ1
| a_consis__flex_l : forall Θ0 Θ1 α P0,                    (* FlexL *)
    a_non_flex Θ0 P0 ->
    a_assign Θ0 nil α P0 Θ1 ->
    a_consis Θ0 P0 (pskl_var_f α) (pskl_var_f α) Θ1
| a_consis__flex_r : forall Θ0 Θ1 α P,                     (* FlexR *)
    a_non_flex Θ0 P ->
    a_assign Θ0 nil α P Θ1 ->
    a_consis Θ0 (pskl_var_f α) P (pskl_var_f α) Θ1.

(* [Θ0 ⊢ P ~ P0 ⊣ Θ1]: consistency when the join output is not used
   (paper abbreviation [aconsis{Θ0}{P}{P0}{Θ1}]). *)
Definition a_consis_chk (Θ0 : aenv) (P P0 : pskl) (Θ1 : aenv) : Prop :=
  exists Q, a_consis Θ0 P0 P Q Θ1.

(* Flexible-variable subtyping (the "broom" [◁], paper fig:alg-subtyping
   second box).  DEFERRED: minimal reflexive stub at uncoloured sort. *)
Inductive a_broom : a_sub_mode -> mode -> pskl -> aenv -> pskl -> pskl -> aenv -> Prop :=
| a_broom__refl : forall NM m P0 Θ P, a_broom NM m P0 Θ P P Θ.

(* ===================================================================== *)
(*  Algorithmic subtyping  [Θ0 ⊢_{N;M;P0} P ⊑ Q ⊣ Θ1]                      *)
(*  (paper fig:alg-subtyping, main box).  Uncoloured: over [pskl].        *)
(*  DEFERRED: ForallL (instantiation via extract/guess) and FlexMono      *)
(*  (the flex-variable [◁] box).                                          *)
(* ===================================================================== *)
Inductive a_sub : a_sub_mode -> mode -> pskl -> aenv -> pskl -> pskl -> aenv -> Prop :=
| a_sub__infer : forall NM P Θ0,                              (* Infer *)
    a_sub NM mode_ti pskl_hole Θ0 P P Θ0
| a_sub__check : forall Θ0 Θ1 A B,                           (* Check *)
    guarded_pskl A -> guarded_pskl B ->
    a_consis_chk Θ0 A B Θ1 ->
    a_sub a_sub_mode_ty mode_tc B Θ0 A B Θ1
| a_sub__forall_r : forall L Θ0 Θ1 Ξ A B,                    (* ForallR *)
    a_suffix Ξ ->
    (forall α, α `notin` L ->
       a_sub a_sub_mode_ty mode_tc (open_pskl_wrt_pskl B (pskl_var_f α))
         ((α ~ abind_tvar) ++ Θ0) A (open_pskl_wrt_pskl B (pskl_var_f α))
         (Ξ ++ (α ~ abind_tvar) ++ Θ1)) ->
    a_sub a_sub_mode_ty mode_tc (pskl_all_syn B) Θ0 A (pskl_all_syn B) Θ1
| a_sub__univ_ghost_r : forall Θ0 P,                         (* UnivGhostR *)
    guarded_pskl P ->
    a_sub a_sub_mode_sk mode_tc pskl_hole Θ0 P (pskl_tophole P) Θ0
| a_sub__arrow : forall NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2,   (* Arrow *)
    a_consis Θ0 P0a P1 Q1 Θ1 ->
    a_sub NM M P0b Θ1 P2 Q2 Θ2 ->
    a_sub NM (mode_fn M) (pskl_arrow P0a P0b) Θ0 (pskl_arrow P1 P2)
      (pskl_arrow Q1 Q2) Θ2
| a_sub__ghost : forall M Θ0 P0,                             (* Ghost *)
    a_sub a_sub_mode_sk M P0 Θ0 pskl_hole P0 Θ0
| a_sub__univ_ghost_l : forall M Θ0 Θ1 P0 P Q,              (* UnivGhostL *)
    M <> mode_ti ->
    a_sub a_sub_mode_sk M P0 Θ0 P Q Θ1 ->
    a_sub a_sub_mode_sk M P0 Θ0 (pskl_tophole P) Q Θ1.

(* Skeleton splitting  [Θ0 ⊢ split P0 = P→Q ⊣ Θ1]
   (paper fig:alg-type-inference).  Uncoloured.  Flex case deferred. *)
Inductive a_split : aenv -> pskl -> pskl -> pskl -> aenv -> Prop :=
| a_split__arrow : forall Θ0 P Q,
    a_split Θ0 (pskl_arrow P Q) P Q Θ0
| a_split__hole : forall Θ0,
    a_split Θ0 pskl_hole pskl_hole pskl_hole Θ0.

(* Algorithmic type inference [Θ ⊢[m;P0] e ⦂ A ⊣ Θ'] (output [ptyp]) and
   skeleton inference [Θ ⊢[m;P0] e ⇨ P ⊣ Θ'] (output [pskl]) — paper
   fig:alg-type-inference / fig:alg-skeleton-inference.  Uncoloured: the
   whole algorithm works on [ptyp]/[pskl], no [btyp]/[bskl] painting (that
   happens only at the soundness/completeness bridge). *)
Inductive a_typing : mode -> aenv -> pskl -> exp -> ptyp -> aenv -> Prop :=
| a_typing__unit : forall m Θ0 P0 A Θ1,
    a_sub a_sub_mode_ty m P0 Θ0 pskl_unit (ptyp_to_pskl A) Θ1 ->
    a_typing m Θ0 P0 exp_unit A Θ1
| a_typing__var : forall m Θ0 P0 x A B Θ1,
    binds x (abind_var_typ A) Θ0 ->
    a_sub a_sub_mode_ty m P0 Θ0 (ptyp_to_pskl A) (ptyp_to_pskl B) Θ1 ->
    a_typing m Θ0 P0 (exp_var_f x) B Θ1
| a_typing__anno : forall m Θ0 P0 e A B Θ1 Θ2,
    a_typing mode_tc Θ0 (ptyp_to_pskl A) e A Θ1 ->
    a_sub a_sub_mode_ty m P0 Θ1 (ptyp_to_pskl A) (ptyp_to_pskl B) Θ2 ->
    a_typing m Θ0 P0 (exp_anno e A) B Θ2
| a_typing__freeze : forall Θ0 P0 e A B Θ1 Θ2,
    a_typing mode_ti Θ0 pskl_hole e B Θ1 ->
    a_consis_chk Θ1 (ptyp_to_pskl B) (ptyp_to_pskl A) Θ2 ->
    a_typing mode_tc Θ0 P0 (exp_freeze e) A Θ2
| a_typing__abs : forall L m Θ0 Θ1 Θ2 P0 P Q αs A e B Ξ,
    m <> mode_tc ->
    a_split Θ0 P0 P Q Θ1 ->
    a_guess_mono Θ1 P αs A ->
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       a_typing (decr_mode m) ((x ~ abind_var_typ A) ++ αs ++ Θ1) Q
         (open_exp_wrt_exp e (exp_var_f x)) B
         (Ξ ++ (x ~ abind_var_typ A) ++ Θ2)) ->
    a_typing m Θ0 P0 (exp_abs e) (ptyp_arrow A B) (Ξ ++ Θ2)
| a_typing__abs_anno : forall L m Θ0 Θ1 Θ2 Θ3 P0 P Q A e B Ξ,
    m <> mode_tc ->
    a_split Θ0 P0 P Q Θ1 ->
    a_consis_chk Θ1 (ptyp_to_pskl A) P Θ2 ->
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       a_typing (decr_mode m) ((x ~ abind_var_typ A) ++ Θ2) Q
         (open_exp_wrt_exp e (exp_var_f x)) B
         (Ξ ++ (x ~ abind_var_typ A) ++ Θ3)) ->
    a_typing m Θ0 P0 (exp_abs_anno A e) (ptyp_arrow A B) (Ξ ++ Θ3)
| a_typing__abs_check : forall L Θ0 Θ1 A e B Ξ,
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       a_typing mode_tc ((x ~ abind_var_typ A) ++ Θ0) pskl_hole
         (open_exp_wrt_exp e (exp_var_f x)) B
         (Ξ ++ (x ~ abind_var_typ A) ++ Θ1)) ->
    a_typing mode_tc Θ0 pskl_hole (exp_abs e) (ptyp_arrow A B) (Ξ ++ Θ1)
| a_typing__abs_anno_check : forall L Θ0 Θ1 Θ2 A e B Ξ,
    a_consis_chk Θ0 (ptyp_to_pskl A) (ptyp_to_pskl A) Θ1 ->
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       a_typing mode_tc ((x ~ abind_var_typ A) ++ Θ1) pskl_hole
         (open_exp_wrt_exp e (exp_var_f x)) B
         (Ξ ++ (x ~ abind_var_typ A) ++ Θ2)) ->
    a_typing mode_tc Θ0 pskl_hole (exp_abs_anno A e) (ptyp_arrow A B) (Ξ ++ Θ2)
| a_typing__app : forall m Θ0 Θ1 Θ2 Θ3 P Q A A' B e1 e2,
    a_pat mode_tc Θ0 pskl_hole e2 P Θ1 ->
    a_typing (mode_fn m) Θ1 (pskl_arrow P Q) e1 (ptyp_arrow A B) Θ2 ->
    a_typing mode_tc Θ2 (ptyp_to_pskl A) e2 A' Θ3 ->
    a_typing m Θ0 Q (exp_app e1 e2) B Θ3

with a_pat : mode -> aenv -> pskl -> exp -> pskl -> aenv -> Prop :=
| a_pat__unit : forall m Θ0 P0,
    a_pat m Θ0 P0 exp_unit pskl_unit Θ0
| a_pat__var : forall m Θ0 P0 x P,
    binds x (abind_var_typ P) Θ0 ->
    a_pat m Θ0 P0 (exp_var_f x) (ptyp_to_pskl P) Θ0
| a_pat__anno : forall m Θ0 P0 e A,
    a_pat m Θ0 P0 (exp_anno e A) (ptyp_to_pskl A) Θ0
| a_pat__freeze : forall Θ0 e Q Θ1,
    a_pat mode_ti Θ0 pskl_hole e Q Θ1 ->
    a_pat mode_tc Θ0 pskl_hole (exp_freeze e) Q Θ1
| a_pat__abs : forall L m Θ0 Θ2 P e Q Ξ,
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       a_pat (decr_mode m) ((x ~ abind_var_typ P) ++ Θ0) pskl_hole
         (open_exp_wrt_exp e (exp_var_f x)) Q
         (Ξ ++ (x ~ abind_var_typ P) ++ Θ2)) ->
    a_pat m Θ0 (ptyp_to_pskl P) (exp_abs e)
      (pskl_arrow (ptyp_to_pskl P) Q) (Ξ ++ Θ2)
| a_pat__abs_check : forall L Θ0 Θ1 e Q Ξ,
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       a_pat mode_tc ((x ~ abind_var_typ ptyp_unit) ++ Θ0) pskl_hole
         (open_exp_wrt_exp e (exp_var_f x)) Q
         (Ξ ++ (x ~ abind_var_typ ptyp_unit) ++ Θ1)) ->
    a_pat mode_tc Θ0 pskl_hole (exp_abs e)
      (pskl_tophole (pskl_arrow pskl_hole Q)) (Ξ ++ Θ1)
| a_pat__abs_anno : forall L m Θ0 Θ2 A e Q Ξ,
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       a_pat (decr_mode m) ((x ~ abind_var_typ A) ++ Θ0) pskl_hole
         (open_exp_wrt_exp e (exp_var_f x)) Q
         (Ξ ++ (x ~ abind_var_typ A) ++ Θ2)) ->
    a_pat m Θ0 (ptyp_to_pskl A) (exp_abs_anno A e)
      (pskl_arrow (ptyp_to_pskl A) Q) (Ξ ++ Θ2)
| a_pat__abs_anno_check : forall L Θ0 Θ1 A e Q Ξ,
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       a_pat mode_tc ((x ~ abind_var_typ A) ++ Θ0) pskl_hole
         (open_exp_wrt_exp e (exp_var_f x)) Q
         (Ξ ++ (x ~ abind_var_typ A) ++ Θ1)) ->
    a_pat mode_tc Θ0 pskl_hole (exp_abs_anno A e)
      (pskl_tophole (pskl_arrow (ptyp_to_pskl A) Q)) (Ξ ++ Θ1)
| a_pat__app : forall m Θ0 Θ1 Θ2 Θ3 P Q A A2 B Sres e1 e2,
    a_pat mode_tc Θ0 pskl_hole e2 P Θ1 ->
    a_typing (mode_fn m) Θ1 (pskl_arrow P Q) e1 (ptyp_arrow A B) Θ2 ->
    a_pat mode_tc Θ2 (ptyp_to_pskl A) e2 Sres Θ3 ->
    a_pat m Θ0 Q (exp_app e1 e2) (pskl_arrow A2 Sres) Θ3.
