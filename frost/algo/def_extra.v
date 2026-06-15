(** Frost algorithmic-system definitions for the current split syntax.

    This file intentionally uses the latest generated categories
    directly: [ptyp], [btyp], [utyp], [pskl], [bskl], and [uskl]. *)

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

Inductive a_wf_btyp : aenv -> btyp -> Prop :=
| a_wf_btyp__decl : forall Θ B,
    lc_btyp B ->
    a_wf_btyp Θ B.

Inductive a_wf_pskl : aenv -> pskl -> Prop :=
| a_wf_pskl__decl : forall Θ P,
    lc_pskl P ->
    a_wf_pskl Θ P.

Inductive a_guarded : aenv -> ptyp -> Prop :=
| a_guarded__ptyp : forall Θ A, a_wf_ptyp Θ A -> a_guarded Θ A.

Inductive a_ty_mode_compat : mode -> btyp -> Prop :=
| a_ty_mode_compat__any : forall m B, a_ty_mode_compat m B.

Inductive a_sk_mode_compat : mode -> bskl -> Prop :=
| a_sk_mode_compat__any : forall m Q, a_sk_mode_compat m Q.

Inductive a_sub_mode : Set :=
| a_sub_mode_ty : a_sub_mode
| a_sub_mode_sk : a_sub_mode.

Inductive a_non_flex_poly : aenv -> ptyp -> Prop :=
| a_non_flex_poly__ptyp : forall Θ A, a_wf_ptyp Θ A -> a_non_flex_poly Θ A.

Inductive a_non_flex : aenv -> ptyp -> Prop :=
| a_non_flex__ptyp : forall Θ A, a_wf_ptyp Θ A -> a_non_flex Θ A.

Inductive a_guess_mono : aenv -> pskl -> aenv -> ptyp -> Prop :=
| a_guess_mono__plain : forall Θ A,
    a_guess_mono Θ (ptyp_to_pskl A) nil A.

(** Pre-subtyping [⊢_M presub P Q [P']] and pre-join [prejoin P Q [P']]
    (paper algorithmic.tex).  Both operate on (algorithmic) skeletons
    [bskl] — the sort carrying ghosts [□]/[⫯] and the ∀; flex-mono
    variables [α̂] are [bskl_var_f] bound as [abind_flex_mono] in [Θ].

    Following the latest paper, overlapping rules are permitted (they
    agree on overlaps), so the hole rules use a plain [guarded] side
    condition.  The [(□,□)] presub case and the [(□,Q)] / [(P,□)]
    prejoin cases are the recently-added missing cases. *)
Inductive a_pre_sub : aenv -> mode -> bskl -> bskl -> bskl -> Prop :=
| a_pre_sub__hole_hole : forall Θ m,
    a_pre_sub Θ m bskl_hole bskl_hole bskl_hole
| a_pre_sub__unit : forall Θ m Q,
    a_pre_sub Θ m bskl_unit Q bskl_unit
| a_pre_sub__var : forall Θ m X Q,
    binds X abind_tvar Θ ->
    a_pre_sub Θ m (bskl_var_f X) Q (bskl_var_f X)
| a_pre_sub__hole_l : forall Θ m Q,
    guarded_bskl Q ->
    a_pre_sub Θ m bskl_hole Q Q
| a_pre_sub__hole_r : forall Θ m P,
    guarded_bskl P ->
    a_pre_sub Θ m P bskl_hole P
| a_pre_sub__guarded : forall Θ m P Q P',
    guarded_bskl P ->
    guarded_bskl Q ->
    (m = mode_ti \/ m = mode_tc) ->
    a_pre_join Θ P Q P' ->
    a_pre_sub Θ m P Q P'
| a_pre_sub__flex_mono_fn : forall Θ m α Q,
    binds α abind_flex_mono Θ ->
    guarded_bskl Q ->
    a_pre_sub Θ (mode_fn m) (bskl_var_f α) Q (bskl_var_f α)
| a_pre_sub__all_l : forall L Θ m P Q P',
    (forall X, X `notin` L ->
       a_pre_sub Θ m (open_bskl_wrt_bskl P (bskl_var_f X)) Q P') ->
    a_pre_sub Θ m (bskl_all_syn P) Q (bskl_all_syn P')
| a_pre_sub__all_r : forall L Θ m P Q P',
    (forall X, X `notin` L ->
       a_pre_sub Θ m P (open_bskl_wrt_bskl Q (bskl_var_f X)) P') ->
    a_pre_sub Θ m P (bskl_all_syn Q) P'
| a_pre_sub__tophole_l : forall Θ m P Q P',
    a_pre_sub Θ m P Q P' ->
    a_pre_sub Θ m (bskl_tophole P) Q P'
| a_pre_sub__tophole_r : forall Θ m P Q P',
    a_pre_sub Θ m P Q P' ->
    a_pre_sub Θ m P (bskl_tophole Q) P'
| a_pre_sub__arrow : forall Θ m P1 P2 Q1 Q2 P1' P2',
    a_pre_join Θ P1 Q1 P1' ->
    a_pre_sub Θ m P2 Q2 P2' ->
    a_pre_sub Θ (mode_fn m) (bskl_arrow P1 P2) (bskl_arrow Q1 Q2) (bskl_arrow P1' P2')

with a_pre_join : aenv -> bskl -> bskl -> bskl -> Prop :=
| a_pre_join__hole_l : forall Θ Q,
    a_pre_join Θ bskl_hole Q Q
| a_pre_join__hole_r : forall Θ P,
    a_pre_join Θ P bskl_hole P
| a_pre_join__unit : forall Θ Q,
    a_pre_join Θ bskl_unit Q bskl_unit
| a_pre_join__var : forall Θ X Q,
    binds X abind_tvar Θ ->
    a_pre_join Θ (bskl_var_f X) Q (bskl_var_f X)
| a_pre_join__flex_mono_l : forall Θ α Q,
    binds α abind_flex_mono Θ ->
    a_pre_join Θ (bskl_var_f α) Q (bskl_var_f α)
| a_pre_join__flex_mono_r : forall Θ α P,
    binds α abind_flex_mono Θ ->
    a_pre_join Θ P (bskl_var_f α) P
| a_pre_join__all_both : forall L Θ P Q P',
    (forall X, X `notin` L ->
       a_pre_join Θ (open_bskl_wrt_bskl P (bskl_var_f X))
                  (open_bskl_wrt_bskl Q (bskl_var_f X)) P') ->
    a_pre_join Θ (bskl_all_syn P) (bskl_all_syn Q) (bskl_all_syn P')
| a_pre_join__tophole_both : forall Θ P Q P',
    a_pre_join Θ P Q P' ->
    a_pre_join Θ (bskl_tophole P) (bskl_tophole Q) (bskl_tophole P')
| a_pre_join__tophole_l_all : forall L Θ P Q P',
    (forall X, X `notin` L ->
       a_pre_join Θ (bskl_tophole P) (open_bskl_wrt_bskl Q (bskl_var_f X)) P') ->
    a_pre_join Θ (bskl_tophole P) (bskl_all_syn Q) (bskl_all_syn P')
| a_pre_join__tophole_l_guarded : forall Θ P Q P',
    guarded_bskl Q ->
    a_pre_join Θ P Q P' ->
    a_pre_join Θ (bskl_tophole P) Q P'
| a_pre_join__all_l_tophole : forall L Θ P Q P',
    (forall X, X `notin` L ->
       a_pre_join Θ (open_bskl_wrt_bskl P (bskl_var_f X)) (bskl_tophole Q) P') ->
    a_pre_join Θ (bskl_all_syn P) (bskl_tophole Q) (bskl_all_syn P')
| a_pre_join__guarded_r_tophole : forall Θ P Q P',
    guarded_bskl P ->
    a_pre_join Θ P Q P' ->
    a_pre_join Θ P (bskl_tophole Q) P'
| a_pre_join__arrow : forall Θ P1 P2 Q1 Q2 P1' P2',
    a_pre_join Θ P1 Q1 P1' ->
    a_pre_join Θ P2 Q2 P2' ->
    a_pre_join Θ (bskl_arrow P1 P2) (bskl_arrow Q1 Q2) (bskl_arrow P1' P2').

Inductive a_unify : aenv -> btyp -> btyp -> btyp -> aenv -> Prop :=
| a_unify__refl : forall Θ B,
    a_unify Θ B B B Θ.

Inductive a_assign : aenv -> aenv -> ptyp -> ptyp -> aenv -> Prop :=
| a_assign__refl : forall Θ A,
    a_assign Θ nil A A Θ.

Inductive a_consis : aenv -> utyp -> btyp -> aenv -> Prop :=
| a_consis__decl : forall Θ C B,
    a_consis Θ C B Θ.

Inductive a_ajoin : aenv -> bskl -> bskl -> bskl -> aenv -> Prop :=
| a_ajoin__refl : forall Θ Q,
    a_ajoin Θ Q Q Q Θ.

Inductive a_meta_subst : aenv -> ptyp -> ptyp -> Prop :=
| a_meta_subst__nil : forall A, a_meta_subst nil A A.

Inductive a_broom : a_sub_mode -> mode -> pskl -> aenv -> btyp -> btyp -> aenv -> Prop :=
| a_broom__sub : forall NM m P0 Θ B,
    a_broom NM m P0 Θ B B Θ.

Inductive a_sub : a_sub_mode -> mode -> pskl -> aenv -> btyp -> btyp -> aenv -> Prop :=
| a_sub__refl : forall NM m P0 Θ B,
    a_sub NM m P0 Θ B B Θ.

Inductive a_split : aenv -> btyp -> btyp -> btyp -> aenv -> Prop :=
| a_split__arrow : forall Θ B1 B2,
    a_split Θ (btyp_arrow B1 B2) B1 B2 Θ.

(* Algorithmic type inference [Θ ⊢[m;P0] e ⦂ B ⊣ Θ'] and skeleton
   inference [Θ ⊢[m;P0] e ⇨ Q ⊣ Θ'] (paper algorithmic.tex
   fig:alg-type-inference / fig:alg-skeleton-inference, latest draft).

   First-pass sync with the latest paper rules: the rule structure and the
   recent paper changes are reflected —
     - [Freeze] / [AbsAnno] / [AbsAnnoCheck] consistency premises use the
       (renamed) [a_consis] judgment, not [a_unify];
     - [Abs] / [AbsAnno] carry [M ≠ TC];
     - [App] checks the argument at a possibly-distinct type [A'].
   The output-context [Θ2,x:A,Ξ] discipline is encoded with an [a_suffix Ξ]
   that is dropped from the conclusion.  TODO (deferred): a dedicated
   skeleton-splitting judgment for the abstraction input skeleton (here the
   argument mono type is taken directly by [a_guess_mono] and the body's
   input skeleton is left a hole). *)
Inductive a_typing : mode -> aenv -> pskl -> exp -> btyp -> aenv -> Prop :=
| a_typing__unit : forall m Θ0 P0 A Θ1,
    a_sub a_sub_mode_ty m P0 Θ0 btyp_unit A Θ1 ->
    a_typing m Θ0 P0 exp_unit A Θ1
| a_typing__var : forall m Θ0 P0 x A B Θ1,
    binds x (abind_var_typ A) Θ0 ->
    a_sub a_sub_mode_ty m P0 Θ0 (ptyp_to_btyp_syn A) B Θ1 ->
    a_typing m Θ0 P0 (exp_var_f x) B Θ1
| a_typing__anno : forall m Θ0 P0 e A B Θ1 Θ2,
    a_typing mode_tc Θ0 (ptyp_to_pskl A) e (ptyp_to_btyp_inh A) Θ1 ->
    a_sub a_sub_mode_ty m P0 Θ1 (ptyp_to_btyp_syn A) B Θ2 ->
    a_typing m Θ0 P0 (exp_anno e A) B Θ2
| a_typing__freeze : forall Θ0 P0 e A B Θ1 Θ2,
    a_typing mode_ti Θ0 pskl_hole e B Θ1 ->
    a_consis Θ1 (btyp_to_utyp_syn B) A Θ2 ->
    a_typing mode_tc Θ0 P0 (exp_freeze e) A Θ2
| a_typing__abs : forall L m Θ0 Θ2 P0 αs A e B Ξ,
    m <> mode_tc ->
    a_guess_mono Θ0 P0 αs A ->
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       a_typing (decr_mode m) ((x ~ abind_var_typ A) ++ αs ++ Θ0) pskl_hole
         (open_exp_wrt_exp e (exp_var_f x)) B
         (Ξ ++ (x ~ abind_var_typ A) ++ Θ2)) ->
    a_typing m Θ0 P0 (exp_abs e) (btyp_arrow (ptyp_to_btyp_inh A) B) (Ξ ++ Θ2)
| a_typing__abs_anno : forall L m Θ0 Θ1 Θ2 P0 A e B Ξ,
    m <> mode_tc ->
    a_consis Θ0 (ptyp_to_utyp_syn A) (ptyp_to_btyp_inh A) Θ1 ->
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       a_typing (decr_mode m) ((x ~ abind_var_typ A) ++ Θ1) pskl_hole
         (open_exp_wrt_exp e (exp_var_f x)) B
         (Ξ ++ (x ~ abind_var_typ A) ++ Θ2)) ->
    a_typing m Θ0 P0 (exp_abs_anno A e) (btyp_arrow (ptyp_to_btyp_inh A) B) (Ξ ++ Θ2)
| a_typing__abs_check : forall L Θ0 Θ1 A e B Ξ,
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       a_typing mode_tc ((x ~ abind_var_typ A) ++ Θ0) pskl_hole
         (open_exp_wrt_exp e (exp_var_f x)) B
         (Ξ ++ (x ~ abind_var_typ A) ++ Θ1)) ->
    a_typing mode_tc Θ0 pskl_hole (exp_abs e)
      (btyp_arrow (ptyp_to_btyp_inh A) B) (Ξ ++ Θ1)
| a_typing__abs_anno_check : forall L Θ0 Θ1 Θ2 A e B Ξ,
    a_consis Θ0 (ptyp_to_utyp_syn A) (ptyp_to_btyp_inh A) Θ1 ->
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       a_typing mode_tc ((x ~ abind_var_typ A) ++ Θ1) pskl_hole
         (open_exp_wrt_exp e (exp_var_f x)) B
         (Ξ ++ (x ~ abind_var_typ A) ++ Θ2)) ->
    a_typing mode_tc Θ0 pskl_hole (exp_abs_anno A e)
      (btyp_arrow (ptyp_to_btyp_inh A) B) (Ξ ++ Θ2)
| a_typing__app : forall m Θ0 Θ1 Θ2 Θ3 P Q A A' B e1 e2,
    a_pat mode_tc Θ0 pskl_hole e2 (pskl_to_bskl_syn P) Θ1 ->
    a_typing (mode_fn m) Θ1 (pskl_arrow P Q) e1 (btyp_arrow A B) Θ2 ->
    (* the argument is re-checked, possibly at a distinct type [A'] *)
    a_typing mode_tc Θ2 (ptyp_to_pskl (btyp_to_ptyp A)) e2 A' Θ3 ->
    a_typing m Θ0 Q (exp_app e1 e2) B Θ3

with a_pat : mode -> aenv -> pskl -> exp -> bskl -> aenv -> Prop :=
(* TODO (deferred): the base cases should thread [Θ] through a
   skeleton-mode subtyping ([atypsub SK]); the mechanization currently lacks
   a skeleton-typed [a_sub] with context output, so they pass [Θ] through. *)
| a_pat__unit : forall m Θ0 P0,
    a_pat m Θ0 P0 exp_unit bskl_unit Θ0
| a_pat__var : forall m Θ0 P0 x P,
    binds x (abind_var_typ P) Θ0 ->
    a_pat m Θ0 P0 (exp_var_f x) (pskl_to_bskl_syn (ptyp_to_pskl P)) Θ0
| a_pat__anno : forall m Θ0 P0 e A,
    a_pat m Θ0 P0 (exp_anno e A) (pskl_to_bskl_syn (ptyp_to_pskl A)) Θ0
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
      (bskl_arrow (pskl_to_bskl_inh (ptyp_to_pskl P)) Q) (Ξ ++ Θ2)
| a_pat__abs_check : forall L Θ0 Θ1 e Q Ξ,
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       a_pat mode_tc ((x ~ abind_var_typ ptyp_unit) ++ Θ0) pskl_hole
         (open_exp_wrt_exp e (exp_var_f x)) Q
         (Ξ ++ (x ~ abind_var_typ ptyp_unit) ++ Θ1)) ->
    a_pat mode_tc Θ0 pskl_hole (exp_abs e)
      (bskl_tophole (bskl_arrow bskl_hole Q)) (Ξ ++ Θ1)
| a_pat__abs_anno : forall L m Θ0 Θ2 A e Q Ξ,
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       a_pat (decr_mode m) ((x ~ abind_var_typ A) ++ Θ0) pskl_hole
         (open_exp_wrt_exp e (exp_var_f x)) Q
         (Ξ ++ (x ~ abind_var_typ A) ++ Θ2)) ->
    a_pat m Θ0 (ptyp_to_pskl A) (exp_abs_anno A e)
      (bskl_arrow (pskl_to_bskl_inh (ptyp_to_pskl A)) Q) (Ξ ++ Θ2)
| a_pat__abs_anno_check : forall L Θ0 Θ1 A e Q Ξ,
    a_suffix Ξ ->
    (forall x, x `notin` L ->
       a_pat mode_tc ((x ~ abind_var_typ A) ++ Θ0) pskl_hole
         (open_exp_wrt_exp e (exp_var_f x)) Q
         (Ξ ++ (x ~ abind_var_typ A) ++ Θ1)) ->
    a_pat mode_tc Θ0 pskl_hole (exp_abs_anno A e)
      (bskl_tophole (bskl_arrow (pskl_to_bskl_inh (ptyp_to_pskl A)) Q)) (Ξ ++ Θ1)
| a_pat__app : forall m Θ0 Θ1 Θ2 Θ3 P Q A A2 B Sres e1 e2,
    a_pat mode_tc Θ0 pskl_hole e2 (pskl_to_bskl_syn P) Θ1 ->
    a_typing (mode_fn m) Θ1 (pskl_arrow P Q) e1 (btyp_arrow A B) Θ2 ->
    a_pat mode_tc Θ2 (ptyp_to_pskl (btyp_to_ptyp A)) e2 Sres Θ3 ->
    a_pat m Θ0 Q (exp_app e1 e2) (bskl_arrow A2 Sres) Θ3.
