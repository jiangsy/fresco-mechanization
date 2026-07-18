(** Declarative judgments in ALGORITHMIC contexts (paper
    app:decl-in-algo-context).

    "All declarative judgements … are naturally extended to algorithmic
    contexts": the rules are the declarative ones with [Γ] replaced by [Θ],
    plus lookup rules that retrieve flexible-variable definitions from [Θ]
    (FlexL/FlexR for consistency, FlexMono for subtyping, two rules for
    refinement).  This file provides the consistency/refinement layer used
    by the soundness lemmas of appendix B (consistency-proofs.tex); the
    subtyping/typing layer follows with appendix C/D.

    Naming: [ad_*] = the [d_*] judgment over an [aenv].  Notations mirror
    the declarative ones (decl/notations.v legend) with an [ᵃ] mark on the
    turnstile. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.

Set Implicit Arguments.

(* Same level discipline as decl/def_extra.v: middle slots of ⨟-judgments at
   level 74. *)
Reserved Notation "Ψ ⨟ Θ ⊨ₛᵃ R ≈ Q"
  (at level 75, Θ at level 74, R at level 74, Q at level 74, no associativity).
Reserved Notation "Θ ⨟ Δ ⊢ᵣᵃ Q ⊳ P"
  (at level 75, Δ at level 74, Q at level 74, P at level 74, no associativity).
Reserved Notation "Θ ⨟ Δ ⊢ᵣₚᵃ P ⊳ Q"
  (at level 75, Δ at level 74, P at level 74, Q at level 74, no associativity).

(** Monotype embeddings used by the definition-lookup rules. *)
Definition ptyp_to_bskl_syn (A : ptyp) : bskl :=
  pskl_to_bskl_syn (ptyp_to_pskl A).
Definition ptyp_to_uskl_syn (A : ptyp) : uskl :=
  bskl_to_uskl (ptyp_to_bskl_syn A).

(* [a_binds_tvar] now lives in algo/def_extra.v (shared with a_wf_ptyp). *)

(* [a_wf_pskl] now lives in algo/def_extra.v (needed by ForallL's
   disciplined instantiation premise). *)

(* ===================================================================== *)
(*  Skeleton consistency over Θ  (decl [Ψ ⨟ Γ ⊨ₛ S ≈ Q] + FlexL/FlexR)    *)
(* ===================================================================== *)

Inductive ad_pat_consis : atoms -> aenv -> uskl -> bskl -> Prop :=
| ad_pat_consis__unit : forall Ψ Θ,
    Ψ [=] empty ->
    Ψ ⨟ Θ ⊨ₛᵃ uskl_unit ≈ bskl_unit
| ad_pat_consis__var : forall Ψ Θ X,
    Ψ [=] empty ->
    a_binds_tvar X Θ ->
    Ψ ⨟ Θ ⊨ₛᵃ (uskl_var_f X) ≈ (bskl_var_f X)
| ad_pat_consis__arrow : forall Ψ Ψ1 Ψ2 Θ R1 R2 Q1 Q2,
    Ψ1 ⨟ Θ ⊨ₛᵃ R1 ≈ Q1 ->
    Ψ2 ⨟ Θ ⊨ₛᵃ R2 ≈ Q2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    Ψ ⨟ Θ ⊨ₛᵃ (uskl_arrow R1 R2) ≈ (bskl_arrow Q1 Q2)
| ad_pat_consis__forall_inh_tagged : forall L Ψ Ψ0 Θ ε R Q,
    (forall X, X `notin` L ->
       Ψ0 ⨟ ((X ~ abind_tvar) ++ Θ) ⊨ₛᵃ
         (open_uskl_wrt_uskl R (uskl_var_f X)) ≈
         (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    Ψ [=] add ε Ψ0 ->
    Ψ ⨟ Θ ⊨ₛᵃ (uskl_all_etag ε R) ≈ (bskl_all_inh Q)
| ad_pat_consis__forall_inh_untagged : forall L Ψ Θ R Q,
    (forall X, X `notin` L ->
       Ψ ⨟ ((X ~ abind_tvar) ++ Θ) ⊨ₛᵃ
         (open_uskl_wrt_uskl R (uskl_var_f X)) ≈
         (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    Ψ ⨟ Θ ⊨ₛᵃ (uskl_all_syn R) ≈ (bskl_all_inh Q)
| ad_pat_consis__forall_syn_tagged : forall L Ψ Θ ε R Q,
    (forall X, X `notin` L ->
       Ψ ⨟ ((X ~ abind_tvar) ++ Θ) ⊨ₛᵃ
         (open_uskl_wrt_uskl R (uskl_var_f X)) ≈
         (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    Ψ ⨟ Θ ⊨ₛᵃ (uskl_all_etag ε R) ≈ (bskl_all_syn Q)
| ad_pat_consis__forall_syn : forall L Ψ Θ R Q,
    (forall X, X `notin` L ->
       Ψ ⨟ ((X ~ abind_tvar) ++ Θ) ⊨ₛᵃ
         (open_uskl_wrt_uskl R (uskl_var_f X)) ≈
         (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    Ψ ⨟ Θ ⊨ₛᵃ (uskl_all_syn R) ≈ (bskl_all_syn Q)
| ad_pat_consis__ghostg : forall Ψ Θ,
    Ψ [=] empty ->
    Ψ ⨟ Θ ⊨ₛᵃ uskl_holeg ≈ bskl_hole
| ad_pat_consis__topholeg : forall Ψ Θ R Q,
    Ψ ⨟ Θ ⊨ₛᵃ R ≈ Q ->
    Ψ ⨟ Θ ⊨ₛᵃ (uskl_topholeg R) ≈ (bskl_tophole Q)
| ad_pat_consis__hole : forall Ψ Θ P,
    Ψ [=] empty ->
    Θ ⨟ empty ⊢ₚₛᵃ P ->
    Ψ ⨟ Θ ⊨ₛᵃ uskl_hole ≈ (pskl_to_bskl_inh P)
| ad_pat_consis__tophole : forall Ψ Θ R Q,
    Ψ ⨟ Θ ⊨ₛᵃ R ≈ Q ->
    Ψ ⨟ Θ ⊨ₛᵃ (uskl_tophole R) ≈ (bskl_tophole Q)
| ad_pat_consis__tophole_inh : forall L Ψ Θ R Q,
    (forall X, X `notin` L ->
       Ψ ⨟ ((X ~ abind_tvar) ++ Θ) ⊨ₛᵃ
         (uskl_tophole R) ≈ (open_bskl_wrt_bskl Q (bskl_var_f X))) ->
    Ψ ⨟ Θ ⊨ₛᵃ (uskl_tophole R) ≈ (bskl_all_inh Q)
| ad_pat_consis__tophole_drop : forall Ψ Θ R Q,
    Ψ ⨟ Θ ⊨ₛᵃ R ≈ Q ->
    Ψ ⨟ Θ ⊨ₛᵃ (uskl_tophole R) ≈ Q
(* — new lookup rules (paper eqlab FlexL / FlexR) — *)
| ad_pat_consis__flex_l : forall Ψ Θ α τ Q,
    binds α (abind_flex_mono_def τ) Θ ->
    Ψ ⨟ Θ ⊨ₛᵃ (ptyp_to_uskl_syn τ) ≈ Q ->
    Ψ ⨟ Θ ⊨ₛᵃ (uskl_var_f α) ≈ Q
| ad_pat_consis__flex_r : forall Ψ Θ α τ S,
    binds α (abind_flex_mono_def τ) Θ ->
    Ψ ⨟ Θ ⊨ₛᵃ S ≈ (ptyp_to_bskl_syn τ) ->
    Ψ ⨟ Θ ⊨ₛᵃ S ≈ (bskl_var_f α)
where "Ψ ⨟ Θ ⊨ₛᵃ R ≈ Q" := (ad_pat_consis Ψ Θ R Q) : type_scope.

(* ===================================================================== *)
(*  Skeleton refinement over Θ, coloured  (decl [Γ ⨟ Δ ⊢ᵣ Q ⊳ P] + flex)  *)
(* ===================================================================== *)

Inductive ad_refine_syn : aenv -> atoms -> bskl -> bskl -> Prop :=
| ad_refine_syn__unit : forall Θ Δ,
    Θ ⨟ Δ ⊢ᵣᵃ bskl_unit ⊳ bskl_unit
| ad_refine_syn__var : forall Θ Δ X,
    X `in` Δ \/ a_binds_tvar X Θ ->
    Θ ⨟ Δ ⊢ᵣᵃ (bskl_var_f X) ⊳ (bskl_var_f X)
| ad_refine_syn__arrow : forall Θ Δ Q1 Q2 P1 P2,
    Θ ⨟ Δ ⊢ᵣᵃ Q1 ⊳ P1 ->
    Θ ⨟ Δ ⊢ᵣᵃ Q2 ⊳ P2 ->
    Θ ⨟ Δ ⊢ᵣᵃ (bskl_arrow Q1 Q2) ⊳ (bskl_arrow P1 P2)
| ad_refine_syn__all : forall L Θ Δ Q P,
    (forall X, X `notin` L ->
       Θ ⨟ (add X Δ) ⊢ᵣᵃ
         (open_bskl_wrt_bskl Q (bskl_var_f X)) ⊳
         (open_bskl_wrt_bskl P (bskl_var_f X))) ->
    Θ ⨟ Δ ⊢ᵣᵃ (bskl_all_inh Q) ⊳ (bskl_all_inh P)
| ad_refine_syn__hole : forall Θ Δ P,
    Θ ⨟ empty ⊢ₚₛᵃ P ->
    Θ ⨟ Δ ⊢ᵣᵃ bskl_hole ⊳ (pskl_to_bskl_syn P)
| ad_refine_syn__tophole_remove : forall Θ Δ Q P,
    Θ ⨟ Δ ⊢ᵣᵃ Q ⊳ P ->
    Θ ⨟ Δ ⊢ᵣᵃ (bskl_tophole Q) ⊳ P
| ad_refine_syn__tophole_fill : forall L Θ Δ Q P,
    (forall X, X `notin` L ->
       ((X ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ᵣᵃ
         (bskl_tophole Q) ⊳ (open_bskl_wrt_bskl P (bskl_var_f X))) ->
    Θ ⨟ Δ ⊢ᵣᵃ (bskl_tophole Q) ⊳ (bskl_all_syn P)
| ad_refine_syn__tophole_keep : forall Θ Δ Q P,
    guarded_bskl P ->
    Θ ⨟ Δ ⊢ᵣᵃ Q ⊳ P ->
    Θ ⨟ Δ ⊢ᵣᵃ (bskl_tophole Q) ⊳ (bskl_tophole P)
(* — new lookup rules (paper fig:declarative-in-algo-context, refinement) — *)
| ad_refine_syn__flex_l : forall Θ Δ α τ Q,
    binds α (abind_flex_mono_def τ) Θ ->
    Θ ⨟ Δ ⊢ᵣᵃ (ptyp_to_bskl_syn τ) ⊳ Q ->
    Θ ⨟ Δ ⊢ᵣᵃ (bskl_var_f α) ⊳ Q
| ad_refine_syn__flex_r : forall Θ Δ α τ P,
    binds α (abind_flex_mono_def τ) Θ ->
    Θ ⨟ Δ ⊢ᵣᵃ P ⊳ (ptyp_to_bskl_syn τ) ->
    Θ ⨟ Δ ⊢ᵣᵃ P ⊳ (bskl_var_f α)
where "Θ ⨟ Δ ⊢ᵣᵃ Q ⊳ P" := (ad_refine_syn Θ Δ Q P) : type_scope.

(* ===================================================================== *)
(*  Skeleton refinement over Θ, uncoloured  (decl [Γ ⊢ P ⊳ Q], the paper's *)
(*  colour-ignoring reading of the refinement rules, + flex lookups)       *)
(* ===================================================================== *)

Inductive ad_refine_pskl : aenv -> atoms -> pskl -> pskl -> Prop :=
| ad_refine_pskl__unit : forall Θ Δ,
    Θ ⨟ Δ ⊢ᵣₚᵃ pskl_unit ⊳ pskl_unit
| ad_refine_pskl__var : forall Θ Δ X,
    X `in` Δ \/ a_binds_tvar X Θ ->
    Θ ⨟ Δ ⊢ᵣₚᵃ (pskl_var_f X) ⊳ (pskl_var_f X)
| ad_refine_pskl__arrow : forall Θ Δ P1 P2 Q1 Q2,
    Θ ⨟ Δ ⊢ᵣₚᵃ P1 ⊳ Q1 ->
    Θ ⨟ Δ ⊢ᵣₚᵃ P2 ⊳ Q2 ->
    Θ ⨟ Δ ⊢ᵣₚᵃ (pskl_arrow P1 P2) ⊳ (pskl_arrow Q1 Q2)
| ad_refine_pskl__all : forall L Θ Δ P Q,
    (forall X, X `notin` L ->
       Θ ⨟ (add X Δ) ⊢ᵣₚᵃ
         (open_pskl_wrt_pskl P (pskl_var_f X)) ⊳
         (open_pskl_wrt_pskl Q (pskl_var_f X))) ->
    Θ ⨟ Δ ⊢ᵣₚᵃ (pskl_all_syn P) ⊳ (pskl_all_syn Q)
| ad_refine_pskl__hole : forall Θ Δ Q,
    Θ ⨟ empty ⊢ₚₛᵃ Q ->
    Θ ⨟ Δ ⊢ᵣₚᵃ pskl_hole ⊳ Q
| ad_refine_pskl__tophole_remove : forall Θ Δ P Q,
    Θ ⨟ Δ ⊢ᵣₚᵃ P ⊳ Q ->
    Θ ⨟ Δ ⊢ᵣₚᵃ (pskl_tophole P) ⊳ Q
| ad_refine_pskl__tophole_fill : forall L Θ Δ P Q,
    (forall X, X `notin` L ->
       ((X ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ᵣₚᵃ
         (pskl_tophole P) ⊳ (open_pskl_wrt_pskl Q (pskl_var_f X))) ->
    Θ ⨟ Δ ⊢ᵣₚᵃ (pskl_tophole P) ⊳ (pskl_all_syn Q)
| ad_refine_pskl__tophole_keep : forall Θ Δ P Q,
    guarded_pskl Q ->
    Θ ⨟ Δ ⊢ᵣₚᵃ P ⊳ Q ->
    Θ ⨟ Δ ⊢ᵣₚᵃ (pskl_tophole P) ⊳ (pskl_tophole Q)
| ad_refine_pskl__flex_l : forall Θ Δ α τ Q,
    binds α (abind_flex_mono_def τ) Θ ->
    Θ ⨟ Δ ⊢ᵣₚᵃ (ptyp_to_pskl τ) ⊳ Q ->
    Θ ⨟ Δ ⊢ᵣₚᵃ (pskl_var_f α) ⊳ Q
| ad_refine_pskl__flex_r : forall Θ Δ α τ P,
    binds α (abind_flex_mono_def τ) Θ ->
    Θ ⨟ Δ ⊢ᵣₚᵃ P ⊳ (ptyp_to_pskl τ) ->
    Θ ⨟ Δ ⊢ᵣₚᵃ P ⊳ (pskl_var_f α)
where "Θ ⨟ Δ ⊢ᵣₚᵃ P ⊳ Q" := (ad_refine_pskl Θ Δ P Q) : type_scope.
