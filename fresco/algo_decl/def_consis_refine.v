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

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.

Set Implicit Arguments.

(* the judgement notations below live in this scope; `Open Scope` is not
   transitive through `Require Import`, so the DECLARING file must open it *)
Open Scope fresco_ad_scope.

(* Same level discipline as decl/def_rules.v: middle slots of ⨟-judgments at
   level 74. *)
Reserved Notation "{{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad"
  (at level 0, Θ at level 74, R at level 74, Q at level 74,
   format "'{{'  Ψ  ⨟  Θ  ⊢ˢ  R  ∼  Q  '}}ad'").
Reserved Notation "{{ Θ ⨟ Δ ⊢ᵣ Q ⊳ P }}ad"
  (at level 0, Δ at level 74, Q at level 74, P at level 74,
   format "'{{'  Θ  ⨟  Δ  ⊢ᵣ  Q  ⊳  P  '}}ad'").
Reserved Notation "{{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ Q }}ad"
  (at level 0, Δ at level 74, P at level 74, Q at level 74,
   format "'{{'  Θ  ⨟  Δ  ⊢ᵣₚ  P  ⊳  Q  '}}ad'").
(* ⚙ THE JOIN: consistency AND its refinement presupposition, as one
   relation.  [ᵣ] is the refinement subscript, as in [⊢ᵣₚ] — the twin of
   [{{ Ψ ⨟ Γ ⊢ˢ R ∼ᵣ Q }}d] (decl/def_rules.v). *)
Reserved Notation "{{ Ψ ⨟ Θ ⊢ˢ R ∼ᵣ Q }}ad"
  (at level 0, Θ at level 74, R at level 74, Q at level 74,
   format "'{{'  Ψ  ⨟  Θ  ⊢ˢ  R  ∼ᵣ  Q  '}}ad'").

(** Monotype embeddings used by the definition-lookup rules. *)
Definition ptyp_to_bskl_syn (A : ptyp) : bskl :=
  pskl_to_bskl_syn (ptyp_to_pskl A).
Definition ptyp_to_uskl_syn (A : ptyp) : uskl :=
  bskl_to_uskl (ptyp_to_bskl_syn A).

(* [a_binds_tvar] now lives in algo/def_rules.v (shared with a_wf_ptyp). *)

(* [a_wf_pskl] now lives in algo/def_rules.v (needed by ForallL's
   disciplined instantiation premise). *)

(* ===================================================================== *)
(*  Skeleton consistency over Θ  (decl [Ψ ⨟ Γ ⊢ₛ R ∼ Q] + FlexL/FlexR)    *)
(* ===================================================================== *)

Inductive ad_pat_consis : atoms -> aenv -> uskl -> bskl -> Prop :=
| ad_pat_consis__unit : forall Ψ Θ,
    Ψ [=] empty ->
    {{ Ψ ⨟ Θ ⊢ˢ uskl_unit ∼ bskl_unit }}ad
| ad_pat_consis__var : forall Ψ Θ α,
    Ψ [=] empty ->
    a_binds_tvar α Θ ->
    {{ Ψ ⨟ Θ ⊢ˢ (uskl_var_f α) ∼ (bskl_var_f α) }}ad
| ad_pat_consis__arrow : forall Ψ Ψ1 Ψ2 Θ R1 R2 Q1 Q2,
    {{ Ψ1 ⨟ Θ ⊢ˢ R1 ∼ Q1 }}ad ->
    {{ Ψ2 ⨟ Θ ⊢ˢ R2 ∼ Q2 }}ad ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    {{ Ψ ⨟ Θ ⊢ˢ (uskl_arrow R1 R2) ∼ (bskl_arrow Q1 Q2) }}ad
| ad_pat_consis__forall_inh_tagged : forall L Ψ Ψ0 Θ ε R Q,
    (forall α, α `notin` L ->
       {{ Ψ0 ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ˢ
         (open_uskl_wrt_uskl R (uskl_var_f α)) ∼
         (open_bskl_wrt_bskl Q (bskl_var_f α)) }}ad) ->
    Ψ [=] add ε Ψ0 ->
    {{ Ψ ⨟ Θ ⊢ˢ (uskl_all_tag ε R) ∼ (bskl_all_inh Q) }}ad
| ad_pat_consis__forall_inh_untagged : forall L Ψ Θ R Q,
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ˢ
         (open_uskl_wrt_uskl R (uskl_var_f α)) ∼
         (open_bskl_wrt_bskl Q (bskl_var_f α)) }}ad) ->
    {{ Ψ ⨟ Θ ⊢ˢ (uskl_all_syn R) ∼ (bskl_all_inh Q) }}ad
| ad_pat_consis__forall_syn_tagged : forall L Ψ Θ ε R Q,
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ˢ
         (open_uskl_wrt_uskl R (uskl_var_f α)) ∼
         (open_bskl_wrt_bskl Q (bskl_var_f α)) }}ad) ->
    {{ Ψ ⨟ Θ ⊢ˢ (uskl_all_tag ε R) ∼ (bskl_all_syn Q) }}ad
| ad_pat_consis__forall_syn : forall L Ψ Θ R Q,
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ˢ
         (open_uskl_wrt_uskl R (uskl_var_f α)) ∼
         (open_bskl_wrt_bskl Q (bskl_var_f α)) }}ad) ->
    {{ Ψ ⨟ Θ ⊢ˢ (uskl_all_syn R) ∼ (bskl_all_syn Q) }}ad
| ad_pat_consis__ghostg : forall Ψ Θ,
    Ψ [=] empty ->
    {{ Ψ ⨟ Θ ⊢ˢ uskl_holeg ∼ bskl_hole }}ad
| ad_pat_consis__topholeg : forall Ψ Θ R Q,
    {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ (uskl_topholeg R) ∼ (bskl_tophole Q) }}ad
| ad_pat_consis__hole : forall Ψ Θ P,
    Ψ [=] empty ->
    {{ Θ ⨟ empty ⊢ₚₛ P }}a ->
    {{ Ψ ⨟ Θ ⊢ˢ uskl_hole ∼ (pskl_to_bskl_inh P) }}ad
| ad_pat_consis__tophole : forall Ψ Θ R Q,
    {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ (uskl_tophole R) ∼ (bskl_tophole Q) }}ad
| ad_pat_consis__tophole_inh : forall L Ψ Θ R Q,
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ˢ
         (uskl_tophole R) ∼ (open_bskl_wrt_bskl Q (bskl_var_f α)) }}ad) ->
    {{ Ψ ⨟ Θ ⊢ˢ (uskl_tophole R) ∼ (bskl_all_inh Q) }}ad
| ad_pat_consis__tophole_drop : forall Ψ Θ R Q,
    {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ (uskl_tophole R) ∼ Q }}ad
(* — new lookup rules (paper eqlab FlexL / FlexR) — *)
| ad_pat_consis__flex_l : forall Ψ Θ α τ Q,
    binds α (abind_flex_mono_def τ) Θ ->
    {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn τ) ∼ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ (uskl_var_f α) ∼ Q }}ad
| ad_pat_consis__flex_r : forall Ψ Θ α τ R,
    binds α (abind_flex_mono_def τ) Θ ->
    {{ Ψ ⨟ Θ ⊢ˢ R ∼ (ptyp_to_bskl_syn τ) }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ R ∼ (bskl_var_f α) }}ad
where "{{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad" := (ad_pat_consis Ψ Θ R Q) : fresco_ad_scope.

(* ===================================================================== *)
(*  Skeleton refinement over Θ, coloured  (decl [{{ Γ ⨟ Δ ⊢ᵣ Q ⊳ P }}d] + flex) *)
(* ===================================================================== *)

(* The declarative refinement rules read over Θ (full-algo-spec.tex,
   fig:declarative-in-algo-context), plus the two flexible lookups.  Like the
   declarative copy, it carries no scoping premises: well-formedness of both
   sides is the paper's presupposition, carried as a hypothesis by the lemmas
   that need it. *)

Inductive ad_refine_syn : aenv -> atoms -> bskl -> bskl -> Prop :=
| ad_refine_syn__unit : forall Θ Δ,
    {{ Θ ⨟ Δ ⊢ᵣ bskl_unit ⊳ bskl_unit }}ad
| ad_refine_syn__var : forall Θ Δ α,
    {{ Θ ⨟ Δ ⊢ᵣ (bskl_var_f α) ⊳ (bskl_var_f α) }}ad
| ad_refine_syn__arrow : forall Θ Δ Q1 Q2 P1 P2,
    {{ Θ ⨟ Δ ⊢ᵣ Q1 ⊳ P1 }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣ Q2 ⊳ P2 }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣ (bskl_arrow Q1 Q2) ⊳ (bskl_arrow P1 P2) }}ad
| ad_refine_syn__all : forall L Θ Δ Q P,
    (forall α, α `notin` L ->
       {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α Δ) ⊢ᵣ
         (open_bskl_wrt_bskl Q (bskl_var_f α)) ⊳
         (open_bskl_wrt_bskl P (bskl_var_f α)) }}ad) ->
    {{ Θ ⨟ Δ ⊢ᵣ (bskl_all_inh Q) ⊳ (bskl_all_inh P) }}ad
| ad_refine_syn__hole : forall Θ Δ P,
    Δ ∩ ftvar_in_pskl P [=] empty ->
    {{ Θ ⨟ Δ ⊢ᵣ bskl_hole ⊳ (pskl_to_bskl_syn P) }}ad
| ad_refine_syn__tophole_remove : forall Θ Δ Q P,
    {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ P }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣ (bskl_tophole Q) ⊳ P }}ad
| ad_refine_syn__tophole_fill : forall L Θ Δ Q P,
    (forall α, α `notin` L ->
       {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ᵣ
         (bskl_tophole Q) ⊳ (open_bskl_wrt_bskl P (bskl_var_f α)) }}ad) ->
    {{ Θ ⨟ Δ ⊢ᵣ (bskl_tophole Q) ⊳ (bskl_all_syn P) }}ad
| ad_refine_syn__tophole_keep : forall Θ Δ Q P,
    {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ P }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣ (bskl_tophole Q) ⊳ (bskl_tophole P) }}ad
(* — new lookup rules (paper fig:declarative-in-algo-context, refinement) — *)
| ad_refine_syn__flex_l : forall Θ Δ α τ Q,
    binds α (abind_flex_mono_def τ) Θ ->
    {{ Θ ⨟ Δ ⊢ᵣ (ptyp_to_bskl_syn τ) ⊳ Q }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣ (bskl_var_f α) ⊳ Q }}ad
| ad_refine_syn__flex_r : forall Θ Δ α τ P,
    binds α (abind_flex_mono_def τ) Θ ->
    {{ Θ ⨟ Δ ⊢ᵣ P ⊳ (ptyp_to_bskl_syn τ) }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣ P ⊳ (bskl_var_f α) }}ad
where "{{ Θ ⨟ Δ ⊢ᵣ Q ⊳ P }}ad" := (ad_refine_syn Θ Δ Q P) : fresco_ad_scope.

(* ===================================================================== *)
(*  Skeleton refinement over Θ, uncoloured  (decl [Γ ⊢ P ⊳ Q], the paper's *)
(*  colour-ignoring reading of the refinement rules, + flex lookups)       *)
(* ===================================================================== *)

Inductive ad_refine_pskl : aenv -> atoms -> pskl -> pskl -> Prop :=
| ad_refine_pskl__unit : forall Θ Δ,
    {{ Θ ⨟ Δ ⊢ᵣₚ pskl_unit ⊳ pskl_unit }}ad
| ad_refine_pskl__var : forall Θ Δ α,
    {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_var_f α) ⊳ (pskl_var_f α) }}ad
| ad_refine_pskl__arrow : forall Θ Δ P1 P2 Q1 Q2,
    {{ Θ ⨟ Δ ⊢ᵣₚ P1 ⊳ Q1 }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣₚ P2 ⊳ Q2 }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_arrow P1 P2) ⊳ (pskl_arrow Q1 Q2) }}ad
| ad_refine_pskl__all : forall L Θ Δ P Q,
    (forall α, α `notin` L ->
       {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α Δ) ⊢ᵣₚ
         (open_pskl_wrt_pskl P (pskl_var_f α)) ⊳
         (open_pskl_wrt_pskl Q (pskl_var_f α)) }}ad) ->
    {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_all_syn P) ⊳ (pskl_all_syn Q) }}ad
| ad_refine_pskl__hole : forall Θ Δ Q,
    Δ ∩ ftvar_in_pskl Q [=] empty ->
    {{ Θ ⨟ Δ ⊢ᵣₚ pskl_hole ⊳ Q }}ad
| ad_refine_pskl__tophole_remove : forall Θ Δ P Q,
    {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ Q }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_tophole P) ⊳ Q }}ad
| ad_refine_pskl__tophole_fill : forall L Θ Δ P Q,
    (forall α, α `notin` L ->
       {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ᵣₚ
         (pskl_tophole P) ⊳ (open_pskl_wrt_pskl Q (pskl_var_f α)) }}ad) ->
    {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_tophole P) ⊳ (pskl_all_syn Q) }}ad
| ad_refine_pskl__tophole_keep : forall Θ Δ P Q,
    {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ Q }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_tophole P) ⊳ (pskl_tophole Q) }}ad
| ad_refine_pskl__flex_l : forall Θ Δ α τ Q,
    binds α (abind_flex_mono_def τ) Θ ->
    {{ Θ ⨟ Δ ⊢ᵣₚ (ptyp_to_pskl τ) ⊳ Q }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_var_f α) ⊳ Q }}ad
| ad_refine_pskl__flex_r : forall Θ Δ α τ P,
    binds α (abind_flex_mono_def τ) Θ ->
    {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ (ptyp_to_pskl τ) }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ (pskl_var_f α) }}ad
where "{{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ Q }}ad" := (ad_refine_pskl Θ Δ P Q) : fresco_ad_scope.

(* ===================================================================== *)
(*  THE JOIN  [{{ Ψ ⨟ Θ ⊢ˢ R ∼ᵣ Q }}ad]                                   *)
(*                                                                        *)
(*  Consistency TOGETHER WITH its refinement presupposition — the [ad]    *)
(*  twin of [d_consis_join] (decl/def_rules.v).  The two never travel     *)
(*  apart: every consistency premise of [ad_pat_sub] / [ad_pat_sub_fuel]  *)
(*  is a JOIN, i.e. it also asserts that the subject refines to the       *)
(*  counterpart it is consistent with.                                    *)
(*                                                                        *)
(*  ⭐ [paper-gap] The refinement half is the paper's PRESUPPOSITION of    *)
(*  skeleton consistency (declarative.tex:2074) and, at a subtyping       *)
(*  LEAF, the third solution condition of the augmented                   *)
(*  thm:complete-consistency (consistency-proofs.tex:2230-2242).  It is   *)
(*  NOT derivable from the consistency half — the capture configuration   *)
(*  [∀X.◇ ∼ ∀ˢX.X] satisfies one and refutes the other                    *)
(*  (cex/cex_ad_pat_join_not_leaf_valid.v).                               *)
(*                                                                        *)
(*  ⚙ Δ is [empty] BY CONSTRUCTION: the presupposition is always stated   *)
(*  at the empty ∀-scope, so the combined relation does not expose it.    *)
(* ===================================================================== *)

Definition ad_consis_join (Ψ : atoms) (Θ : aenv) (R : uskl) (Q : bskl) : Prop :=
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad /\
  {{ Θ ⨟ empty ⊢ᵣₚ ⌊ R ⌋ˢ ⊳ (bskl_to_pskl Q) }}ad.

Notation "{{ Ψ ⨟ Θ ⊢ˢ R ∼ᵣ Q }}ad" := (ad_consis_join Ψ Θ R Q) : fresco_ad_scope.

(** The two projections and the pairing, so consumers never unfold. *)
Lemma ad_consis_join_consis : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ᵣ Q }}ad -> {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad.
Proof. intros * [H _]; exact H. Qed.

Lemma ad_consis_join_refine : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ᵣ Q }}ad ->
  {{ Θ ⨟ empty ⊢ᵣₚ ⌊ R ⌋ˢ ⊳ (bskl_to_pskl Q) }}ad.
Proof. intros * [_ H]; exact H. Qed.

Lemma ad_consis_join_intro : forall Ψ Θ R Q,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
  {{ Θ ⨟ empty ⊢ᵣₚ ⌊ R ⌋ˢ ⊳ (bskl_to_pskl Q) }}ad ->
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ᵣ Q }}ad.
Proof. intros; split; assumption. Qed.

(** ⚙ THE [inh] FORM, for the TY rows (Check), whose counterpart is a
    painted [inh{B}]: [⌊inh{B}⌋ = B] is a RETRACTION, not a conversion, so
    the refinement half needs one rewrite.  Both directions, so a Check row
    can be built from and destructed to the [B]-shaped premise. *)
Lemma ad_consis_join_inh : forall Ψ Θ R B,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ᵣ (pskl_to_bskl_inh B) }}ad <->
  ({{ Ψ ⨟ Θ ⊢ˢ R ∼ (pskl_to_bskl_inh B) }}ad /\
   {{ Θ ⨟ empty ⊢ᵣₚ ⌊ R ⌋ˢ ⊳ B }}ad).
Proof.
  intros. unfold ad_consis_join.
  rewrite bskl_to_pskl_pskl_to_bskl_inh. reflexivity.
Qed.

Lemma ad_consis_join_inh_intro : forall Ψ Θ R B,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ (pskl_to_bskl_inh B) }}ad ->
  {{ Θ ⨟ empty ⊢ᵣₚ ⌊ R ⌋ˢ ⊳ B }}ad ->
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ᵣ (pskl_to_bskl_inh B) }}ad.
Proof. intros. apply ad_consis_join_inh. split; assumption. Qed.

Lemma ad_consis_join_inh_refine : forall Ψ Θ R B,
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ᵣ (pskl_to_bskl_inh B) }}ad ->
  {{ Θ ⨟ empty ⊢ᵣₚ ⌊ R ⌋ˢ ⊳ B }}ad.
Proof. intros * H. apply ad_consis_join_inh in H. destruct H; assumption. Qed.

#[export] Hint Resolve ad_consis_join_intro ad_consis_join_inh_intro : fresco.
#[export] Hint Unfold ad_consis_join : fresco.
