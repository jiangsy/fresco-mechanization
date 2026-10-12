Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.

Set Implicit Arguments.

Open Scope fresco_ad_scope.

Reserved Notation "{{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad"
  (at level 0, Θ at level 74, R at level 74, Q at level 74,
   format "'{{'  Ψ  ⨟  Θ  ⊢ˢ  R  ∼  Q  '}}ad'").
Reserved Notation "{{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad"
  (at level 0, Δ at level 74, Q at level 74, Q' at level 74,
   format "'{{'  Θ  ⨟  Δ  ⊢ᵣ  Q  ⊳  Q'  '}}ad'").
Reserved Notation "{{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad"
  (at level 0, Δ at level 74, P at level 74, P' at level 74,
   format "'{{'  Θ  ⨟  Δ  ⊢ᵣₚ  P  ⊳  P'  '}}ad'").
Reserved Notation "{{ Ψ ⨟ Θ ⊢ˢ R ∼ᵣ Q }}ad"
  (at level 0, Θ at level 74, R at level 74, Q at level 74,
   format "'{{'  Ψ  ⨟  Θ  ⊢ˢ  R  ∼ᵣ  Q  '}}ad'").

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
    {{ Ψ ⨟ Θ ⊢ˢ uskl_dot_ghost ∼ bskl_ghost }}ad
| ad_pat_consis__dot_univ_ghost : forall Ψ Θ R Q,
    {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ (uskl_dot_univ_ghost R) ∼ (bskl_univ_ghost Q) }}ad
| ad_pat_consis__ghost : forall Ψ Θ P,
    Ψ [=] empty ->
    {{ Ψ ⨟ Θ ⊢ˢ uskl_ghost ∼ (pskl_to_bskl_inh P) }}ad
| ad_pat_consis__univ_ghost : forall Ψ Θ R Q,
    {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ (uskl_univ_ghost R) ∼ (bskl_univ_ghost Q) }}ad
| ad_pat_consis__univ_ghost_inh : forall L Ψ Θ R Q,
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ˢ
         (uskl_univ_ghost R) ∼ (open_bskl_wrt_bskl Q (bskl_var_f α)) }}ad) ->
    {{ Ψ ⨟ Θ ⊢ˢ (uskl_univ_ghost R) ∼ (bskl_all_inh Q) }}ad
| ad_pat_consis__univ_ghost_drop : forall Ψ Θ R Q,
    {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ (uskl_univ_ghost R) ∼ Q }}ad

| ad_pat_consis__flex_l : forall Ψ Θ α τ Q,
    binds α (abind_flex_mono_def τ) Θ ->
    {{ Ψ ⨟ Θ ⊢ˢ (ptyp_to_uskl_syn τ) ∼ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ (uskl_var_f α) ∼ Q }}ad
| ad_pat_consis__flex_r : forall Ψ Θ α τ R,
    binds α (abind_flex_mono_def τ) Θ ->
    {{ Ψ ⨟ Θ ⊢ˢ R ∼ (ptyp_to_bskl_syn τ) }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ R ∼ (bskl_var_f α) }}ad
where "{{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad" := (ad_pat_consis Ψ Θ R Q) : fresco_ad_scope.

Inductive ad_refine_syn : aenv -> atoms -> bskl -> bskl -> Prop :=
| ad_refine_syn__unit : forall Θ Δ,
    {{ Θ ⨟ Δ ⊢ᵣ bskl_unit ⊳ bskl_unit }}ad
| ad_refine_syn__var : forall Θ Δ α,
    {{ Θ ⨟ Δ ⊢ᵣ (bskl_var_f α) ⊳ (bskl_var_f α) }}ad
| ad_refine_syn__arrow : forall Θ Δ Q1 Q2 Q3 Q4,
    is_iskl (bskl_arrow Q1 Q2) ->
    {{ Θ ⨟ Δ ⊢ᵣ Q1 ⊳ Q3 }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣ Q2 ⊳ Q4 }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣ (bskl_arrow Q1 Q2) ⊳ (bskl_arrow Q3 Q4) }}ad
| ad_refine_syn__all : forall L Θ Δ Q Q',
    is_iskl (bskl_all_inh Q) ->
    (forall α, α `notin` L ->
       {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α Δ) ⊢ᵣ
         (open_bskl_wrt_bskl Q (bskl_var_f α)) ⊳
         (open_bskl_wrt_bskl Q' (bskl_var_f α)) }}ad) ->
    {{ Θ ⨟ Δ ⊢ᵣ (bskl_all_inh Q) ⊳ (bskl_all_inh Q') }}ad
| ad_refine_syn__ghost : forall Θ Δ P,
    Δ ∩ ftvar_in_pskl P [=] empty ->
    {{ Θ ⨟ Δ ⊢ᵣ bskl_ghost ⊳ (pskl_to_bskl_syn P) }}ad
| ad_refine_syn__univ_ghost_remove : forall Θ Δ Q Q',
    is_iskl (bskl_univ_ghost Q) ->
    {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣ (bskl_univ_ghost Q) ⊳ Q' }}ad
| ad_refine_syn__univ_ghost_fill : forall L Θ Δ Q Q',
    is_iskl (bskl_univ_ghost Q) ->
    (forall α, α `notin` L ->
       {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ᵣ
         (bskl_univ_ghost Q) ⊳ (open_bskl_wrt_bskl Q' (bskl_var_f α)) }}ad) ->
    {{ Θ ⨟ Δ ⊢ᵣ (bskl_univ_ghost Q) ⊳ (bskl_all_syn Q') }}ad
| ad_refine_syn__univ_ghost_keep : forall Θ Δ Q Q',
    is_iskl (bskl_univ_ghost Q) ->
    {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣ (bskl_univ_ghost Q) ⊳ (bskl_univ_ghost Q') }}ad

| ad_refine_syn__flex_l : forall Θ Δ α τ Q',
    binds α (abind_flex_mono_def τ) Θ ->
    {{ Θ ⨟ Δ ⊢ᵣ (ptyp_to_bskl_syn τ) ⊳ Q' }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣ (bskl_var_f α) ⊳ Q' }}ad
| ad_refine_syn__flex_r : forall Θ Δ α τ Q,
    binds α (abind_flex_mono_def τ) Θ ->
    {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ (ptyp_to_bskl_syn τ) }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣ Q ⊳ (bskl_var_f α) }}ad
where "{{ Θ ⨟ Δ ⊢ᵣ Q ⊳ Q' }}ad" := (ad_refine_syn Θ Δ Q Q') : fresco_ad_scope.

Inductive ad_refine_pskl : aenv -> atoms -> pskl -> pskl -> Prop :=
| ad_refine_pskl__unit : forall Θ Δ,
    {{ Θ ⨟ Δ ⊢ᵣₚ pskl_unit ⊳ pskl_unit }}ad
| ad_refine_pskl__var : forall Θ Δ α,
    {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_var_f α) ⊳ (pskl_var_f α) }}ad
| ad_refine_pskl__arrow : forall Θ Δ P1 P2 P3 P4,
    {{ Θ ⨟ Δ ⊢ᵣₚ P1 ⊳ P3 }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣₚ P2 ⊳ P4 }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_arrow P1 P2) ⊳ (pskl_arrow P3 P4) }}ad
| ad_refine_pskl__all : forall L Θ Δ P P',
    (forall α, α `notin` L ->
       {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α Δ) ⊢ᵣₚ
         (open_pskl_wrt_pskl P (pskl_var_f α)) ⊳
         (open_pskl_wrt_pskl P' (pskl_var_f α)) }}ad) ->
    {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_all_syn P) ⊳ (pskl_all_syn P') }}ad
| ad_refine_pskl__ghost : forall Θ Δ P',
    Δ ∩ ftvar_in_pskl P' [=] empty ->
    {{ Θ ⨟ Δ ⊢ᵣₚ pskl_ghost ⊳ P' }}ad
| ad_refine_pskl__univ_ghost_remove : forall Θ Δ P P',
    {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_univ_ghost P) ⊳ P' }}ad
| ad_refine_pskl__univ_ghost_fill : forall L Θ Δ P P',
    (forall α, α `notin` L ->
       {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ᵣₚ
         (pskl_univ_ghost P) ⊳ (open_pskl_wrt_pskl P' (pskl_var_f α)) }}ad) ->
    {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_univ_ghost P) ⊳ (pskl_all_syn P') }}ad
| ad_refine_pskl__univ_ghost_keep : forall Θ Δ P P',
    {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_univ_ghost P) ⊳ (pskl_univ_ghost P') }}ad
| ad_refine_pskl__flex_l : forall Θ Δ α τ P',
    binds α (abind_flex_mono_def τ) Θ ->
    {{ Θ ⨟ Δ ⊢ᵣₚ (ptyp_to_pskl τ) ⊳ P' }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣₚ (pskl_var_f α) ⊳ P' }}ad
| ad_refine_pskl__flex_r : forall Θ Δ α τ P,
    binds α (abind_flex_mono_def τ) Θ ->
    {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ (ptyp_to_pskl τ) }}ad ->
    {{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ (pskl_var_f α) }}ad
where "{{ Θ ⨟ Δ ⊢ᵣₚ P ⊳ P' }}ad" := (ad_refine_pskl Θ Δ P P') : fresco_ad_scope.

Definition ad_consis_join (Ψ : atoms) (Θ : aenv) (R : uskl) (Q : bskl) : Prop :=
  {{ Ψ ⨟ Θ ⊢ˢ R ∼ Q }}ad /\
  {{ Θ ⨟ empty ⊢ᵣₚ ⌊ R ⌋ˢ ⊳ (bskl_to_pskl Q) }}ad.

Notation "{{ Ψ ⨟ Θ ⊢ˢ R ∼ᵣ Q }}ad" := (ad_consis_join Ψ Θ R Q) : fresco_ad_scope.

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
