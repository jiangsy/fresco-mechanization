Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.deco_algo.def_decorated.

Set Implicit Arguments.

Open Scope fresco_ad_scope.

Reserved Notation "{{ Ψ ⨟ Θ ⊢ˢ[ NM | M ] R ⩽ Q }}ad"
  (at level 0, Θ at level 74, NM at level 0, M at level 0, R at level 74, Q at level 74,
   format "'{{'  Ψ  ⨟  Θ  ⊢ˢ[  NM  |  M  ]  R  ⩽  Q  '}}ad'").

Inductive ad_pat_sub :
  a_sub_mode -> mode -> atoms -> aenv -> uskl -> bskl -> Prop :=
| ad_pat_sub__infer : forall NM Ψ Θ R Q,
    Ψ [=] empty ->
    {{ empty ⨟ Θ ⊢ˢ R ∼ᵣ Q }}ad ->
    is_sskl Q ->
    {{ Ψ ⨟ Θ ⊢ˢ[ NM | mode_ti ] R ⩽ Q }}ad
| ad_pat_sub__check : forall Ψ Θ T B,
    guarded_uskl T ->
    guarded_pskl B ->
    {{ Ψ ⨟ Θ ⊢ˢ T ∼ᵣ (pskl_to_bskl_inh B) }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_ty | mode_tc ] T ⩽ (pskl_to_bskl_inh B) }}ad
| ad_pat_sub__forall_r : forall L Ψ Θ T B,
    (forall α, α `notin` L ->
       {{ Ψ ⨟ ((α ~ abind_tvar) ++ Θ) ⊢ˢ[ a_sub_mode_ty | mode_tc ]
         T ⩽ (open_bskl_wrt_bskl B (bskl_var_f α)) }}ad) ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_ty | mode_tc ] T ⩽ (bskl_all_inh B) }}ad
| ad_pat_sub__univ_ghost_r : forall Ψ Θ R Q,
    Ψ [=] empty ->
    guarded_uskl R ->
    guarded_bskl Q ->
    is_sskl Q ->
    {{ empty ⨟ Θ ⊢ˢ R ∼ᵣ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | mode_tc ] R ⩽ (bskl_univ_ghost Q) }}ad
| ad_pat_sub__arrow : forall NM Ψ Ψ1 Ψ2 Θ M R1 R2 Q1 Q2,

    {{ Ψ1 ⨟ Θ ⊢ˢ R1 ∼ᵣ Q1 }}ad ->
    {{ Ψ2 ⨟ Θ ⊢ˢ[ NM | M ] R2 ⩽ Q2 }}ad ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    {{ Ψ ⨟ Θ ⊢ˢ[ NM | mode_fn M ] (uskl_arrow R1 R2) ⩽ (bskl_arrow Q1 Q2) }}ad
| ad_pat_sub__forall_l_tagged : forall NM Ψ Ψ' Θ M ε R ψ Q,
    M <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_uskl (uskl_all_tag ε R)) [=] empty ->
    a_tags_sort NM Ψ' ψ ->
    {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψ ⌋ˢ }}a ->
    {{ (Ψ `union` Ψ') ⨟ Θ ⊢ˢ[ NM | M ] (open_uskl_wrt_uskl R ψ) ⩽ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ[ NM | M ] (uskl_all_tag ε R) ⩽ Q }}ad
| ad_pat_sub__forall_l_untagged : forall NM Ψ Ψ' Θ M R ψ Q,
    M <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_uskl (uskl_all_syn R)) [=] empty ->
    a_tags_sort NM Ψ' ψ ->
    {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψ ⌋ˢ }}a ->
    {{ (Ψ `union` Ψ') ⨟ Θ ⊢ˢ[ NM | M ] (open_uskl_wrt_uskl R ψ) ⩽ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ[ NM | M ] (uskl_all_syn R) ⩽ Q }}ad
| ad_pat_sub__ghost : forall Ψ Θ M P,
    Ψ [=] empty ->
    mod_comp_sk (pskl_to_bskl_inh P) M ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | M ] uskl_ghost ⩽ (pskl_to_bskl_inh P) }}ad
| ad_pat_sub__ghostg : forall Ψ Θ M,
    Ψ [=] empty ->
    mod_comp_sk bskl_ghost M ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | M ] uskl_dot_ghost ⩽ bskl_ghost }}ad
| ad_pat_sub__univ_ghost_l : forall Ψ Θ M R Q,
    M <> mode_ti ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | M ] R ⩽ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | M ] (uskl_univ_ghost R) ⩽ Q }}ad
| ad_pat_sub__univ_ghost_lg : forall Ψ Θ M R Q,
    M <> mode_ti ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | M ] R ⩽ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ[ a_sub_mode_sk | M ] (uskl_dot_univ_ghost R) ⩽ Q }}ad

| ad_pat_sub__flex_mono : forall NM Ψ Θ M α τ Q,
    binds α (abind_flex_mono_def τ) Θ ->
    {{ Ψ ⨟ Θ ⊢ˢ[ NM | mode_fn M ] (ptyp_to_uskl_syn τ) ⩽ Q }}ad ->
    {{ Ψ ⨟ Θ ⊢ˢ[ NM | mode_fn M ] (uskl_var_f α) ⩽ Q }}ad
where "{{ Ψ ⨟ Θ ⊢ˢ[ NM | M ] R ⩽ Q }}ad" :=
  (ad_pat_sub NM M Ψ Θ R Q) : fresco_ad_scope.

Inductive ad_pat_sub_fuel :
  nat -> a_sub_mode -> mode -> atoms -> aenv -> uskl -> bskl -> Prop :=
| ad_pat_sub_fuel__infer : forall n NM Ψ Θ R Q,
    Ψ [=] empty ->
    {{ empty ⨟ Θ ⊢ˢ R ∼ᵣ Q }}ad ->
    is_sskl Q ->
    ad_pat_sub_fuel n NM mode_ti Ψ Θ R Q
| ad_pat_sub_fuel__check : forall n Ψ Θ T B,
    guarded_uskl T ->
    guarded_pskl B ->
    {{ Ψ ⨟ Θ ⊢ˢ T ∼ᵣ (pskl_to_bskl_inh B) }}ad ->
    ad_pat_sub_fuel n a_sub_mode_ty mode_tc Ψ Θ T (pskl_to_bskl_inh B)
| ad_pat_sub_fuel__forall_r : forall n L Ψ Θ T B,
    (forall α, α `notin` L ->
       ad_pat_sub_fuel n a_sub_mode_ty mode_tc Ψ ((α ~ abind_tvar) ++ Θ)
         T (open_bskl_wrt_bskl B (bskl_var_f α))) ->
    ad_pat_sub_fuel (S n) a_sub_mode_ty mode_tc Ψ Θ T (bskl_all_inh B)
| ad_pat_sub_fuel__univ_ghost_r : forall n Ψ Θ R Q,
    Ψ [=] empty ->
    guarded_uskl R ->
    guarded_bskl Q ->
    is_sskl Q ->
    {{ empty ⨟ Θ ⊢ˢ R ∼ᵣ Q }}ad ->
    ad_pat_sub_fuel n a_sub_mode_sk mode_tc Ψ Θ R (bskl_univ_ghost Q)
| ad_pat_sub_fuel__arrow : forall n NM Ψ Ψ1 Ψ2 Θ M R1 R2 Q1 Q2,
    {{ Ψ1 ⨟ Θ ⊢ˢ R1 ∼ᵣ Q1 }}ad ->
    ad_pat_sub_fuel n NM M Ψ2 Θ R2 Q2 ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    ad_pat_sub_fuel (S n) NM (mode_fn M) Ψ Θ (uskl_arrow R1 R2) (bskl_arrow Q1 Q2)
| ad_pat_sub_fuel__forall_l_tagged : forall n NM Ψ Ψ' Θ M ε R ψ Q,
    M <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_uskl (uskl_all_tag ε R)) [=] empty ->
    a_tags_sort NM Ψ' ψ ->
    {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψ ⌋ˢ }}a ->
    ad_pat_sub_fuel n NM M (Ψ `union` Ψ') Θ (open_uskl_wrt_uskl R ψ) Q ->
    ad_pat_sub_fuel (S n) NM M Ψ Θ (uskl_all_tag ε R) Q
| ad_pat_sub_fuel__forall_l_untagged : forall n NM Ψ Ψ' Θ M R ψ Q,
    M <> mode_ti ->
    Ψ' ∩ Ψ [=] empty ->
    Ψ' ∩ (ftag_in_uskl (uskl_all_syn R)) [=] empty ->
    a_tags_sort NM Ψ' ψ ->
    {{ Θ ⨟ empty ⊢ₚₛ ⌊ ψ ⌋ˢ }}a ->
    ad_pat_sub_fuel n NM M (Ψ `union` Ψ') Θ (open_uskl_wrt_uskl R ψ) Q ->
    ad_pat_sub_fuel (S n) NM M Ψ Θ (uskl_all_syn R) Q
| ad_pat_sub_fuel__ghost : forall n Ψ Θ M P,

    Ψ [=] empty ->
    mod_comp_sk (pskl_to_bskl_inh P) M ->
    ad_pat_sub_fuel n a_sub_mode_sk M Ψ Θ uskl_ghost (pskl_to_bskl_inh P)
| ad_pat_sub_fuel__ghostg : forall n Ψ Θ M,
    Ψ [=] empty ->
    mod_comp_sk bskl_ghost M ->
    ad_pat_sub_fuel n a_sub_mode_sk M Ψ Θ uskl_dot_ghost bskl_ghost
| ad_pat_sub_fuel__univ_ghost_l : forall n Ψ Θ M R Q,
    M <> mode_ti ->
    ad_pat_sub_fuel n a_sub_mode_sk M Ψ Θ R Q ->
    ad_pat_sub_fuel n a_sub_mode_sk M Ψ Θ (uskl_univ_ghost R) Q
| ad_pat_sub_fuel__univ_ghost_lg : forall n Ψ Θ M R Q,
    M <> mode_ti ->
    ad_pat_sub_fuel n a_sub_mode_sk M Ψ Θ R Q ->
    ad_pat_sub_fuel n a_sub_mode_sk M Ψ Θ (uskl_dot_univ_ghost R) Q
| ad_pat_sub_fuel__flex_mono : forall n NM Ψ Θ M α τ Q,
    binds α (abind_flex_mono_def τ) Θ ->
    ad_pat_sub_fuel n NM (mode_fn M) Ψ Θ (ptyp_to_uskl_syn τ) Q ->
    ad_pat_sub_fuel n NM (mode_fn M) Ψ Θ (uskl_var_f α) Q.

Reserved Notation "{{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad"
  (at level 0, Δ at level 74, P at level 74, Ψ at level 0, ψ at level 74,
   format "'{{'  Θ  ⨟  Δ  ⊢ˢ  P  ⊑ᵖ[  Ψ  ]  ψ  '}}ad'").

Inductive ad_partial_precise :
  aenv -> atoms -> atoms -> pskl -> uskl -> Prop :=
| ad_ppre__unit : forall Θ Δ Ψ,
    Ψ [=] empty ->
    {{ Θ ⨟ Δ ⊢ˢ pskl_unit ⊑ᵖ[ Ψ ] uskl_unit }}ad
| ad_ppre__var : forall Θ Δ Ψ α,
    Ψ [=] empty ->
    {{ Θ ⨟ Δ ⊢ˢ (pskl_var_f α) ⊑ᵖ[ Ψ ] (uskl_var_f α) }}ad
| ad_ppre__arrow : forall Θ Δ Ψ Ψ1 Ψ2 P1 P2 ψ1 ψ2,
    {{ Θ ⨟ Δ ⊢ˢ P1 ⊑ᵖ[ Ψ1 ] ψ1 }}ad ->
    {{ Θ ⨟ Δ ⊢ˢ P2 ⊑ᵖ[ Ψ2 ] ψ2 }}ad ->
    Ψ [=] Ψ1 `union` Ψ2 ->
    {{ Θ ⨟ Δ ⊢ˢ (pskl_arrow P1 P2) ⊑ᵖ[ Ψ ] (uskl_arrow ψ1 ψ2) }}ad
| ad_ppre__forall : forall L Θ Δ Ψ Ψ0 ε P ψ,
    (forall α, α `notin` L ->
       {{ ((α ~ abind_tvar) ++ Θ) ⨟ (add α Δ) ⊢ˢ
         (open_pskl_wrt_pskl P (pskl_var_f α))
         ⊑ᵖ[ Ψ0 ] (open_uskl_wrt_uskl ψ (uskl_var_f α)) }}ad) ->
    Ψ [=] add ε Ψ0 ->
    {{ Θ ⨟ Δ ⊢ˢ (pskl_all_syn P) ⊑ᵖ[ Ψ ] (uskl_all_tag ε ψ) }}ad
| ad_ppre__ghost : forall Θ Δ Ψ ψ,
    Ψ [=] empty ->
    Δ ∩ ftvar_in_uskl ψ [=] empty ->
    {{ Θ ⨟ Δ ⊢ˢ pskl_ghost ⊑ᵖ[ Ψ ] ψ }}ad
| ad_ppre__univ_ghost_remove : forall Θ Δ Ψ P ψ,
    {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
    {{ Θ ⨟ Δ ⊢ˢ (pskl_univ_ghost P) ⊑ᵖ[ Ψ ] ψ }}ad
| ad_ppre__univ_ghost_fill : forall L Θ Δ Ψ P ψ,
    (forall α, α `notin` L ->
       {{ ((α ~ abind_tvar) ++ Θ) ⨟ Δ ⊢ˢ (pskl_univ_ghost P)
         ⊑ᵖ[ Ψ ] (open_uskl_wrt_uskl ψ (uskl_var_f α)) }}ad) ->
    forall ε,
    {{ Θ ⨟ Δ ⊢ˢ (pskl_univ_ghost P) ⊑ᵖ[ Ψ ] (uskl_all_tag ε ψ) }}ad
| ad_ppre__univ_ghost_keep : forall Θ Δ Ψ P ψ,
    {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad ->
    {{ Θ ⨟ Δ ⊢ˢ (pskl_univ_ghost P) ⊑ᵖ[ Ψ ] (uskl_dot_univ_ghost ψ) }}ad

| ad_ppre__flex_l : forall Θ Δ Ψ α τ ψ,
    binds α (abind_flex_mono_def τ) Θ ->
    {{ Θ ⨟ Δ ⊢ˢ (ptyp_to_pskl τ) ⊑ᵖ[ Ψ ] ψ }}ad ->
    {{ Θ ⨟ Δ ⊢ˢ (pskl_var_f α) ⊑ᵖ[ Ψ ] ψ }}ad
| ad_ppre__flex_r : forall Θ Δ Ψ α τ P,
    binds α (abind_flex_mono_def τ) Θ ->
    {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] (ptyp_to_uskl_syn τ) }}ad ->
    {{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] (uskl_var_f α) }}ad
where "{{ Θ ⨟ Δ ⊢ˢ P ⊑ᵖ[ Ψ ] ψ }}ad" :=
  (ad_partial_precise Θ Δ Ψ P ψ) : fresco_ad_scope.
