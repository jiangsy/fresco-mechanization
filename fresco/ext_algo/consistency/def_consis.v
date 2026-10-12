Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_guess.

Set Implicit Arguments.

Open Scope fresco_e_scope.

Reserved Notation "{{ S0 ↝ S1 ⊨ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ' }}e"
  (at level 0, S1 at level 0, Ξ at level 0, α at level 74, P at level 74, Θ' at level 74,
   format "'{{'  S0  ↝  S1  ⊨  Θ  ⊲[  Ξ  ]  α  ≔  P  ⊣  Θ'  '}}e'").
Reserved Notation "{{ S0 ↝ S1 ⊨ Θ ⊲ α ≈ᵘ β ⊣ Θ' }}e"
  (at level 0, S1 at level 0, α at level 74, β at level 74, Θ' at level 74,
   format "'{{'  S0  ↝  S1  ⊨  Θ  ⊲  α  ≈ᵘ  β  ⊣  Θ'  '}}e'").
Reserved Notation "{{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}e"
  (at level 0, S1 at level 0, Δ1 at level 0, Δ2 at level 0, P0 at level 0,
   P at level 74, Q at level 74, Θ' at level 74,
   format "'{{'  S0  ↝  S1  ⊨  Θ  ⊢[  Δ1  |  Δ2  |  P0  ]  P  ∼  Q  ⊣  Θ'  '}}e'").

Inductive e_assign : supply -> aenv -> aenv -> atom -> pskl -> supply -> aenv -> Prop :=
| e_assign__univ_ghost_id : forall S Θ0 α,
    {{ S ↝ S ⊨ ((α ~ abind_flex_mono) ++ Θ0) ⊲[ nil ] α
       ≔ (pskl_univ_ghost (pskl_var_f α)) ⊣ ((α ~ abind_flex_mono) ++ Θ0) }}e
| e_assign__solve_m : forall S0 S1 Θ0 Ξ α P βs τ,
    α `notin` ftvar_in_pskl P ->
    e_guess_mono S0 P S1 βs τ ->
    mono_ptyp τ ->
    {{ S0 ↝ S1 ⊨ ((α ~ abind_flex_mono) ++ Θ0) ⊲[ Ξ ] α ≔ P
       ⊣ ((α ~ abind_flex_mono_def τ) ++ βs ++ Ξ ++ Θ0) }}e
| e_assign__assign : forall S0 S1 Θ0 Θ1 Ξ α β τ P Q,

    a_flex_tvar ((β ~ abind_flex_mono_def τ) ++ Θ0) α ->
    {{ S0 ↝ S1 ⊨ (Ξ ++ Θ0) ⊢[ empty | empty
         | (subst_pskl_in_pskl (ptyp_to_pskl τ) β P) ]
       (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)) ∼ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ ((β ~ abind_flex_mono_def τ) ++ Θ0) ⊲[ Ξ ] α ≔ P
       ⊣ ((β ~ abind_flex_mono_def τ) ++ Θ1) }}e
| e_assign__depend : forall S0 S1 Θ0 Θ1 Ξ α β P,

    α <> β ->
    β `in` ftvar_in_pskl P ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ++ (β ~ abind_flex_mono) ] α ≔ P ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ ((β ~ abind_flex_mono) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e
| e_assign__skip : forall S0 S1 Θ0 Θ1 Ξ α β P,

    α <> β ->
    β `notin` ftvar_in_pskl P ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ ((β ~ abind_flex_mono) ++ Θ0) ⊲[ Ξ ] α ≔ P
       ⊣ ((β ~ abind_flex_mono) ++ Θ1) }}e
| e_assign__skip_rigid : forall S0 S1 Θ0 Θ1 Ξ α β P,

    β `notin` ftvar_in_pskl P ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ0) ⊲[ Ξ ] α ≔ P
       ⊣ ((β ~ abind_tvar) ++ Θ1) }}e
| e_assign__skip_tm_var : forall S0 S1 Θ0 Θ1 Ξ α x A P,

    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ ((x ~ abind_var_typ A) ++ Θ0) ⊲[ Ξ ] α ≔ P
       ⊣ ((x ~ abind_var_typ A) ++ Θ1) }}e
| e_assign__skip_tm_skl : forall S0 S1 Θ0 Θ1 Ξ α x Q P,

    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ ((x ~ abind_var_skl Q) ++ Θ0) ⊲[ Ξ ] α ≔ P
       ⊣ ((x ~ abind_var_skl Q) ++ Θ1) }}e

with e_unify : supply -> aenv -> atom -> atom -> supply -> aenv -> Prop :=
| e_unify__flex_id : forall S Θ0 α,
    a_flex_tvar Θ0 α ->
    {{ S ↝ S ⊨ Θ0 ⊲ α ≈ᵘ α ⊣ Θ0 }}e
| e_unify__flex_l : forall S Θ0 α β,
    α <> β ->
    a_flex_tvar Θ0 β ->
    {{ S ↝ S ⊨ ((α ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β
       ⊣ ((α ~ abind_flex_mono_def (ptyp_var_f β)) ++ Θ0) }}e
| e_unify__flex_r : forall S Θ0 α β,
    α <> β ->
    a_flex_tvar Θ0 α ->
    {{ S ↝ S ⊨ ((β ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β
       ⊣ ((β ~ abind_flex_mono_def (ptyp_var_f α)) ++ Θ0) }}e
| e_unify__flex_assign : forall S0 S1 Θ0 Θ1 α1 τ α β Q,

    a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) α ->
    a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) β ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ empty | empty
         | (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β))) ]
       (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α))) ∼ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ ((α1 ~ abind_flex_mono_def τ) ++ Θ0) ⊲ α ≈ᵘ β
       ⊣ ((α1 ~ abind_flex_mono_def τ) ++ Θ1) }}e
| e_unify__flex_skip : forall S0 S1 Θ0 Θ1 α1 α β,

    α1 <> α ->
    α1 <> β ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ ((α1 ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β
       ⊣ ((α1 ~ abind_flex_mono) ++ Θ1) }}e
| e_unify__skip_other : forall S0 S1 Θ0 Θ1 c b α β,

    (b = abind_tvar \/
     (exists A, b = abind_var_typ A) \/
     (exists Q, b = abind_var_skl Q)) ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ ((c ~ b) ++ Θ0) ⊲ α ≈ᵘ β ⊣ ((c ~ b) ++ Θ1) }}e

with e_consis : atoms -> atoms -> supply -> aenv -> pskl -> pskl -> pskl
                -> supply -> aenv -> Prop :=
| e_consis__ghost : forall Δ1 Δ2 S Θ0 P0,
    Δ2 ∩ ftvar_in_pskl P0 [=] empty ->
    {{ S ↝ S ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] pskl_ghost ∼ P0 ⊣ Θ0 }}e
| e_consis__unit : forall Δ1 Δ2 S Θ0,
    {{ S ↝ S ⊨ Θ0 ⊢[ Δ1 | Δ2 | pskl_unit ] pskl_unit ∼ pskl_unit ⊣ Θ0 }}e
| e_consis__rigid : forall Δ1 Δ2 S Θ0 α,
    binds α abind_tvar Θ0 ->
    {{ S ↝ S ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f α) ]
       (pskl_var_f α) ∼ (pskl_var_f α) ⊣ Θ0 }}e
| e_consis__arrow : forall Δ1 Δ2 S0 S1 S2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2,

    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0a ] P1 ∼ Q1 ⊣ Θ1 }}e ->
    {{ S1 ↝ S2 ⊨ Θ1 ⊢[ Δ1 | Δ2 | P0b ] P2 ∼ Q2 ⊣ Θ2 }}e ->
    {{ S0 ↝ S2 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_arrow P0a P0b) ]
       (pskl_arrow P1 P2) ∼ (pskl_arrow Q1 Q2) ⊣ Θ2 }}e
| e_consis__forall_inh : forall Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α,
    α `notin` S0 ->
    {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ (add α Δ1) | (add α Δ2)
         | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ]
       (open_pskl_wrt_pskl P (pskl_var_f α)) ∼ Q
       ⊣ ((α ~ abind_tvar) ++ Θ1) }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_all_syn P0) ]
       (pskl_all_syn P) ∼ (pskl_all_syn (close_pskl_wrt_pskl α Q)) ⊣ Θ1 }}e
| e_consis__forall_syn : forall Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α,
    α `notin` S0 ->
    {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ Δ1 | (add α Δ2) | (pskl_univ_ghost P0) ]
       (open_pskl_wrt_pskl P (pskl_var_f α)) ∼ Q
       ⊣ ((α ~ abind_tvar) ++ Θ1) }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) ]
       (pskl_all_syn P) ∼ (pskl_all_syn (close_pskl_wrt_pskl α Q)) ⊣ Θ1 }}e
| e_consis__univ_ghost : forall Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q,
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) ]
       (pskl_univ_ghost P) ∼ (pskl_univ_ghost Q) ⊣ Θ1 }}e
| e_consis__univ_ghost1 : forall Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α,
    α `notin` S0 ->
    {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ (add α Δ1) | Δ2
         | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ]
       (pskl_univ_ghost P) ∼ Q
       ⊣ ((α ~ abind_tvar) ++ Θ1) }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_all_syn P0) ]
       (pskl_univ_ghost P) ∼ (pskl_all_syn (close_pskl_wrt_pskl α Q)) ⊣ Θ1 }}e
| e_consis__univ_ghost2 : forall Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q,
    guarded_pskl P0 ->
    a_non_flex Θ0 P0 ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] (pskl_univ_ghost P) ∼ Q ⊣ Θ1 }}e
| e_consis__flex : forall Δ1 Δ2 S0 S1 Θ0 Θ1 α β,
    {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f β) ]
       (pskl_var_f α) ∼ (pskl_var_f α) ⊣ Θ1 }}e
| e_consis__flex_l : forall Δ1 Δ2 S0 S1 Θ0 Θ1 α P0,
    a_non_flex Θ0 P0 ->
    P0 <> pskl_ghost ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] α ≔ P0 ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ]
       (pskl_var_f α) ∼ (pskl_var_f α) ⊣ Θ1 }}e
| e_consis__flex_r : forall Δ1 Δ2 S0 S1 Θ0 Θ1 α P,
    a_non_flex Θ0 P ->
    P <> pskl_ghost ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] α ≔ P ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f α) ] P ∼ (pskl_var_f α) ⊣ Θ1 }}e
| e_consis__ghost_r : forall Δ1 Δ2 S Θ0 P,
    Δ1 ∩ ftvar_in_pskl P [=] empty ->
    {{ S ↝ S ⊨ Θ0 ⊢[ Δ1 | Δ2 | pskl_ghost ] P ∼ P ⊣ Θ0 }}e
| e_consis__univ_ghost_r : forall Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q,
    guarded_pskl P ->
    a_non_flex Θ0 P ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_univ_ghost P0) ] P ∼ Q ⊣ Θ1 }}e
where "{{ S0 ↝ S1 ⊨ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ' }}e" :=
  (e_assign S0 Θ Ξ α P S1 Θ') : fresco_e_scope
and "{{ S0 ↝ S1 ⊨ Θ ⊲ α ≈ᵘ β ⊣ Θ' }}e" :=
  (e_unify S0 Θ α β S1 Θ') : fresco_e_scope
and "{{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}e" :=
  (e_consis Δ1 Δ2 S0 Θ P0 P Q S1 Θ') : fresco_e_scope.

Scheme e_assign_mind := Induction for e_assign Sort Prop
  with e_unify_mind  := Induction for e_unify  Sort Prop
  with e_consis_mind := Induction for e_consis Sort Prop.
Combined Scheme e_assign_unify_consis_mutind
  from e_assign_mind, e_unify_mind, e_consis_mind.
