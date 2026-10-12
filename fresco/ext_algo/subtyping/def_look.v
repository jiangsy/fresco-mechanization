Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.

Set Implicit Arguments.

Open Scope fresco_e_scope.

Reserved Notation "{{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e"
  (at level 0, S1 at level 0, P at level 74, α at level 0, m at level 0,
   P' at level 74, Ξ at level 74, C at level 74,
   format "'{{'  S0  ↝  S1  ⊨  Θ  ⊢  P  ≼[  α  ,  m  ]  P'  ⤳  Ξ  ⨾  C  '}}e'").
Reserved Notation "{{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e"
  (at level 0, S1 at level 0, P at level 74, α at level 0, P' at level 74,
   Ξ at level 74, C at level 74,
   format "'{{'  S0  ↝  S1  ⊨  Θ  ⊢  P  ∼[  α  ]  P'  ⤳  Ξ  ⨾  C  '}}e'").

Inductive e_looksub : supply -> aenv -> atom -> mode -> pskl -> pskl
                      -> supply -> aenv -> a_cstrs -> Prop :=
| e_looksub__var : forall S Θ α m P,
    {{ S ↝ S ⊨ Θ ⊢ (pskl_var_f α) ≼[ α , m ] P ⤳ nil
       ⨾ (a_cstr_sub m P :: nil) }}e
| e_looksub__absent : forall S Θ α m P P',
    α `notin` ftvar_in_pskl P ->
    {{ S ↝ S ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ nil ⨾ nil }}e
| e_looksub__vacuous : forall S Θ α m P,
    P <> pskl_var_f α ->
    {{ S ↝ S ⊨ Θ ⊢ P ≼[ α , m ] pskl_ghost ⤳ nil ⨾ nil }}e
| e_looksub__check : forall S0 S1 Θ α A B Ξ C,
    pskl_ghost_free B ->
    A <> pskl_var_f α ->
    guarded_pskl A ->
    guarded_pskl B ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ A ∼[ α ] B ⤳ Ξ ⨾ C }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ A ≼[ α , mode_tc ] B ⤳ Ξ ⨾ C }}e
| e_looksub__forall_r : forall S0 S1 Θ α A B Ξ C β,

    pskl_ghost_free (pskl_all_syn B) ->
    β `notin` S0 ->
    α `in` ftvar_in_pskl A ->
    A <> pskl_var_f α ->
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ) ⊢ A ≼[ α , mode_tc ]
       (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ C }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ A ≼[ α , mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ C }}e
| e_looksub__arrow : forall S0 S1 S2 Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2,

    {{ S0 ↝ S1 ⊨ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}e ->
    {{ S1 ↝ S2 ⊨ Θ ⊢ P2 ≼[ α , m ] P2' ⤳ Ξ2 ⨾ C2 }}e ->
    {{ S0 ↝ S2 ⊨ Θ ⊢ (pskl_arrow P1 P2) ≼[ α , (mode_fn m) ]
       (pskl_arrow P1' P2') ⤳ (Ξ1 ++ Ξ2) ⨾ (C1 ++ C2) }}e
| e_looksub__forall_l : forall S0 S1 Θ α m P P' Ξ C β,

    β `notin` S0 ->
    α `in` ftvar_in_pskl (pskl_all_syn P) ->
    P' <> pskl_ghost ->

    forall_r_off m P' ->
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
       ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_all_syn P) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e
| e_looksub__univ_ghost_l : forall S0 S1 Θ α m P P' Ξ C,
    P' <> pskl_ghost ->

    forall_r_off m P' ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_univ_ghost P) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e

with e_lookeq : supply -> aenv -> atom -> pskl -> pskl
                -> supply -> aenv -> a_cstrs -> Prop :=
| e_lookeq__var : forall S Θ α P,
    {{ S ↝ S ⊨ Θ ⊢ (pskl_var_f α) ∼[ α ] P ⤳ nil
       ⨾ (a_cstr_eq P :: nil) }}e
| e_lookeq__absent : forall S Θ α P P',
    α `notin` ftvar_in_pskl P ->
    {{ S ↝ S ⊨ Θ ⊢ P ∼[ α ] P' ⤳ nil ⨾ nil }}e
| e_lookeq__vacuous : forall S Θ α P,
    P <> pskl_var_f α ->
    {{ S ↝ S ⊨ Θ ⊢ P ∼[ α ] pskl_ghost ⤳ nil ⨾ nil }}e
| e_lookeq__flex_r : forall S Θ α P β α1,
    α1 `notin` S ->

    a_flex_tvar Θ β ->
    P <> pskl_var_f α ->
    α `in` ftvar_in_pskl P ->
    {{ S ↝ (add α1 S) ⊨ Θ ⊢ P ∼[ α ] (pskl_var_f β)
       ⤳ ((α1 ~ abind_flex_mono) ++ nil)
       ⨾ (a_cstr_eq (pskl_var_f α1) :: nil) }}e
| e_lookeq__arrow : forall S0 S1 S2 Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2,

    {{ S0 ↝ S1 ⊨ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}e ->
    {{ S1 ↝ S2 ⊨ Θ ⊢ P2 ∼[ α ] P2' ⤳ Ξ2 ⨾ C2 }}e ->
    {{ S0 ↝ S2 ⊨ Θ ⊢ (pskl_arrow P1 P2) ∼[ α ] (pskl_arrow P1' P2')
       ⤳ (Ξ1 ++ Ξ2) ⨾ (C1 ++ C2) }}e
| e_lookeq__forall_inh : forall S0 S1 Θ α P P' Ξ C β,

    β `notin` S0 ->
    α `in` ftvar_in_pskl (pskl_all_syn P) ->
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
       ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ]
       (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ ⨾ C }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_all_syn P) ∼[ α ] (pskl_all_syn P') ⤳ Ξ ⨾ C }}e
| e_lookeq__forall_syn : forall S0 S1 Θ α P P' Ξ C β,

    β `notin` S0 ->
    α `in` ftvar_in_pskl (pskl_all_syn P) ->
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
       ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ]
       (pskl_univ_ghost P') ⤳ Ξ ⨾ C }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_all_syn P) ∼[ α ] (pskl_univ_ghost P') ⤳ Ξ ⨾ C }}e
| e_lookeq__univ_ghost : forall S0 S1 Θ α P P' Ξ C,
    {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_univ_ghost P) ∼[ α ] (pskl_univ_ghost P') ⤳ Ξ ⨾ C }}e
| e_lookeq__univ_ghost1 : forall S0 S1 Θ α P P' Ξ C β,

    β `notin` S0 ->
    α `in` ftvar_in_pskl (pskl_univ_ghost P) ->
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
       ⊢ (pskl_univ_ghost P) ∼[ α ]
       (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ ⨾ C }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_univ_ghost P) ∼[ α ] (pskl_all_syn P') ⤳ Ξ ⨾ C }}e
| e_lookeq__univ_ghost2 : forall S0 S1 Θ α P P' Ξ C,
    guarded_pskl P' ->

    flex_r_off Θ P' ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_univ_ghost P) ∼[ α ] P' ⤳ Ξ ⨾ C }}e
| e_lookeq__univ_ghost_r : forall S0 S1 Θ α P P' Ξ C,
    P <> pskl_var_f α ->
    guarded_pskl P ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] (pskl_univ_ghost P') ⤳ Ξ ⨾ C }}e
where "{{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e" :=
  (e_looksub S0 Θ α m P P' S1 Ξ C) : fresco_e_scope
and "{{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e" :=
  (e_lookeq S0 Θ α P P' S1 Ξ C) : fresco_e_scope.

Scheme e_looksub_mind := Induction for e_looksub Sort Prop
  with e_lookeq_mind  := Induction for e_lookeq  Sort Prop.
Combined Scheme e_looksub_lookeq_mutind
  from e_looksub_mind, e_lookeq_mind.
