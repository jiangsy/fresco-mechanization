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

Reserved Notation "{{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e"
  (at level 0, S1 at level 0, P at level 74, m at level 0, Q at level 74,
   Ξ at level 74, P' at level 74,
   format "'{{'  S0  ↝  S1  ⊨  Θ  ⊢ₛ  P  ≼[  m  ]  Q  ⤳  Ξ  ⨾  P'  '}}e'").
Reserved Notation "{{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e"
  (at level 0, S1 at level 0, P at level 74, Q at level 74, Ξ at level 74,
   P' at level 74,
   format "'{{'  S0  ↝  S1  ⊨  Θ  ⊢ₑ  P  ∼  Q  ⤳  Ξ  ⨾  P'  '}}e'").

Inductive e_solve_sub : supply -> aenv -> mode -> pskl -> pskl
                        -> supply -> aenv -> pskl -> Prop :=
| e_solve_sub__var : forall S Θ m α Q,
    {{ S ↝ S ⊨ Θ ⊢ₛ (pskl_var_f α) ≼[ m ] Q ⤳ nil ⨾ (pskl_var_f α) }}e
| e_solve_sub__forall_l : forall S0 S1 Θ m P Q Ξ P' β,
    β `notin` S0 ->
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
       ⊢ₛ (open_pskl_wrt_pskl P (pskl_var_f β)) ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₛ (pskl_all_syn P) ≼[ m ] Q
       ⤳ Ξ ⨾ (pskl_all_syn (close_pskl_wrt_pskl β P')) }}e
| e_solve_sub__univ_ghost_l : forall S0 S1 Θ m P Q Ξ P',
    {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₛ (pskl_univ_ghost P) ≼[ m ] Q ⤳ Ξ ⨾ (pskl_univ_ghost P') }}e
| e_solve_sub__vacuous : forall S Θ m P,

    peel_l_off P ->
    {{ S ↝ S ⊨ Θ ⊢ₛ P ≼[ m ] pskl_ghost ⤳ nil ⨾ P }}e
| e_solve_sub__check : forall S0 S1 Θ P Q Ξ P',
    pskl_ghost_free Q ->
    guarded_pskl P ->
    guarded_pskl Q ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ mode_tc ] Q ⤳ Ξ ⨾ P' }}e
| e_solve_sub__forall_r : forall S0 S1 Θ P B Ξ P' β,
    pskl_ghost_free (pskl_all_syn B) ->

    solve_l_off P ->
    β `notin` S0 ->
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ mode_tc ]
       (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ P' }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ P' }}e
| e_solve_sub__arrow : forall S0 S1 S2 Θ m P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2',

    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ P1' }}e ->
    {{ S1 ↝ S2 ⊨ (Ξ1 ++ Θ) ⊢ₛ P2 ≼[ m ] Q2 ⤳ Ξ2 ⨾ P2' }}e ->
    {{ S0 ↝ S2 ⊨ Θ ⊢ₛ (pskl_arrow P1 P2) ≼[ (mode_fn m) ] (pskl_arrow Q1 Q2)
       ⤳ (Ξ2 ++ Ξ1) ⨾ (pskl_arrow P1' P2') }}e
| e_solve_sub__ghost_l_fn : forall S0 S1 S2 Θ m Q1 Q2 Ξ1 Ξ2 P1' P2',
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ pskl_ghost ∼ Q1 ⤳ Ξ1 ⨾ P1' }}e ->
    {{ S1 ↝ S2 ⊨ (Ξ1 ++ Θ) ⊢ₛ pskl_ghost ≼[ m ] Q2 ⤳ Ξ2 ⨾ P2' }}e ->
    {{ S0 ↝ S2 ⊨ Θ ⊢ₛ pskl_ghost ≼[ (mode_fn m) ] (pskl_arrow Q1 Q2)
       ⤳ (Ξ2 ++ Ξ1) ⨾ (pskl_univ_ghost (pskl_arrow P1' P2')) }}e
| e_solve_sub__ghost_l : forall S Θ B,
    pskl_ghost_free B ->
    guarded_pskl B ->
    {{ S ↝ S ⊨ Θ ⊢ₛ pskl_ghost ≼[ mode_tc ] B ⤳ nil ⨾ (pskl_univ_ghost B) }}e

with e_solve_eq : supply -> aenv -> pskl -> pskl -> supply -> aenv -> pskl -> Prop :=
| e_solve_eq__unit : forall S Θ,
    {{ S ↝ S ⊨ Θ ⊢ₑ pskl_unit ∼ pskl_unit ⤳ nil ⨾ pskl_unit }}e
| e_solve_eq__var : forall S Θ α Q,
    {{ S ↝ S ⊨ Θ ⊢ₑ (pskl_var_f α) ∼ Q ⤳ nil ⨾ (pskl_var_f α) }}e
| e_solve_eq__flex_r : forall S0 S1 Θ α P Ξ A,
    a_flex_tvar Θ α ->
    a_non_flex Θ P ->
    nonghost_pskl P ->
    e_guess_mono S0 P S1 Ξ A ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ (pskl_var_f α) ⤳ Ξ ⨾ (ptyp_to_pskl A) }}e
| e_solve_eq__ghost_l : forall S Θ Q,
    {{ S ↝ S ⊨ Θ ⊢ₑ pskl_ghost ∼ Q ⤳ nil ⨾ Q }}e
| e_solve_eq__ghost_r : forall S Θ P,
    {{ S ↝ S ⊨ Θ ⊢ₑ P ∼ pskl_ghost ⤳ nil ⨾ P }}e
| e_solve_eq__arrow : forall S0 S1 S2 Θ P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2',

    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ P1' }}e ->
    {{ S1 ↝ S2 ⊨ (Ξ1 ++ Θ) ⊢ₑ P2 ∼ Q2 ⤳ Ξ2 ⨾ P2' }}e ->
    {{ S0 ↝ S2 ⊨ Θ ⊢ₑ (pskl_arrow P1 P2) ∼ (pskl_arrow Q1 Q2)
       ⤳ (Ξ2 ++ Ξ1) ⨾ (pskl_arrow P1' P2') }}e
| e_solve_eq__forall : forall S0 S1 Θ P Q Ξ P' β,
    β `notin` S0 ->
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
       ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f β))
       ∼ (open_pskl_wrt_pskl Q (pskl_var_f β)) ⤳ Ξ ⨾ P' }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_all_syn P) ∼ (pskl_all_syn Q)
       ⤳ Ξ ⨾ (pskl_all_syn (close_pskl_wrt_pskl β P')) }}e
| e_solve_eq__univ_ghost_both : forall S0 S1 Θ P Q Ξ P',
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_univ_ghost P) ∼ (pskl_univ_ghost Q)
       ⤳ Ξ ⨾ (pskl_univ_ghost P') }}e
| e_solve_eq__univ_ghost_l_all : forall S0 S1 Θ P Q Ξ P' β,
    β `notin` S0 ->
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ) ⊢ₑ (pskl_univ_ghost P)
       ∼ (open_pskl_wrt_pskl Q (pskl_var_f β)) ⤳ Ξ ⨾ P' }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_univ_ghost P) ∼ (pskl_all_syn Q)
       ⤳ Ξ ⨾ (pskl_all_syn (close_pskl_wrt_pskl β P')) }}e
| e_solve_eq__univ_ghost_l_guarded : forall S0 S1 Θ P Q Ξ P',
    guarded_pskl Q ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_univ_ghost P) ∼ Q ⤳ Ξ ⨾ P' }}e
| e_solve_eq__all_l_univ_ghost : forall S0 S1 Θ P Q Ξ P' β,
    β `notin` S0 ->
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
       ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f β))
       ∼ (pskl_univ_ghost Q) ⤳ Ξ ⨾ P' }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_all_syn P) ∼ (pskl_univ_ghost Q)
       ⤳ Ξ ⨾ (pskl_all_syn (close_pskl_wrt_pskl β P')) }}e
| e_solve_eq__univ_ghost_r_guarded : forall S0 S1 Θ P Q Ξ P',
    guarded_pskl P ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ (pskl_univ_ghost Q) ⤳ Ξ ⨾ P' }}e
where "{{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e" :=
  (e_solve_sub S0 Θ m P Q S1 Ξ P') : fresco_e_scope
and "{{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e" :=
  (e_solve_eq S0 Θ P Q S1 Ξ P') : fresco_e_scope.

Scheme e_solve_sub_mind := Induction for e_solve_sub Sort Prop
  with e_solve_eq_mind  := Induction for e_solve_eq  Sort Prop.
Combined Scheme e_solve_sub_eq_mutind
  from e_solve_sub_mind, e_solve_eq_mind.

Reserved Notation "{{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}e"
  (at level 0, S1 at level 0, C at level 74, P at level 74, Ξ at level 74,
   Q at level 74,
   format "'{{'  S0  ↝  S1  ⊨  Θ  ⊩  C  ⨾  P  ⤳  Ξ  ⨾  Q  '}}e'").

Inductive e_solve_cstr : supply -> aenv -> a_cstrs -> pskl
                         -> supply -> aenv -> pskl -> Prop :=
| e_solve_cstr__empty : forall S Θ P,
    {{ S ↝ S ⊨ Θ ⊩ nil ⨾ P ⤳ nil ⨾ P }}e
| e_solve_cstr__sub : forall S0 S1 Θ m Q P Ξ P',
    {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊩ (a_cstr_sub m Q :: nil) ⨾ P ⤳ Ξ ⨾ P' }}e
| e_solve_cstr__eq : forall S0 S1 S2 Θ Q C P Ξ1 Ξ2 P' P'',

    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ1 ⨾ P'' }}e ->
    {{ S1 ↝ S2 ⊨ (Ξ1 ++ Θ) ⊩ C ⨾ P'' ⤳ Ξ2 ⨾ P' }}e ->
    {{ S0 ↝ S2 ⊨ Θ ⊩ (a_cstr_eq Q :: C) ⨾ P ⤳ (Ξ2 ++ Ξ1) ⨾ P' }}e
where "{{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}e" :=
  (e_solve_cstr S0 Θ C P S1 Ξ Q) : fresco_e_scope.
