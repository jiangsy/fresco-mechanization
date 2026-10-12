Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.ext_algo.basic.def_supply.

Set Implicit Arguments.

Inductive e_guess_mono : supply -> pskl -> supply -> aenv -> ptyp -> Prop :=
| e_guess_mono__ghost : forall S α,
    α `notin` S ->
    e_guess_mono S pskl_ghost (add α S)
      ((α ~ abind_flex_mono) ++ nil) (ptyp_var_f α)
| e_guess_mono__univ_ghost : forall S0 S1 P Ξ A,
    e_guess_mono S0 P S1 Ξ A ->
    e_guess_mono S0 (pskl_univ_ghost P) S1 Ξ A
| e_guess_mono__var : forall S α,
    e_guess_mono S (pskl_var_f α) S nil (ptyp_var_f α)
| e_guess_mono__unit : forall S,
    e_guess_mono S pskl_unit S nil ptyp_unit
| e_guess_mono__arrow : forall S0 S1 S2 P Q Ξ1 Ξ2 A B,

    e_guess_mono S0 P S1 Ξ1 A ->
    e_guess_mono S1 Q S2 Ξ2 B ->
    e_guess_mono S0 (pskl_arrow P Q) S2 (Ξ1 ++ Ξ2) (ptyp_arrow A B)
| e_guess_mono__forall : forall S0 S1 P Ξ A β,
    β `notin` S0 ->
    e_guess_mono (add β S0) (open_pskl_wrt_pskl P (pskl_var_f β)) S1 Ξ A ->
    e_guess_mono S0 (pskl_all_syn P) S1 Ξ (ptyp_all (close_ptyp_wrt_ptyp β A)).

Inductive e_guess : supply -> a_sub_mode -> pskl -> supply -> aenv -> pskl
                    -> Prop :=
| e_guess__sk : forall S Q,
    e_guess S a_sub_mode_sk Q S nil Q
| e_guess__ty : forall S0 S1 Q Ξ A,
    e_guess_mono S0 Q S1 Ξ A ->
    e_guess S0 a_sub_mode_ty Q S1 Ξ (ptyp_to_pskl A).
