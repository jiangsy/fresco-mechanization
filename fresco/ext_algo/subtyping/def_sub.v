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
Require Import src.fresco.ext_algo.consistency.def_consis.
Require Import src.fresco.ext_algo.subtyping.def_look.
Require Import src.fresco.ext_algo.subtyping.def_solve.
Require Import src.fresco.ext_algo.subtyping.def_extract.

Set Implicit Arguments.

Open Scope fresco_e_scope.

Definition e_consis_chk (S0 : supply) (Θ0 : aenv) (P P0 : pskl)
                        (S1 : supply) (Θ1 : aenv) : Prop :=
  exists Q, {{ S0 ↝ S1 ⊨ Θ0 ⊢[ empty | empty | P0 ] P ∼ Q ⊣ Θ1 }}e.

Reserved Notation "{{ S0 ↝ S1 ⊨ Θ ⊢[ N | m | P0 ] P ⩽ Q ⊣ Θ' }}e"
  (at level 0, S1 at level 0, N at level 0, m at level 0, P0 at level 0,
   P at level 74, Q at level 74, Θ' at level 74,
   format "'{{'  S0  ↝  S1  ⊨  Θ  ⊢[  N  |  m  |  P0  ]  P  ⩽  Q  ⊣  Θ'  '}}e'").

Inductive e_sub : supply -> a_sub_mode -> mode -> pskl -> aenv -> pskl -> pskl
                  -> supply -> aenv -> Prop :=
| e_sub__infer : forall S NM P Θ0,
    {{ S ↝ S ⊨ Θ0 ⊢[ NM | mode_ti | pskl_ghost ] P ⩽ P ⊣ Θ0 }}e
| e_sub__check : forall S0 S1 Θ0 Θ1 A B,
    pskl_ghost_free A -> pskl_ghost_free B ->
    guarded_pskl A -> guarded_pskl B ->
    e_consis_chk S0 Θ0 A B S1 Θ1 ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_ty | mode_tc | B ] A ⩽ B ⊣ Θ1 }}e
| e_sub__forall_r : forall α S0 S1 Θ0 Θ1 Ξ A B,
    pskl_ghost_free (pskl_all_syn B) ->
    a_suffix Ξ ->
    uniq (Ξ ++ Θ0) ->
    α `notin` S0 ->
    {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ a_sub_mode_ty | mode_tc | (open_pskl_wrt_pskl B (pskl_var_f α)) ]
       A ⩽ (open_pskl_wrt_pskl B (pskl_var_f α))
       ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θ1) }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_ty | mode_tc | (pskl_all_syn B) ]
       A ⩽ (pskl_all_syn B) ⊣ Θ1 }}e
| e_sub__univ_ghost_r : forall S Θ0 P,
    guarded_pskl P ->
    {{ S ↝ S ⊨ Θ0 ⊢[ a_sub_mode_sk | mode_tc | pskl_ghost ]
       P ⩽ (pskl_univ_ghost P) ⊣ Θ0 }}e
| e_sub__flex_mono : forall S0 S1 NM M P0 Θ0 Θ1 α Q,
    e_sub_flex S0 NM M P0 Θ0 nil α Q S1 Θ1 ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | (mode_fn M) | P0 ]
       (pskl_var_f α) ⩽ Q ⊣ Θ1 }}e
| e_sub__arrow : forall S0 S1 S2 NM M Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2,

    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ empty | empty | P0a ] P1 ∼ Q1 ⊣ Θ1 }}e ->
    {{ S1 ↝ S2 ⊨ Θ1 ⊢[ NM | M | P0b ] P2 ⩽ Q2 ⊣ Θ2 }}e ->
    {{ S0 ↝ S2 ⊨ Θ0 ⊢[ NM | (mode_fn M) | (pskl_arrow P0a P0b) ]
       (pskl_arrow P1 P2) ⩽ (pskl_arrow Q1 Q2) ⊣ Θ2 }}e
| e_sub__forall_l : forall α S0 S1 S2 NM M P0 Θ0 Θ1 P Q Ξ P1,
    M <> mode_ti ->
    (guarded_pskl P0 \/ P0 = pskl_ghost) ->
    α `notin` S0 ->
    {{ (add α S0) ↝ S1 ⊨ Θ0 ⊢ (open_pskl_wrt_pskl P (pskl_var_f α))
       ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ P1 }}e ->
    {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a ->
    {{ S1 ↝ S2 ⊨ (Ξ ++ Θ0) ⊢[ NM | M | P0 ]
       (open_pskl_wrt_pskl P P1) ⩽ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S2 ⊨ Θ0 ⊢[ NM | M | P0 ] (pskl_all_syn P) ⩽ Q ⊣ Θ1 }}e
| e_sub__ghost : forall S M Θ0 P0,

    M <> mode_ti ->
    {{ S ↝ S ⊨ Θ0 ⊢[ a_sub_mode_sk | M | P0 ] pskl_ghost ⩽ P0 ⊣ Θ0 }}e
| e_sub__univ_ghost_l : forall S0 S1 M Θ0 Θ1 P0 P Q,
    M <> mode_ti ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | M | P0 ]
       (pskl_univ_ghost P) ⩽ Q ⊣ Θ1 }}e

with e_sub_flex : supply -> a_sub_mode -> mode -> pskl -> aenv -> aenv -> atom
                  -> pskl -> supply -> aenv -> Prop :=
| e_sub_flex__solve : forall S0 S1 NM M P0 Θ0 Θ1 Ξ α0 α β Q,
    α `notin` S0 ->
    β `notin` add α S0 ->
    {{ (add β (add α S0)) ↝ S1 ⊨
       (Ξ ++ (α0 ~ abind_flex_mono_def
                    (ptyp_arrow (ptyp_var_f α) (ptyp_var_f β)))
           ++ (β ~ abind_flex_mono) ++ (α ~ abind_flex_mono) ++ Θ0)
       ⊢[ NM | (mode_fn M) | P0 ]
       (pskl_arrow (pskl_var_f α) (pskl_var_f β)) ⩽ Q ⊣ Θ1 }}e ->
    e_sub_flex S0 NM M P0 ((α0 ~ abind_flex_mono) ++ Θ0) Ξ α0 Q S1 Θ1
| e_sub_flex__assign : forall S0 S1 NM M P0 Θ0 Θ1 Ξ α β τ Q,

    {{ S0 ↝ S1 ⊨ (Ξ ++ Θ0)
       ⊢[ NM | (mode_fn M) | (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0) ]
       (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)) ⩽ Q ⊣ Θ1 }}e ->
    e_sub_flex S0 NM M P0 ((β ~ abind_flex_mono_def τ) ++ Θ0) Ξ α Q
      S1 ((β ~ abind_flex_mono_def τ) ++ Θ1)
| e_sub_flex__depend : forall S0 S1 NM M P0 Θ0 Θ1 Ξ α β Q,
    α <> β ->
    β `in` ftvar_in_pskl P0 ->
    e_sub_flex S0 NM M P0 Θ0 (Ξ ++ (β ~ abind_flex_mono)) α Q S1 Θ1 ->
    e_sub_flex S0 NM M P0 ((β ~ abind_flex_mono) ++ Θ0) Ξ α Q S1 Θ1
| e_sub_flex__skip : forall S0 S1 NM M P0 Θ0 Θ1 Ξ α β Q,

    α <> β ->
    β `notin` ftvar_in_pskl P0 ->
    e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
    e_sub_flex S0 NM M P0 ((β ~ abind_flex_mono) ++ Θ0) Ξ α Q
      S1 ((β ~ abind_flex_mono) ++ Θ1)
| e_sub_flex__skip_rigid : forall S0 S1 NM M P0 Θ0 Θ1 Ξ α β Q,

    α <> β ->
    β `notin` ftvar_in_pskl P0 ->
    e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
    e_sub_flex S0 NM M P0 ((β ~ abind_tvar) ++ Θ0) Ξ α Q
      S1 ((β ~ abind_tvar) ++ Θ1)
| e_sub_flex__skip_tm_var : forall S0 S1 NM M P0 Θ0 Θ1 Ξ α x Apay Q,

    e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
    e_sub_flex S0 NM M P0 ((x ~ abind_var_typ Apay) ++ Θ0) Ξ α Q
      S1 ((x ~ abind_var_typ Apay) ++ Θ1)
| e_sub_flex__skip_tm_skl : forall S0 S1 NM M P0 Θ0 Θ1 Ξ α x Qpay Q,

    e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1 ->
    e_sub_flex S0 NM M P0 ((x ~ abind_var_skl Qpay) ++ Θ0) Ξ α Q
      S1 ((x ~ abind_var_skl Qpay) ++ Θ1)
where "{{ S0 ↝ S1 ⊨ Θ ⊢[ N | m | P0 ] P ⩽ Q ⊣ Θ' }}e" :=
  (e_sub S0 N m P0 Θ P Q S1 Θ') : fresco_e_scope.

Scheme e_sub_mind      := Induction for e_sub      Sort Prop
  with e_sub_flex_mind := Induction for e_sub_flex Sort Prop.
Combined Scheme e_sub_sub_flex_mutind from e_sub_mind, e_sub_flex_mind.
