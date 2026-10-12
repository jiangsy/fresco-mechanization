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
Require Import src.fresco.ext_algo.subtyping.def_sub.

Set Implicit Arguments.

Open Scope fresco_e_scope.

Reserved Notation "{{ S0 ↝ S1 ⊨ Θ ⊲ P0 ▹ P ⇢ Q ⊣ Θ' }}e"
  (at level 0, S1 at level 0, P0 at level 74, P at level 74, Q at level 74,
   Θ' at level 74,
   format "'{{'  S0  ↝  S1  ⊨  Θ  ⊲  P0  ▹  P  ⇢  Q  ⊣  Θ'  '}}e'").

Inductive e_split : supply -> aenv -> pskl -> pskl -> pskl -> supply -> aenv
                    -> Prop :=
| e_split__arrow : forall S Θ0 P Q,
    {{ S ↝ S ⊨ Θ0 ⊲ (pskl_arrow P Q) ▹ P ⇢ Q ⊣ Θ0 }}e
| e_split__ghost : forall S Θ0,
    {{ S ↝ S ⊨ Θ0 ⊲ pskl_ghost ▹ pskl_ghost ⇢ pskl_ghost ⊣ Θ0 }}e
| e_split__flex : forall S0 S1 Θ0 Θ1 α β α1 Q,
    β `notin` S0 ->
    α1 `notin` add β S0 ->
    {{ (add α1 (add β S0)) ↝ S1
       ⊨ ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono) ++ Θ0)
       ⊢[ empty | empty | (pskl_arrow (pskl_var_f β) (pskl_var_f α1)) ]
         (pskl_var_f α) ∼ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊲ (pskl_var_f α) ▹ (pskl_var_f β) ⇢ (pskl_var_f α1)
       ⊣ Θ1 }}e
where "{{ S0 ↝ S1 ⊨ Θ ⊲ P0 ▹ P ⇢ Q ⊣ Θ' }}e" :=
  (e_split S0 Θ P0 P Q S1 Θ') : fresco_e_scope.

Reserved Notation "{{ S0 ↝ S1 ⊨ Θ ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ' }}e"
  (at level 0, S1 at level 0, m at level 0, P0 at level 0, e at level 74,
   Q at level 74, Θ' at level 74,
   format "'{{'  S0  ↝  S1  ⊨  Θ  ⊢ˢ[  m  ;  P0  ]  e  ⦂  Q  ⊣  Θ'  '}}e'").

Inductive e_pat : supply -> mode -> aenv -> pskl -> exp -> pskl -> supply
                  -> aenv -> Prop :=
| e_pat__unit : forall S0 S1 m Θ0 Θ1 P0 P,
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | m | P0 ] pskl_unit ⩽ P ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ m ; P0 ] exp_unit ⦂ P ⊣ Θ1 }}e
| e_pat__var : forall S0 S1 m Θ0 Θ1 P0 x A Q,
    binds x (abind_var_typ A) Θ0 ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | m | P0 ]
       (ptyp_to_pskl A) ⩽ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ m ; P0 ] (exp_var_f x) ⦂ Q ⊣ Θ1 }}e
| e_pat__var_skl : forall S0 S1 m Θ0 Θ1 P0 x P Q,
    binds x (abind_var_skl P) Θ0 ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | m | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ m ; P0 ] (exp_var_f x) ⦂ Q ⊣ Θ1 }}e
| e_pat__anno : forall S0 S1 m Θ0 Θ1 P0 e A Q,
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | m | P0 ]
       (ptyp_to_pskl A) ⩽ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ m ; P0 ] (exp_anno e A) ⦂ Q ⊣ Θ1 }}e
| e_pat__freeze : forall S0 S1 Θ0 e Q Θ1,
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ mode_ti ; pskl_ghost ] e ⦂ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ mode_tc ; pskl_ghost ] (exp_freeze e) ⦂ Q ⊣ Θ1 }}e
| e_pat__abs : forall x S0 S1 S2 m Θ0 Θ1 Θ2 P0 P Q0 e Q Ξ,

    m <> mode_tc ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q0 ⊣ Θ1 }}e ->
    a_suffix Ξ ->
    x `notin` S1 ->
    {{ (add x S1) ↝ S2 ⊨ ((x ~ abind_var_skl P) ++ Θ1) ⊢ˢ[ (decr_mode m) ; Q0 ]
       (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q
       ⊣ (Ξ ++ (x ~ abind_var_skl P) ++ Θ2) }}e ->
    {{ S0 ↝ S2 ⊨ Θ0 ⊢ˢ[ m ; P0 ] (exp_abs e) ⦂ (pskl_arrow P Q)
       ⊣ (Ξ ++ Θ2) }}e
| e_pat__abs_anno : forall x S0 S1 S2 S3 m Θ0 Θ1 Θ2 Θ3 P0 P Q0 A e Q Ξ,
    m <> mode_tc ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q0 ⊣ Θ1 }}e ->
    e_consis_chk S1 Θ1 (ptyp_to_pskl A) P S2 Θ2 ->
    a_suffix Ξ ->
    x `notin` S2 ->
    {{ (add x S2) ↝ S3 ⊨ ((x ~ abind_var_typ A) ++ Θ2)
       ⊢ˢ[ (decr_mode m) ; Q0 ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q
       ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ3) }}e ->
    {{ S0 ↝ S3 ⊨ Θ0 ⊢ˢ[ m ; P0 ] (exp_abs_anno A e)
       ⦂ (pskl_arrow (ptyp_to_pskl A) Q) ⊣ (Ξ ++ Θ3) }}e
| e_pat__abs_check : forall x S0 S1 Θ0 Θ1 e Q Ξ,
    a_suffix Ξ ->
    x `notin` S0 ->
    {{ (add x S0) ↝ S1 ⊨ ((x ~ abind_var_skl pskl_ghost) ++ Θ0)
       ⊢ˢ[ mode_tc ; pskl_ghost ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q
       ⊣ (Ξ ++ (x ~ abind_var_skl pskl_ghost) ++ Θ1) }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ mode_tc ; pskl_ghost ] (exp_abs e)
       ⦂ (pskl_univ_ghost (pskl_arrow pskl_ghost Q)) ⊣ (Ξ ++ Θ1) }}e
| e_pat__abs_anno_check : forall x S0 S1 Θ0 Θ1 A e Q Ξ,
    a_suffix Ξ ->
    x `notin` S0 ->
    {{ (add x S0) ↝ S1 ⊨ ((x ~ abind_var_typ A) ++ Θ0)
       ⊢ˢ[ mode_tc ; pskl_ghost ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q
       ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ1) }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ mode_tc ; pskl_ghost ] (exp_abs_anno A e)
       ⦂ (pskl_univ_ghost (pskl_arrow (ptyp_to_pskl A) Q)) ⊣ (Ξ ++ Θ1) }}e
| e_pat__app : forall S0 S1 S2 m Θ0 Θ1 Θ2 P0 Q0 P Q e1 e2,
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ mode_tc ; pskl_ghost ] e2 ⦂ P0 ⊣ Θ1 }}e ->
    {{ S1 ↝ S2 ⊨ Θ1 ⊢ˢ[ (mode_fn m) ; (pskl_arrow P0 Q0) ] e1
       ⦂ (pskl_arrow P Q) ⊣ Θ2 }}e ->
    {{ S0 ↝ S2 ⊨ Θ0 ⊢ˢ[ m ; Q0 ] (exp_app e1 e2) ⦂ Q ⊣ Θ2 }}e
where "{{ S0 ↝ S1 ⊨ Θ ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ' }}e" :=
  (e_pat S0 m Θ P0 e Q S1 Θ') : fresco_e_scope.
