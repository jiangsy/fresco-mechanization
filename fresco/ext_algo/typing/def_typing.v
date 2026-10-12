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
Require Import src.fresco.ext_algo.typing.def_pat.

Set Implicit Arguments.

Open Scope fresco_e_scope.

Reserved Notation "{{ S0 ↝ S1 ⊨ Θ ⊢[ m ; P0 ] e ⦂ B ⊣ Θ' }}e"
  (at level 0, S1 at level 0, m at level 0, P0 at level 0, e at level 74,
   B at level 74, Θ' at level 74,
   format "'{{'  S0  ↝  S1  ⊨  Θ  ⊢[  m  ;  P0  ]  e  ⦂  B  ⊣  Θ'  '}}e'").

Inductive e_typing : supply -> mode -> aenv -> pskl -> exp -> ptyp -> supply
                     -> aenv -> Prop :=
| e_typing__unit : forall S0 S1 m Θ0 P0 A Θ1,
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_ty | m | P0 ]
       pskl_unit ⩽ (ptyp_to_pskl A) ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ m ; P0 ] exp_unit ⦂ A ⊣ Θ1 }}e
| e_typing__var : forall S0 S1 m Θ0 P0 x A B Θ1,
    binds x (abind_var_typ A) Θ0 ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_ty | m | P0 ]
       (ptyp_to_pskl A) ⩽ (ptyp_to_pskl B) ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ m ; P0 ] (exp_var_f x) ⦂ B ⊣ Θ1 }}e
| e_typing__anno : forall S0 S1 S2 m Θ0 P0 e A B Θ1 Θ2,
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl A) ] e ⦂ A ⊣ Θ1 }}e ->
    {{ S1 ↝ S2 ⊨ Θ1 ⊢[ a_sub_mode_ty | m | P0 ]
       (ptyp_to_pskl A) ⩽ (ptyp_to_pskl B) ⊣ Θ2 }}e ->
    {{ S0 ↝ S2 ⊨ Θ0 ⊢[ m ; P0 ] (exp_anno e A) ⦂ B ⊣ Θ2 }}e
| e_typing__freeze : forall S0 S1 S2 Θ0 e A B Θ1 Θ2,
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ mode_ti ; pskl_ghost ] e ⦂ B ⊣ Θ1 }}e ->
    e_consis_chk S1 Θ1 (ptyp_to_pskl B) (ptyp_to_pskl A) S2 Θ2 ->
    {{ S0 ↝ S2 ⊨ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl A) ]
       (exp_freeze e) ⦂ A ⊣ Θ2 }}e
| e_typing__abs : forall x S0 S1 S2 S3 m Θ0 Θ1 Θ2 P0 P Q αs A e B Ξ,
    m <> mode_tc ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e ->
    e_guess_mono S1 P S2 αs A ->
    a_suffix Ξ ->
    x `notin` S2 ->
    {{ (add x S2) ↝ S3 ⊨ ((x ~ abind_var_typ A) ++ αs ++ Θ1)
       ⊢[ (decr_mode m) ; Q ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ B
       ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ2) }}e ->
    {{ S0 ↝ S3 ⊨ Θ0 ⊢[ m ; P0 ] (exp_abs e) ⦂ (ptyp_arrow A B)
       ⊣ (Ξ ++ Θ2) }}e
| e_typing__abs_anno : forall x S0 S1 S2 S3 m Θ0 Θ1 Θ2 Θ3 P0 P Q A e B Ξ,
    m <> mode_tc ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q ⊣ Θ1 }}e ->
    e_consis_chk S1 Θ1 (ptyp_to_pskl A) P S2 Θ2 ->
    a_suffix Ξ ->
    x `notin` S2 ->
    {{ (add x S2) ↝ S3 ⊨ ((x ~ abind_var_typ A) ++ Θ2)
       ⊢[ (decr_mode m) ; Q ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ B
       ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ3) }}e ->
    {{ S0 ↝ S3 ⊨ Θ0 ⊢[ m ; P0 ] (exp_abs_anno A e) ⦂ (ptyp_arrow A B)
       ⊣ (Ξ ++ Θ3) }}e
| e_typing__abs_check_step : forall α S0 S1 Θ0 Θ1 A0 e A Ξ,
    a_suffix Ξ ->
    uniq (Ξ ++ Θ0) ->
    (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A) ->
    α `notin` ftvar_in_ptyp A ->
    α `notin` S0 ->
    {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ mode_tc ; (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) ]
       (exp_abs e) ⦂ (open_ptyp_wrt_ptyp A (ptyp_var_f α))
       ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θ1) }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl (ptyp_all A0)) ]
       (exp_abs e) ⦂ (ptyp_all A) ⊣ Θ1 }}e
| e_typing__abs_check_base : forall x S0 S1 S2 Θ0 Θ1 Θ2 A0 A B B1 e Ξ,
    {{ S0 ↝ S1 ⊨ Θ0 ⊲ (ptyp_to_pskl A0) ▹ (ptyp_to_pskl A)
       ⇢ (ptyp_to_pskl B) ⊣ Θ1 }}e ->
    a_suffix Ξ ->
    uniq (Ξ ++ Θ1) ->
    (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp B1) ->
    x `notin` S1 ->
    {{ (add x S1) ↝ S2 ⊨ ((x ~ abind_var_typ A) ++ Θ1)
       ⊢[ mode_tc ; (ptyp_to_pskl B) ]
       (open_exp_wrt_exp e (exp_var_f x)) ⦂ B1
       ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ2) }}e ->
    {{ S0 ↝ S2 ⊨ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl A0) ] (exp_abs e)
       ⦂ (ptyp_arrow A B1) ⊣ Θ2 }}e
| e_typing__abs_anno_check_step : forall α S0 S1 Θ0 Θ1 A0 Aan e A Ξ,
    a_suffix Ξ ->
    uniq (Ξ ++ Θ0) ->
    (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp A) ->
    α `notin` ftvar_in_ptyp A ->
    α `notin` S0 ->
    {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ mode_tc ; (ptyp_to_pskl (open_ptyp_wrt_ptyp A0 (ptyp_var_f α))) ]
       (exp_abs_anno Aan e) ⦂ (open_ptyp_wrt_ptyp A (ptyp_var_f α))
       ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θ1) }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl (ptyp_all A0)) ]
       (exp_abs_anno Aan e) ⦂ (ptyp_all A) ⊣ Θ1 }}e
| e_typing__abs_anno_check_base :
    forall x S0 S1 S2 S3 Θ0 Θ1 Θ2 Θ3 A0 A' A B B1 e Ξ,
    {{ S0 ↝ S1 ⊨ Θ0 ⊲ (ptyp_to_pskl A0) ▹ (ptyp_to_pskl A')
       ⇢ (ptyp_to_pskl B) ⊣ Θ1 }}e ->
    e_consis_chk S1 Θ1 (ptyp_to_pskl A') (ptyp_to_pskl A) S2 Θ2 ->
    a_suffix Ξ ->
    uniq (Ξ ++ Θ2) ->
    (forall γ, γ `in` dom Ξ -> γ `notin` ftvar_in_ptyp B1) ->
    x `notin` S2 ->
    {{ (add x S2) ↝ S3 ⊨ ((x ~ abind_var_typ A) ++ Θ2)
       ⊢[ mode_tc ; (ptyp_to_pskl B) ]
       (open_exp_wrt_exp e (exp_var_f x)) ⦂ B1
       ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ3) }}e ->
    {{ S0 ↝ S3 ⊨ Θ0 ⊢[ mode_tc ; (ptyp_to_pskl A0) ] (exp_abs_anno A e)
       ⦂ (ptyp_arrow A' B1) ⊣ Θ3 }}e
| e_typing__app : forall S0 S1 S2 S3 m Θ0 Θ1 Θ2 Θ3 P Q A A' B e1 e2,
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ mode_tc ; pskl_ghost ] e2 ⦂ P ⊣ Θ1 }}e ->
    {{ S1 ↝ S2 ⊨ Θ1 ⊢[ (mode_fn m) ; (pskl_arrow P Q) ] e1
       ⦂ (ptyp_arrow A B) ⊣ Θ2 }}e ->
    {{ S2 ↝ S3 ⊨ Θ2 ⊢[ mode_tc ; (ptyp_to_pskl A) ] e2 ⦂ A' ⊣ Θ3 }}e ->
    {{ S0 ↝ S3 ⊨ Θ0 ⊢[ m ; Q ] (exp_app e1 e2) ⦂ B ⊣ Θ3 }}e
where "{{ S0 ↝ S1 ⊨ Θ ⊢[ m ; P0 ] e ⦂ B ⊣ Θ' }}e" :=
  (e_typing S0 m Θ P0 e B S1 Θ') : fresco_e_scope.
