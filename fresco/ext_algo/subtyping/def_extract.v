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
Require Import src.fresco.ext_algo.subtyping.def_look.
Require Import src.fresco.ext_algo.subtyping.def_solve.

Set Implicit Arguments.

Open Scope fresco_e_scope.

Reserved Notation "{{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q }}e"
  (at level 0, S1 at level 0, P at level 74, NM at level 0, α at level 0,
   m at level 0, P' at level 74, Ξ at level 74, Q at level 74,
   format "'{{'  S0  ↝  S1  ⊨  Θ0  ⊢  P  ⊳[  NM  ,  α  ,  m  ]  P'  ⤳  Ξ  ↪  Q  '}}e'").

Inductive e_extract : supply -> aenv -> a_sub_mode -> atom -> mode
                      -> pskl -> pskl -> supply -> aenv -> pskl -> Prop :=
| e_extract__solve : forall S0 S1 S2 S3 Θ0 NM α m P P' Ξ Ξs Ξ' C Q Q',
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
    {{ S1 ↝ S2 ⊨ (Ξ ++ Θ0) ⊩ C ⨾ pskl_ghost ⤳ Ξs ⨾ Q }}e ->
    e_guess S2 NM Q S3 Ξ' Q' ->
    {{ S0 ↝ S3 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ (Ξ ++ Ξs ++ Ξ') ↪ Q' }}e
where "{{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q }}e" :=
  (e_extract S0 Θ0 NM α m P P' S1 Ξ Q) : fresco_e_scope.
