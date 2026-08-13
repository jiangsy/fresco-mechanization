(** ext_algo — SPLITTING and SKELETON INFERENCE, threaded.  (M4, first half.)

    Two judgements, in the order [frost/algo/def_rules.v] states them:
    [e_split] (3 rows) and [e_pat] (10 rows).  [e_split] is not folded into
    [e_pat] even though it is tiny, because [e_typing] needs it too.

    ⭐ THE TERM BINDER IS DRAWN FROM THE SUPPLY, exactly as the type binders
    are.  That is the faithful reading: [type.ml] opens a lambda with
    [Bindlib.unbind], which invents a name from the same global source as
    every other fresh name.  It is also what retires the rows' side
    conditions — see below.

    ⚙ WHAT THIS RETIRES.  [a_pat]'s four binder rows were the tree's last
    COFINITE algorithmic rows until 2026-08-13; they are exists-fresh now, so
    the two encodings' [a_pat] and [e_pat] differ ONLY in the threading, and
    the bridge is structural rather than a family regeneration.  Each row's
    side condition

        x ∉ dom (Ξ ++ Θ1) ∪ dom Θ2 ∪ fvar_in_exp e

    splits three ways and every part is discharged by the supply:
    [dom Θ1] and [fvar_in_exp e] are covered by [S1] (coverage), while
    [dom Ξ] and [dom Θ2] are OUTPUT constraints and come from uniqueness of
    the premise's output [Ξ ++ (x ~ b) ++ Θ2].  So the whole condition
    collapses to [x ∉ S1] — Δ-drop ×2 and Δ-supply, in one line.

    ⚠️ [fvar_in_exp e] is the reason the bridge's coverage hypothesis names
    the SUBJECT's term variables and not only its type variables.  It costs
    nothing: a well-formed subject's free term variables are bound in [Θ0],
    and [dom Θ0 ⊆ ftvar_in_aenv Θ0] already, so at the entry point the
    condition is still [reflexivity].

    ⚙ [e_split]'s flexible row draws BOTH invented flexibles from the supply
    in sequence, so [β ∉ ftvar_in_aenv Θ0] and [α1 ∉ add β (ftvar_in_aenv Θ0)]
    are consequences rather than premises — the same Δ-supply payoff as
    [e_sub_flex__solve]. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_guess.
Require Import src.frost.ext_algo.def_consis.
Require Import src.frost.ext_algo.def_look.
Require Import src.frost.ext_algo.def_solve.
Require Import src.frost.ext_algo.def_extract.
Require Import src.frost.ext_algo.def_sub.

Set Implicit Arguments.

Open Scope frost_e_scope.

(* ===================================================================== *)
(*  Skeleton splitting  [Θ0 ⊲ split P0 = P→Q ⊣ Θ1], threaded              *)
(* ===================================================================== *)

(* ⚠️ [P0] sits at level 74, NOT 0, so that this notation and the [≈ᵘ] one
   (def_consis.v) share their prefix at the same entry — mismatch there fills
   the build with [notation-incompatible-prefix] and silently breaks one of
   them.  The [}}a] twin makes the same choice for the same reason. *)
Reserved Notation "{{ S0 ↝ S1 ⊨ Θ ⊲ P0 ▹ P ⇢ Q ⊣ Θ' }}e"
  (at level 0, S1 at level 0, P0 at level 74, P at level 74, Q at level 74,
   Θ' at level 74,
   format "'{{'  S0  ↝  S1  ⊨  Θ  ⊲  P0  ▹  P  ⇢  Q  ⊣  Θ'  '}}e'").

Inductive e_split : supply -> aenv -> pskl -> pskl -> pskl -> supply -> aenv
                    -> Prop :=
| e_split__arrow : forall S Θ0 P Q,
    {{ S ↝ S ⊨ Θ0 ⊲ (pskl_arrow P Q) ▹ P ⇢ Q ⊣ Θ0 }}e
| e_split__hole : forall S Θ0,
    {{ S ↝ S ⊨ Θ0 ⊲ pskl_hole ▹ pskl_hole ⇢ pskl_hole ⊣ Θ0 }}e
| e_split__flex : forall S0 S1 Θ0 Θ1 α β α1 Q,          (* split[α̂] = β̂→α1̂ *)
    (* ⭐ Δ-supply ×2.  [frost/algo]'s two premises state the invented pair
       fresh against [ftvar_in_aenv Θ0] — INPUT-only, so not part of TODO
       (1)'s census, but drawn in sequence from the supply they are theorems
       all the same, and the [α1 <> β] half is free. *)
    β `notin` S0 ->
    α1 `notin` add β S0 ->
    {{ (add α1 (add β S0)) ↝ S1
       ⊨ ((α1 ~ abind_flex_mono) ++ (β ~ abind_flex_mono) ++ Θ0)
       ⊢[ empty | empty | (pskl_arrow (pskl_var_f β) (pskl_var_f α1)) ]
         (pskl_var_f α) ∼ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊲ (pskl_var_f α) ▹ (pskl_var_f β) ⇢ (pskl_var_f α1)
       ⊣ Θ1 }}e
where "{{ S0 ↝ S1 ⊨ Θ ⊲ P0 ▹ P ⇢ Q ⊣ Θ' }}e" :=
  (e_split S0 Θ P0 P Q S1 Θ') : frost_e_scope.

(* ===================================================================== *)
(*  Algorithmic skeleton inference, threaded                              *)
(*  Rule for rule, in the order of frost/algo/def_rules.v.                *)
(* ===================================================================== *)

Reserved Notation "{{ S0 ↝ S1 ⊨ Θ ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ' }}e"
  (at level 0, S1 at level 0, m at level 0, P0 at level 0, e at level 74,
   Q at level 74, Θ' at level 74,
   format "'{{'  S0  ↝  S1  ⊨  Θ  ⊢ˢ[  m  ;  P0  ]  e  ⦂  Q  ⊣  Θ'  '}}e'").

Inductive e_pat : supply -> mode -> aenv -> pskl -> exp -> pskl -> supply
                  -> aenv -> Prop :=
| e_pat__unit : forall S0 S1 m Θ0 Θ1 P0 P,                    (* AP-Unit *)
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | m | P0 ] pskl_unit ⩽ P ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ m ; P0 ] exp_unit ⦂ P ⊣ Θ1 }}e
| e_pat__var : forall S0 S1 m Θ0 Θ1 P0 x A Q,      (* AP-Var (type-bound) *)
    binds x (abind_var_typ A) Θ0 ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | m | P0 ]
       (ptyp_to_pskl A) ⩽ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ m ; P0 ] (exp_var_f x) ⦂ Q ⊣ Θ1 }}e
| e_pat__var_skl : forall S0 S1 m Θ0 Θ1 P0 x P Q,  (* AP-Var (skl-bound) *)
    binds x (abind_var_skl P) Θ0 ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | m | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ m ; P0 ] (exp_var_f x) ⦂ Q ⊣ Θ1 }}e
| e_pat__anno : forall S0 S1 m Θ0 Θ1 P0 e A Q,                (* AP-Anno *)
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | m | P0 ]
       (ptyp_to_pskl A) ⩽ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ m ; P0 ] (exp_anno e A) ⦂ Q ⊣ Θ1 }}e
| e_pat__freeze : forall S0 S1 Θ0 e Q Θ1,                     (* AP-Freeze *)
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ mode_ti ; pskl_hole ] e ⦂ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ mode_tc ; pskl_hole ] (exp_freeze e) ⦂ Q ⊣ Θ1 }}e
| e_pat__abs : forall x S0 S1 S2 m Θ0 Θ1 Θ2 P0 P Q0 e Q Ξ,    (* AP-Abs *)
    (* Δ-drop ×2 and Δ-supply, in one line — see the header. *)
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
    m <> mode_tc ->                                        (* AP-AbsAnno *)
    {{ S0 ↝ S1 ⊨ Θ0 ⊲ P0 ▹ P ⇢ Q0 ⊣ Θ1 }}e ->
    e_consis_chk S1 Θ1 (ptyp_to_pskl A) P S2 Θ2 ->
    a_suffix Ξ ->
    x `notin` S2 ->
    {{ (add x S2) ↝ S3 ⊨ ((x ~ abind_var_typ A) ++ Θ2)
       ⊢ˢ[ (decr_mode m) ; Q0 ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q
       ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ3) }}e ->
    {{ S0 ↝ S3 ⊨ Θ0 ⊢ˢ[ m ; P0 ] (exp_abs_anno A e)
       ⦂ (pskl_arrow (ptyp_to_pskl A) Q) ⊣ (Ξ ++ Θ3) }}e
| e_pat__abs_check : forall x S0 S1 Θ0 Θ1 e Q Ξ,           (* AP-AbsCheck *)
    a_suffix Ξ ->
    x `notin` S0 ->
    {{ (add x S0) ↝ S1 ⊨ ((x ~ abind_var_skl pskl_hole) ++ Θ0)
       ⊢ˢ[ mode_tc ; pskl_hole ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q
       ⊣ (Ξ ++ (x ~ abind_var_skl pskl_hole) ++ Θ1) }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ mode_tc ; pskl_hole ] (exp_abs e)
       ⦂ (pskl_tophole (pskl_arrow pskl_hole Q)) ⊣ (Ξ ++ Θ1) }}e
| e_pat__abs_anno_check : forall x S0 S1 Θ0 Θ1 A e Q Ξ, (* AP-AbsAnnoCheck *)
    a_suffix Ξ ->
    x `notin` S0 ->
    {{ (add x S0) ↝ S1 ⊨ ((x ~ abind_var_typ A) ++ Θ0)
       ⊢ˢ[ mode_tc ; pskl_hole ] (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q
       ⊣ (Ξ ++ (x ~ abind_var_typ A) ++ Θ1) }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ mode_tc ; pskl_hole ] (exp_abs_anno A e)
       ⦂ (pskl_tophole (pskl_arrow (ptyp_to_pskl A) Q)) ⊣ (Ξ ++ Θ1) }}e
| e_pat__app : forall S0 S1 S2 m Θ0 Θ1 Θ2 P0 Q0 P Q e1 e2,     (* AP-App *)
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ˢ[ mode_tc ; pskl_hole ] e2 ⦂ P0 ⊣ Θ1 }}e ->
    {{ S1 ↝ S2 ⊨ Θ1 ⊢ˢ[ (mode_fn m) ; (pskl_arrow P0 Q0) ] e1
       ⦂ (pskl_arrow P Q) ⊣ Θ2 }}e ->
    {{ S0 ↝ S2 ⊨ Θ0 ⊢ˢ[ m ; Q0 ] (exp_app e1 e2) ⦂ Q ⊣ Θ2 }}e
where "{{ S0 ↝ S1 ⊨ Θ ⊢ˢ[ m ; P0 ] e ⦂ Q ⊣ Θ' }}e" :=
  (e_pat S0 m Θ P0 e Q S1 Θ') : frost_e_scope.
