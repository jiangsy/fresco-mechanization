(** ext_algo — the CONSTRAINT-SOLVING layer, state-threaded.

    M3b step 1 of docs/HANDOFF-extractable-algo-encoding.md: [a_solve_sub] /
    [a_solve_eq] (mutual, 21 rows) and [a_solve_cstr] (3 rows), which
    [a_extract] composes with the collection of M3a before handing the result
    to [a_sub__forall_l].

    ⭐⭐ THE TREE ALREADY MADE M1'S ARGUMENT HERE, AND FOR M1'S REASON.  The
    comment on [a_solve_sub__arrow] (fresco/algo/def_rules.v:683-693) says:

      "THE SIBLING PREMISE THREADS, [Ξ2 ++ Ξ1].  Both halves may now GENERATE
       names, and a guess avoids only what its own context mentions — run both
       at [Θ] and the two blocks can pick THE SAME atom, making [Ξ1 ++ Ξ2]
       non-uniq and silently conflating two independently-invented flexibles
       … Running the second half at [Ξ1 ++ Θ] makes disjointness DERIVABLE …
       and it is what the reference implementation does anyway (one global
       counter, never reused)."

    That is exactly the M1 finding — including the appeal to [type.ml]'s
    counter — reached independently, four rows earlier in the same file.  ⚙ So
    the tree carries TWO conventions for one problem: the solve layer and
    [a_extract] thread by hand (through the CONTEXT, as a stand-in for a
    supply), while [a_guess_mono__arrow] does not, which is what costs
    [AT-Abs] its [uniq] premise.  A supply is the uniform version of the
    device this layer already uses.

    ⚠️ THE CONTEXT THREADING STAYS.  It is not merely an avoid-set here:
    [a_solve_eq__flex_r] asks whether a variable is hatted ([a_flex_tvar Θ α]),
    so the second premise of an arrow row must SEE the flexibles the first one
    invented.  The supply is added ALONGSIDE it, not in place of it — and it
    is the supply, not the context, that will make [uniq (Ξ2 ++ Ξ1)] a
    theorem, because the context threading proves disjointness only via
    [a_guess_mono]'s avoid-input, i.e. only where a guess is what generated. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_guess.

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

(* ===================================================================== *)
(*  Rule for rule, in the order of fresco/algo/def_rules.v:577-745.        *)
(*    Δ-thread   the supply joins the CONTEXT threading already there     *)
(*    Δ-supply   an exists-fresh side condition became [β ∉ S]            *)
(*    Δ-guess    SE-FlexR calls [e_guess_mono]                            *)
(* ===================================================================== *)

Inductive e_solve_sub : supply -> aenv -> mode -> pskl -> pskl
                        -> supply -> aenv -> pskl -> Prop :=
| e_solve_sub__var : forall S Θ m α Q,                  (* SS-Var + SS-Flex *)
    {{ S ↝ S ⊨ Θ ⊢ₛ (pskl_var_f α) ≼[ m ] Q ⤳ nil ⨾ (pskl_var_f α) }}e
| e_solve_sub__forall_l : forall S0 S1 Θ m P Q Ξ P' β,  (* SS-ForallL *)
    (* Δ-supply.  ⭐ The old side condition's job — "the block generated below
       is apart from β, so the CLOSE does not capture it" — is now the
       supply's, and it holds for every generator, not only for a guess. *)
    β `notin` S0 ->
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
       ⊢ₛ (open_pskl_wrt_pskl P (pskl_var_f β)) ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₛ (pskl_all_syn P) ≼[ m ] Q
       ⤳ Ξ ⨾ (pskl_all_syn (close_pskl_wrt_pskl β P')) }}e
| e_solve_sub__univ_ghost_l : forall S0 S1 Θ m P Q Ξ P', (* SS-UnivGhostL *)
    {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₛ (pskl_univ_ghost P) ≼[ m ] Q ⤳ Ξ ⨾ (pskl_univ_ghost P') }}e
| e_solve_sub__vacuous : forall S Θ m P,                (* SS-Vacuous *)
    (* [paper-gap] SOLVE-DISPATCH GUARD — see [a_solve_sub__vacuous]. *)
    peel_l_off P ->
    {{ S ↝ S ⊨ Θ ⊢ₛ P ≼[ m ] pskl_ghost ⤳ nil ⨾ P }}e
| e_solve_sub__check : forall S0 S1 Θ P Q Ξ P',         (* SS-Check *)
    pskl_ghost_free Q ->
    guarded_pskl P ->
    guarded_pskl Q ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ mode_tc ] Q ⤳ Ξ ⨾ P' }}e
| e_solve_sub__forall_r : forall S0 S1 Θ P B Ξ P' β,    (* SS-ForallR *)
    (* Δ-supply.  ⚠️ NO CLOSE here, by design: β may legitimately ESCAPE into
       [P'] (def_rules.v:625-638).  Threading changes nothing about that —
       the supply records that β was spent, which is all it ever claims. *)
    pskl_ghost_free (pskl_all_syn B) ->
    (* [paper-gap] SOLVE-DISPATCH GUARD — see [a_solve_sub__forall_r]. *)
    solve_l_off P ->
    β `notin` S0 ->
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ mode_tc ]
       (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ P' }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ P' }}e
| e_solve_sub__arrow : forall S0 S1 S2 Θ m P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2', (* SS-Arrow *)
    (* Δ-thread — the supply joins the context threading this row already has *)
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ P1' }}e ->
    {{ S1 ↝ S2 ⊨ (Ξ1 ++ Θ) ⊢ₛ P2 ≼[ m ] Q2 ⤳ Ξ2 ⨾ P2' }}e ->
    {{ S0 ↝ S2 ⊨ Θ ⊢ₛ (pskl_arrow P1 P2) ≼[ (mode_fn m) ] (pskl_arrow Q1 Q2)
       ⤳ (Ξ2 ++ Ξ1) ⨾ (pskl_arrow P1' P2') }}e
| e_solve_sub__ghost_l_fn : forall S0 S1 S2 Θ m Q1 Q2 Ξ1 Ξ2 P1' P2', (* SS-GhostLF *)
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ pskl_ghost ∼ Q1 ⤳ Ξ1 ⨾ P1' }}e ->
    {{ S1 ↝ S2 ⊨ (Ξ1 ++ Θ) ⊢ₛ pskl_ghost ≼[ m ] Q2 ⤳ Ξ2 ⨾ P2' }}e ->
    {{ S0 ↝ S2 ⊨ Θ ⊢ₛ pskl_ghost ≼[ (mode_fn m) ] (pskl_arrow Q1 Q2)
       ⤳ (Ξ2 ++ Ξ1) ⨾ (pskl_univ_ghost (pskl_arrow P1' P2')) }}e
| e_solve_sub__ghost_l : forall S Θ B,                  (* SS-GhostL *)
    pskl_ghost_free B ->
    guarded_pskl B ->
    {{ S ↝ S ⊨ Θ ⊢ₛ pskl_ghost ≼[ mode_tc ] B ⤳ nil ⨾ (pskl_univ_ghost B) }}e

with e_solve_eq : supply -> aenv -> pskl -> pskl -> supply -> aenv -> pskl -> Prop :=
| e_solve_eq__unit : forall S Θ,                        (* SE-Unit *)
    {{ S ↝ S ⊨ Θ ⊢ₑ pskl_unit ∼ pskl_unit ⤳ nil ⨾ pskl_unit }}e
| e_solve_eq__var : forall S Θ α Q,                     (* SE-Var + SE-FlexL *)
    {{ S ↝ S ⊨ Θ ⊢ₑ (pskl_var_f α) ∼ Q ⤳ nil ⨾ (pskl_var_f α) }}e
| e_solve_eq__flex_r : forall S0 S1 Θ α P Ξ A,          (* SE-FlexR *)
    (* Δ-guess — the layer's ONLY generating row, and the authors' repair:
       the accumulated pattern is handed through [guess^TY] so each ghost
       becomes a fresh flexible (def_rules.v:694-720). *)
    a_flex_tvar Θ α ->
    a_non_flex Θ P ->
    nonghost_pskl P ->
    e_guess_mono S0 P S1 Ξ A ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ (pskl_var_f α) ⤳ Ξ ⨾ (ptyp_to_pskl A) }}e
| e_solve_eq__ghost_l : forall S Θ Q,                    (* SE-GhostL *)
    {{ S ↝ S ⊨ Θ ⊢ₑ pskl_ghost ∼ Q ⤳ nil ⨾ Q }}e
| e_solve_eq__ghost_r : forall S Θ P,                    (* SE-VacuousR *)
    {{ S ↝ S ⊨ Θ ⊢ₑ P ∼ pskl_ghost ⤳ nil ⨾ P }}e
| e_solve_eq__arrow : forall S0 S1 S2 Θ P1 P2 Q1 Q2 Ξ1 Ξ2 P1' P2', (* SE-Arrow *)
    (* Δ-thread *)
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ P1' }}e ->
    {{ S1 ↝ S2 ⊨ (Ξ1 ++ Θ) ⊢ₑ P2 ∼ Q2 ⤳ Ξ2 ⨾ P2' }}e ->
    {{ S0 ↝ S2 ⊨ Θ ⊢ₑ (pskl_arrow P1 P2) ∼ (pskl_arrow Q1 Q2)
       ⤳ (Ξ2 ++ Ξ1) ⨾ (pskl_arrow P1' P2') }}e
| e_solve_eq__forall : forall S0 S1 Θ P Q Ξ P' β,       (* SE-Forall *)
    β `notin` S0 ->
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
       ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f β))
       ∼ (open_pskl_wrt_pskl Q (pskl_var_f β)) ⤳ Ξ ⨾ P' }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_all_syn P) ∼ (pskl_all_syn Q)
       ⤳ Ξ ⨾ (pskl_all_syn (close_pskl_wrt_pskl β P')) }}e
| e_solve_eq__univ_ghost_both : forall S0 S1 Θ P Q Ξ P',   (* SE-UnivGhost *)
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_univ_ghost P) ∼ (pskl_univ_ghost Q)
       ⤳ Ξ ⨾ (pskl_univ_ghost P') }}e
| e_solve_eq__univ_ghost_l_all : forall S0 S1 Θ P Q Ξ P' β, (* SE-GhostForall *)
    β `notin` S0 ->
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ) ⊢ₑ (pskl_univ_ghost P)
       ∼ (open_pskl_wrt_pskl Q (pskl_var_f β)) ⤳ Ξ ⨾ P' }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_univ_ghost P) ∼ (pskl_all_syn Q)
       ⤳ Ξ ⨾ (pskl_all_syn (close_pskl_wrt_pskl β P')) }}e
| e_solve_eq__univ_ghost_l_guarded : forall S0 S1 Θ P Q Ξ P', (* SE-GhostGuarded *)
    guarded_pskl Q ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_univ_ghost P) ∼ Q ⤳ Ξ ⨾ P' }}e
| e_solve_eq__all_l_univ_ghost : forall S0 S1 Θ P Q Ξ P' β, (* SE-ForallGhost *)
    β `notin` S0 ->
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
       ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f β))
       ∼ (pskl_univ_ghost Q) ⤳ Ξ ⨾ P' }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ (pskl_all_syn P) ∼ (pskl_univ_ghost Q)
       ⤳ Ξ ⨾ (pskl_all_syn (close_pskl_wrt_pskl β P')) }}e
| e_solve_eq__univ_ghost_r_guarded : forall S0 S1 Θ P Q Ξ P', (* SE-GuardedGhost *)
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

(* ===================================================================== *)
(*  The constraint fold.  A separate [Inductive] (not mutual), and the    *)
(*  one place where the CONTEXT threading is forced rather than chosen:   *)
(*  the tail solves on the head's yield [P''], which mentions the         *)
(*  flexibles SE-FlexR invented, and a later [a_flex_tvar] check must see *)
(*  them (def_rules.v:770-776).                                           *)
(* ===================================================================== *)

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
    (* Δ-thread *)
    {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ1 ⨾ P'' }}e ->
    {{ S1 ↝ S2 ⊨ (Ξ1 ++ Θ) ⊩ C ⨾ P'' ⤳ Ξ2 ⨾ P' }}e ->
    {{ S0 ↝ S2 ⊨ Θ ⊩ (a_cstr_eq Q :: C) ⨾ P ⤳ (Ξ2 ++ Ξ1) ⨾ P' }}e
where "{{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}e" :=
  (e_solve_cstr S0 Θ C P S1 Ξ Q) : fresco_e_scope.
