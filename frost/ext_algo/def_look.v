(** ext_algo — the CONSTRAINT-COLLECTION cluster, state-threaded.

    M3a of docs/HANDOFF-extractable-algo-encoding.md.  Taken before
    [a_sub]/[a_sub_flex] because the collection is CLOSED — [a_looksub] and
    [a_lookeq] call only each other — while [a_sub__forall_l] consumes a
    collection's output block [Ξ], so threading the subtyping walk first would
    leave a hole in the supply exactly where the collection deposits names.

    ⚙ NOTE THE SHAPE DIFFERENCE FROM M2.  The collection has NO OUTPUT
    CONTEXT: [Θ] goes in and nothing comes back, and the generated names leave
    in [Ξ].  So this cluster's invariants are [e_guess_mono]'s, not
    [e_assign]'s — growth, the block is in the output supply, the block is
    fresh for the input supply, hence [uniq Ξ] — and there is no domain upper
    bound to prove and no [uniq]-preservation obligation.

    ⭐ THE PAYOFF, and it is the same one M1 bought at [AT-Abs].
    [a_sub__forall_l] carries [uniq (Ξ ++ Θ0)] (frost/algo/def_rules.v:1256),
    flagged there as a prose-completion of the paper's "fresh" Ξ and needed
    because [a_lookeq]'s LE-FlexR and [a_guess_mono]'s hole rule "pick
    arbitrary names, so re-attaching Ξ needs the freshness stated".  Threaded,
    [uniq Ξ] is a theorem ([e_looksub_uniq]) and the block's freshness for the
    ambient context is another ([e_looksub_generated_fresh]) — so the premise
    becomes derivable, exactly as [AT-Abs]'s did.

    ⚠️ NO ROW HERE CONSTRAINS ITS OWN OUTPUT.  The collection's freshness side
    conditions are already INPUT-only ([β ∉ add α (ftvar_in_aenv Θ ∪ …)]), so
    unlike M2 this file retires no [Δ-drop] premise.  What it does is put the
    generated names under the supply's accounting, which is what (2) needs and
    what the [uniq] payoff above rests on. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.

Set Implicit Arguments.

Open Scope frost_e_scope.

(** The free variables of a constraint list.  ⚙ A fact about [frost]'s
    [a_cstrs] living in [ext_algo] only because this line of work leaves
    [frost/] alone; if a [frost]-side consumer ever appears, move it to
    [frost/def_shapes.v] beside the other cross-system meta-functions.

    It is needed because the collection's output [C] is fed to the SOLVING
    layer at a later supply ([a_extract]), so the bridge has to say what [C]
    can mention — and unlike the block [Ξ], that is not a statement about
    [dom]. *)
Definition ftvar_in_a_cstr (c : a_cstr) : atoms :=
  match c with
  | a_cstr_sub _ P => ftvar_in_pskl P
  | a_cstr_eq P    => ftvar_in_pskl P
  end.

Fixpoint ftvar_in_a_cstrs (C : a_cstrs) : atoms :=
  match C with
  | nil      => empty
  | c :: C'  => ftvar_in_a_cstr c `union` ftvar_in_a_cstrs C'
  end.

Lemma ftvar_in_a_cstrs_app : forall C1 C2,
  ftvar_in_a_cstrs (C1 ++ C2)
  [=] ftvar_in_a_cstrs C1 `union` ftvar_in_a_cstrs C2.
Proof.
  induction C1 as [ | c C1' IH ]; intros; simpl; [ fsetdec | ].
  rewrite IH. fsetdec.
Qed.

Reserved Notation "{{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e"
  (at level 0, S1 at level 0, P at level 74, α at level 0, m at level 0,
   P' at level 74, Ξ at level 74, C at level 74,
   format "'{{'  S0  ↝  S1  ⊨  Θ  ⊢  P  ≼[  α  ,  m  ]  P'  ⤳  Ξ  ⨾  C  '}}e'").
Reserved Notation "{{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e"
  (at level 0, S1 at level 0, P at level 74, α at level 0, P' at level 74,
   Ξ at level 74, C at level 74,
   format "'{{'  S0  ↝  S1  ⊨  Θ  ⊢  P  ∼[  α  ]  P'  ⤳  Ξ  ⨾  C  '}}e'").

(* ===================================================================== *)
(*  Rule for rule, and in the same ORDER, as                              *)
(*  frost/algo/def_rules.v:418-528.  Two kinds of difference only:        *)
(*    Δ-thread   the supply is passed along (the two ARROW rows)          *)
(*    Δ-supply   an exists-fresh side condition became [β ∉ S], and the   *)
(*               witness enters the supply for the premise                *)
(* ===================================================================== *)

Inductive e_looksub : supply -> aenv -> atom -> mode -> pskl -> pskl
                      -> supply -> aenv -> a_cstrs -> Prop :=
| e_looksub__var : forall S Θ α m P,                    (* LS-Var *)
    {{ S ↝ S ⊨ Θ ⊢ (pskl_var_f α) ≼[ α , m ] P ⤳ nil
       ⨾ (a_cstr_sub m P :: nil) }}e
| e_looksub__absent : forall S Θ α m P P',              (* LS-Absent *)
    α `notin` ftvar_in_pskl P ->
    {{ S ↝ S ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ nil ⨾ nil }}e
| e_looksub__vacuous : forall S Θ α m P,                (* LS-Vacuous *)
    {{ S ↝ S ⊨ Θ ⊢ P ≼[ α , m ] pskl_hole ⤳ nil ⨾ nil }}e
| e_looksub__check : forall S0 S1 Θ α A B Ξ C,          (* LS-Check *)
    pskl_ghost_free B ->
    A <> pskl_var_f α ->
    guarded_pskl A ->
    guarded_pskl B ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ A ∼[ α ] B ⤳ Ξ ⨾ C }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ A ≼[ α , mode_tc ] B ⤳ Ξ ⨾ C }}e
| e_looksub__forall_r : forall S0 S1 Θ α A B Ξ C β,     (* LS-ForallR — LEAKS *)
    (* Δ-supply.  The paper's side condition names [α], the context and both
       skeletons; a supply that covers the run holds all four. *)
    pskl_ghost_free (pskl_all_syn B) ->
    β `notin` S0 ->
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ) ⊢ A ≼[ α , mode_tc ]
       (open_pskl_wrt_pskl B (pskl_var_f β)) ⤳ Ξ ⨾ C }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ A ≼[ α , mode_tc ] (pskl_all_syn B) ⤳ Ξ ⨾ C }}e
| e_looksub__arrow : forall S0 S1 S2 Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2, (* LS-Arrow *)
    (* Δ-thread — ⭐ this is the row that makes [uniq (Ξ1 ++ Ξ2)] a theorem *)
    {{ S0 ↝ S1 ⊨ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}e ->
    {{ S1 ↝ S2 ⊨ Θ ⊢ P2 ≼[ α , m ] P2' ⤳ Ξ2 ⨾ C2 }}e ->
    {{ S0 ↝ S2 ⊨ Θ ⊢ (pskl_arrow P1 P2) ≼[ α , (mode_fn m) ]
       (pskl_arrow P1' P2') ⤳ (Ξ1 ++ Ξ2) ⨾ (C1 ++ C2) }}e
| e_looksub__forall_l : forall S0 S1 Θ α m P P' Ξ C β,  (* LS-ForallL — LEAKS *)
    β `notin` S0 ->
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
       ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_all_syn P) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e
| e_looksub__univ_ghost_l : forall S0 S1 Θ α m P P' Ξ C, (* LS-UnivGhostL *)
    {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_tophole P) ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e

with e_lookeq : supply -> aenv -> atom -> pskl -> pskl
                -> supply -> aenv -> a_cstrs -> Prop :=
| e_lookeq__var : forall S Θ α P,                       (* LE-Var *)
    {{ S ↝ S ⊨ Θ ⊢ (pskl_var_f α) ∼[ α ] P ⤳ nil
       ⨾ (a_cstr_eq P :: nil) }}e
| e_lookeq__absent : forall S Θ α P P',                 (* LE-Absent *)
    α `notin` ftvar_in_pskl P ->
    {{ S ↝ S ⊨ Θ ⊢ P ∼[ α ] P' ⤳ nil ⨾ nil }}e
| e_lookeq__vacuous : forall S Θ α P,                   (* LE-Vacuous *)
    {{ S ↝ S ⊨ Θ ⊢ P ∼[ α ] pskl_hole ⤳ nil ⨾ nil }}e
| e_lookeq__flex_r : forall S Θ α P β α1,               (* LE-FlexR *)
    (* Δ-supply.  ⭐ THE ONLY GENERATING ROW of the cluster — the paper's
       "fresh γ̂" (algorithmic.tex:1204).  Everything the old side condition
       named ([α], [β], the context, the subject) is in the supply. *)
    α1 `notin` S ->
    P <> pskl_var_f α ->
    α `in` ftvar_in_pskl P ->
    {{ S ↝ (add α1 S) ⊨ Θ ⊢ P ∼[ α ] (pskl_var_f β)
       ⤳ ((α1 ~ abind_flex_mono) ++ nil)
       ⨾ (a_cstr_eq (pskl_var_f α1) :: nil) }}e
| e_lookeq__arrow : forall S0 S1 S2 Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2, (* LE-Arrow *)
    (* Δ-thread *)
    {{ S0 ↝ S1 ⊨ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}e ->
    {{ S1 ↝ S2 ⊨ Θ ⊢ P2 ∼[ α ] P2' ⤳ Ξ2 ⨾ C2 }}e ->
    {{ S0 ↝ S2 ⊨ Θ ⊢ (pskl_arrow P1 P2) ∼[ α ] (pskl_arrow P1' P2')
       ⤳ (Ξ1 ++ Ξ2) ⨾ (C1 ++ C2) }}e
| e_lookeq__forall_inh : forall S0 S1 Θ α P P' Ξ C β,   (* LE-ForallInh — LEAKS *)
    β `notin` S0 ->
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
       ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ]
       (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ ⨾ C }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_all_syn P) ∼[ α ] (pskl_all_syn P') ⤳ Ξ ⨾ C }}e
| e_lookeq__forall_syn : forall S0 S1 Θ α P P' Ξ C β,   (* LE-ForallSyn — LEAKS *)
    β `notin` S0 ->
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
       ⊢ (open_pskl_wrt_pskl P (pskl_var_f β)) ∼[ α ]
       (pskl_tophole P') ⤳ Ξ ⨾ C }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_all_syn P) ∼[ α ] (pskl_tophole P') ⤳ Ξ ⨾ C }}e
| e_lookeq__univ_ghost : forall S0 S1 Θ α P P' Ξ C,     (* LE-UnivGhost *)
    {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_tophole P) ∼[ α ] (pskl_tophole P') ⤳ Ξ ⨾ C }}e
| e_lookeq__univ_ghost1 : forall S0 S1 Θ α P P' Ξ C β,  (* LE-UnivGhost1 — LEAKS *)
    β `notin` S0 ->
    {{ (add β S0) ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ)
       ⊢ (pskl_tophole P) ∼[ α ]
       (open_pskl_wrt_pskl P' (pskl_var_f β)) ⤳ Ξ ⨾ C }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_tophole P) ∼[ α ] (pskl_all_syn P') ⤳ Ξ ⨾ C }}e
| e_lookeq__univ_ghost2 : forall S0 S1 Θ α P P' Ξ C,    (* LE-UnivGhost2 *)
    guarded_pskl P' ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ (pskl_tophole P) ∼[ α ] P' ⤳ Ξ ⨾ C }}e
| e_lookeq__univ_ghost_r : forall S0 S1 Θ α P P' Ξ C,   (* LE-UnivGhostR *)
    P <> pskl_var_f α ->
    guarded_pskl P ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
    {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] (pskl_tophole P') ⤳ Ξ ⨾ C }}e
where "{{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e" :=
  (e_looksub S0 Θ α m P P' S1 Ξ C) : frost_e_scope
and "{{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e" :=
  (e_lookeq S0 Θ α P P' S1 Ξ C) : frost_e_scope.

Scheme e_looksub_mind := Induction for e_looksub Sort Prop
  with e_lookeq_mind  := Induction for e_lookeq  Sort Prop.
Combined Scheme e_looksub_lookeq_mutind
  from e_looksub_mind, e_lookeq_mind.
