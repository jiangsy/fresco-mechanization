(** ext_algo — the [assign] / [unifyvar] / [consistency] block, state-threaded.

    M2 of docs/HANDOFF-extractable-algo-encoding.md.  This is where the second
    encoding earns its keep: eight of the eleven rows that constrain their own
    OUTPUT live in this block ([def_rules.v:936,956,962,967,972,1030,1039,1046],
    each marked "prose-completion (Barendregt)"), and all eight lose the
    premise here.

    ⭐ WHY THE PREMISE WAS THERE, AND WHY THREADING RETIRES IT.  The walk
    STRIPS an entry off the context, runs its premise at the smaller context,
    and RE-ATTACHES the entry.  So the context — which is what the exists-fresh
    discipline uses as its avoid-set — temporarily SHRINKS, and the premise's
    run may reinvent the very name that is about to be put back.  Hence
    [β ∉ dom Θ1], a rule filtering what its own premise produced.  A supply
    does not shrink when the context does: the premise runs at the SAME [S],
    which still holds [β], so the collision is impossible rather than filtered.

    ⚠️⚠️ [def_rules.v:879-882] WARNS AGAINST EXACTLY THIS, and the warning is
    correct where it stands:

      "Do NOT reintroduce a used-name set [F] as a fourth index: it is a
       mech-only device the paper does not have, and it cannot coexist with
       the §13b argument, which needs [β ∉ F] — false at a premise running at
       [add β F]."

    It is an objection to putting a supply on THOSE rules, whose freshness
    premises are justified by [prop_swap.v] §13b's transposition argument;
    a supply and that argument cannot both be the justification.  Here there
    is nothing to coexist with — the premises are GONE, and what justifies the
    encoding is the supply invariant plus the bridge, not §13b.  ⚙ The other
    half of the warning ("the paper does not have it") is answered by the
    reference implementation, which does: [type.ml]'s global [counter].

    ⭐ AND [Assign-SolveM] LOSES TWO MORE PREMISES.  Its [uniq βs] and its
    "generated names avoid [α] and [dom (Ξ ++ Θ0)]" ([def_rules.v:896-898],
    itself flagged as a prose-completion) are both consequences of
    [e_guess_mono]'s supply invariants — the same payoff that made [AT-Abs]'s
    [uniq (αs ++ Θ1)] derivable at M1.  So this block goes from eight
    output-constraining premises plus two guess-block filters, to none. *)

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

Set Implicit Arguments.

Open Scope frost_e_scope.

(* The three judgement notations.  Each is its [}}a] twin with the supply
   movement prefixed and the delimiter changed, and nothing else — see
   ext_algo/notations.v for why that is load-bearing. *)
Reserved Notation "{{ S0 ↝ S1 ⊨ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ' }}e"
  (at level 0, S1 at level 0, Ξ at level 0, α at level 74, P at level 74, Θ' at level 74,
   format "'{{'  S0  ↝  S1  ⊨  Θ  ⊲[  Ξ  ]  α  ≔  P  ⊣  Θ'  '}}e'").
Reserved Notation "{{ S0 ↝ S1 ⊨ Θ ⊲ α ≈ᵘ β ⊣ Θ' }}e"
  (at level 0, S1 at level 0, α at level 74, β at level 74, Θ' at level 74,
   format "'{{'  S0  ↝  S1  ⊨  Θ  ⊲  α  ≈ᵘ  β  ⊣  Θ'  '}}e'").
Reserved Notation "{{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}e"
  (at level 0, S1 at level 0, Δ1 at level 0, Δ2 at level 0, P0 at level 0,
   P at level 74, Q at level 74, Θ' at level 74,
   format "'{{'  S0  ↝  S1  ⊨  Θ  ⊢[  Δ1  |  Δ2  |  P0  ]  P  ∼  Q  ⊣  Θ'  '}}e'").

(* ===================================================================== *)
(*  The mutual block.  Rule for rule, and in the same ORDER, as            *)
(*  frost/algo/def_rules.v:883-1146 — the two files are meant to be read   *)
(*  side by side, and a reordering would cost that.  Every difference is   *)
(*  marked [Δ-…]; there are exactly four kinds:                            *)
(*                                                                        *)
(*    Δ-thread   the supply is passed along (no other change)              *)
(*    Δ-drop     an output-freshness premise is GONE                       *)
(*    Δ-supply   an exists-fresh side condition became [α ∉ S]             *)
(*    Δ-guess    [Assign-SolveM] calls [e_guess_mono], losing two filters  *)
(* ===================================================================== *)

Inductive e_assign : supply -> aenv -> aenv -> atom -> pskl -> supply -> aenv -> Prop :=
| e_assign__univ_ghost_id : forall S Θ0 α,              (* Assign-UnivGhost-Id *)
    {{ S ↝ S ⊨ ((α ~ abind_flex_mono) ++ Θ0) ⊲[ nil ] α
       ≔ (pskl_tophole (pskl_var_f α)) ⊣ ((α ~ abind_flex_mono) ++ Θ0) }}e
| e_assign__solve_m : forall S0 S1 Θ0 Ξ α P βs τ,       (* Assign-SolveM *)
    (* Δ-guess: [uniq βs] and the "generated names avoid α and dom (Ξ ++ Θ0)"
       filter are both DERIVABLE here ([e_guess_mono_uniq],
       [e_guess_mono_generated_fresh]) and so are not premises. *)
    α `notin` ftvar_in_pskl P ->
    e_guess_mono S0 P S1 βs τ ->
    mono_ptyp τ ->
    {{ S0 ↝ S1 ⊨ ((α ~ abind_flex_mono) ++ Θ0) ⊲[ Ξ ] α ≔ P
       ⊣ ((α ~ abind_flex_mono_def τ) ++ βs ++ Ξ ++ Θ0) }}e
| e_assign__assign : forall S0 S1 Θ0 Θ1 Ξ α β τ P Q,    (* Assign-Assign *)
    (* Δ-drop: [β ∉ dom Θ1] *)
    a_flex_tvar ((β ~ abind_flex_mono_def τ) ++ Θ0) α ->
    {{ S0 ↝ S1 ⊨ (Ξ ++ Θ0) ⊢[ empty | empty
         | (subst_pskl_in_pskl (ptyp_to_pskl τ) β P) ]
       (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)) ∼ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ ((β ~ abind_flex_mono_def τ) ++ Θ0) ⊲[ Ξ ] α ≔ P
       ⊣ ((β ~ abind_flex_mono_def τ) ++ Θ1) }}e
| e_assign__depend : forall S0 S1 Θ0 Θ1 Ξ α β P,        (* Assign-Depend *)
    (* Δ-thread *)
    α <> β ->
    β `in` ftvar_in_pskl P ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ++ (β ~ abind_flex_mono) ] α ≔ P ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ ((β ~ abind_flex_mono) ++ Θ0) ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e
| e_assign__skip : forall S0 S1 Θ0 Θ1 Ξ α β P,          (* Assign-Skip *)
    (* Δ-drop: [β ∉ dom Θ1] *)
    α <> β ->
    β `notin` ftvar_in_pskl P ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ ((β ~ abind_flex_mono) ++ Θ0) ⊲[ Ξ ] α ≔ P
       ⊣ ((β ~ abind_flex_mono) ++ Θ1) }}e
| e_assign__skip_rigid : forall S0 S1 Θ0 Θ1 Ξ α β P,    (* Assign-SkipRigid *)
    (* Δ-drop: [β ∉ dom Θ1] *)
    β `notin` ftvar_in_pskl P ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ ((β ~ abind_tvar) ++ Θ0) ⊲[ Ξ ] α ≔ P
       ⊣ ((β ~ abind_tvar) ++ Θ1) }}e
| e_assign__skip_tm_var : forall S0 S1 Θ0 Θ1 Ξ α x A P, (* Assign-SkipTmVar *)
    (* Δ-drop: [x ∉ dom Θ1] *)
    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ ((x ~ abind_var_typ A) ++ Θ0) ⊲[ Ξ ] α ≔ P
       ⊣ ((x ~ abind_var_typ A) ++ Θ1) }}e
| e_assign__skip_tm_skl : forall S0 S1 Θ0 Θ1 Ξ α x Q P, (* Assign-SkipTmVar (skl) *)
    (* Δ-drop: [x ∉ dom Θ1] *)
    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ Ξ ] α ≔ P ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ ((x ~ abind_var_skl Q) ++ Θ0) ⊲[ Ξ ] α ≔ P
       ⊣ ((x ~ abind_var_skl Q) ++ Θ1) }}e

with e_unify : supply -> aenv -> atom -> atom -> supply -> aenv -> Prop :=
| e_unify__flex_id : forall S Θ0 α,                      (* Flex-Flex-Id *)
    a_flex_tvar Θ0 α ->
    {{ S ↝ S ⊨ Θ0 ⊲ α ≈ᵘ α ⊣ Θ0 }}e
| e_unify__flex_l : forall S Θ0 α β,                     (* Flex-Flex-L *)
    α <> β ->
    a_flex_tvar Θ0 β ->
    {{ S ↝ S ⊨ ((α ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β
       ⊣ ((α ~ abind_flex_mono_def (ptyp_var_f β)) ++ Θ0) }}e
| e_unify__flex_r : forall S Θ0 α β,                     (* Flex-Flex-R *)
    α <> β ->
    a_flex_tvar Θ0 α ->
    {{ S ↝ S ⊨ ((β ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β
       ⊣ ((β ~ abind_flex_mono_def (ptyp_var_f α)) ++ Θ0) }}e
| e_unify__flex_assign : forall S0 S1 Θ0 Θ1 α1 τ α β Q,  (* Flex-Flex-Assign *)
    (* Δ-drop: [α1 ∉ dom Θ1] *)
    a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) α ->
    a_flex_tvar ((α1 ~ abind_flex_mono_def τ) ++ Θ0) β ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ empty | empty
         | (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β))) ]
       (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α))) ∼ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ ((α1 ~ abind_flex_mono_def τ) ++ Θ0) ⊲ α ≈ᵘ β
       ⊣ ((α1 ~ abind_flex_mono_def τ) ++ Θ1) }}e
| e_unify__flex_skip : forall S0 S1 Θ0 Θ1 α1 α β,        (* Flex-Flex-Skip *)
    (* Δ-drop: [α1 ∉ dom Θ1] *)
    α1 <> α ->
    α1 <> β ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ ((α1 ~ abind_flex_mono) ++ Θ0) ⊲ α ≈ᵘ β
       ⊣ ((α1 ~ abind_flex_mono) ++ Θ1) }}e
| e_unify__skip_other : forall S0 S1 Θ0 Θ1 c b α β,      (* Flex-Flex-Skip' *)
    (* Δ-drop: [c ∉ dom Θ1] *)
    (b = abind_tvar \/
     (exists A, b = abind_var_typ A) \/
     (exists Q, b = abind_var_skl Q)) ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ ((c ~ b) ++ Θ0) ⊲ α ≈ᵘ β ⊣ ((c ~ b) ++ Θ1) }}e

with e_consis : atoms -> atoms -> supply -> aenv -> pskl -> pskl -> pskl
                -> supply -> aenv -> Prop :=
| e_consis__ghost : forall Δ1 Δ2 S Θ0 P0,                    (* Ghost *)
    Δ2 ∩ ftvar_in_pskl P0 [=] empty ->
    {{ S ↝ S ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] pskl_hole ∼ P0 ⊣ Θ0 }}e
| e_consis__unit : forall Δ1 Δ2 S Θ0,                        (* Unit *)
    {{ S ↝ S ⊨ Θ0 ⊢[ Δ1 | Δ2 | pskl_unit ] pskl_unit ∼ pskl_unit ⊣ Θ0 }}e
| e_consis__rigid : forall Δ1 Δ2 S Θ0 α,                     (* Rigid *)
    binds α abind_tvar Θ0 ->
    {{ S ↝ S ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f α) ]
       (pskl_var_f α) ∼ (pskl_var_f α) ⊣ Θ0 }}e
| e_consis__arrow : forall Δ1 Δ2 S0 S1 S2 Θ0 Θ1 Θ2 P0a P0b P1 P2 Q1 Q2, (* Arrow *)
    (* Δ-thread — beside [Θ], which this rule already threaded *)
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0a ] P1 ∼ Q1 ⊣ Θ1 }}e ->
    {{ S1 ↝ S2 ⊨ Θ1 ⊢[ Δ1 | Δ2 | P0b ] P2 ∼ Q2 ⊣ Θ2 }}e ->
    {{ S0 ↝ S2 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_arrow P0a P0b) ]
       (pskl_arrow P1 P2) ∼ (pskl_arrow Q1 Q2) ⊣ Θ2 }}e
(* Δ-supply, the three ∀ rows.  [a_consis]'s side condition names four things
   to avoid — [ftvar_in_aenv Θ0], [ftvar_in_pskl P0], [ftvar_in_pskl P], and
   the two bound-variable sets [Δ1]/[Δ2].  A supply that covers the run holds
   all of them, so [α ∉ S0] is the whole condition.  ⚠️ THIS IS WHY THE BRIDGE
   MUST ASSUME THE SUPPLY COVERS Δ1 AND Δ2 TOO, not merely the context and the
   skeletons: the bound-variable sets are not reachable from either. *)
| e_consis__forall_inh : forall Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α,  (* ForallInh *)
    α `notin` S0 ->
    {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ (add α Δ1) | (add α Δ2)
         | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ]
       (open_pskl_wrt_pskl P (pskl_var_f α)) ∼ Q
       ⊣ ((α ~ abind_tvar) ++ Θ1) }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_all_syn P0) ]
       (pskl_all_syn P) ∼ (pskl_all_syn (close_pskl_wrt_pskl α Q)) ⊣ Θ1 }}e
| e_consis__forall_syn : forall Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α,  (* ForallSyn *)
    α `notin` S0 ->
    {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ Δ1 | (add α Δ2) | (pskl_tophole P0) ]
       (open_pskl_wrt_pskl P (pskl_var_f α)) ∼ Q
       ⊣ ((α ~ abind_tvar) ++ Θ1) }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_tophole P0) ]
       (pskl_all_syn P) ∼ (pskl_all_syn (close_pskl_wrt_pskl α Q)) ⊣ Θ1 }}e
| e_consis__univ_ghost : forall Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q,    (* UnivGhost *)
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_tophole P0) ]
       (pskl_tophole P) ∼ (pskl_tophole Q) ⊣ Θ1 }}e
| e_consis__univ_ghost1 : forall Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q α, (* UnivGhost1 *)
    α `notin` S0 ->
    {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ (add α Δ1) | Δ2
         | (open_pskl_wrt_pskl P0 (pskl_var_f α)) ]
       (pskl_tophole P) ∼ Q
       ⊣ ((α ~ abind_tvar) ++ Θ1) }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_all_syn P0) ]
       (pskl_tophole P) ∼ (pskl_all_syn (close_pskl_wrt_pskl α Q)) ⊣ Θ1 }}e
| e_consis__univ_ghost2 : forall Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q,   (* UnivGhost2 *)
    guarded_pskl P0 ->
    a_non_flex Θ0 P0 ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] (pskl_tophole P) ∼ Q ⊣ Θ1 }}e
| e_consis__flex : forall Δ1 Δ2 S0 S1 Θ0 Θ1 α β,             (* Flex *)
    {{ S0 ↝ S1 ⊨ Θ0 ⊲ α ≈ᵘ β ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f β) ]
       (pskl_var_f α) ∼ (pskl_var_f α) ⊣ Θ1 }}e
| e_consis__flex_l : forall Δ1 Δ2 S0 S1 Θ0 Θ1 α P0,          (* FlexL *)
    a_non_flex Θ0 P0 ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] α ≔ P0 ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ]
       (pskl_var_f α) ∼ (pskl_var_f α) ⊣ Θ1 }}e
| e_consis__flex_r : forall Δ1 Δ2 S0 S1 Θ0 Θ1 α P,           (* FlexR *)
    a_non_flex Θ0 P ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊲[ nil ] α ≔ P ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_var_f α) ] P ∼ (pskl_var_f α) ⊣ Θ1 }}e
| e_consis__ghost_r : forall Δ1 Δ2 S Θ0 P,                   (* GhostR *)
    Δ1 ∩ ftvar_in_pskl P [=] empty ->
    {{ S ↝ S ⊨ Θ0 ⊢[ Δ1 | Δ2 | pskl_hole ] P ∼ P ⊣ Θ0 }}e
| e_consis__univ_ghost_r : forall Δ1 Δ2 S0 S1 Θ0 Θ1 P0 P Q,  (* UnivGhostR *)
    guarded_pskl P ->
    a_non_flex Θ0 P ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ1 }}e ->
    {{ S0 ↝ S1 ⊨ Θ0 ⊢[ Δ1 | Δ2 | (pskl_tophole P0) ] P ∼ Q ⊣ Θ1 }}e
where "{{ S0 ↝ S1 ⊨ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ' }}e" :=
  (e_assign S0 Θ Ξ α P S1 Θ') : frost_e_scope
and "{{ S0 ↝ S1 ⊨ Θ ⊲ α ≈ᵘ β ⊣ Θ' }}e" :=
  (e_unify S0 Θ α β S1 Θ') : frost_e_scope
and "{{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}e" :=
  (e_consis Δ1 Δ2 S0 Θ P0 P Q S1 Θ') : frost_e_scope.

(* The mutual induction scheme, mirroring [a_assign_unify_consis_mutind]. *)
Scheme e_assign_mind := Induction for e_assign Sort Prop
  with e_unify_mind  := Induction for e_unify  Sort Prop
  with e_consis_mind := Induction for e_consis Sort Prop.
Combined Scheme e_assign_unify_consis_mutind
  from e_assign_mind, e_unify_mind, e_consis_mind.
