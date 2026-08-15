(** ext_algo — the [assign] / [unifyvar] / [consistency] block as EXECUTABLE
    FUNCTIONS, by Bove–Capretta.  Phase 4 step 5: an [Equations] on the
    mutual orders of def_order.v §5, total at lc inputs over a defs-mono
    context (prop_termination.v §16).

    Result shape, dispatch discipline and obligation-tactic recipe are
    def_look_impl.v's; the reference dispatch orders are [join_sk]
    (type.ml:143-262), [join_var] (:299-336) and [assign] (:338-388).
    Rows the mech does not have (Con, Mod, kinds) are skipped, and rigid/flex
    is decided by CONTEXT LOOKUP where the OCaml matches on [TVar]/[MFlex]
    syntactically.

    ⭐ WHY ONE TAGGED BLOCK AND NOT A MUTUAL [with] (§8c.4, user directive
    2026-08-14; def_sub_impl.v is the template and carries the full
    story).  [Equations] does not derive unfolding equations for mutual
    [with] companions, and completeness needs them — the check-mode
    entry-point exhibit (prop_run_complete.v) is stuck exactly on this
    block's [e_consis_impl].  So: a tag [consis_call] distinguishes which
    judgement runs, the block recurses on a combined single-inductive
    order, and the public three keep their signatures as wrappers.  The
    two measured traps are honoured: the tag is the FIRST argument, and
    the shape dispatch that would expand the case tree (assign's special
    row, the consistency P0 × P matrix) lives in TERM-LEVEL convoy
    matches, so the derivation proves one equation per CLAUSE, not per
    leaf.  ⚠️ The block returns [consis_result] UNIFORMLY — a
    tag-dependent result type would extract through [Obj.magic] (§8 bar).
    The assign/unify rows put [pskl_unit] in the join field; their specs
    never read it, and the wrappers repack to [unify_result].

    ⚙ THE PRECONDITIONS ARE §16's, VERBATIM: local closure of the skeleton
    inputs and [aenv_defs_mono] of the context — the discipline that every
    definition payload is a MONOTYPE, which is what makes the substituted
    skeletons at [Assign-Assign]/[Flex-Flex-Assign] locally closed and lets
    [Arrow] hand the domain's output context to the codomain
    ([e_consis_defs_mono]).  All erased at extraction.

    ⚙ ONE RULE HAS NO type.ml COUNTERPART: [Assign-UnivGhost-Id]
    (def_consis.v:84) — at pattern [⫯α̂] against target [α̂] itself the paper
    answers identity where type.ml raises [Occurs] (:344).  The runner
    implements the rule (an inner convoy on [Ξ]/[P] inside the
    flexible-head clause; the α-test commutes with the shape test, so the
    dispatch is the two original rows' first-match verbatim), so the
    occurs-check test lives only on the [SolveM] path.

    ⚙ THE ∀ ROWS SPLIT THEIR PREMISE'S OUTPUT CONTEXT at the rigid marker
    they pushed ([split_tvar_head], the evidence-carrying [List.tl] of
    type.ml:200) — the premise's run is only a rule instance if the marker
    survived at the head, so the split is tested, not assumed. *)

Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.sub.prop_solve_sub.   (* lc_pskl_*_inv *)
Require Import src.frost.prop_coercions.
Require Import src.frost.prop_ln.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_uip.
Require Import src.frost.ext_algo.def_dec.
Require Import src.frost.ext_algo.def_guess.
Require Import src.frost.ext_algo.def_guess_impl.
Require Import src.frost.ext_algo.def_consis.
Require Import src.frost.ext_algo.def_order.
Require Import src.frost.ext_algo.prop_termination.

(* ⚠️ NO [Set Implicit Arguments] in an implementation file — see
   def_guess_impl.v's header. *)

(* ⭐ §8c.4 — the unfolding equations, derived against def_uip.v's
   Hedberg UIP so no axiom is incurred.  ⚠️ per-FILE flag. *)
Set Equations With UIP.

Open Scope frost_e_scope.

(* ===================================================================== *)
(*  §1  The results                                                       *)
(* ===================================================================== *)

(** [assign] and [unifyvar] return the same two things. *)
Record unify_result : Type := mk_unify_result {
  ur_supply : supply;
  ur_ctx    : aenv       (* Θ' — the updated context *)
}.

Record consis_result : Type := mk_consis_result {
  cs_supply : supply;
  cs_ctx    : aenv;      (* Θ' — the updated context *)
  cs_out    : pskl       (* Q — the join *)
}.

Definition assign_spec (S0 : supply) (Θ Ξ : aenv) (α : atom) (P : pskl)
    (r : unify_result) : Prop :=
  {{ S0 ↝ (ur_supply r) ⊨ Θ ⊲[ Ξ ] α ≔ P ⊣ (ur_ctx r) }}e.

Definition unify_spec (S0 : supply) (Θ : aenv) (α β : atom)
    (r : unify_result) : Prop :=
  {{ S0 ↝ (ur_supply r) ⊨ Θ ⊲ α ≈ᵘ β ⊣ (ur_ctx r) }}e.

Definition consis_spec (Δ1 Δ2 : atoms) (S0 : supply) (Θ : aenv)
    (P0 P : pskl) (r : consis_result) : Prop :=
  {{ S0 ↝ (cs_supply r) ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ (cs_out r)
     ⊣ (cs_ctx r) }}e.

(* ===================================================================== *)
(*  §1b  The call tag, and the combined order                             *)
(* ===================================================================== *)

(** Which judgement a combined call runs.  ⚙ DATA — it survives
    extraction; it is the dispatch datum that replaces the mutual
    [with].  ⚠️ [Type], not [Set]: the Δ-slots carry [atoms], metalib's
    set type, which lives above [Set]. *)
Inductive consis_call : Type :=
| consis_call_assign (Ξ : aenv) (α : atom) (P : pskl)
| consis_call_unify  (α β : atom)
| consis_call_consis (Δ1 Δ2 : atoms) (P0 P : pskl).

Derive NoConfusion for consis_call.

(** The spec, keyed by the tag over the UNIFORM result record — the
    assign/unify sides read only the first two fields. *)
Definition consis_call_spec (S0 : supply) (Θ : aenv) (c : consis_call)
    : consis_result -> Prop :=
  match c with
  | consis_call_assign Ξ α P => fun r =>
      assign_spec S0 Θ Ξ α P (mk_unify_result (cs_supply r) (cs_ctx r))
  | consis_call_unify α β => fun r =>
      unify_spec S0 Θ α β (mk_unify_result (cs_supply r) (cs_ctx r))
  | consis_call_consis Δ1 Δ2 P0 P => consis_spec Δ1 Δ2 S0 Θ P0 P
  end.

Definition consis_call_lc (c : consis_call) : Prop :=
  match c with
  | consis_call_assign _ _ P    => lc_pskl P
  | consis_call_unify _ _       => True
  | consis_call_consis _ _ P0 P => lc_pskl P0 /\ lc_pskl P
  end.

Definition consis_call_defs_mono (Θ : aenv) (c : consis_call) : Prop :=
  match c with
  | consis_call_assign Ξ _ _ => aenv_defs_mono (Ξ ++ Θ)
  | _                        => aenv_defs_mono Θ
  end.

(** def_order.v §5's mutual trio as ONE inductive over the tag — premise
    for premise the same.  The mutual trio stays canonical (totality lives
    on it); the injections below convert. *)
Inductive e_consis_call_order : supply -> aenv -> consis_call -> Prop :=
| e_consis_call_order__assign : forall S0 Θ Ξ α P,
    (* Assign-SolveM — the head is the target itself, undefined *)
    (forall Θ0,
       Θ = (α ~ abind_flex_mono) ++ Θ0 ->
       e_guess_mono_order S0 P) ->
    (* Assign-Assign — a DEFINED head is substituted away and dropped *)
    (forall β τ Θ0,
       Θ = (β ~ abind_flex_mono_def τ) ++ Θ0 ->
       e_consis_call_order S0 (Ξ ++ Θ0)
         (consis_call_consis empty empty
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)))) ->
    (* Assign-Depend / Assign-Skip — an undefined non-target head *)
    (forall β Θ0,
       Θ = (β ~ abind_flex_mono) ++ Θ0 ->
       e_consis_call_order S0 Θ0
         (consis_call_assign (Ξ ++ (β ~ abind_flex_mono)) α P)
       /\ e_consis_call_order S0 Θ0 (consis_call_assign Ξ α P)) ->
    (* Assign-SkipRigid *)
    (forall β Θ0,
       Θ = (β ~ abind_tvar) ++ Θ0 ->
       e_consis_call_order S0 Θ0 (consis_call_assign Ξ α P)) ->
    (* Assign-SkipTmVar, both payload sorts *)
    (forall x A Θ0,
       Θ = (x ~ abind_var_typ A) ++ Θ0 ->
       e_consis_call_order S0 Θ0 (consis_call_assign Ξ α P)) ->
    (forall x Q Θ0,
       Θ = (x ~ abind_var_skl Q) ++ Θ0 ->
       e_consis_call_order S0 Θ0 (consis_call_assign Ξ α P)) ->
    e_consis_call_order S0 Θ (consis_call_assign Ξ α P)

| e_consis_call_order__unify : forall S0 Θ α β,
    (* Flex-Flex-Assign — a defined head is substituted into both sides *)
    (forall α1 τ Θ0,
       Θ = (α1 ~ abind_flex_mono_def τ) ++ Θ0 ->
       e_consis_call_order S0 Θ0
         (consis_call_consis empty empty
            (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β)))
            (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α))))) ->
    (* Flex-Flex-Skip *)
    (forall α1 Θ0,
       Θ = (α1 ~ abind_flex_mono) ++ Θ0 ->
       e_consis_call_order S0 Θ0 (consis_call_unify α β)) ->
    (* Flex-Flex-Skip' — the three other binding sorts *)
    (forall c0 Θ0,
       Θ = (c0 ~ abind_tvar) ++ Θ0 ->
       e_consis_call_order S0 Θ0 (consis_call_unify α β)) ->
    (forall x A Θ0,
       Θ = (x ~ abind_var_typ A) ++ Θ0 ->
       e_consis_call_order S0 Θ0 (consis_call_unify α β)) ->
    (forall x Q Θ0,
       Θ = (x ~ abind_var_skl Q) ++ Θ0 ->
       e_consis_call_order S0 Θ0 (consis_call_unify α β)) ->
    e_consis_call_order S0 Θ (consis_call_unify α β)

| e_consis_call_order__consis : forall S0 Θ Δ1 Δ2 P0 P,
    (* Arrow — the sibling runs at the FIRST premise's output context *)
    (forall P0a P0b P1 P2,
       P0 = pskl_arrow P0a P0b -> P = pskl_arrow P1 P2 ->
       e_consis_call_order S0 Θ (consis_call_consis Δ1 Δ2 P0a P1)
       /\ (forall S1 Θ1 Q1,
             {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0a ] P1 ∼ Q1 ⊣ Θ1 }}e ->
             e_consis_call_order S1 Θ1 (consis_call_consis Δ1 Δ2 P0b P2))) ->
    (* ForallInh *)
    (forall P0' P1,
       P0 = pskl_all_syn P0' -> P = pskl_all_syn P1 ->
       e_consis_call_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (consis_call_consis
            (add (supply_fresh S0) Δ1) (add (supply_fresh S0) Δ2)
            (open_pskl_wrt_pskl P0' (pskl_var_f (supply_fresh S0)))
            (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0))))) ->
    (* ForallSyn *)
    (forall P0' P1,
       P0 = pskl_tophole P0' -> P = pskl_all_syn P1 ->
       e_consis_call_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (consis_call_consis Δ1 (add (supply_fresh S0) Δ2)
            (pskl_tophole P0')
            (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0))))) ->
    (* UnivGhost *)
    (forall P0' P1,
       P0 = pskl_tophole P0' -> P = pskl_tophole P1 ->
       e_consis_call_order S0 Θ (consis_call_consis Δ1 Δ2 P0' P1)) ->
    (* UnivGhost1 *)
    (forall P0' P1,
       P0 = pskl_all_syn P0' -> P = pskl_tophole P1 ->
       e_consis_call_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (consis_call_consis (add (supply_fresh S0) Δ1) Δ2
            (open_pskl_wrt_pskl P0' (pskl_var_f (supply_fresh S0)))
            (pskl_tophole P1))) ->
    (* UnivGhost2 — strip the subject's ⫯ against a guarded pattern *)
    (forall P1,
       P = pskl_tophole P1 ->
       e_consis_call_order S0 Θ (consis_call_consis Δ1 Δ2 P0 P1)) ->
    (* UnivGhostR — strip the pattern's ⫯ *)
    (forall P0',
       P0 = pskl_tophole P0' ->
       e_consis_call_order S0 Θ (consis_call_consis Δ1 Δ2 P0' P)) ->
    (* Flex — both sides the same flexible, pattern a variable *)
    (forall α β,
       P = pskl_var_f α -> P0 = pskl_var_f β ->
       e_consis_call_order S0 Θ (consis_call_unify α β)) ->
    (* FlexL — the subject variable is assigned the pattern *)
    (forall α,
       P = pskl_var_f α ->
       e_consis_call_order S0 Θ (consis_call_assign nil α P0)) ->
    (* FlexR — the pattern variable is assigned the subject *)
    (forall α,
       P0 = pskl_var_f α ->
       e_consis_call_order S0 Θ (consis_call_assign nil α P)) ->
    e_consis_call_order S0 Θ (consis_call_consis Δ1 Δ2 P0 P).

Derive Signature for e_consis_call_order.

(** The injections — the canonical mutual orders imply the combined one,
    so the runners' callers keep producing the §5 orders via
    [e_consis_order_total] and never see the tag. *)
Fixpoint e_assign_order_to_call S0 Θ Ξ α P
    (H : e_assign_order S0 Θ Ξ α P) {struct H}
  : e_consis_call_order S0 Θ (consis_call_assign Ξ α P) :=
  match H with
  | e_assign_order__intro _ _ _ _ _ Hg Has Hds Hrg Htv Hts =>
      e_consis_call_order__assign _ _ _ _ _
        Hg
        (fun β τ Θ0 E =>
           e_consis_order_to_call _ _ _ _ _ _ (Has β τ Θ0 E))
        (fun β Θ0 E =>
           match Hds β Θ0 E with
           | conj h1 h2 =>
               conj (e_assign_order_to_call _ _ _ _ _ h1)
                    (e_assign_order_to_call _ _ _ _ _ h2)
           end)
        (fun β Θ0 E =>
           e_assign_order_to_call _ _ _ _ _ (Hrg β Θ0 E))
        (fun x A Θ0 E =>
           e_assign_order_to_call _ _ _ _ _ (Htv x A Θ0 E))
        (fun x Q Θ0 E =>
           e_assign_order_to_call _ _ _ _ _ (Hts x Q Θ0 E))
  end
with e_unify_order_to_call S0 Θ α β
    (H : e_unify_order S0 Θ α β) {struct H}
  : e_consis_call_order S0 Θ (consis_call_unify α β) :=
  match H with
  | e_unify_order__intro _ _ _ _ Has Hsk Hr Htv Hts =>
      e_consis_call_order__unify _ _ _ _
        (fun α1 τ Θ0 E =>
           e_consis_order_to_call _ _ _ _ _ _ (Has α1 τ Θ0 E))
        (fun α1 Θ0 E =>
           e_unify_order_to_call _ _ _ _ (Hsk α1 Θ0 E))
        (fun c0 Θ0 E =>
           e_unify_order_to_call _ _ _ _ (Hr c0 Θ0 E))
        (fun x A Θ0 E =>
           e_unify_order_to_call _ _ _ _ (Htv x A Θ0 E))
        (fun x Q Θ0 E =>
           e_unify_order_to_call _ _ _ _ (Hts x Q Θ0 E))
  end
with e_consis_order_to_call Δ1 Δ2 S0 Θ P0 P
    (H : e_consis_order Δ1 Δ2 S0 Θ P0 P) {struct H}
  : e_consis_call_order S0 Θ (consis_call_consis Δ1 Δ2 P0 P) :=
  match H with
  | e_consis_order__intro _ _ _ _ _ _
      Harr Hfi Hfs Hug Hug1 Hug2 Hugr Hfx Hfl Hfr =>
      e_consis_call_order__consis _ _ _ _ _ _
        (fun P0a P0b P1 P2 E1 E2 =>
           match Harr P0a P0b P1 P2 E1 E2 with
           | conj h1 h2 =>
               conj (e_consis_order_to_call _ _ _ _ _ _ h1)
                    (fun S1 Θ1 Q1 Hrun =>
                       e_consis_order_to_call _ _ _ _ _ _
                         (h2 S1 Θ1 Q1 Hrun))
           end)
        (fun P0' P1 E1 E2 =>
           e_consis_order_to_call _ _ _ _ _ _ (Hfi P0' P1 E1 E2))
        (fun P0' P1 E1 E2 =>
           e_consis_order_to_call _ _ _ _ _ _ (Hfs P0' P1 E1 E2))
        (fun P0' P1 E1 E2 =>
           e_consis_order_to_call _ _ _ _ _ _ (Hug P0' P1 E1 E2))
        (fun P0' P1 E1 E2 =>
           e_consis_order_to_call _ _ _ _ _ _ (Hug1 P0' P1 E1 E2))
        (fun P1 E =>
           e_consis_order_to_call _ _ _ _ _ _ (Hug2 P1 E))
        (fun P0' E =>
           e_consis_order_to_call _ _ _ _ _ _ (Hugr P0' E))
        (fun α β E1 E2 =>
           e_unify_order_to_call _ _ _ _ (Hfx α β E1 E2))
        (fun α E =>
           e_assign_order_to_call _ _ _ _ _ (Hfl α E))
        (fun α E =>
           e_assign_order_to_call _ _ _ _ _ (Hfr α E))
  end.

(* ===================================================================== *)
(*  §2  The obligation tactic                                             *)
(* ===================================================================== *)

#[local] Hint Resolve supply_fresh_notin mem_true_in mem_false_notin
  inter_is_empty_sound flex_bound_ck_flex_tvar flex_bound_false_non_flex
  rigid_bound_ck_binds non_flex_ck_sound mono_ck_sound
  lc_pskl_all_syn_inv subst_pskl_in_pskl_lc_pskl subst_ptyp_in_ptyp_lc_ptyp
  mono_ptyp_to_pskl_lc ptyp_to_pskl_lc mono_ptyp_lc
  e_consis_defs_mono : consisdec.
#[local] Hint Constructors lc_pskl lc_ptyp guarded_pskl : consisdec.
(* ⚠️ The three judgements are deliberately NOT hinted: the re-attaching
   rows' conclusions are stated [(β ~ b) ++ Θ] while the clause patterns
   produce cons-form goals — a conversion the simple-apply behind
   [Hint Constructors] cannot make, and an [econstructor] Extern does not
   backtrack usefully inside [eauto]'s search.  The rule instance is built
   by the tactic's TRAILING step instead ([econstructor; eauto], where the
   [;]-composition does backtrack across the constructors). *)
#[local] Hint Extern 2 (non_flex_ck _ _ = true) => reflexivity : consisdec.
#[local] Hint Extern 4 (_ <> _) => congruence : consisdec.
(* ⚠️ [Forall_app_intro] must NOT be a bare [Hint Resolve]: on a
   [Forall _ ?l] goal with [?l] an evar-able variable it lets [eauto] split
   endlessly.  The assembly is deterministic, so it is an Extern. *)
#[local] Hint Extern 4 (Forall entry_def_mono _) =>
  repeat first [ assumption
               | apply Forall_app_intro
               | apply List.Forall_cons
               | apply List.Forall_nil ];
  auto using entry_def_mono_flex, entry_def_mono_tvar,
    entry_def_mono_var_typ, entry_def_mono_var_skl, entry_def_mono_def
  : consisdec.

#[local] Ltac select_shape_premises :=
  repeat match goal with
         | Hp : forall _ _ _ _ _, _ = _ -> _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ _ _ _ eq_refl eq_refl eq_refl)
                   | clear Hp ]
         | Hp : forall _ _ _, _ = _ -> _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ _ eq_refl eq_refl eq_refl)
                   | clear Hp ]
         | Hp : forall _ _ _ _, _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ _ _ eq_refl eq_refl) | clear Hp ]
         | Hp : forall _ _, _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ eq_refl eq_refl) | clear Hp ]
         | Hp : forall _, _ = _ -> _ = _ -> _ |- _ =>
             first [ specialize (Hp _ eq_refl eq_refl) | clear Hp ]
         | Hp : forall _ _ _, _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ _ eq_refl) | clear Hp ]
         | Hp : forall _ _, _ = _ -> _ |- _ =>
             first [ specialize (Hp _ _ eq_refl) | clear Hp ]
         | Hp : forall _, _ = _ -> _ |- _ =>
             first [ specialize (Hp _ eq_refl) | clear Hp ]
         | Hp : _ = _ -> _ |- _ =>
             first [ specialize (Hp eq_refl) | clear Hp ]
         | Hp : _ /\ _ |- _ => destruct Hp
         end.

#[local] Ltac saturate_lc :=
  repeat match goal with
         | Hlc : lc_pskl (pskl_arrow ?a ?b) |- _ =>
             lazymatch goal with
             | _ : lc_pskl a, _ : lc_pskl b |- _ => fail
             | _ => let Hx := fresh "Hlc0" in
                    assert (Hx := Hlc); apply lc_pskl_arrow_inv in Hx;
                    destruct Hx
             end
         | Hlc : lc_pskl (pskl_tophole ?a) |- _ =>
             lazymatch goal with
             | _ : lc_pskl a |- _ => fail
             | _ => let Hx := fresh "Hlc0" in
                    assert (Hx := Hlc); apply lc_pskl_tophole_inv in Hx
             end
         end.

(** The defs-mono hypothesis is consumed piecewise: split every app, invert
    every cons, and let [simpl] reduce the [entry_def_mono] payloads. *)
#[local] Ltac saturate_defs :=
  repeat match goal with
         | HF : Forall _ (_ ++ _) |- _ =>
             apply Forall_app in HF; destruct HF
         | HF : Forall _ (_ :: _) |- _ => inversion HF; subst; clear HF
         | HF : Forall _ (one _) |- _ => inversion HF; subst; clear HF
         end.

#[local] Ltac consis_impl_tac :=
  cbv zeta; intros;
  try match goal with
      | H : e_consis_call_order _ _ _ |- _ => inversion H; subst
      end;
  try match goal with
      | Hlc : lc_pskl (pskl_var_b _) |- _ => inversion Hlc
      end;
  unfold consis_call_spec, consis_call_lc, consis_call_defs_mono,
         assign_spec, unify_spec, consis_spec, guess_spec in *;
  (* the tag wrappers leave matches on a CONCRETE tag behind — iota them
     away before the saturation steps read the hypotheses *)
  cbv beta iota in *;
  repeat match goal with
         | Hc : cs_ctx _ = _ ++ _ |- _ => rewrite Hc in *; clear Hc
         end;
  repeat match goal with
         | Hb : _ && _ = true |- _ => apply andb_prop in Hb; destruct Hb
         | Hb : _ && _ = false |- _ =>
             apply andb_false_iff in Hb; destruct Hb
         end;
  select_shape_premises; saturate_defs; saturate_lc; simpl in *;
  (* a substituted VARIABLE reduces under simpl to an if-form (§8b's ⚠️) *)
  repeat match goal with
         | |- context [ if ?c then _ else _ ] => destruct c
         end;
  try congruence;
  try solve [ eauto 7 with consisdec ];
  solve [ econstructor; eauto 6 with consisdec ].

(* ===================================================================== *)
(*  §3  The block, ONE tagged [Equations]                                 *)
(* ===================================================================== *)

#[tactic="consis_impl_tac", derive(equations=yes,eliminator=no)]
Equations e_consis_call_impl (c : consis_call) (S0 : supply) (Θ : aenv)
    (Hlc : consis_call_lc c) (HD : consis_call_defs_mono Θ c)
    (H : e_consis_call_order S0 Θ c)
    : option (sig (consis_call_spec S0 Θ c)) by struct H :=

(* ------------------------------------------------------------ assign — *)

(* undefined flexible head.  ⭐ The [Assign-UnivGhost-Id] special row
   (pattern [⫯γ̂] at [Ξ = nil]) lives in an inner convoy: the α-test
   commutes with the shape test — both rows agree everywhere except the
   Id sub-case — so this is the two original rows' first-match. *)
| consis_call_assign Ξ α P, S0, ((β0, abind_flex_mono) :: Θ0),
  Hlc, HD, H =>
    match β0 == α with
    | left _ =>
        match Ξ as Ξ1 return Ξ = Ξ1
            -> option (sig (consis_call_spec S0
                              ((β0, abind_flex_mono) :: Θ0)
                              (consis_call_assign Ξ α P)))
        with
        | nil => fun EΞ =>
            match P as Pp return P = Pp
                -> option (sig (consis_call_spec S0
                                  ((β0, abind_flex_mono) :: Θ0)
                                  (consis_call_assign Ξ α P)))
            with
            | pskl_tophole (pskl_var_f γ) => fun EP =>
                match γ == α with
                | left _ =>                        (* Assign-UnivGhost-Id *)
                    Some (exist _ (mk_consis_result S0
                            ((β0 ~ abind_flex_mono) ++ Θ0) pskl_unit) _)
                | right _ =>                               (* Assign-SolveM *)
                    match sumbool_of_bool (mem α (ftvar_in_pskl P)) with
                    | left _ => None                       (* occurs *)
                    | right _ =>
                        let (rg, Hg) := e_guess_mono_impl S0 P _ in
                        match sumbool_of_bool (mono_ck (gr_type rg)) with
                        | right _ => None
                        | left _ =>
                            Some (exist _ (mk_consis_result (gr_supply rg)
                                    ((α ~ abind_flex_mono_def (gr_type rg))
                                       ++ gr_block rg ++ Ξ ++ Θ0)
                                    pskl_unit) _)
                        end
                    end
                end
            | _ => fun EP =>                               (* Assign-SolveM *)
                match sumbool_of_bool (mem α (ftvar_in_pskl P)) with
                | left _ => None                           (* occurs *)
                | right _ =>
                    let (rg, Hg) := e_guess_mono_impl S0 P _ in
                    match sumbool_of_bool (mono_ck (gr_type rg)) with
                    | right _ => None
                    | left _ =>
                        Some (exist _ (mk_consis_result (gr_supply rg)
                                ((α ~ abind_flex_mono_def (gr_type rg))
                                   ++ gr_block rg ++ Ξ ++ Θ0)
                                pskl_unit) _)
                    end
                end
            end eq_refl
        | _ :: _ => fun EΞ =>                              (* Assign-SolveM *)
            match sumbool_of_bool (mem α (ftvar_in_pskl P)) with
            | left _ => None                               (* occurs *)
            | right _ =>
                let (rg, Hg) := e_guess_mono_impl S0 P _ in
                match sumbool_of_bool (mono_ck (gr_type rg)) with
                | right _ => None
                | left _ =>
                    Some (exist _ (mk_consis_result (gr_supply rg)
                            ((α ~ abind_flex_mono_def (gr_type rg))
                               ++ gr_block rg ++ Ξ ++ Θ0) pskl_unit) _)
                end
            end
        end eq_refl
    | right _ =>                                  (* Depend / Skip walk *)
        match sumbool_of_bool (mem β0 (ftvar_in_pskl P)) with
        | left _ =>                                        (* Assign-Depend *)
            match e_consis_call_impl
                    (consis_call_assign (Ξ ++ (β0 ~ abind_flex_mono)) α P)
                    S0 Θ0 _ _ _ with
            | None => None
            | Some (exist _ r Hr) => Some (exist _ r _)
            end
        | right _ =>                                       (* Assign-Skip *)
            match e_consis_call_impl (consis_call_assign Ξ α P) S0 Θ0
                    _ _ _ with
            | None => None
            | Some (exist _ r Hr) =>
                Some (exist _ (mk_consis_result (cs_supply r)
                        ((β0 ~ abind_flex_mono) ++ cs_ctx r)
                        pskl_unit) _)
            end
        end
    end

(* defined flexible head — Assign-Assign *)
| consis_call_assign Ξ α P, S0, ((β0, abind_flex_mono_def τ) :: Θ0),
  Hlc, HD, H =>
    match sumbool_of_bool
            (flex_bound_ck ((β0, abind_flex_mono_def τ) :: Θ0) α) with
    | right _ => None
    | left _ =>
        match e_consis_call_impl
                (consis_call_consis empty empty
                   (subst_pskl_in_pskl (ptyp_to_pskl τ) β0 P)
                   (subst_pskl_in_pskl (ptyp_to_pskl τ) β0 (pskl_var_f α)))
                S0 (Ξ ++ Θ0) _ _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_consis_result (cs_supply r)
                    ((β0 ~ abind_flex_mono_def τ) ++ cs_ctx r)
                    pskl_unit) _)
        end
    end

(* rigid head — Assign-SkipRigid *)
| consis_call_assign Ξ α P, S0, ((β0, abind_tvar) :: Θ0), Hlc, HD, H =>
    match sumbool_of_bool (mem β0 (ftvar_in_pskl P)) with
    | left _ => None
    | right _ =>
        match e_consis_call_impl (consis_call_assign Ξ α P) S0 Θ0
                _ _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_consis_result (cs_supply r)
                    ((β0 ~ abind_tvar) ++ cs_ctx r) pskl_unit) _)
        end
    end

(* term-variable heads — Assign-SkipTmVar, both payload sorts *)
| consis_call_assign Ξ α P, S0, ((x, abind_var_typ A) :: Θ0), Hlc, HD, H =>
    match e_consis_call_impl (consis_call_assign Ξ α P) S0 Θ0 _ _ _ with
    | None => None
    | Some (exist _ r Hr) =>
        Some (exist _ (mk_consis_result (cs_supply r)
                ((x ~ abind_var_typ A) ++ cs_ctx r) pskl_unit) _)
    end
| consis_call_assign Ξ α P, S0, ((x, abind_var_skl Q) :: Θ0), Hlc, HD, H =>
    match e_consis_call_impl (consis_call_assign Ξ α P) S0 Θ0 _ _ _ with
    | None => None
    | Some (exist _ r Hr) =>
        Some (exist _ (mk_consis_result (cs_supply r)
                ((x ~ abind_var_skl Q) ++ cs_ctx r) pskl_unit) _)
    end
| consis_call_assign Ξ α P, S0, nil, Hlc, HD, H => None

(* ------------------------------------------------------------- unify — *)

| consis_call_unify α β, S0, nil, Hlc, HD, H => None
| consis_call_unify α β, S0, ((γ, abind_flex_mono) :: Θ0), Hlc, HD, H =>
    match α == β with
    | left _ =>                                      (* Flex-Flex-Id *)
        match sumbool_of_bool
                (flex_bound_ck ((γ, abind_flex_mono) :: Θ0) α) with
        | left _ =>
            Some (exist _ (mk_consis_result S0
                    ((γ, abind_flex_mono) :: Θ0) pskl_unit) _)
        | right _ => None
        end
    | right _ =>
        match γ == α with
        | left _ =>                                  (* Flex-Flex-L *)
            match sumbool_of_bool (flex_bound_ck Θ0 β) with
            | left _ =>
                Some (exist _ (mk_consis_result S0
                        ((γ ~ abind_flex_mono_def (ptyp_var_f β)) ++ Θ0)
                        pskl_unit) _)
            | right _ => None
            end
        | right _ =>
            match γ == β with
            | left _ =>                              (* Flex-Flex-R *)
                match sumbool_of_bool (flex_bound_ck Θ0 α) with
                | left _ =>
                    Some (exist _ (mk_consis_result S0
                            ((γ ~ abind_flex_mono_def (ptyp_var_f α))
                               ++ Θ0) pskl_unit) _)
                | right _ => None
                end
            | right _ =>                             (* Flex-Flex-Skip *)
                match e_consis_call_impl (consis_call_unify α β) S0 Θ0
                        _ _ _ with
                | None => None
                | Some (exist _ r Hr) =>
                    Some (exist _ (mk_consis_result (cs_supply r)
                            ((γ ~ abind_flex_mono) ++ cs_ctx r)
                            pskl_unit) _)
                end
            end
        end
    end
| consis_call_unify α β, S0, ((γ, abind_flex_mono_def τ) :: Θ0),
  Hlc, HD, H =>
    match α == β with
    | left _ =>                                      (* Flex-Flex-Id *)
        match sumbool_of_bool
                (flex_bound_ck ((γ, abind_flex_mono_def τ) :: Θ0) α) with
        | left _ =>
            Some (exist _ (mk_consis_result S0
                    ((γ, abind_flex_mono_def τ) :: Θ0) pskl_unit) _)
        | right _ => None
        end
    | right _ =>                                     (* Flex-Flex-Assign *)
        match sumbool_of_bool
                (flex_bound_ck ((γ, abind_flex_mono_def τ) :: Θ0) α
                 && flex_bound_ck ((γ, abind_flex_mono_def τ) :: Θ0) β) with
        | right _ => None
        | left _ =>
            match e_consis_call_impl
                    (consis_call_consis empty empty
                       (ptyp_to_pskl (subst_ptyp_in_ptyp τ γ (ptyp_var_f β)))
                       (ptyp_to_pskl (subst_ptyp_in_ptyp τ γ (ptyp_var_f α))))
                    S0 Θ0 _ _ _ with
            | None => None
            | Some (exist _ r Hr) =>
                Some (exist _ (mk_consis_result (cs_supply r)
                        ((γ ~ abind_flex_mono_def τ) ++ cs_ctx r)
                        pskl_unit) _)
            end
        end
    end
| consis_call_unify α β, S0, ((γ, abind_tvar) :: Θ0), Hlc, HD, H =>
    match α == β with                                (* Flex-Flex-Skip' *)
    | left _ =>
        match sumbool_of_bool
                (flex_bound_ck ((γ, abind_tvar) :: Θ0) α) with
        | left _ =>
            Some (exist _ (mk_consis_result S0 ((γ, abind_tvar) :: Θ0)
                    pskl_unit) _)
        | right _ => None
        end
    | right _ =>
        match e_consis_call_impl (consis_call_unify α β) S0 Θ0 _ _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_consis_result (cs_supply r)
                    ((γ ~ abind_tvar) ++ cs_ctx r) pskl_unit) _)
        end
    end
| consis_call_unify α β, S0, ((x, abind_var_typ A) :: Θ0), Hlc, HD, H =>
    match α == β with                                (* Flex-Flex-Skip' *)
    | left _ =>
        match sumbool_of_bool
                (flex_bound_ck ((x, abind_var_typ A) :: Θ0) α) with
        | left _ =>
            Some (exist _ (mk_consis_result S0
                    ((x, abind_var_typ A) :: Θ0) pskl_unit) _)
        | right _ => None
        end
    | right _ =>
        match e_consis_call_impl (consis_call_unify α β) S0 Θ0 _ _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_consis_result (cs_supply r)
                    ((x ~ abind_var_typ A) ++ cs_ctx r) pskl_unit) _)
        end
    end
| consis_call_unify α β, S0, ((x, abind_var_skl Q) :: Θ0), Hlc, HD, H =>
    match α == β with                                (* Flex-Flex-Skip' *)
    | left _ =>
        match sumbool_of_bool
                (flex_bound_ck ((x, abind_var_skl Q) :: Θ0) α) with
        | left _ =>
            Some (exist _ (mk_consis_result S0
                    ((x, abind_var_skl Q) :: Θ0) pskl_unit) _)
        | right _ => None
        end
    | right _ =>
        match e_consis_call_impl (consis_call_unify α β) S0 Θ0 _ _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_consis_result (cs_supply r)
                    ((x ~ abind_var_skl Q) ++ cs_ctx r) pskl_unit) _)
        end
    end

(* ------------------------------------------------------------ consis — *)

(* ⭐ ONE clause; the P0 × P matrix lives in the RHS as convoy-pattern
   matches (the §8c.4 leaf-explosion trap: as clause patterns the
   catch-all rows expand per constructor pair and the derivation proves
   one equation per LEAF).  The arm order is the original clause list's
   first-match order, [join_sk] type.ml:143-262: the hole rows first,
   then per-(P0,P) pair with the flexible-variable fallbacks. *)
| consis_call_consis Δ1 Δ2 P0 P, S0, Θ, Hlc, HD, H =>
  match P0 as P01 return P0 = P01
      -> option (sig (consis_call_spec S0 Θ
                        (consis_call_consis Δ1 Δ2 P0 P)))
  with
  (* U-GhostR — a hole pattern answers the subject *)
  | pskl_hole => fun EP0 =>
      match sumbool_of_bool (is_empty (inter Δ1 (ftvar_in_pskl P))) with
      | left _ => Some (exist _ (mk_consis_result S0 Θ P) _)
      | right _ => None
      end
  | pskl_unit => fun EP0 =>
      match P as P1 return P = P1
          -> option (sig (consis_call_spec S0 Θ
                            (consis_call_consis Δ1 Δ2 P0 P)))
      with
      (* U-Ghost — a hole subject answers the pattern *)
      | pskl_hole => fun EP =>
          match sumbool_of_bool (is_empty (inter Δ2 (ftvar_in_pskl P0)))
          with
          | left _ => Some (exist _ (mk_consis_result S0 Θ P0) _)
          | right _ => None
          end
      (* U-Unit *)
      | pskl_unit => fun EP =>
          Some (exist _ (mk_consis_result S0 Θ pskl_unit) _)
      (* U-FlexR at a unit pattern *)
      | pskl_var_f α0 => fun EP =>
          match sumbool_of_bool (flex_bound_ck Θ α0) with
          | left _ =>
              match e_consis_call_impl
                      (consis_call_assign nil α0 pskl_unit) S0 Θ _ _ _
              with
              | None => None
              | Some (exist _ r Hr) =>
                  Some (exist _ (mk_consis_result (cs_supply r) (cs_ctx r)
                          (pskl_var_f α0)) _)
              end
          | right _ => None
          end
      (* U-UnivGhost2 — strip the subject's ⫯ *)
      | pskl_tophole P1 => fun EP =>
          match e_consis_call_impl
                  (consis_call_consis Δ1 Δ2 pskl_unit P1) S0 Θ _ _ _ with
          | None => None
          | Some (exist _ r Hr) => Some (exist _ r _)
          end
      | _ => fun _ => None
      end eq_refl
  | pskl_var_f β0 => fun EP0 =>
      match P as P1 return P = P1
          -> option (sig (consis_call_spec S0 Θ
                            (consis_call_consis Δ1 Δ2 P0 P)))
      with
      (* U-Ghost *)
      | pskl_hole => fun EP =>
          match sumbool_of_bool (is_empty (inter Δ2 (ftvar_in_pskl P0)))
          with
          | left _ => Some (exist _ (mk_consis_result S0 Θ P0) _)
          | right _ => None
          end
      (* variables — U-Rigid / U-Flex / U-FlexR / U-FlexL, type.ml's
         order *)
      | pskl_var_f α0 => fun EP =>
          match α0 == β0 with
          | left _ =>
              match sumbool_of_bool (rigid_bound_ck Θ α0) with
              | left _ =>                                  (* U-Rigid *)
                  Some (exist _ (mk_consis_result S0 Θ (pskl_var_f α0)) _)
              | right _ =>                                 (* U-Flex (Id) *)
                  match e_consis_call_impl (consis_call_unify α0 β0) S0 Θ
                          _ _ _ with
                  | None => None
                  | Some (exist _ r Hr) =>
                      Some (exist _ (mk_consis_result (cs_supply r)
                              (cs_ctx r) (pskl_var_f α0)) _)
                  end
              end
          | right _ =>
              match sumbool_of_bool
                      (flex_bound_ck Θ α0 && flex_bound_ck Θ β0) with
              | left _ =>                                  (* U-Flex *)
                  match e_consis_call_impl (consis_call_unify α0 β0) S0 Θ
                          _ _ _ with
                  | None => None
                  | Some (exist _ r Hr) =>
                      Some (exist _ (mk_consis_result (cs_supply r)
                              (cs_ctx r) (pskl_var_f α0)) _)
                  end
              | right _ =>
                  match sumbool_of_bool (flex_bound_ck Θ β0) with
                  | left _ =>                              (* U-FlexR *)
                      match e_consis_call_impl
                              (consis_call_assign nil β0 (pskl_var_f α0))
                              S0 Θ _ _ _ with
                      | None => None
                      | Some (exist _ r Hr) =>
                          Some (exist _ (mk_consis_result (cs_supply r)
                                  (cs_ctx r) (pskl_var_f β0)) _)
                      end
                  | right _ =>
                      match sumbool_of_bool (flex_bound_ck Θ α0) with
                      | left _ =>                          (* U-FlexL *)
                          match e_consis_call_impl
                                  (consis_call_assign nil α0
                                     (pskl_var_f β0)) S0 Θ _ _ _ with
                          | None => None
                          | Some (exist _ r Hr) =>
                              Some (exist _ (mk_consis_result
                                      (cs_supply r) (cs_ctx r)
                                      (pskl_var_f α0)) _)
                          end
                      | right _ => None
                      end
                  end
              end
          end
      (* flexible-variable pattern against a non-variable subject —
         U-FlexR, with the ⫯-strip U-UnivGhost2 as the rigid fallback *)
      | pskl_tophole P1 => fun EP =>
          match sumbool_of_bool (flex_bound_ck Θ β0) with
          | left _ =>                                      (* U-FlexR *)
              match e_consis_call_impl
                      (consis_call_assign nil β0 (pskl_tophole P1))
                      S0 Θ _ _ _ with
              | None => None
              | Some (exist _ r Hr) =>
                  Some (exist _ (mk_consis_result (cs_supply r) (cs_ctx r)
                          (pskl_var_f β0)) _)
              end
          | right _ =>                                     (* U-UnivGhost2 *)
              match e_consis_call_impl
                      (consis_call_consis Δ1 Δ2 (pskl_var_f β0) P1)
                      S0 Θ _ _ _ with
              | None => None
              | Some (exist _ r Hr) => Some (exist _ r _)
              end
          end
      | pskl_unit => fun EP =>
          match sumbool_of_bool (flex_bound_ck Θ β0) with
          | left _ =>
              match e_consis_call_impl
                      (consis_call_assign nil β0 pskl_unit) S0 Θ _ _ _
              with
              | None => None
              | Some (exist _ r Hr) =>
                  Some (exist _ (mk_consis_result (cs_supply r) (cs_ctx r)
                          (pskl_var_f β0)) _)
              end
          | right _ => None
          end
      | pskl_arrow P1 P2 => fun EP =>
          match sumbool_of_bool (flex_bound_ck Θ β0) with
          | left _ =>
              match e_consis_call_impl
                      (consis_call_assign nil β0 (pskl_arrow P1 P2))
                      S0 Θ _ _ _ with
              | None => None
              | Some (exist _ r Hr) =>
                  Some (exist _ (mk_consis_result (cs_supply r) (cs_ctx r)
                          (pskl_var_f β0)) _)
              end
          | right _ => None
          end
      | pskl_all_syn P1 => fun EP =>
          match sumbool_of_bool (flex_bound_ck Θ β0) with
          | left _ =>
              match e_consis_call_impl
                      (consis_call_assign nil β0 (pskl_all_syn P1))
                      S0 Θ _ _ _ with
              | None => None
              | Some (exist _ r Hr) =>
                  Some (exist _ (mk_consis_result (cs_supply r) (cs_ctx r)
                          (pskl_var_f β0)) _)
              end
          | right _ => None
          end
      | _ => fun _ => None
      end eq_refl
  | pskl_arrow P0a P0b => fun EP0 =>
      match P as P1 return P = P1
          -> option (sig (consis_call_spec S0 Θ
                            (consis_call_consis Δ1 Δ2 P0 P)))
      with
      (* U-Ghost *)
      | pskl_hole => fun EP =>
          match sumbool_of_bool (is_empty (inter Δ2 (ftvar_in_pskl P0)))
          with
          | left _ => Some (exist _ (mk_consis_result S0 Θ P0) _)
          | right _ => None
          end
      (* U-FlexL at an arrow pattern *)
      | pskl_var_f α0 => fun EP =>
          match sumbool_of_bool (flex_bound_ck Θ α0) with
          | left _ =>
              match e_consis_call_impl
                      (consis_call_assign nil α0 (pskl_arrow P0a P0b))
                      S0 Θ _ _ _ with
              | None => None
              | Some (exist _ r Hr) =>
                  Some (exist _ (mk_consis_result (cs_supply r) (cs_ctx r)
                          (pskl_var_f α0)) _)
              end
          | right _ => None
          end
      (* U-Arrow *)
      | pskl_arrow P1 P2 => fun EP =>
          match e_consis_call_impl (consis_call_consis Δ1 Δ2 P0a P1)
                  S0 Θ _ _ _ with
          | None => None
          | Some (exist _ r1 Hr1) =>
              match e_consis_call_impl (consis_call_consis Δ1 Δ2 P0b P2)
                      (cs_supply r1) (cs_ctx r1) _ _ _ with
              | None => None
              | Some (exist _ r2 Hr2) =>
                  Some (exist _ (mk_consis_result (cs_supply r2)
                          (cs_ctx r2)
                          (pskl_arrow (cs_out r1) (cs_out r2))) _)
              end
          end
      (* U-UnivGhost2 *)
      | pskl_tophole P1 => fun EP =>
          match e_consis_call_impl
                  (consis_call_consis Δ1 Δ2 (pskl_arrow P0a P0b) P1)
                  S0 Θ _ _ _ with
          | None => None
          | Some (exist _ r Hr) => Some (exist _ r _)
          end
      | _ => fun _ => None
      end eq_refl
  | pskl_all_syn P0' => fun EP0 =>
      match P as P1 return P = P1
          -> option (sig (consis_call_spec S0 Θ
                            (consis_call_consis Δ1 Δ2 P0 P)))
      with
      (* U-Ghost *)
      | pskl_hole => fun EP =>
          match sumbool_of_bool (is_empty (inter Δ2 (ftvar_in_pskl P0)))
          with
          | left _ => Some (exist _ (mk_consis_result S0 Θ P0) _)
          | right _ => None
          end
      (* U-FlexL at a ∀ pattern *)
      | pskl_var_f α0 => fun EP =>
          match sumbool_of_bool (flex_bound_ck Θ α0) with
          | left _ =>
              match e_consis_call_impl
                      (consis_call_assign nil α0 (pskl_all_syn P0'))
                      S0 Θ _ _ _ with
              | None => None
              | Some (exist _ r Hr) =>
                  Some (exist _ (mk_consis_result (cs_supply r) (cs_ctx r)
                          (pskl_var_f α0)) _)
              end
          | right _ => None
          end
      (* U-ForallInh *)
      | pskl_all_syn P1 => fun EP =>
          match e_consis_call_impl
                  (consis_call_consis
                     (add (supply_fresh S0) Δ1) (add (supply_fresh S0) Δ2)
                     (open_pskl_wrt_pskl P0' (pskl_var_f (supply_fresh S0)))
                     (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0))))
                  (add (supply_fresh S0) S0)
                  ((supply_fresh S0 ~ abind_tvar) ++ Θ) _ _ _ with
          | None => None
          | Some (exist _ r Hr) =>
              match split_tvar_head (supply_fresh S0) (cs_ctx r) with
              | None => None
              | Some (exist _ Θ1 HΘ) =>
                  Some (exist _ (mk_consis_result (cs_supply r) Θ1
                          (pskl_all_syn
                             (close_pskl_wrt_pskl (supply_fresh S0)
                                (cs_out r)))) _)
              end
          end
      (* U-UnivGhost1 *)
      | pskl_tophole P1 => fun EP =>
          match e_consis_call_impl
                  (consis_call_consis (add (supply_fresh S0) Δ1) Δ2
                     (open_pskl_wrt_pskl P0' (pskl_var_f (supply_fresh S0)))
                     (pskl_tophole P1))
                  (add (supply_fresh S0) S0)
                  ((supply_fresh S0 ~ abind_tvar) ++ Θ) _ _ _ with
          | None => None
          | Some (exist _ r Hr) =>
              match split_tvar_head (supply_fresh S0) (cs_ctx r) with
              | None => None
              | Some (exist _ Θ1 HΘ) =>
                  Some (exist _ (mk_consis_result (cs_supply r) Θ1
                          (pskl_all_syn
                             (close_pskl_wrt_pskl (supply_fresh S0)
                                (cs_out r)))) _)
              end
          end
      | _ => fun _ => None
      end eq_refl
  | pskl_tophole P0' => fun EP0 =>
      match P as P1 return P = P1
          -> option (sig (consis_call_spec S0 Θ
                            (consis_call_consis Δ1 Δ2 P0 P)))
      with
      (* U-Ghost *)
      | pskl_hole => fun EP =>
          match sumbool_of_bool (is_empty (inter Δ2 (ftvar_in_pskl P0)))
          with
          | left _ => Some (exist _ (mk_consis_result S0 Θ P0) _)
          | right _ => None
          end
      (* flexible-variable subject — U-FlexL, ⫯-strip U-UnivGhostR as the
         rigid fallback *)
      | pskl_var_f α0 => fun EP =>
          match sumbool_of_bool (flex_bound_ck Θ α0) with
          | left _ =>                                      (* U-FlexL *)
              match e_consis_call_impl
                      (consis_call_assign nil α0 (pskl_tophole P0'))
                      S0 Θ _ _ _ with
              | None => None
              | Some (exist _ r Hr) =>
                  Some (exist _ (mk_consis_result (cs_supply r) (cs_ctx r)
                          (pskl_var_f α0)) _)
              end
          | right _ =>                                     (* U-UnivGhostR *)
              match e_consis_call_impl
                      (consis_call_consis Δ1 Δ2 P0' (pskl_var_f α0))
                      S0 Θ _ _ _ with
              | None => None
              | Some (exist _ r Hr) => Some (exist _ r _)
              end
          end
      (* U-UnivGhost *)
      | pskl_tophole P1 => fun EP =>
          match e_consis_call_impl (consis_call_consis Δ1 Δ2 P0' P1)
                  S0 Θ _ _ _ with
          | None => None
          | Some (exist _ r Hr) =>
              Some (exist _ (mk_consis_result (cs_supply r) (cs_ctx r)
                      (pskl_tophole (cs_out r))) _)
          end
      (* U-ForallSyn *)
      | pskl_all_syn P1 => fun EP =>
          match e_consis_call_impl
                  (consis_call_consis Δ1 (add (supply_fresh S0) Δ2)
                     (pskl_tophole P0')
                     (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0))))
                  (add (supply_fresh S0) S0)
                  ((supply_fresh S0 ~ abind_tvar) ++ Θ) _ _ _ with
          | None => None
          | Some (exist _ r Hr) =>
              match split_tvar_head (supply_fresh S0) (cs_ctx r) with
              | None => None
              | Some (exist _ Θ1 HΘ) =>
                  Some (exist _ (mk_consis_result (cs_supply r) Θ1
                          (pskl_all_syn
                             (close_pskl_wrt_pskl (supply_fresh S0)
                                (cs_out r)))) _)
              end
          end
      (* U-UnivGhostR — strip the pattern's ⫯ against a guarded subject *)
      | pskl_unit => fun EP =>
          match e_consis_call_impl
                  (consis_call_consis Δ1 Δ2 P0' pskl_unit) S0 Θ _ _ _
          with
          | None => None
          | Some (exist _ r Hr) => Some (exist _ r _)
          end
      | pskl_arrow P1 P2 => fun EP =>
          match e_consis_call_impl
                  (consis_call_consis Δ1 Δ2 P0' (pskl_arrow P1 P2))
                  S0 Θ _ _ _ with
          | None => None
          | Some (exist _ r Hr) => Some (exist _ r _)
          end
      | _ => fun _ => None
      end eq_refl
  | _ => fun EP0 =>
      match P as P1 return P = P1
          -> option (sig (consis_call_spec S0 Θ
                            (consis_call_consis Δ1 Δ2 P0 P)))
      with
      (* U-Ghost — a hole subject answers ANY pattern *)
      | pskl_hole => fun EP =>
          match sumbool_of_bool (is_empty (inter Δ2 (ftvar_in_pskl P0)))
          with
          | left _ => Some (exist _ (mk_consis_result S0 Θ P0) _)
          | right _ => None
          end
      | _ => fun _ => None
      end eq_refl
  end eq_refl.

(** The public functions, at their original signatures — thin wrappers
    over the tagged block.  The assign/unify wrappers repack the uniform
    [consis_result] into [unify_result]; the spec at a concrete tag is
    stated over exactly that repacking, so the proof component transports
    unchanged. *)
Definition e_assign_impl (S0 : supply) (Θ Ξ : aenv) (α : atom) (P : pskl)
    (HP : lc_pskl P) (HD : aenv_defs_mono (Ξ ++ Θ))
    (H : e_assign_order S0 Θ Ξ α P)
    : option (sig (assign_spec S0 Θ Ξ α P)) :=
  match e_consis_call_impl (consis_call_assign Ξ α P) S0 Θ HP HD
          (e_assign_order_to_call _ _ _ _ _ H) with
  | None => None
  | Some (exist _ r Hr) =>
      Some (exist _ (mk_unify_result (cs_supply r) (cs_ctx r)) Hr)
  end.

Definition e_unify_impl (S0 : supply) (Θ : aenv) (α β : atom)
    (HD : aenv_defs_mono Θ) (H : e_unify_order S0 Θ α β)
    : option (sig (unify_spec S0 Θ α β)) :=
  match e_consis_call_impl (consis_call_unify α β) S0 Θ I HD
          (e_unify_order_to_call _ _ _ _ H) with
  | None => None
  | Some (exist _ r Hr) =>
      Some (exist _ (mk_unify_result (cs_supply r) (cs_ctx r)) Hr)
  end.

Definition e_consis_impl (Δ1 Δ2 : atoms) (S0 : supply) (Θ : aenv)
    (P0 P : pskl) (HP0 : lc_pskl P0) (HP : lc_pskl P)
    (HD : aenv_defs_mono Θ) (H : e_consis_order Δ1 Δ2 S0 Θ P0 P)
    : option (sig (consis_spec Δ1 Δ2 S0 Θ P0 P)) :=
  e_consis_call_impl (consis_call_consis Δ1 Δ2 P0 P) S0 Θ
    (conj HP0 HP) HD (e_consis_order_to_call _ _ _ _ _ _ H).

(* ===================================================================== *)
(*  §4  Totality-backed argument-free runners, and their soundness        *)
(* ===================================================================== *)

Definition e_consis_run (Δ1 Δ2 : atoms) (S0 : supply) (Θ : aenv)
    (P0 P : pskl) (HP0 : lc_pskl P0) (HP : lc_pskl P)
    (HD : aenv_defs_mono Θ) : option consis_result :=
  match e_consis_impl Δ1 Δ2 S0 Θ P0 P HP0 HP HD
          (@e_consis_order_total Δ1 Δ2 S0 Θ P0 P HP0 HP HD) with
  | Some r => Some (proj1_sig r)
  | None => None
  end.

Lemma e_consis_run_sound : forall Δ1 Δ2 S0 Θ P0 P HP0 HP HD r,
  e_consis_run Δ1 Δ2 S0 Θ P0 P HP0 HP HD = Some r ->
  {{ S0 ↝ (cs_supply r) ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ (cs_out r)
     ⊣ (cs_ctx r) }}e.
Proof.
  intros *. unfold e_consis_run.
  destruct (e_consis_impl Δ1 Δ2 S0 Θ P0 P HP0 HP HD
              (@e_consis_order_total Δ1 Δ2 S0 Θ P0 P HP0 HP HD))
    as [ [r' Hr'] | ];
    intro Heq; inversion Heq; subst; exact Hr'.
Qed.
