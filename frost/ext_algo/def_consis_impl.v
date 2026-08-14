(** ext_algo — the [assign] / [unifyvar] / [consistency] block as EXECUTABLE
    FUNCTIONS, by Bove–Capretta.  Phase 4 step 5: a MUTUAL [Equations] on the
    mutual orders of def_order.v §5, total at lc inputs over a defs-mono
    context (prop_termination.v §16).

    Result shape, dispatch discipline and obligation-tactic recipe are
    def_look_impl.v's; the reference dispatch orders are [join_sk]
    (type.ml:143-262), [join_var] (:299-336) and [assign] (:338-388).
    Rows the mech does not have (Con, Mod, kinds) are skipped, and rigid/flex
    is decided by CONTEXT LOOKUP where the OCaml matches on [TVar]/[MFlex]
    syntactically.

    ⚙ THE PRECONDITIONS ARE §16's, VERBATIM: local closure of the skeleton
    inputs and [aenv_defs_mono] of the context — the discipline that every
    definition payload is a MONOTYPE, which is what makes the substituted
    skeletons at [Assign-Assign]/[Flex-Flex-Assign] locally closed and lets
    [Arrow] hand the domain's output context to the codomain
    ([e_consis_defs_mono]).  All erased at extraction.

    ⚙ ONE RULE HAS NO type.ml COUNTERPART: [Assign-UnivGhost-Id]
    (def_consis.v:84) — at pattern [⫯α̂] against target [α̂] itself the paper
    answers identity where type.ml raises [Occurs] (:344).  The runner
    implements the rule (its own specialised clause), so the occurs-check
    test lives only on the [SolveM] path.

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
Require Import src.frost.ext_algo.def_dec.
Require Import src.frost.ext_algo.def_guess.
Require Import src.frost.ext_algo.def_guess_impl.
Require Import src.frost.ext_algo.def_consis.
Require Import src.frost.ext_algo.def_order.
Require Import src.frost.ext_algo.prop_termination.

(* ⚠️ NO [Set Implicit Arguments] in an implementation file — see
   def_guess_impl.v's header. *)

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
  intros;
  try match goal with
      | H : e_assign_order _ _ _ _ _ |- _ => inversion H; subst
      end;
  try match goal with
      | H : e_unify_order _ _ _ _ |- _ => inversion H; subst
      end;
  try match goal with
      | H : e_consis_order _ _ _ _ _ _ |- _ => inversion H; subst
      end;
  try match goal with
      | Hlc : lc_pskl (pskl_var_b _) |- _ => inversion Hlc
      end;
  unfold assign_spec, unify_spec, consis_spec, guess_spec in *;
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
(*  §3  The mutual block                                                  *)
(* ===================================================================== *)

#[tactic="consis_impl_tac", derive(equations=no,eliminator=no)]
Equations e_assign_impl (S0 : supply) (Θ Ξ : aenv) (α : atom) (P : pskl)
    (HP : lc_pskl P) (HD : aenv_defs_mono (Ξ ++ Θ))
    (H : e_assign_order S0 Θ Ξ α P)
    : option (sig (assign_spec S0 Θ Ξ α P)) by struct H :=

(* Assign-UnivGhost-Id — the one row with no type.ml counterpart *)
| S0, ((β0, abind_flex_mono) :: Θ0), nil, α, pskl_tophole (pskl_var_f γ),
  HP, HD, H =>
    match β0 == α with
    | left _ =>
        match γ == α with
        | left _ =>
            Some (exist _ (mk_unify_result S0
                    ((β0 ~ abind_flex_mono) ++ Θ0)) _)
        | right _ =>                                       (* Assign-SolveM *)
            match sumbool_of_bool
                    (mem α (ftvar_in_pskl
                              (pskl_tophole (pskl_var_f γ)))) with
            | left _ => None                               (* occurs *)
            | right _ =>
                let (rg, Hg) := e_guess_mono_impl S0
                                  (pskl_tophole (pskl_var_f γ)) _ in
                match sumbool_of_bool (mono_ck (gr_type rg)) with
                | right _ => None
                | left _ =>
                    Some (exist _ (mk_unify_result (gr_supply rg)
                            ((α ~ abind_flex_mono_def (gr_type rg))
                               ++ gr_block rg ++ nil ++ Θ0)) _)
                end
            end
        end
    | right _ =>                                  (* Depend / Skip walk *)
        match sumbool_of_bool
                (mem β0 (ftvar_in_pskl (pskl_tophole (pskl_var_f γ)))) with
        | left _ =>                                        (* Assign-Depend *)
            match e_assign_impl S0 Θ0 (nil ++ (β0 ~ abind_flex_mono)) α
                    (pskl_tophole (pskl_var_f γ)) _ _ _ with
            | None => None
            | Some (exist _ r Hr) => Some (exist _ r _)
            end
        | right _ =>                                       (* Assign-Skip *)
            match e_assign_impl S0 Θ0 nil α
                    (pskl_tophole (pskl_var_f γ)) _ _ _ with
            | None => None
            | Some (exist _ r Hr) =>
                Some (exist _ (mk_unify_result (ur_supply r)
                        ((β0 ~ abind_flex_mono) ++ ur_ctx r)) _)
            end
        end
    end

(* undefined flexible head, general pattern *)
| S0, ((β0, abind_flex_mono) :: Θ0), Ξ, α, P, HP, HD, H =>
    match β0 == α with
    | left _ =>                                            (* Assign-SolveM *)
        match sumbool_of_bool (mem α (ftvar_in_pskl P)) with
        | left _ => None                                   (* occurs *)
        | right _ =>
            let (rg, Hg) := e_guess_mono_impl S0 P _ in
            match sumbool_of_bool (mono_ck (gr_type rg)) with
            | right _ => None
            | left _ =>
                Some (exist _ (mk_unify_result (gr_supply rg)
                        ((α ~ abind_flex_mono_def (gr_type rg))
                           ++ gr_block rg ++ Ξ ++ Θ0)) _)
            end
        end
    | right _ =>
        match sumbool_of_bool (mem β0 (ftvar_in_pskl P)) with
        | left _ =>                                        (* Assign-Depend *)
            match e_assign_impl S0 Θ0 (Ξ ++ (β0 ~ abind_flex_mono)) α P
                    _ _ _ with
            | None => None
            | Some (exist _ r Hr) => Some (exist _ r _)
            end
        | right _ =>                                       (* Assign-Skip *)
            match e_assign_impl S0 Θ0 Ξ α P _ _ _ with
            | None => None
            | Some (exist _ r Hr) =>
                Some (exist _ (mk_unify_result (ur_supply r)
                        ((β0 ~ abind_flex_mono) ++ ur_ctx r)) _)
            end
        end
    end

(* defined flexible head — Assign-Assign *)
| S0, ((β0, abind_flex_mono_def τ) :: Θ0), Ξ, α, P, HP, HD, H =>
    match sumbool_of_bool
            (flex_bound_ck ((β0, abind_flex_mono_def τ) :: Θ0) α) with
    | right _ => None
    | left _ =>
        match e_consis_impl empty empty S0 (Ξ ++ Θ0)
                (subst_pskl_in_pskl (ptyp_to_pskl τ) β0 P)
                (subst_pskl_in_pskl (ptyp_to_pskl τ) β0 (pskl_var_f α))
                _ _ _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_unify_result (cs_supply r)
                    ((β0 ~ abind_flex_mono_def τ) ++ cs_ctx r)) _)
        end
    end

(* rigid head — Assign-SkipRigid *)
| S0, ((β0, abind_tvar) :: Θ0), Ξ, α, P, HP, HD, H =>
    match sumbool_of_bool (mem β0 (ftvar_in_pskl P)) with
    | left _ => None
    | right _ =>
        match e_assign_impl S0 Θ0 Ξ α P _ _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_unify_result (ur_supply r)
                    ((β0 ~ abind_tvar) ++ ur_ctx r)) _)
        end
    end

(* term-variable heads — Assign-SkipTmVar, both payload sorts *)
| S0, ((x, abind_var_typ A) :: Θ0), Ξ, α, P, HP, HD, H =>
    match e_assign_impl S0 Θ0 Ξ α P _ _ _ with
    | None => None
    | Some (exist _ r Hr) =>
        Some (exist _ (mk_unify_result (ur_supply r)
                ((x ~ abind_var_typ A) ++ ur_ctx r)) _)
    end
| S0, ((x, abind_var_skl Q) :: Θ0), Ξ, α, P, HP, HD, H =>
    match e_assign_impl S0 Θ0 Ξ α P _ _ _ with
    | None => None
    | Some (exist _ r Hr) =>
        Some (exist _ (mk_unify_result (ur_supply r)
                ((x ~ abind_var_skl Q) ++ ur_ctx r)) _)
    end
| S0, nil, Ξ, α, P, HP, HD, H => None

(* ===================================================================== *)
with e_unify_impl (S0 : supply) (Θ : aenv) (α β : atom)
    (HD : aenv_defs_mono Θ)
    (H : e_unify_order S0 Θ α β)
    : option (sig (unify_spec S0 Θ α β)) by struct H :=

| S0, nil, α, β, HD, H => None
| S0, ((γ, abind_flex_mono) :: Θ0), α, β, HD, H =>
    match α == β with
    | left _ =>                                      (* Flex-Flex-Id *)
        match sumbool_of_bool
                (flex_bound_ck ((γ, abind_flex_mono) :: Θ0) α) with
        | left _ =>
            Some (exist _ (mk_unify_result S0
                    ((γ, abind_flex_mono) :: Θ0)) _)
        | right _ => None
        end
    | right _ =>
        match γ == α with
        | left _ =>                                  (* Flex-Flex-L *)
            match sumbool_of_bool (flex_bound_ck Θ0 β) with
            | left _ =>
                Some (exist _ (mk_unify_result S0
                        ((γ ~ abind_flex_mono_def (ptyp_var_f β))
                           ++ Θ0)) _)
            | right _ => None
            end
        | right _ =>
            match γ == β with
            | left _ =>                              (* Flex-Flex-R *)
                match sumbool_of_bool (flex_bound_ck Θ0 α) with
                | left _ =>
                    Some (exist _ (mk_unify_result S0
                            ((γ ~ abind_flex_mono_def (ptyp_var_f α))
                               ++ Θ0)) _)
                | right _ => None
                end
            | right _ =>                             (* Flex-Flex-Skip *)
                match e_unify_impl S0 Θ0 α β _ _ with
                | None => None
                | Some (exist _ r Hr) =>
                    Some (exist _ (mk_unify_result (ur_supply r)
                            ((γ ~ abind_flex_mono) ++ ur_ctx r)) _)
                end
            end
        end
    end
| S0, ((γ, abind_flex_mono_def τ) :: Θ0), α, β, HD, H =>
    match α == β with
    | left _ =>                                      (* Flex-Flex-Id *)
        match sumbool_of_bool
                (flex_bound_ck ((γ, abind_flex_mono_def τ) :: Θ0) α) with
        | left _ =>
            Some (exist _ (mk_unify_result S0
                    ((γ, abind_flex_mono_def τ) :: Θ0)) _)
        | right _ => None
        end
    | right _ =>                                     (* Flex-Flex-Assign *)
        match sumbool_of_bool
                (flex_bound_ck ((γ, abind_flex_mono_def τ) :: Θ0) α
                 && flex_bound_ck ((γ, abind_flex_mono_def τ) :: Θ0) β) with
        | right _ => None
        | left _ =>
            match e_consis_impl empty empty S0 Θ0
                    (ptyp_to_pskl (subst_ptyp_in_ptyp τ γ (ptyp_var_f β)))
                    (ptyp_to_pskl (subst_ptyp_in_ptyp τ γ (ptyp_var_f α)))
                    _ _ _ _ with
            | None => None
            | Some (exist _ r Hr) =>
                Some (exist _ (mk_unify_result (cs_supply r)
                        ((γ ~ abind_flex_mono_def τ) ++ cs_ctx r)) _)
            end
        end
    end
| S0, ((γ, abind_tvar) :: Θ0), α, β, HD, H =>        (* Flex-Flex-Skip' *)
    match α == β with
    | left _ =>
        match sumbool_of_bool
                (flex_bound_ck ((γ, abind_tvar) :: Θ0) α) with
        | left _ =>
            Some (exist _ (mk_unify_result S0 ((γ, abind_tvar) :: Θ0)) _)
        | right _ => None
        end
    | right _ =>
        match e_unify_impl S0 Θ0 α β _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_unify_result (ur_supply r)
                    ((γ ~ abind_tvar) ++ ur_ctx r)) _)
        end
    end
| S0, ((x, abind_var_typ A) :: Θ0), α, β, HD, H =>   (* Flex-Flex-Skip' *)
    match α == β with
    | left _ =>
        match sumbool_of_bool
                (flex_bound_ck ((x, abind_var_typ A) :: Θ0) α) with
        | left _ =>
            Some (exist _ (mk_unify_result S0
                    ((x, abind_var_typ A) :: Θ0)) _)
        | right _ => None
        end
    | right _ =>
        match e_unify_impl S0 Θ0 α β _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_unify_result (ur_supply r)
                    ((x ~ abind_var_typ A) ++ ur_ctx r)) _)
        end
    end
| S0, ((x, abind_var_skl Q) :: Θ0), α, β, HD, H =>   (* Flex-Flex-Skip' *)
    match α == β with
    | left _ =>
        match sumbool_of_bool
                (flex_bound_ck ((x, abind_var_skl Q) :: Θ0) α) with
        | left _ =>
            Some (exist _ (mk_unify_result S0
                    ((x, abind_var_skl Q) :: Θ0)) _)
        | right _ => None
        end
    | right _ =>
        match e_unify_impl S0 Θ0 α β _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_unify_result (ur_supply r)
                    ((x ~ abind_var_skl Q) ++ ur_ctx r)) _)
        end
    end

(* ===================================================================== *)
with e_consis_impl (Δ1 Δ2 : atoms) (S0 : supply) (Θ : aenv) (P0 P : pskl)
    (HP0 : lc_pskl P0) (HP : lc_pskl P) (HD : aenv_defs_mono Θ)
    (H : e_consis_order Δ1 Δ2 S0 Θ P0 P)
    : option (sig (consis_spec Δ1 Δ2 S0 Θ P0 P)) by struct H :=

(* U-GhostR / U-Ghost — a hole on either side answers the other *)
| Δ1, Δ2, S0, Θ, pskl_hole, P, HP0, HP, HD, H =>
    match sumbool_of_bool (is_empty (inter Δ1 (ftvar_in_pskl P))) with
    | left _ => Some (exist _ (mk_consis_result S0 Θ P) _)
    | right _ => None
    end
| Δ1, Δ2, S0, Θ, P0, pskl_hole, HP0, HP, HD, H =>
    match sumbool_of_bool (is_empty (inter Δ2 (ftvar_in_pskl P0))) with
    | left _ => Some (exist _ (mk_consis_result S0 Θ P0) _)
    | right _ => None
    end
(* U-Unit *)
| Δ1, Δ2, S0, Θ, pskl_unit, pskl_unit, HP0, HP, HD, H =>
    Some (exist _ (mk_consis_result S0 Θ pskl_unit) _)

(* variables — U-Rigid / U-Flex / U-FlexR / U-FlexL, in type.ml's order *)
| Δ1, Δ2, S0, Θ, pskl_var_f β0, pskl_var_f α0, HP0, HP, HD, H =>
    match α0 == β0 with
    | left _ =>
        match sumbool_of_bool (rigid_bound_ck Θ α0) with
        | left _ =>                                        (* U-Rigid *)
            Some (exist _ (mk_consis_result S0 Θ (pskl_var_f α0)) _)
        | right _ =>                                       (* U-Flex (Id) *)
            match e_unify_impl S0 Θ α0 β0 _ _ with
            | None => None
            | Some (exist _ r Hr) =>
                Some (exist _ (mk_consis_result (ur_supply r) (ur_ctx r)
                        (pskl_var_f α0)) _)
            end
        end
    | right _ =>
        match sumbool_of_bool (flex_bound_ck Θ α0 && flex_bound_ck Θ β0)
        with
        | left _ =>                                        (* U-Flex *)
            match e_unify_impl S0 Θ α0 β0 _ _ with
            | None => None
            | Some (exist _ r Hr) =>
                Some (exist _ (mk_consis_result (ur_supply r) (ur_ctx r)
                        (pskl_var_f α0)) _)
            end
        | right _ =>
            match sumbool_of_bool (flex_bound_ck Θ β0) with
            | left _ =>                                    (* U-FlexR *)
                match e_assign_impl S0 Θ nil β0 (pskl_var_f α0) _ _ _ with
                | None => None
                | Some (exist _ r Hr) =>
                    Some (exist _ (mk_consis_result (ur_supply r)
                            (ur_ctx r) (pskl_var_f β0)) _)
                end
            | right _ =>
                match sumbool_of_bool (flex_bound_ck Θ α0) with
                | left _ =>                                (* U-FlexL *)
                    match e_assign_impl S0 Θ nil α0 (pskl_var_f β0)
                            _ _ _ with
                    | None => None
                    | Some (exist _ r Hr) =>
                        Some (exist _ (mk_consis_result (ur_supply r)
                                (ur_ctx r) (pskl_var_f α0)) _)
                    end
                | right _ => None
                end
            end
        end
    end

(* flexible-variable pattern against a non-variable subject — U-FlexR,
   with the ⫯-strip U-UnivGhost2 as the rigid fallback *)
| Δ1, Δ2, S0, Θ, pskl_var_f β0, pskl_tophole P1, HP0, HP, HD, H =>
    match sumbool_of_bool (flex_bound_ck Θ β0) with
    | left _ =>                                            (* U-FlexR *)
        match e_assign_impl S0 Θ nil β0 (pskl_tophole P1) _ _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_consis_result (ur_supply r) (ur_ctx r)
                    (pskl_var_f β0)) _)
        end
    | right _ =>                                           (* U-UnivGhost2 *)
        match e_consis_impl Δ1 Δ2 S0 Θ (pskl_var_f β0) P1 _ _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    end
| Δ1, Δ2, S0, Θ, pskl_var_f β0, pskl_unit, HP0, HP, HD, H =>
    match sumbool_of_bool (flex_bound_ck Θ β0) with
    | left _ =>
        match e_assign_impl S0 Θ nil β0 pskl_unit _ _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_consis_result (ur_supply r) (ur_ctx r)
                    (pskl_var_f β0)) _)
        end
    | right _ => None
    end
| Δ1, Δ2, S0, Θ, pskl_var_f β0, pskl_arrow P1 P2, HP0, HP, HD, H =>
    match sumbool_of_bool (flex_bound_ck Θ β0) with
    | left _ =>
        match e_assign_impl S0 Θ nil β0 (pskl_arrow P1 P2) _ _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_consis_result (ur_supply r) (ur_ctx r)
                    (pskl_var_f β0)) _)
        end
    | right _ => None
    end
| Δ1, Δ2, S0, Θ, pskl_var_f β0, pskl_all_syn P1, HP0, HP, HD, H =>
    match sumbool_of_bool (flex_bound_ck Θ β0) with
    | left _ =>
        match e_assign_impl S0 Θ nil β0 (pskl_all_syn P1) _ _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_consis_result (ur_supply r) (ur_ctx r)
                    (pskl_var_f β0)) _)
        end
    | right _ => None
    end
| Δ1, Δ2, S0, Θ, pskl_var_f β0, pskl_var_b n, HP0, HP, HD, H => None

(* flexible-variable subject against a non-variable pattern — U-FlexL,
   with the ⫯-strip U-UnivGhostR as the rigid fallback *)
| Δ1, Δ2, S0, Θ, pskl_tophole P0', pskl_var_f α0, HP0, HP, HD, H =>
    match sumbool_of_bool (flex_bound_ck Θ α0) with
    | left _ =>                                            (* U-FlexL *)
        match e_assign_impl S0 Θ nil α0 (pskl_tophole P0') _ _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_consis_result (ur_supply r) (ur_ctx r)
                    (pskl_var_f α0)) _)
        end
    | right _ =>                                           (* U-UnivGhostR *)
        match e_consis_impl Δ1 Δ2 S0 Θ P0' (pskl_var_f α0) _ _ _ _ with
        | None => None
        | Some (exist _ r Hr) => Some (exist _ r _)
        end
    end
| Δ1, Δ2, S0, Θ, pskl_unit, pskl_var_f α0, HP0, HP, HD, H =>
    match sumbool_of_bool (flex_bound_ck Θ α0) with
    | left _ =>
        match e_assign_impl S0 Θ nil α0 pskl_unit _ _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_consis_result (ur_supply r) (ur_ctx r)
                    (pskl_var_f α0)) _)
        end
    | right _ => None
    end
| Δ1, Δ2, S0, Θ, pskl_arrow P0a P0b, pskl_var_f α0, HP0, HP, HD, H =>
    match sumbool_of_bool (flex_bound_ck Θ α0) with
    | left _ =>
        match e_assign_impl S0 Θ nil α0 (pskl_arrow P0a P0b) _ _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_consis_result (ur_supply r) (ur_ctx r)
                    (pskl_var_f α0)) _)
        end
    | right _ => None
    end
| Δ1, Δ2, S0, Θ, pskl_all_syn P0', pskl_var_f α0, HP0, HP, HD, H =>
    match sumbool_of_bool (flex_bound_ck Θ α0) with
    | left _ =>
        match e_assign_impl S0 Θ nil α0 (pskl_all_syn P0') _ _ _ with
        | None => None
        | Some (exist _ r Hr) =>
            Some (exist _ (mk_consis_result (ur_supply r) (ur_ctx r)
                    (pskl_var_f α0)) _)
        end
    | right _ => None
    end

(* U-Arrow *)
| Δ1, Δ2, S0, Θ, pskl_arrow P0a P0b, pskl_arrow P1 P2, HP0, HP, HD, H =>
    match e_consis_impl Δ1 Δ2 S0 Θ P0a P1 _ _ _ _ with
    | None => None
    | Some (exist _ r1 Hr1) =>
        match e_consis_impl Δ1 Δ2 (cs_supply r1) (cs_ctx r1) P0b P2
                _ _ _ _ with
        | None => None
        | Some (exist _ r2 Hr2) =>
            Some (exist _ (mk_consis_result (cs_supply r2) (cs_ctx r2)
                    (pskl_arrow (cs_out r1) (cs_out r2))) _)
        end
    end

(* U-ForallInh *)
| Δ1, Δ2, S0, Θ, pskl_all_syn P0', pskl_all_syn P1, HP0, HP, HD, H =>
    match e_consis_impl (add (supply_fresh S0) Δ1) (add (supply_fresh S0) Δ2)
            (add (supply_fresh S0) S0)
            ((supply_fresh S0 ~ abind_tvar) ++ Θ)
            (open_pskl_wrt_pskl P0' (pskl_var_f (supply_fresh S0)))
            (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0)))
            _ _ _ _ with
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

(* U-UnivGhost *)
| Δ1, Δ2, S0, Θ, pskl_tophole P0', pskl_tophole P1, HP0, HP, HD, H =>
    match e_consis_impl Δ1 Δ2 S0 Θ P0' P1 _ _ _ _ with
    | None => None
    | Some (exist _ r Hr) =>
        Some (exist _ (mk_consis_result (cs_supply r) (cs_ctx r)
                (pskl_tophole (cs_out r))) _)
    end

(* U-UnivGhost1 *)
| Δ1, Δ2, S0, Θ, pskl_all_syn P0', pskl_tophole P1, HP0, HP, HD, H =>
    match e_consis_impl (add (supply_fresh S0) Δ1) Δ2
            (add (supply_fresh S0) S0)
            ((supply_fresh S0 ~ abind_tvar) ++ Θ)
            (open_pskl_wrt_pskl P0' (pskl_var_f (supply_fresh S0)))
            (pskl_tophole P1) _ _ _ _ with
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

(* U-ForallSyn *)
| Δ1, Δ2, S0, Θ, pskl_tophole P0', pskl_all_syn P1, HP0, HP, HD, H =>
    match e_consis_impl Δ1 (add (supply_fresh S0) Δ2)
            (add (supply_fresh S0) S0)
            ((supply_fresh S0 ~ abind_tvar) ++ Θ)
            (pskl_tophole P0')
            (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0)))
            _ _ _ _ with
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

(* U-UnivGhost2 — strip the subject's ⫯ against a guarded pattern *)
| Δ1, Δ2, S0, Θ, pskl_unit, pskl_tophole P1, HP0, HP, HD, H =>
    match e_consis_impl Δ1 Δ2 S0 Θ pskl_unit P1 _ _ _ _ with
    | None => None
    | Some (exist _ r Hr) => Some (exist _ r _)
    end
| Δ1, Δ2, S0, Θ, pskl_arrow P0a P0b, pskl_tophole P1, HP0, HP, HD, H =>
    match e_consis_impl Δ1 Δ2 S0 Θ (pskl_arrow P0a P0b) P1 _ _ _ _ with
    | None => None
    | Some (exist _ r Hr) => Some (exist _ r _)
    end

(* U-UnivGhostR — strip the pattern's ⫯ against a guarded subject *)
| Δ1, Δ2, S0, Θ, pskl_tophole P0', pskl_unit, HP0, HP, HD, H =>
    match e_consis_impl Δ1 Δ2 S0 Θ P0' pskl_unit _ _ _ _ with
    | None => None
    | Some (exist _ r Hr) => Some (exist _ r _)
    end
| Δ1, Δ2, S0, Θ, pskl_tophole P0', pskl_arrow P1 P2, HP0, HP, HD, H =>
    match e_consis_impl Δ1 Δ2 S0 Θ P0' (pskl_arrow P1 P2) _ _ _ _ with
    | None => None
    | Some (exist _ r Hr) => Some (exist _ r _)
    end

| Δ1, Δ2, S0, Θ, P0, P, HP0, HP, HD, H => None.

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
