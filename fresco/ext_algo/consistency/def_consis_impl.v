Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.prop_ln.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.basic.def_supply.
Require Import src.fresco.ext_algo.basic.def_uip.
Require Import src.fresco.ext_algo.basic.def_dec.
Require Import src.fresco.ext_algo.basic.def_guess.
Require Import src.fresco.ext_algo.basic.def_guess_impl.
Require Import src.fresco.ext_algo.consistency.def_consis.
Require Import src.fresco.ext_algo.basic.def_order.
Require Import src.fresco.ext_algo.basic.prop_termination.

Set Equations With UIP.

Open Scope fresco_e_scope.

Record unify_result : Type := mk_unify_result {
  ur_supply : supply;
  ur_ctx    : aenv
}.

Record consis_result : Type := mk_consis_result {
  cs_supply : supply;
  cs_ctx    : aenv;
  cs_out    : pskl
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

Inductive consis_call : Type :=
| consis_call_assign (Ξ : aenv) (α : atom) (P : pskl)
| consis_call_unify  (α β : atom)
| consis_call_consis (Δ1 Δ2 : atoms) (P0 P : pskl).

Derive NoConfusion for consis_call.

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

Inductive e_consis_call_order : supply -> aenv -> consis_call -> Prop :=
| e_consis_call_order__assign : forall S0 Θ Ξ α P,

    (forall Θ0,
       Θ = (α ~ abind_flex_mono) ++ Θ0 ->
       e_guess_mono_order S0 P) ->

    (forall β τ Θ0,
       Θ = (β ~ abind_flex_mono_def τ) ++ Θ0 ->
       e_consis_call_order S0 (Ξ ++ Θ0)
         (consis_call_consis empty empty
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)))) ->

    (forall β Θ0,
       Θ = (β ~ abind_flex_mono) ++ Θ0 ->
       e_consis_call_order S0 Θ0
         (consis_call_assign (Ξ ++ (β ~ abind_flex_mono)) α P)) ->
    (forall β Θ0,
       Θ = (β ~ abind_flex_mono) ++ Θ0 ->
       e_consis_call_order S0 Θ0 (consis_call_assign Ξ α P)) ->

    (forall β Θ0,
       Θ = (β ~ abind_tvar) ++ Θ0 ->
       e_consis_call_order S0 Θ0 (consis_call_assign Ξ α P)) ->

    (forall x A Θ0,
       Θ = (x ~ abind_var_typ A) ++ Θ0 ->
       e_consis_call_order S0 Θ0 (consis_call_assign Ξ α P)) ->
    (forall x Q Θ0,
       Θ = (x ~ abind_var_skl Q) ++ Θ0 ->
       e_consis_call_order S0 Θ0 (consis_call_assign Ξ α P)) ->
    e_consis_call_order S0 Θ (consis_call_assign Ξ α P)

| e_consis_call_order__unify : forall S0 Θ α β,

    (forall α1 τ Θ0,
       Θ = (α1 ~ abind_flex_mono_def τ) ++ Θ0 ->
       e_consis_call_order S0 Θ0
         (consis_call_consis empty empty
            (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β)))
            (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α))))) ->

    (forall α1 Θ0,
       Θ = (α1 ~ abind_flex_mono) ++ Θ0 ->
       e_consis_call_order S0 Θ0 (consis_call_unify α β)) ->

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

    (forall P0a P0b P1 P2,
       P0 = pskl_arrow P0a P0b -> P = pskl_arrow P1 P2 ->
       e_consis_call_order S0 Θ (consis_call_consis Δ1 Δ2 P0a P1)) ->
    (forall P0a P0b P1 P2 S1 Θ1 Q1,
       P0 = pskl_arrow P0a P0b -> P = pskl_arrow P1 P2 ->
       {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0a ] P1 ∼ Q1 ⊣ Θ1 }}e ->
       e_consis_call_order S1 Θ1 (consis_call_consis Δ1 Δ2 P0b P2)) ->

    (forall P0' P1,
       P0 = pskl_all_syn P0' -> P = pskl_all_syn P1 ->
       e_consis_call_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (consis_call_consis
            (add (supply_fresh S0) Δ1) (add (supply_fresh S0) Δ2)
            (open_pskl_wrt_pskl P0' (pskl_var_f (supply_fresh S0)))
            (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0))))) ->

    (forall P0' P1,
       P0 = pskl_univ_ghost P0' -> P = pskl_all_syn P1 ->
       e_consis_call_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (consis_call_consis Δ1 (add (supply_fresh S0) Δ2)
            (pskl_univ_ghost P0')
            (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0))))) ->

    (forall P0' P1,
       P0 = pskl_univ_ghost P0' -> P = pskl_univ_ghost P1 ->
       e_consis_call_order S0 Θ (consis_call_consis Δ1 Δ2 P0' P1)) ->

    (forall P0' P1,
       P0 = pskl_all_syn P0' -> P = pskl_univ_ghost P1 ->
       e_consis_call_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (consis_call_consis (add (supply_fresh S0) Δ1) Δ2
            (open_pskl_wrt_pskl P0' (pskl_var_f (supply_fresh S0)))
            (pskl_univ_ghost P1))) ->

    (forall P1,
       P = pskl_univ_ghost P1 ->
       e_consis_call_order S0 Θ (consis_call_consis Δ1 Δ2 P0 P1)) ->

    (forall P0',
       P0 = pskl_univ_ghost P0' ->
       e_consis_call_order S0 Θ (consis_call_consis Δ1 Δ2 P0' P)) ->

    (forall α β,
       P = pskl_var_f α -> P0 = pskl_var_f β ->
       e_consis_call_order S0 Θ (consis_call_unify α β)) ->

    (forall α,
       P = pskl_var_f α ->
       e_consis_call_order S0 Θ (consis_call_assign nil α P0)) ->

    (forall α,
       P0 = pskl_var_f α ->
       e_consis_call_order S0 Θ (consis_call_assign nil α P)) ->
    e_consis_call_order S0 Θ (consis_call_consis Δ1 Δ2 P0 P).

Derive Signature for e_consis_call_order.

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
           match Hds β Θ0 E with conj h1 _ => e_assign_order_to_call _ _ _ _ _ h1 end)
        (fun β Θ0 E =>
           match Hds β Θ0 E with conj _ h2 => e_assign_order_to_call _ _ _ _ _ h2 end)
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
           | conj h1 _ => e_consis_order_to_call _ _ _ _ _ _ h1
           end)
        (fun P0a P0b P1 P2 S1 Θ1 Q1 E1 E2 Hrun =>
           match Harr P0a P0b P1 P2 E1 E2 with
           | conj _ h2 => e_consis_order_to_call _ _ _ _ _ _ (h2 S1 Θ1 Q1 Hrun)
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

#[local] Hint Resolve supply_fresh_notin mem_true_in mem_false_notin
  inter_is_empty_sound flex_bound_ck_flex_tvar flex_bound_false_non_flex
  rigid_bound_ck_binds non_flex_ck_sound mono_ck_sound
  lc_pskl_all_syn_inv subst_pskl_in_pskl_lc_pskl subst_ptyp_in_ptyp_lc_ptyp
  mono_ptyp_to_pskl_lc ptyp_to_pskl_lc mono_ptyp_lc
  e_consis_defs_mono : consisdec.
#[local] Hint Constructors lc_pskl lc_ptyp guarded_pskl : consisdec.
#[local] Hint Extern 2 (non_flex_ck _ _ = true) => reflexivity : consisdec.
#[local] Hint Extern 4 (_ <> _) => congruence : consisdec.
#[local] Hint Extern 4 (Forall entry_def_mono _) =>
  repeat first [ assumption
               | apply Forall_app_intro
               | apply List.Forall_cons
               | apply List.Forall_nil ];
  auto using entry_def_mono_flex, entry_def_mono_tvar,
    entry_def_mono_var_typ, entry_def_mono_var_skl, entry_def_mono_def
  : consisdec.

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

  repeat match goal with
         | |- context [ if ?c then _ else _ ] => destruct c
         end;
  try congruence;
  try solve [ eauto 7 with consisdec ];
  solve [ econstructor; eauto 6 with consisdec ].

#[tactic="consis_impl_tac", derive(equations=yes,eliminator=no)]
Equations e_consis_call_impl (c : consis_call) (S0 : supply) (Θ : aenv)
    (Hlc : consis_call_lc c) (HD : consis_call_defs_mono Θ c)
    (H : e_consis_call_order S0 Θ c)
    : option (sig (consis_call_spec S0 Θ c)) by struct H :=

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
            | pskl_univ_ghost (pskl_var_f γ) => fun EP =>
                match γ == α with
                | left _ =>
                    Some (exist _ (mk_consis_result S0
                            ((β0 ~ abind_flex_mono) ++ Θ0) pskl_unit) _)
                | right _ =>
                    match sumbool_of_bool (mem α (ftvar_in_pskl P)) with
                    | left _ => None
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
            | _ => fun EP =>
                match sumbool_of_bool (mem α (ftvar_in_pskl P)) with
                | left _ => None
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
        | _ :: _ => fun EΞ =>
            match sumbool_of_bool (mem α (ftvar_in_pskl P)) with
            | left _ => None
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
    | right _ =>
        match sumbool_of_bool (mem β0 (ftvar_in_pskl P)) with
        | left _ =>
            match e_consis_call_impl
                    (consis_call_assign (Ξ ++ (β0 ~ abind_flex_mono)) α P)
                    S0 Θ0 _ _ _ with
            | None => None
            | Some (exist _ r Hr) => Some (exist _ r _)
            end
        | right _ =>
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

| consis_call_unify α β, S0, nil, Hlc, HD, H => None
| consis_call_unify α β, S0, ((γ, abind_flex_mono) :: Θ0), Hlc, HD, H =>
    match α == β with
    | left _ =>
        match sumbool_of_bool
                (flex_bound_ck ((γ, abind_flex_mono) :: Θ0) α) with
        | left _ =>
            Some (exist _ (mk_consis_result S0
                    ((γ, abind_flex_mono) :: Θ0) pskl_unit) _)
        | right _ => None
        end
    | right _ =>
        match γ == α with
        | left _ =>
            match sumbool_of_bool (flex_bound_ck Θ0 β) with
            | left _ =>
                Some (exist _ (mk_consis_result S0
                        ((γ ~ abind_flex_mono_def (ptyp_var_f β)) ++ Θ0)
                        pskl_unit) _)
            | right _ => None
            end
        | right _ =>
            match γ == β with
            | left _ =>
                match sumbool_of_bool (flex_bound_ck Θ0 α) with
                | left _ =>
                    Some (exist _ (mk_consis_result S0
                            ((γ ~ abind_flex_mono_def (ptyp_var_f α))
                               ++ Θ0) pskl_unit) _)
                | right _ => None
                end
            | right _ =>
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
    | left _ =>
        match sumbool_of_bool
                (flex_bound_ck ((γ, abind_flex_mono_def τ) :: Θ0) α) with
        | left _ =>
            Some (exist _ (mk_consis_result S0
                    ((γ, abind_flex_mono_def τ) :: Θ0) pskl_unit) _)
        | right _ => None
        end
    | right _ =>
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
    match α == β with
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
    match α == β with
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
    match α == β with
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

| consis_call_consis Δ1 Δ2 P0 P, S0, Θ, Hlc, HD, H =>
  match P0 as P01 return P0 = P01
      -> option (sig (consis_call_spec S0 Θ
                        (consis_call_consis Δ1 Δ2 P0 P)))
  with

  | pskl_ghost => fun EP0 =>
      match sumbool_of_bool (is_empty (inter Δ1 (ftvar_in_pskl P))) with
      | left _ => Some (exist _ (mk_consis_result S0 Θ P) _)
      | right _ => None
      end
  | pskl_unit => fun EP0 =>
      match P as P1 return P = P1
          -> option (sig (consis_call_spec S0 Θ
                            (consis_call_consis Δ1 Δ2 P0 P)))
      with

      | pskl_ghost => fun EP =>
          match sumbool_of_bool (is_empty (inter Δ2 (ftvar_in_pskl P0)))
          with
          | left _ => Some (exist _ (mk_consis_result S0 Θ P0) _)
          | right _ => None
          end

      | pskl_unit => fun EP =>
          Some (exist _ (mk_consis_result S0 Θ pskl_unit) _)

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

      | pskl_univ_ghost P1 => fun EP =>
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

      | pskl_ghost => fun EP =>
          match sumbool_of_bool (is_empty (inter Δ2 (ftvar_in_pskl P0)))
          with
          | left _ => Some (exist _ (mk_consis_result S0 Θ P0) _)
          | right _ => None
          end
      | pskl_var_f α0 => fun EP =>
          match α0 == β0 with
          | left _ =>
              match sumbool_of_bool (rigid_bound_ck Θ α0) with
              | left _ =>
                  Some (exist _ (mk_consis_result S0 Θ (pskl_var_f α0)) _)
              | right _ =>
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
              | left _ =>
                  match e_consis_call_impl (consis_call_unify α0 β0) S0 Θ
                          _ _ _ with
                  | None => None
                  | Some (exist _ r Hr) =>
                      Some (exist _ (mk_consis_result (cs_supply r)
                              (cs_ctx r) (pskl_var_f α0)) _)
                  end
              | right _ =>
                  match sumbool_of_bool (flex_bound_ck Θ β0) with
                  | left _ =>
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
                      | left _ =>
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
      | pskl_univ_ghost P1 => fun EP =>
          match sumbool_of_bool (flex_bound_ck Θ β0) with
          | left _ =>
              match e_consis_call_impl
                      (consis_call_assign nil β0 (pskl_univ_ghost P1))
                      S0 Θ _ _ _ with
              | None => None
              | Some (exist _ r Hr) =>
                  Some (exist _ (mk_consis_result (cs_supply r) (cs_ctx r)
                          (pskl_var_f β0)) _)
              end
          | right _ =>
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

      | pskl_ghost => fun EP =>
          match sumbool_of_bool (is_empty (inter Δ2 (ftvar_in_pskl P0)))
          with
          | left _ => Some (exist _ (mk_consis_result S0 Θ P0) _)
          | right _ => None
          end

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

      | pskl_univ_ghost P1 => fun EP =>
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

      | pskl_ghost => fun EP =>
          match sumbool_of_bool (is_empty (inter Δ2 (ftvar_in_pskl P0)))
          with
          | left _ => Some (exist _ (mk_consis_result S0 Θ P0) _)
          | right _ => None
          end

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

      | pskl_univ_ghost P1 => fun EP =>
          match e_consis_call_impl
                  (consis_call_consis (add (supply_fresh S0) Δ1) Δ2
                     (open_pskl_wrt_pskl P0' (pskl_var_f (supply_fresh S0)))
                     (pskl_univ_ghost P1))
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
  | pskl_univ_ghost P0' => fun EP0 =>
      match P as P1 return P = P1
          -> option (sig (consis_call_spec S0 Θ
                            (consis_call_consis Δ1 Δ2 P0 P)))
      with

      | pskl_ghost => fun EP =>
          match sumbool_of_bool (is_empty (inter Δ2 (ftvar_in_pskl P0)))
          with
          | left _ => Some (exist _ (mk_consis_result S0 Θ P0) _)
          | right _ => None
          end
      | pskl_var_f α0 => fun EP =>
          match sumbool_of_bool (flex_bound_ck Θ α0) with
          | left _ =>
              match e_consis_call_impl
                      (consis_call_assign nil α0 (pskl_univ_ghost P0'))
                      S0 Θ _ _ _ with
              | None => None
              | Some (exist _ r Hr) =>
                  Some (exist _ (mk_consis_result (cs_supply r) (cs_ctx r)
                          (pskl_var_f α0)) _)
              end
          | right _ =>
              match e_consis_call_impl
                      (consis_call_consis Δ1 Δ2 P0' (pskl_var_f α0))
                      S0 Θ _ _ _ with
              | None => None
              | Some (exist _ r Hr) => Some (exist _ r _)
              end
          end

      | pskl_univ_ghost P1 => fun EP =>
          match e_consis_call_impl (consis_call_consis Δ1 Δ2 P0' P1)
                  S0 Θ _ _ _ with
          | None => None
          | Some (exist _ r Hr) =>
              Some (exist _ (mk_consis_result (cs_supply r) (cs_ctx r)
                      (pskl_univ_ghost (cs_out r))) _)
          end

      | pskl_all_syn P1 => fun EP =>
          match e_consis_call_impl
                  (consis_call_consis Δ1 (add (supply_fresh S0) Δ2)
                     (pskl_univ_ghost P0')
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

      | pskl_ghost => fun EP =>
          match sumbool_of_bool (is_empty (inter Δ2 (ftvar_in_pskl P0)))
          with
          | left _ => Some (exist _ (mk_consis_result S0 Θ P0) _)
          | right _ => None
          end
      | _ => fun _ => None
      end eq_refl
  end eq_refl.

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
