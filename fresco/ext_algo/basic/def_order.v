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
Require Import src.fresco.ext_algo.basic.def_guess_impl.
Require Import src.fresco.ext_algo.consistency.def_consis.
Require Import src.fresco.ext_algo.subtyping.def_look.
Require Import src.fresco.ext_algo.subtyping.def_solve.
Require Import src.fresco.ext_algo.subtyping.def_extract.
Require Import src.fresco.ext_algo.subtyping.def_sub.

Open Scope fresco_e_scope.

Inductive e_guess_order : supply -> a_sub_mode -> pskl -> Prop :=
| e_guess_order__intro : forall S0 NM Q,
    (NM = a_sub_mode_ty -> e_guess_mono_order S0 Q) ->
    e_guess_order S0 NM Q.

Inductive e_lookeq_order : supply -> aenv -> atom -> pskl -> pskl -> Prop :=
| e_lookeq_order__intro : forall S0 Θ α P P',

    (forall P1 P2 P1' P2',
       P = pskl_arrow P1 P2 -> P' = pskl_arrow P1' P2' ->
       e_lookeq_order S0 Θ α P1 P1') ->
    (forall P1 P2 P1' P2' S1 Ξ1 C1,
       P = pskl_arrow P1 P2 -> P' = pskl_arrow P1' P2' ->
       {{ S0 ↝ S1 ⊨ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}e ->
       e_lookeq_order S1 Θ α P2 P2') ->

    (forall Q Q',
       P = pskl_all_syn Q -> P' = pskl_all_syn Q' ->
       e_lookeq_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) α
         (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
         (open_pskl_wrt_pskl Q' (pskl_var_f (supply_fresh S0)))) ->

    (forall Q Q',
       P = pskl_all_syn Q -> P' = pskl_univ_ghost Q' ->
       e_lookeq_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) α
         (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
         (pskl_univ_ghost Q')) ->

    (forall Q Q',
       P = pskl_univ_ghost Q -> P' = pskl_univ_ghost Q' ->
       e_lookeq_order S0 Θ α Q Q') ->

    (forall Q Q',
       P = pskl_univ_ghost Q -> P' = pskl_all_syn Q' ->
       e_lookeq_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) α
         (pskl_univ_ghost Q)
         (open_pskl_wrt_pskl Q' (pskl_var_f (supply_fresh S0)))) ->

    (forall Q,
       P = pskl_univ_ghost Q ->
       e_lookeq_order S0 Θ α Q P') ->

    (forall Q',
       P' = pskl_univ_ghost Q' ->
       e_lookeq_order S0 Θ α P Q') ->
    e_lookeq_order S0 Θ α P P'.

Inductive e_looksub_order : supply -> aenv -> atom -> mode -> pskl -> pskl
                            -> Prop :=
| e_looksub_order__intro : forall S0 Θ α m P P',

    (m = mode_tc -> e_lookeq_order S0 Θ α P P') ->

    (forall B,
       m = mode_tc -> P' = pskl_all_syn B ->
       e_looksub_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) α mode_tc P
         (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))) ->

    (forall m' P1 P2 P1' P2',
       m = mode_fn m' -> P = pskl_arrow P1 P2 -> P' = pskl_arrow P1' P2' ->
       e_lookeq_order S0 Θ α P1 P1') ->
    (forall m' P1 P2 P1' P2' S1 Ξ1 C1,
       m = mode_fn m' -> P = pskl_arrow P1 P2 -> P' = pskl_arrow P1' P2' ->
       {{ S0 ↝ S1 ⊨ Θ ⊢ P1 ∼[ α ] P1' ⤳ Ξ1 ⨾ C1 }}e ->
       e_looksub_order S1 Θ α m' P2 P2') ->

    (forall Q,
       P = pskl_all_syn Q ->
       e_looksub_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) α m
         (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0))) P') ->

    (forall Q,
       P = pskl_univ_ghost Q ->
       e_looksub_order S0 Θ α m Q P') ->
    e_looksub_order S0 Θ α m P P'.

Inductive e_solve_eq_order : supply -> aenv -> pskl -> pskl -> Prop :=
| e_solve_eq_order__intro : forall S0 Θ P Q,

    (forall β,
       Q = pskl_var_f β ->
       e_guess_mono_order S0 P) ->

    (forall P1 P2 Q1 Q2,
       P = pskl_arrow P1 P2 -> Q = pskl_arrow Q1 Q2 ->
       e_solve_eq_order S0 Θ P1 Q1) ->
    (forall P1 P2 Q1 Q2 S1 Ξ1 P1',
       P = pskl_arrow P1 P2 -> Q = pskl_arrow Q1 Q2 ->
       {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ P1' }}e ->
       e_solve_eq_order S1 (Ξ1 ++ Θ) P2 Q2) ->

    (forall P1 Q1,
       P = pskl_all_syn P1 -> Q = pskl_all_syn Q1 ->
       e_solve_eq_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0)))
         (open_pskl_wrt_pskl Q1 (pskl_var_f (supply_fresh S0)))) ->

    (forall P1 Q1,
       P = pskl_univ_ghost P1 -> Q = pskl_univ_ghost Q1 ->
       e_solve_eq_order S0 Θ P1 Q1) ->

    (forall P1 Q1,
       P = pskl_univ_ghost P1 -> Q = pskl_all_syn Q1 ->
       e_solve_eq_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (pskl_univ_ghost P1)
         (open_pskl_wrt_pskl Q1 (pskl_var_f (supply_fresh S0)))) ->

    (forall P1,
       P = pskl_univ_ghost P1 ->
       e_solve_eq_order S0 Θ P1 Q) ->

    (forall P1 Q1,
       P = pskl_all_syn P1 -> Q = pskl_univ_ghost Q1 ->
       e_solve_eq_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0)))
         (pskl_univ_ghost Q1)) ->

    (forall Q1,
       Q = pskl_univ_ghost Q1 ->
       e_solve_eq_order S0 Θ P Q1) ->
    e_solve_eq_order S0 Θ P Q.

Inductive e_solve_sub_order : supply -> aenv -> mode -> pskl -> pskl -> Prop :=
| e_solve_sub_order__intro : forall S0 Θ m P Q,

    (forall P1,
       P = pskl_all_syn P1 ->
       e_solve_sub_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) m
         (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0))) Q) ->

    (forall P1,
       P = pskl_univ_ghost P1 ->
       e_solve_sub_order S0 Θ m P1 Q) ->

    (m = mode_tc -> e_solve_eq_order S0 Θ P Q) ->

    (forall B,
       m = mode_tc -> Q = pskl_all_syn B ->
       e_solve_sub_order (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ) mode_tc P
         (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))) ->

    (forall m' P1 P2 Q1 Q2,
       m = mode_fn m' -> P = pskl_arrow P1 P2 -> Q = pskl_arrow Q1 Q2 ->
       e_solve_eq_order S0 Θ P1 Q1) ->
    (forall m' P1 P2 Q1 Q2 S1 Ξ1 P1',
       m = mode_fn m' -> P = pskl_arrow P1 P2 -> Q = pskl_arrow Q1 Q2 ->
       {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P1 ∼ Q1 ⤳ Ξ1 ⨾ P1' }}e ->
       e_solve_sub_order S1 (Ξ1 ++ Θ) m' P2 Q2) ->

    (forall m' Q1 Q2,
       m = mode_fn m' -> P = pskl_ghost -> Q = pskl_arrow Q1 Q2 ->
       e_solve_eq_order S0 Θ pskl_ghost Q1) ->
    (forall m' Q1 Q2 S1 Ξ1 P1',
       m = mode_fn m' -> P = pskl_ghost -> Q = pskl_arrow Q1 Q2 ->
       {{ S0 ↝ S1 ⊨ Θ ⊢ₑ pskl_ghost ∼ Q1 ⤳ Ξ1 ⨾ P1' }}e ->
       e_solve_sub_order S1 (Ξ1 ++ Θ) m' pskl_ghost Q2) ->

    e_solve_sub_order S0 Θ m P Q.

Inductive e_solve_cstr_order : supply -> aenv -> a_cstrs -> pskl -> Prop :=
| e_solve_cstr_order__intro : forall S0 Θ C P,
    (forall m Q,
       C = a_cstr_sub m Q :: nil ->
       e_solve_sub_order S0 Θ m P Q) ->
    (forall Q C',
       C = a_cstr_eq Q :: C' ->
       e_solve_eq_order S0 Θ P Q
       /\ (forall S1 Ξ1 P'',
             {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ1 ⨾ P'' }}e ->
             e_solve_cstr_order S1 (Ξ1 ++ Θ) C' P'')) ->
    e_solve_cstr_order S0 Θ C P.

Inductive e_extract_order : supply -> aenv -> a_sub_mode -> atom -> mode
                            -> pskl -> pskl -> Prop :=
| e_extract_order__intro : forall S0 Θ0 NM α m P P',
    e_looksub_order S0 Θ0 α m P P' ->
    (forall S1 Ξ C,
       {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
       e_solve_cstr_order S1 (Ξ ++ Θ0) C pskl_ghost) ->
    (forall S1 Ξ C S2 Ξs Q,
       {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
       {{ S1 ↝ S2 ⊨ (Ξ ++ Θ0) ⊩ C ⨾ pskl_ghost ⤳ Ξs ⨾ Q }}e ->
       e_guess_order S2 NM Q) ->
    e_extract_order S0 Θ0 NM α m P P'.

Inductive e_assign_order : supply -> aenv -> aenv -> atom -> pskl -> Prop :=
| e_assign_order__intro : forall S0 Θ Ξ α P,

    (forall Θ0,
       Θ = (α ~ abind_flex_mono) ++ Θ0 ->
       e_guess_mono_order S0 P) ->

    (forall β τ Θ0,
       Θ = (β ~ abind_flex_mono_def τ) ++ Θ0 ->
       e_consis_order empty empty S0 (Ξ ++ Θ0)
         (subst_pskl_in_pskl (ptyp_to_pskl τ) β P)
         (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))) ->

    (forall β Θ0,
       Θ = (β ~ abind_flex_mono) ++ Θ0 ->
       e_assign_order S0 Θ0 (Ξ ++ (β ~ abind_flex_mono)) α P
       /\ e_assign_order S0 Θ0 Ξ α P) ->

    (forall β Θ0,
       Θ = (β ~ abind_tvar) ++ Θ0 ->
       e_assign_order S0 Θ0 Ξ α P) ->

    (forall x A Θ0,
       Θ = (x ~ abind_var_typ A) ++ Θ0 ->
       e_assign_order S0 Θ0 Ξ α P) ->
    (forall x Q Θ0,
       Θ = (x ~ abind_var_skl Q) ++ Θ0 ->
       e_assign_order S0 Θ0 Ξ α P) ->
    e_assign_order S0 Θ Ξ α P

with e_unify_order : supply -> aenv -> atom -> atom -> Prop :=
| e_unify_order__intro : forall S0 Θ α β,

    (forall α1 τ Θ0,
       Θ = (α1 ~ abind_flex_mono_def τ) ++ Θ0 ->
       e_consis_order empty empty S0 Θ0
         (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f β)))
         (ptyp_to_pskl (subst_ptyp_in_ptyp τ α1 (ptyp_var_f α)))) ->

    (forall α1 Θ0,
       Θ = (α1 ~ abind_flex_mono) ++ Θ0 ->
       e_unify_order S0 Θ0 α β) ->

    (forall c Θ0,
       Θ = (c ~ abind_tvar) ++ Θ0 ->
       e_unify_order S0 Θ0 α β) ->
    (forall x A Θ0,
       Θ = (x ~ abind_var_typ A) ++ Θ0 ->
       e_unify_order S0 Θ0 α β) ->
    (forall x Q Θ0,
       Θ = (x ~ abind_var_skl Q) ++ Θ0 ->
       e_unify_order S0 Θ0 α β) ->
    e_unify_order S0 Θ α β

with e_consis_order : atoms -> atoms -> supply -> aenv -> pskl -> pskl
                      -> Prop :=
| e_consis_order__intro : forall Δ1 Δ2 S0 Θ P0 P,

    (forall P0a P0b P1 P2,
       P0 = pskl_arrow P0a P0b -> P = pskl_arrow P1 P2 ->
       e_consis_order Δ1 Δ2 S0 Θ P0a P1
       /\ (forall S1 Θ1 Q1,
             {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0a ] P1 ∼ Q1 ⊣ Θ1 }}e ->
             e_consis_order Δ1 Δ2 S1 Θ1 P0b P2)) ->

    (forall P0' P1,
       P0 = pskl_all_syn P0' -> P = pskl_all_syn P1 ->
       e_consis_order (add (supply_fresh S0) Δ1) (add (supply_fresh S0) Δ2)
         (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (open_pskl_wrt_pskl P0' (pskl_var_f (supply_fresh S0)))
         (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0)))) ->

    (forall P0' P1,
       P0 = pskl_univ_ghost P0' -> P = pskl_all_syn P1 ->
       e_consis_order Δ1 (add (supply_fresh S0) Δ2)
         (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (pskl_univ_ghost P0')
         (open_pskl_wrt_pskl P1 (pskl_var_f (supply_fresh S0)))) ->

    (forall P0' P1,
       P0 = pskl_univ_ghost P0' -> P = pskl_univ_ghost P1 ->
       e_consis_order Δ1 Δ2 S0 Θ P0' P1) ->

    (forall P0' P1,
       P0 = pskl_all_syn P0' -> P = pskl_univ_ghost P1 ->
       e_consis_order (add (supply_fresh S0) Δ1) Δ2
         (add (supply_fresh S0) S0)
         ((supply_fresh S0 ~ abind_tvar) ++ Θ)
         (open_pskl_wrt_pskl P0' (pskl_var_f (supply_fresh S0)))
         (pskl_univ_ghost P1)) ->

    (forall P1,
       P = pskl_univ_ghost P1 ->
       e_consis_order Δ1 Δ2 S0 Θ P0 P1) ->

    (forall P0',
       P0 = pskl_univ_ghost P0' ->
       e_consis_order Δ1 Δ2 S0 Θ P0' P) ->

    (forall α β,
       P = pskl_var_f α -> P0 = pskl_var_f β ->
       e_unify_order S0 Θ α β) ->

    (forall α,
       P = pskl_var_f α ->
       e_assign_order S0 Θ nil α P0) ->

    (forall α,
       P0 = pskl_var_f α ->
       e_assign_order S0 Θ nil α P) ->
    e_consis_order Δ1 Δ2 S0 Θ P0 P.

Scheme e_assign_order_mind := Induction for e_assign_order Sort Prop
  with e_unify_order_mind  := Induction for e_unify_order  Sort Prop
  with e_consis_order_mind := Induction for e_consis_order Sort Prop.
Combined Scheme e_assign_unify_consis_order_mutind
  from e_assign_order_mind, e_unify_order_mind, e_consis_order_mind.

Inductive e_sub_order : supply -> a_sub_mode -> mode -> pskl -> aenv -> pskl
                        -> Prop :=
| e_sub_order__intro : forall S0 NM M P0 Θ0 P,

    (M = mode_tc -> e_consis_order empty empty S0 Θ0 P0 P) ->

    (forall B,
       M = mode_tc -> P0 = pskl_all_syn B ->
       e_sub_order (add (supply_fresh S0) S0) a_sub_mode_ty mode_tc
         (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))
         ((supply_fresh S0 ~ abind_tvar) ++ Θ0) P) ->

    (forall α M',
       P = pskl_var_f α -> M = mode_fn M' ->
       e_sub_flex_order S0 NM M' P0 Θ0 nil α) ->

    (forall M' P0a P0b P1 P2,
       M = mode_fn M' -> P0 = pskl_arrow P0a P0b -> P = pskl_arrow P1 P2 ->
       e_consis_order empty empty S0 Θ0 P0a P1
       /\ (forall S1 Θ1 Q1,
             {{ S0 ↝ S1 ⊨ Θ0 ⊢[ empty | empty | P0a ] P1 ∼ Q1 ⊣ Θ1 }}e ->
             e_sub_order S1 NM M' P0b Θ1 P2)) ->
    (forall Q,
       P = pskl_all_syn Q -> M <> mode_ti ->
       (guarded_pskl P0 \/ P0 = pskl_ghost) ->
       e_extract_order (add (supply_fresh S0) S0) Θ0 NM (supply_fresh S0) M
         (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0))) P0
       /\ (forall S1 Ξ P1,
             {{ (add (supply_fresh S0) S0) ↝ S1 ⊨ Θ0
                ⊢ (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
                ⊳[ NM , (supply_fresh S0) , M ] P0 ⤳ Ξ ↪ P1 }}e ->
             {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a ->
             e_sub_order S1 NM M P0 (Ξ ++ Θ0) (open_pskl_wrt_pskl Q P1))) ->

    (forall Q,
       P = pskl_univ_ghost Q -> M <> mode_ti ->
       e_sub_order S0 NM M P0 Θ0 Q) ->
    e_sub_order S0 NM M P0 Θ0 P

with e_sub_flex_order : supply -> a_sub_mode -> mode -> pskl -> aenv -> aenv
                        -> atom -> Prop :=
| e_sub_flex_order__intro : forall S0 NM M P0 Θ0 Ξ α,
    (forall Θ0',
       Θ0 = (α ~ abind_flex_mono) ++ Θ0' ->
       e_sub_order
         (add (supply_fresh (add (supply_fresh S0) S0))
            (add (supply_fresh S0) S0))
         NM (mode_fn M) P0
         (Ξ ++ (α ~ abind_flex_mono_def
                      (ptyp_arrow (ptyp_var_f (supply_fresh S0))
                         (ptyp_var_f (supply_fresh (add (supply_fresh S0) S0)))))
             ++ (supply_fresh (add (supply_fresh S0) S0) ~ abind_flex_mono)
             ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0')
         (pskl_arrow (pskl_var_f (supply_fresh S0))
            (pskl_var_f (supply_fresh (add (supply_fresh S0) S0))))) ->

    (forall β τ Θ0',
       Θ0 = (β ~ abind_flex_mono_def τ) ++ Θ0' ->
       e_sub_order S0 NM (mode_fn M)
         (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
         (Ξ ++ Θ0')
         (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α))) ->

    (forall β Θ0',
       Θ0 = (β ~ abind_flex_mono) ++ Θ0' ->
       e_sub_flex_order S0 NM M P0 Θ0' (Ξ ++ (β ~ abind_flex_mono)) α
       /\ e_sub_flex_order S0 NM M P0 Θ0' Ξ α) ->

    (forall β Θ0',
       Θ0 = (β ~ abind_tvar) ++ Θ0' ->
       e_sub_flex_order S0 NM M P0 Θ0' Ξ α) ->

    (forall x A Θ0',
       Θ0 = (x ~ abind_var_typ A) ++ Θ0' ->
       e_sub_flex_order S0 NM M P0 Θ0' Ξ α) ->
    (forall x Q Θ0',
       Θ0 = (x ~ abind_var_skl Q) ++ Θ0' ->
       e_sub_flex_order S0 NM M P0 Θ0' Ξ α) ->
    e_sub_flex_order S0 NM M P0 Θ0 Ξ α.

Scheme e_sub_order_mind      := Induction for e_sub_order      Sort Prop
  with e_sub_flex_order_mind := Induction for e_sub_flex_order Sort Prop.
Combined Scheme e_sub_sub_flex_order_mutind
  from e_sub_order_mind, e_sub_flex_order_mind.
