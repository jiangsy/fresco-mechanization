(** ⛔⛔ A FIFTH DISPATCH GUARD IS OWED, AND IT IS ON THE SOLVE LAYER
    (2026-08-18).

    ⚠️ WHAT THIS FILE REFUTES.  §8c.16 §D's STEP 2 statement —
    [e_extract] is deterministic UP TO A FRESH RENAMING — is STILL FALSE
    after the four dispatch guards, and the drift is one layer below the
    collection this time: it is [SS-ForallR] racing [SS-Var] in the SOLVE
    layer.

    ⭐ THE CELL.  At subject [γ] (a VARIABLE) against counterpart [∀_. 0]
    (ghost-free) in CHECK mode, both

        SS-Var       γ ≼[TC] ∀_.0  ⤳  ·  ⨾  γ          (spends NOTHING)
        SS-ForallR   draw β, recurse at  γ ≼[TC] 0[β]   (spends ONE atom)

    fire, and the second's premise is [SS-Var] again — so the two
    derivations agree on the block ([·]) and on the yield ([γ]) and differ
    ONLY in SUPPLY, by one atom.  Identical species to
    [cex/probe_extract_supply_drift.v], which the ABSENCE-FIRST guard
    retracted, and to [cex/probe_extract_flexr_ug2_drift.v], which the
    FlexR-PRIORITY guard retracted.

    ⭐ AND THE RUNNER ALREADY DISAGREES WITH THE RELATION.
    [e_solve_sub_impl] (ext_algo/def_solve_impl.v:316) dispatches on the
    SUBJECT first — [SS-Var], then [SS-ForallL], then [SS-UnivGhostL] —
    and only then on the counterpart ([SS-Vacuous], [SS-ForallR],
    [SS-GhostL], [SS-Check]).  So at this cell the implementation takes
    [SS-Var] and never reaches [SS-ForallR].  A relational encoding has no
    match order, so the exclusion has to be a PREMISE — exactly the
    argument that landed guards 1-4.

    ⛔ A SECOND DRIFTING CELL, same species: [SS-Vacuous] races
    [SS-ForallL] at a [∀] subject against a [◇] counterpart, and the
    runner takes [SS-ForallL] (clause 2 precedes clause 4).  It is not
    formalized here; one witness is enough to block STEP 2.

    ⚙ THE LIFT TO [e_extract] IS ONE ARROW.  At

        NM = SK   m = FN(TC)   Θ0 = ·
        subject   α → α        counterpart  γ → ∀_.0

    [LS-Arrow] hands its first half to [LE-Var] (collecting [≐ γ]) and its
    second to [LS-Var] (collecting [≼TC ∀_.0]); the fold then solves
    [◇ ∼ γ ⤳ γ] and hands the accumulated [γ] to the cell above; and at
    [NM = SK] the guess is the identity.  ⭐ The BLOCK conjunct is not even
    needed — both routes emit [·] — the SUPPLY conjunct alone refutes the
    statement. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_guess.
Require Import src.frost.ext_algo.def_look.
Require Import src.frost.ext_algo.def_solve.
Require Import src.frost.ext_algo.def_extract.
Require Import src.frost.ext_algo.prop_solve_det.

Local Open Scope frost_e_scope.

(* ===================================================================== *)
(*  §1  The configuration                                                 *)
(* ===================================================================== *)

(** the ghost-free [∀] the counterpart's codomain is *)
Definition drift_all : pskl := pskl_all_syn (pskl_var_b 0).

Lemma drift_all_ghost_free : pskl_ghost_free drift_all.
Proof. unfold drift_all. simpl. exact I. Qed.

Definition dsubj (α : atom) : pskl := pskl_arrow (pskl_var_f α) (pskl_var_f α).
Definition dcpt (γ : atom) : pskl := pskl_arrow (pskl_var_f γ) drift_all.

(** the COLLECTION is the same on both routes: it emits no block and the
    two constraints [≐ γ] and [≼TC ∀_.0] *)
Lemma drift_collect : forall S Θ α γ,
  {{ S ↝ S ⊨ Θ ⊢ (dsubj α) ≼[ α , (mode_fn mode_tc) ] (dcpt γ)
     ⤳ (nil ++ nil)
     ⨾ ((a_cstr_eq (pskl_var_f γ) :: nil)
        ++ (a_cstr_sub mode_tc drift_all :: nil)) }}e.
Proof.
  intros. unfold dsubj, dcpt.
  eapply e_looksub__arrow;
    [ apply e_lookeq__var | apply e_looksub__var ].
Qed.

(* ===================================================================== *)
(*  §2  The two extractions — same inputs, supplies one atom apart        *)
(* ===================================================================== *)

(** ROUTE A — the fold's [sub] constraint is answered by [SS-Var]. *)
Lemma drift_extract_var : forall S Θ α γ,
  {{ S ↝ S ⊨ Θ ⊢ (dsubj α) ⊳[ a_sub_mode_sk , α , (mode_fn mode_tc) ]
     (dcpt γ) ⤳ (nil ++ nil ++ nil) ↪ (pskl_var_f γ) }}e.
Proof.
  intros S Θ α γ.
  apply e_extract__solve
    with (S1 := S) (S2 := S) (Ξ := nil ++ nil) (Ξs := nil ++ nil)
         (C := (a_cstr_eq (pskl_var_f γ) :: nil)
               ++ (a_cstr_sub mode_tc drift_all :: nil))
         (Q := pskl_var_f γ).
  - apply drift_collect.
  - apply e_solve_cstr__eq
      with (S1 := S) (Ξ1 := nil) (Ξ2 := nil) (P'' := pskl_var_f γ).
    + apply e_solve_eq__hole_l.
    + apply e_solve_cstr__sub. apply e_solve_sub__var.
  - apply e_guess__sk.
Qed.

(** ROUTE B — the SAME cell is answered by [SS-ForallR], which DRAWS an
    opener and then falls back to [SS-Var]. *)
Lemma drift_extract_forall_r : forall S Θ α γ β,
  β `notin` S ->
  {{ S ↝ (add β S) ⊨ Θ ⊢ (dsubj α)
     ⊳[ a_sub_mode_sk , α , (mode_fn mode_tc) ] (dcpt γ)
     ⤳ (nil ++ nil ++ nil) ↪ (pskl_var_f γ) }}e.
Proof.
  intros S Θ α γ β Hβ.
  apply e_extract__solve
    with (S1 := S) (S2 := add β S) (Ξ := nil ++ nil) (Ξs := nil ++ nil)
         (C := (a_cstr_eq (pskl_var_f γ) :: nil)
               ++ (a_cstr_sub mode_tc drift_all :: nil))
         (Q := pskl_var_f γ).
  - apply drift_collect.
  - apply e_solve_cstr__eq
      with (S1 := S) (Ξ1 := nil) (Ξ2 := nil) (P'' := pskl_var_f γ).
    + apply e_solve_eq__hole_l.
    + apply e_solve_cstr__sub.
      apply e_solve_sub__forall_r with (β := β).
      * exact drift_all_ghost_free.
      * exact Hβ.
      * unfold drift_all. simpl. apply e_solve_sub__var.
  - apply e_guess__sk.
Qed.

(* ===================================================================== *)
(*  §2b  THE SECOND DRIFTING CELL — [SS-Vacuous] vs [SS-ForallL]          *)
(*                                                                        *)
(*  ⭐ It matters because it fixes the SHAPE of the missing guard: TWO     *)
(*  premises are owed, not one.  At a [∀] subject against a [◇]           *)
(*  counterpart the runner takes [SS-ForallL] (def_solve_impl.v's clause   *)
(*  2 precedes its clause 4) and so does [solve_sub] (type.ml:494 —        *)
(*  [SolS-ForallL] is matched before [SolS-Vacuous]), but the RELATION     *)
(*  admits both, and [SS-ForallL] draws an opener that [SS-Vacuous] does   *)
(*  not.  The two answers are otherwise IDENTICAL, because a [close] over  *)
(*  a fresh opener undoes the [open].                                     *)
(* ===================================================================== *)

Lemma vacuous_route : forall S Θ m P,
  {{ S ↝ S ⊨ Θ ⊢ₛ (pskl_all_syn P) ≼[ m ] pskl_hole
     ⤳ nil ⨾ (pskl_all_syn P) }}e.
Proof. intros. apply e_solve_sub__vacuous. Qed.

Lemma forall_l_route : forall S Θ m P β,
  β `notin` S ->
  β `notin` ftvar_in_pskl P ->
  {{ S ↝ (add β S) ⊨ Θ ⊢ₛ (pskl_all_syn P) ≼[ m ] pskl_hole
     ⤳ nil ⨾ (pskl_all_syn P) }}e.
Proof.
  intros S Θ m P β Hβ HβP.
  replace (pskl_all_syn P)
    with (pskl_all_syn
            (close_pskl_wrt_pskl β (open_pskl_wrt_pskl P (pskl_var_f β))))
    by (f_equal; apply close_pskl_wrt_pskl_open_pskl_wrt_pskl; exact HβP).
  apply e_solve_sub__forall_l with (β := β).
  - exact Hβ.
  - rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl by exact HβP.
    apply e_solve_sub__vacuous.
Qed.

(* ===================================================================== *)
(*  §3  ⛔ THE REFUTATION                                                  *)
(* ===================================================================== *)

Definition e_extract_det : Prop :=
  forall S0 Θ0 NM α m P P' S1 Ξ Q S1' Ξ' Q',
    {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q }}e ->
    {{ S0 ↝ S1' ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ' ↪ Q' }}e ->
    add α (ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P ∪ ftvar_in_pskl P') [<=] S0 ->
    exists ps,
      (forall x y, In (x, y) ps -> x `notin` S0 /\ y `notin` S0)
      /\ swaps_atoms ps S1 [=] S1'
      /\ swaps_aenv ps Ξ = Ξ'
      /\ swaps_pskl ps Q = Q'.

(** ⛔ The SUPPLY conjunct alone: a chain whose every pair avoids [S0] is
    the IDENTITY on [S0] ([swaps_atoms_notin]), and route B's output
    supply properly contains it. *)
Theorem e_extract_det_false : ~ e_extract_det.
Proof.
  intros Hdet.
  destruct (atom_fresh empty) as [α _].
  destruct (atom_fresh (singleton α)) as [γ Hγ].
  destruct (atom_fresh (add γ (singleton α))) as [β Hβ].
  set (S0 := add γ (singleton α)).
  assert (HβS0 : β `notin` S0) by (subst S0; exact Hβ).
  destruct (Hdet S0 nil a_sub_mode_sk α (mode_fn mode_tc)
              (dsubj α) (dcpt γ) S0 (nil ++ nil ++ nil) (pskl_var_f γ)
              (add β S0) (nil ++ nil ++ nil) (pskl_var_f γ)
              (drift_extract_var S0 nil α γ)
              (drift_extract_forall_r S0 nil α γ β HβS0)
              ltac:(unfold dsubj, dcpt, drift_all, S0; simpl;
                    clear; fsetdec))
    as [ps [Hav [HS _]]].
  assert (Hid : swaps_atoms ps S0 [=] S0)
    by (apply swaps_atoms_notin; exact Hav).
  assert (Hin : β `in` S0) by (rewrite <- Hid; rewrite HS; clear; fsetdec).
  clear - Hin HβS0. fsetdec.
Qed.
