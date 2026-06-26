(** Frost — Ltac utilities. *)

Require Import Coq.Program.Equality.
Require Export Metalib.Metatheory.

Require Import src.frost.notations.

(* Specialise a cofinite-quantified hypothesis to a fresh atom x. *)
Ltac inst_cofinite_impl H x :=
  match type of H with
  | forall x0, x0 `notin` ?L -> _ =>
      let Fr := fresh "Fr" in
      assert (x `notin` L) as Fr by auto;
      specialize (H x Fr); clear Fr
  end.

Ltac inst_cofinites_with x :=
  repeat
    match goal with
    | H : forall x0, x0 `notin` ?L -> _ |- _ =>
        inst_cofinite_impl H x
    end.

Tactic Notation "inst_cofinites_with" ident(x) :=
  inst_cofinites_with x.

Ltac inst_cofinites :=
  match goal with
  | x : atom |- _ => inst_cofinites_with x
  end.

(* Discharge absurd category mismatches for the current split syntax. *)
Ltac discharge_category :=
  match goal with
  | H : is_styp (btyp_all_inh _) |- _ => inversion H
  | H : is_ityp (btyp_all_syn _) |- _ => inversion H
  | H : is_ttyp (utyp_all_syn _) |- _ => inversion H
  | H : is_sskl (bskl_all_inh _) |- _ => inversion H
  | H : is_iskl (bskl_all_syn _) |- _ => inversion H
  end.

(** Override Metalib's [gather_atoms] to include every atom-bearing
    source in our context: name-sets [atoms], single atoms, term
    contexts ([list (atom * dbind)]), tag / Ψ-scope contexts
    ([list atom]), and free-variable functions on all current type
    categories / [exp].

    Pairs with [pick fresh] (already metalib) and with
    [inst_cofinites_for], defined below, which applies a cofinite
    rule [R] using all gathered atoms as [L].

    Conventions follow the public reference at
      jiangsy/proof_worklist_remechnization/systemdk/ltac_utils.v.
*)
Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (atom * dbind) => dom x) in
  let D := gather_atoms_with (fun x : list atom => List.fold_right add empty x) in
  let E := gather_atoms_with (fun x : exp => fvar_in_exp x) in
  let F := gather_atoms_with (fun x : exp => ftvar_in_exp x) in
  let G := gather_atoms_with (fun x : ptyp => ftvar_in_ptyp x) in
  let H := gather_atoms_with (fun x : btyp => ftvar_in_btyp x) in
  let I := gather_atoms_with (fun x : utyp => ftvar_in_utyp x) in
  let J := gather_atoms_with (fun x : pskl => ftvar_in_pskl x) in
  let K := gather_atoms_with (fun x : bskl => ftvar_in_bskl x) in
  let L := gather_atoms_with (fun x : uskl => ftvar_in_uskl x) in
  constr:(A `union` B `union` C `union` D `union` E `union` F `union`
          G `union` H `union` I `union` J `union` K `union` L).

(** Apply a cofinite-quantified rule [R] using [gather_atoms] as the
    freshness set. Replaces [apply R with (L := L `union` ... `union` dom Γ)]. *)
Tactic Notation "inst_cofinites_for" constr(R) :=
  let _L := gather_atoms in
  apply R with (L := _L).

Tactic Notation "inst_cofinites_for" constr(R) ident(name) ":=" constr(val) :=
  let _L := gather_atoms in
  apply R with (L := _L) (name := val).
