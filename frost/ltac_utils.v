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

(* Discharge an absurd category-mismatch on the unified typ AST. Use inside
   an Inductive whose case-split implicitly assumes a category (e.g.,
   d_consis case where we know the input is is_utyp; if a typ_hole shows
   up, this tactic kills it). *)
Ltac discharge_category :=
  match goal with
  | H : is_typ typ_hole |- _ => inversion H
  | H : is_typ (typ_tophole _) |- _ => inversion H
  | H : is_typ (typ_all_etag _ _) |- _ => inversion H
  | H : is_typ (typ_all_plain _) |- _ => inversion H
  | H : is_ttyp typ_hole |- _ => inversion H
  | H : is_ttyp (typ_tophole _) |- _ => inversion H
  | H : is_ttyp (typ_all_col _ _) |- _ => inversion H
  | H : is_ttyp (typ_all_plain _) |- _ => inversion H
  | H : is_utyp typ_hole |- _ => inversion H
  | H : is_utyp (typ_tophole _) |- _ => inversion H
  | H : is_utyp (typ_all_col _ _) |- _ => inversion H
  | H : is_syn_typ typ_hole |- _ => inversion H
  | H : is_syn_typ (typ_tophole _) |- _ => inversion H
  | H : is_syn_typ (typ_all_etag _ _) |- _ => inversion H
  | H : is_syn_typ (typ_all_plain _) |- _ => inversion H
  | H : is_syn_typ (typ_all_col colour_inh _) |- _ => inversion H
  | H : is_inh_typ typ_hole |- _ => inversion H
  | H : is_inh_typ (typ_tophole _) |- _ => inversion H
  | H : is_inh_typ (typ_all_etag _ _) |- _ => inversion H
  | H : is_inh_typ (typ_all_plain _) |- _ => inversion H
  | H : is_inh_typ (typ_all_col colour_syn _) |- _ => inversion H
  | H : is_skel (typ_all_etag _ _) |- _ => inversion H
  | H : is_skel (typ_all_plain _) |- _ => inversion H
  | H : is_tskel (typ_all_col _ _) |- _ => inversion H
  | H : is_tskel (typ_all_plain _) |- _ => inversion H
  | H : is_uskel (typ_all_col _ _) |- _ => inversion H
  end.

(** Override Metalib's [gather_atoms] to include every atom-bearing
    source in our context: name-sets [atoms], single atoms, term
    contexts ([list (atom * dbind)]), tag / Ψ-scope contexts
    ([list atom]), and free-variable functions on [typ] / [exp].

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
  let G := gather_atoms_with (fun x : typ => ftvar_in_typ x) in
  constr:(A `union` B `union` C `union` D `union` E `union` F `union` G).

(** Apply a cofinite-quantified rule [R] using [gather_atoms] as the
    freshness set. Replaces [apply R with (L := L `union` ... `union` dom Γ)]. *)
Tactic Notation "inst_cofinites_for" constr(R) :=
  let _L := gather_atoms in
  apply R with (L := _L).

Tactic Notation "inst_cofinites_for" constr(R) ident(name) ":=" constr(val) :=
  let _L := gather_atoms in
  apply R with (L := _L) (name := val).
