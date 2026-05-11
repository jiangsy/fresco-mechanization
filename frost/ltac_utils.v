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
