Require Import Coq.Program.Equality.
Require Export Metalib.Metatheory.

Require Import src.fresco.notations.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (atom * dbind) => dom x) in
  let E := gather_atoms_with (fun x : exp => fvar_in_exp x) in
  let F := gather_atoms_with (fun x : exp => ftvar_in_exp x) in
  let G := gather_atoms_with (fun x : ptyp => ftvar_in_ptyp x) in
  let H := gather_atoms_with (fun x : btyp => ftvar_in_btyp x) in
  let I := gather_atoms_with (fun x : utyp => ftvar_in_utyp x) in
  let J := gather_atoms_with (fun x : pskl => ftvar_in_pskl x) in
  let K := gather_atoms_with (fun x : bskl => ftvar_in_bskl x) in
  let L := gather_atoms_with (fun x : uskl => ftvar_in_uskl x) in
  constr:(A `union` B `union` C `union` E `union` F `union`
          G `union` H `union` I `union` J `union` K `union` L).

Tactic Notation "inst_cofinites_for" constr(R) :=
  let _L := gather_atoms in
  apply R with (L := _L).

Tactic Notation "inst_cofinites_for" constr(R) ident(name) ":=" constr(val) :=
  let _L := gather_atoms in
  apply R with (L := _L) (name := val).

Tactic Notation "destruct_if" :=
  match goal with |- context [ if ?e then _ else _ ] => destruct e end.
Tactic Notation "destruct_if" "as" simple_intropattern(pat) :=
  match goal with |- context [ if ?e then _ else _ ] => destruct e as pat end.

Ltac fsetdec_empty :=
  match goal with H : _ [=] empty |- _ => clear - H; fsetdec end.

Ltac inv_guarded_ghost :=
  match goal with H : guarded_pskl pskl_ghost |- _ => inversion H end.

Ltac keep_only_subject :=
  match goal with
  | |- ?v `notin` _ =>
      repeat match goal with
             | H : ?w `notin` _ |- _ =>
                 tryif constr_eq w v then fail else clear H
             end
  end.

Ltac two_foreign_notin :=
  match goal with
  | |- ?v `notin` _ =>
      match goal with
      | H1 : ?w1 `notin` _, H2 : ?w2 `notin` _ |- _ =>
          tryif constr_eq H1 H2 then fail else
          tryif constr_eq w1 v  then fail else
          tryif constr_eq w2 v  then fail else idtac
      end
  end.

Ltac solve_notin_auto :=
  first [ assumption
        | tryif two_foreign_notin
          then first [ solve [ keep_only_subject; fsetdec ]
                     | solve [ destruct_notin; fsetdec ] ]
          else first [ solve [ destruct_notin; fsetdec ]
                     | solve [ keep_only_subject; fsetdec ] ]
        | solve [ solve_notin ]
        | fsetdec ].
