Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export frost.def_ott.

Local Set Warnings "-non-recursive". 

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme ptyp_ind' := Induction for ptyp Sort Prop.

Combined Scheme ptyp_mutind from ptyp_ind'.

Scheme ptyp_rec' := Induction for ptyp Sort Set.

Combined Scheme ptyp_mutrec from ptyp_rec'.

Scheme btyp_ind' := Induction for btyp Sort Prop.

Combined Scheme btyp_mutind from btyp_ind'.

Scheme btyp_rec' := Induction for btyp Sort Set.

Combined Scheme btyp_mutrec from btyp_rec'.

Scheme utyp_ind' := Induction for utyp Sort Prop.

Combined Scheme utyp_mutind from utyp_ind'.

Scheme utyp_rec' := Induction for utyp Sort Set.

Combined Scheme utyp_mutrec from utyp_rec'.

Scheme pskel_ind' := Induction for pskel Sort Prop.

Combined Scheme pskel_mutind from pskel_ind'.

Scheme pskel_rec' := Induction for pskel Sort Set.

Combined Scheme pskel_mutrec from pskel_rec'.

Scheme bskel_ind' := Induction for bskel Sort Prop.

Combined Scheme bskel_mutind from bskel_ind'.

Scheme bskel_rec' := Induction for bskel Sort Set.

Combined Scheme bskel_mutrec from bskel_rec'.

Scheme uskel_ind' := Induction for uskel Sort Prop.

Combined Scheme uskel_mutind from uskel_ind'.

Scheme uskel_rec' := Induction for uskel Sort Set.

Combined Scheme uskel_mutrec from uskel_rec'.

Scheme exp_ind' := Induction for exp Sort Prop.

Combined Scheme exp_mutind from exp_ind'.

Scheme exp_rec' := Induction for exp Sort Set.

Combined Scheme exp_mutrec from exp_rec'.

Scheme mode_ind' := Induction for mode Sort Prop.

Combined Scheme mode_mutind from mode_ind'.

Scheme mode_rec' := Induction for mode Sort Set.

Combined Scheme mode_mutrec from mode_rec'.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_ptyp_wrt_ptyp_rec (n1 : nat) (Xpt1 : ptypvar) (A1 : ptyp) {struct A1} : ptyp :=
  match A1 with
    | ptyp_unit => ptyp_unit
    | ptyp_var_f Xpt2 => if (Xpt1 == Xpt2) then (ptyp_var_b n1) else (ptyp_var_f Xpt2)
    | ptyp_var_b n2 => if (lt_ge_dec n2 n1) then (ptyp_var_b n2) else (ptyp_var_b (S n2))
    | ptyp_arrow A2 A3 => ptyp_arrow (close_ptyp_wrt_ptyp_rec n1 Xpt1 A2) (close_ptyp_wrt_ptyp_rec n1 Xpt1 A3)
    | ptyp_all A2 => ptyp_all (close_ptyp_wrt_ptyp_rec (S n1) Xpt1 A2)
  end.

Definition close_ptyp_wrt_ptyp Xpt1 A1 := close_ptyp_wrt_ptyp_rec 0 Xpt1 A1.

Fixpoint close_btyp_wrt_btyp_rec (n1 : nat) (Xbt1 : btypvar) (B1 : btyp) {struct B1} : btyp :=
  match B1 with
    | btyp_unit => btyp_unit
    | btyp_var_f Xbt2 => if (Xbt1 == Xbt2) then (btyp_var_b n1) else (btyp_var_f Xbt2)
    | btyp_var_b n2 => if (lt_ge_dec n2 n1) then (btyp_var_b n2) else (btyp_var_b (S n2))
    | btyp_arrow => btyp_arrow
    | btyp_all_syn B2 => btyp_all_syn (close_btyp_wrt_btyp_rec (S n1) Xbt1 B2)
    | btyp_all_inh B2 => btyp_all_inh (close_btyp_wrt_btyp_rec (S n1) Xbt1 B2)
  end.

Definition close_btyp_wrt_btyp Xbt1 B1 := close_btyp_wrt_btyp_rec 0 Xbt1 B1.

Fixpoint close_utyp_wrt_utyp_rec (n1 : nat) (Xut1 : utypvar) (C1 : utyp) {struct C1} : utyp :=
  match C1 with
    | utyp_unit => utyp_unit
    | utyp_var_f Xut2 => if (Xut1 == Xut2) then (utyp_var_b n1) else (utyp_var_f Xut2)
    | utyp_var_b n2 => if (lt_ge_dec n2 n1) then (utyp_var_b n2) else (utyp_var_b (S n2))
    | utyp_arrow C2 C3 => utyp_arrow (close_utyp_wrt_utyp_rec n1 Xut1 C2) (close_utyp_wrt_utyp_rec n1 Xut1 C3)
    | utyp_all_syn C2 => utyp_all_syn (close_utyp_wrt_utyp_rec (S n1) Xut1 C2)
    | utyp_all_etag ε1 C2 => utyp_all_etag ε1 (close_utyp_wrt_utyp_rec (S n1) Xut1 C2)
  end.

Definition close_utyp_wrt_utyp Xut1 C1 := close_utyp_wrt_utyp_rec 0 Xut1 C1.

Fixpoint close_pskel_wrt_pskel_rec (n1 : nat) (Xps1 : psklvar) (P1 : pskel) {struct P1} : pskel :=
  match P1 with
    | pskel_unit => pskel_unit
    | pskel_var_f Xps2 => if (Xps1 == Xps2) then (pskel_var_b n1) else (pskel_var_f Xps2)
    | pskel_var_b n2 => if (lt_ge_dec n2 n1) then (pskel_var_b n2) else (pskel_var_b (S n2))
    | pskel_arrow P2 P3 => pskel_arrow (close_pskel_wrt_pskel_rec n1 Xps1 P2) (close_pskel_wrt_pskel_rec n1 Xps1 P3)
    | pskel_all_syn P2 => pskel_all_syn (close_pskel_wrt_pskel_rec (S n1) Xps1 P2)
    | pskel_hole => pskel_hole
    | pskel_tophole P2 => pskel_tophole (close_pskel_wrt_pskel_rec n1 Xps1 P2)
  end.

Definition close_pskel_wrt_pskel Xps1 P1 := close_pskel_wrt_pskel_rec 0 Xps1 P1.

Fixpoint close_bskel_wrt_bskel_rec (n1 : nat) (Xbs1 : bsklvar) (Q1 : bskel) {struct Q1} : bskel :=
  match Q1 with
    | bskel_unit => bskel_unit
    | bskel_var_f Xbs2 => if (Xbs1 == Xbs2) then (bskel_var_b n1) else (bskel_var_f Xbs2)
    | bskel_var_b n2 => if (lt_ge_dec n2 n1) then (bskel_var_b n2) else (bskel_var_b (S n2))
    | bskel_arrow Q2 Q3 => bskel_arrow (close_bskel_wrt_bskel_rec n1 Xbs1 Q2) (close_bskel_wrt_bskel_rec n1 Xbs1 Q3)
    | bskel_all_syn Q2 => bskel_all_syn (close_bskel_wrt_bskel_rec (S n1) Xbs1 Q2)
    | bskel_all_inh Q2 => bskel_all_inh (close_bskel_wrt_bskel_rec (S n1) Xbs1 Q2)
    | bskel_hole => bskel_hole
    | bskel_tophole Q2 => bskel_tophole (close_bskel_wrt_bskel_rec n1 Xbs1 Q2)
  end.

Definition close_bskel_wrt_bskel Xbs1 Q1 := close_bskel_wrt_bskel_rec 0 Xbs1 Q1.

Fixpoint close_uskel_wrt_uskel_rec (n1 : nat) (Xus1 : usklvar) (R1 : uskel) {struct R1} : uskel :=
  match R1 with
    | uskel_unit => uskel_unit
    | uskel_var_f Xus2 => if (Xus1 == Xus2) then (uskel_var_b n1) else (uskel_var_f Xus2)
    | uskel_var_b n2 => if (lt_ge_dec n2 n1) then (uskel_var_b n2) else (uskel_var_b (S n2))
    | uskel_arrow R2 R3 => uskel_arrow (close_uskel_wrt_uskel_rec n1 Xus1 R2) (close_uskel_wrt_uskel_rec n1 Xus1 R3)
    | uskel_all_syn R2 => uskel_all_syn (close_uskel_wrt_uskel_rec (S n1) Xus1 R2)
    | uskel_all_etag ε1 R2 => uskel_all_etag ε1 (close_uskel_wrt_uskel_rec (S n1) Xus1 R2)
    | uskel_hole => uskel_hole
    | uskel_tophole R2 => uskel_tophole (close_uskel_wrt_uskel_rec n1 Xus1 R2)
  end.

Definition close_uskel_wrt_uskel Xus1 R1 := close_uskel_wrt_uskel_rec 0 Xus1 R1.

Fixpoint close_exp_wrt_ptyp_rec (n1 : nat) (Xpt1 : ptypvar) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | exp_unit => exp_unit
    | exp_var_f x1 => exp_var_f x1
    | exp_var_b n2 => exp_var_b n2
    | exp_abs e2 => exp_abs (close_exp_wrt_ptyp_rec n1 Xpt1 e2)
    | exp_abs_anno A1 e2 => exp_abs_anno (close_ptyp_wrt_ptyp_rec n1 Xpt1 A1) (close_exp_wrt_ptyp_rec n1 Xpt1 e2)
    | exp_app e2 e3 => exp_app (close_exp_wrt_ptyp_rec n1 Xpt1 e2) (close_exp_wrt_ptyp_rec n1 Xpt1 e3)
    | exp_anno e2 A1 => exp_anno (close_exp_wrt_ptyp_rec n1 Xpt1 e2) (close_ptyp_wrt_ptyp_rec n1 Xpt1 A1)
    | exp_freeze e2 => exp_freeze (close_exp_wrt_ptyp_rec n1 Xpt1 e2)
  end.

Fixpoint close_exp_wrt_exp_rec (n1 : nat) (x1 : expvar) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | exp_unit => exp_unit
    | exp_var_f x2 => if (x1 == x2) then (exp_var_b n1) else (exp_var_f x2)
    | exp_var_b n2 => if (lt_ge_dec n2 n1) then (exp_var_b n2) else (exp_var_b (S n2))
    | exp_abs e2 => exp_abs (close_exp_wrt_exp_rec (S n1) x1 e2)
    | exp_abs_anno A1 e2 => exp_abs_anno A1 (close_exp_wrt_exp_rec (S n1) x1 e2)
    | exp_app e2 e3 => exp_app (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
    | exp_anno e2 A1 => exp_anno (close_exp_wrt_exp_rec n1 x1 e2) A1
    | exp_freeze e2 => exp_freeze (close_exp_wrt_exp_rec n1 x1 e2)
  end.

Definition close_exp_wrt_ptyp Xpt1 e1 := close_exp_wrt_ptyp_rec 0 Xpt1 e1.

Definition close_exp_wrt_exp x1 e1 := close_exp_wrt_exp_rec 0 x1 e1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_ptyp (A1 : ptyp) {struct A1} : nat :=
  match A1 with
    | ptyp_unit => 1
    | ptyp_var_f Xpt1 => 1
    | ptyp_var_b n1 => 1
    | ptyp_arrow A2 A3 => 1 + (size_ptyp A2) + (size_ptyp A3)
    | ptyp_all A2 => 1 + (size_ptyp A2)
  end.

Fixpoint size_btyp (B1 : btyp) {struct B1} : nat :=
  match B1 with
    | btyp_unit => 1
    | btyp_var_f Xbt1 => 1
    | btyp_var_b n1 => 1
    | btyp_arrow => 1
    | btyp_all_syn B2 => 1 + (size_btyp B2)
    | btyp_all_inh B2 => 1 + (size_btyp B2)
  end.

Fixpoint size_utyp (C1 : utyp) {struct C1} : nat :=
  match C1 with
    | utyp_unit => 1
    | utyp_var_f Xut1 => 1
    | utyp_var_b n1 => 1
    | utyp_arrow C2 C3 => 1 + (size_utyp C2) + (size_utyp C3)
    | utyp_all_syn C2 => 1 + (size_utyp C2)
    | utyp_all_etag ε1 C2 => 1 + (size_utyp C2)
  end.

Fixpoint size_pskel (P1 : pskel) {struct P1} : nat :=
  match P1 with
    | pskel_unit => 1
    | pskel_var_f Xps1 => 1
    | pskel_var_b n1 => 1
    | pskel_arrow P2 P3 => 1 + (size_pskel P2) + (size_pskel P3)
    | pskel_all_syn P2 => 1 + (size_pskel P2)
    | pskel_hole => 1
    | pskel_tophole P2 => 1 + (size_pskel P2)
  end.

Fixpoint size_bskel (Q1 : bskel) {struct Q1} : nat :=
  match Q1 with
    | bskel_unit => 1
    | bskel_var_f Xbs1 => 1
    | bskel_var_b n1 => 1
    | bskel_arrow Q2 Q3 => 1 + (size_bskel Q2) + (size_bskel Q3)
    | bskel_all_syn Q2 => 1 + (size_bskel Q2)
    | bskel_all_inh Q2 => 1 + (size_bskel Q2)
    | bskel_hole => 1
    | bskel_tophole Q2 => 1 + (size_bskel Q2)
  end.

Fixpoint size_uskel (R1 : uskel) {struct R1} : nat :=
  match R1 with
    | uskel_unit => 1
    | uskel_var_f Xus1 => 1
    | uskel_var_b n1 => 1
    | uskel_arrow R2 R3 => 1 + (size_uskel R2) + (size_uskel R3)
    | uskel_all_syn R2 => 1 + (size_uskel R2)
    | uskel_all_etag ε1 R2 => 1 + (size_uskel R2)
    | uskel_hole => 1
    | uskel_tophole R2 => 1 + (size_uskel R2)
  end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | exp_unit => 1
    | exp_var_f x1 => 1
    | exp_var_b n1 => 1
    | exp_abs e2 => 1 + (size_exp e2)
    | exp_abs_anno A1 e2 => 1 + (size_ptyp A1) + (size_exp e2)
    | exp_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | exp_anno e2 A1 => 1 + (size_exp e2) + (size_ptyp A1)
    | exp_freeze e2 => 1 + (size_exp e2)
  end.

Fixpoint size_mode (m1 : mode) {struct m1} : nat :=
  match m1 with
    | mode_ti => 1
    | mode_tc => 1
    | mode_fn m2 => 1 + (size_mode m2)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_ptyp_wrt_ptyp : nat -> ptyp -> Prop :=
  | degree_wrt_ptyp_ptyp_unit : forall n1,
    degree_ptyp_wrt_ptyp n1 (ptyp_unit)
  | degree_wrt_ptyp_ptyp_var_f : forall n1 Xpt1,
    degree_ptyp_wrt_ptyp n1 (ptyp_var_f Xpt1)
  | degree_wrt_ptyp_ptyp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_ptyp_wrt_ptyp n1 (ptyp_var_b n2)
  | degree_wrt_ptyp_ptyp_arrow : forall n1 A1 A2,
    degree_ptyp_wrt_ptyp n1 A1 ->
    degree_ptyp_wrt_ptyp n1 A2 ->
    degree_ptyp_wrt_ptyp n1 (ptyp_arrow A1 A2)
  | degree_wrt_ptyp_ptyp_all : forall n1 A1,
    degree_ptyp_wrt_ptyp (S n1) A1 ->
    degree_ptyp_wrt_ptyp n1 (ptyp_all A1).

Scheme degree_ptyp_wrt_ptyp_ind' := Induction for degree_ptyp_wrt_ptyp Sort Prop.

Combined Scheme degree_ptyp_wrt_ptyp_mutind from degree_ptyp_wrt_ptyp_ind'.

#[export] Hint Constructors degree_ptyp_wrt_ptyp : core lngen.

Inductive degree_btyp_wrt_btyp : nat -> btyp -> Prop :=
  | degree_wrt_btyp_btyp_unit : forall n1,
    degree_btyp_wrt_btyp n1 (btyp_unit)
  | degree_wrt_btyp_btyp_var_f : forall n1 Xbt1,
    degree_btyp_wrt_btyp n1 (btyp_var_f Xbt1)
  | degree_wrt_btyp_btyp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_btyp_wrt_btyp n1 (btyp_var_b n2)
  | degree_wrt_btyp_btyp_arrow : forall n1,
    degree_btyp_wrt_btyp n1 (btyp_arrow)
  | degree_wrt_btyp_btyp_all_syn : forall n1 B1,
    degree_btyp_wrt_btyp (S n1) B1 ->
    degree_btyp_wrt_btyp n1 (btyp_all_syn B1)
  | degree_wrt_btyp_btyp_all_inh : forall n1 B1,
    degree_btyp_wrt_btyp (S n1) B1 ->
    degree_btyp_wrt_btyp n1 (btyp_all_inh B1).

Scheme degree_btyp_wrt_btyp_ind' := Induction for degree_btyp_wrt_btyp Sort Prop.

Combined Scheme degree_btyp_wrt_btyp_mutind from degree_btyp_wrt_btyp_ind'.

#[export] Hint Constructors degree_btyp_wrt_btyp : core lngen.

Inductive degree_utyp_wrt_utyp : nat -> utyp -> Prop :=
  | degree_wrt_utyp_utyp_unit : forall n1,
    degree_utyp_wrt_utyp n1 (utyp_unit)
  | degree_wrt_utyp_utyp_var_f : forall n1 Xut1,
    degree_utyp_wrt_utyp n1 (utyp_var_f Xut1)
  | degree_wrt_utyp_utyp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_utyp_wrt_utyp n1 (utyp_var_b n2)
  | degree_wrt_utyp_utyp_arrow : forall n1 C1 C2,
    degree_utyp_wrt_utyp n1 C1 ->
    degree_utyp_wrt_utyp n1 C2 ->
    degree_utyp_wrt_utyp n1 (utyp_arrow C1 C2)
  | degree_wrt_utyp_utyp_all_syn : forall n1 C1,
    degree_utyp_wrt_utyp (S n1) C1 ->
    degree_utyp_wrt_utyp n1 (utyp_all_syn C1)
  | degree_wrt_utyp_utyp_all_etag : forall n1 ε1 C1,
    degree_utyp_wrt_utyp (S n1) C1 ->
    degree_utyp_wrt_utyp n1 (utyp_all_etag ε1 C1).

Scheme degree_utyp_wrt_utyp_ind' := Induction for degree_utyp_wrt_utyp Sort Prop.

Combined Scheme degree_utyp_wrt_utyp_mutind from degree_utyp_wrt_utyp_ind'.

#[export] Hint Constructors degree_utyp_wrt_utyp : core lngen.

Inductive degree_pskel_wrt_pskel : nat -> pskel -> Prop :=
  | degree_wrt_pskel_pskel_unit : forall n1,
    degree_pskel_wrt_pskel n1 (pskel_unit)
  | degree_wrt_pskel_pskel_var_f : forall n1 Xps1,
    degree_pskel_wrt_pskel n1 (pskel_var_f Xps1)
  | degree_wrt_pskel_pskel_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_pskel_wrt_pskel n1 (pskel_var_b n2)
  | degree_wrt_pskel_pskel_arrow : forall n1 P1 P2,
    degree_pskel_wrt_pskel n1 P1 ->
    degree_pskel_wrt_pskel n1 P2 ->
    degree_pskel_wrt_pskel n1 (pskel_arrow P1 P2)
  | degree_wrt_pskel_pskel_all_syn : forall n1 P1,
    degree_pskel_wrt_pskel (S n1) P1 ->
    degree_pskel_wrt_pskel n1 (pskel_all_syn P1)
  | degree_wrt_pskel_pskel_hole : forall n1,
    degree_pskel_wrt_pskel n1 (pskel_hole)
  | degree_wrt_pskel_pskel_tophole : forall n1 P1,
    degree_pskel_wrt_pskel n1 P1 ->
    degree_pskel_wrt_pskel n1 (pskel_tophole P1).

Scheme degree_pskel_wrt_pskel_ind' := Induction for degree_pskel_wrt_pskel Sort Prop.

Combined Scheme degree_pskel_wrt_pskel_mutind from degree_pskel_wrt_pskel_ind'.

#[export] Hint Constructors degree_pskel_wrt_pskel : core lngen.

Inductive degree_bskel_wrt_bskel : nat -> bskel -> Prop :=
  | degree_wrt_bskel_bskel_unit : forall n1,
    degree_bskel_wrt_bskel n1 (bskel_unit)
  | degree_wrt_bskel_bskel_var_f : forall n1 Xbs1,
    degree_bskel_wrt_bskel n1 (bskel_var_f Xbs1)
  | degree_wrt_bskel_bskel_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_bskel_wrt_bskel n1 (bskel_var_b n2)
  | degree_wrt_bskel_bskel_arrow : forall n1 Q1 Q2,
    degree_bskel_wrt_bskel n1 Q1 ->
    degree_bskel_wrt_bskel n1 Q2 ->
    degree_bskel_wrt_bskel n1 (bskel_arrow Q1 Q2)
  | degree_wrt_bskel_bskel_all_syn : forall n1 Q1,
    degree_bskel_wrt_bskel (S n1) Q1 ->
    degree_bskel_wrt_bskel n1 (bskel_all_syn Q1)
  | degree_wrt_bskel_bskel_all_inh : forall n1 Q1,
    degree_bskel_wrt_bskel (S n1) Q1 ->
    degree_bskel_wrt_bskel n1 (bskel_all_inh Q1)
  | degree_wrt_bskel_bskel_hole : forall n1,
    degree_bskel_wrt_bskel n1 (bskel_hole)
  | degree_wrt_bskel_bskel_tophole : forall n1 Q1,
    degree_bskel_wrt_bskel n1 Q1 ->
    degree_bskel_wrt_bskel n1 (bskel_tophole Q1).

Scheme degree_bskel_wrt_bskel_ind' := Induction for degree_bskel_wrt_bskel Sort Prop.

Combined Scheme degree_bskel_wrt_bskel_mutind from degree_bskel_wrt_bskel_ind'.

#[export] Hint Constructors degree_bskel_wrt_bskel : core lngen.

Inductive degree_uskel_wrt_uskel : nat -> uskel -> Prop :=
  | degree_wrt_uskel_uskel_unit : forall n1,
    degree_uskel_wrt_uskel n1 (uskel_unit)
  | degree_wrt_uskel_uskel_var_f : forall n1 Xus1,
    degree_uskel_wrt_uskel n1 (uskel_var_f Xus1)
  | degree_wrt_uskel_uskel_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_uskel_wrt_uskel n1 (uskel_var_b n2)
  | degree_wrt_uskel_uskel_arrow : forall n1 R1 R2,
    degree_uskel_wrt_uskel n1 R1 ->
    degree_uskel_wrt_uskel n1 R2 ->
    degree_uskel_wrt_uskel n1 (uskel_arrow R1 R2)
  | degree_wrt_uskel_uskel_all_syn : forall n1 R1,
    degree_uskel_wrt_uskel (S n1) R1 ->
    degree_uskel_wrt_uskel n1 (uskel_all_syn R1)
  | degree_wrt_uskel_uskel_all_etag : forall n1 ε1 R1,
    degree_uskel_wrt_uskel (S n1) R1 ->
    degree_uskel_wrt_uskel n1 (uskel_all_etag ε1 R1)
  | degree_wrt_uskel_uskel_hole : forall n1,
    degree_uskel_wrt_uskel n1 (uskel_hole)
  | degree_wrt_uskel_uskel_tophole : forall n1 R1,
    degree_uskel_wrt_uskel n1 R1 ->
    degree_uskel_wrt_uskel n1 (uskel_tophole R1).

Scheme degree_uskel_wrt_uskel_ind' := Induction for degree_uskel_wrt_uskel Sort Prop.

Combined Scheme degree_uskel_wrt_uskel_mutind from degree_uskel_wrt_uskel_ind'.

#[export] Hint Constructors degree_uskel_wrt_uskel : core lngen.

Inductive degree_exp_wrt_ptyp : nat -> exp -> Prop :=
  | degree_wrt_ptyp_exp_unit : forall n1,
    degree_exp_wrt_ptyp n1 (exp_unit)
  | degree_wrt_ptyp_exp_var_f : forall n1 x1,
    degree_exp_wrt_ptyp n1 (exp_var_f x1)
  | degree_wrt_ptyp_exp_var_b : forall n1 n2,
    degree_exp_wrt_ptyp n1 (exp_var_b n2)
  | degree_wrt_ptyp_exp_abs : forall n1 e1,
    degree_exp_wrt_ptyp n1 e1 ->
    degree_exp_wrt_ptyp n1 (exp_abs e1)
  | degree_wrt_ptyp_exp_abs_anno : forall n1 A1 e1,
    degree_ptyp_wrt_ptyp n1 A1 ->
    degree_exp_wrt_ptyp n1 e1 ->
    degree_exp_wrt_ptyp n1 (exp_abs_anno A1 e1)
  | degree_wrt_ptyp_exp_app : forall n1 e1 e2,
    degree_exp_wrt_ptyp n1 e1 ->
    degree_exp_wrt_ptyp n1 e2 ->
    degree_exp_wrt_ptyp n1 (exp_app e1 e2)
  | degree_wrt_ptyp_exp_anno : forall n1 e1 A1,
    degree_exp_wrt_ptyp n1 e1 ->
    degree_ptyp_wrt_ptyp n1 A1 ->
    degree_exp_wrt_ptyp n1 (exp_anno e1 A1)
  | degree_wrt_ptyp_exp_freeze : forall n1 e1,
    degree_exp_wrt_ptyp n1 e1 ->
    degree_exp_wrt_ptyp n1 (exp_freeze e1).

Inductive degree_exp_wrt_exp : nat -> exp -> Prop :=
  | degree_wrt_exp_exp_unit : forall n1,
    degree_exp_wrt_exp n1 (exp_unit)
  | degree_wrt_exp_exp_var_f : forall n1 x1,
    degree_exp_wrt_exp n1 (exp_var_f x1)
  | degree_wrt_exp_exp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_exp_wrt_exp n1 (exp_var_b n2)
  | degree_wrt_exp_exp_abs : forall n1 e1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (exp_abs e1)
  | degree_wrt_exp_exp_abs_anno : forall n1 A1 e1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (exp_abs_anno A1 e1)
  | degree_wrt_exp_exp_app : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (exp_app e1 e2)
  | degree_wrt_exp_exp_anno : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_anno e1 A1)
  | degree_wrt_exp_exp_freeze : forall n1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_freeze e1).

Scheme degree_exp_wrt_ptyp_ind' := Induction for degree_exp_wrt_ptyp Sort Prop.

Combined Scheme degree_exp_wrt_ptyp_mutind from degree_exp_wrt_ptyp_ind'.

Scheme degree_exp_wrt_exp_ind' := Induction for degree_exp_wrt_exp Sort Prop.

Combined Scheme degree_exp_wrt_exp_mutind from degree_exp_wrt_exp_ind'.

#[export] Hint Constructors degree_exp_wrt_ptyp : core lngen.

#[export] Hint Constructors degree_exp_wrt_exp : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_ptyp : ptyp -> Set :=
  | lc_set_ptyp_unit :
    lc_set_ptyp (ptyp_unit)
  | lc_set_ptyp_var_f : forall Xpt1,
    lc_set_ptyp (ptyp_var_f Xpt1)
  | lc_set_ptyp_arrow : forall A1 A2,
    lc_set_ptyp A1 ->
    lc_set_ptyp A2 ->
    lc_set_ptyp (ptyp_arrow A1 A2)
  | lc_set_ptyp_all : forall A1,
    (forall Xpt1 : ptypvar, lc_set_ptyp (open_ptyp_wrt_ptyp A1 (ptyp_var_f Xpt1))) ->
    lc_set_ptyp (ptyp_all A1).
Scheme lc_ptyp_ind' := Induction for lc_ptyp Sort Prop.

Combined Scheme lc_ptyp_mutind from lc_ptyp_ind'.

Scheme lc_set_ptyp_ind' := Induction for lc_set_ptyp Sort Prop.

Combined Scheme lc_set_ptyp_mutind from lc_set_ptyp_ind'.

Scheme lc_set_ptyp_rec' := Induction for lc_set_ptyp Sort Set.

Combined Scheme lc_set_ptyp_mutrec from lc_set_ptyp_rec'.

#[export] Hint Constructors lc_ptyp : core lngen.

#[export] Hint Constructors lc_set_ptyp : core lngen.

Inductive lc_set_btyp : btyp -> Set :=
  | lc_set_btyp_unit :
    lc_set_btyp (btyp_unit)
  | lc_set_btyp_var_f : forall Xbt1,
    lc_set_btyp (btyp_var_f Xbt1)
  | lc_set_btyp_arrow :
    lc_set_btyp (btyp_arrow)
  | lc_set_btyp_all_syn : forall B1,
    (forall Xbt1 : btypvar, lc_set_btyp (open_btyp_wrt_btyp B1 (btyp_var_f Xbt1))) ->
    lc_set_btyp (btyp_all_syn B1)
  | lc_set_btyp_all_inh : forall B1,
    (forall Xbt1 : btypvar, lc_set_btyp (open_btyp_wrt_btyp B1 (btyp_var_f Xbt1))) ->
    lc_set_btyp (btyp_all_inh B1).
Scheme lc_btyp_ind' := Induction for lc_btyp Sort Prop.

Combined Scheme lc_btyp_mutind from lc_btyp_ind'.

Scheme lc_set_btyp_ind' := Induction for lc_set_btyp Sort Prop.

Combined Scheme lc_set_btyp_mutind from lc_set_btyp_ind'.

Scheme lc_set_btyp_rec' := Induction for lc_set_btyp Sort Set.

Combined Scheme lc_set_btyp_mutrec from lc_set_btyp_rec'.

#[export] Hint Constructors lc_btyp : core lngen.

#[export] Hint Constructors lc_set_btyp : core lngen.

Inductive lc_set_utyp : utyp -> Set :=
  | lc_set_utyp_unit :
    lc_set_utyp (utyp_unit)
  | lc_set_utyp_var_f : forall Xut1,
    lc_set_utyp (utyp_var_f Xut1)
  | lc_set_utyp_arrow : forall C1 C2,
    lc_set_utyp C1 ->
    lc_set_utyp C2 ->
    lc_set_utyp (utyp_arrow C1 C2)
  | lc_set_utyp_all_syn : forall C1,
    (forall Xut1 : utypvar, lc_set_utyp (open_utyp_wrt_utyp C1 (utyp_var_f Xut1))) ->
    lc_set_utyp (utyp_all_syn C1)
  | lc_set_utyp_all_etag : forall ε1 C1,
    (forall Xut1 : utypvar, lc_set_utyp (open_utyp_wrt_utyp C1 (utyp_var_f Xut1))) ->
    lc_set_utyp (utyp_all_etag ε1 C1).
Scheme lc_utyp_ind' := Induction for lc_utyp Sort Prop.

Combined Scheme lc_utyp_mutind from lc_utyp_ind'.

Scheme lc_set_utyp_ind' := Induction for lc_set_utyp Sort Prop.

Combined Scheme lc_set_utyp_mutind from lc_set_utyp_ind'.

Scheme lc_set_utyp_rec' := Induction for lc_set_utyp Sort Set.

Combined Scheme lc_set_utyp_mutrec from lc_set_utyp_rec'.

#[export] Hint Constructors lc_utyp : core lngen.

#[export] Hint Constructors lc_set_utyp : core lngen.

Inductive lc_set_pskel : pskel -> Set :=
  | lc_set_pskel_unit :
    lc_set_pskel (pskel_unit)
  | lc_set_pskel_var_f : forall Xps1,
    lc_set_pskel (pskel_var_f Xps1)
  | lc_set_pskel_arrow : forall P1 P2,
    lc_set_pskel P1 ->
    lc_set_pskel P2 ->
    lc_set_pskel (pskel_arrow P1 P2)
  | lc_set_pskel_all_syn : forall P1,
    (forall Xps1 : psklvar, lc_set_pskel (open_pskel_wrt_pskel P1 (pskel_var_f Xps1))) ->
    lc_set_pskel (pskel_all_syn P1)
  | lc_set_pskel_hole :
    lc_set_pskel (pskel_hole)
  | lc_set_pskel_tophole : forall P1,
    lc_set_pskel P1 ->
    lc_set_pskel (pskel_tophole P1).
Scheme lc_pskel_ind' := Induction for lc_pskel Sort Prop.

Combined Scheme lc_pskel_mutind from lc_pskel_ind'.

Scheme lc_set_pskel_ind' := Induction for lc_set_pskel Sort Prop.

Combined Scheme lc_set_pskel_mutind from lc_set_pskel_ind'.

Scheme lc_set_pskel_rec' := Induction for lc_set_pskel Sort Set.

Combined Scheme lc_set_pskel_mutrec from lc_set_pskel_rec'.

#[export] Hint Constructors lc_pskel : core lngen.

#[export] Hint Constructors lc_set_pskel : core lngen.

Inductive lc_set_bskel : bskel -> Set :=
  | lc_set_bskel_unit :
    lc_set_bskel (bskel_unit)
  | lc_set_bskel_var_f : forall Xbs1,
    lc_set_bskel (bskel_var_f Xbs1)
  | lc_set_bskel_arrow : forall Q1 Q2,
    lc_set_bskel Q1 ->
    lc_set_bskel Q2 ->
    lc_set_bskel (bskel_arrow Q1 Q2)
  | lc_set_bskel_all_syn : forall Q1,
    (forall Xbs1 : bsklvar, lc_set_bskel (open_bskel_wrt_bskel Q1 (bskel_var_f Xbs1))) ->
    lc_set_bskel (bskel_all_syn Q1)
  | lc_set_bskel_all_inh : forall Q1,
    (forall Xbs1 : bsklvar, lc_set_bskel (open_bskel_wrt_bskel Q1 (bskel_var_f Xbs1))) ->
    lc_set_bskel (bskel_all_inh Q1)
  | lc_set_bskel_hole :
    lc_set_bskel (bskel_hole)
  | lc_set_bskel_tophole : forall Q1,
    lc_set_bskel Q1 ->
    lc_set_bskel (bskel_tophole Q1).
Scheme lc_bskel_ind' := Induction for lc_bskel Sort Prop.

Combined Scheme lc_bskel_mutind from lc_bskel_ind'.

Scheme lc_set_bskel_ind' := Induction for lc_set_bskel Sort Prop.

Combined Scheme lc_set_bskel_mutind from lc_set_bskel_ind'.

Scheme lc_set_bskel_rec' := Induction for lc_set_bskel Sort Set.

Combined Scheme lc_set_bskel_mutrec from lc_set_bskel_rec'.

#[export] Hint Constructors lc_bskel : core lngen.

#[export] Hint Constructors lc_set_bskel : core lngen.

Inductive lc_set_uskel : uskel -> Set :=
  | lc_set_uskel_unit :
    lc_set_uskel (uskel_unit)
  | lc_set_uskel_var_f : forall Xus1,
    lc_set_uskel (uskel_var_f Xus1)
  | lc_set_uskel_arrow : forall R1 R2,
    lc_set_uskel R1 ->
    lc_set_uskel R2 ->
    lc_set_uskel (uskel_arrow R1 R2)
  | lc_set_uskel_all_syn : forall R1,
    (forall Xus1 : usklvar, lc_set_uskel (open_uskel_wrt_uskel R1 (uskel_var_f Xus1))) ->
    lc_set_uskel (uskel_all_syn R1)
  | lc_set_uskel_all_etag : forall ε1 R1,
    (forall Xus1 : usklvar, lc_set_uskel (open_uskel_wrt_uskel R1 (uskel_var_f Xus1))) ->
    lc_set_uskel (uskel_all_etag ε1 R1)
  | lc_set_uskel_hole :
    lc_set_uskel (uskel_hole)
  | lc_set_uskel_tophole : forall R1,
    lc_set_uskel R1 ->
    lc_set_uskel (uskel_tophole R1).
Scheme lc_uskel_ind' := Induction for lc_uskel Sort Prop.

Combined Scheme lc_uskel_mutind from lc_uskel_ind'.

Scheme lc_set_uskel_ind' := Induction for lc_set_uskel Sort Prop.

Combined Scheme lc_set_uskel_mutind from lc_set_uskel_ind'.

Scheme lc_set_uskel_rec' := Induction for lc_set_uskel Sort Set.

Combined Scheme lc_set_uskel_mutrec from lc_set_uskel_rec'.

#[export] Hint Constructors lc_uskel : core lngen.

#[export] Hint Constructors lc_set_uskel : core lngen.

Inductive lc_set_exp : exp -> Set :=
  | lc_set_exp_unit :
    lc_set_exp (exp_unit)
  | lc_set_exp_var_f : forall x1,
    lc_set_exp (exp_var_f x1)
  | lc_set_exp_abs : forall e1,
    (forall x1 : expvar, lc_set_exp (open_exp_wrt_exp e1 (exp_var_f x1))) ->
    lc_set_exp (exp_abs e1)
  | lc_set_exp_abs_anno : forall A1 e1,
    lc_set_ptyp A1 ->
    (forall x1 : expvar, lc_set_exp (open_exp_wrt_exp e1 (exp_var_f x1))) ->
    lc_set_exp (exp_abs_anno A1 e1)
  | lc_set_exp_app : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (exp_app e1 e2)
  | lc_set_exp_anno : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_ptyp A1 ->
    lc_set_exp (exp_anno e1 A1)
  | lc_set_exp_freeze : forall e1,
    lc_set_exp e1 ->
    lc_set_exp (exp_freeze e1).
Scheme lc_exp_ind' := Induction for lc_exp Sort Prop.

Combined Scheme lc_exp_mutind from lc_exp_ind'.

Scheme lc_set_exp_ind' := Induction for lc_set_exp Sort Prop.

Combined Scheme lc_set_exp_mutind from lc_set_exp_ind'.

Scheme lc_set_exp_rec' := Induction for lc_set_exp Sort Set.

Combined Scheme lc_set_exp_mutrec from lc_set_exp_rec'.

#[export] Hint Constructors lc_exp : core lngen.

#[export] Hint Constructors lc_set_exp : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_ptyp_wrt_ptyp A1 := forall Xpt1, lc_ptyp (open_ptyp_wrt_ptyp A1 (ptyp_var_f Xpt1)).

#[export] Hint Unfold body_ptyp_wrt_ptyp : core.

Definition body_btyp_wrt_btyp B1 := forall Xbt1, lc_btyp (open_btyp_wrt_btyp B1 (btyp_var_f Xbt1)).

#[export] Hint Unfold body_btyp_wrt_btyp : core.

Definition body_utyp_wrt_utyp C1 := forall Xut1, lc_utyp (open_utyp_wrt_utyp C1 (utyp_var_f Xut1)).

#[export] Hint Unfold body_utyp_wrt_utyp : core.

Definition body_pskel_wrt_pskel P1 := forall Xps1, lc_pskel (open_pskel_wrt_pskel P1 (pskel_var_f Xps1)).

#[export] Hint Unfold body_pskel_wrt_pskel : core.

Definition body_bskel_wrt_bskel Q1 := forall Xbs1, lc_bskel (open_bskel_wrt_bskel Q1 (bskel_var_f Xbs1)).

#[export] Hint Unfold body_bskel_wrt_bskel : core.

Definition body_uskel_wrt_uskel R1 := forall Xus1, lc_uskel (open_uskel_wrt_uskel R1 (uskel_var_f Xus1)).

#[export] Hint Unfold body_uskel_wrt_uskel : core.

Definition body_exp_wrt_ptyp e1 := forall Xpt1, lc_exp (open_exp_wrt_ptyp e1 (ptyp_var_f Xpt1)).

Definition body_exp_wrt_exp e1 := forall x1, lc_exp (open_exp_wrt_exp e1 (exp_var_f x1)).

#[export] Hint Unfold body_exp_wrt_ptyp : core.

#[export] Hint Unfold body_exp_wrt_exp : core.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

#[export] Hint Resolve Nat.add_le_mono : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_ptyp_min_mutual :
(forall A1, 1 <= size_ptyp A1).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_ptyp_min :
forall A1, 1 <= size_ptyp A1.
Proof.
pose proof size_ptyp_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ptyp_min : lngen.

(* begin hide *)

Lemma size_btyp_min_mutual :
(forall B1, 1 <= size_btyp B1).
Proof.
apply_mutual_ind btyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_btyp_min :
forall B1, 1 <= size_btyp B1.
Proof.
pose proof size_btyp_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_btyp_min : lngen.

(* begin hide *)

Lemma size_utyp_min_mutual :
(forall C1, 1 <= size_utyp C1).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_utyp_min :
forall C1, 1 <= size_utyp C1.
Proof.
pose proof size_utyp_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_utyp_min : lngen.

(* begin hide *)

Lemma size_pskel_min_mutual :
(forall P1, 1 <= size_pskel P1).
Proof.
apply_mutual_ind pskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_pskel_min :
forall P1, 1 <= size_pskel P1.
Proof.
pose proof size_pskel_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_pskel_min : lngen.

(* begin hide *)

Lemma size_bskel_min_mutual :
(forall Q1, 1 <= size_bskel Q1).
Proof.
apply_mutual_ind bskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_bskel_min :
forall Q1, 1 <= size_bskel Q1.
Proof.
pose proof size_bskel_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_bskel_min : lngen.

(* begin hide *)

Lemma size_uskel_min_mutual :
(forall R1, 1 <= size_uskel R1).
Proof.
apply_mutual_ind uskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_uskel_min :
forall R1, 1 <= size_uskel R1.
Proof.
pose proof size_uskel_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_uskel_min : lngen.

(* begin hide *)

Lemma size_exp_min_mutual :
(forall e1, 1 <= size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_exp_min :
forall e1, 1 <= size_exp e1.
Proof.
pose proof size_exp_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_min : lngen.

(* begin hide *)

Lemma size_mode_min_mutual :
(forall m1, 1 <= size_mode m1).
Proof.
apply_mutual_ind mode_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_mode_min :
forall m1, 1 <= size_mode m1.
Proof.
pose proof size_mode_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_mode_min : lngen.

(* begin hide *)

Lemma size_ptyp_close_ptyp_wrt_ptyp_rec_mutual :
(forall A1 Xpt1 n1,
  size_ptyp (close_ptyp_wrt_ptyp_rec n1 Xpt1 A1) = size_ptyp A1).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_ptyp_close_ptyp_wrt_ptyp_rec :
forall A1 Xpt1 n1,
  size_ptyp (close_ptyp_wrt_ptyp_rec n1 Xpt1 A1) = size_ptyp A1.
Proof.
pose proof size_ptyp_close_ptyp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ptyp_close_ptyp_wrt_ptyp_rec : lngen.
#[export] Hint Rewrite size_ptyp_close_ptyp_wrt_ptyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_btyp_close_btyp_wrt_btyp_rec_mutual :
(forall B1 Xbt1 n1,
  size_btyp (close_btyp_wrt_btyp_rec n1 Xbt1 B1) = size_btyp B1).
Proof.
apply_mutual_ind btyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_btyp_close_btyp_wrt_btyp_rec :
forall B1 Xbt1 n1,
  size_btyp (close_btyp_wrt_btyp_rec n1 Xbt1 B1) = size_btyp B1.
Proof.
pose proof size_btyp_close_btyp_wrt_btyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_btyp_close_btyp_wrt_btyp_rec : lngen.
#[export] Hint Rewrite size_btyp_close_btyp_wrt_btyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_utyp_close_utyp_wrt_utyp_rec_mutual :
(forall C1 Xut1 n1,
  size_utyp (close_utyp_wrt_utyp_rec n1 Xut1 C1) = size_utyp C1).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_utyp_close_utyp_wrt_utyp_rec :
forall C1 Xut1 n1,
  size_utyp (close_utyp_wrt_utyp_rec n1 Xut1 C1) = size_utyp C1.
Proof.
pose proof size_utyp_close_utyp_wrt_utyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_utyp_close_utyp_wrt_utyp_rec : lngen.
#[export] Hint Rewrite size_utyp_close_utyp_wrt_utyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_pskel_close_pskel_wrt_pskel_rec_mutual :
(forall P1 Xps1 n1,
  size_pskel (close_pskel_wrt_pskel_rec n1 Xps1 P1) = size_pskel P1).
Proof.
apply_mutual_ind pskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_pskel_close_pskel_wrt_pskel_rec :
forall P1 Xps1 n1,
  size_pskel (close_pskel_wrt_pskel_rec n1 Xps1 P1) = size_pskel P1.
Proof.
pose proof size_pskel_close_pskel_wrt_pskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_pskel_close_pskel_wrt_pskel_rec : lngen.
#[export] Hint Rewrite size_pskel_close_pskel_wrt_pskel_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_bskel_close_bskel_wrt_bskel_rec_mutual :
(forall Q1 Xbs1 n1,
  size_bskel (close_bskel_wrt_bskel_rec n1 Xbs1 Q1) = size_bskel Q1).
Proof.
apply_mutual_ind bskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_bskel_close_bskel_wrt_bskel_rec :
forall Q1 Xbs1 n1,
  size_bskel (close_bskel_wrt_bskel_rec n1 Xbs1 Q1) = size_bskel Q1.
Proof.
pose proof size_bskel_close_bskel_wrt_bskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_bskel_close_bskel_wrt_bskel_rec : lngen.
#[export] Hint Rewrite size_bskel_close_bskel_wrt_bskel_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_uskel_close_uskel_wrt_uskel_rec_mutual :
(forall R1 Xus1 n1,
  size_uskel (close_uskel_wrt_uskel_rec n1 Xus1 R1) = size_uskel R1).
Proof.
apply_mutual_ind uskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_uskel_close_uskel_wrt_uskel_rec :
forall R1 Xus1 n1,
  size_uskel (close_uskel_wrt_uskel_rec n1 Xus1 R1) = size_uskel R1.
Proof.
pose proof size_uskel_close_uskel_wrt_uskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_uskel_close_uskel_wrt_uskel_rec : lngen.
#[export] Hint Rewrite size_uskel_close_uskel_wrt_uskel_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_ptyp_rec_mutual :
(forall e1 Xpt1 n1,
  size_exp (close_exp_wrt_ptyp_rec n1 Xpt1 e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_ptyp_rec :
forall e1 Xpt1 n1,
  size_exp (close_exp_wrt_ptyp_rec n1 Xpt1 e1) = size_exp e1.
Proof.
pose proof size_exp_close_exp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_ptyp_rec : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_ptyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1.
Proof.
pose proof size_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_ptyp_close_ptyp_wrt_ptyp :
forall A1 Xpt1,
  size_ptyp (close_ptyp_wrt_ptyp Xpt1 A1) = size_ptyp A1.
Proof.
unfold close_ptyp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve size_ptyp_close_ptyp_wrt_ptyp : lngen.
#[export] Hint Rewrite size_ptyp_close_ptyp_wrt_ptyp using solve [auto] : lngen.

Lemma size_btyp_close_btyp_wrt_btyp :
forall B1 Xbt1,
  size_btyp (close_btyp_wrt_btyp Xbt1 B1) = size_btyp B1.
Proof.
unfold close_btyp_wrt_btyp; default_simp.
Qed.

#[export] Hint Resolve size_btyp_close_btyp_wrt_btyp : lngen.
#[export] Hint Rewrite size_btyp_close_btyp_wrt_btyp using solve [auto] : lngen.

Lemma size_utyp_close_utyp_wrt_utyp :
forall C1 Xut1,
  size_utyp (close_utyp_wrt_utyp Xut1 C1) = size_utyp C1.
Proof.
unfold close_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve size_utyp_close_utyp_wrt_utyp : lngen.
#[export] Hint Rewrite size_utyp_close_utyp_wrt_utyp using solve [auto] : lngen.

Lemma size_pskel_close_pskel_wrt_pskel :
forall P1 Xps1,
  size_pskel (close_pskel_wrt_pskel Xps1 P1) = size_pskel P1.
Proof.
unfold close_pskel_wrt_pskel; default_simp.
Qed.

#[export] Hint Resolve size_pskel_close_pskel_wrt_pskel : lngen.
#[export] Hint Rewrite size_pskel_close_pskel_wrt_pskel using solve [auto] : lngen.

Lemma size_bskel_close_bskel_wrt_bskel :
forall Q1 Xbs1,
  size_bskel (close_bskel_wrt_bskel Xbs1 Q1) = size_bskel Q1.
Proof.
unfold close_bskel_wrt_bskel; default_simp.
Qed.

#[export] Hint Resolve size_bskel_close_bskel_wrt_bskel : lngen.
#[export] Hint Rewrite size_bskel_close_bskel_wrt_bskel using solve [auto] : lngen.

Lemma size_uskel_close_uskel_wrt_uskel :
forall R1 Xus1,
  size_uskel (close_uskel_wrt_uskel Xus1 R1) = size_uskel R1.
Proof.
unfold close_uskel_wrt_uskel; default_simp.
Qed.

#[export] Hint Resolve size_uskel_close_uskel_wrt_uskel : lngen.
#[export] Hint Rewrite size_uskel_close_uskel_wrt_uskel using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_ptyp :
forall e1 Xpt1,
  size_exp (close_exp_wrt_ptyp Xpt1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_ptyp : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_ptyp using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_exp :
forall e1 x1,
  size_exp (close_exp_wrt_exp x1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma size_ptyp_open_ptyp_wrt_ptyp_rec_mutual :
(forall A1 A2 n1,
  size_ptyp A1 <= size_ptyp (open_ptyp_wrt_ptyp_rec n1 A2 A1)).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_ptyp_open_ptyp_wrt_ptyp_rec :
forall A1 A2 n1,
  size_ptyp A1 <= size_ptyp (open_ptyp_wrt_ptyp_rec n1 A2 A1).
Proof.
pose proof size_ptyp_open_ptyp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ptyp_open_ptyp_wrt_ptyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_btyp_open_btyp_wrt_btyp_rec_mutual :
(forall B1 B2 n1,
  size_btyp B1 <= size_btyp (open_btyp_wrt_btyp_rec n1 B2 B1)).
Proof.
apply_mutual_ind btyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_btyp_open_btyp_wrt_btyp_rec :
forall B1 B2 n1,
  size_btyp B1 <= size_btyp (open_btyp_wrt_btyp_rec n1 B2 B1).
Proof.
pose proof size_btyp_open_btyp_wrt_btyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_btyp_open_btyp_wrt_btyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_utyp_open_utyp_wrt_utyp_rec_mutual :
(forall C1 C2 n1,
  size_utyp C1 <= size_utyp (open_utyp_wrt_utyp_rec n1 C2 C1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_utyp_open_utyp_wrt_utyp_rec :
forall C1 C2 n1,
  size_utyp C1 <= size_utyp (open_utyp_wrt_utyp_rec n1 C2 C1).
Proof.
pose proof size_utyp_open_utyp_wrt_utyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_utyp_open_utyp_wrt_utyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_pskel_open_pskel_wrt_pskel_rec_mutual :
(forall P1 P2 n1,
  size_pskel P1 <= size_pskel (open_pskel_wrt_pskel_rec n1 P2 P1)).
Proof.
apply_mutual_ind pskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_pskel_open_pskel_wrt_pskel_rec :
forall P1 P2 n1,
  size_pskel P1 <= size_pskel (open_pskel_wrt_pskel_rec n1 P2 P1).
Proof.
pose proof size_pskel_open_pskel_wrt_pskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_pskel_open_pskel_wrt_pskel_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_bskel_open_bskel_wrt_bskel_rec_mutual :
(forall Q1 Q2 n1,
  size_bskel Q1 <= size_bskel (open_bskel_wrt_bskel_rec n1 Q2 Q1)).
Proof.
apply_mutual_ind bskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_bskel_open_bskel_wrt_bskel_rec :
forall Q1 Q2 n1,
  size_bskel Q1 <= size_bskel (open_bskel_wrt_bskel_rec n1 Q2 Q1).
Proof.
pose proof size_bskel_open_bskel_wrt_bskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_bskel_open_bskel_wrt_bskel_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_uskel_open_uskel_wrt_uskel_rec_mutual :
(forall R1 R2 n1,
  size_uskel R1 <= size_uskel (open_uskel_wrt_uskel_rec n1 R2 R1)).
Proof.
apply_mutual_ind uskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_uskel_open_uskel_wrt_uskel_rec :
forall R1 R2 n1,
  size_uskel R1 <= size_uskel (open_uskel_wrt_uskel_rec n1 R2 R1).
Proof.
pose proof size_uskel_open_uskel_wrt_uskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_uskel_open_uskel_wrt_uskel_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_ptyp_rec_mutual :
(forall e1 A1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_ptyp_rec n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_ptyp_rec :
forall e1 A1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_ptyp_rec n1 A1 e1).
Proof.
pose proof size_exp_open_exp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_ptyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1,
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec :
forall e1 e2 n1,
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma size_ptyp_open_ptyp_wrt_ptyp :
forall A1 A2,
  size_ptyp A1 <= size_ptyp (open_ptyp_wrt_ptyp A1 A2).
Proof.
unfold open_ptyp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve size_ptyp_open_ptyp_wrt_ptyp : lngen.

Lemma size_btyp_open_btyp_wrt_btyp :
forall B1 B2,
  size_btyp B1 <= size_btyp (open_btyp_wrt_btyp B1 B2).
Proof.
unfold open_btyp_wrt_btyp; default_simp.
Qed.

#[export] Hint Resolve size_btyp_open_btyp_wrt_btyp : lngen.

Lemma size_utyp_open_utyp_wrt_utyp :
forall C1 C2,
  size_utyp C1 <= size_utyp (open_utyp_wrt_utyp C1 C2).
Proof.
unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve size_utyp_open_utyp_wrt_utyp : lngen.

Lemma size_pskel_open_pskel_wrt_pskel :
forall P1 P2,
  size_pskel P1 <= size_pskel (open_pskel_wrt_pskel P1 P2).
Proof.
unfold open_pskel_wrt_pskel; default_simp.
Qed.

#[export] Hint Resolve size_pskel_open_pskel_wrt_pskel : lngen.

Lemma size_bskel_open_bskel_wrt_bskel :
forall Q1 Q2,
  size_bskel Q1 <= size_bskel (open_bskel_wrt_bskel Q1 Q2).
Proof.
unfold open_bskel_wrt_bskel; default_simp.
Qed.

#[export] Hint Resolve size_bskel_open_bskel_wrt_bskel : lngen.

Lemma size_uskel_open_uskel_wrt_uskel :
forall R1 R2,
  size_uskel R1 <= size_uskel (open_uskel_wrt_uskel R1 R2).
Proof.
unfold open_uskel_wrt_uskel; default_simp.
Qed.

#[export] Hint Resolve size_uskel_open_uskel_wrt_uskel : lngen.

Lemma size_exp_open_exp_wrt_ptyp :
forall e1 A1,
  size_exp e1 <= size_exp (open_exp_wrt_ptyp e1 A1).
Proof.
unfold open_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_ptyp : lngen.

Lemma size_exp_open_exp_wrt_exp :
forall e1 e2,
  size_exp e1 <= size_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_exp : lngen.

(* begin hide *)

Lemma size_ptyp_open_ptyp_wrt_ptyp_rec_var_mutual :
(forall A1 Xpt1 n1,
  size_ptyp (open_ptyp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) A1) = size_ptyp A1).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_ptyp_open_ptyp_wrt_ptyp_rec_var :
forall A1 Xpt1 n1,
  size_ptyp (open_ptyp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) A1) = size_ptyp A1.
Proof.
pose proof size_ptyp_open_ptyp_wrt_ptyp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ptyp_open_ptyp_wrt_ptyp_rec_var : lngen.
#[export] Hint Rewrite size_ptyp_open_ptyp_wrt_ptyp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_btyp_open_btyp_wrt_btyp_rec_var_mutual :
(forall B1 Xbt1 n1,
  size_btyp (open_btyp_wrt_btyp_rec n1 (btyp_var_f Xbt1) B1) = size_btyp B1).
Proof.
apply_mutual_ind btyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_btyp_open_btyp_wrt_btyp_rec_var :
forall B1 Xbt1 n1,
  size_btyp (open_btyp_wrt_btyp_rec n1 (btyp_var_f Xbt1) B1) = size_btyp B1.
Proof.
pose proof size_btyp_open_btyp_wrt_btyp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_btyp_open_btyp_wrt_btyp_rec_var : lngen.
#[export] Hint Rewrite size_btyp_open_btyp_wrt_btyp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_utyp_open_utyp_wrt_utyp_rec_var_mutual :
(forall C1 Xut1 n1,
  size_utyp (open_utyp_wrt_utyp_rec n1 (utyp_var_f Xut1) C1) = size_utyp C1).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_utyp_open_utyp_wrt_utyp_rec_var :
forall C1 Xut1 n1,
  size_utyp (open_utyp_wrt_utyp_rec n1 (utyp_var_f Xut1) C1) = size_utyp C1.
Proof.
pose proof size_utyp_open_utyp_wrt_utyp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_utyp_open_utyp_wrt_utyp_rec_var : lngen.
#[export] Hint Rewrite size_utyp_open_utyp_wrt_utyp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_pskel_open_pskel_wrt_pskel_rec_var_mutual :
(forall P1 Xps1 n1,
  size_pskel (open_pskel_wrt_pskel_rec n1 (pskel_var_f Xps1) P1) = size_pskel P1).
Proof.
apply_mutual_ind pskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_pskel_open_pskel_wrt_pskel_rec_var :
forall P1 Xps1 n1,
  size_pskel (open_pskel_wrt_pskel_rec n1 (pskel_var_f Xps1) P1) = size_pskel P1.
Proof.
pose proof size_pskel_open_pskel_wrt_pskel_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_pskel_open_pskel_wrt_pskel_rec_var : lngen.
#[export] Hint Rewrite size_pskel_open_pskel_wrt_pskel_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_bskel_open_bskel_wrt_bskel_rec_var_mutual :
(forall Q1 Xbs1 n1,
  size_bskel (open_bskel_wrt_bskel_rec n1 (bskel_var_f Xbs1) Q1) = size_bskel Q1).
Proof.
apply_mutual_ind bskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_bskel_open_bskel_wrt_bskel_rec_var :
forall Q1 Xbs1 n1,
  size_bskel (open_bskel_wrt_bskel_rec n1 (bskel_var_f Xbs1) Q1) = size_bskel Q1.
Proof.
pose proof size_bskel_open_bskel_wrt_bskel_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_bskel_open_bskel_wrt_bskel_rec_var : lngen.
#[export] Hint Rewrite size_bskel_open_bskel_wrt_bskel_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_uskel_open_uskel_wrt_uskel_rec_var_mutual :
(forall R1 Xus1 n1,
  size_uskel (open_uskel_wrt_uskel_rec n1 (uskel_var_f Xus1) R1) = size_uskel R1).
Proof.
apply_mutual_ind uskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_uskel_open_uskel_wrt_uskel_rec_var :
forall R1 Xus1 n1,
  size_uskel (open_uskel_wrt_uskel_rec n1 (uskel_var_f Xus1) R1) = size_uskel R1.
Proof.
pose proof size_uskel_open_uskel_wrt_uskel_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_uskel_open_uskel_wrt_uskel_rec_var : lngen.
#[export] Hint Rewrite size_uskel_open_uskel_wrt_uskel_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_ptyp_rec_var_mutual :
(forall e1 Xpt1 n1,
  size_exp (open_exp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_ptyp_rec_var :
forall e1 Xpt1 n1,
  size_exp (open_exp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) e1) = size_exp e1.
Proof.
pose proof size_exp_open_exp_wrt_ptyp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_ptyp_rec_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_ptyp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_var_mutual :
(forall e1 x1 n1,
  size_exp (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_var :
forall e1 x1 n1,
  size_exp (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = size_exp e1.
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_exp_rec_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_exp_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_ptyp_open_ptyp_wrt_ptyp_var :
forall A1 Xpt1,
  size_ptyp (open_ptyp_wrt_ptyp A1 (ptyp_var_f Xpt1)) = size_ptyp A1.
Proof.
unfold open_ptyp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve size_ptyp_open_ptyp_wrt_ptyp_var : lngen.
#[export] Hint Rewrite size_ptyp_open_ptyp_wrt_ptyp_var using solve [auto] : lngen.

Lemma size_btyp_open_btyp_wrt_btyp_var :
forall B1 Xbt1,
  size_btyp (open_btyp_wrt_btyp B1 (btyp_var_f Xbt1)) = size_btyp B1.
Proof.
unfold open_btyp_wrt_btyp; default_simp.
Qed.

#[export] Hint Resolve size_btyp_open_btyp_wrt_btyp_var : lngen.
#[export] Hint Rewrite size_btyp_open_btyp_wrt_btyp_var using solve [auto] : lngen.

Lemma size_utyp_open_utyp_wrt_utyp_var :
forall C1 Xut1,
  size_utyp (open_utyp_wrt_utyp C1 (utyp_var_f Xut1)) = size_utyp C1.
Proof.
unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve size_utyp_open_utyp_wrt_utyp_var : lngen.
#[export] Hint Rewrite size_utyp_open_utyp_wrt_utyp_var using solve [auto] : lngen.

Lemma size_pskel_open_pskel_wrt_pskel_var :
forall P1 Xps1,
  size_pskel (open_pskel_wrt_pskel P1 (pskel_var_f Xps1)) = size_pskel P1.
Proof.
unfold open_pskel_wrt_pskel; default_simp.
Qed.

#[export] Hint Resolve size_pskel_open_pskel_wrt_pskel_var : lngen.
#[export] Hint Rewrite size_pskel_open_pskel_wrt_pskel_var using solve [auto] : lngen.

Lemma size_bskel_open_bskel_wrt_bskel_var :
forall Q1 Xbs1,
  size_bskel (open_bskel_wrt_bskel Q1 (bskel_var_f Xbs1)) = size_bskel Q1.
Proof.
unfold open_bskel_wrt_bskel; default_simp.
Qed.

#[export] Hint Resolve size_bskel_open_bskel_wrt_bskel_var : lngen.
#[export] Hint Rewrite size_bskel_open_bskel_wrt_bskel_var using solve [auto] : lngen.

Lemma size_uskel_open_uskel_wrt_uskel_var :
forall R1 Xus1,
  size_uskel (open_uskel_wrt_uskel R1 (uskel_var_f Xus1)) = size_uskel R1.
Proof.
unfold open_uskel_wrt_uskel; default_simp.
Qed.

#[export] Hint Resolve size_uskel_open_uskel_wrt_uskel_var : lngen.
#[export] Hint Rewrite size_uskel_open_uskel_wrt_uskel_var using solve [auto] : lngen.

Lemma size_exp_open_exp_wrt_ptyp_var :
forall e1 Xpt1,
  size_exp (open_exp_wrt_ptyp e1 (ptyp_var_f Xpt1)) = size_exp e1.
Proof.
unfold open_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_ptyp_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_ptyp_var using solve [auto] : lngen.

Lemma size_exp_open_exp_wrt_exp_var :
forall e1 x1,
  size_exp (open_exp_wrt_exp e1 (exp_var_f x1)) = size_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_exp_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_exp_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_ptyp_wrt_ptyp_S_mutual :
(forall n1 A1,
  degree_ptyp_wrt_ptyp n1 A1 ->
  degree_ptyp_wrt_ptyp (S n1) A1).
Proof.
apply_mutual_ind degree_ptyp_wrt_ptyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_ptyp_wrt_ptyp_S :
forall n1 A1,
  degree_ptyp_wrt_ptyp n1 A1 ->
  degree_ptyp_wrt_ptyp (S n1) A1.
Proof.
pose proof degree_ptyp_wrt_ptyp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ptyp_wrt_ptyp_S : lngen.

(* begin hide *)

Lemma degree_btyp_wrt_btyp_S_mutual :
(forall n1 B1,
  degree_btyp_wrt_btyp n1 B1 ->
  degree_btyp_wrt_btyp (S n1) B1).
Proof.
apply_mutual_ind degree_btyp_wrt_btyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_btyp_wrt_btyp_S :
forall n1 B1,
  degree_btyp_wrt_btyp n1 B1 ->
  degree_btyp_wrt_btyp (S n1) B1.
Proof.
pose proof degree_btyp_wrt_btyp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_btyp_wrt_btyp_S : lngen.

(* begin hide *)

Lemma degree_utyp_wrt_utyp_S_mutual :
(forall n1 C1,
  degree_utyp_wrt_utyp n1 C1 ->
  degree_utyp_wrt_utyp (S n1) C1).
Proof.
apply_mutual_ind degree_utyp_wrt_utyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_utyp_wrt_utyp_S :
forall n1 C1,
  degree_utyp_wrt_utyp n1 C1 ->
  degree_utyp_wrt_utyp (S n1) C1.
Proof.
pose proof degree_utyp_wrt_utyp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_utyp_wrt_utyp_S : lngen.

(* begin hide *)

Lemma degree_pskel_wrt_pskel_S_mutual :
(forall n1 P1,
  degree_pskel_wrt_pskel n1 P1 ->
  degree_pskel_wrt_pskel (S n1) P1).
Proof.
apply_mutual_ind degree_pskel_wrt_pskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_pskel_wrt_pskel_S :
forall n1 P1,
  degree_pskel_wrt_pskel n1 P1 ->
  degree_pskel_wrt_pskel (S n1) P1.
Proof.
pose proof degree_pskel_wrt_pskel_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_pskel_wrt_pskel_S : lngen.

(* begin hide *)

Lemma degree_bskel_wrt_bskel_S_mutual :
(forall n1 Q1,
  degree_bskel_wrt_bskel n1 Q1 ->
  degree_bskel_wrt_bskel (S n1) Q1).
Proof.
apply_mutual_ind degree_bskel_wrt_bskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_bskel_wrt_bskel_S :
forall n1 Q1,
  degree_bskel_wrt_bskel n1 Q1 ->
  degree_bskel_wrt_bskel (S n1) Q1.
Proof.
pose proof degree_bskel_wrt_bskel_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_bskel_wrt_bskel_S : lngen.

(* begin hide *)

Lemma degree_uskel_wrt_uskel_S_mutual :
(forall n1 R1,
  degree_uskel_wrt_uskel n1 R1 ->
  degree_uskel_wrt_uskel (S n1) R1).
Proof.
apply_mutual_ind degree_uskel_wrt_uskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_uskel_wrt_uskel_S :
forall n1 R1,
  degree_uskel_wrt_uskel n1 R1 ->
  degree_uskel_wrt_uskel (S n1) R1.
Proof.
pose proof degree_uskel_wrt_uskel_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_uskel_wrt_uskel_S : lngen.

(* begin hide *)

Lemma degree_exp_wrt_ptyp_S_mutual :
(forall n1 e1,
  degree_exp_wrt_ptyp n1 e1 ->
  degree_exp_wrt_ptyp (S n1) e1).
Proof.
apply_mutual_ind degree_exp_wrt_ptyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_exp_wrt_ptyp_S :
forall n1 e1,
  degree_exp_wrt_ptyp n1 e1 ->
  degree_exp_wrt_ptyp (S n1) e1.
Proof.
pose proof degree_exp_wrt_ptyp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_ptyp_S : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_S_mutual :
(forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1).
Proof.
apply_mutual_ind degree_exp_wrt_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_exp_wrt_exp_S :
forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_exp_wrt_exp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_S : lngen.

Lemma degree_ptyp_wrt_ptyp_O :
forall n1 A1,
  degree_ptyp_wrt_ptyp O A1 ->
  degree_ptyp_wrt_ptyp n1 A1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_ptyp_wrt_ptyp_O : lngen.

Lemma degree_btyp_wrt_btyp_O :
forall n1 B1,
  degree_btyp_wrt_btyp O B1 ->
  degree_btyp_wrt_btyp n1 B1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_btyp_wrt_btyp_O : lngen.

Lemma degree_utyp_wrt_utyp_O :
forall n1 C1,
  degree_utyp_wrt_utyp O C1 ->
  degree_utyp_wrt_utyp n1 C1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_utyp_wrt_utyp_O : lngen.

Lemma degree_pskel_wrt_pskel_O :
forall n1 P1,
  degree_pskel_wrt_pskel O P1 ->
  degree_pskel_wrt_pskel n1 P1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_pskel_wrt_pskel_O : lngen.

Lemma degree_bskel_wrt_bskel_O :
forall n1 Q1,
  degree_bskel_wrt_bskel O Q1 ->
  degree_bskel_wrt_bskel n1 Q1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_bskel_wrt_bskel_O : lngen.

Lemma degree_uskel_wrt_uskel_O :
forall n1 R1,
  degree_uskel_wrt_uskel O R1 ->
  degree_uskel_wrt_uskel n1 R1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_uskel_wrt_uskel_O : lngen.

Lemma degree_exp_wrt_ptyp_O :
forall n1 e1,
  degree_exp_wrt_ptyp O e1 ->
  degree_exp_wrt_ptyp n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_ptyp_O : lngen.

Lemma degree_exp_wrt_exp_O :
forall n1 e1,
  degree_exp_wrt_exp O e1 ->
  degree_exp_wrt_exp n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_O : lngen.

(* begin hide *)

Lemma degree_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp_rec_mutual :
(forall A1 Xpt1 n1,
  degree_ptyp_wrt_ptyp n1 A1 ->
  degree_ptyp_wrt_ptyp (S n1) (close_ptyp_wrt_ptyp_rec n1 Xpt1 A1)).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp_rec :
forall A1 Xpt1 n1,
  degree_ptyp_wrt_ptyp n1 A1 ->
  degree_ptyp_wrt_ptyp (S n1) (close_ptyp_wrt_ptyp_rec n1 Xpt1 A1).
Proof.
pose proof degree_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_btyp_wrt_btyp_close_btyp_wrt_btyp_rec_mutual :
(forall B1 Xbt1 n1,
  degree_btyp_wrt_btyp n1 B1 ->
  degree_btyp_wrt_btyp (S n1) (close_btyp_wrt_btyp_rec n1 Xbt1 B1)).
Proof.
apply_mutual_ind btyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_btyp_wrt_btyp_close_btyp_wrt_btyp_rec :
forall B1 Xbt1 n1,
  degree_btyp_wrt_btyp n1 B1 ->
  degree_btyp_wrt_btyp (S n1) (close_btyp_wrt_btyp_rec n1 Xbt1 B1).
Proof.
pose proof degree_btyp_wrt_btyp_close_btyp_wrt_btyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_btyp_wrt_btyp_close_btyp_wrt_btyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_utyp_wrt_utyp_close_utyp_wrt_utyp_rec_mutual :
(forall C1 Xut1 n1,
  degree_utyp_wrt_utyp n1 C1 ->
  degree_utyp_wrt_utyp (S n1) (close_utyp_wrt_utyp_rec n1 Xut1 C1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_utyp_wrt_utyp_close_utyp_wrt_utyp_rec :
forall C1 Xut1 n1,
  degree_utyp_wrt_utyp n1 C1 ->
  degree_utyp_wrt_utyp (S n1) (close_utyp_wrt_utyp_rec n1 Xut1 C1).
Proof.
pose proof degree_utyp_wrt_utyp_close_utyp_wrt_utyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_utyp_wrt_utyp_close_utyp_wrt_utyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_pskel_wrt_pskel_close_pskel_wrt_pskel_rec_mutual :
(forall P1 Xps1 n1,
  degree_pskel_wrt_pskel n1 P1 ->
  degree_pskel_wrt_pskel (S n1) (close_pskel_wrt_pskel_rec n1 Xps1 P1)).
Proof.
apply_mutual_ind pskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_pskel_wrt_pskel_close_pskel_wrt_pskel_rec :
forall P1 Xps1 n1,
  degree_pskel_wrt_pskel n1 P1 ->
  degree_pskel_wrt_pskel (S n1) (close_pskel_wrt_pskel_rec n1 Xps1 P1).
Proof.
pose proof degree_pskel_wrt_pskel_close_pskel_wrt_pskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_pskel_wrt_pskel_close_pskel_wrt_pskel_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_bskel_wrt_bskel_close_bskel_wrt_bskel_rec_mutual :
(forall Q1 Xbs1 n1,
  degree_bskel_wrt_bskel n1 Q1 ->
  degree_bskel_wrt_bskel (S n1) (close_bskel_wrt_bskel_rec n1 Xbs1 Q1)).
Proof.
apply_mutual_ind bskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_bskel_wrt_bskel_close_bskel_wrt_bskel_rec :
forall Q1 Xbs1 n1,
  degree_bskel_wrt_bskel n1 Q1 ->
  degree_bskel_wrt_bskel (S n1) (close_bskel_wrt_bskel_rec n1 Xbs1 Q1).
Proof.
pose proof degree_bskel_wrt_bskel_close_bskel_wrt_bskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_bskel_wrt_bskel_close_bskel_wrt_bskel_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_uskel_wrt_uskel_close_uskel_wrt_uskel_rec_mutual :
(forall R1 Xus1 n1,
  degree_uskel_wrt_uskel n1 R1 ->
  degree_uskel_wrt_uskel (S n1) (close_uskel_wrt_uskel_rec n1 Xus1 R1)).
Proof.
apply_mutual_ind uskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_uskel_wrt_uskel_close_uskel_wrt_uskel_rec :
forall R1 Xus1 n1,
  degree_uskel_wrt_uskel n1 R1 ->
  degree_uskel_wrt_uskel (S n1) (close_uskel_wrt_uskel_rec n1 Xus1 R1).
Proof.
pose proof degree_uskel_wrt_uskel_close_uskel_wrt_uskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_uskel_wrt_uskel_close_uskel_wrt_uskel_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ptyp_close_exp_wrt_ptyp_rec_mutual :
(forall e1 Xpt1 n1,
  degree_exp_wrt_ptyp n1 e1 ->
  degree_exp_wrt_ptyp (S n1) (close_exp_wrt_ptyp_rec n1 Xpt1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ptyp_close_exp_wrt_ptyp_rec :
forall e1 Xpt1 n1,
  degree_exp_wrt_ptyp n1 e1 ->
  degree_exp_wrt_ptyp (S n1) (close_exp_wrt_ptyp_rec n1 Xpt1 e1).
Proof.
pose proof degree_exp_wrt_ptyp_close_exp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_ptyp_close_exp_wrt_ptyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ptyp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_ptyp n2 e1 ->
  degree_exp_wrt_ptyp n2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ptyp_close_exp_wrt_exp_rec :
forall e1 x1 n1 n2,
  degree_exp_wrt_ptyp n2 e1 ->
  degree_exp_wrt_ptyp n2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof degree_exp_wrt_ptyp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_ptyp_close_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_ptyp_rec_mutual :
(forall e1 Xpt1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_ptyp_rec n1 Xpt1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_ptyp_rec :
forall e1 Xpt1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_ptyp_rec n1 Xpt1 e1).
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_ptyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma degree_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp :
forall A1 Xpt1,
  degree_ptyp_wrt_ptyp 0 A1 ->
  degree_ptyp_wrt_ptyp 1 (close_ptyp_wrt_ptyp Xpt1 A1).
Proof.
unfold close_ptyp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve degree_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp : lngen.

Lemma degree_btyp_wrt_btyp_close_btyp_wrt_btyp :
forall B1 Xbt1,
  degree_btyp_wrt_btyp 0 B1 ->
  degree_btyp_wrt_btyp 1 (close_btyp_wrt_btyp Xbt1 B1).
Proof.
unfold close_btyp_wrt_btyp; default_simp.
Qed.

#[export] Hint Resolve degree_btyp_wrt_btyp_close_btyp_wrt_btyp : lngen.

Lemma degree_utyp_wrt_utyp_close_utyp_wrt_utyp :
forall C1 Xut1,
  degree_utyp_wrt_utyp 0 C1 ->
  degree_utyp_wrt_utyp 1 (close_utyp_wrt_utyp Xut1 C1).
Proof.
unfold close_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve degree_utyp_wrt_utyp_close_utyp_wrt_utyp : lngen.

Lemma degree_pskel_wrt_pskel_close_pskel_wrt_pskel :
forall P1 Xps1,
  degree_pskel_wrt_pskel 0 P1 ->
  degree_pskel_wrt_pskel 1 (close_pskel_wrt_pskel Xps1 P1).
Proof.
unfold close_pskel_wrt_pskel; default_simp.
Qed.

#[export] Hint Resolve degree_pskel_wrt_pskel_close_pskel_wrt_pskel : lngen.

Lemma degree_bskel_wrt_bskel_close_bskel_wrt_bskel :
forall Q1 Xbs1,
  degree_bskel_wrt_bskel 0 Q1 ->
  degree_bskel_wrt_bskel 1 (close_bskel_wrt_bskel Xbs1 Q1).
Proof.
unfold close_bskel_wrt_bskel; default_simp.
Qed.

#[export] Hint Resolve degree_bskel_wrt_bskel_close_bskel_wrt_bskel : lngen.

Lemma degree_uskel_wrt_uskel_close_uskel_wrt_uskel :
forall R1 Xus1,
  degree_uskel_wrt_uskel 0 R1 ->
  degree_uskel_wrt_uskel 1 (close_uskel_wrt_uskel Xus1 R1).
Proof.
unfold close_uskel_wrt_uskel; default_simp.
Qed.

#[export] Hint Resolve degree_uskel_wrt_uskel_close_uskel_wrt_uskel : lngen.

Lemma degree_exp_wrt_ptyp_close_exp_wrt_ptyp :
forall e1 Xpt1,
  degree_exp_wrt_ptyp 0 e1 ->
  degree_exp_wrt_ptyp 1 (close_exp_wrt_ptyp Xpt1 e1).
Proof.
unfold close_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_ptyp_close_exp_wrt_ptyp : lngen.

Lemma degree_exp_wrt_ptyp_close_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_ptyp n1 e1 ->
  degree_exp_wrt_ptyp n1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_ptyp_close_exp_wrt_exp : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_ptyp :
forall e1 Xpt1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (close_exp_wrt_ptyp Xpt1 e1).
Proof.
unfold close_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_ptyp : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  degree_exp_wrt_exp 0 e1 ->
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp : lngen.

(* begin hide *)

Lemma degree_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp_rec_inv_mutual :
(forall A1 Xpt1 n1,
  degree_ptyp_wrt_ptyp (S n1) (close_ptyp_wrt_ptyp_rec n1 Xpt1 A1) ->
  degree_ptyp_wrt_ptyp n1 A1).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp_rec_inv :
forall A1 Xpt1 n1,
  degree_ptyp_wrt_ptyp (S n1) (close_ptyp_wrt_ptyp_rec n1 Xpt1 A1) ->
  degree_ptyp_wrt_ptyp n1 A1.
Proof.
pose proof degree_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_btyp_wrt_btyp_close_btyp_wrt_btyp_rec_inv_mutual :
(forall B1 Xbt1 n1,
  degree_btyp_wrt_btyp (S n1) (close_btyp_wrt_btyp_rec n1 Xbt1 B1) ->
  degree_btyp_wrt_btyp n1 B1).
Proof.
apply_mutual_ind btyp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_btyp_wrt_btyp_close_btyp_wrt_btyp_rec_inv :
forall B1 Xbt1 n1,
  degree_btyp_wrt_btyp (S n1) (close_btyp_wrt_btyp_rec n1 Xbt1 B1) ->
  degree_btyp_wrt_btyp n1 B1.
Proof.
pose proof degree_btyp_wrt_btyp_close_btyp_wrt_btyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_btyp_wrt_btyp_close_btyp_wrt_btyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_utyp_wrt_utyp_close_utyp_wrt_utyp_rec_inv_mutual :
(forall C1 Xut1 n1,
  degree_utyp_wrt_utyp (S n1) (close_utyp_wrt_utyp_rec n1 Xut1 C1) ->
  degree_utyp_wrt_utyp n1 C1).
Proof.
apply_mutual_ind utyp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_utyp_wrt_utyp_close_utyp_wrt_utyp_rec_inv :
forall C1 Xut1 n1,
  degree_utyp_wrt_utyp (S n1) (close_utyp_wrt_utyp_rec n1 Xut1 C1) ->
  degree_utyp_wrt_utyp n1 C1.
Proof.
pose proof degree_utyp_wrt_utyp_close_utyp_wrt_utyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_utyp_wrt_utyp_close_utyp_wrt_utyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_pskel_wrt_pskel_close_pskel_wrt_pskel_rec_inv_mutual :
(forall P1 Xps1 n1,
  degree_pskel_wrt_pskel (S n1) (close_pskel_wrt_pskel_rec n1 Xps1 P1) ->
  degree_pskel_wrt_pskel n1 P1).
Proof.
apply_mutual_ind pskel_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_pskel_wrt_pskel_close_pskel_wrt_pskel_rec_inv :
forall P1 Xps1 n1,
  degree_pskel_wrt_pskel (S n1) (close_pskel_wrt_pskel_rec n1 Xps1 P1) ->
  degree_pskel_wrt_pskel n1 P1.
Proof.
pose proof degree_pskel_wrt_pskel_close_pskel_wrt_pskel_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_pskel_wrt_pskel_close_pskel_wrt_pskel_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_bskel_wrt_bskel_close_bskel_wrt_bskel_rec_inv_mutual :
(forall Q1 Xbs1 n1,
  degree_bskel_wrt_bskel (S n1) (close_bskel_wrt_bskel_rec n1 Xbs1 Q1) ->
  degree_bskel_wrt_bskel n1 Q1).
Proof.
apply_mutual_ind bskel_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_bskel_wrt_bskel_close_bskel_wrt_bskel_rec_inv :
forall Q1 Xbs1 n1,
  degree_bskel_wrt_bskel (S n1) (close_bskel_wrt_bskel_rec n1 Xbs1 Q1) ->
  degree_bskel_wrt_bskel n1 Q1.
Proof.
pose proof degree_bskel_wrt_bskel_close_bskel_wrt_bskel_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_bskel_wrt_bskel_close_bskel_wrt_bskel_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_uskel_wrt_uskel_close_uskel_wrt_uskel_rec_inv_mutual :
(forall R1 Xus1 n1,
  degree_uskel_wrt_uskel (S n1) (close_uskel_wrt_uskel_rec n1 Xus1 R1) ->
  degree_uskel_wrt_uskel n1 R1).
Proof.
apply_mutual_ind uskel_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_uskel_wrt_uskel_close_uskel_wrt_uskel_rec_inv :
forall R1 Xus1 n1,
  degree_uskel_wrt_uskel (S n1) (close_uskel_wrt_uskel_rec n1 Xus1 R1) ->
  degree_uskel_wrt_uskel n1 R1.
Proof.
pose proof degree_uskel_wrt_uskel_close_uskel_wrt_uskel_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_uskel_wrt_uskel_close_uskel_wrt_uskel_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ptyp_close_exp_wrt_ptyp_rec_inv_mutual :
(forall e1 Xpt1 n1,
  degree_exp_wrt_ptyp (S n1) (close_exp_wrt_ptyp_rec n1 Xpt1 e1) ->
  degree_exp_wrt_ptyp n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ptyp_close_exp_wrt_ptyp_rec_inv :
forall e1 Xpt1 n1,
  degree_exp_wrt_ptyp (S n1) (close_exp_wrt_ptyp_rec n1 Xpt1 e1) ->
  degree_exp_wrt_ptyp n1 e1.
Proof.
pose proof degree_exp_wrt_ptyp_close_exp_wrt_ptyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_ptyp_close_exp_wrt_ptyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ptyp_close_exp_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_ptyp n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_ptyp n2 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ptyp_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1 n2,
  degree_exp_wrt_ptyp n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_ptyp n2 e1.
Proof.
pose proof degree_exp_wrt_ptyp_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_ptyp_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_ptyp_rec_inv_mutual :
(forall e1 Xpt1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_ptyp_rec n1 Xpt1 e1) ->
  degree_exp_wrt_exp n2 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_ptyp_rec_inv :
forall e1 Xpt1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_ptyp_rec n1 Xpt1 e1) ->
  degree_exp_wrt_exp n2 e1.
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_ptyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_ptyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

Lemma degree_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp_inv :
forall A1 Xpt1,
  degree_ptyp_wrt_ptyp 1 (close_ptyp_wrt_ptyp Xpt1 A1) ->
  degree_ptyp_wrt_ptyp 0 A1.
Proof.
unfold close_ptyp_wrt_ptyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp_inv : lngen.

Lemma degree_btyp_wrt_btyp_close_btyp_wrt_btyp_inv :
forall B1 Xbt1,
  degree_btyp_wrt_btyp 1 (close_btyp_wrt_btyp Xbt1 B1) ->
  degree_btyp_wrt_btyp 0 B1.
Proof.
unfold close_btyp_wrt_btyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_btyp_wrt_btyp_close_btyp_wrt_btyp_inv : lngen.

Lemma degree_utyp_wrt_utyp_close_utyp_wrt_utyp_inv :
forall C1 Xut1,
  degree_utyp_wrt_utyp 1 (close_utyp_wrt_utyp Xut1 C1) ->
  degree_utyp_wrt_utyp 0 C1.
Proof.
unfold close_utyp_wrt_utyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_utyp_wrt_utyp_close_utyp_wrt_utyp_inv : lngen.

Lemma degree_pskel_wrt_pskel_close_pskel_wrt_pskel_inv :
forall P1 Xps1,
  degree_pskel_wrt_pskel 1 (close_pskel_wrt_pskel Xps1 P1) ->
  degree_pskel_wrt_pskel 0 P1.
Proof.
unfold close_pskel_wrt_pskel; eauto with lngen.
Qed.

#[export] Hint Immediate degree_pskel_wrt_pskel_close_pskel_wrt_pskel_inv : lngen.

Lemma degree_bskel_wrt_bskel_close_bskel_wrt_bskel_inv :
forall Q1 Xbs1,
  degree_bskel_wrt_bskel 1 (close_bskel_wrt_bskel Xbs1 Q1) ->
  degree_bskel_wrt_bskel 0 Q1.
Proof.
unfold close_bskel_wrt_bskel; eauto with lngen.
Qed.

#[export] Hint Immediate degree_bskel_wrt_bskel_close_bskel_wrt_bskel_inv : lngen.

Lemma degree_uskel_wrt_uskel_close_uskel_wrt_uskel_inv :
forall R1 Xus1,
  degree_uskel_wrt_uskel 1 (close_uskel_wrt_uskel Xus1 R1) ->
  degree_uskel_wrt_uskel 0 R1.
Proof.
unfold close_uskel_wrt_uskel; eauto with lngen.
Qed.

#[export] Hint Immediate degree_uskel_wrt_uskel_close_uskel_wrt_uskel_inv : lngen.

Lemma degree_exp_wrt_ptyp_close_exp_wrt_ptyp_inv :
forall e1 Xpt1,
  degree_exp_wrt_ptyp 1 (close_exp_wrt_ptyp Xpt1 e1) ->
  degree_exp_wrt_ptyp 0 e1.
Proof.
unfold close_exp_wrt_ptyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_ptyp_close_exp_wrt_ptyp_inv : lngen.

Lemma degree_exp_wrt_ptyp_close_exp_wrt_exp_inv :
forall e1 x1 n1,
  degree_exp_wrt_ptyp n1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_ptyp n1 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_ptyp_close_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_ptyp_inv :
forall e1 Xpt1 n1,
  degree_exp_wrt_exp n1 (close_exp_wrt_ptyp Xpt1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
unfold close_exp_wrt_ptyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_ptyp_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_inv :
forall e1 x1,
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_exp 0 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_inv : lngen.

(* begin hide *)

Lemma degree_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp_rec_mutual :
(forall A1 A2 n1,
  degree_ptyp_wrt_ptyp (S n1) A1 ->
  degree_ptyp_wrt_ptyp n1 A2 ->
  degree_ptyp_wrt_ptyp n1 (open_ptyp_wrt_ptyp_rec n1 A2 A1)).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp_rec :
forall A1 A2 n1,
  degree_ptyp_wrt_ptyp (S n1) A1 ->
  degree_ptyp_wrt_ptyp n1 A2 ->
  degree_ptyp_wrt_ptyp n1 (open_ptyp_wrt_ptyp_rec n1 A2 A1).
Proof.
pose proof degree_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_btyp_wrt_btyp_open_btyp_wrt_btyp_rec_mutual :
(forall B1 B2 n1,
  degree_btyp_wrt_btyp (S n1) B1 ->
  degree_btyp_wrt_btyp n1 B2 ->
  degree_btyp_wrt_btyp n1 (open_btyp_wrt_btyp_rec n1 B2 B1)).
Proof.
apply_mutual_ind btyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_btyp_wrt_btyp_open_btyp_wrt_btyp_rec :
forall B1 B2 n1,
  degree_btyp_wrt_btyp (S n1) B1 ->
  degree_btyp_wrt_btyp n1 B2 ->
  degree_btyp_wrt_btyp n1 (open_btyp_wrt_btyp_rec n1 B2 B1).
Proof.
pose proof degree_btyp_wrt_btyp_open_btyp_wrt_btyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_btyp_wrt_btyp_open_btyp_wrt_btyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_utyp_wrt_utyp_open_utyp_wrt_utyp_rec_mutual :
(forall C1 C2 n1,
  degree_utyp_wrt_utyp (S n1) C1 ->
  degree_utyp_wrt_utyp n1 C2 ->
  degree_utyp_wrt_utyp n1 (open_utyp_wrt_utyp_rec n1 C2 C1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_utyp_wrt_utyp_open_utyp_wrt_utyp_rec :
forall C1 C2 n1,
  degree_utyp_wrt_utyp (S n1) C1 ->
  degree_utyp_wrt_utyp n1 C2 ->
  degree_utyp_wrt_utyp n1 (open_utyp_wrt_utyp_rec n1 C2 C1).
Proof.
pose proof degree_utyp_wrt_utyp_open_utyp_wrt_utyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_utyp_wrt_utyp_open_utyp_wrt_utyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_pskel_wrt_pskel_open_pskel_wrt_pskel_rec_mutual :
(forall P1 P2 n1,
  degree_pskel_wrt_pskel (S n1) P1 ->
  degree_pskel_wrt_pskel n1 P2 ->
  degree_pskel_wrt_pskel n1 (open_pskel_wrt_pskel_rec n1 P2 P1)).
Proof.
apply_mutual_ind pskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_pskel_wrt_pskel_open_pskel_wrt_pskel_rec :
forall P1 P2 n1,
  degree_pskel_wrt_pskel (S n1) P1 ->
  degree_pskel_wrt_pskel n1 P2 ->
  degree_pskel_wrt_pskel n1 (open_pskel_wrt_pskel_rec n1 P2 P1).
Proof.
pose proof degree_pskel_wrt_pskel_open_pskel_wrt_pskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_pskel_wrt_pskel_open_pskel_wrt_pskel_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_bskel_wrt_bskel_open_bskel_wrt_bskel_rec_mutual :
(forall Q1 Q2 n1,
  degree_bskel_wrt_bskel (S n1) Q1 ->
  degree_bskel_wrt_bskel n1 Q2 ->
  degree_bskel_wrt_bskel n1 (open_bskel_wrt_bskel_rec n1 Q2 Q1)).
Proof.
apply_mutual_ind bskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_bskel_wrt_bskel_open_bskel_wrt_bskel_rec :
forall Q1 Q2 n1,
  degree_bskel_wrt_bskel (S n1) Q1 ->
  degree_bskel_wrt_bskel n1 Q2 ->
  degree_bskel_wrt_bskel n1 (open_bskel_wrt_bskel_rec n1 Q2 Q1).
Proof.
pose proof degree_bskel_wrt_bskel_open_bskel_wrt_bskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_bskel_wrt_bskel_open_bskel_wrt_bskel_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_uskel_wrt_uskel_open_uskel_wrt_uskel_rec_mutual :
(forall R1 R2 n1,
  degree_uskel_wrt_uskel (S n1) R1 ->
  degree_uskel_wrt_uskel n1 R2 ->
  degree_uskel_wrt_uskel n1 (open_uskel_wrt_uskel_rec n1 R2 R1)).
Proof.
apply_mutual_ind uskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_uskel_wrt_uskel_open_uskel_wrt_uskel_rec :
forall R1 R2 n1,
  degree_uskel_wrt_uskel (S n1) R1 ->
  degree_uskel_wrt_uskel n1 R2 ->
  degree_uskel_wrt_uskel n1 (open_uskel_wrt_uskel_rec n1 R2 R1).
Proof.
pose proof degree_uskel_wrt_uskel_open_uskel_wrt_uskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_uskel_wrt_uskel_open_uskel_wrt_uskel_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ptyp_open_exp_wrt_ptyp_rec_mutual :
(forall e1 A1 n1,
  degree_exp_wrt_ptyp (S n1) e1 ->
  degree_ptyp_wrt_ptyp n1 A1 ->
  degree_exp_wrt_ptyp n1 (open_exp_wrt_ptyp_rec n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ptyp_open_exp_wrt_ptyp_rec :
forall e1 A1 n1,
  degree_exp_wrt_ptyp (S n1) e1 ->
  degree_ptyp_wrt_ptyp n1 A1 ->
  degree_exp_wrt_ptyp n1 (open_exp_wrt_ptyp_rec n1 A1 e1).
Proof.
pose proof degree_exp_wrt_ptyp_open_exp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_ptyp_open_exp_wrt_ptyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ptyp_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_ptyp n1 e1 ->
  degree_exp_wrt_ptyp n1 e2 ->
  degree_exp_wrt_ptyp n1 (open_exp_wrt_exp_rec n2 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ptyp_open_exp_wrt_exp_rec :
forall e1 e2 n1 n2,
  degree_exp_wrt_ptyp n1 e1 ->
  degree_exp_wrt_ptyp n1 e2 ->
  degree_exp_wrt_ptyp n1 (open_exp_wrt_exp_rec n2 e2 e1).
Proof.
pose proof degree_exp_wrt_ptyp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_ptyp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_ptyp_rec_mutual :
(forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_ptyp_rec n2 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_ptyp_rec :
forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_ptyp_rec n2 A1 e1).
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_ptyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec :
forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma degree_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp :
forall A1 A2,
  degree_ptyp_wrt_ptyp 1 A1 ->
  degree_ptyp_wrt_ptyp 0 A2 ->
  degree_ptyp_wrt_ptyp 0 (open_ptyp_wrt_ptyp A1 A2).
Proof.
unfold open_ptyp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve degree_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp : lngen.

Lemma degree_btyp_wrt_btyp_open_btyp_wrt_btyp :
forall B1 B2,
  degree_btyp_wrt_btyp 1 B1 ->
  degree_btyp_wrt_btyp 0 B2 ->
  degree_btyp_wrt_btyp 0 (open_btyp_wrt_btyp B1 B2).
Proof.
unfold open_btyp_wrt_btyp; default_simp.
Qed.

#[export] Hint Resolve degree_btyp_wrt_btyp_open_btyp_wrt_btyp : lngen.

Lemma degree_utyp_wrt_utyp_open_utyp_wrt_utyp :
forall C1 C2,
  degree_utyp_wrt_utyp 1 C1 ->
  degree_utyp_wrt_utyp 0 C2 ->
  degree_utyp_wrt_utyp 0 (open_utyp_wrt_utyp C1 C2).
Proof.
unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve degree_utyp_wrt_utyp_open_utyp_wrt_utyp : lngen.

Lemma degree_pskel_wrt_pskel_open_pskel_wrt_pskel :
forall P1 P2,
  degree_pskel_wrt_pskel 1 P1 ->
  degree_pskel_wrt_pskel 0 P2 ->
  degree_pskel_wrt_pskel 0 (open_pskel_wrt_pskel P1 P2).
Proof.
unfold open_pskel_wrt_pskel; default_simp.
Qed.

#[export] Hint Resolve degree_pskel_wrt_pskel_open_pskel_wrt_pskel : lngen.

Lemma degree_bskel_wrt_bskel_open_bskel_wrt_bskel :
forall Q1 Q2,
  degree_bskel_wrt_bskel 1 Q1 ->
  degree_bskel_wrt_bskel 0 Q2 ->
  degree_bskel_wrt_bskel 0 (open_bskel_wrt_bskel Q1 Q2).
Proof.
unfold open_bskel_wrt_bskel; default_simp.
Qed.

#[export] Hint Resolve degree_bskel_wrt_bskel_open_bskel_wrt_bskel : lngen.

Lemma degree_uskel_wrt_uskel_open_uskel_wrt_uskel :
forall R1 R2,
  degree_uskel_wrt_uskel 1 R1 ->
  degree_uskel_wrt_uskel 0 R2 ->
  degree_uskel_wrt_uskel 0 (open_uskel_wrt_uskel R1 R2).
Proof.
unfold open_uskel_wrt_uskel; default_simp.
Qed.

#[export] Hint Resolve degree_uskel_wrt_uskel_open_uskel_wrt_uskel : lngen.

Lemma degree_exp_wrt_ptyp_open_exp_wrt_ptyp :
forall e1 A1,
  degree_exp_wrt_ptyp 1 e1 ->
  degree_ptyp_wrt_ptyp 0 A1 ->
  degree_exp_wrt_ptyp 0 (open_exp_wrt_ptyp e1 A1).
Proof.
unfold open_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_ptyp_open_exp_wrt_ptyp : lngen.

Lemma degree_exp_wrt_ptyp_open_exp_wrt_exp :
forall e1 e2 n1,
  degree_exp_wrt_ptyp n1 e1 ->
  degree_exp_wrt_ptyp n1 e2 ->
  degree_exp_wrt_ptyp n1 (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_ptyp_open_exp_wrt_exp : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_ptyp :
forall e1 A1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_ptyp e1 A1).
Proof.
unfold open_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_ptyp : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_exp :
forall e1 e2,
  degree_exp_wrt_exp 1 e1 ->
  degree_exp_wrt_exp 0 e2 ->
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp : lngen.

(* begin hide *)

Lemma degree_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp_rec_inv_mutual :
(forall A1 A2 n1,
  degree_ptyp_wrt_ptyp n1 (open_ptyp_wrt_ptyp_rec n1 A2 A1) ->
  degree_ptyp_wrt_ptyp (S n1) A1).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp_rec_inv :
forall A1 A2 n1,
  degree_ptyp_wrt_ptyp n1 (open_ptyp_wrt_ptyp_rec n1 A2 A1) ->
  degree_ptyp_wrt_ptyp (S n1) A1.
Proof.
pose proof degree_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_btyp_wrt_btyp_open_btyp_wrt_btyp_rec_inv_mutual :
(forall B1 B2 n1,
  degree_btyp_wrt_btyp n1 (open_btyp_wrt_btyp_rec n1 B2 B1) ->
  degree_btyp_wrt_btyp (S n1) B1).
Proof.
apply_mutual_ind btyp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_btyp_wrt_btyp_open_btyp_wrt_btyp_rec_inv :
forall B1 B2 n1,
  degree_btyp_wrt_btyp n1 (open_btyp_wrt_btyp_rec n1 B2 B1) ->
  degree_btyp_wrt_btyp (S n1) B1.
Proof.
pose proof degree_btyp_wrt_btyp_open_btyp_wrt_btyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_btyp_wrt_btyp_open_btyp_wrt_btyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_utyp_wrt_utyp_open_utyp_wrt_utyp_rec_inv_mutual :
(forall C1 C2 n1,
  degree_utyp_wrt_utyp n1 (open_utyp_wrt_utyp_rec n1 C2 C1) ->
  degree_utyp_wrt_utyp (S n1) C1).
Proof.
apply_mutual_ind utyp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_utyp_wrt_utyp_open_utyp_wrt_utyp_rec_inv :
forall C1 C2 n1,
  degree_utyp_wrt_utyp n1 (open_utyp_wrt_utyp_rec n1 C2 C1) ->
  degree_utyp_wrt_utyp (S n1) C1.
Proof.
pose proof degree_utyp_wrt_utyp_open_utyp_wrt_utyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_utyp_wrt_utyp_open_utyp_wrt_utyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_pskel_wrt_pskel_open_pskel_wrt_pskel_rec_inv_mutual :
(forall P1 P2 n1,
  degree_pskel_wrt_pskel n1 (open_pskel_wrt_pskel_rec n1 P2 P1) ->
  degree_pskel_wrt_pskel (S n1) P1).
Proof.
apply_mutual_ind pskel_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_pskel_wrt_pskel_open_pskel_wrt_pskel_rec_inv :
forall P1 P2 n1,
  degree_pskel_wrt_pskel n1 (open_pskel_wrt_pskel_rec n1 P2 P1) ->
  degree_pskel_wrt_pskel (S n1) P1.
Proof.
pose proof degree_pskel_wrt_pskel_open_pskel_wrt_pskel_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_pskel_wrt_pskel_open_pskel_wrt_pskel_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_bskel_wrt_bskel_open_bskel_wrt_bskel_rec_inv_mutual :
(forall Q1 Q2 n1,
  degree_bskel_wrt_bskel n1 (open_bskel_wrt_bskel_rec n1 Q2 Q1) ->
  degree_bskel_wrt_bskel (S n1) Q1).
Proof.
apply_mutual_ind bskel_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_bskel_wrt_bskel_open_bskel_wrt_bskel_rec_inv :
forall Q1 Q2 n1,
  degree_bskel_wrt_bskel n1 (open_bskel_wrt_bskel_rec n1 Q2 Q1) ->
  degree_bskel_wrt_bskel (S n1) Q1.
Proof.
pose proof degree_bskel_wrt_bskel_open_bskel_wrt_bskel_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_bskel_wrt_bskel_open_bskel_wrt_bskel_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_uskel_wrt_uskel_open_uskel_wrt_uskel_rec_inv_mutual :
(forall R1 R2 n1,
  degree_uskel_wrt_uskel n1 (open_uskel_wrt_uskel_rec n1 R2 R1) ->
  degree_uskel_wrt_uskel (S n1) R1).
Proof.
apply_mutual_ind uskel_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_uskel_wrt_uskel_open_uskel_wrt_uskel_rec_inv :
forall R1 R2 n1,
  degree_uskel_wrt_uskel n1 (open_uskel_wrt_uskel_rec n1 R2 R1) ->
  degree_uskel_wrt_uskel (S n1) R1.
Proof.
pose proof degree_uskel_wrt_uskel_open_uskel_wrt_uskel_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_uskel_wrt_uskel_open_uskel_wrt_uskel_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ptyp_open_exp_wrt_ptyp_rec_inv_mutual :
(forall e1 A1 n1,
  degree_exp_wrt_ptyp n1 (open_exp_wrt_ptyp_rec n1 A1 e1) ->
  degree_exp_wrt_ptyp (S n1) e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ptyp_open_exp_wrt_ptyp_rec_inv :
forall e1 A1 n1,
  degree_exp_wrt_ptyp n1 (open_exp_wrt_ptyp_rec n1 A1 e1) ->
  degree_exp_wrt_ptyp (S n1) e1.
Proof.
pose proof degree_exp_wrt_ptyp_open_exp_wrt_ptyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_ptyp_open_exp_wrt_ptyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ptyp_open_exp_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_ptyp n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_ptyp n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_ptyp_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1 n2,
  degree_exp_wrt_ptyp n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_ptyp n1 e1.
Proof.
pose proof degree_exp_wrt_ptyp_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_ptyp_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_ptyp_rec_inv_mutual :
(forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_ptyp_rec n2 A1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_ptyp_rec_inv :
forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_ptyp_rec n2 A1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_ptyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_ptyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

Lemma degree_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp_inv :
forall A1 A2,
  degree_ptyp_wrt_ptyp 0 (open_ptyp_wrt_ptyp A1 A2) ->
  degree_ptyp_wrt_ptyp 1 A1.
Proof.
unfold open_ptyp_wrt_ptyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp_inv : lngen.

Lemma degree_btyp_wrt_btyp_open_btyp_wrt_btyp_inv :
forall B1 B2,
  degree_btyp_wrt_btyp 0 (open_btyp_wrt_btyp B1 B2) ->
  degree_btyp_wrt_btyp 1 B1.
Proof.
unfold open_btyp_wrt_btyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_btyp_wrt_btyp_open_btyp_wrt_btyp_inv : lngen.

Lemma degree_utyp_wrt_utyp_open_utyp_wrt_utyp_inv :
forall C1 C2,
  degree_utyp_wrt_utyp 0 (open_utyp_wrt_utyp C1 C2) ->
  degree_utyp_wrt_utyp 1 C1.
Proof.
unfold open_utyp_wrt_utyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_utyp_wrt_utyp_open_utyp_wrt_utyp_inv : lngen.

Lemma degree_pskel_wrt_pskel_open_pskel_wrt_pskel_inv :
forall P1 P2,
  degree_pskel_wrt_pskel 0 (open_pskel_wrt_pskel P1 P2) ->
  degree_pskel_wrt_pskel 1 P1.
Proof.
unfold open_pskel_wrt_pskel; eauto with lngen.
Qed.

#[export] Hint Immediate degree_pskel_wrt_pskel_open_pskel_wrt_pskel_inv : lngen.

Lemma degree_bskel_wrt_bskel_open_bskel_wrt_bskel_inv :
forall Q1 Q2,
  degree_bskel_wrt_bskel 0 (open_bskel_wrt_bskel Q1 Q2) ->
  degree_bskel_wrt_bskel 1 Q1.
Proof.
unfold open_bskel_wrt_bskel; eauto with lngen.
Qed.

#[export] Hint Immediate degree_bskel_wrt_bskel_open_bskel_wrt_bskel_inv : lngen.

Lemma degree_uskel_wrt_uskel_open_uskel_wrt_uskel_inv :
forall R1 R2,
  degree_uskel_wrt_uskel 0 (open_uskel_wrt_uskel R1 R2) ->
  degree_uskel_wrt_uskel 1 R1.
Proof.
unfold open_uskel_wrt_uskel; eauto with lngen.
Qed.

#[export] Hint Immediate degree_uskel_wrt_uskel_open_uskel_wrt_uskel_inv : lngen.

Lemma degree_exp_wrt_ptyp_open_exp_wrt_ptyp_inv :
forall e1 A1,
  degree_exp_wrt_ptyp 0 (open_exp_wrt_ptyp e1 A1) ->
  degree_exp_wrt_ptyp 1 e1.
Proof.
unfold open_exp_wrt_ptyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_ptyp_open_exp_wrt_ptyp_inv : lngen.

Lemma degree_exp_wrt_ptyp_open_exp_wrt_exp_inv :
forall e1 e2 n1,
  degree_exp_wrt_ptyp n1 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_ptyp n1 e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_ptyp_open_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_ptyp_inv :
forall e1 A1 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_ptyp e1 A1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
unfold open_exp_wrt_ptyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_ptyp_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_inv :
forall e1 e2,
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_exp 1 e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_ptyp_wrt_ptyp_rec_inj_mutual :
(forall A1 A2 Xpt1 n1,
  close_ptyp_wrt_ptyp_rec n1 Xpt1 A1 = close_ptyp_wrt_ptyp_rec n1 Xpt1 A2 ->
  A1 = A2).
Proof.
apply_mutual_ind ptyp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_ptyp_wrt_ptyp_rec_inj :
forall A1 A2 Xpt1 n1,
  close_ptyp_wrt_ptyp_rec n1 Xpt1 A1 = close_ptyp_wrt_ptyp_rec n1 Xpt1 A2 ->
  A1 = A2.
Proof.
pose proof close_ptyp_wrt_ptyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_ptyp_wrt_ptyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_btyp_wrt_btyp_rec_inj_mutual :
(forall B1 B2 Xbt1 n1,
  close_btyp_wrt_btyp_rec n1 Xbt1 B1 = close_btyp_wrt_btyp_rec n1 Xbt1 B2 ->
  B1 = B2).
Proof.
apply_mutual_ind btyp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_btyp_wrt_btyp_rec_inj :
forall B1 B2 Xbt1 n1,
  close_btyp_wrt_btyp_rec n1 Xbt1 B1 = close_btyp_wrt_btyp_rec n1 Xbt1 B2 ->
  B1 = B2.
Proof.
pose proof close_btyp_wrt_btyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_btyp_wrt_btyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_utyp_wrt_utyp_rec_inj_mutual :
(forall C1 C2 Xut1 n1,
  close_utyp_wrt_utyp_rec n1 Xut1 C1 = close_utyp_wrt_utyp_rec n1 Xut1 C2 ->
  C1 = C2).
Proof.
apply_mutual_ind utyp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_utyp_wrt_utyp_rec_inj :
forall C1 C2 Xut1 n1,
  close_utyp_wrt_utyp_rec n1 Xut1 C1 = close_utyp_wrt_utyp_rec n1 Xut1 C2 ->
  C1 = C2.
Proof.
pose proof close_utyp_wrt_utyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_utyp_wrt_utyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_pskel_wrt_pskel_rec_inj_mutual :
(forall P1 P2 Xps1 n1,
  close_pskel_wrt_pskel_rec n1 Xps1 P1 = close_pskel_wrt_pskel_rec n1 Xps1 P2 ->
  P1 = P2).
Proof.
apply_mutual_ind pskel_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_pskel_wrt_pskel_rec_inj :
forall P1 P2 Xps1 n1,
  close_pskel_wrt_pskel_rec n1 Xps1 P1 = close_pskel_wrt_pskel_rec n1 Xps1 P2 ->
  P1 = P2.
Proof.
pose proof close_pskel_wrt_pskel_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_pskel_wrt_pskel_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_bskel_wrt_bskel_rec_inj_mutual :
(forall Q1 Q2 Xbs1 n1,
  close_bskel_wrt_bskel_rec n1 Xbs1 Q1 = close_bskel_wrt_bskel_rec n1 Xbs1 Q2 ->
  Q1 = Q2).
Proof.
apply_mutual_ind bskel_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_bskel_wrt_bskel_rec_inj :
forall Q1 Q2 Xbs1 n1,
  close_bskel_wrt_bskel_rec n1 Xbs1 Q1 = close_bskel_wrt_bskel_rec n1 Xbs1 Q2 ->
  Q1 = Q2.
Proof.
pose proof close_bskel_wrt_bskel_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_bskel_wrt_bskel_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_uskel_wrt_uskel_rec_inj_mutual :
(forall R1 R2 Xus1 n1,
  close_uskel_wrt_uskel_rec n1 Xus1 R1 = close_uskel_wrt_uskel_rec n1 Xus1 R2 ->
  R1 = R2).
Proof.
apply_mutual_ind uskel_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_uskel_wrt_uskel_rec_inj :
forall R1 R2 Xus1 n1,
  close_uskel_wrt_uskel_rec n1 Xus1 R1 = close_uskel_wrt_uskel_rec n1 Xus1 R2 ->
  R1 = R2.
Proof.
pose proof close_uskel_wrt_uskel_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_uskel_wrt_uskel_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_ptyp_rec_inj_mutual :
(forall e1 e2 Xpt1 n1,
  close_exp_wrt_ptyp_rec n1 Xpt1 e1 = close_exp_wrt_ptyp_rec n1 Xpt1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_ptyp_rec_inj :
forall e1 e2 Xpt1 n1,
  close_exp_wrt_ptyp_rec n1 Xpt1 e1 = close_exp_wrt_ptyp_rec n1 Xpt1 e2 ->
  e1 = e2.
Proof.
pose proof close_exp_wrt_ptyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_exp_wrt_ptyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj_mutual :
(forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj :
forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

Lemma close_ptyp_wrt_ptyp_inj :
forall A1 A2 Xpt1,
  close_ptyp_wrt_ptyp Xpt1 A1 = close_ptyp_wrt_ptyp Xpt1 A2 ->
  A1 = A2.
Proof.
unfold close_ptyp_wrt_ptyp; eauto with lngen.
Qed.

#[export] Hint Immediate close_ptyp_wrt_ptyp_inj : lngen.

Lemma close_btyp_wrt_btyp_inj :
forall B1 B2 Xbt1,
  close_btyp_wrt_btyp Xbt1 B1 = close_btyp_wrt_btyp Xbt1 B2 ->
  B1 = B2.
Proof.
unfold close_btyp_wrt_btyp; eauto with lngen.
Qed.

#[export] Hint Immediate close_btyp_wrt_btyp_inj : lngen.

Lemma close_utyp_wrt_utyp_inj :
forall C1 C2 Xut1,
  close_utyp_wrt_utyp Xut1 C1 = close_utyp_wrt_utyp Xut1 C2 ->
  C1 = C2.
Proof.
unfold close_utyp_wrt_utyp; eauto with lngen.
Qed.

#[export] Hint Immediate close_utyp_wrt_utyp_inj : lngen.

Lemma close_pskel_wrt_pskel_inj :
forall P1 P2 Xps1,
  close_pskel_wrt_pskel Xps1 P1 = close_pskel_wrt_pskel Xps1 P2 ->
  P1 = P2.
Proof.
unfold close_pskel_wrt_pskel; eauto with lngen.
Qed.

#[export] Hint Immediate close_pskel_wrt_pskel_inj : lngen.

Lemma close_bskel_wrt_bskel_inj :
forall Q1 Q2 Xbs1,
  close_bskel_wrt_bskel Xbs1 Q1 = close_bskel_wrt_bskel Xbs1 Q2 ->
  Q1 = Q2.
Proof.
unfold close_bskel_wrt_bskel; eauto with lngen.
Qed.

#[export] Hint Immediate close_bskel_wrt_bskel_inj : lngen.

Lemma close_uskel_wrt_uskel_inj :
forall R1 R2 Xus1,
  close_uskel_wrt_uskel Xus1 R1 = close_uskel_wrt_uskel Xus1 R2 ->
  R1 = R2.
Proof.
unfold close_uskel_wrt_uskel; eauto with lngen.
Qed.

#[export] Hint Immediate close_uskel_wrt_uskel_inj : lngen.

Lemma close_exp_wrt_ptyp_inj :
forall e1 e2 Xpt1,
  close_exp_wrt_ptyp Xpt1 e1 = close_exp_wrt_ptyp Xpt1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_ptyp; eauto with lngen.
Qed.

#[export] Hint Immediate close_exp_wrt_ptyp_inj : lngen.

Lemma close_exp_wrt_exp_inj :
forall e1 e2 x1,
  close_exp_wrt_exp x1 e1 = close_exp_wrt_exp x1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate close_exp_wrt_exp_inj : lngen.

(* begin hide *)

Lemma close_ptyp_wrt_ptyp_rec_open_ptyp_wrt_ptyp_rec_mutual :
(forall A1 Xpt1 n1,
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  close_ptyp_wrt_ptyp_rec n1 Xpt1 (open_ptyp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) A1) = A1).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_ptyp_wrt_ptyp_rec_open_ptyp_wrt_ptyp_rec :
forall A1 Xpt1 n1,
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  close_ptyp_wrt_ptyp_rec n1 Xpt1 (open_ptyp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) A1) = A1.
Proof.
pose proof close_ptyp_wrt_ptyp_rec_open_ptyp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_ptyp_wrt_ptyp_rec_open_ptyp_wrt_ptyp_rec : lngen.
#[export] Hint Rewrite close_ptyp_wrt_ptyp_rec_open_ptyp_wrt_ptyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_btyp_wrt_btyp_rec_open_btyp_wrt_btyp_rec_mutual :
(forall B1 Xbt1 n1,
  Xbt1 `notin` ftvar_in_btyp B1 ->
  close_btyp_wrt_btyp_rec n1 Xbt1 (open_btyp_wrt_btyp_rec n1 (btyp_var_f Xbt1) B1) = B1).
Proof.
apply_mutual_ind btyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_btyp_wrt_btyp_rec_open_btyp_wrt_btyp_rec :
forall B1 Xbt1 n1,
  Xbt1 `notin` ftvar_in_btyp B1 ->
  close_btyp_wrt_btyp_rec n1 Xbt1 (open_btyp_wrt_btyp_rec n1 (btyp_var_f Xbt1) B1) = B1.
Proof.
pose proof close_btyp_wrt_btyp_rec_open_btyp_wrt_btyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_btyp_wrt_btyp_rec_open_btyp_wrt_btyp_rec : lngen.
#[export] Hint Rewrite close_btyp_wrt_btyp_rec_open_btyp_wrt_btyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_utyp_wrt_utyp_rec_open_utyp_wrt_utyp_rec_mutual :
(forall C1 Xut1 n1,
  Xut1 `notin` ftvar_in_utyp C1 ->
  close_utyp_wrt_utyp_rec n1 Xut1 (open_utyp_wrt_utyp_rec n1 (utyp_var_f Xut1) C1) = C1).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_utyp_wrt_utyp_rec_open_utyp_wrt_utyp_rec :
forall C1 Xut1 n1,
  Xut1 `notin` ftvar_in_utyp C1 ->
  close_utyp_wrt_utyp_rec n1 Xut1 (open_utyp_wrt_utyp_rec n1 (utyp_var_f Xut1) C1) = C1.
Proof.
pose proof close_utyp_wrt_utyp_rec_open_utyp_wrt_utyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_utyp_wrt_utyp_rec_open_utyp_wrt_utyp_rec : lngen.
#[export] Hint Rewrite close_utyp_wrt_utyp_rec_open_utyp_wrt_utyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_pskel_wrt_pskel_rec_open_pskel_wrt_pskel_rec_mutual :
(forall P1 Xps1 n1,
  Xps1 `notin` ftvar_in_pskel P1 ->
  close_pskel_wrt_pskel_rec n1 Xps1 (open_pskel_wrt_pskel_rec n1 (pskel_var_f Xps1) P1) = P1).
Proof.
apply_mutual_ind pskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_pskel_wrt_pskel_rec_open_pskel_wrt_pskel_rec :
forall P1 Xps1 n1,
  Xps1 `notin` ftvar_in_pskel P1 ->
  close_pskel_wrt_pskel_rec n1 Xps1 (open_pskel_wrt_pskel_rec n1 (pskel_var_f Xps1) P1) = P1.
Proof.
pose proof close_pskel_wrt_pskel_rec_open_pskel_wrt_pskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_pskel_wrt_pskel_rec_open_pskel_wrt_pskel_rec : lngen.
#[export] Hint Rewrite close_pskel_wrt_pskel_rec_open_pskel_wrt_pskel_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_bskel_wrt_bskel_rec_open_bskel_wrt_bskel_rec_mutual :
(forall Q1 Xbs1 n1,
  Xbs1 `notin` ftvar_in_bskel Q1 ->
  close_bskel_wrt_bskel_rec n1 Xbs1 (open_bskel_wrt_bskel_rec n1 (bskel_var_f Xbs1) Q1) = Q1).
Proof.
apply_mutual_ind bskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_bskel_wrt_bskel_rec_open_bskel_wrt_bskel_rec :
forall Q1 Xbs1 n1,
  Xbs1 `notin` ftvar_in_bskel Q1 ->
  close_bskel_wrt_bskel_rec n1 Xbs1 (open_bskel_wrt_bskel_rec n1 (bskel_var_f Xbs1) Q1) = Q1.
Proof.
pose proof close_bskel_wrt_bskel_rec_open_bskel_wrt_bskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_bskel_wrt_bskel_rec_open_bskel_wrt_bskel_rec : lngen.
#[export] Hint Rewrite close_bskel_wrt_bskel_rec_open_bskel_wrt_bskel_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_uskel_wrt_uskel_rec_open_uskel_wrt_uskel_rec_mutual :
(forall R1 Xus1 n1,
  Xus1 `notin` ftvar_in_uskel R1 ->
  close_uskel_wrt_uskel_rec n1 Xus1 (open_uskel_wrt_uskel_rec n1 (uskel_var_f Xus1) R1) = R1).
Proof.
apply_mutual_ind uskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_uskel_wrt_uskel_rec_open_uskel_wrt_uskel_rec :
forall R1 Xus1 n1,
  Xus1 `notin` ftvar_in_uskel R1 ->
  close_uskel_wrt_uskel_rec n1 Xus1 (open_uskel_wrt_uskel_rec n1 (uskel_var_f Xus1) R1) = R1.
Proof.
pose proof close_uskel_wrt_uskel_rec_open_uskel_wrt_uskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_uskel_wrt_uskel_rec_open_uskel_wrt_uskel_rec : lngen.
#[export] Hint Rewrite close_uskel_wrt_uskel_rec_open_uskel_wrt_uskel_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_ptyp_rec_open_exp_wrt_ptyp_rec_mutual :
(forall e1 Xpt1 n1,
  Xpt1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_ptyp_rec n1 Xpt1 (open_exp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_ptyp_rec_open_exp_wrt_ptyp_rec :
forall e1 Xpt1 n1,
  Xpt1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_ptyp_rec n1 Xpt1 (open_exp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) e1) = e1.
Proof.
pose proof close_exp_wrt_ptyp_rec_open_exp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_exp_wrt_ptyp_rec_open_exp_wrt_ptyp_rec : lngen.
#[export] Hint Rewrite close_exp_wrt_ptyp_rec_open_exp_wrt_ptyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  x1 `notin` fvar_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e1 x1 n1,
  x1 `notin` fvar_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = e1.
Proof.
pose proof close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_rec_open_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp :
forall A1 Xpt1,
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  close_ptyp_wrt_ptyp Xpt1 (open_ptyp_wrt_ptyp A1 (ptyp_var_f Xpt1)) = A1.
Proof.
unfold close_ptyp_wrt_ptyp; unfold open_ptyp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve close_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp : lngen.
#[export] Hint Rewrite close_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp using solve [auto] : lngen.

Lemma close_btyp_wrt_btyp_open_btyp_wrt_btyp :
forall B1 Xbt1,
  Xbt1 `notin` ftvar_in_btyp B1 ->
  close_btyp_wrt_btyp Xbt1 (open_btyp_wrt_btyp B1 (btyp_var_f Xbt1)) = B1.
Proof.
unfold close_btyp_wrt_btyp; unfold open_btyp_wrt_btyp; default_simp.
Qed.

#[export] Hint Resolve close_btyp_wrt_btyp_open_btyp_wrt_btyp : lngen.
#[export] Hint Rewrite close_btyp_wrt_btyp_open_btyp_wrt_btyp using solve [auto] : lngen.

Lemma close_utyp_wrt_utyp_open_utyp_wrt_utyp :
forall C1 Xut1,
  Xut1 `notin` ftvar_in_utyp C1 ->
  close_utyp_wrt_utyp Xut1 (open_utyp_wrt_utyp C1 (utyp_var_f Xut1)) = C1.
Proof.
unfold close_utyp_wrt_utyp; unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve close_utyp_wrt_utyp_open_utyp_wrt_utyp : lngen.
#[export] Hint Rewrite close_utyp_wrt_utyp_open_utyp_wrt_utyp using solve [auto] : lngen.

Lemma close_pskel_wrt_pskel_open_pskel_wrt_pskel :
forall P1 Xps1,
  Xps1 `notin` ftvar_in_pskel P1 ->
  close_pskel_wrt_pskel Xps1 (open_pskel_wrt_pskel P1 (pskel_var_f Xps1)) = P1.
Proof.
unfold close_pskel_wrt_pskel; unfold open_pskel_wrt_pskel; default_simp.
Qed.

#[export] Hint Resolve close_pskel_wrt_pskel_open_pskel_wrt_pskel : lngen.
#[export] Hint Rewrite close_pskel_wrt_pskel_open_pskel_wrt_pskel using solve [auto] : lngen.

Lemma close_bskel_wrt_bskel_open_bskel_wrt_bskel :
forall Q1 Xbs1,
  Xbs1 `notin` ftvar_in_bskel Q1 ->
  close_bskel_wrt_bskel Xbs1 (open_bskel_wrt_bskel Q1 (bskel_var_f Xbs1)) = Q1.
Proof.
unfold close_bskel_wrt_bskel; unfold open_bskel_wrt_bskel; default_simp.
Qed.

#[export] Hint Resolve close_bskel_wrt_bskel_open_bskel_wrt_bskel : lngen.
#[export] Hint Rewrite close_bskel_wrt_bskel_open_bskel_wrt_bskel using solve [auto] : lngen.

Lemma close_uskel_wrt_uskel_open_uskel_wrt_uskel :
forall R1 Xus1,
  Xus1 `notin` ftvar_in_uskel R1 ->
  close_uskel_wrt_uskel Xus1 (open_uskel_wrt_uskel R1 (uskel_var_f Xus1)) = R1.
Proof.
unfold close_uskel_wrt_uskel; unfold open_uskel_wrt_uskel; default_simp.
Qed.

#[export] Hint Resolve close_uskel_wrt_uskel_open_uskel_wrt_uskel : lngen.
#[export] Hint Rewrite close_uskel_wrt_uskel_open_uskel_wrt_uskel using solve [auto] : lngen.

Lemma close_exp_wrt_ptyp_open_exp_wrt_ptyp :
forall e1 Xpt1,
  Xpt1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_ptyp Xpt1 (open_exp_wrt_ptyp e1 (ptyp_var_f Xpt1)) = e1.
Proof.
unfold close_exp_wrt_ptyp; unfold open_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve close_exp_wrt_ptyp_open_exp_wrt_ptyp : lngen.
#[export] Hint Rewrite close_exp_wrt_ptyp_open_exp_wrt_ptyp using solve [auto] : lngen.

Lemma close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  close_exp_wrt_exp x1 (open_exp_wrt_exp e1 (exp_var_f x1)) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve close_exp_wrt_exp_open_exp_wrt_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_open_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_ptyp_wrt_ptyp_rec_close_ptyp_wrt_ptyp_rec_mutual :
(forall A1 Xpt1 n1,
  open_ptyp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) (close_ptyp_wrt_ptyp_rec n1 Xpt1 A1) = A1).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_ptyp_wrt_ptyp_rec_close_ptyp_wrt_ptyp_rec :
forall A1 Xpt1 n1,
  open_ptyp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) (close_ptyp_wrt_ptyp_rec n1 Xpt1 A1) = A1.
Proof.
pose proof open_ptyp_wrt_ptyp_rec_close_ptyp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_ptyp_wrt_ptyp_rec_close_ptyp_wrt_ptyp_rec : lngen.
#[export] Hint Rewrite open_ptyp_wrt_ptyp_rec_close_ptyp_wrt_ptyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_btyp_wrt_btyp_rec_close_btyp_wrt_btyp_rec_mutual :
(forall B1 Xbt1 n1,
  open_btyp_wrt_btyp_rec n1 (btyp_var_f Xbt1) (close_btyp_wrt_btyp_rec n1 Xbt1 B1) = B1).
Proof.
apply_mutual_ind btyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_btyp_wrt_btyp_rec_close_btyp_wrt_btyp_rec :
forall B1 Xbt1 n1,
  open_btyp_wrt_btyp_rec n1 (btyp_var_f Xbt1) (close_btyp_wrt_btyp_rec n1 Xbt1 B1) = B1.
Proof.
pose proof open_btyp_wrt_btyp_rec_close_btyp_wrt_btyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_btyp_wrt_btyp_rec_close_btyp_wrt_btyp_rec : lngen.
#[export] Hint Rewrite open_btyp_wrt_btyp_rec_close_btyp_wrt_btyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_utyp_wrt_utyp_rec_close_utyp_wrt_utyp_rec_mutual :
(forall C1 Xut1 n1,
  open_utyp_wrt_utyp_rec n1 (utyp_var_f Xut1) (close_utyp_wrt_utyp_rec n1 Xut1 C1) = C1).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_utyp_wrt_utyp_rec_close_utyp_wrt_utyp_rec :
forall C1 Xut1 n1,
  open_utyp_wrt_utyp_rec n1 (utyp_var_f Xut1) (close_utyp_wrt_utyp_rec n1 Xut1 C1) = C1.
Proof.
pose proof open_utyp_wrt_utyp_rec_close_utyp_wrt_utyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_utyp_wrt_utyp_rec_close_utyp_wrt_utyp_rec : lngen.
#[export] Hint Rewrite open_utyp_wrt_utyp_rec_close_utyp_wrt_utyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_pskel_wrt_pskel_rec_close_pskel_wrt_pskel_rec_mutual :
(forall P1 Xps1 n1,
  open_pskel_wrt_pskel_rec n1 (pskel_var_f Xps1) (close_pskel_wrt_pskel_rec n1 Xps1 P1) = P1).
Proof.
apply_mutual_ind pskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_pskel_wrt_pskel_rec_close_pskel_wrt_pskel_rec :
forall P1 Xps1 n1,
  open_pskel_wrt_pskel_rec n1 (pskel_var_f Xps1) (close_pskel_wrt_pskel_rec n1 Xps1 P1) = P1.
Proof.
pose proof open_pskel_wrt_pskel_rec_close_pskel_wrt_pskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_pskel_wrt_pskel_rec_close_pskel_wrt_pskel_rec : lngen.
#[export] Hint Rewrite open_pskel_wrt_pskel_rec_close_pskel_wrt_pskel_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_bskel_wrt_bskel_rec_close_bskel_wrt_bskel_rec_mutual :
(forall Q1 Xbs1 n1,
  open_bskel_wrt_bskel_rec n1 (bskel_var_f Xbs1) (close_bskel_wrt_bskel_rec n1 Xbs1 Q1) = Q1).
Proof.
apply_mutual_ind bskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_bskel_wrt_bskel_rec_close_bskel_wrt_bskel_rec :
forall Q1 Xbs1 n1,
  open_bskel_wrt_bskel_rec n1 (bskel_var_f Xbs1) (close_bskel_wrt_bskel_rec n1 Xbs1 Q1) = Q1.
Proof.
pose proof open_bskel_wrt_bskel_rec_close_bskel_wrt_bskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_bskel_wrt_bskel_rec_close_bskel_wrt_bskel_rec : lngen.
#[export] Hint Rewrite open_bskel_wrt_bskel_rec_close_bskel_wrt_bskel_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_uskel_wrt_uskel_rec_close_uskel_wrt_uskel_rec_mutual :
(forall R1 Xus1 n1,
  open_uskel_wrt_uskel_rec n1 (uskel_var_f Xus1) (close_uskel_wrt_uskel_rec n1 Xus1 R1) = R1).
Proof.
apply_mutual_ind uskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_uskel_wrt_uskel_rec_close_uskel_wrt_uskel_rec :
forall R1 Xus1 n1,
  open_uskel_wrt_uskel_rec n1 (uskel_var_f Xus1) (close_uskel_wrt_uskel_rec n1 Xus1 R1) = R1.
Proof.
pose proof open_uskel_wrt_uskel_rec_close_uskel_wrt_uskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_uskel_wrt_uskel_rec_close_uskel_wrt_uskel_rec : lngen.
#[export] Hint Rewrite open_uskel_wrt_uskel_rec_close_uskel_wrt_uskel_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_ptyp_rec_close_exp_wrt_ptyp_rec_mutual :
(forall e1 Xpt1 n1,
  open_exp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) (close_exp_wrt_ptyp_rec n1 Xpt1 e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_ptyp_rec_close_exp_wrt_ptyp_rec :
forall e1 Xpt1 n1,
  open_exp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) (close_exp_wrt_ptyp_rec n1 Xpt1 e1) = e1.
Proof.
pose proof open_exp_wrt_ptyp_rec_close_exp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_exp_wrt_ptyp_rec_close_exp_wrt_ptyp_rec : lngen.
#[export] Hint Rewrite open_exp_wrt_ptyp_rec_close_exp_wrt_ptyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  open_exp_wrt_exp_rec n1 (exp_var_f x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  open_exp_wrt_exp_rec n1 (exp_var_f x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1.
Proof.
pose proof open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_exp_wrt_exp_rec_close_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_rec_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp :
forall A1 Xpt1,
  open_ptyp_wrt_ptyp (close_ptyp_wrt_ptyp Xpt1 A1) (ptyp_var_f Xpt1) = A1.
Proof.
unfold close_ptyp_wrt_ptyp; unfold open_ptyp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp : lngen.
#[export] Hint Rewrite open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp using solve [auto] : lngen.

Lemma open_btyp_wrt_btyp_close_btyp_wrt_btyp :
forall B1 Xbt1,
  open_btyp_wrt_btyp (close_btyp_wrt_btyp Xbt1 B1) (btyp_var_f Xbt1) = B1.
Proof.
unfold close_btyp_wrt_btyp; unfold open_btyp_wrt_btyp; default_simp.
Qed.

#[export] Hint Resolve open_btyp_wrt_btyp_close_btyp_wrt_btyp : lngen.
#[export] Hint Rewrite open_btyp_wrt_btyp_close_btyp_wrt_btyp using solve [auto] : lngen.

Lemma open_utyp_wrt_utyp_close_utyp_wrt_utyp :
forall C1 Xut1,
  open_utyp_wrt_utyp (close_utyp_wrt_utyp Xut1 C1) (utyp_var_f Xut1) = C1.
Proof.
unfold close_utyp_wrt_utyp; unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve open_utyp_wrt_utyp_close_utyp_wrt_utyp : lngen.
#[export] Hint Rewrite open_utyp_wrt_utyp_close_utyp_wrt_utyp using solve [auto] : lngen.

Lemma open_pskel_wrt_pskel_close_pskel_wrt_pskel :
forall P1 Xps1,
  open_pskel_wrt_pskel (close_pskel_wrt_pskel Xps1 P1) (pskel_var_f Xps1) = P1.
Proof.
unfold close_pskel_wrt_pskel; unfold open_pskel_wrt_pskel; default_simp.
Qed.

#[export] Hint Resolve open_pskel_wrt_pskel_close_pskel_wrt_pskel : lngen.
#[export] Hint Rewrite open_pskel_wrt_pskel_close_pskel_wrt_pskel using solve [auto] : lngen.

Lemma open_bskel_wrt_bskel_close_bskel_wrt_bskel :
forall Q1 Xbs1,
  open_bskel_wrt_bskel (close_bskel_wrt_bskel Xbs1 Q1) (bskel_var_f Xbs1) = Q1.
Proof.
unfold close_bskel_wrt_bskel; unfold open_bskel_wrt_bskel; default_simp.
Qed.

#[export] Hint Resolve open_bskel_wrt_bskel_close_bskel_wrt_bskel : lngen.
#[export] Hint Rewrite open_bskel_wrt_bskel_close_bskel_wrt_bskel using solve [auto] : lngen.

Lemma open_uskel_wrt_uskel_close_uskel_wrt_uskel :
forall R1 Xus1,
  open_uskel_wrt_uskel (close_uskel_wrt_uskel Xus1 R1) (uskel_var_f Xus1) = R1.
Proof.
unfold close_uskel_wrt_uskel; unfold open_uskel_wrt_uskel; default_simp.
Qed.

#[export] Hint Resolve open_uskel_wrt_uskel_close_uskel_wrt_uskel : lngen.
#[export] Hint Rewrite open_uskel_wrt_uskel_close_uskel_wrt_uskel using solve [auto] : lngen.

Lemma open_exp_wrt_ptyp_close_exp_wrt_ptyp :
forall e1 Xpt1,
  open_exp_wrt_ptyp (close_exp_wrt_ptyp Xpt1 e1) (ptyp_var_f Xpt1) = e1.
Proof.
unfold close_exp_wrt_ptyp; unfold open_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_ptyp_close_exp_wrt_ptyp : lngen.
#[export] Hint Rewrite open_exp_wrt_ptyp_close_exp_wrt_ptyp using solve [auto] : lngen.

Lemma open_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  open_exp_wrt_exp (close_exp_wrt_exp x1 e1) (exp_var_f x1) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_ptyp_wrt_ptyp_rec_inj_mutual :
(forall A2 A1 Xpt1 n1,
  Xpt1 `notin` ftvar_in_ptyp A2 ->
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  open_ptyp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) A2 = open_ptyp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) A1 ->
  A2 = A1).
Proof.
apply_mutual_ind ptyp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_ptyp_wrt_ptyp_rec_inj :
forall A2 A1 Xpt1 n1,
  Xpt1 `notin` ftvar_in_ptyp A2 ->
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  open_ptyp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) A2 = open_ptyp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) A1 ->
  A2 = A1.
Proof.
pose proof open_ptyp_wrt_ptyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_ptyp_wrt_ptyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_btyp_wrt_btyp_rec_inj_mutual :
(forall B2 B1 Xbt1 n1,
  Xbt1 `notin` ftvar_in_btyp B2 ->
  Xbt1 `notin` ftvar_in_btyp B1 ->
  open_btyp_wrt_btyp_rec n1 (btyp_var_f Xbt1) B2 = open_btyp_wrt_btyp_rec n1 (btyp_var_f Xbt1) B1 ->
  B2 = B1).
Proof.
apply_mutual_ind btyp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_btyp_wrt_btyp_rec_inj :
forall B2 B1 Xbt1 n1,
  Xbt1 `notin` ftvar_in_btyp B2 ->
  Xbt1 `notin` ftvar_in_btyp B1 ->
  open_btyp_wrt_btyp_rec n1 (btyp_var_f Xbt1) B2 = open_btyp_wrt_btyp_rec n1 (btyp_var_f Xbt1) B1 ->
  B2 = B1.
Proof.
pose proof open_btyp_wrt_btyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_btyp_wrt_btyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_utyp_wrt_utyp_rec_inj_mutual :
(forall C2 C1 Xut1 n1,
  Xut1 `notin` ftvar_in_utyp C2 ->
  Xut1 `notin` ftvar_in_utyp C1 ->
  open_utyp_wrt_utyp_rec n1 (utyp_var_f Xut1) C2 = open_utyp_wrt_utyp_rec n1 (utyp_var_f Xut1) C1 ->
  C2 = C1).
Proof.
apply_mutual_ind utyp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_utyp_wrt_utyp_rec_inj :
forall C2 C1 Xut1 n1,
  Xut1 `notin` ftvar_in_utyp C2 ->
  Xut1 `notin` ftvar_in_utyp C1 ->
  open_utyp_wrt_utyp_rec n1 (utyp_var_f Xut1) C2 = open_utyp_wrt_utyp_rec n1 (utyp_var_f Xut1) C1 ->
  C2 = C1.
Proof.
pose proof open_utyp_wrt_utyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_utyp_wrt_utyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_pskel_wrt_pskel_rec_inj_mutual :
(forall P2 P1 Xps1 n1,
  Xps1 `notin` ftvar_in_pskel P2 ->
  Xps1 `notin` ftvar_in_pskel P1 ->
  open_pskel_wrt_pskel_rec n1 (pskel_var_f Xps1) P2 = open_pskel_wrt_pskel_rec n1 (pskel_var_f Xps1) P1 ->
  P2 = P1).
Proof.
apply_mutual_ind pskel_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_pskel_wrt_pskel_rec_inj :
forall P2 P1 Xps1 n1,
  Xps1 `notin` ftvar_in_pskel P2 ->
  Xps1 `notin` ftvar_in_pskel P1 ->
  open_pskel_wrt_pskel_rec n1 (pskel_var_f Xps1) P2 = open_pskel_wrt_pskel_rec n1 (pskel_var_f Xps1) P1 ->
  P2 = P1.
Proof.
pose proof open_pskel_wrt_pskel_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_pskel_wrt_pskel_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_bskel_wrt_bskel_rec_inj_mutual :
(forall Q2 Q1 Xbs1 n1,
  Xbs1 `notin` ftvar_in_bskel Q2 ->
  Xbs1 `notin` ftvar_in_bskel Q1 ->
  open_bskel_wrt_bskel_rec n1 (bskel_var_f Xbs1) Q2 = open_bskel_wrt_bskel_rec n1 (bskel_var_f Xbs1) Q1 ->
  Q2 = Q1).
Proof.
apply_mutual_ind bskel_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_bskel_wrt_bskel_rec_inj :
forall Q2 Q1 Xbs1 n1,
  Xbs1 `notin` ftvar_in_bskel Q2 ->
  Xbs1 `notin` ftvar_in_bskel Q1 ->
  open_bskel_wrt_bskel_rec n1 (bskel_var_f Xbs1) Q2 = open_bskel_wrt_bskel_rec n1 (bskel_var_f Xbs1) Q1 ->
  Q2 = Q1.
Proof.
pose proof open_bskel_wrt_bskel_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_bskel_wrt_bskel_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_uskel_wrt_uskel_rec_inj_mutual :
(forall R2 R1 Xus1 n1,
  Xus1 `notin` ftvar_in_uskel R2 ->
  Xus1 `notin` ftvar_in_uskel R1 ->
  open_uskel_wrt_uskel_rec n1 (uskel_var_f Xus1) R2 = open_uskel_wrt_uskel_rec n1 (uskel_var_f Xus1) R1 ->
  R2 = R1).
Proof.
apply_mutual_ind uskel_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_uskel_wrt_uskel_rec_inj :
forall R2 R1 Xus1 n1,
  Xus1 `notin` ftvar_in_uskel R2 ->
  Xus1 `notin` ftvar_in_uskel R1 ->
  open_uskel_wrt_uskel_rec n1 (uskel_var_f Xus1) R2 = open_uskel_wrt_uskel_rec n1 (uskel_var_f Xus1) R1 ->
  R2 = R1.
Proof.
pose proof open_uskel_wrt_uskel_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_uskel_wrt_uskel_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_ptyp_rec_inj_mutual :
(forall e2 e1 Xpt1 n1,
  Xpt1 `notin` ftvar_in_exp e2 ->
  Xpt1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) e2 = open_exp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_ptyp_rec_inj :
forall e2 e1 Xpt1 n1,
  Xpt1 `notin` ftvar_in_exp e2 ->
  Xpt1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) e2 = open_exp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) e1 ->
  e2 = e1.
Proof.
pose proof open_exp_wrt_ptyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_exp_wrt_ptyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj_mutual :
(forall e2 e1 x1 n1,
  x1 `notin` fvar_in_exp e2 ->
  x1 `notin` fvar_in_exp e1 ->
  open_exp_wrt_exp_rec n1 (exp_var_f x1) e2 = open_exp_wrt_exp_rec n1 (exp_var_f x1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` fvar_in_exp e2 ->
  x1 `notin` fvar_in_exp e1 ->
  open_exp_wrt_exp_rec n1 (exp_var_f x1) e2 = open_exp_wrt_exp_rec n1 (exp_var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

Lemma open_ptyp_wrt_ptyp_inj :
forall A2 A1 Xpt1,
  Xpt1 `notin` ftvar_in_ptyp A2 ->
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  open_ptyp_wrt_ptyp A2 (ptyp_var_f Xpt1) = open_ptyp_wrt_ptyp A1 (ptyp_var_f Xpt1) ->
  A2 = A1.
Proof.
unfold open_ptyp_wrt_ptyp; eauto with lngen.
Qed.

#[export] Hint Immediate open_ptyp_wrt_ptyp_inj : lngen.

Lemma open_btyp_wrt_btyp_inj :
forall B2 B1 Xbt1,
  Xbt1 `notin` ftvar_in_btyp B2 ->
  Xbt1 `notin` ftvar_in_btyp B1 ->
  open_btyp_wrt_btyp B2 (btyp_var_f Xbt1) = open_btyp_wrt_btyp B1 (btyp_var_f Xbt1) ->
  B2 = B1.
Proof.
unfold open_btyp_wrt_btyp; eauto with lngen.
Qed.

#[export] Hint Immediate open_btyp_wrt_btyp_inj : lngen.

Lemma open_utyp_wrt_utyp_inj :
forall C2 C1 Xut1,
  Xut1 `notin` ftvar_in_utyp C2 ->
  Xut1 `notin` ftvar_in_utyp C1 ->
  open_utyp_wrt_utyp C2 (utyp_var_f Xut1) = open_utyp_wrt_utyp C1 (utyp_var_f Xut1) ->
  C2 = C1.
Proof.
unfold open_utyp_wrt_utyp; eauto with lngen.
Qed.

#[export] Hint Immediate open_utyp_wrt_utyp_inj : lngen.

Lemma open_pskel_wrt_pskel_inj :
forall P2 P1 Xps1,
  Xps1 `notin` ftvar_in_pskel P2 ->
  Xps1 `notin` ftvar_in_pskel P1 ->
  open_pskel_wrt_pskel P2 (pskel_var_f Xps1) = open_pskel_wrt_pskel P1 (pskel_var_f Xps1) ->
  P2 = P1.
Proof.
unfold open_pskel_wrt_pskel; eauto with lngen.
Qed.

#[export] Hint Immediate open_pskel_wrt_pskel_inj : lngen.

Lemma open_bskel_wrt_bskel_inj :
forall Q2 Q1 Xbs1,
  Xbs1 `notin` ftvar_in_bskel Q2 ->
  Xbs1 `notin` ftvar_in_bskel Q1 ->
  open_bskel_wrt_bskel Q2 (bskel_var_f Xbs1) = open_bskel_wrt_bskel Q1 (bskel_var_f Xbs1) ->
  Q2 = Q1.
Proof.
unfold open_bskel_wrt_bskel; eauto with lngen.
Qed.

#[export] Hint Immediate open_bskel_wrt_bskel_inj : lngen.

Lemma open_uskel_wrt_uskel_inj :
forall R2 R1 Xus1,
  Xus1 `notin` ftvar_in_uskel R2 ->
  Xus1 `notin` ftvar_in_uskel R1 ->
  open_uskel_wrt_uskel R2 (uskel_var_f Xus1) = open_uskel_wrt_uskel R1 (uskel_var_f Xus1) ->
  R2 = R1.
Proof.
unfold open_uskel_wrt_uskel; eauto with lngen.
Qed.

#[export] Hint Immediate open_uskel_wrt_uskel_inj : lngen.

Lemma open_exp_wrt_ptyp_inj :
forall e2 e1 Xpt1,
  Xpt1 `notin` ftvar_in_exp e2 ->
  Xpt1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_ptyp e2 (ptyp_var_f Xpt1) = open_exp_wrt_ptyp e1 (ptyp_var_f Xpt1) ->
  e2 = e1.
Proof.
unfold open_exp_wrt_ptyp; eauto with lngen.
Qed.

#[export] Hint Immediate open_exp_wrt_ptyp_inj : lngen.

Lemma open_exp_wrt_exp_inj :
forall e2 e1 x1,
  x1 `notin` fvar_in_exp e2 ->
  x1 `notin` fvar_in_exp e1 ->
  open_exp_wrt_exp e2 (exp_var_f x1) = open_exp_wrt_exp e1 (exp_var_f x1) ->
  e2 = e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate open_exp_wrt_exp_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_ptyp_wrt_ptyp_of_lc_ptyp_mutual :
(forall A1,
  lc_ptyp A1 ->
  degree_ptyp_wrt_ptyp 0 A1).
Proof.
apply_mutual_ind lc_ptyp_mutind;
intros;
let Xpt1 := fresh "Xpt1" in pick_fresh Xpt1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_ptyp_wrt_ptyp_of_lc_ptyp :
forall A1,
  lc_ptyp A1 ->
  degree_ptyp_wrt_ptyp 0 A1.
Proof.
pose proof degree_ptyp_wrt_ptyp_of_lc_ptyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ptyp_wrt_ptyp_of_lc_ptyp : lngen.

(* begin hide *)

Lemma degree_btyp_wrt_btyp_of_lc_btyp_mutual :
(forall B1,
  lc_btyp B1 ->
  degree_btyp_wrt_btyp 0 B1).
Proof.
apply_mutual_ind lc_btyp_mutind;
intros;
let Xbt1 := fresh "Xbt1" in pick_fresh Xbt1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_btyp_wrt_btyp_of_lc_btyp :
forall B1,
  lc_btyp B1 ->
  degree_btyp_wrt_btyp 0 B1.
Proof.
pose proof degree_btyp_wrt_btyp_of_lc_btyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_btyp_wrt_btyp_of_lc_btyp : lngen.

(* begin hide *)

Lemma degree_utyp_wrt_utyp_of_lc_utyp_mutual :
(forall C1,
  lc_utyp C1 ->
  degree_utyp_wrt_utyp 0 C1).
Proof.
apply_mutual_ind lc_utyp_mutind;
intros;
let Xut1 := fresh "Xut1" in pick_fresh Xut1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_utyp_wrt_utyp_of_lc_utyp :
forall C1,
  lc_utyp C1 ->
  degree_utyp_wrt_utyp 0 C1.
Proof.
pose proof degree_utyp_wrt_utyp_of_lc_utyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_utyp_wrt_utyp_of_lc_utyp : lngen.

(* begin hide *)

Lemma degree_pskel_wrt_pskel_of_lc_pskel_mutual :
(forall P1,
  lc_pskel P1 ->
  degree_pskel_wrt_pskel 0 P1).
Proof.
apply_mutual_ind lc_pskel_mutind;
intros;
let Xps1 := fresh "Xps1" in pick_fresh Xps1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_pskel_wrt_pskel_of_lc_pskel :
forall P1,
  lc_pskel P1 ->
  degree_pskel_wrt_pskel 0 P1.
Proof.
pose proof degree_pskel_wrt_pskel_of_lc_pskel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_pskel_wrt_pskel_of_lc_pskel : lngen.

(* begin hide *)

Lemma degree_bskel_wrt_bskel_of_lc_bskel_mutual :
(forall Q1,
  lc_bskel Q1 ->
  degree_bskel_wrt_bskel 0 Q1).
Proof.
apply_mutual_ind lc_bskel_mutind;
intros;
let Xbs1 := fresh "Xbs1" in pick_fresh Xbs1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_bskel_wrt_bskel_of_lc_bskel :
forall Q1,
  lc_bskel Q1 ->
  degree_bskel_wrt_bskel 0 Q1.
Proof.
pose proof degree_bskel_wrt_bskel_of_lc_bskel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_bskel_wrt_bskel_of_lc_bskel : lngen.

(* begin hide *)

Lemma degree_uskel_wrt_uskel_of_lc_uskel_mutual :
(forall R1,
  lc_uskel R1 ->
  degree_uskel_wrt_uskel 0 R1).
Proof.
apply_mutual_ind lc_uskel_mutind;
intros;
let Xus1 := fresh "Xus1" in pick_fresh Xus1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_uskel_wrt_uskel_of_lc_uskel :
forall R1,
  lc_uskel R1 ->
  degree_uskel_wrt_uskel 0 R1.
Proof.
pose proof degree_uskel_wrt_uskel_of_lc_uskel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_uskel_wrt_uskel_of_lc_uskel : lngen.

(* begin hide *)

Lemma degree_exp_wrt_ptyp_of_lc_exp_mutual :
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_ptyp 0 e1).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let Xpt1 := fresh "Xpt1" in pick_fresh Xpt1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_exp_wrt_ptyp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_ptyp 0 e1.
Proof.
pose proof degree_exp_wrt_ptyp_of_lc_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_ptyp_of_lc_exp : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_of_lc_exp_mutual :
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let Xpt1 := fresh "Xpt1" in pick_fresh Xpt1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_exp_wrt_exp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1.
Proof.
pose proof degree_exp_wrt_exp_of_lc_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_of_lc_exp : lngen.

(* begin hide *)

Lemma lc_ptyp_of_degree_size_mutual :
forall i1,
(forall A1,
  size_ptyp A1 = i1 ->
  degree_ptyp_wrt_ptyp 0 A1 ->
  lc_ptyp A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind ptyp_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_ptyp_of_degree :
forall A1,
  degree_ptyp_wrt_ptyp 0 A1 ->
  lc_ptyp A1.
Proof.
intros A1; intros;
pose proof (lc_ptyp_of_degree_size_mutual (size_ptyp A1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_ptyp_of_degree : lngen.

(* begin hide *)

Lemma lc_btyp_of_degree_size_mutual :
forall i1,
(forall B1,
  size_btyp B1 = i1 ->
  degree_btyp_wrt_btyp 0 B1 ->
  lc_btyp B1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind btyp_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_btyp_of_degree :
forall B1,
  degree_btyp_wrt_btyp 0 B1 ->
  lc_btyp B1.
Proof.
intros B1; intros;
pose proof (lc_btyp_of_degree_size_mutual (size_btyp B1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_btyp_of_degree : lngen.

(* begin hide *)

Lemma lc_utyp_of_degree_size_mutual :
forall i1,
(forall C1,
  size_utyp C1 = i1 ->
  degree_utyp_wrt_utyp 0 C1 ->
  lc_utyp C1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind utyp_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_utyp_of_degree :
forall C1,
  degree_utyp_wrt_utyp 0 C1 ->
  lc_utyp C1.
Proof.
intros C1; intros;
pose proof (lc_utyp_of_degree_size_mutual (size_utyp C1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_utyp_of_degree : lngen.

(* begin hide *)

Lemma lc_pskel_of_degree_size_mutual :
forall i1,
(forall P1,
  size_pskel P1 = i1 ->
  degree_pskel_wrt_pskel 0 P1 ->
  lc_pskel P1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind pskel_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_pskel_of_degree :
forall P1,
  degree_pskel_wrt_pskel 0 P1 ->
  lc_pskel P1.
Proof.
intros P1; intros;
pose proof (lc_pskel_of_degree_size_mutual (size_pskel P1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_pskel_of_degree : lngen.

(* begin hide *)

Lemma lc_bskel_of_degree_size_mutual :
forall i1,
(forall Q1,
  size_bskel Q1 = i1 ->
  degree_bskel_wrt_bskel 0 Q1 ->
  lc_bskel Q1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind bskel_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_bskel_of_degree :
forall Q1,
  degree_bskel_wrt_bskel 0 Q1 ->
  lc_bskel Q1.
Proof.
intros Q1; intros;
pose proof (lc_bskel_of_degree_size_mutual (size_bskel Q1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_bskel_of_degree : lngen.

(* begin hide *)

Lemma lc_uskel_of_degree_size_mutual :
forall i1,
(forall R1,
  size_uskel R1 = i1 ->
  degree_uskel_wrt_uskel 0 R1 ->
  lc_uskel R1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind uskel_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_uskel_of_degree :
forall R1,
  degree_uskel_wrt_uskel 0 R1 ->
  lc_uskel R1.
Proof.
intros R1; intros;
pose proof (lc_uskel_of_degree_size_mutual (size_uskel R1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_uskel_of_degree : lngen.

(* begin hide *)

Lemma lc_exp_of_degree_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  degree_exp_wrt_ptyp 0 e1 ->
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind exp_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_exp_of_degree :
forall e1,
  degree_exp_wrt_ptyp 0 e1 ->
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1.
Proof.
intros e1; intros;
pose proof (lc_exp_of_degree_size_mutual (size_exp e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_exp_of_degree : lngen.

Ltac ptyp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_ptyp_wrt_ptyp_of_lc_ptyp in J1; clear H
          end).

Ltac btyp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_btyp_wrt_btyp_of_lc_btyp in J1; clear H
          end).

Ltac utyp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_utyp_wrt_utyp_of_lc_utyp in J1; clear H
          end).

Ltac pskel_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_pskel_wrt_pskel_of_lc_pskel in J1; clear H
          end).

Ltac bskel_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_bskel_wrt_bskel_of_lc_bskel in J1; clear H
          end).

Ltac uskel_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_uskel_wrt_uskel_of_lc_uskel in J1; clear H
          end).

Ltac exp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_exp_wrt_ptyp_of_lc_exp in J1;
              let J2 := fresh in pose proof H as J2; apply degree_exp_wrt_exp_of_lc_exp in J2; clear H
          end).

Ltac mode_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Lemma lc_ptyp_all_exists :
forall Xpt1 A1,
  lc_ptyp (open_ptyp_wrt_ptyp A1 (ptyp_var_f Xpt1)) ->
  lc_ptyp (ptyp_all A1).
Proof.
intros; ptyp_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_btyp_all_syn_exists :
forall Xbt1 B1,
  lc_btyp (open_btyp_wrt_btyp B1 (btyp_var_f Xbt1)) ->
  lc_btyp (btyp_all_syn B1).
Proof.
intros; btyp_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_btyp_all_inh_exists :
forall Xbt1 B1,
  lc_btyp (open_btyp_wrt_btyp B1 (btyp_var_f Xbt1)) ->
  lc_btyp (btyp_all_inh B1).
Proof.
intros; btyp_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_utyp_all_syn_exists :
forall Xut1 C1,
  lc_utyp (open_utyp_wrt_utyp C1 (utyp_var_f Xut1)) ->
  lc_utyp (utyp_all_syn C1).
Proof.
intros; utyp_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_utyp_all_etag_exists :
forall Xut1 ε1 C1,
  lc_utyp (open_utyp_wrt_utyp C1 (utyp_var_f Xut1)) ->
  lc_utyp (utyp_all_etag ε1 C1).
Proof.
intros; utyp_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_pskel_all_syn_exists :
forall Xps1 P1,
  lc_pskel (open_pskel_wrt_pskel P1 (pskel_var_f Xps1)) ->
  lc_pskel (pskel_all_syn P1).
Proof.
intros; pskel_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_bskel_all_syn_exists :
forall Xbs1 Q1,
  lc_bskel (open_bskel_wrt_bskel Q1 (bskel_var_f Xbs1)) ->
  lc_bskel (bskel_all_syn Q1).
Proof.
intros; bskel_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_bskel_all_inh_exists :
forall Xbs1 Q1,
  lc_bskel (open_bskel_wrt_bskel Q1 (bskel_var_f Xbs1)) ->
  lc_bskel (bskel_all_inh Q1).
Proof.
intros; bskel_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_uskel_all_syn_exists :
forall Xus1 R1,
  lc_uskel (open_uskel_wrt_uskel R1 (uskel_var_f Xus1)) ->
  lc_uskel (uskel_all_syn R1).
Proof.
intros; uskel_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_uskel_all_etag_exists :
forall Xus1 ε1 R1,
  lc_uskel (open_uskel_wrt_uskel R1 (uskel_var_f Xus1)) ->
  lc_uskel (uskel_all_etag ε1 R1).
Proof.
intros; uskel_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_exp_abs_exists :
forall x1 e1,
  lc_exp (open_exp_wrt_exp e1 (exp_var_f x1)) ->
  lc_exp (exp_abs e1).
Proof.
intros; exp_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_exp_abs_anno_exists :
forall x1 A1 e1,
  lc_ptyp A1 ->
  lc_exp (open_exp_wrt_exp e1 (exp_var_f x1)) ->
  lc_exp (exp_abs_anno A1 e1).
Proof.
intros; exp_lc_exists_tac; eauto 6 with lngen.
Qed.

#[export] Hint Extern 1 (lc_ptyp (ptyp_all _)) =>
  let Xpt1 := fresh in
  pick_fresh Xpt1;
  apply (lc_ptyp_all_exists Xpt1) : core.

#[export] Hint Extern 1 (lc_btyp (btyp_all_syn _)) =>
  let Xbt1 := fresh in
  pick_fresh Xbt1;
  apply (lc_btyp_all_syn_exists Xbt1) : core.

#[export] Hint Extern 1 (lc_btyp (btyp_all_inh _)) =>
  let Xbt1 := fresh in
  pick_fresh Xbt1;
  apply (lc_btyp_all_inh_exists Xbt1) : core.

#[export] Hint Extern 1 (lc_utyp (utyp_all_syn _)) =>
  let Xut1 := fresh in
  pick_fresh Xut1;
  apply (lc_utyp_all_syn_exists Xut1) : core.

#[export] Hint Extern 1 (lc_utyp (utyp_all_etag _ _)) =>
  let Xut1 := fresh in
  pick_fresh Xut1;
  apply (lc_utyp_all_etag_exists Xut1) : core.

#[export] Hint Extern 1 (lc_pskel (pskel_all_syn _)) =>
  let Xps1 := fresh in
  pick_fresh Xps1;
  apply (lc_pskel_all_syn_exists Xps1) : core.

#[export] Hint Extern 1 (lc_bskel (bskel_all_syn _)) =>
  let Xbs1 := fresh in
  pick_fresh Xbs1;
  apply (lc_bskel_all_syn_exists Xbs1) : core.

#[export] Hint Extern 1 (lc_bskel (bskel_all_inh _)) =>
  let Xbs1 := fresh in
  pick_fresh Xbs1;
  apply (lc_bskel_all_inh_exists Xbs1) : core.

#[export] Hint Extern 1 (lc_uskel (uskel_all_syn _)) =>
  let Xus1 := fresh in
  pick_fresh Xus1;
  apply (lc_uskel_all_syn_exists Xus1) : core.

#[export] Hint Extern 1 (lc_uskel (uskel_all_etag _ _)) =>
  let Xus1 := fresh in
  pick_fresh Xus1;
  apply (lc_uskel_all_etag_exists Xus1) : core.

#[export] Hint Extern 1 (lc_exp (exp_abs _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_exp_abs_exists x1) : core.

#[export] Hint Extern 1 (lc_exp (exp_abs_anno _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_exp_abs_anno_exists x1) : core.

Lemma lc_body_ptyp_wrt_ptyp :
forall A1 A2,
  body_ptyp_wrt_ptyp A1 ->
  lc_ptyp A2 ->
  lc_ptyp (open_ptyp_wrt_ptyp A1 A2).
Proof.
unfold body_ptyp_wrt_ptyp;
default_simp;
let Xpt1 := fresh "x" in
pick_fresh Xpt1;
specialize_all Xpt1;
ptyp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_ptyp_wrt_ptyp : lngen.

Lemma lc_body_btyp_wrt_btyp :
forall B1 B2,
  body_btyp_wrt_btyp B1 ->
  lc_btyp B2 ->
  lc_btyp (open_btyp_wrt_btyp B1 B2).
Proof.
unfold body_btyp_wrt_btyp;
default_simp;
let Xbt1 := fresh "x" in
pick_fresh Xbt1;
specialize_all Xbt1;
btyp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_btyp_wrt_btyp : lngen.

Lemma lc_body_utyp_wrt_utyp :
forall C1 C2,
  body_utyp_wrt_utyp C1 ->
  lc_utyp C2 ->
  lc_utyp (open_utyp_wrt_utyp C1 C2).
Proof.
unfold body_utyp_wrt_utyp;
default_simp;
let Xut1 := fresh "x" in
pick_fresh Xut1;
specialize_all Xut1;
utyp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_utyp_wrt_utyp : lngen.

Lemma lc_body_pskel_wrt_pskel :
forall P1 P2,
  body_pskel_wrt_pskel P1 ->
  lc_pskel P2 ->
  lc_pskel (open_pskel_wrt_pskel P1 P2).
Proof.
unfold body_pskel_wrt_pskel;
default_simp;
let Xps1 := fresh "x" in
pick_fresh Xps1;
specialize_all Xps1;
pskel_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_pskel_wrt_pskel : lngen.

Lemma lc_body_bskel_wrt_bskel :
forall Q1 Q2,
  body_bskel_wrt_bskel Q1 ->
  lc_bskel Q2 ->
  lc_bskel (open_bskel_wrt_bskel Q1 Q2).
Proof.
unfold body_bskel_wrt_bskel;
default_simp;
let Xbs1 := fresh "x" in
pick_fresh Xbs1;
specialize_all Xbs1;
bskel_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_bskel_wrt_bskel : lngen.

Lemma lc_body_uskel_wrt_uskel :
forall R1 R2,
  body_uskel_wrt_uskel R1 ->
  lc_uskel R2 ->
  lc_uskel (open_uskel_wrt_uskel R1 R2).
Proof.
unfold body_uskel_wrt_uskel;
default_simp;
let Xus1 := fresh "x" in
pick_fresh Xus1;
specialize_all Xus1;
uskel_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_uskel_wrt_uskel : lngen.

Lemma lc_body_exp_wrt_ptyp :
forall e1 A1,
  body_exp_wrt_ptyp e1 ->
  lc_ptyp A1 ->
  lc_exp (open_exp_wrt_ptyp e1 A1).
Proof.
unfold body_exp_wrt_ptyp;
default_simp;
let Xpt1 := fresh "x" in
pick_fresh Xpt1;
specialize_all Xpt1;
exp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_exp_wrt_ptyp : lngen.

Lemma lc_body_exp_wrt_exp :
forall e1 e2,
  body_exp_wrt_exp e1 ->
  lc_exp e2 ->
  lc_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold body_exp_wrt_exp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
exp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_exp_wrt_exp : lngen.

Lemma lc_body_ptyp_all_1 :
forall A1,
  lc_ptyp (ptyp_all A1) ->
  body_ptyp_wrt_ptyp A1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_ptyp_all_1 : lngen.

Lemma lc_body_btyp_all_syn_1 :
forall B1,
  lc_btyp (btyp_all_syn B1) ->
  body_btyp_wrt_btyp B1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_btyp_all_syn_1 : lngen.

Lemma lc_body_btyp_all_inh_1 :
forall B1,
  lc_btyp (btyp_all_inh B1) ->
  body_btyp_wrt_btyp B1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_btyp_all_inh_1 : lngen.

Lemma lc_body_utyp_all_syn_1 :
forall C1,
  lc_utyp (utyp_all_syn C1) ->
  body_utyp_wrt_utyp C1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_utyp_all_syn_1 : lngen.

Lemma lc_body_utyp_all_etag_2 :
forall ε1 C1,
  lc_utyp (utyp_all_etag ε1 C1) ->
  body_utyp_wrt_utyp C1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_utyp_all_etag_2 : lngen.

Lemma lc_body_pskel_all_syn_1 :
forall P1,
  lc_pskel (pskel_all_syn P1) ->
  body_pskel_wrt_pskel P1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_pskel_all_syn_1 : lngen.

Lemma lc_body_bskel_all_syn_1 :
forall Q1,
  lc_bskel (bskel_all_syn Q1) ->
  body_bskel_wrt_bskel Q1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_bskel_all_syn_1 : lngen.

Lemma lc_body_bskel_all_inh_1 :
forall Q1,
  lc_bskel (bskel_all_inh Q1) ->
  body_bskel_wrt_bskel Q1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_bskel_all_inh_1 : lngen.

Lemma lc_body_uskel_all_syn_1 :
forall R1,
  lc_uskel (uskel_all_syn R1) ->
  body_uskel_wrt_uskel R1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_uskel_all_syn_1 : lngen.

Lemma lc_body_uskel_all_etag_2 :
forall ε1 R1,
  lc_uskel (uskel_all_etag ε1 R1) ->
  body_uskel_wrt_uskel R1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_uskel_all_etag_2 : lngen.

Lemma lc_body_exp_abs_1 :
forall e1,
  lc_exp (exp_abs e1) ->
  body_exp_wrt_exp e1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_exp_abs_1 : lngen.

Lemma lc_body_exp_abs_anno_2 :
forall A1 e1,
  lc_exp (exp_abs_anno A1 e1) ->
  body_exp_wrt_exp e1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_exp_abs_anno_2 : lngen.

(* begin hide *)

Lemma lc_ptyp_unique_mutual :
(forall A1 (proof2 proof3 : lc_ptyp A1), proof2 = proof3).
Proof.
apply_mutual_ind lc_ptyp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_ptyp_unique :
forall A1 (proof2 proof3 : lc_ptyp A1), proof2 = proof3.
Proof.
pose proof lc_ptyp_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_ptyp_unique : lngen.

(* begin hide *)

Lemma lc_btyp_unique_mutual :
(forall B1 (proof2 proof3 : lc_btyp B1), proof2 = proof3).
Proof.
apply_mutual_ind lc_btyp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_btyp_unique :
forall B1 (proof2 proof3 : lc_btyp B1), proof2 = proof3.
Proof.
pose proof lc_btyp_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_btyp_unique : lngen.

(* begin hide *)

Lemma lc_utyp_unique_mutual :
(forall C1 (proof2 proof3 : lc_utyp C1), proof2 = proof3).
Proof.
apply_mutual_ind lc_utyp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_utyp_unique :
forall C1 (proof2 proof3 : lc_utyp C1), proof2 = proof3.
Proof.
pose proof lc_utyp_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_utyp_unique : lngen.

(* begin hide *)

Lemma lc_pskel_unique_mutual :
(forall P1 (proof2 proof3 : lc_pskel P1), proof2 = proof3).
Proof.
apply_mutual_ind lc_pskel_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_pskel_unique :
forall P1 (proof2 proof3 : lc_pskel P1), proof2 = proof3.
Proof.
pose proof lc_pskel_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_pskel_unique : lngen.

(* begin hide *)

Lemma lc_bskel_unique_mutual :
(forall Q1 (proof2 proof3 : lc_bskel Q1), proof2 = proof3).
Proof.
apply_mutual_ind lc_bskel_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_bskel_unique :
forall Q1 (proof2 proof3 : lc_bskel Q1), proof2 = proof3.
Proof.
pose proof lc_bskel_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_bskel_unique : lngen.

(* begin hide *)

Lemma lc_uskel_unique_mutual :
(forall R1 (proof2 proof3 : lc_uskel R1), proof2 = proof3).
Proof.
apply_mutual_ind lc_uskel_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_uskel_unique :
forall R1 (proof2 proof3 : lc_uskel R1), proof2 = proof3.
Proof.
pose proof lc_uskel_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_uskel_unique : lngen.

(* begin hide *)

Lemma lc_exp_unique_mutual :
(forall e1 (proof2 proof3 : lc_exp e1), proof2 = proof3).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_exp_unique :
forall e1 (proof2 proof3 : lc_exp e1), proof2 = proof3.
Proof.
pose proof lc_exp_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_exp_unique : lngen.

(* begin hide *)

Lemma lc_ptyp_of_lc_set_ptyp_mutual :
(forall A1, lc_set_ptyp A1 -> lc_ptyp A1).
Proof.
apply_mutual_ind lc_set_ptyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_ptyp_of_lc_set_ptyp :
forall A1, lc_set_ptyp A1 -> lc_ptyp A1.
Proof.
pose proof lc_ptyp_of_lc_set_ptyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_ptyp_of_lc_set_ptyp : lngen.

(* begin hide *)

Lemma lc_btyp_of_lc_set_btyp_mutual :
(forall B1, lc_set_btyp B1 -> lc_btyp B1).
Proof.
apply_mutual_ind lc_set_btyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_btyp_of_lc_set_btyp :
forall B1, lc_set_btyp B1 -> lc_btyp B1.
Proof.
pose proof lc_btyp_of_lc_set_btyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_btyp_of_lc_set_btyp : lngen.

(* begin hide *)

Lemma lc_utyp_of_lc_set_utyp_mutual :
(forall C1, lc_set_utyp C1 -> lc_utyp C1).
Proof.
apply_mutual_ind lc_set_utyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_utyp_of_lc_set_utyp :
forall C1, lc_set_utyp C1 -> lc_utyp C1.
Proof.
pose proof lc_utyp_of_lc_set_utyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_utyp_of_lc_set_utyp : lngen.

(* begin hide *)

Lemma lc_pskel_of_lc_set_pskel_mutual :
(forall P1, lc_set_pskel P1 -> lc_pskel P1).
Proof.
apply_mutual_ind lc_set_pskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_pskel_of_lc_set_pskel :
forall P1, lc_set_pskel P1 -> lc_pskel P1.
Proof.
pose proof lc_pskel_of_lc_set_pskel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_pskel_of_lc_set_pskel : lngen.

(* begin hide *)

Lemma lc_bskel_of_lc_set_bskel_mutual :
(forall Q1, lc_set_bskel Q1 -> lc_bskel Q1).
Proof.
apply_mutual_ind lc_set_bskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_bskel_of_lc_set_bskel :
forall Q1, lc_set_bskel Q1 -> lc_bskel Q1.
Proof.
pose proof lc_bskel_of_lc_set_bskel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_bskel_of_lc_set_bskel : lngen.

(* begin hide *)

Lemma lc_uskel_of_lc_set_uskel_mutual :
(forall R1, lc_set_uskel R1 -> lc_uskel R1).
Proof.
apply_mutual_ind lc_set_uskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_uskel_of_lc_set_uskel :
forall R1, lc_set_uskel R1 -> lc_uskel R1.
Proof.
pose proof lc_uskel_of_lc_set_uskel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_uskel_of_lc_set_uskel : lngen.

(* begin hide *)

Lemma lc_exp_of_lc_set_exp_mutual :
(forall e1, lc_set_exp e1 -> lc_exp e1).
Proof.
apply_mutual_ind lc_set_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_exp_of_lc_set_exp :
forall e1, lc_set_exp e1 -> lc_exp e1.
Proof.
pose proof lc_exp_of_lc_set_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_exp_of_lc_set_exp : lngen.

(* begin hide *)

Lemma lc_set_ptyp_of_lc_ptyp_size_mutual :
forall i1,
(forall A1,
  size_ptyp A1 = i1 ->
  lc_ptyp A1 ->
  lc_set_ptyp A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind ptyp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_ptyp_of_lc_ptyp];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_ptyp_of_lc_ptyp :
forall A1,
  lc_ptyp A1 ->
  lc_set_ptyp A1.
Proof.
intros A1; intros;
pose proof (lc_set_ptyp_of_lc_ptyp_size_mutual (size_ptyp A1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_ptyp_of_lc_ptyp : lngen.

(* begin hide *)

Lemma lc_set_btyp_of_lc_btyp_size_mutual :
forall i1,
(forall B1,
  size_btyp B1 = i1 ->
  lc_btyp B1 ->
  lc_set_btyp B1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind btyp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_btyp_of_lc_btyp];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_btyp_of_lc_btyp :
forall B1,
  lc_btyp B1 ->
  lc_set_btyp B1.
Proof.
intros B1; intros;
pose proof (lc_set_btyp_of_lc_btyp_size_mutual (size_btyp B1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_btyp_of_lc_btyp : lngen.

(* begin hide *)

Lemma lc_set_utyp_of_lc_utyp_size_mutual :
forall i1,
(forall C1,
  size_utyp C1 = i1 ->
  lc_utyp C1 ->
  lc_set_utyp C1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind utyp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_utyp_of_lc_utyp];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_utyp_of_lc_utyp :
forall C1,
  lc_utyp C1 ->
  lc_set_utyp C1.
Proof.
intros C1; intros;
pose proof (lc_set_utyp_of_lc_utyp_size_mutual (size_utyp C1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_utyp_of_lc_utyp : lngen.

(* begin hide *)

Lemma lc_set_pskel_of_lc_pskel_size_mutual :
forall i1,
(forall P1,
  size_pskel P1 = i1 ->
  lc_pskel P1 ->
  lc_set_pskel P1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind pskel_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_pskel_of_lc_pskel];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_pskel_of_lc_pskel :
forall P1,
  lc_pskel P1 ->
  lc_set_pskel P1.
Proof.
intros P1; intros;
pose proof (lc_set_pskel_of_lc_pskel_size_mutual (size_pskel P1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_pskel_of_lc_pskel : lngen.

(* begin hide *)

Lemma lc_set_bskel_of_lc_bskel_size_mutual :
forall i1,
(forall Q1,
  size_bskel Q1 = i1 ->
  lc_bskel Q1 ->
  lc_set_bskel Q1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind bskel_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_bskel_of_lc_bskel];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_bskel_of_lc_bskel :
forall Q1,
  lc_bskel Q1 ->
  lc_set_bskel Q1.
Proof.
intros Q1; intros;
pose proof (lc_set_bskel_of_lc_bskel_size_mutual (size_bskel Q1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_bskel_of_lc_bskel : lngen.

(* begin hide *)

Lemma lc_set_uskel_of_lc_uskel_size_mutual :
forall i1,
(forall R1,
  size_uskel R1 = i1 ->
  lc_uskel R1 ->
  lc_set_uskel R1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind uskel_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_uskel_of_lc_uskel];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_uskel_of_lc_uskel :
forall R1,
  lc_uskel R1 ->
  lc_set_uskel R1.
Proof.
intros R1; intros;
pose proof (lc_set_uskel_of_lc_uskel_size_mutual (size_uskel R1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_uskel_of_lc_uskel : lngen.

(* begin hide *)

Lemma lc_set_exp_of_lc_exp_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  lc_exp e1 ->
  lc_set_exp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind exp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_ptyp_of_lc_ptyp
 | apply lc_set_exp_of_lc_exp];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_exp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  lc_set_exp e1.
Proof.
intros e1; intros;
pose proof (lc_set_exp_of_lc_exp_size_mutual (size_exp e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_exp_of_lc_exp : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_ptyp_wrt_ptyp_rec_degree_ptyp_wrt_ptyp_mutual :
(forall A1 Xpt1 n1,
  degree_ptyp_wrt_ptyp n1 A1 ->
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  close_ptyp_wrt_ptyp_rec n1 Xpt1 A1 = A1).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_ptyp_wrt_ptyp_rec_degree_ptyp_wrt_ptyp :
forall A1 Xpt1 n1,
  degree_ptyp_wrt_ptyp n1 A1 ->
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  close_ptyp_wrt_ptyp_rec n1 Xpt1 A1 = A1.
Proof.
pose proof close_ptyp_wrt_ptyp_rec_degree_ptyp_wrt_ptyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_ptyp_wrt_ptyp_rec_degree_ptyp_wrt_ptyp : lngen.
#[export] Hint Rewrite close_ptyp_wrt_ptyp_rec_degree_ptyp_wrt_ptyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_btyp_wrt_btyp_rec_degree_btyp_wrt_btyp_mutual :
(forall B1 Xbt1 n1,
  degree_btyp_wrt_btyp n1 B1 ->
  Xbt1 `notin` ftvar_in_btyp B1 ->
  close_btyp_wrt_btyp_rec n1 Xbt1 B1 = B1).
Proof.
apply_mutual_ind btyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_btyp_wrt_btyp_rec_degree_btyp_wrt_btyp :
forall B1 Xbt1 n1,
  degree_btyp_wrt_btyp n1 B1 ->
  Xbt1 `notin` ftvar_in_btyp B1 ->
  close_btyp_wrt_btyp_rec n1 Xbt1 B1 = B1.
Proof.
pose proof close_btyp_wrt_btyp_rec_degree_btyp_wrt_btyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_btyp_wrt_btyp_rec_degree_btyp_wrt_btyp : lngen.
#[export] Hint Rewrite close_btyp_wrt_btyp_rec_degree_btyp_wrt_btyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_utyp_wrt_utyp_rec_degree_utyp_wrt_utyp_mutual :
(forall C1 Xut1 n1,
  degree_utyp_wrt_utyp n1 C1 ->
  Xut1 `notin` ftvar_in_utyp C1 ->
  close_utyp_wrt_utyp_rec n1 Xut1 C1 = C1).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_utyp_wrt_utyp_rec_degree_utyp_wrt_utyp :
forall C1 Xut1 n1,
  degree_utyp_wrt_utyp n1 C1 ->
  Xut1 `notin` ftvar_in_utyp C1 ->
  close_utyp_wrt_utyp_rec n1 Xut1 C1 = C1.
Proof.
pose proof close_utyp_wrt_utyp_rec_degree_utyp_wrt_utyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_utyp_wrt_utyp_rec_degree_utyp_wrt_utyp : lngen.
#[export] Hint Rewrite close_utyp_wrt_utyp_rec_degree_utyp_wrt_utyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_pskel_wrt_pskel_rec_degree_pskel_wrt_pskel_mutual :
(forall P1 Xps1 n1,
  degree_pskel_wrt_pskel n1 P1 ->
  Xps1 `notin` ftvar_in_pskel P1 ->
  close_pskel_wrt_pskel_rec n1 Xps1 P1 = P1).
Proof.
apply_mutual_ind pskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_pskel_wrt_pskel_rec_degree_pskel_wrt_pskel :
forall P1 Xps1 n1,
  degree_pskel_wrt_pskel n1 P1 ->
  Xps1 `notin` ftvar_in_pskel P1 ->
  close_pskel_wrt_pskel_rec n1 Xps1 P1 = P1.
Proof.
pose proof close_pskel_wrt_pskel_rec_degree_pskel_wrt_pskel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_pskel_wrt_pskel_rec_degree_pskel_wrt_pskel : lngen.
#[export] Hint Rewrite close_pskel_wrt_pskel_rec_degree_pskel_wrt_pskel using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_bskel_wrt_bskel_rec_degree_bskel_wrt_bskel_mutual :
(forall Q1 Xbs1 n1,
  degree_bskel_wrt_bskel n1 Q1 ->
  Xbs1 `notin` ftvar_in_bskel Q1 ->
  close_bskel_wrt_bskel_rec n1 Xbs1 Q1 = Q1).
Proof.
apply_mutual_ind bskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_bskel_wrt_bskel_rec_degree_bskel_wrt_bskel :
forall Q1 Xbs1 n1,
  degree_bskel_wrt_bskel n1 Q1 ->
  Xbs1 `notin` ftvar_in_bskel Q1 ->
  close_bskel_wrt_bskel_rec n1 Xbs1 Q1 = Q1.
Proof.
pose proof close_bskel_wrt_bskel_rec_degree_bskel_wrt_bskel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_bskel_wrt_bskel_rec_degree_bskel_wrt_bskel : lngen.
#[export] Hint Rewrite close_bskel_wrt_bskel_rec_degree_bskel_wrt_bskel using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_uskel_wrt_uskel_rec_degree_uskel_wrt_uskel_mutual :
(forall R1 Xus1 n1,
  degree_uskel_wrt_uskel n1 R1 ->
  Xus1 `notin` ftvar_in_uskel R1 ->
  close_uskel_wrt_uskel_rec n1 Xus1 R1 = R1).
Proof.
apply_mutual_ind uskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_uskel_wrt_uskel_rec_degree_uskel_wrt_uskel :
forall R1 Xus1 n1,
  degree_uskel_wrt_uskel n1 R1 ->
  Xus1 `notin` ftvar_in_uskel R1 ->
  close_uskel_wrt_uskel_rec n1 Xus1 R1 = R1.
Proof.
pose proof close_uskel_wrt_uskel_rec_degree_uskel_wrt_uskel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_uskel_wrt_uskel_rec_degree_uskel_wrt_uskel : lngen.
#[export] Hint Rewrite close_uskel_wrt_uskel_rec_degree_uskel_wrt_uskel using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_ptyp_rec_degree_exp_wrt_ptyp_mutual :
(forall e1 Xpt1 n1,
  degree_exp_wrt_ptyp n1 e1 ->
  Xpt1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_ptyp_rec n1 Xpt1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_ptyp_rec_degree_exp_wrt_ptyp :
forall e1 Xpt1 n1,
  degree_exp_wrt_ptyp n1 e1 ->
  Xpt1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_ptyp_rec n1 Xpt1 e1 = e1.
Proof.
pose proof close_exp_wrt_ptyp_rec_degree_exp_wrt_ptyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_exp_wrt_ptyp_rec_degree_exp_wrt_ptyp : lngen.
#[export] Hint Rewrite close_exp_wrt_ptyp_rec_degree_exp_wrt_ptyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` fvar_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` fvar_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1.
Proof.
pose proof close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

Lemma close_ptyp_wrt_ptyp_lc_ptyp :
forall A1 Xpt1,
  lc_ptyp A1 ->
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  close_ptyp_wrt_ptyp Xpt1 A1 = A1.
Proof.
unfold close_ptyp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve close_ptyp_wrt_ptyp_lc_ptyp : lngen.
#[export] Hint Rewrite close_ptyp_wrt_ptyp_lc_ptyp using solve [auto] : lngen.

Lemma close_btyp_wrt_btyp_lc_btyp :
forall B1 Xbt1,
  lc_btyp B1 ->
  Xbt1 `notin` ftvar_in_btyp B1 ->
  close_btyp_wrt_btyp Xbt1 B1 = B1.
Proof.
unfold close_btyp_wrt_btyp; default_simp.
Qed.

#[export] Hint Resolve close_btyp_wrt_btyp_lc_btyp : lngen.
#[export] Hint Rewrite close_btyp_wrt_btyp_lc_btyp using solve [auto] : lngen.

Lemma close_utyp_wrt_utyp_lc_utyp :
forall C1 Xut1,
  lc_utyp C1 ->
  Xut1 `notin` ftvar_in_utyp C1 ->
  close_utyp_wrt_utyp Xut1 C1 = C1.
Proof.
unfold close_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve close_utyp_wrt_utyp_lc_utyp : lngen.
#[export] Hint Rewrite close_utyp_wrt_utyp_lc_utyp using solve [auto] : lngen.

Lemma close_pskel_wrt_pskel_lc_pskel :
forall P1 Xps1,
  lc_pskel P1 ->
  Xps1 `notin` ftvar_in_pskel P1 ->
  close_pskel_wrt_pskel Xps1 P1 = P1.
Proof.
unfold close_pskel_wrt_pskel; default_simp.
Qed.

#[export] Hint Resolve close_pskel_wrt_pskel_lc_pskel : lngen.
#[export] Hint Rewrite close_pskel_wrt_pskel_lc_pskel using solve [auto] : lngen.

Lemma close_bskel_wrt_bskel_lc_bskel :
forall Q1 Xbs1,
  lc_bskel Q1 ->
  Xbs1 `notin` ftvar_in_bskel Q1 ->
  close_bskel_wrt_bskel Xbs1 Q1 = Q1.
Proof.
unfold close_bskel_wrt_bskel; default_simp.
Qed.

#[export] Hint Resolve close_bskel_wrt_bskel_lc_bskel : lngen.
#[export] Hint Rewrite close_bskel_wrt_bskel_lc_bskel using solve [auto] : lngen.

Lemma close_uskel_wrt_uskel_lc_uskel :
forall R1 Xus1,
  lc_uskel R1 ->
  Xus1 `notin` ftvar_in_uskel R1 ->
  close_uskel_wrt_uskel Xus1 R1 = R1.
Proof.
unfold close_uskel_wrt_uskel; default_simp.
Qed.

#[export] Hint Resolve close_uskel_wrt_uskel_lc_uskel : lngen.
#[export] Hint Rewrite close_uskel_wrt_uskel_lc_uskel using solve [auto] : lngen.

Lemma close_exp_wrt_ptyp_lc_exp :
forall e1 Xpt1,
  lc_exp e1 ->
  Xpt1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_ptyp Xpt1 e1 = e1.
Proof.
unfold close_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve close_exp_wrt_ptyp_lc_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_ptyp_lc_exp using solve [auto] : lngen.

Lemma close_exp_wrt_exp_lc_exp :
forall e1 x1,
  lc_exp e1 ->
  x1 `notin` fvar_in_exp e1 ->
  close_exp_wrt_exp x1 e1 = e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve close_exp_wrt_exp_lc_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_lc_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_ptyp_wrt_ptyp_rec_degree_ptyp_wrt_ptyp_mutual :
(forall A2 A1 n1,
  degree_ptyp_wrt_ptyp n1 A2 ->
  open_ptyp_wrt_ptyp_rec n1 A1 A2 = A2).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_ptyp_wrt_ptyp_rec_degree_ptyp_wrt_ptyp :
forall A2 A1 n1,
  degree_ptyp_wrt_ptyp n1 A2 ->
  open_ptyp_wrt_ptyp_rec n1 A1 A2 = A2.
Proof.
pose proof open_ptyp_wrt_ptyp_rec_degree_ptyp_wrt_ptyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_ptyp_wrt_ptyp_rec_degree_ptyp_wrt_ptyp : lngen.
#[export] Hint Rewrite open_ptyp_wrt_ptyp_rec_degree_ptyp_wrt_ptyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_btyp_wrt_btyp_rec_degree_btyp_wrt_btyp_mutual :
(forall B2 B1 n1,
  degree_btyp_wrt_btyp n1 B2 ->
  open_btyp_wrt_btyp_rec n1 B1 B2 = B2).
Proof.
apply_mutual_ind btyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_btyp_wrt_btyp_rec_degree_btyp_wrt_btyp :
forall B2 B1 n1,
  degree_btyp_wrt_btyp n1 B2 ->
  open_btyp_wrt_btyp_rec n1 B1 B2 = B2.
Proof.
pose proof open_btyp_wrt_btyp_rec_degree_btyp_wrt_btyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_btyp_wrt_btyp_rec_degree_btyp_wrt_btyp : lngen.
#[export] Hint Rewrite open_btyp_wrt_btyp_rec_degree_btyp_wrt_btyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_utyp_wrt_utyp_rec_degree_utyp_wrt_utyp_mutual :
(forall C2 C1 n1,
  degree_utyp_wrt_utyp n1 C2 ->
  open_utyp_wrt_utyp_rec n1 C1 C2 = C2).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_utyp_wrt_utyp_rec_degree_utyp_wrt_utyp :
forall C2 C1 n1,
  degree_utyp_wrt_utyp n1 C2 ->
  open_utyp_wrt_utyp_rec n1 C1 C2 = C2.
Proof.
pose proof open_utyp_wrt_utyp_rec_degree_utyp_wrt_utyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_utyp_wrt_utyp_rec_degree_utyp_wrt_utyp : lngen.
#[export] Hint Rewrite open_utyp_wrt_utyp_rec_degree_utyp_wrt_utyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_pskel_wrt_pskel_rec_degree_pskel_wrt_pskel_mutual :
(forall P2 P1 n1,
  degree_pskel_wrt_pskel n1 P2 ->
  open_pskel_wrt_pskel_rec n1 P1 P2 = P2).
Proof.
apply_mutual_ind pskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_pskel_wrt_pskel_rec_degree_pskel_wrt_pskel :
forall P2 P1 n1,
  degree_pskel_wrt_pskel n1 P2 ->
  open_pskel_wrt_pskel_rec n1 P1 P2 = P2.
Proof.
pose proof open_pskel_wrt_pskel_rec_degree_pskel_wrt_pskel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_pskel_wrt_pskel_rec_degree_pskel_wrt_pskel : lngen.
#[export] Hint Rewrite open_pskel_wrt_pskel_rec_degree_pskel_wrt_pskel using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_bskel_wrt_bskel_rec_degree_bskel_wrt_bskel_mutual :
(forall Q2 Q1 n1,
  degree_bskel_wrt_bskel n1 Q2 ->
  open_bskel_wrt_bskel_rec n1 Q1 Q2 = Q2).
Proof.
apply_mutual_ind bskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_bskel_wrt_bskel_rec_degree_bskel_wrt_bskel :
forall Q2 Q1 n1,
  degree_bskel_wrt_bskel n1 Q2 ->
  open_bskel_wrt_bskel_rec n1 Q1 Q2 = Q2.
Proof.
pose proof open_bskel_wrt_bskel_rec_degree_bskel_wrt_bskel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_bskel_wrt_bskel_rec_degree_bskel_wrt_bskel : lngen.
#[export] Hint Rewrite open_bskel_wrt_bskel_rec_degree_bskel_wrt_bskel using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_uskel_wrt_uskel_rec_degree_uskel_wrt_uskel_mutual :
(forall R2 R1 n1,
  degree_uskel_wrt_uskel n1 R2 ->
  open_uskel_wrt_uskel_rec n1 R1 R2 = R2).
Proof.
apply_mutual_ind uskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_uskel_wrt_uskel_rec_degree_uskel_wrt_uskel :
forall R2 R1 n1,
  degree_uskel_wrt_uskel n1 R2 ->
  open_uskel_wrt_uskel_rec n1 R1 R2 = R2.
Proof.
pose proof open_uskel_wrt_uskel_rec_degree_uskel_wrt_uskel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_uskel_wrt_uskel_rec_degree_uskel_wrt_uskel : lngen.
#[export] Hint Rewrite open_uskel_wrt_uskel_rec_degree_uskel_wrt_uskel using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_ptyp_rec_degree_exp_wrt_ptyp_mutual :
(forall e1 A1 n1,
  degree_exp_wrt_ptyp n1 e1 ->
  open_exp_wrt_ptyp_rec n1 A1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_ptyp_rec_degree_exp_wrt_ptyp :
forall e1 A1 n1,
  degree_exp_wrt_ptyp n1 e1 ->
  open_exp_wrt_ptyp_rec n1 A1 e1 = e1.
Proof.
pose proof open_exp_wrt_ptyp_rec_degree_exp_wrt_ptyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_exp_wrt_ptyp_rec_degree_exp_wrt_ptyp : lngen.
#[export] Hint Rewrite open_exp_wrt_ptyp_rec_degree_exp_wrt_ptyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual :
(forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_exp_wrt_exp_rec n1 e1 e2 = e2).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_exp_wrt_exp_rec n1 e1 e2 = e2.
Proof.
pose proof open_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

Lemma open_ptyp_wrt_ptyp_lc_ptyp :
forall A2 A1,
  lc_ptyp A2 ->
  open_ptyp_wrt_ptyp A2 A1 = A2.
Proof.
unfold open_ptyp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve open_ptyp_wrt_ptyp_lc_ptyp : lngen.
#[export] Hint Rewrite open_ptyp_wrt_ptyp_lc_ptyp using solve [auto] : lngen.

Lemma open_btyp_wrt_btyp_lc_btyp :
forall B2 B1,
  lc_btyp B2 ->
  open_btyp_wrt_btyp B2 B1 = B2.
Proof.
unfold open_btyp_wrt_btyp; default_simp.
Qed.

#[export] Hint Resolve open_btyp_wrt_btyp_lc_btyp : lngen.
#[export] Hint Rewrite open_btyp_wrt_btyp_lc_btyp using solve [auto] : lngen.

Lemma open_utyp_wrt_utyp_lc_utyp :
forall C2 C1,
  lc_utyp C2 ->
  open_utyp_wrt_utyp C2 C1 = C2.
Proof.
unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve open_utyp_wrt_utyp_lc_utyp : lngen.
#[export] Hint Rewrite open_utyp_wrt_utyp_lc_utyp using solve [auto] : lngen.

Lemma open_pskel_wrt_pskel_lc_pskel :
forall P2 P1,
  lc_pskel P2 ->
  open_pskel_wrt_pskel P2 P1 = P2.
Proof.
unfold open_pskel_wrt_pskel; default_simp.
Qed.

#[export] Hint Resolve open_pskel_wrt_pskel_lc_pskel : lngen.
#[export] Hint Rewrite open_pskel_wrt_pskel_lc_pskel using solve [auto] : lngen.

Lemma open_bskel_wrt_bskel_lc_bskel :
forall Q2 Q1,
  lc_bskel Q2 ->
  open_bskel_wrt_bskel Q2 Q1 = Q2.
Proof.
unfold open_bskel_wrt_bskel; default_simp.
Qed.

#[export] Hint Resolve open_bskel_wrt_bskel_lc_bskel : lngen.
#[export] Hint Rewrite open_bskel_wrt_bskel_lc_bskel using solve [auto] : lngen.

Lemma open_uskel_wrt_uskel_lc_uskel :
forall R2 R1,
  lc_uskel R2 ->
  open_uskel_wrt_uskel R2 R1 = R2.
Proof.
unfold open_uskel_wrt_uskel; default_simp.
Qed.

#[export] Hint Resolve open_uskel_wrt_uskel_lc_uskel : lngen.
#[export] Hint Rewrite open_uskel_wrt_uskel_lc_uskel using solve [auto] : lngen.

Lemma open_exp_wrt_ptyp_lc_exp :
forall e1 A1,
  lc_exp e1 ->
  open_exp_wrt_ptyp e1 A1 = e1.
Proof.
unfold open_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_ptyp_lc_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_ptyp_lc_exp using solve [auto] : lngen.

Lemma open_exp_wrt_exp_lc_exp :
forall e2 e1,
  lc_exp e2 ->
  open_exp_wrt_exp e2 e1 = e2.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_exp_lc_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_lc_exp using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma ftvar_in_ptyp_close_ptyp_wrt_ptyp_rec_mutual :
(forall A1 Xpt1 n1,
  ftvar_in_ptyp (close_ptyp_wrt_ptyp_rec n1 Xpt1 A1) [=] remove Xpt1 (ftvar_in_ptyp A1)).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_ptyp_close_ptyp_wrt_ptyp_rec :
forall A1 Xpt1 n1,
  ftvar_in_ptyp (close_ptyp_wrt_ptyp_rec n1 Xpt1 A1) [=] remove Xpt1 (ftvar_in_ptyp A1).
Proof.
pose proof ftvar_in_ptyp_close_ptyp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_ptyp_close_ptyp_wrt_ptyp_rec : lngen.
#[export] Hint Rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_btyp_close_btyp_wrt_btyp_rec_mutual :
(forall B1 Xbt1 n1,
  ftvar_in_btyp (close_btyp_wrt_btyp_rec n1 Xbt1 B1) [=] remove Xbt1 (ftvar_in_btyp B1)).
Proof.
apply_mutual_ind btyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_btyp_close_btyp_wrt_btyp_rec :
forall B1 Xbt1 n1,
  ftvar_in_btyp (close_btyp_wrt_btyp_rec n1 Xbt1 B1) [=] remove Xbt1 (ftvar_in_btyp B1).
Proof.
pose proof ftvar_in_btyp_close_btyp_wrt_btyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_btyp_close_btyp_wrt_btyp_rec : lngen.
#[export] Hint Rewrite ftvar_in_btyp_close_btyp_wrt_btyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_utyp_close_utyp_wrt_utyp_rec_mutual :
(forall C1 Xut1 n1,
  ftvar_in_utyp (close_utyp_wrt_utyp_rec n1 Xut1 C1) [=] remove Xut1 (ftvar_in_utyp C1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_utyp_close_utyp_wrt_utyp_rec :
forall C1 Xut1 n1,
  ftvar_in_utyp (close_utyp_wrt_utyp_rec n1 Xut1 C1) [=] remove Xut1 (ftvar_in_utyp C1).
Proof.
pose proof ftvar_in_utyp_close_utyp_wrt_utyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_utyp_close_utyp_wrt_utyp_rec : lngen.
#[export] Hint Rewrite ftvar_in_utyp_close_utyp_wrt_utyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_pskel_close_pskel_wrt_pskel_rec_mutual :
(forall P1 Xps1 n1,
  ftvar_in_pskel (close_pskel_wrt_pskel_rec n1 Xps1 P1) [=] remove Xps1 (ftvar_in_pskel P1)).
Proof.
apply_mutual_ind pskel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_pskel_close_pskel_wrt_pskel_rec :
forall P1 Xps1 n1,
  ftvar_in_pskel (close_pskel_wrt_pskel_rec n1 Xps1 P1) [=] remove Xps1 (ftvar_in_pskel P1).
Proof.
pose proof ftvar_in_pskel_close_pskel_wrt_pskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_pskel_close_pskel_wrt_pskel_rec : lngen.
#[export] Hint Rewrite ftvar_in_pskel_close_pskel_wrt_pskel_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bskel_close_bskel_wrt_bskel_rec_mutual :
(forall Q1 Xbs1 n1,
  ftvar_in_bskel (close_bskel_wrt_bskel_rec n1 Xbs1 Q1) [=] remove Xbs1 (ftvar_in_bskel Q1)).
Proof.
apply_mutual_ind bskel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bskel_close_bskel_wrt_bskel_rec :
forall Q1 Xbs1 n1,
  ftvar_in_bskel (close_bskel_wrt_bskel_rec n1 Xbs1 Q1) [=] remove Xbs1 (ftvar_in_bskel Q1).
Proof.
pose proof ftvar_in_bskel_close_bskel_wrt_bskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bskel_close_bskel_wrt_bskel_rec : lngen.
#[export] Hint Rewrite ftvar_in_bskel_close_bskel_wrt_bskel_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_uskel_close_uskel_wrt_uskel_rec_mutual :
(forall R1 Xus1 n1,
  ftvar_in_uskel (close_uskel_wrt_uskel_rec n1 Xus1 R1) [=] remove Xus1 (ftvar_in_uskel R1)).
Proof.
apply_mutual_ind uskel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_uskel_close_uskel_wrt_uskel_rec :
forall R1 Xus1 n1,
  ftvar_in_uskel (close_uskel_wrt_uskel_rec n1 Xus1 R1) [=] remove Xus1 (ftvar_in_uskel R1).
Proof.
pose proof ftvar_in_uskel_close_uskel_wrt_uskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_uskel_close_uskel_wrt_uskel_rec : lngen.
#[export] Hint Rewrite ftvar_in_uskel_close_uskel_wrt_uskel_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_close_exp_wrt_ptyp_rec_mutual :
(forall e1 Xpt1 n1,
  ftvar_in_exp (close_exp_wrt_ptyp_rec n1 Xpt1 e1) [=] remove Xpt1 (ftvar_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_close_exp_wrt_ptyp_rec :
forall e1 Xpt1 n1,
  ftvar_in_exp (close_exp_wrt_ptyp_rec n1 Xpt1 e1) [=] remove Xpt1 (ftvar_in_exp e1).
Proof.
pose proof ftvar_in_exp_close_exp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_close_exp_wrt_ptyp_rec : lngen.
#[export] Hint Rewrite ftvar_in_exp_close_exp_wrt_ptyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  ftvar_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] ftvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  ftvar_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] ftvar_in_exp e1.
Proof.
pose proof ftvar_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_close_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite ftvar_in_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_close_exp_wrt_ptyp_rec_mutual :
(forall e1 Xpt1 n1,
  fvar_in_exp (close_exp_wrt_ptyp_rec n1 Xpt1 e1) [=] fvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_close_exp_wrt_ptyp_rec :
forall e1 Xpt1 n1,
  fvar_in_exp (close_exp_wrt_ptyp_rec n1 Xpt1 e1) [=] fvar_in_exp e1.
Proof.
pose proof fvar_in_exp_close_exp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_close_exp_wrt_ptyp_rec : lngen.
#[export] Hint Rewrite fvar_in_exp_close_exp_wrt_ptyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  fvar_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (fvar_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  fvar_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (fvar_in_exp e1).
Proof.
pose proof fvar_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_close_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite fvar_in_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma ftvar_in_ptyp_close_ptyp_wrt_ptyp :
forall A1 Xpt1,
  ftvar_in_ptyp (close_ptyp_wrt_ptyp Xpt1 A1) [=] remove Xpt1 (ftvar_in_ptyp A1).
Proof.
unfold close_ptyp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_ptyp_close_ptyp_wrt_ptyp : lngen.
#[export] Hint Rewrite ftvar_in_ptyp_close_ptyp_wrt_ptyp using solve [auto] : lngen.

Lemma ftvar_in_btyp_close_btyp_wrt_btyp :
forall B1 Xbt1,
  ftvar_in_btyp (close_btyp_wrt_btyp Xbt1 B1) [=] remove Xbt1 (ftvar_in_btyp B1).
Proof.
unfold close_btyp_wrt_btyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_btyp_close_btyp_wrt_btyp : lngen.
#[export] Hint Rewrite ftvar_in_btyp_close_btyp_wrt_btyp using solve [auto] : lngen.

Lemma ftvar_in_utyp_close_utyp_wrt_utyp :
forall C1 Xut1,
  ftvar_in_utyp (close_utyp_wrt_utyp Xut1 C1) [=] remove Xut1 (ftvar_in_utyp C1).
Proof.
unfold close_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_utyp_close_utyp_wrt_utyp : lngen.
#[export] Hint Rewrite ftvar_in_utyp_close_utyp_wrt_utyp using solve [auto] : lngen.

Lemma ftvar_in_pskel_close_pskel_wrt_pskel :
forall P1 Xps1,
  ftvar_in_pskel (close_pskel_wrt_pskel Xps1 P1) [=] remove Xps1 (ftvar_in_pskel P1).
Proof.
unfold close_pskel_wrt_pskel; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_pskel_close_pskel_wrt_pskel : lngen.
#[export] Hint Rewrite ftvar_in_pskel_close_pskel_wrt_pskel using solve [auto] : lngen.

Lemma ftvar_in_bskel_close_bskel_wrt_bskel :
forall Q1 Xbs1,
  ftvar_in_bskel (close_bskel_wrt_bskel Xbs1 Q1) [=] remove Xbs1 (ftvar_in_bskel Q1).
Proof.
unfold close_bskel_wrt_bskel; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_bskel_close_bskel_wrt_bskel : lngen.
#[export] Hint Rewrite ftvar_in_bskel_close_bskel_wrt_bskel using solve [auto] : lngen.

Lemma ftvar_in_uskel_close_uskel_wrt_uskel :
forall R1 Xus1,
  ftvar_in_uskel (close_uskel_wrt_uskel Xus1 R1) [=] remove Xus1 (ftvar_in_uskel R1).
Proof.
unfold close_uskel_wrt_uskel; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_uskel_close_uskel_wrt_uskel : lngen.
#[export] Hint Rewrite ftvar_in_uskel_close_uskel_wrt_uskel using solve [auto] : lngen.

Lemma ftvar_in_exp_close_exp_wrt_ptyp :
forall e1 Xpt1,
  ftvar_in_exp (close_exp_wrt_ptyp Xpt1 e1) [=] remove Xpt1 (ftvar_in_exp e1).
Proof.
unfold close_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_close_exp_wrt_ptyp : lngen.
#[export] Hint Rewrite ftvar_in_exp_close_exp_wrt_ptyp using solve [auto] : lngen.

Lemma ftvar_in_exp_close_exp_wrt_exp :
forall e1 x1,
  ftvar_in_exp (close_exp_wrt_exp x1 e1) [=] ftvar_in_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite ftvar_in_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma fvar_in_exp_close_exp_wrt_ptyp :
forall e1 Xpt1,
  fvar_in_exp (close_exp_wrt_ptyp Xpt1 e1) [=] fvar_in_exp e1.
Proof.
unfold close_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_close_exp_wrt_ptyp : lngen.
#[export] Hint Rewrite fvar_in_exp_close_exp_wrt_ptyp using solve [auto] : lngen.

Lemma fvar_in_exp_close_exp_wrt_exp :
forall e1 x1,
  fvar_in_exp (close_exp_wrt_exp x1 e1) [=] remove x1 (fvar_in_exp e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite fvar_in_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_ptyp_open_ptyp_wrt_ptyp_rec_lower_mutual :
(forall A1 A2 n1,
  ftvar_in_ptyp A1 [<=] ftvar_in_ptyp (open_ptyp_wrt_ptyp_rec n1 A2 A1)).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_ptyp_open_ptyp_wrt_ptyp_rec_lower :
forall A1 A2 n1,
  ftvar_in_ptyp A1 [<=] ftvar_in_ptyp (open_ptyp_wrt_ptyp_rec n1 A2 A1).
Proof.
pose proof ftvar_in_ptyp_open_ptyp_wrt_ptyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_ptyp_open_ptyp_wrt_ptyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_btyp_open_btyp_wrt_btyp_rec_lower_mutual :
(forall B1 B2 n1,
  ftvar_in_btyp B1 [<=] ftvar_in_btyp (open_btyp_wrt_btyp_rec n1 B2 B1)).
Proof.
apply_mutual_ind btyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_btyp_open_btyp_wrt_btyp_rec_lower :
forall B1 B2 n1,
  ftvar_in_btyp B1 [<=] ftvar_in_btyp (open_btyp_wrt_btyp_rec n1 B2 B1).
Proof.
pose proof ftvar_in_btyp_open_btyp_wrt_btyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_btyp_open_btyp_wrt_btyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_utyp_open_utyp_wrt_utyp_rec_lower_mutual :
(forall C1 C2 n1,
  ftvar_in_utyp C1 [<=] ftvar_in_utyp (open_utyp_wrt_utyp_rec n1 C2 C1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_utyp_open_utyp_wrt_utyp_rec_lower :
forall C1 C2 n1,
  ftvar_in_utyp C1 [<=] ftvar_in_utyp (open_utyp_wrt_utyp_rec n1 C2 C1).
Proof.
pose proof ftvar_in_utyp_open_utyp_wrt_utyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_utyp_open_utyp_wrt_utyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_pskel_open_pskel_wrt_pskel_rec_lower_mutual :
(forall P1 P2 n1,
  ftvar_in_pskel P1 [<=] ftvar_in_pskel (open_pskel_wrt_pskel_rec n1 P2 P1)).
Proof.
apply_mutual_ind pskel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_pskel_open_pskel_wrt_pskel_rec_lower :
forall P1 P2 n1,
  ftvar_in_pskel P1 [<=] ftvar_in_pskel (open_pskel_wrt_pskel_rec n1 P2 P1).
Proof.
pose proof ftvar_in_pskel_open_pskel_wrt_pskel_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_pskel_open_pskel_wrt_pskel_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bskel_open_bskel_wrt_bskel_rec_lower_mutual :
(forall Q1 Q2 n1,
  ftvar_in_bskel Q1 [<=] ftvar_in_bskel (open_bskel_wrt_bskel_rec n1 Q2 Q1)).
Proof.
apply_mutual_ind bskel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bskel_open_bskel_wrt_bskel_rec_lower :
forall Q1 Q2 n1,
  ftvar_in_bskel Q1 [<=] ftvar_in_bskel (open_bskel_wrt_bskel_rec n1 Q2 Q1).
Proof.
pose proof ftvar_in_bskel_open_bskel_wrt_bskel_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bskel_open_bskel_wrt_bskel_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_uskel_open_uskel_wrt_uskel_rec_lower_mutual :
(forall R1 R2 n1,
  ftvar_in_uskel R1 [<=] ftvar_in_uskel (open_uskel_wrt_uskel_rec n1 R2 R1)).
Proof.
apply_mutual_ind uskel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_uskel_open_uskel_wrt_uskel_rec_lower :
forall R1 R2 n1,
  ftvar_in_uskel R1 [<=] ftvar_in_uskel (open_uskel_wrt_uskel_rec n1 R2 R1).
Proof.
pose proof ftvar_in_uskel_open_uskel_wrt_uskel_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_uskel_open_uskel_wrt_uskel_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_ptyp_rec_lower_mutual :
(forall e1 A1 n1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_ptyp_rec n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_ptyp_rec_lower :
forall e1 A1 n1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_ptyp_rec n1 A1 e1).
Proof.
pose proof ftvar_in_exp_open_exp_wrt_ptyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_ptyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_exp_rec_lower_mutual :
(forall e1 e2 n1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_exp_rec_lower :
forall e1 e2 n1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof ftvar_in_exp_open_exp_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_ptyp_rec_lower_mutual :
(forall e1 A1 n1,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_ptyp_rec n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_ptyp_rec_lower :
forall e1 A1 n1,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_ptyp_rec n1 A1 e1).
Proof.
pose proof fvar_in_exp_open_exp_wrt_ptyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_ptyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_exp_rec_lower_mutual :
(forall e1 e2 n1,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_exp_rec_lower :
forall e1 e2 n1,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof fvar_in_exp_open_exp_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

Lemma ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower :
forall A1 A2,
  ftvar_in_ptyp A1 [<=] ftvar_in_ptyp (open_ptyp_wrt_ptyp A1 A2).
Proof.
unfold open_ptyp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_ptyp_open_ptyp_wrt_ptyp_lower : lngen.

Lemma ftvar_in_btyp_open_btyp_wrt_btyp_lower :
forall B1 B2,
  ftvar_in_btyp B1 [<=] ftvar_in_btyp (open_btyp_wrt_btyp B1 B2).
Proof.
unfold open_btyp_wrt_btyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_btyp_open_btyp_wrt_btyp_lower : lngen.

Lemma ftvar_in_utyp_open_utyp_wrt_utyp_lower :
forall C1 C2,
  ftvar_in_utyp C1 [<=] ftvar_in_utyp (open_utyp_wrt_utyp C1 C2).
Proof.
unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_utyp_open_utyp_wrt_utyp_lower : lngen.

Lemma ftvar_in_pskel_open_pskel_wrt_pskel_lower :
forall P1 P2,
  ftvar_in_pskel P1 [<=] ftvar_in_pskel (open_pskel_wrt_pskel P1 P2).
Proof.
unfold open_pskel_wrt_pskel; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_pskel_open_pskel_wrt_pskel_lower : lngen.

Lemma ftvar_in_bskel_open_bskel_wrt_bskel_lower :
forall Q1 Q2,
  ftvar_in_bskel Q1 [<=] ftvar_in_bskel (open_bskel_wrt_bskel Q1 Q2).
Proof.
unfold open_bskel_wrt_bskel; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_bskel_open_bskel_wrt_bskel_lower : lngen.

Lemma ftvar_in_uskel_open_uskel_wrt_uskel_lower :
forall R1 R2,
  ftvar_in_uskel R1 [<=] ftvar_in_uskel (open_uskel_wrt_uskel R1 R2).
Proof.
unfold open_uskel_wrt_uskel; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_uskel_open_uskel_wrt_uskel_lower : lngen.

Lemma ftvar_in_exp_open_exp_wrt_ptyp_lower :
forall e1 A1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_ptyp e1 A1).
Proof.
unfold open_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_ptyp_lower : lngen.

Lemma ftvar_in_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_exp_lower : lngen.

Lemma fvar_in_exp_open_exp_wrt_ptyp_lower :
forall e1 A1,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_ptyp e1 A1).
Proof.
unfold open_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_ptyp_lower : lngen.

Lemma fvar_in_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_exp_lower : lngen.

(* begin hide *)

Lemma ftvar_in_ptyp_open_ptyp_wrt_ptyp_rec_upper_mutual :
(forall A1 A2 n1,
  ftvar_in_ptyp (open_ptyp_wrt_ptyp_rec n1 A2 A1) [<=] ftvar_in_ptyp A2 `union` ftvar_in_ptyp A1).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_ptyp_open_ptyp_wrt_ptyp_rec_upper :
forall A1 A2 n1,
  ftvar_in_ptyp (open_ptyp_wrt_ptyp_rec n1 A2 A1) [<=] ftvar_in_ptyp A2 `union` ftvar_in_ptyp A1.
Proof.
pose proof ftvar_in_ptyp_open_ptyp_wrt_ptyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_ptyp_open_ptyp_wrt_ptyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_btyp_open_btyp_wrt_btyp_rec_upper_mutual :
(forall B1 B2 n1,
  ftvar_in_btyp (open_btyp_wrt_btyp_rec n1 B2 B1) [<=] ftvar_in_btyp B2 `union` ftvar_in_btyp B1).
Proof.
apply_mutual_ind btyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_btyp_open_btyp_wrt_btyp_rec_upper :
forall B1 B2 n1,
  ftvar_in_btyp (open_btyp_wrt_btyp_rec n1 B2 B1) [<=] ftvar_in_btyp B2 `union` ftvar_in_btyp B1.
Proof.
pose proof ftvar_in_btyp_open_btyp_wrt_btyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_btyp_open_btyp_wrt_btyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_utyp_open_utyp_wrt_utyp_rec_upper_mutual :
(forall C1 C2 n1,
  ftvar_in_utyp (open_utyp_wrt_utyp_rec n1 C2 C1) [<=] ftvar_in_utyp C2 `union` ftvar_in_utyp C1).
Proof.
apply_mutual_ind utyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_utyp_open_utyp_wrt_utyp_rec_upper :
forall C1 C2 n1,
  ftvar_in_utyp (open_utyp_wrt_utyp_rec n1 C2 C1) [<=] ftvar_in_utyp C2 `union` ftvar_in_utyp C1.
Proof.
pose proof ftvar_in_utyp_open_utyp_wrt_utyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_utyp_open_utyp_wrt_utyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_pskel_open_pskel_wrt_pskel_rec_upper_mutual :
(forall P1 P2 n1,
  ftvar_in_pskel (open_pskel_wrt_pskel_rec n1 P2 P1) [<=] ftvar_in_pskel P2 `union` ftvar_in_pskel P1).
Proof.
apply_mutual_ind pskel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_pskel_open_pskel_wrt_pskel_rec_upper :
forall P1 P2 n1,
  ftvar_in_pskel (open_pskel_wrt_pskel_rec n1 P2 P1) [<=] ftvar_in_pskel P2 `union` ftvar_in_pskel P1.
Proof.
pose proof ftvar_in_pskel_open_pskel_wrt_pskel_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_pskel_open_pskel_wrt_pskel_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bskel_open_bskel_wrt_bskel_rec_upper_mutual :
(forall Q1 Q2 n1,
  ftvar_in_bskel (open_bskel_wrt_bskel_rec n1 Q2 Q1) [<=] ftvar_in_bskel Q2 `union` ftvar_in_bskel Q1).
Proof.
apply_mutual_ind bskel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bskel_open_bskel_wrt_bskel_rec_upper :
forall Q1 Q2 n1,
  ftvar_in_bskel (open_bskel_wrt_bskel_rec n1 Q2 Q1) [<=] ftvar_in_bskel Q2 `union` ftvar_in_bskel Q1.
Proof.
pose proof ftvar_in_bskel_open_bskel_wrt_bskel_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bskel_open_bskel_wrt_bskel_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_uskel_open_uskel_wrt_uskel_rec_upper_mutual :
(forall R1 R2 n1,
  ftvar_in_uskel (open_uskel_wrt_uskel_rec n1 R2 R1) [<=] ftvar_in_uskel R2 `union` ftvar_in_uskel R1).
Proof.
apply_mutual_ind uskel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_uskel_open_uskel_wrt_uskel_rec_upper :
forall R1 R2 n1,
  ftvar_in_uskel (open_uskel_wrt_uskel_rec n1 R2 R1) [<=] ftvar_in_uskel R2 `union` ftvar_in_uskel R1.
Proof.
pose proof ftvar_in_uskel_open_uskel_wrt_uskel_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_uskel_open_uskel_wrt_uskel_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_ptyp_rec_upper_mutual :
(forall e1 A1 n1,
  ftvar_in_exp (open_exp_wrt_ptyp_rec n1 A1 e1) [<=] ftvar_in_ptyp A1 `union` ftvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_ptyp_rec_upper :
forall e1 A1 n1,
  ftvar_in_exp (open_exp_wrt_ptyp_rec n1 A1 e1) [<=] ftvar_in_ptyp A1 `union` ftvar_in_exp e1.
Proof.
pose proof ftvar_in_exp_open_exp_wrt_ptyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_ptyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_exp_rec_upper_mutual :
(forall e1 e2 n1,
  ftvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] ftvar_in_exp e2 `union` ftvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_exp_rec_upper :
forall e1 e2 n1,
  ftvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] ftvar_in_exp e2 `union` ftvar_in_exp e1.
Proof.
pose proof ftvar_in_exp_open_exp_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_ptyp_rec_upper_mutual :
(forall e1 A1 n1,
  fvar_in_exp (open_exp_wrt_ptyp_rec n1 A1 e1) [<=] fvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_ptyp_rec_upper :
forall e1 A1 n1,
  fvar_in_exp (open_exp_wrt_ptyp_rec n1 A1 e1) [<=] fvar_in_exp e1.
Proof.
pose proof fvar_in_exp_open_exp_wrt_ptyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_ptyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_exp_rec_upper_mutual :
(forall e1 e2 n1,
  fvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] fvar_in_exp e2 `union` fvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_exp_rec_upper :
forall e1 e2 n1,
  fvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] fvar_in_exp e2 `union` fvar_in_exp e1.
Proof.
pose proof fvar_in_exp_open_exp_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

Lemma ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper :
forall A1 A2,
  ftvar_in_ptyp (open_ptyp_wrt_ptyp A1 A2) [<=] ftvar_in_ptyp A2 `union` ftvar_in_ptyp A1.
Proof.
unfold open_ptyp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_ptyp_open_ptyp_wrt_ptyp_upper : lngen.

Lemma ftvar_in_btyp_open_btyp_wrt_btyp_upper :
forall B1 B2,
  ftvar_in_btyp (open_btyp_wrt_btyp B1 B2) [<=] ftvar_in_btyp B2 `union` ftvar_in_btyp B1.
Proof.
unfold open_btyp_wrt_btyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_btyp_open_btyp_wrt_btyp_upper : lngen.

Lemma ftvar_in_utyp_open_utyp_wrt_utyp_upper :
forall C1 C2,
  ftvar_in_utyp (open_utyp_wrt_utyp C1 C2) [<=] ftvar_in_utyp C2 `union` ftvar_in_utyp C1.
Proof.
unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_utyp_open_utyp_wrt_utyp_upper : lngen.

Lemma ftvar_in_pskel_open_pskel_wrt_pskel_upper :
forall P1 P2,
  ftvar_in_pskel (open_pskel_wrt_pskel P1 P2) [<=] ftvar_in_pskel P2 `union` ftvar_in_pskel P1.
Proof.
unfold open_pskel_wrt_pskel; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_pskel_open_pskel_wrt_pskel_upper : lngen.

Lemma ftvar_in_bskel_open_bskel_wrt_bskel_upper :
forall Q1 Q2,
  ftvar_in_bskel (open_bskel_wrt_bskel Q1 Q2) [<=] ftvar_in_bskel Q2 `union` ftvar_in_bskel Q1.
Proof.
unfold open_bskel_wrt_bskel; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_bskel_open_bskel_wrt_bskel_upper : lngen.

Lemma ftvar_in_uskel_open_uskel_wrt_uskel_upper :
forall R1 R2,
  ftvar_in_uskel (open_uskel_wrt_uskel R1 R2) [<=] ftvar_in_uskel R2 `union` ftvar_in_uskel R1.
Proof.
unfold open_uskel_wrt_uskel; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_uskel_open_uskel_wrt_uskel_upper : lngen.

Lemma ftvar_in_exp_open_exp_wrt_ptyp_upper :
forall e1 A1,
  ftvar_in_exp (open_exp_wrt_ptyp e1 A1) [<=] ftvar_in_ptyp A1 `union` ftvar_in_exp e1.
Proof.
unfold open_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_ptyp_upper : lngen.

Lemma ftvar_in_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  ftvar_in_exp (open_exp_wrt_exp e1 e2) [<=] ftvar_in_exp e2 `union` ftvar_in_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_exp_upper : lngen.

Lemma fvar_in_exp_open_exp_wrt_ptyp_upper :
forall e1 A1,
  fvar_in_exp (open_exp_wrt_ptyp e1 A1) [<=] fvar_in_exp e1.
Proof.
unfold open_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_ptyp_upper : lngen.

Lemma fvar_in_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  fvar_in_exp (open_exp_wrt_exp e1 e2) [<=] fvar_in_exp e2 `union` fvar_in_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_exp_upper : lngen.

(* begin hide *)

Lemma ftvar_in_ptyp_subst_ptyp_in_ptyp_fresh_mutual :
(forall A1 A2 Xpt1,
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  ftvar_in_ptyp (subst_ptyp_in_ptyp A2 Xpt1 A1) [=] ftvar_in_ptyp A1).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_ptyp_subst_ptyp_in_ptyp_fresh :
forall A1 A2 Xpt1,
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  ftvar_in_ptyp (subst_ptyp_in_ptyp A2 Xpt1 A1) [=] ftvar_in_ptyp A1.
Proof.
pose proof ftvar_in_ptyp_subst_ptyp_in_ptyp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_ptyp_subst_ptyp_in_ptyp_fresh : lngen.
#[export] Hint Rewrite ftvar_in_ptyp_subst_ptyp_in_ptyp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_btyp_subst_btyp_in_btyp_fresh_mutual :
(forall B1 B2 Xbt1,
  Xbt1 `notin` ftvar_in_btyp B1 ->
  ftvar_in_btyp (subst_btyp_in_btyp B2 Xbt1 B1) [=] ftvar_in_btyp B1).
Proof.
apply_mutual_ind btyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_btyp_subst_btyp_in_btyp_fresh :
forall B1 B2 Xbt1,
  Xbt1 `notin` ftvar_in_btyp B1 ->
  ftvar_in_btyp (subst_btyp_in_btyp B2 Xbt1 B1) [=] ftvar_in_btyp B1.
Proof.
pose proof ftvar_in_btyp_subst_btyp_in_btyp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_btyp_subst_btyp_in_btyp_fresh : lngen.
#[export] Hint Rewrite ftvar_in_btyp_subst_btyp_in_btyp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_utyp_subst_utyp_in_utyp_fresh_mutual :
(forall C1 C2 Xut1,
  Xut1 `notin` ftvar_in_utyp C1 ->
  ftvar_in_utyp (subst_utyp_in_utyp C2 Xut1 C1) [=] ftvar_in_utyp C1).
Proof.
apply_mutual_ind utyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_utyp_subst_utyp_in_utyp_fresh :
forall C1 C2 Xut1,
  Xut1 `notin` ftvar_in_utyp C1 ->
  ftvar_in_utyp (subst_utyp_in_utyp C2 Xut1 C1) [=] ftvar_in_utyp C1.
Proof.
pose proof ftvar_in_utyp_subst_utyp_in_utyp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_utyp_subst_utyp_in_utyp_fresh : lngen.
#[export] Hint Rewrite ftvar_in_utyp_subst_utyp_in_utyp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_pskel_subst_pskl_in_pskel_fresh_mutual :
(forall P1 P2 Xps1,
  Xps1 `notin` ftvar_in_pskel P1 ->
  ftvar_in_pskel (subst_pskl_in_pskel P2 Xps1 P1) [=] ftvar_in_pskel P1).
Proof.
apply_mutual_ind pskel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_pskel_subst_pskl_in_pskel_fresh :
forall P1 P2 Xps1,
  Xps1 `notin` ftvar_in_pskel P1 ->
  ftvar_in_pskel (subst_pskl_in_pskel P2 Xps1 P1) [=] ftvar_in_pskel P1.
Proof.
pose proof ftvar_in_pskel_subst_pskl_in_pskel_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_pskel_subst_pskl_in_pskel_fresh : lngen.
#[export] Hint Rewrite ftvar_in_pskel_subst_pskl_in_pskel_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_bskel_subst_bskl_in_bskel_fresh_mutual :
(forall Q1 Q2 Xbs1,
  Xbs1 `notin` ftvar_in_bskel Q1 ->
  ftvar_in_bskel (subst_bskl_in_bskel Q2 Xbs1 Q1) [=] ftvar_in_bskel Q1).
Proof.
apply_mutual_ind bskel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_bskel_subst_bskl_in_bskel_fresh :
forall Q1 Q2 Xbs1,
  Xbs1 `notin` ftvar_in_bskel Q1 ->
  ftvar_in_bskel (subst_bskl_in_bskel Q2 Xbs1 Q1) [=] ftvar_in_bskel Q1.
Proof.
pose proof ftvar_in_bskel_subst_bskl_in_bskel_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bskel_subst_bskl_in_bskel_fresh : lngen.
#[export] Hint Rewrite ftvar_in_bskel_subst_bskl_in_bskel_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_uskel_subst_bskl_in_uskel_fresh_mutual :
(forall R1 R2 Xus1,
  Xus1 `notin` ftvar_in_uskel R1 ->
  ftvar_in_uskel (subst_bskl_in_uskel R2 Xus1 R1) [=] ftvar_in_uskel R1).
Proof.
apply_mutual_ind uskel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_uskel_subst_bskl_in_uskel_fresh :
forall R1 R2 Xus1,
  Xus1 `notin` ftvar_in_uskel R1 ->
  ftvar_in_uskel (subst_bskl_in_uskel R2 Xus1 R1) [=] ftvar_in_uskel R1.
Proof.
pose proof ftvar_in_uskel_subst_bskl_in_uskel_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_uskel_subst_bskl_in_uskel_fresh : lngen.
#[export] Hint Rewrite ftvar_in_uskel_subst_bskl_in_uskel_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_ptyp_in_exp_fresh_mutual :
(forall e1 A1 Xpt1,
  Xpt1 `notin` ftvar_in_exp e1 ->
  ftvar_in_exp (subst_ptyp_in_exp A1 Xpt1 e1) [=] ftvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_ptyp_in_exp_fresh :
forall e1 A1 Xpt1,
  Xpt1 `notin` ftvar_in_exp e1 ->
  ftvar_in_exp (subst_ptyp_in_exp A1 Xpt1 e1) [=] ftvar_in_exp e1.
Proof.
pose proof ftvar_in_exp_subst_ptyp_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_ptyp_in_exp_fresh : lngen.
#[export] Hint Rewrite ftvar_in_exp_subst_ptyp_in_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_fresh_mutual :
(forall e1 A1 Xpt1,
  fvar_in_exp (subst_ptyp_in_exp A1 Xpt1 e1) [=] fvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_fresh :
forall e1 A1 Xpt1,
  fvar_in_exp (subst_ptyp_in_exp A1 Xpt1 e1) [=] fvar_in_exp e1.
Proof.
pose proof ftvar_in_exp_subst_exp_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_exp_in_exp_fresh : lngen.
#[export] Hint Rewrite ftvar_in_exp_subst_exp_in_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fvar_in_exp_subst_exp_in_exp_fresh_mutual :
(forall e1 e2 x1,
  x1 `notin` fvar_in_exp e1 ->
  fvar_in_exp (subst_exp_in_exp e2 x1 e1) [=] fvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_exp_subst_exp_in_exp_fresh :
forall e1 e2 x1,
  x1 `notin` fvar_in_exp e1 ->
  fvar_in_exp (subst_exp_in_exp e2 x1 e1) [=] fvar_in_exp e1.
Proof.
pose proof fvar_in_exp_subst_exp_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_exp_in_exp_fresh : lngen.
#[export] Hint Rewrite fvar_in_exp_subst_exp_in_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_ptyp_subst_ptyp_in_ptyp_lower_mutual :
(forall A1 A2 Xpt1,
  remove Xpt1 (ftvar_in_ptyp A1) [<=] ftvar_in_ptyp (subst_ptyp_in_ptyp A2 Xpt1 A1)).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_ptyp_subst_ptyp_in_ptyp_lower :
forall A1 A2 Xpt1,
  remove Xpt1 (ftvar_in_ptyp A1) [<=] ftvar_in_ptyp (subst_ptyp_in_ptyp A2 Xpt1 A1).
Proof.
pose proof ftvar_in_ptyp_subst_ptyp_in_ptyp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_ptyp_subst_ptyp_in_ptyp_lower : lngen.

(* begin hide *)

Lemma ftvar_in_btyp_subst_btyp_in_btyp_lower_mutual :
(forall B1 B2 Xbt1,
  remove Xbt1 (ftvar_in_btyp B1) [<=] ftvar_in_btyp (subst_btyp_in_btyp B2 Xbt1 B1)).
Proof.
apply_mutual_ind btyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_btyp_subst_btyp_in_btyp_lower :
forall B1 B2 Xbt1,
  remove Xbt1 (ftvar_in_btyp B1) [<=] ftvar_in_btyp (subst_btyp_in_btyp B2 Xbt1 B1).
Proof.
pose proof ftvar_in_btyp_subst_btyp_in_btyp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_btyp_subst_btyp_in_btyp_lower : lngen.

(* begin hide *)

Lemma ftvar_in_utyp_subst_utyp_in_utyp_lower_mutual :
(forall C1 C2 Xut1,
  remove Xut1 (ftvar_in_utyp C1) [<=] ftvar_in_utyp (subst_utyp_in_utyp C2 Xut1 C1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_utyp_subst_utyp_in_utyp_lower :
forall C1 C2 Xut1,
  remove Xut1 (ftvar_in_utyp C1) [<=] ftvar_in_utyp (subst_utyp_in_utyp C2 Xut1 C1).
Proof.
pose proof ftvar_in_utyp_subst_utyp_in_utyp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_utyp_subst_utyp_in_utyp_lower : lngen.

(* begin hide *)

Lemma ftvar_in_pskel_subst_pskl_in_pskel_lower_mutual :
(forall P1 P2 Xps1,
  remove Xps1 (ftvar_in_pskel P1) [<=] ftvar_in_pskel (subst_pskl_in_pskel P2 Xps1 P1)).
Proof.
apply_mutual_ind pskel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_pskel_subst_pskl_in_pskel_lower :
forall P1 P2 Xps1,
  remove Xps1 (ftvar_in_pskel P1) [<=] ftvar_in_pskel (subst_pskl_in_pskel P2 Xps1 P1).
Proof.
pose proof ftvar_in_pskel_subst_pskl_in_pskel_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_pskel_subst_pskl_in_pskel_lower : lngen.

(* begin hide *)

Lemma ftvar_in_bskel_subst_bskl_in_bskel_lower_mutual :
(forall Q1 Q2 Xbs1,
  remove Xbs1 (ftvar_in_bskel Q1) [<=] ftvar_in_bskel (subst_bskl_in_bskel Q2 Xbs1 Q1)).
Proof.
apply_mutual_ind bskel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_bskel_subst_bskl_in_bskel_lower :
forall Q1 Q2 Xbs1,
  remove Xbs1 (ftvar_in_bskel Q1) [<=] ftvar_in_bskel (subst_bskl_in_bskel Q2 Xbs1 Q1).
Proof.
pose proof ftvar_in_bskel_subst_bskl_in_bskel_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bskel_subst_bskl_in_bskel_lower : lngen.

(* begin hide *)

Lemma ftvar_in_uskel_subst_bskl_in_uskel_lower_mutual :
(forall R1 R2 Xus1,
  remove Xus1 (ftvar_in_uskel R1) [<=] ftvar_in_uskel (subst_bskl_in_uskel R2 Xus1 R1)).
Proof.
apply_mutual_ind uskel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_uskel_subst_bskl_in_uskel_lower :
forall R1 R2 Xus1,
  remove Xus1 (ftvar_in_uskel R1) [<=] ftvar_in_uskel (subst_bskl_in_uskel R2 Xus1 R1).
Proof.
pose proof ftvar_in_uskel_subst_bskl_in_uskel_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_uskel_subst_bskl_in_uskel_lower : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_ptyp_in_exp_lower_mutual :
(forall e1 A1 Xpt1,
  remove Xpt1 (ftvar_in_exp e1) [<=] ftvar_in_exp (subst_ptyp_in_exp A1 Xpt1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_ptyp_in_exp_lower :
forall e1 A1 Xpt1,
  remove Xpt1 (ftvar_in_exp e1) [<=] ftvar_in_exp (subst_ptyp_in_exp A1 Xpt1 e1).
Proof.
pose proof ftvar_in_exp_subst_ptyp_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_ptyp_in_exp_lower : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_lower_mutual :
(forall e1 e2 x1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_lower :
forall e1 e2 x1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof ftvar_in_exp_subst_exp_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_exp_in_exp_lower : lngen.

(* begin hide *)

Lemma fvar_in_exp_subst_ptyp_in_exp_lower_mutual :
(forall e1 A1 Xpt1,
  fvar_in_exp e1 [<=] fvar_in_exp (subst_ptyp_in_exp A1 Xpt1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_exp_subst_ptyp_in_exp_lower :
forall e1 A1 Xpt1,
  fvar_in_exp e1 [<=] fvar_in_exp (subst_ptyp_in_exp A1 Xpt1 e1).
Proof.
pose proof fvar_in_exp_subst_ptyp_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_ptyp_in_exp_lower : lngen.

(* begin hide *)

Lemma fvar_in_exp_subst_exp_in_exp_lower_mutual :
(forall e1 e2 x1,
  remove x1 (fvar_in_exp e1) [<=] fvar_in_exp (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_exp_subst_exp_in_exp_lower :
forall e1 e2 x1,
  remove x1 (fvar_in_exp e1) [<=] fvar_in_exp (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof fvar_in_exp_subst_exp_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_exp_in_exp_lower : lngen.

(* begin hide *)

Lemma ftvar_in_ptyp_subst_ptyp_in_ptyp_notin_mutual :
(forall A1 A2 Xpt1 Xpt2,
  Xpt2 `notin` ftvar_in_ptyp A1 ->
  Xpt2 `notin` ftvar_in_ptyp A2 ->
  Xpt2 `notin` ftvar_in_ptyp (subst_ptyp_in_ptyp A2 Xpt1 A1)).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_ptyp_subst_ptyp_in_ptyp_notin :
forall A1 A2 Xpt1 Xpt2,
  Xpt2 `notin` ftvar_in_ptyp A1 ->
  Xpt2 `notin` ftvar_in_ptyp A2 ->
  Xpt2 `notin` ftvar_in_ptyp (subst_ptyp_in_ptyp A2 Xpt1 A1).
Proof.
pose proof ftvar_in_ptyp_subst_ptyp_in_ptyp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_ptyp_subst_ptyp_in_ptyp_notin : lngen.

(* begin hide *)

Lemma ftvar_in_btyp_subst_btyp_in_btyp_notin_mutual :
(forall B1 B2 Xbt1 Xbt2,
  Xbt2 `notin` ftvar_in_btyp B1 ->
  Xbt2 `notin` ftvar_in_btyp B2 ->
  Xbt2 `notin` ftvar_in_btyp (subst_btyp_in_btyp B2 Xbt1 B1)).
Proof.
apply_mutual_ind btyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_btyp_subst_btyp_in_btyp_notin :
forall B1 B2 Xbt1 Xbt2,
  Xbt2 `notin` ftvar_in_btyp B1 ->
  Xbt2 `notin` ftvar_in_btyp B2 ->
  Xbt2 `notin` ftvar_in_btyp (subst_btyp_in_btyp B2 Xbt1 B1).
Proof.
pose proof ftvar_in_btyp_subst_btyp_in_btyp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_btyp_subst_btyp_in_btyp_notin : lngen.

(* begin hide *)

Lemma ftvar_in_utyp_subst_utyp_in_utyp_notin_mutual :
(forall C1 C2 Xut1 Xut2,
  Xut2 `notin` ftvar_in_utyp C1 ->
  Xut2 `notin` ftvar_in_utyp C2 ->
  Xut2 `notin` ftvar_in_utyp (subst_utyp_in_utyp C2 Xut1 C1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_utyp_subst_utyp_in_utyp_notin :
forall C1 C2 Xut1 Xut2,
  Xut2 `notin` ftvar_in_utyp C1 ->
  Xut2 `notin` ftvar_in_utyp C2 ->
  Xut2 `notin` ftvar_in_utyp (subst_utyp_in_utyp C2 Xut1 C1).
Proof.
pose proof ftvar_in_utyp_subst_utyp_in_utyp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_utyp_subst_utyp_in_utyp_notin : lngen.

(* begin hide *)

Lemma ftvar_in_pskel_subst_pskl_in_pskel_notin_mutual :
(forall P1 P2 Xps1 Xps2,
  Xps2 `notin` ftvar_in_pskel P1 ->
  Xps2 `notin` ftvar_in_pskel P2 ->
  Xps2 `notin` ftvar_in_pskel (subst_pskl_in_pskel P2 Xps1 P1)).
Proof.
apply_mutual_ind pskel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_pskel_subst_pskl_in_pskel_notin :
forall P1 P2 Xps1 Xps2,
  Xps2 `notin` ftvar_in_pskel P1 ->
  Xps2 `notin` ftvar_in_pskel P2 ->
  Xps2 `notin` ftvar_in_pskel (subst_pskl_in_pskel P2 Xps1 P1).
Proof.
pose proof ftvar_in_pskel_subst_pskl_in_pskel_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_pskel_subst_pskl_in_pskel_notin : lngen.

(* begin hide *)

Lemma ftvar_in_bskel_subst_bskl_in_bskel_notin_mutual :
(forall Q1 Q2 Xbs1 Xbs2,
  Xbs2 `notin` ftvar_in_bskel Q1 ->
  Xbs2 `notin` ftvar_in_bskel Q2 ->
  Xbs2 `notin` ftvar_in_bskel (subst_bskl_in_bskel Q2 Xbs1 Q1)).
Proof.
apply_mutual_ind bskel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_bskel_subst_bskl_in_bskel_notin :
forall Q1 Q2 Xbs1 Xbs2,
  Xbs2 `notin` ftvar_in_bskel Q1 ->
  Xbs2 `notin` ftvar_in_bskel Q2 ->
  Xbs2 `notin` ftvar_in_bskel (subst_bskl_in_bskel Q2 Xbs1 Q1).
Proof.
pose proof ftvar_in_bskel_subst_bskl_in_bskel_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bskel_subst_bskl_in_bskel_notin : lngen.

(* begin hide *)

Lemma ftvar_in_uskel_subst_bskl_in_uskel_notin_mutual :
(forall R1 R2 Xus1 Xus2,
  Xus2 `notin` ftvar_in_uskel R1 ->
  Xus2 `notin` ftvar_in_uskel R2 ->
  Xus2 `notin` ftvar_in_uskel (subst_bskl_in_uskel R2 Xus1 R1)).
Proof.
apply_mutual_ind uskel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_uskel_subst_bskl_in_uskel_notin :
forall R1 R2 Xus1 Xus2,
  Xus2 `notin` ftvar_in_uskel R1 ->
  Xus2 `notin` ftvar_in_uskel R2 ->
  Xus2 `notin` ftvar_in_uskel (subst_bskl_in_uskel R2 Xus1 R1).
Proof.
pose proof ftvar_in_uskel_subst_bskl_in_uskel_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_uskel_subst_bskl_in_uskel_notin : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_ptyp_in_exp_notin_mutual :
(forall e1 A1 Xpt1 Xpt2,
  Xpt2 `notin` ftvar_in_exp e1 ->
  Xpt2 `notin` ftvar_in_ptyp A1 ->
  Xpt2 `notin` ftvar_in_exp (subst_ptyp_in_exp A1 Xpt1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_ptyp_in_exp_notin :
forall e1 A1 Xpt1 Xpt2,
  Xpt2 `notin` ftvar_in_exp e1 ->
  Xpt2 `notin` ftvar_in_ptyp A1 ->
  Xpt2 `notin` ftvar_in_exp (subst_ptyp_in_exp A1 Xpt1 e1).
Proof.
pose proof ftvar_in_exp_subst_ptyp_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_ptyp_in_exp_notin : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_notin_mutual :
(forall e1 e2 x1 Xpt1,
  Xpt1 `notin` ftvar_in_exp e1 ->
  Xpt1 `notin` ftvar_in_exp e2 ->
  Xpt1 `notin` ftvar_in_exp (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_notin :
forall e1 e2 x1 Xpt1,
  Xpt1 `notin` ftvar_in_exp e1 ->
  Xpt1 `notin` ftvar_in_exp e2 ->
  Xpt1 `notin` ftvar_in_exp (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof ftvar_in_exp_subst_exp_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_exp_in_exp_notin : lngen.

(* begin hide *)

Lemma fvar_in_exp_subst_ptyp_in_exp_notin_mutual :
(forall e1 A1 Xpt1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_ptyp_in_exp A1 Xpt1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_exp_subst_ptyp_in_exp_notin :
forall e1 A1 Xpt1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_ptyp_in_exp A1 Xpt1 e1).
Proof.
pose proof fvar_in_exp_subst_ptyp_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_ptyp_in_exp_notin : lngen.

(* begin hide *)

Lemma fvar_in_exp_subst_exp_in_exp_notin_mutual :
(forall e1 e2 x1 x2,
  x2 `notin` fvar_in_exp e1 ->
  x2 `notin` fvar_in_exp e2 ->
  x2 `notin` fvar_in_exp (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_exp_subst_exp_in_exp_notin :
forall e1 e2 x1 x2,
  x2 `notin` fvar_in_exp e1 ->
  x2 `notin` fvar_in_exp e2 ->
  x2 `notin` fvar_in_exp (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof fvar_in_exp_subst_exp_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_exp_in_exp_notin : lngen.

(* begin hide *)

Lemma ftvar_in_ptyp_subst_ptyp_in_ptyp_upper_mutual :
(forall A1 A2 Xpt1,
  ftvar_in_ptyp (subst_ptyp_in_ptyp A2 Xpt1 A1) [<=] ftvar_in_ptyp A2 `union` remove Xpt1 (ftvar_in_ptyp A1)).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_ptyp_subst_ptyp_in_ptyp_upper :
forall A1 A2 Xpt1,
  ftvar_in_ptyp (subst_ptyp_in_ptyp A2 Xpt1 A1) [<=] ftvar_in_ptyp A2 `union` remove Xpt1 (ftvar_in_ptyp A1).
Proof.
pose proof ftvar_in_ptyp_subst_ptyp_in_ptyp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_ptyp_subst_ptyp_in_ptyp_upper : lngen.

(* begin hide *)

Lemma ftvar_in_btyp_subst_btyp_in_btyp_upper_mutual :
(forall B1 B2 Xbt1,
  ftvar_in_btyp (subst_btyp_in_btyp B2 Xbt1 B1) [<=] ftvar_in_btyp B2 `union` remove Xbt1 (ftvar_in_btyp B1)).
Proof.
apply_mutual_ind btyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_btyp_subst_btyp_in_btyp_upper :
forall B1 B2 Xbt1,
  ftvar_in_btyp (subst_btyp_in_btyp B2 Xbt1 B1) [<=] ftvar_in_btyp B2 `union` remove Xbt1 (ftvar_in_btyp B1).
Proof.
pose proof ftvar_in_btyp_subst_btyp_in_btyp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_btyp_subst_btyp_in_btyp_upper : lngen.

(* begin hide *)

Lemma ftvar_in_utyp_subst_utyp_in_utyp_upper_mutual :
(forall C1 C2 Xut1,
  ftvar_in_utyp (subst_utyp_in_utyp C2 Xut1 C1) [<=] ftvar_in_utyp C2 `union` remove Xut1 (ftvar_in_utyp C1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_utyp_subst_utyp_in_utyp_upper :
forall C1 C2 Xut1,
  ftvar_in_utyp (subst_utyp_in_utyp C2 Xut1 C1) [<=] ftvar_in_utyp C2 `union` remove Xut1 (ftvar_in_utyp C1).
Proof.
pose proof ftvar_in_utyp_subst_utyp_in_utyp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_utyp_subst_utyp_in_utyp_upper : lngen.

(* begin hide *)

Lemma ftvar_in_pskel_subst_pskl_in_pskel_upper_mutual :
(forall P1 P2 Xps1,
  ftvar_in_pskel (subst_pskl_in_pskel P2 Xps1 P1) [<=] ftvar_in_pskel P2 `union` remove Xps1 (ftvar_in_pskel P1)).
Proof.
apply_mutual_ind pskel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_pskel_subst_pskl_in_pskel_upper :
forall P1 P2 Xps1,
  ftvar_in_pskel (subst_pskl_in_pskel P2 Xps1 P1) [<=] ftvar_in_pskel P2 `union` remove Xps1 (ftvar_in_pskel P1).
Proof.
pose proof ftvar_in_pskel_subst_pskl_in_pskel_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_pskel_subst_pskl_in_pskel_upper : lngen.

(* begin hide *)

Lemma ftvar_in_bskel_subst_bskl_in_bskel_upper_mutual :
(forall Q1 Q2 Xbs1,
  ftvar_in_bskel (subst_bskl_in_bskel Q2 Xbs1 Q1) [<=] ftvar_in_bskel Q2 `union` remove Xbs1 (ftvar_in_bskel Q1)).
Proof.
apply_mutual_ind bskel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_bskel_subst_bskl_in_bskel_upper :
forall Q1 Q2 Xbs1,
  ftvar_in_bskel (subst_bskl_in_bskel Q2 Xbs1 Q1) [<=] ftvar_in_bskel Q2 `union` remove Xbs1 (ftvar_in_bskel Q1).
Proof.
pose proof ftvar_in_bskel_subst_bskl_in_bskel_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bskel_subst_bskl_in_bskel_upper : lngen.

(* begin hide *)

Lemma ftvar_in_uskel_subst_bskl_in_uskel_upper_mutual :
(forall R1 R2 Xus1,
  ftvar_in_uskel (subst_bskl_in_uskel R2 Xus1 R1) [<=] ftvar_in_uskel R2 `union` remove Xus1 (ftvar_in_uskel R1)).
Proof.
apply_mutual_ind uskel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_uskel_subst_bskl_in_uskel_upper :
forall R1 R2 Xus1,
  ftvar_in_uskel (subst_bskl_in_uskel R2 Xus1 R1) [<=] ftvar_in_uskel R2 `union` remove Xus1 (ftvar_in_uskel R1).
Proof.
pose proof ftvar_in_uskel_subst_bskl_in_uskel_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_uskel_subst_bskl_in_uskel_upper : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_ptyp_in_exp_upper_mutual :
(forall e1 A1 Xpt1,
  ftvar_in_exp (subst_ptyp_in_exp A1 Xpt1 e1) [<=] ftvar_in_ptyp A1 `union` remove Xpt1 (ftvar_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_ptyp_in_exp_upper :
forall e1 A1 Xpt1,
  ftvar_in_exp (subst_ptyp_in_exp A1 Xpt1 e1) [<=] ftvar_in_ptyp A1 `union` remove Xpt1 (ftvar_in_exp e1).
Proof.
pose proof ftvar_in_exp_subst_ptyp_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_ptyp_in_exp_upper : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_upper_mutual :
(forall e1 e2 x1,
  ftvar_in_exp (subst_exp_in_exp e2 x1 e1) [<=] ftvar_in_exp e2 `union` ftvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_upper :
forall e1 e2 x1,
  ftvar_in_exp (subst_exp_in_exp e2 x1 e1) [<=] ftvar_in_exp e2 `union` ftvar_in_exp e1.
Proof.
pose proof ftvar_in_exp_subst_exp_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_exp_in_exp_upper : lngen.

(* begin hide *)

Lemma fvar_in_exp_subst_ptyp_in_exp_upper_mutual :
(forall e1 A1 Xpt1,
  fvar_in_exp (subst_ptyp_in_exp A1 Xpt1 e1) [<=] fvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_exp_subst_ptyp_in_exp_upper :
forall e1 A1 Xpt1,
  fvar_in_exp (subst_ptyp_in_exp A1 Xpt1 e1) [<=] fvar_in_exp e1.
Proof.
pose proof fvar_in_exp_subst_ptyp_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_ptyp_in_exp_upper : lngen.

(* begin hide *)

Lemma fvar_in_exp_subst_exp_in_exp_upper_mutual :
(forall e1 e2 x1,
  fvar_in_exp (subst_exp_in_exp e2 x1 e1) [<=] fvar_in_exp e2 `union` remove x1 (fvar_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_exp_subst_exp_in_exp_upper :
forall e1 e2 x1,
  fvar_in_exp (subst_exp_in_exp e2 x1 e1) [<=] fvar_in_exp e2 `union` remove x1 (fvar_in_exp e1).
Proof.
pose proof fvar_in_exp_subst_exp_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_exp_in_exp_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_ptyp_in_ptyp_close_ptyp_wrt_ptyp_rec_mutual :
(forall A2 A1 Xpt1 Xpt2 n1,
  degree_ptyp_wrt_ptyp n1 A1 ->
  Xpt1 <> Xpt2 ->
  Xpt2 `notin` ftvar_in_ptyp A1 ->
  subst_ptyp_in_ptyp A1 Xpt1 (close_ptyp_wrt_ptyp_rec n1 Xpt2 A2) = close_ptyp_wrt_ptyp_rec n1 Xpt2 (subst_ptyp_in_ptyp A1 Xpt1 A2)).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ptyp_in_ptyp_close_ptyp_wrt_ptyp_rec :
forall A2 A1 Xpt1 Xpt2 n1,
  degree_ptyp_wrt_ptyp n1 A1 ->
  Xpt1 <> Xpt2 ->
  Xpt2 `notin` ftvar_in_ptyp A1 ->
  subst_ptyp_in_ptyp A1 Xpt1 (close_ptyp_wrt_ptyp_rec n1 Xpt2 A2) = close_ptyp_wrt_ptyp_rec n1 Xpt2 (subst_ptyp_in_ptyp A1 Xpt1 A2).
Proof.
pose proof subst_ptyp_in_ptyp_close_ptyp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_ptyp_close_ptyp_wrt_ptyp_rec : lngen.

(* begin hide *)

Lemma subst_btyp_in_btyp_close_btyp_wrt_btyp_rec_mutual :
(forall B2 B1 Xbt1 Xbt2 n1,
  degree_btyp_wrt_btyp n1 B1 ->
  Xbt1 <> Xbt2 ->
  Xbt2 `notin` ftvar_in_btyp B1 ->
  subst_btyp_in_btyp B1 Xbt1 (close_btyp_wrt_btyp_rec n1 Xbt2 B2) = close_btyp_wrt_btyp_rec n1 Xbt2 (subst_btyp_in_btyp B1 Xbt1 B2)).
Proof.
apply_mutual_ind btyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_btyp_in_btyp_close_btyp_wrt_btyp_rec :
forall B2 B1 Xbt1 Xbt2 n1,
  degree_btyp_wrt_btyp n1 B1 ->
  Xbt1 <> Xbt2 ->
  Xbt2 `notin` ftvar_in_btyp B1 ->
  subst_btyp_in_btyp B1 Xbt1 (close_btyp_wrt_btyp_rec n1 Xbt2 B2) = close_btyp_wrt_btyp_rec n1 Xbt2 (subst_btyp_in_btyp B1 Xbt1 B2).
Proof.
pose proof subst_btyp_in_btyp_close_btyp_wrt_btyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_btyp_in_btyp_close_btyp_wrt_btyp_rec : lngen.

(* begin hide *)

Lemma subst_utyp_in_utyp_close_utyp_wrt_utyp_rec_mutual :
(forall C2 C1 Xut1 Xut2 n1,
  degree_utyp_wrt_utyp n1 C1 ->
  Xut1 <> Xut2 ->
  Xut2 `notin` ftvar_in_utyp C1 ->
  subst_utyp_in_utyp C1 Xut1 (close_utyp_wrt_utyp_rec n1 Xut2 C2) = close_utyp_wrt_utyp_rec n1 Xut2 (subst_utyp_in_utyp C1 Xut1 C2)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_utyp_in_utyp_close_utyp_wrt_utyp_rec :
forall C2 C1 Xut1 Xut2 n1,
  degree_utyp_wrt_utyp n1 C1 ->
  Xut1 <> Xut2 ->
  Xut2 `notin` ftvar_in_utyp C1 ->
  subst_utyp_in_utyp C1 Xut1 (close_utyp_wrt_utyp_rec n1 Xut2 C2) = close_utyp_wrt_utyp_rec n1 Xut2 (subst_utyp_in_utyp C1 Xut1 C2).
Proof.
pose proof subst_utyp_in_utyp_close_utyp_wrt_utyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_close_utyp_wrt_utyp_rec : lngen.

(* begin hide *)

Lemma subst_pskl_in_pskel_close_pskel_wrt_pskel_rec_mutual :
(forall P2 P1 Xps1 Xps2 n1,
  degree_pskel_wrt_pskel n1 P1 ->
  Xps1 <> Xps2 ->
  Xps2 `notin` ftvar_in_pskel P1 ->
  subst_pskl_in_pskel P1 Xps1 (close_pskel_wrt_pskel_rec n1 Xps2 P2) = close_pskel_wrt_pskel_rec n1 Xps2 (subst_pskl_in_pskel P1 Xps1 P2)).
Proof.
apply_mutual_ind pskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pskl_in_pskel_close_pskel_wrt_pskel_rec :
forall P2 P1 Xps1 Xps2 n1,
  degree_pskel_wrt_pskel n1 P1 ->
  Xps1 <> Xps2 ->
  Xps2 `notin` ftvar_in_pskel P1 ->
  subst_pskl_in_pskel P1 Xps1 (close_pskel_wrt_pskel_rec n1 Xps2 P2) = close_pskel_wrt_pskel_rec n1 Xps2 (subst_pskl_in_pskel P1 Xps1 P2).
Proof.
pose proof subst_pskl_in_pskel_close_pskel_wrt_pskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pskl_in_pskel_close_pskel_wrt_pskel_rec : lngen.

(* begin hide *)

Lemma subst_bskl_in_bskel_close_bskel_wrt_bskel_rec_mutual :
(forall Q2 Q1 Xbs1 Xbs2 n1,
  degree_bskel_wrt_bskel n1 Q1 ->
  Xbs1 <> Xbs2 ->
  Xbs2 `notin` ftvar_in_bskel Q1 ->
  subst_bskl_in_bskel Q1 Xbs1 (close_bskel_wrt_bskel_rec n1 Xbs2 Q2) = close_bskel_wrt_bskel_rec n1 Xbs2 (subst_bskl_in_bskel Q1 Xbs1 Q2)).
Proof.
apply_mutual_ind bskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_bskl_in_bskel_close_bskel_wrt_bskel_rec :
forall Q2 Q1 Xbs1 Xbs2 n1,
  degree_bskel_wrt_bskel n1 Q1 ->
  Xbs1 <> Xbs2 ->
  Xbs2 `notin` ftvar_in_bskel Q1 ->
  subst_bskl_in_bskel Q1 Xbs1 (close_bskel_wrt_bskel_rec n1 Xbs2 Q2) = close_bskel_wrt_bskel_rec n1 Xbs2 (subst_bskl_in_bskel Q1 Xbs1 Q2).
Proof.
pose proof subst_bskl_in_bskel_close_bskel_wrt_bskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bskl_in_bskel_close_bskel_wrt_bskel_rec : lngen.

(* begin hide *)

Lemma subst_bskl_in_uskel_close_uskel_wrt_uskel_rec_mutual :
(forall R2 R1 Xus1 Xus2 n1,
  degree_uskel_wrt_uskel n1 R1 ->
  Xus1 <> Xus2 ->
  Xus2 `notin` ftvar_in_uskel R1 ->
  subst_bskl_in_uskel R1 Xus1 (close_uskel_wrt_uskel_rec n1 Xus2 R2) = close_uskel_wrt_uskel_rec n1 Xus2 (subst_bskl_in_uskel R1 Xus1 R2)).
Proof.
apply_mutual_ind uskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_bskl_in_uskel_close_uskel_wrt_uskel_rec :
forall R2 R1 Xus1 Xus2 n1,
  degree_uskel_wrt_uskel n1 R1 ->
  Xus1 <> Xus2 ->
  Xus2 `notin` ftvar_in_uskel R1 ->
  subst_bskl_in_uskel R1 Xus1 (close_uskel_wrt_uskel_rec n1 Xus2 R2) = close_uskel_wrt_uskel_rec n1 Xus2 (subst_bskl_in_uskel R1 Xus1 R2).
Proof.
pose proof subst_bskl_in_uskel_close_uskel_wrt_uskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bskl_in_uskel_close_uskel_wrt_uskel_rec : lngen.

(* begin hide *)

Lemma subst_ptyp_in_exp_close_exp_wrt_ptyp_rec_mutual :
(forall e1 A1 Xpt1 Xpt2 n1,
  degree_ptyp_wrt_ptyp n1 A1 ->
  Xpt1 <> Xpt2 ->
  Xpt2 `notin` ftvar_in_ptyp A1 ->
  subst_ptyp_in_exp A1 Xpt1 (close_exp_wrt_ptyp_rec n1 Xpt2 e1) = close_exp_wrt_ptyp_rec n1 Xpt2 (subst_ptyp_in_exp A1 Xpt1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ptyp_in_exp_close_exp_wrt_ptyp_rec :
forall e1 A1 Xpt1 Xpt2 n1,
  degree_ptyp_wrt_ptyp n1 A1 ->
  Xpt1 <> Xpt2 ->
  Xpt2 `notin` ftvar_in_ptyp A1 ->
  subst_ptyp_in_exp A1 Xpt1 (close_exp_wrt_ptyp_rec n1 Xpt2 e1) = close_exp_wrt_ptyp_rec n1 Xpt2 (subst_ptyp_in_exp A1 Xpt1 e1).
Proof.
pose proof subst_ptyp_in_exp_close_exp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_close_exp_wrt_ptyp_rec : lngen.

(* begin hide *)

Lemma subst_ptyp_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 A1 x1 Xpt1 n1,
  subst_ptyp_in_exp A1 x1 (close_exp_wrt_exp_rec n1 Xpt1 e1) = close_exp_wrt_exp_rec n1 Xpt1 (subst_ptyp_in_exp A1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ptyp_in_exp_close_exp_wrt_exp_rec :
forall e1 A1 x1 Xpt1 n1,
  subst_ptyp_in_exp A1 x1 (close_exp_wrt_exp_rec n1 Xpt1 e1) = close_exp_wrt_exp_rec n1 Xpt1 (subst_ptyp_in_exp A1 x1 e1).
Proof.
pose proof subst_ptyp_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_close_exp_wrt_exp_rec : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_ptyp_rec_mutual :
(forall e2 e1 Xpt1 x1 n1,
  degree_exp_wrt_ptyp n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_exp e1 Xpt1 (close_exp_wrt_ptyp_rec n1 x1 e2) = close_exp_wrt_ptyp_rec n1 x1 (subst_exp_in_exp e1 Xpt1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_close_exp_wrt_ptyp_rec :
forall e2 e1 Xpt1 x1 n1,
  degree_exp_wrt_ptyp n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_exp e1 Xpt1 (close_exp_wrt_ptyp_rec n1 x1 e2) = close_exp_wrt_ptyp_rec n1 x1 (subst_exp_in_exp e1 Xpt1 e2).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_ptyp_rec : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_exp_in_exp e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (subst_exp_in_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_close_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_exp_in_exp e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (subst_exp_in_exp e1 x1 e2).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_exp_rec : lngen.

Lemma subst_ptyp_in_ptyp_close_ptyp_wrt_ptyp :
forall A2 A1 Xpt1 Xpt2,
  lc_ptyp A1 ->  Xpt1 <> Xpt2 ->
  Xpt2 `notin` ftvar_in_ptyp A1 ->
  subst_ptyp_in_ptyp A1 Xpt1 (close_ptyp_wrt_ptyp Xpt2 A2) = close_ptyp_wrt_ptyp Xpt2 (subst_ptyp_in_ptyp A1 Xpt1 A2).
Proof.
unfold close_ptyp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve subst_ptyp_in_ptyp_close_ptyp_wrt_ptyp : lngen.

Lemma subst_btyp_in_btyp_close_btyp_wrt_btyp :
forall B2 B1 Xbt1 Xbt2,
  lc_btyp B1 ->  Xbt1 <> Xbt2 ->
  Xbt2 `notin` ftvar_in_btyp B1 ->
  subst_btyp_in_btyp B1 Xbt1 (close_btyp_wrt_btyp Xbt2 B2) = close_btyp_wrt_btyp Xbt2 (subst_btyp_in_btyp B1 Xbt1 B2).
Proof.
unfold close_btyp_wrt_btyp; default_simp.
Qed.

#[export] Hint Resolve subst_btyp_in_btyp_close_btyp_wrt_btyp : lngen.

Lemma subst_utyp_in_utyp_close_utyp_wrt_utyp :
forall C2 C1 Xut1 Xut2,
  lc_utyp C1 ->  Xut1 <> Xut2 ->
  Xut2 `notin` ftvar_in_utyp C1 ->
  subst_utyp_in_utyp C1 Xut1 (close_utyp_wrt_utyp Xut2 C2) = close_utyp_wrt_utyp Xut2 (subst_utyp_in_utyp C1 Xut1 C2).
Proof.
unfold close_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_close_utyp_wrt_utyp : lngen.

Lemma subst_pskl_in_pskel_close_pskel_wrt_pskel :
forall P2 P1 Xps1 Xps2,
  lc_pskel P1 ->  Xps1 <> Xps2 ->
  Xps2 `notin` ftvar_in_pskel P1 ->
  subst_pskl_in_pskel P1 Xps1 (close_pskel_wrt_pskel Xps2 P2) = close_pskel_wrt_pskel Xps2 (subst_pskl_in_pskel P1 Xps1 P2).
Proof.
unfold close_pskel_wrt_pskel; default_simp.
Qed.

#[export] Hint Resolve subst_pskl_in_pskel_close_pskel_wrt_pskel : lngen.

Lemma subst_bskl_in_bskel_close_bskel_wrt_bskel :
forall Q2 Q1 Xbs1 Xbs2,
  lc_bskel Q1 ->  Xbs1 <> Xbs2 ->
  Xbs2 `notin` ftvar_in_bskel Q1 ->
  subst_bskl_in_bskel Q1 Xbs1 (close_bskel_wrt_bskel Xbs2 Q2) = close_bskel_wrt_bskel Xbs2 (subst_bskl_in_bskel Q1 Xbs1 Q2).
Proof.
unfold close_bskel_wrt_bskel; default_simp.
Qed.

#[export] Hint Resolve subst_bskl_in_bskel_close_bskel_wrt_bskel : lngen.

Lemma subst_bskl_in_uskel_close_uskel_wrt_uskel :
forall R2 R1 Xus1 Xus2,
  lc_uskel R1 ->  Xus1 <> Xus2 ->
  Xus2 `notin` ftvar_in_uskel R1 ->
  subst_bskl_in_uskel R1 Xus1 (close_uskel_wrt_uskel Xus2 R2) = close_uskel_wrt_uskel Xus2 (subst_bskl_in_uskel R1 Xus1 R2).
Proof.
unfold close_uskel_wrt_uskel; default_simp.
Qed.

#[export] Hint Resolve subst_bskl_in_uskel_close_uskel_wrt_uskel : lngen.

Lemma subst_ptyp_in_exp_close_exp_wrt_ptyp :
forall e1 A1 Xpt1 Xpt2,
  lc_ptyp A1 ->  Xpt1 <> Xpt2 ->
  Xpt2 `notin` ftvar_in_ptyp A1 ->
  subst_ptyp_in_exp A1 Xpt1 (close_exp_wrt_ptyp Xpt2 e1) = close_exp_wrt_ptyp Xpt2 (subst_ptyp_in_exp A1 Xpt1 e1).
Proof.
unfold close_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_close_exp_wrt_ptyp : lngen.

Lemma subst_ptyp_in_exp_close_exp_wrt_exp :
forall e1 A1 x1 Xpt1,
  lc_ptyp A1 ->  subst_ptyp_in_exp A1 x1 (close_exp_wrt_exp Xpt1 e1) = close_exp_wrt_exp Xpt1 (subst_ptyp_in_exp A1 x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_close_exp_wrt_exp : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_ptyp :
forall e2 e1 Xpt1 x1,
  lc_exp e1 ->  x1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_exp e1 Xpt1 (close_exp_wrt_ptyp x1 e2) = close_exp_wrt_ptyp x1 (subst_exp_in_exp e1 Xpt1 e2).
Proof.
unfold close_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_ptyp : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_exp :
forall e2 e1 x1 x2,
  lc_exp e1 ->  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_exp_in_exp e1 x1 (close_exp_wrt_exp x2 e2) = close_exp_wrt_exp x2 (subst_exp_in_exp e1 x1 e2).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_exp : lngen.

(* begin hide *)

Lemma subst_ptyp_in_ptyp_degree_ptyp_wrt_ptyp_mutual :
(forall A1 A2 Xpt1 n1,
  degree_ptyp_wrt_ptyp n1 A1 ->
  degree_ptyp_wrt_ptyp n1 A2 ->
  degree_ptyp_wrt_ptyp n1 (subst_ptyp_in_ptyp A2 Xpt1 A1)).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ptyp_in_ptyp_degree_ptyp_wrt_ptyp :
forall A1 A2 Xpt1 n1,
  degree_ptyp_wrt_ptyp n1 A1 ->
  degree_ptyp_wrt_ptyp n1 A2 ->
  degree_ptyp_wrt_ptyp n1 (subst_ptyp_in_ptyp A2 Xpt1 A1).
Proof.
pose proof subst_ptyp_in_ptyp_degree_ptyp_wrt_ptyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_ptyp_degree_ptyp_wrt_ptyp : lngen.

(* begin hide *)

Lemma subst_btyp_in_btyp_degree_btyp_wrt_btyp_mutual :
(forall B1 B2 Xbt1 n1,
  degree_btyp_wrt_btyp n1 B1 ->
  degree_btyp_wrt_btyp n1 B2 ->
  degree_btyp_wrt_btyp n1 (subst_btyp_in_btyp B2 Xbt1 B1)).
Proof.
apply_mutual_ind btyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_btyp_in_btyp_degree_btyp_wrt_btyp :
forall B1 B2 Xbt1 n1,
  degree_btyp_wrt_btyp n1 B1 ->
  degree_btyp_wrt_btyp n1 B2 ->
  degree_btyp_wrt_btyp n1 (subst_btyp_in_btyp B2 Xbt1 B1).
Proof.
pose proof subst_btyp_in_btyp_degree_btyp_wrt_btyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_btyp_in_btyp_degree_btyp_wrt_btyp : lngen.

(* begin hide *)

Lemma subst_utyp_in_utyp_degree_utyp_wrt_utyp_mutual :
(forall C1 C2 Xut1 n1,
  degree_utyp_wrt_utyp n1 C1 ->
  degree_utyp_wrt_utyp n1 C2 ->
  degree_utyp_wrt_utyp n1 (subst_utyp_in_utyp C2 Xut1 C1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_utyp_in_utyp_degree_utyp_wrt_utyp :
forall C1 C2 Xut1 n1,
  degree_utyp_wrt_utyp n1 C1 ->
  degree_utyp_wrt_utyp n1 C2 ->
  degree_utyp_wrt_utyp n1 (subst_utyp_in_utyp C2 Xut1 C1).
Proof.
pose proof subst_utyp_in_utyp_degree_utyp_wrt_utyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_degree_utyp_wrt_utyp : lngen.

(* begin hide *)

Lemma subst_pskl_in_pskel_degree_pskel_wrt_pskel_mutual :
(forall P1 P2 Xps1 n1,
  degree_pskel_wrt_pskel n1 P1 ->
  degree_pskel_wrt_pskel n1 P2 ->
  degree_pskel_wrt_pskel n1 (subst_pskl_in_pskel P2 Xps1 P1)).
Proof.
apply_mutual_ind pskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pskl_in_pskel_degree_pskel_wrt_pskel :
forall P1 P2 Xps1 n1,
  degree_pskel_wrt_pskel n1 P1 ->
  degree_pskel_wrt_pskel n1 P2 ->
  degree_pskel_wrt_pskel n1 (subst_pskl_in_pskel P2 Xps1 P1).
Proof.
pose proof subst_pskl_in_pskel_degree_pskel_wrt_pskel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pskl_in_pskel_degree_pskel_wrt_pskel : lngen.

(* begin hide *)

Lemma subst_bskl_in_bskel_degree_bskel_wrt_bskel_mutual :
(forall Q1 Q2 Xbs1 n1,
  degree_bskel_wrt_bskel n1 Q1 ->
  degree_bskel_wrt_bskel n1 Q2 ->
  degree_bskel_wrt_bskel n1 (subst_bskl_in_bskel Q2 Xbs1 Q1)).
Proof.
apply_mutual_ind bskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_bskl_in_bskel_degree_bskel_wrt_bskel :
forall Q1 Q2 Xbs1 n1,
  degree_bskel_wrt_bskel n1 Q1 ->
  degree_bskel_wrt_bskel n1 Q2 ->
  degree_bskel_wrt_bskel n1 (subst_bskl_in_bskel Q2 Xbs1 Q1).
Proof.
pose proof subst_bskl_in_bskel_degree_bskel_wrt_bskel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bskl_in_bskel_degree_bskel_wrt_bskel : lngen.

(* begin hide *)

Lemma subst_bskl_in_uskel_degree_uskel_wrt_uskel_mutual :
(forall R1 R2 Xus1 n1,
  degree_uskel_wrt_uskel n1 R1 ->
  degree_uskel_wrt_uskel n1 R2 ->
  degree_uskel_wrt_uskel n1 (subst_bskl_in_uskel R2 Xus1 R1)).
Proof.
apply_mutual_ind uskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_bskl_in_uskel_degree_uskel_wrt_uskel :
forall R1 R2 Xus1 n1,
  degree_uskel_wrt_uskel n1 R1 ->
  degree_uskel_wrt_uskel n1 R2 ->
  degree_uskel_wrt_uskel n1 (subst_bskl_in_uskel R2 Xus1 R1).
Proof.
pose proof subst_bskl_in_uskel_degree_uskel_wrt_uskel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bskl_in_uskel_degree_uskel_wrt_uskel : lngen.

(* begin hide *)

Lemma subst_ptyp_in_exp_degree_exp_wrt_ptyp_mutual :
(forall e1 A1 Xpt1 n1,
  degree_exp_wrt_ptyp n1 e1 ->
  degree_ptyp_wrt_ptyp n1 A1 ->
  degree_exp_wrt_ptyp n1 (subst_ptyp_in_exp A1 Xpt1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ptyp_in_exp_degree_exp_wrt_ptyp :
forall e1 A1 Xpt1 n1,
  degree_exp_wrt_ptyp n1 e1 ->
  degree_ptyp_wrt_ptyp n1 A1 ->
  degree_exp_wrt_ptyp n1 (subst_ptyp_in_exp A1 Xpt1 e1).
Proof.
pose proof subst_ptyp_in_exp_degree_exp_wrt_ptyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_degree_exp_wrt_ptyp : lngen.

(* begin hide *)

Lemma subst_ptyp_in_exp_degree_exp_wrt_exp_mutual :
(forall e1 A1 Xpt1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (subst_ptyp_in_exp A1 Xpt1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ptyp_in_exp_degree_exp_wrt_exp :
forall e1 A1 Xpt1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (subst_ptyp_in_exp A1 Xpt1 e1).
Proof.
pose proof subst_ptyp_in_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_ptyp_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_ptyp n1 e1 ->
  degree_exp_wrt_ptyp n1 e2 ->
  degree_exp_wrt_ptyp n1 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_ptyp :
forall e1 e2 x1 n1,
  degree_exp_wrt_ptyp n1 e1 ->
  degree_exp_wrt_ptyp n1 e2 ->
  degree_exp_wrt_ptyp n1 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_degree_exp_wrt_ptyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_degree_exp_wrt_ptyp : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_exp_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_exp :
forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma subst_ptyp_in_ptyp_fresh_eq_mutual :
(forall A2 A1 Xpt1,
  Xpt1 `notin` ftvar_in_ptyp A2 ->
  subst_ptyp_in_ptyp A1 Xpt1 A2 = A2).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ptyp_in_ptyp_fresh_eq :
forall A2 A1 Xpt1,
  Xpt1 `notin` ftvar_in_ptyp A2 ->
  subst_ptyp_in_ptyp A1 Xpt1 A2 = A2.
Proof.
pose proof subst_ptyp_in_ptyp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_ptyp_fresh_eq : lngen.
#[export] Hint Rewrite subst_ptyp_in_ptyp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_btyp_in_btyp_fresh_eq_mutual :
(forall B2 B1 Xbt1,
  Xbt1 `notin` ftvar_in_btyp B2 ->
  subst_btyp_in_btyp B1 Xbt1 B2 = B2).
Proof.
apply_mutual_ind btyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_btyp_in_btyp_fresh_eq :
forall B2 B1 Xbt1,
  Xbt1 `notin` ftvar_in_btyp B2 ->
  subst_btyp_in_btyp B1 Xbt1 B2 = B2.
Proof.
pose proof subst_btyp_in_btyp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_btyp_in_btyp_fresh_eq : lngen.
#[export] Hint Rewrite subst_btyp_in_btyp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_utyp_in_utyp_fresh_eq_mutual :
(forall C2 C1 Xut1,
  Xut1 `notin` ftvar_in_utyp C2 ->
  subst_utyp_in_utyp C1 Xut1 C2 = C2).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_utyp_in_utyp_fresh_eq :
forall C2 C1 Xut1,
  Xut1 `notin` ftvar_in_utyp C2 ->
  subst_utyp_in_utyp C1 Xut1 C2 = C2.
Proof.
pose proof subst_utyp_in_utyp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_fresh_eq : lngen.
#[export] Hint Rewrite subst_utyp_in_utyp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_pskl_in_pskel_fresh_eq_mutual :
(forall P2 P1 Xps1,
  Xps1 `notin` ftvar_in_pskel P2 ->
  subst_pskl_in_pskel P1 Xps1 P2 = P2).
Proof.
apply_mutual_ind pskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pskl_in_pskel_fresh_eq :
forall P2 P1 Xps1,
  Xps1 `notin` ftvar_in_pskel P2 ->
  subst_pskl_in_pskel P1 Xps1 P2 = P2.
Proof.
pose proof subst_pskl_in_pskel_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pskl_in_pskel_fresh_eq : lngen.
#[export] Hint Rewrite subst_pskl_in_pskel_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_bskl_in_bskel_fresh_eq_mutual :
(forall Q2 Q1 Xbs1,
  Xbs1 `notin` ftvar_in_bskel Q2 ->
  subst_bskl_in_bskel Q1 Xbs1 Q2 = Q2).
Proof.
apply_mutual_ind bskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_bskl_in_bskel_fresh_eq :
forall Q2 Q1 Xbs1,
  Xbs1 `notin` ftvar_in_bskel Q2 ->
  subst_bskl_in_bskel Q1 Xbs1 Q2 = Q2.
Proof.
pose proof subst_bskl_in_bskel_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bskl_in_bskel_fresh_eq : lngen.
#[export] Hint Rewrite subst_bskl_in_bskel_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_bskl_in_uskel_fresh_eq_mutual :
(forall R2 R1 Xus1,
  Xus1 `notin` ftvar_in_uskel R2 ->
  subst_bskl_in_uskel R1 Xus1 R2 = R2).
Proof.
apply_mutual_ind uskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_bskl_in_uskel_fresh_eq :
forall R2 R1 Xus1,
  Xus1 `notin` ftvar_in_uskel R2 ->
  subst_bskl_in_uskel R1 Xus1 R2 = R2.
Proof.
pose proof subst_bskl_in_uskel_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bskl_in_uskel_fresh_eq : lngen.
#[export] Hint Rewrite subst_bskl_in_uskel_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_ptyp_in_exp_fresh_eq_mutual :
(forall e1 A1 Xpt1,
  Xpt1 `notin` ftvar_in_exp e1 ->
  subst_ptyp_in_exp A1 Xpt1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ptyp_in_exp_fresh_eq :
forall e1 A1 Xpt1,
  Xpt1 `notin` ftvar_in_exp e1 ->
  subst_ptyp_in_exp A1 Xpt1 e1 = e1.
Proof.
pose proof subst_ptyp_in_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_fresh_eq : lngen.
#[export] Hint Rewrite subst_ptyp_in_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_fresh_eq_mutual :
(forall e2 e1 x1,
  x1 `notin` fvar_in_exp e2 ->
  subst_exp_in_exp e1 x1 e2 = e2).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_fresh_eq :
forall e2 e1 x1,
  x1 `notin` fvar_in_exp e2 ->
  subst_exp_in_exp e1 x1 e2 = e2.
Proof.
pose proof subst_exp_in_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_fresh_eq : lngen.
#[export] Hint Rewrite subst_exp_in_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_ptyp_in_ptyp_fresh_same_mutual :
(forall A2 A1 Xpt1,
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  Xpt1 `notin` ftvar_in_ptyp (subst_ptyp_in_ptyp A1 Xpt1 A2)).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ptyp_in_ptyp_fresh_same :
forall A2 A1 Xpt1,
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  Xpt1 `notin` ftvar_in_ptyp (subst_ptyp_in_ptyp A1 Xpt1 A2).
Proof.
pose proof subst_ptyp_in_ptyp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_ptyp_fresh_same : lngen.

(* begin hide *)

Lemma subst_btyp_in_btyp_fresh_same_mutual :
(forall B2 B1 Xbt1,
  Xbt1 `notin` ftvar_in_btyp B1 ->
  Xbt1 `notin` ftvar_in_btyp (subst_btyp_in_btyp B1 Xbt1 B2)).
Proof.
apply_mutual_ind btyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_btyp_in_btyp_fresh_same :
forall B2 B1 Xbt1,
  Xbt1 `notin` ftvar_in_btyp B1 ->
  Xbt1 `notin` ftvar_in_btyp (subst_btyp_in_btyp B1 Xbt1 B2).
Proof.
pose proof subst_btyp_in_btyp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_btyp_in_btyp_fresh_same : lngen.

(* begin hide *)

Lemma subst_utyp_in_utyp_fresh_same_mutual :
(forall C2 C1 Xut1,
  Xut1 `notin` ftvar_in_utyp C1 ->
  Xut1 `notin` ftvar_in_utyp (subst_utyp_in_utyp C1 Xut1 C2)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_utyp_in_utyp_fresh_same :
forall C2 C1 Xut1,
  Xut1 `notin` ftvar_in_utyp C1 ->
  Xut1 `notin` ftvar_in_utyp (subst_utyp_in_utyp C1 Xut1 C2).
Proof.
pose proof subst_utyp_in_utyp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_fresh_same : lngen.

(* begin hide *)

Lemma subst_pskl_in_pskel_fresh_same_mutual :
(forall P2 P1 Xps1,
  Xps1 `notin` ftvar_in_pskel P1 ->
  Xps1 `notin` ftvar_in_pskel (subst_pskl_in_pskel P1 Xps1 P2)).
Proof.
apply_mutual_ind pskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pskl_in_pskel_fresh_same :
forall P2 P1 Xps1,
  Xps1 `notin` ftvar_in_pskel P1 ->
  Xps1 `notin` ftvar_in_pskel (subst_pskl_in_pskel P1 Xps1 P2).
Proof.
pose proof subst_pskl_in_pskel_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pskl_in_pskel_fresh_same : lngen.

(* begin hide *)

Lemma subst_bskl_in_bskel_fresh_same_mutual :
(forall Q2 Q1 Xbs1,
  Xbs1 `notin` ftvar_in_bskel Q1 ->
  Xbs1 `notin` ftvar_in_bskel (subst_bskl_in_bskel Q1 Xbs1 Q2)).
Proof.
apply_mutual_ind bskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_bskl_in_bskel_fresh_same :
forall Q2 Q1 Xbs1,
  Xbs1 `notin` ftvar_in_bskel Q1 ->
  Xbs1 `notin` ftvar_in_bskel (subst_bskl_in_bskel Q1 Xbs1 Q2).
Proof.
pose proof subst_bskl_in_bskel_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bskl_in_bskel_fresh_same : lngen.

(* begin hide *)

Lemma subst_bskl_in_uskel_fresh_same_mutual :
(forall R2 R1 Xus1,
  Xus1 `notin` ftvar_in_uskel R1 ->
  Xus1 `notin` ftvar_in_uskel (subst_bskl_in_uskel R1 Xus1 R2)).
Proof.
apply_mutual_ind uskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_bskl_in_uskel_fresh_same :
forall R2 R1 Xus1,
  Xus1 `notin` ftvar_in_uskel R1 ->
  Xus1 `notin` ftvar_in_uskel (subst_bskl_in_uskel R1 Xus1 R2).
Proof.
pose proof subst_bskl_in_uskel_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bskl_in_uskel_fresh_same : lngen.

(* begin hide *)

Lemma subst_ptyp_in_exp_fresh_same_mutual :
(forall e1 A1 Xpt1,
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  Xpt1 `notin` ftvar_in_exp (subst_ptyp_in_exp A1 Xpt1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ptyp_in_exp_fresh_same :
forall e1 A1 Xpt1,
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  Xpt1 `notin` ftvar_in_exp (subst_ptyp_in_exp A1 Xpt1 e1).
Proof.
pose proof subst_ptyp_in_exp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_fresh_same : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_fresh_same_mutual :
(forall e2 e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_exp_in_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_fresh_same :
forall e2 e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_exp_in_exp e1 x1 e2).
Proof.
pose proof subst_exp_in_exp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_fresh_same : lngen.

(* begin hide *)

Lemma subst_ptyp_in_ptyp_fresh_mutual :
(forall A2 A1 Xpt1 Xpt2,
  Xpt1 `notin` ftvar_in_ptyp A2 ->
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  Xpt1 `notin` ftvar_in_ptyp (subst_ptyp_in_ptyp A1 Xpt2 A2)).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ptyp_in_ptyp_fresh :
forall A2 A1 Xpt1 Xpt2,
  Xpt1 `notin` ftvar_in_ptyp A2 ->
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  Xpt1 `notin` ftvar_in_ptyp (subst_ptyp_in_ptyp A1 Xpt2 A2).
Proof.
pose proof subst_ptyp_in_ptyp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_ptyp_fresh : lngen.

(* begin hide *)

Lemma subst_btyp_in_btyp_fresh_mutual :
(forall B2 B1 Xbt1 Xbt2,
  Xbt1 `notin` ftvar_in_btyp B2 ->
  Xbt1 `notin` ftvar_in_btyp B1 ->
  Xbt1 `notin` ftvar_in_btyp (subst_btyp_in_btyp B1 Xbt2 B2)).
Proof.
apply_mutual_ind btyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_btyp_in_btyp_fresh :
forall B2 B1 Xbt1 Xbt2,
  Xbt1 `notin` ftvar_in_btyp B2 ->
  Xbt1 `notin` ftvar_in_btyp B1 ->
  Xbt1 `notin` ftvar_in_btyp (subst_btyp_in_btyp B1 Xbt2 B2).
Proof.
pose proof subst_btyp_in_btyp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_btyp_in_btyp_fresh : lngen.

(* begin hide *)

Lemma subst_utyp_in_utyp_fresh_mutual :
(forall C2 C1 Xut1 Xut2,
  Xut1 `notin` ftvar_in_utyp C2 ->
  Xut1 `notin` ftvar_in_utyp C1 ->
  Xut1 `notin` ftvar_in_utyp (subst_utyp_in_utyp C1 Xut2 C2)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_utyp_in_utyp_fresh :
forall C2 C1 Xut1 Xut2,
  Xut1 `notin` ftvar_in_utyp C2 ->
  Xut1 `notin` ftvar_in_utyp C1 ->
  Xut1 `notin` ftvar_in_utyp (subst_utyp_in_utyp C1 Xut2 C2).
Proof.
pose proof subst_utyp_in_utyp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_fresh : lngen.

(* begin hide *)

Lemma subst_pskl_in_pskel_fresh_mutual :
(forall P2 P1 Xps1 Xps2,
  Xps1 `notin` ftvar_in_pskel P2 ->
  Xps1 `notin` ftvar_in_pskel P1 ->
  Xps1 `notin` ftvar_in_pskel (subst_pskl_in_pskel P1 Xps2 P2)).
Proof.
apply_mutual_ind pskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pskl_in_pskel_fresh :
forall P2 P1 Xps1 Xps2,
  Xps1 `notin` ftvar_in_pskel P2 ->
  Xps1 `notin` ftvar_in_pskel P1 ->
  Xps1 `notin` ftvar_in_pskel (subst_pskl_in_pskel P1 Xps2 P2).
Proof.
pose proof subst_pskl_in_pskel_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pskl_in_pskel_fresh : lngen.

(* begin hide *)

Lemma subst_bskl_in_bskel_fresh_mutual :
(forall Q2 Q1 Xbs1 Xbs2,
  Xbs1 `notin` ftvar_in_bskel Q2 ->
  Xbs1 `notin` ftvar_in_bskel Q1 ->
  Xbs1 `notin` ftvar_in_bskel (subst_bskl_in_bskel Q1 Xbs2 Q2)).
Proof.
apply_mutual_ind bskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_bskl_in_bskel_fresh :
forall Q2 Q1 Xbs1 Xbs2,
  Xbs1 `notin` ftvar_in_bskel Q2 ->
  Xbs1 `notin` ftvar_in_bskel Q1 ->
  Xbs1 `notin` ftvar_in_bskel (subst_bskl_in_bskel Q1 Xbs2 Q2).
Proof.
pose proof subst_bskl_in_bskel_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bskl_in_bskel_fresh : lngen.

(* begin hide *)

Lemma subst_bskl_in_uskel_fresh_mutual :
(forall R2 R1 Xus1 Xus2,
  Xus1 `notin` ftvar_in_uskel R2 ->
  Xus1 `notin` ftvar_in_uskel R1 ->
  Xus1 `notin` ftvar_in_uskel (subst_bskl_in_uskel R1 Xus2 R2)).
Proof.
apply_mutual_ind uskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_bskl_in_uskel_fresh :
forall R2 R1 Xus1 Xus2,
  Xus1 `notin` ftvar_in_uskel R2 ->
  Xus1 `notin` ftvar_in_uskel R1 ->
  Xus1 `notin` ftvar_in_uskel (subst_bskl_in_uskel R1 Xus2 R2).
Proof.
pose proof subst_bskl_in_uskel_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bskl_in_uskel_fresh : lngen.

(* begin hide *)

Lemma subst_ptyp_in_exp_fresh_mutual :
(forall e1 A1 Xpt1 Xpt2,
  Xpt1 `notin` ftvar_in_exp e1 ->
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  Xpt1 `notin` ftvar_in_exp (subst_ptyp_in_exp A1 Xpt2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ptyp_in_exp_fresh :
forall e1 A1 Xpt1 Xpt2,
  Xpt1 `notin` ftvar_in_exp e1 ->
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  Xpt1 `notin` ftvar_in_exp (subst_ptyp_in_exp A1 Xpt2 e1).
Proof.
pose proof subst_ptyp_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_fresh : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_fresh_mutual :
(forall e2 e1 x1 x2,
  x1 `notin` fvar_in_exp e2 ->
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_exp_in_exp e1 x2 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_fresh :
forall e2 e1 x1 x2,
  x1 `notin` fvar_in_exp e2 ->
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_exp_in_exp e1 x2 e2).
Proof.
pose proof subst_exp_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_fresh : lngen.

Lemma subst_ptyp_in_ptyp_lc_ptyp :
forall A1 A2 Xpt1,
  lc_ptyp A1 ->
  lc_ptyp A2 ->
  lc_ptyp (subst_ptyp_in_ptyp A2 Xpt1 A1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_ptyp_in_ptyp_lc_ptyp : lngen.

Lemma subst_btyp_in_btyp_lc_btyp :
forall B1 B2 Xbt1,
  lc_btyp B1 ->
  lc_btyp B2 ->
  lc_btyp (subst_btyp_in_btyp B2 Xbt1 B1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_btyp_in_btyp_lc_btyp : lngen.

Lemma subst_utyp_in_utyp_lc_utyp :
forall C1 C2 Xut1,
  lc_utyp C1 ->
  lc_utyp C2 ->
  lc_utyp (subst_utyp_in_utyp C2 Xut1 C1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_lc_utyp : lngen.

Lemma subst_pskl_in_pskel_lc_pskel :
forall P1 P2 Xps1,
  lc_pskel P1 ->
  lc_pskel P2 ->
  lc_pskel (subst_pskl_in_pskel P2 Xps1 P1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_pskl_in_pskel_lc_pskel : lngen.

Lemma subst_bskl_in_bskel_lc_bskel :
forall Q1 Q2 Xbs1,
  lc_bskel Q1 ->
  lc_bskel Q2 ->
  lc_bskel (subst_bskl_in_bskel Q2 Xbs1 Q1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_bskl_in_bskel_lc_bskel : lngen.

Lemma subst_bskl_in_uskel_lc_uskel :
forall R1 R2 Xus1,
  lc_uskel R1 ->
  lc_uskel R2 ->
  lc_uskel (subst_bskl_in_uskel R2 Xus1 R1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_bskl_in_uskel_lc_uskel : lngen.

Lemma subst_ptyp_in_exp_lc_exp :
forall e1 A1 Xpt1,
  lc_exp e1 ->
  lc_ptyp A1 ->
  lc_exp (subst_ptyp_in_exp A1 Xpt1 e1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_lc_exp : lngen.

Lemma subst_exp_in_exp_lc_exp :
forall e1 e2 x1,
  lc_exp e1 ->
  lc_exp e2 ->
  lc_exp (subst_exp_in_exp e2 x1 e1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_lc_exp : lngen.

(* begin hide *)

Lemma subst_ptyp_in_ptyp_open_ptyp_wrt_ptyp_rec_mutual :
(forall A3 A1 A2 Xpt1 n1,
  lc_ptyp A1 ->
  subst_ptyp_in_ptyp A1 Xpt1 (open_ptyp_wrt_ptyp_rec n1 A2 A3) = open_ptyp_wrt_ptyp_rec n1 (subst_ptyp_in_ptyp A1 Xpt1 A2) (subst_ptyp_in_ptyp A1 Xpt1 A3)).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ptyp_in_ptyp_open_ptyp_wrt_ptyp_rec :
forall A3 A1 A2 Xpt1 n1,
  lc_ptyp A1 ->
  subst_ptyp_in_ptyp A1 Xpt1 (open_ptyp_wrt_ptyp_rec n1 A2 A3) = open_ptyp_wrt_ptyp_rec n1 (subst_ptyp_in_ptyp A1 Xpt1 A2) (subst_ptyp_in_ptyp A1 Xpt1 A3).
Proof.
pose proof subst_ptyp_in_ptyp_open_ptyp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_ptyp_open_ptyp_wrt_ptyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_btyp_in_btyp_open_btyp_wrt_btyp_rec_mutual :
(forall B3 B1 B2 Xbt1 n1,
  lc_btyp B1 ->
  subst_btyp_in_btyp B1 Xbt1 (open_btyp_wrt_btyp_rec n1 B2 B3) = open_btyp_wrt_btyp_rec n1 (subst_btyp_in_btyp B1 Xbt1 B2) (subst_btyp_in_btyp B1 Xbt1 B3)).
Proof.
apply_mutual_ind btyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_btyp_in_btyp_open_btyp_wrt_btyp_rec :
forall B3 B1 B2 Xbt1 n1,
  lc_btyp B1 ->
  subst_btyp_in_btyp B1 Xbt1 (open_btyp_wrt_btyp_rec n1 B2 B3) = open_btyp_wrt_btyp_rec n1 (subst_btyp_in_btyp B1 Xbt1 B2) (subst_btyp_in_btyp B1 Xbt1 B3).
Proof.
pose proof subst_btyp_in_btyp_open_btyp_wrt_btyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_btyp_in_btyp_open_btyp_wrt_btyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_utyp_in_utyp_open_utyp_wrt_utyp_rec_mutual :
(forall C3 C1 C2 Xut1 n1,
  lc_utyp C1 ->
  subst_utyp_in_utyp C1 Xut1 (open_utyp_wrt_utyp_rec n1 C2 C3) = open_utyp_wrt_utyp_rec n1 (subst_utyp_in_utyp C1 Xut1 C2) (subst_utyp_in_utyp C1 Xut1 C3)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_utyp_in_utyp_open_utyp_wrt_utyp_rec :
forall C3 C1 C2 Xut1 n1,
  lc_utyp C1 ->
  subst_utyp_in_utyp C1 Xut1 (open_utyp_wrt_utyp_rec n1 C2 C3) = open_utyp_wrt_utyp_rec n1 (subst_utyp_in_utyp C1 Xut1 C2) (subst_utyp_in_utyp C1 Xut1 C3).
Proof.
pose proof subst_utyp_in_utyp_open_utyp_wrt_utyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_open_utyp_wrt_utyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_pskl_in_pskel_open_pskel_wrt_pskel_rec_mutual :
(forall P3 P1 P2 Xps1 n1,
  lc_pskel P1 ->
  subst_pskl_in_pskel P1 Xps1 (open_pskel_wrt_pskel_rec n1 P2 P3) = open_pskel_wrt_pskel_rec n1 (subst_pskl_in_pskel P1 Xps1 P2) (subst_pskl_in_pskel P1 Xps1 P3)).
Proof.
apply_mutual_ind pskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_pskl_in_pskel_open_pskel_wrt_pskel_rec :
forall P3 P1 P2 Xps1 n1,
  lc_pskel P1 ->
  subst_pskl_in_pskel P1 Xps1 (open_pskel_wrt_pskel_rec n1 P2 P3) = open_pskel_wrt_pskel_rec n1 (subst_pskl_in_pskel P1 Xps1 P2) (subst_pskl_in_pskel P1 Xps1 P3).
Proof.
pose proof subst_pskl_in_pskel_open_pskel_wrt_pskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pskl_in_pskel_open_pskel_wrt_pskel_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_bskl_in_bskel_open_bskel_wrt_bskel_rec_mutual :
(forall Q3 Q1 Q2 Xbs1 n1,
  lc_bskel Q1 ->
  subst_bskl_in_bskel Q1 Xbs1 (open_bskel_wrt_bskel_rec n1 Q2 Q3) = open_bskel_wrt_bskel_rec n1 (subst_bskl_in_bskel Q1 Xbs1 Q2) (subst_bskl_in_bskel Q1 Xbs1 Q3)).
Proof.
apply_mutual_ind bskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_bskl_in_bskel_open_bskel_wrt_bskel_rec :
forall Q3 Q1 Q2 Xbs1 n1,
  lc_bskel Q1 ->
  subst_bskl_in_bskel Q1 Xbs1 (open_bskel_wrt_bskel_rec n1 Q2 Q3) = open_bskel_wrt_bskel_rec n1 (subst_bskl_in_bskel Q1 Xbs1 Q2) (subst_bskl_in_bskel Q1 Xbs1 Q3).
Proof.
pose proof subst_bskl_in_bskel_open_bskel_wrt_bskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bskl_in_bskel_open_bskel_wrt_bskel_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_bskl_in_uskel_open_uskel_wrt_uskel_rec_mutual :
(forall R3 R1 R2 Xus1 n1,
  lc_uskel R1 ->
  subst_bskl_in_uskel R1 Xus1 (open_uskel_wrt_uskel_rec n1 R2 R3) = open_uskel_wrt_uskel_rec n1 (subst_bskl_in_uskel R1 Xus1 R2) (subst_bskl_in_uskel R1 Xus1 R3)).
Proof.
apply_mutual_ind uskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_bskl_in_uskel_open_uskel_wrt_uskel_rec :
forall R3 R1 R2 Xus1 n1,
  lc_uskel R1 ->
  subst_bskl_in_uskel R1 Xus1 (open_uskel_wrt_uskel_rec n1 R2 R3) = open_uskel_wrt_uskel_rec n1 (subst_bskl_in_uskel R1 Xus1 R2) (subst_bskl_in_uskel R1 Xus1 R3).
Proof.
pose proof subst_bskl_in_uskel_open_uskel_wrt_uskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bskl_in_uskel_open_uskel_wrt_uskel_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ptyp_in_exp_open_exp_wrt_ptyp_rec_mutual :
(forall e1 A1 A2 Xpt1 n1,
  lc_ptyp A1 ->
  subst_ptyp_in_exp A1 Xpt1 (open_exp_wrt_ptyp_rec n1 A2 e1) = open_exp_wrt_ptyp_rec n1 (subst_ptyp_in_ptyp A1 Xpt1 A2) (subst_ptyp_in_exp A1 Xpt1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ptyp_in_exp_open_exp_wrt_ptyp_rec :
forall e1 A1 A2 Xpt1 n1,
  lc_ptyp A1 ->
  subst_ptyp_in_exp A1 Xpt1 (open_exp_wrt_ptyp_rec n1 A2 e1) = open_exp_wrt_ptyp_rec n1 (subst_ptyp_in_ptyp A1 Xpt1 A2) (subst_ptyp_in_exp A1 Xpt1 e1).
Proof.
pose proof subst_ptyp_in_exp_open_exp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_open_exp_wrt_ptyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ptyp_in_exp_open_exp_wrt_exp_rec_mutual :
(forall e2 A1 e1 Xpt1 n1,
  subst_ptyp_in_exp A1 Xpt1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (subst_ptyp_in_exp A1 Xpt1 e1) (subst_ptyp_in_exp A1 Xpt1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ptyp_in_exp_open_exp_wrt_exp_rec :
forall e2 A1 e1 Xpt1 n1,
  subst_ptyp_in_exp A1 Xpt1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (subst_ptyp_in_exp A1 Xpt1 e1) (subst_ptyp_in_exp A1 Xpt1 e2).
Proof.
pose proof subst_ptyp_in_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_ptyp_rec_mutual :
(forall e2 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_ptyp_rec n1 A1 e2) = open_exp_wrt_ptyp_rec n1 A1 (subst_exp_in_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_ptyp_rec :
forall e2 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_ptyp_rec n1 A1 e2) = open_exp_wrt_ptyp_rec n1 A1 (subst_exp_in_exp e1 x1 e2).
Proof.
pose proof subst_exp_in_exp_open_exp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_ptyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_exp_rec_mutual :
(forall e3 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_exp_rec n1 e2 e3) = open_exp_wrt_exp_rec n1 (subst_exp_in_exp e1 x1 e2) (subst_exp_in_exp e1 x1 e3)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_exp_rec :
forall e3 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_exp_rec n1 e2 e3) = open_exp_wrt_exp_rec n1 (subst_exp_in_exp e1 x1 e2) (subst_exp_in_exp e1 x1 e3).
Proof.
pose proof subst_exp_in_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma subst_ptyp_in_ptyp_open_ptyp_wrt_ptyp :
forall A3 A1 A2 Xpt1,
  lc_ptyp A1 ->
  subst_ptyp_in_ptyp A1 Xpt1 (open_ptyp_wrt_ptyp A3 A2) = open_ptyp_wrt_ptyp (subst_ptyp_in_ptyp A1 Xpt1 A3) (subst_ptyp_in_ptyp A1 Xpt1 A2).
Proof.
unfold open_ptyp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve subst_ptyp_in_ptyp_open_ptyp_wrt_ptyp : lngen.

Lemma subst_btyp_in_btyp_open_btyp_wrt_btyp :
forall B3 B1 B2 Xbt1,
  lc_btyp B1 ->
  subst_btyp_in_btyp B1 Xbt1 (open_btyp_wrt_btyp B3 B2) = open_btyp_wrt_btyp (subst_btyp_in_btyp B1 Xbt1 B3) (subst_btyp_in_btyp B1 Xbt1 B2).
Proof.
unfold open_btyp_wrt_btyp; default_simp.
Qed.

#[export] Hint Resolve subst_btyp_in_btyp_open_btyp_wrt_btyp : lngen.

Lemma subst_utyp_in_utyp_open_utyp_wrt_utyp :
forall C3 C1 C2 Xut1,
  lc_utyp C1 ->
  subst_utyp_in_utyp C1 Xut1 (open_utyp_wrt_utyp C3 C2) = open_utyp_wrt_utyp (subst_utyp_in_utyp C1 Xut1 C3) (subst_utyp_in_utyp C1 Xut1 C2).
Proof.
unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_open_utyp_wrt_utyp : lngen.

Lemma subst_pskl_in_pskel_open_pskel_wrt_pskel :
forall P3 P1 P2 Xps1,
  lc_pskel P1 ->
  subst_pskl_in_pskel P1 Xps1 (open_pskel_wrt_pskel P3 P2) = open_pskel_wrt_pskel (subst_pskl_in_pskel P1 Xps1 P3) (subst_pskl_in_pskel P1 Xps1 P2).
Proof.
unfold open_pskel_wrt_pskel; default_simp.
Qed.

#[export] Hint Resolve subst_pskl_in_pskel_open_pskel_wrt_pskel : lngen.

Lemma subst_bskl_in_bskel_open_bskel_wrt_bskel :
forall Q3 Q1 Q2 Xbs1,
  lc_bskel Q1 ->
  subst_bskl_in_bskel Q1 Xbs1 (open_bskel_wrt_bskel Q3 Q2) = open_bskel_wrt_bskel (subst_bskl_in_bskel Q1 Xbs1 Q3) (subst_bskl_in_bskel Q1 Xbs1 Q2).
Proof.
unfold open_bskel_wrt_bskel; default_simp.
Qed.

#[export] Hint Resolve subst_bskl_in_bskel_open_bskel_wrt_bskel : lngen.

Lemma subst_bskl_in_uskel_open_uskel_wrt_uskel :
forall R3 R1 R2 Xus1,
  lc_uskel R1 ->
  subst_bskl_in_uskel R1 Xus1 (open_uskel_wrt_uskel R3 R2) = open_uskel_wrt_uskel (subst_bskl_in_uskel R1 Xus1 R3) (subst_bskl_in_uskel R1 Xus1 R2).
Proof.
unfold open_uskel_wrt_uskel; default_simp.
Qed.

#[export] Hint Resolve subst_bskl_in_uskel_open_uskel_wrt_uskel : lngen.

Lemma subst_ptyp_in_exp_open_exp_wrt_ptyp :
forall e1 A1 A2 Xpt1,
  lc_ptyp A1 ->
  subst_ptyp_in_exp A1 Xpt1 (open_exp_wrt_ptyp e1 A2) = open_exp_wrt_ptyp (subst_ptyp_in_exp A1 Xpt1 e1) (subst_ptyp_in_ptyp A1 Xpt1 A2).
Proof.
unfold open_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_open_exp_wrt_ptyp : lngen.

Lemma subst_ptyp_in_exp_open_exp_wrt_exp :
forall e2 A1 e1 Xpt1,
  subst_ptyp_in_exp A1 Xpt1 (open_exp_wrt_exp e2 e1) = open_exp_wrt_exp (subst_ptyp_in_exp A1 Xpt1 e2) (subst_ptyp_in_exp A1 Xpt1 e1).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_ptyp :
forall e2 e1 A1 x1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_ptyp e2 A1) = open_exp_wrt_ptyp (subst_exp_in_exp e1 x1 e2) A1.
Proof.
unfold open_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_ptyp : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_exp :
forall e3 e1 e2 x1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_exp e3 e2) = open_exp_wrt_exp (subst_exp_in_exp e1 x1 e3) (subst_exp_in_exp e1 x1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_exp : lngen.

Lemma subst_ptyp_in_ptyp_open_ptyp_wrt_ptyp_var :
forall A2 A1 Xpt1 Xpt2,
  Xpt1 <> Xpt2 ->
  lc_ptyp A1 ->
  open_ptyp_wrt_ptyp (subst_ptyp_in_ptyp A1 Xpt1 A2) (ptyp_var_f Xpt2) = subst_ptyp_in_ptyp A1 Xpt1 (open_ptyp_wrt_ptyp A2 (ptyp_var_f Xpt2)).
Proof.
intros; rewrite subst_ptyp_in_ptyp_open_ptyp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve subst_ptyp_in_ptyp_open_ptyp_wrt_ptyp_var : lngen.

Lemma subst_btyp_in_btyp_open_btyp_wrt_btyp_var :
forall B2 B1 Xbt1 Xbt2,
  Xbt1 <> Xbt2 ->
  lc_btyp B1 ->
  open_btyp_wrt_btyp (subst_btyp_in_btyp B1 Xbt1 B2) (btyp_var_f Xbt2) = subst_btyp_in_btyp B1 Xbt1 (open_btyp_wrt_btyp B2 (btyp_var_f Xbt2)).
Proof.
intros; rewrite subst_btyp_in_btyp_open_btyp_wrt_btyp; default_simp.
Qed.

#[export] Hint Resolve subst_btyp_in_btyp_open_btyp_wrt_btyp_var : lngen.

Lemma subst_utyp_in_utyp_open_utyp_wrt_utyp_var :
forall C2 C1 Xut1 Xut2,
  Xut1 <> Xut2 ->
  lc_utyp C1 ->
  open_utyp_wrt_utyp (subst_utyp_in_utyp C1 Xut1 C2) (utyp_var_f Xut2) = subst_utyp_in_utyp C1 Xut1 (open_utyp_wrt_utyp C2 (utyp_var_f Xut2)).
Proof.
intros; rewrite subst_utyp_in_utyp_open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_open_utyp_wrt_utyp_var : lngen.

Lemma subst_pskl_in_pskel_open_pskel_wrt_pskel_var :
forall P2 P1 Xps1 Xps2,
  Xps1 <> Xps2 ->
  lc_pskel P1 ->
  open_pskel_wrt_pskel (subst_pskl_in_pskel P1 Xps1 P2) (pskel_var_f Xps2) = subst_pskl_in_pskel P1 Xps1 (open_pskel_wrt_pskel P2 (pskel_var_f Xps2)).
Proof.
intros; rewrite subst_pskl_in_pskel_open_pskel_wrt_pskel; default_simp.
Qed.

#[export] Hint Resolve subst_pskl_in_pskel_open_pskel_wrt_pskel_var : lngen.

Lemma subst_bskl_in_bskel_open_bskel_wrt_bskel_var :
forall Q2 Q1 Xbs1 Xbs2,
  Xbs1 <> Xbs2 ->
  lc_bskel Q1 ->
  open_bskel_wrt_bskel (subst_bskl_in_bskel Q1 Xbs1 Q2) (bskel_var_f Xbs2) = subst_bskl_in_bskel Q1 Xbs1 (open_bskel_wrt_bskel Q2 (bskel_var_f Xbs2)).
Proof.
intros; rewrite subst_bskl_in_bskel_open_bskel_wrt_bskel; default_simp.
Qed.

#[export] Hint Resolve subst_bskl_in_bskel_open_bskel_wrt_bskel_var : lngen.

Lemma subst_bskl_in_uskel_open_uskel_wrt_uskel_var :
forall R2 R1 Xus1 Xus2,
  Xus1 <> Xus2 ->
  lc_uskel R1 ->
  open_uskel_wrt_uskel (subst_bskl_in_uskel R1 Xus1 R2) (uskel_var_f Xus2) = subst_bskl_in_uskel R1 Xus1 (open_uskel_wrt_uskel R2 (uskel_var_f Xus2)).
Proof.
intros; rewrite subst_bskl_in_uskel_open_uskel_wrt_uskel; default_simp.
Qed.

#[export] Hint Resolve subst_bskl_in_uskel_open_uskel_wrt_uskel_var : lngen.

Lemma subst_ptyp_in_exp_open_exp_wrt_ptyp_var :
forall e1 A1 Xpt1 Xpt2,
  Xpt1 <> Xpt2 ->
  lc_ptyp A1 ->
  open_exp_wrt_ptyp (subst_ptyp_in_exp A1 Xpt1 e1) (ptyp_var_f Xpt2) = subst_ptyp_in_exp A1 Xpt1 (open_exp_wrt_ptyp e1 (ptyp_var_f Xpt2)).
Proof.
intros; rewrite subst_ptyp_in_exp_open_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_open_exp_wrt_ptyp_var : lngen.

Lemma subst_ptyp_in_exp_open_exp_wrt_exp_var :
forall e1 A1 Xpt1 x1,
  open_exp_wrt_exp (subst_ptyp_in_exp A1 Xpt1 e1) (exp_var_f x1) = subst_ptyp_in_exp A1 Xpt1 (open_exp_wrt_exp e1 (exp_var_f x1)).
Proof.
intros; rewrite subst_ptyp_in_exp_open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_open_exp_wrt_exp_var : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_ptyp_var :
forall e2 e1 x1 Xpt1,
  lc_exp e1 ->
  open_exp_wrt_ptyp (subst_exp_in_exp e1 x1 e2) (ptyp_var_f Xpt1) = subst_exp_in_exp e1 x1 (open_exp_wrt_ptyp e2 (ptyp_var_f Xpt1)).
Proof.
intros; rewrite subst_exp_in_exp_open_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_ptyp_var : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_exp_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_exp e1 ->
  open_exp_wrt_exp (subst_exp_in_exp e1 x1 e2) (exp_var_f x2) = subst_exp_in_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2)).
Proof.
intros; rewrite subst_exp_in_exp_open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_exp_var : lngen.

(* begin hide *)

Lemma subst_ptyp_in_ptyp_spec_rec_mutual :
(forall A1 A2 Xpt1 n1,
  subst_ptyp_in_ptyp A2 Xpt1 A1 = open_ptyp_wrt_ptyp_rec n1 A2 (close_ptyp_wrt_ptyp_rec n1 Xpt1 A1)).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ptyp_in_ptyp_spec_rec :
forall A1 A2 Xpt1 n1,
  subst_ptyp_in_ptyp A2 Xpt1 A1 = open_ptyp_wrt_ptyp_rec n1 A2 (close_ptyp_wrt_ptyp_rec n1 Xpt1 A1).
Proof.
pose proof subst_ptyp_in_ptyp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_ptyp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_btyp_in_btyp_spec_rec_mutual :
(forall B1 B2 Xbt1 n1,
  subst_btyp_in_btyp B2 Xbt1 B1 = open_btyp_wrt_btyp_rec n1 B2 (close_btyp_wrt_btyp_rec n1 Xbt1 B1)).
Proof.
apply_mutual_ind btyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_btyp_in_btyp_spec_rec :
forall B1 B2 Xbt1 n1,
  subst_btyp_in_btyp B2 Xbt1 B1 = open_btyp_wrt_btyp_rec n1 B2 (close_btyp_wrt_btyp_rec n1 Xbt1 B1).
Proof.
pose proof subst_btyp_in_btyp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_btyp_in_btyp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_utyp_in_utyp_spec_rec_mutual :
(forall C1 C2 Xut1 n1,
  subst_utyp_in_utyp C2 Xut1 C1 = open_utyp_wrt_utyp_rec n1 C2 (close_utyp_wrt_utyp_rec n1 Xut1 C1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_utyp_in_utyp_spec_rec :
forall C1 C2 Xut1 n1,
  subst_utyp_in_utyp C2 Xut1 C1 = open_utyp_wrt_utyp_rec n1 C2 (close_utyp_wrt_utyp_rec n1 Xut1 C1).
Proof.
pose proof subst_utyp_in_utyp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_pskl_in_pskel_spec_rec_mutual :
(forall P1 P2 Xps1 n1,
  subst_pskl_in_pskel P2 Xps1 P1 = open_pskel_wrt_pskel_rec n1 P2 (close_pskel_wrt_pskel_rec n1 Xps1 P1)).
Proof.
apply_mutual_ind pskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_pskl_in_pskel_spec_rec :
forall P1 P2 Xps1 n1,
  subst_pskl_in_pskel P2 Xps1 P1 = open_pskel_wrt_pskel_rec n1 P2 (close_pskel_wrt_pskel_rec n1 Xps1 P1).
Proof.
pose proof subst_pskl_in_pskel_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pskl_in_pskel_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_bskl_in_bskel_spec_rec_mutual :
(forall Q1 Q2 Xbs1 n1,
  subst_bskl_in_bskel Q2 Xbs1 Q1 = open_bskel_wrt_bskel_rec n1 Q2 (close_bskel_wrt_bskel_rec n1 Xbs1 Q1)).
Proof.
apply_mutual_ind bskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_bskl_in_bskel_spec_rec :
forall Q1 Q2 Xbs1 n1,
  subst_bskl_in_bskel Q2 Xbs1 Q1 = open_bskel_wrt_bskel_rec n1 Q2 (close_bskel_wrt_bskel_rec n1 Xbs1 Q1).
Proof.
pose proof subst_bskl_in_bskel_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bskl_in_bskel_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_bskl_in_uskel_spec_rec_mutual :
(forall R1 R2 Xus1 n1,
  subst_bskl_in_uskel R2 Xus1 R1 = open_uskel_wrt_uskel_rec n1 R2 (close_uskel_wrt_uskel_rec n1 Xus1 R1)).
Proof.
apply_mutual_ind uskel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_bskl_in_uskel_spec_rec :
forall R1 R2 Xus1 n1,
  subst_bskl_in_uskel R2 Xus1 R1 = open_uskel_wrt_uskel_rec n1 R2 (close_uskel_wrt_uskel_rec n1 Xus1 R1).
Proof.
pose proof subst_bskl_in_uskel_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bskl_in_uskel_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ptyp_in_exp_spec_rec_mutual :
(forall e1 A1 Xpt1 n1,
  subst_ptyp_in_exp A1 Xpt1 e1 = open_exp_wrt_ptyp_rec n1 A1 (close_exp_wrt_ptyp_rec n1 Xpt1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ptyp_in_exp_spec_rec :
forall e1 A1 Xpt1 n1,
  subst_ptyp_in_exp A1 Xpt1 e1 = open_exp_wrt_ptyp_rec n1 A1 (close_exp_wrt_ptyp_rec n1 Xpt1 e1).
Proof.
pose proof subst_ptyp_in_exp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_spec_rec_mutual :
(forall e1 e2 x1 n1,
  subst_exp_in_exp e2 x1 e1 = open_exp_wrt_exp_rec n1 e2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_spec_rec :
forall e1 e2 x1 n1,
  subst_exp_in_exp e2 x1 e1 = open_exp_wrt_exp_rec n1 e2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof subst_exp_in_exp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_spec_rec : lngen.

(* end hide *)

Lemma subst_ptyp_in_ptyp_spec :
forall A1 A2 Xpt1,
  subst_ptyp_in_ptyp A2 Xpt1 A1 = open_ptyp_wrt_ptyp (close_ptyp_wrt_ptyp Xpt1 A1) A2.
Proof.
unfold close_ptyp_wrt_ptyp; unfold open_ptyp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve subst_ptyp_in_ptyp_spec : lngen.

Lemma subst_btyp_in_btyp_spec :
forall B1 B2 Xbt1,
  subst_btyp_in_btyp B2 Xbt1 B1 = open_btyp_wrt_btyp (close_btyp_wrt_btyp Xbt1 B1) B2.
Proof.
unfold close_btyp_wrt_btyp; unfold open_btyp_wrt_btyp; default_simp.
Qed.

#[export] Hint Resolve subst_btyp_in_btyp_spec : lngen.

Lemma subst_utyp_in_utyp_spec :
forall C1 C2 Xut1,
  subst_utyp_in_utyp C2 Xut1 C1 = open_utyp_wrt_utyp (close_utyp_wrt_utyp Xut1 C1) C2.
Proof.
unfold close_utyp_wrt_utyp; unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_spec : lngen.

Lemma subst_pskl_in_pskel_spec :
forall P1 P2 Xps1,
  subst_pskl_in_pskel P2 Xps1 P1 = open_pskel_wrt_pskel (close_pskel_wrt_pskel Xps1 P1) P2.
Proof.
unfold close_pskel_wrt_pskel; unfold open_pskel_wrt_pskel; default_simp.
Qed.

#[export] Hint Resolve subst_pskl_in_pskel_spec : lngen.

Lemma subst_bskl_in_bskel_spec :
forall Q1 Q2 Xbs1,
  subst_bskl_in_bskel Q2 Xbs1 Q1 = open_bskel_wrt_bskel (close_bskel_wrt_bskel Xbs1 Q1) Q2.
Proof.
unfold close_bskel_wrt_bskel; unfold open_bskel_wrt_bskel; default_simp.
Qed.

#[export] Hint Resolve subst_bskl_in_bskel_spec : lngen.

Lemma subst_bskl_in_uskel_spec :
forall R1 R2 Xus1,
  subst_bskl_in_uskel R2 Xus1 R1 = open_uskel_wrt_uskel (close_uskel_wrt_uskel Xus1 R1) R2.
Proof.
unfold close_uskel_wrt_uskel; unfold open_uskel_wrt_uskel; default_simp.
Qed.

#[export] Hint Resolve subst_bskl_in_uskel_spec : lngen.

Lemma subst_ptyp_in_exp_spec :
forall e1 A1 Xpt1,
  subst_ptyp_in_exp A1 Xpt1 e1 = open_exp_wrt_ptyp (close_exp_wrt_ptyp Xpt1 e1) A1.
Proof.
unfold close_exp_wrt_ptyp; unfold open_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_spec : lngen.

Lemma subst_exp_in_exp_spec :
forall e1 e2 x1,
  subst_exp_in_exp e2 x1 e1 = open_exp_wrt_exp (close_exp_wrt_exp x1 e1) e2.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_spec : lngen.

(* begin hide *)

Lemma subst_ptyp_in_ptyp_subst_ptyp_in_ptyp_mutual :
(forall A1 A2 A3 Xpt2 Xpt1,
  Xpt2 `notin` ftvar_in_ptyp A2 ->
  Xpt2 <> Xpt1 ->
  subst_ptyp_in_ptyp A2 Xpt1 (subst_ptyp_in_ptyp A3 Xpt2 A1) = subst_ptyp_in_ptyp (subst_ptyp_in_ptyp A2 Xpt1 A3) Xpt2 (subst_ptyp_in_ptyp A2 Xpt1 A1)).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ptyp_in_ptyp_subst_ptyp_in_ptyp :
forall A1 A2 A3 Xpt2 Xpt1,
  Xpt2 `notin` ftvar_in_ptyp A2 ->
  Xpt2 <> Xpt1 ->
  subst_ptyp_in_ptyp A2 Xpt1 (subst_ptyp_in_ptyp A3 Xpt2 A1) = subst_ptyp_in_ptyp (subst_ptyp_in_ptyp A2 Xpt1 A3) Xpt2 (subst_ptyp_in_ptyp A2 Xpt1 A1).
Proof.
pose proof subst_ptyp_in_ptyp_subst_ptyp_in_ptyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_ptyp_subst_ptyp_in_ptyp : lngen.

(* begin hide *)

Lemma subst_btyp_in_btyp_subst_btyp_in_btyp_mutual :
(forall B1 B2 B3 Xbt2 Xbt1,
  Xbt2 `notin` ftvar_in_btyp B2 ->
  Xbt2 <> Xbt1 ->
  subst_btyp_in_btyp B2 Xbt1 (subst_btyp_in_btyp B3 Xbt2 B1) = subst_btyp_in_btyp (subst_btyp_in_btyp B2 Xbt1 B3) Xbt2 (subst_btyp_in_btyp B2 Xbt1 B1)).
Proof.
apply_mutual_ind btyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_btyp_in_btyp_subst_btyp_in_btyp :
forall B1 B2 B3 Xbt2 Xbt1,
  Xbt2 `notin` ftvar_in_btyp B2 ->
  Xbt2 <> Xbt1 ->
  subst_btyp_in_btyp B2 Xbt1 (subst_btyp_in_btyp B3 Xbt2 B1) = subst_btyp_in_btyp (subst_btyp_in_btyp B2 Xbt1 B3) Xbt2 (subst_btyp_in_btyp B2 Xbt1 B1).
Proof.
pose proof subst_btyp_in_btyp_subst_btyp_in_btyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_btyp_in_btyp_subst_btyp_in_btyp : lngen.

(* begin hide *)

Lemma subst_utyp_in_utyp_subst_utyp_in_utyp_mutual :
(forall C1 C2 C3 Xut2 Xut1,
  Xut2 `notin` ftvar_in_utyp C2 ->
  Xut2 <> Xut1 ->
  subst_utyp_in_utyp C2 Xut1 (subst_utyp_in_utyp C3 Xut2 C1) = subst_utyp_in_utyp (subst_utyp_in_utyp C2 Xut1 C3) Xut2 (subst_utyp_in_utyp C2 Xut1 C1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_utyp_in_utyp_subst_utyp_in_utyp :
forall C1 C2 C3 Xut2 Xut1,
  Xut2 `notin` ftvar_in_utyp C2 ->
  Xut2 <> Xut1 ->
  subst_utyp_in_utyp C2 Xut1 (subst_utyp_in_utyp C3 Xut2 C1) = subst_utyp_in_utyp (subst_utyp_in_utyp C2 Xut1 C3) Xut2 (subst_utyp_in_utyp C2 Xut1 C1).
Proof.
pose proof subst_utyp_in_utyp_subst_utyp_in_utyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_subst_utyp_in_utyp : lngen.

(* begin hide *)

Lemma subst_pskl_in_pskel_subst_pskl_in_pskel_mutual :
(forall P1 P2 P3 Xps2 Xps1,
  Xps2 `notin` ftvar_in_pskel P2 ->
  Xps2 <> Xps1 ->
  subst_pskl_in_pskel P2 Xps1 (subst_pskl_in_pskel P3 Xps2 P1) = subst_pskl_in_pskel (subst_pskl_in_pskel P2 Xps1 P3) Xps2 (subst_pskl_in_pskel P2 Xps1 P1)).
Proof.
apply_mutual_ind pskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pskl_in_pskel_subst_pskl_in_pskel :
forall P1 P2 P3 Xps2 Xps1,
  Xps2 `notin` ftvar_in_pskel P2 ->
  Xps2 <> Xps1 ->
  subst_pskl_in_pskel P2 Xps1 (subst_pskl_in_pskel P3 Xps2 P1) = subst_pskl_in_pskel (subst_pskl_in_pskel P2 Xps1 P3) Xps2 (subst_pskl_in_pskel P2 Xps1 P1).
Proof.
pose proof subst_pskl_in_pskel_subst_pskl_in_pskel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pskl_in_pskel_subst_pskl_in_pskel : lngen.

(* begin hide *)

Lemma subst_bskl_in_bskel_subst_bskl_in_bskel_mutual :
(forall Q1 Q2 Q3 Xbs2 Xbs1,
  Xbs2 `notin` ftvar_in_bskel Q2 ->
  Xbs2 <> Xbs1 ->
  subst_bskl_in_bskel Q2 Xbs1 (subst_bskl_in_bskel Q3 Xbs2 Q1) = subst_bskl_in_bskel (subst_bskl_in_bskel Q2 Xbs1 Q3) Xbs2 (subst_bskl_in_bskel Q2 Xbs1 Q1)).
Proof.
apply_mutual_ind bskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_bskl_in_bskel_subst_bskl_in_bskel :
forall Q1 Q2 Q3 Xbs2 Xbs1,
  Xbs2 `notin` ftvar_in_bskel Q2 ->
  Xbs2 <> Xbs1 ->
  subst_bskl_in_bskel Q2 Xbs1 (subst_bskl_in_bskel Q3 Xbs2 Q1) = subst_bskl_in_bskel (subst_bskl_in_bskel Q2 Xbs1 Q3) Xbs2 (subst_bskl_in_bskel Q2 Xbs1 Q1).
Proof.
pose proof subst_bskl_in_bskel_subst_bskl_in_bskel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bskl_in_bskel_subst_bskl_in_bskel : lngen.

(* begin hide *)

Lemma subst_bskl_in_uskel_subst_bskl_in_uskel_mutual :
(forall R1 R2 R3 Xus2 Xus1,
  Xus2 `notin` ftvar_in_uskel R2 ->
  Xus2 <> Xus1 ->
  subst_bskl_in_uskel R2 Xus1 (subst_bskl_in_uskel R3 Xus2 R1) = subst_bskl_in_uskel (subst_bskl_in_uskel R2 Xus1 R3) Xus2 (subst_bskl_in_uskel R2 Xus1 R1)).
Proof.
apply_mutual_ind uskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_bskl_in_uskel_subst_bskl_in_uskel :
forall R1 R2 R3 Xus2 Xus1,
  Xus2 `notin` ftvar_in_uskel R2 ->
  Xus2 <> Xus1 ->
  subst_bskl_in_uskel R2 Xus1 (subst_bskl_in_uskel R3 Xus2 R1) = subst_bskl_in_uskel (subst_bskl_in_uskel R2 Xus1 R3) Xus2 (subst_bskl_in_uskel R2 Xus1 R1).
Proof.
pose proof subst_bskl_in_uskel_subst_bskl_in_uskel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bskl_in_uskel_subst_bskl_in_uskel : lngen.

(* begin hide *)

Lemma subst_ptyp_in_exp_subst_ptyp_in_exp_mutual :
(forall e1 A1 A2 Xpt2 Xpt1,
  Xpt2 `notin` ftvar_in_ptyp A1 ->
  Xpt2 <> Xpt1 ->
  subst_ptyp_in_exp A1 Xpt1 (subst_ptyp_in_exp A2 Xpt2 e1) = subst_ptyp_in_exp (subst_ptyp_in_ptyp A1 Xpt1 A2) Xpt2 (subst_ptyp_in_exp A1 Xpt1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ptyp_in_exp_subst_ptyp_in_exp :
forall e1 A1 A2 Xpt2 Xpt1,
  Xpt2 `notin` ftvar_in_ptyp A1 ->
  Xpt2 <> Xpt1 ->
  subst_ptyp_in_exp A1 Xpt1 (subst_ptyp_in_exp A2 Xpt2 e1) = subst_ptyp_in_exp (subst_ptyp_in_ptyp A1 Xpt1 A2) Xpt2 (subst_ptyp_in_exp A1 Xpt1 e1).
Proof.
pose proof subst_ptyp_in_exp_subst_ptyp_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_subst_ptyp_in_exp : lngen.

(* begin hide *)

Lemma subst_ptyp_in_exp_subst_exp_in_exp_mutual :
(forall e1 A1 e2 x1 Xpt1,
  subst_ptyp_in_exp A1 Xpt1 (subst_exp_in_exp e2 x1 e1) = subst_exp_in_exp (subst_ptyp_in_exp A1 Xpt1 e2) x1 (subst_ptyp_in_exp A1 Xpt1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ptyp_in_exp_subst_exp_in_exp :
forall e1 A1 e2 x1 Xpt1,
  subst_ptyp_in_exp A1 Xpt1 (subst_exp_in_exp e2 x1 e1) = subst_exp_in_exp (subst_ptyp_in_exp A1 Xpt1 e2) x1 (subst_ptyp_in_exp A1 Xpt1 e1).
Proof.
pose proof subst_ptyp_in_exp_subst_exp_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_subst_exp_in_exp : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_subst_ptyp_in_exp_mutual :
(forall e1 e2 A1 Xpt1 x1,
  Xpt1 `notin` ftvar_in_exp e2 ->
  subst_exp_in_exp e2 x1 (subst_ptyp_in_exp A1 Xpt1 e1) = subst_ptyp_in_exp A1 Xpt1 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_subst_ptyp_in_exp :
forall e1 e2 A1 Xpt1 x1,
  Xpt1 `notin` ftvar_in_exp e2 ->
  subst_exp_in_exp e2 x1 (subst_ptyp_in_exp A1 Xpt1 e1) = subst_ptyp_in_exp A1 Xpt1 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_subst_ptyp_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_subst_ptyp_in_exp : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_subst_exp_in_exp_mutual :
(forall e1 e2 e3 x2 x1,
  x2 `notin` fvar_in_exp e2 ->
  x2 <> x1 ->
  subst_exp_in_exp e2 x1 (subst_exp_in_exp e3 x2 e1) = subst_exp_in_exp (subst_exp_in_exp e2 x1 e3) x2 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_subst_exp_in_exp :
forall e1 e2 e3 x2 x1,
  x2 `notin` fvar_in_exp e2 ->
  x2 <> x1 ->
  subst_exp_in_exp e2 x1 (subst_exp_in_exp e3 x2 e1) = subst_exp_in_exp (subst_exp_in_exp e2 x1 e3) x2 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_subst_exp_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_subst_exp_in_exp : lngen.

(* begin hide *)

Lemma subst_ptyp_in_ptyp_close_ptyp_wrt_ptyp_rec_open_ptyp_wrt_ptyp_rec_mutual :
(forall A2 A1 Xpt1 Xpt2 n1,
  Xpt2 `notin` ftvar_in_ptyp A2 ->
  Xpt2 `notin` ftvar_in_ptyp A1 ->
  Xpt2 <> Xpt1 ->
  degree_ptyp_wrt_ptyp n1 A1 ->
  subst_ptyp_in_ptyp A1 Xpt1 A2 = close_ptyp_wrt_ptyp_rec n1 Xpt2 (subst_ptyp_in_ptyp A1 Xpt1 (open_ptyp_wrt_ptyp_rec n1 (ptyp_var_f Xpt2) A2))).
Proof.
apply_mutual_ind ptyp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ptyp_in_ptyp_close_ptyp_wrt_ptyp_rec_open_ptyp_wrt_ptyp_rec :
forall A2 A1 Xpt1 Xpt2 n1,
  Xpt2 `notin` ftvar_in_ptyp A2 ->
  Xpt2 `notin` ftvar_in_ptyp A1 ->
  Xpt2 <> Xpt1 ->
  degree_ptyp_wrt_ptyp n1 A1 ->
  subst_ptyp_in_ptyp A1 Xpt1 A2 = close_ptyp_wrt_ptyp_rec n1 Xpt2 (subst_ptyp_in_ptyp A1 Xpt1 (open_ptyp_wrt_ptyp_rec n1 (ptyp_var_f Xpt2) A2)).
Proof.
pose proof subst_ptyp_in_ptyp_close_ptyp_wrt_ptyp_rec_open_ptyp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_ptyp_close_ptyp_wrt_ptyp_rec_open_ptyp_wrt_ptyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_btyp_in_btyp_close_btyp_wrt_btyp_rec_open_btyp_wrt_btyp_rec_mutual :
(forall B2 B1 Xbt1 Xbt2 n1,
  Xbt2 `notin` ftvar_in_btyp B2 ->
  Xbt2 `notin` ftvar_in_btyp B1 ->
  Xbt2 <> Xbt1 ->
  degree_btyp_wrt_btyp n1 B1 ->
  subst_btyp_in_btyp B1 Xbt1 B2 = close_btyp_wrt_btyp_rec n1 Xbt2 (subst_btyp_in_btyp B1 Xbt1 (open_btyp_wrt_btyp_rec n1 (btyp_var_f Xbt2) B2))).
Proof.
apply_mutual_ind btyp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_btyp_in_btyp_close_btyp_wrt_btyp_rec_open_btyp_wrt_btyp_rec :
forall B2 B1 Xbt1 Xbt2 n1,
  Xbt2 `notin` ftvar_in_btyp B2 ->
  Xbt2 `notin` ftvar_in_btyp B1 ->
  Xbt2 <> Xbt1 ->
  degree_btyp_wrt_btyp n1 B1 ->
  subst_btyp_in_btyp B1 Xbt1 B2 = close_btyp_wrt_btyp_rec n1 Xbt2 (subst_btyp_in_btyp B1 Xbt1 (open_btyp_wrt_btyp_rec n1 (btyp_var_f Xbt2) B2)).
Proof.
pose proof subst_btyp_in_btyp_close_btyp_wrt_btyp_rec_open_btyp_wrt_btyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_btyp_in_btyp_close_btyp_wrt_btyp_rec_open_btyp_wrt_btyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_utyp_in_utyp_close_utyp_wrt_utyp_rec_open_utyp_wrt_utyp_rec_mutual :
(forall C2 C1 Xut1 Xut2 n1,
  Xut2 `notin` ftvar_in_utyp C2 ->
  Xut2 `notin` ftvar_in_utyp C1 ->
  Xut2 <> Xut1 ->
  degree_utyp_wrt_utyp n1 C1 ->
  subst_utyp_in_utyp C1 Xut1 C2 = close_utyp_wrt_utyp_rec n1 Xut2 (subst_utyp_in_utyp C1 Xut1 (open_utyp_wrt_utyp_rec n1 (utyp_var_f Xut2) C2))).
Proof.
apply_mutual_ind utyp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_utyp_in_utyp_close_utyp_wrt_utyp_rec_open_utyp_wrt_utyp_rec :
forall C2 C1 Xut1 Xut2 n1,
  Xut2 `notin` ftvar_in_utyp C2 ->
  Xut2 `notin` ftvar_in_utyp C1 ->
  Xut2 <> Xut1 ->
  degree_utyp_wrt_utyp n1 C1 ->
  subst_utyp_in_utyp C1 Xut1 C2 = close_utyp_wrt_utyp_rec n1 Xut2 (subst_utyp_in_utyp C1 Xut1 (open_utyp_wrt_utyp_rec n1 (utyp_var_f Xut2) C2)).
Proof.
pose proof subst_utyp_in_utyp_close_utyp_wrt_utyp_rec_open_utyp_wrt_utyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_close_utyp_wrt_utyp_rec_open_utyp_wrt_utyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_pskl_in_pskel_close_pskel_wrt_pskel_rec_open_pskel_wrt_pskel_rec_mutual :
(forall P2 P1 Xps1 Xps2 n1,
  Xps2 `notin` ftvar_in_pskel P2 ->
  Xps2 `notin` ftvar_in_pskel P1 ->
  Xps2 <> Xps1 ->
  degree_pskel_wrt_pskel n1 P1 ->
  subst_pskl_in_pskel P1 Xps1 P2 = close_pskel_wrt_pskel_rec n1 Xps2 (subst_pskl_in_pskel P1 Xps1 (open_pskel_wrt_pskel_rec n1 (pskel_var_f Xps2) P2))).
Proof.
apply_mutual_ind pskel_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_pskl_in_pskel_close_pskel_wrt_pskel_rec_open_pskel_wrt_pskel_rec :
forall P2 P1 Xps1 Xps2 n1,
  Xps2 `notin` ftvar_in_pskel P2 ->
  Xps2 `notin` ftvar_in_pskel P1 ->
  Xps2 <> Xps1 ->
  degree_pskel_wrt_pskel n1 P1 ->
  subst_pskl_in_pskel P1 Xps1 P2 = close_pskel_wrt_pskel_rec n1 Xps2 (subst_pskl_in_pskel P1 Xps1 (open_pskel_wrt_pskel_rec n1 (pskel_var_f Xps2) P2)).
Proof.
pose proof subst_pskl_in_pskel_close_pskel_wrt_pskel_rec_open_pskel_wrt_pskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pskl_in_pskel_close_pskel_wrt_pskel_rec_open_pskel_wrt_pskel_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_bskl_in_bskel_close_bskel_wrt_bskel_rec_open_bskel_wrt_bskel_rec_mutual :
(forall Q2 Q1 Xbs1 Xbs2 n1,
  Xbs2 `notin` ftvar_in_bskel Q2 ->
  Xbs2 `notin` ftvar_in_bskel Q1 ->
  Xbs2 <> Xbs1 ->
  degree_bskel_wrt_bskel n1 Q1 ->
  subst_bskl_in_bskel Q1 Xbs1 Q2 = close_bskel_wrt_bskel_rec n1 Xbs2 (subst_bskl_in_bskel Q1 Xbs1 (open_bskel_wrt_bskel_rec n1 (bskel_var_f Xbs2) Q2))).
Proof.
apply_mutual_ind bskel_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_bskl_in_bskel_close_bskel_wrt_bskel_rec_open_bskel_wrt_bskel_rec :
forall Q2 Q1 Xbs1 Xbs2 n1,
  Xbs2 `notin` ftvar_in_bskel Q2 ->
  Xbs2 `notin` ftvar_in_bskel Q1 ->
  Xbs2 <> Xbs1 ->
  degree_bskel_wrt_bskel n1 Q1 ->
  subst_bskl_in_bskel Q1 Xbs1 Q2 = close_bskel_wrt_bskel_rec n1 Xbs2 (subst_bskl_in_bskel Q1 Xbs1 (open_bskel_wrt_bskel_rec n1 (bskel_var_f Xbs2) Q2)).
Proof.
pose proof subst_bskl_in_bskel_close_bskel_wrt_bskel_rec_open_bskel_wrt_bskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bskl_in_bskel_close_bskel_wrt_bskel_rec_open_bskel_wrt_bskel_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_bskl_in_uskel_close_uskel_wrt_uskel_rec_open_uskel_wrt_uskel_rec_mutual :
(forall R2 R1 Xus1 Xus2 n1,
  Xus2 `notin` ftvar_in_uskel R2 ->
  Xus2 `notin` ftvar_in_uskel R1 ->
  Xus2 <> Xus1 ->
  degree_uskel_wrt_uskel n1 R1 ->
  subst_bskl_in_uskel R1 Xus1 R2 = close_uskel_wrt_uskel_rec n1 Xus2 (subst_bskl_in_uskel R1 Xus1 (open_uskel_wrt_uskel_rec n1 (uskel_var_f Xus2) R2))).
Proof.
apply_mutual_ind uskel_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_bskl_in_uskel_close_uskel_wrt_uskel_rec_open_uskel_wrt_uskel_rec :
forall R2 R1 Xus1 Xus2 n1,
  Xus2 `notin` ftvar_in_uskel R2 ->
  Xus2 `notin` ftvar_in_uskel R1 ->
  Xus2 <> Xus1 ->
  degree_uskel_wrt_uskel n1 R1 ->
  subst_bskl_in_uskel R1 Xus1 R2 = close_uskel_wrt_uskel_rec n1 Xus2 (subst_bskl_in_uskel R1 Xus1 (open_uskel_wrt_uskel_rec n1 (uskel_var_f Xus2) R2)).
Proof.
pose proof subst_bskl_in_uskel_close_uskel_wrt_uskel_rec_open_uskel_wrt_uskel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bskl_in_uskel_close_uskel_wrt_uskel_rec_open_uskel_wrt_uskel_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ptyp_in_exp_close_exp_wrt_ptyp_rec_open_exp_wrt_ptyp_rec_mutual :
(forall e1 A1 Xpt1 Xpt2 n1,
  Xpt2 `notin` ftvar_in_exp e1 ->
  Xpt2 `notin` ftvar_in_ptyp A1 ->
  Xpt2 <> Xpt1 ->
  degree_ptyp_wrt_ptyp n1 A1 ->
  subst_ptyp_in_exp A1 Xpt1 e1 = close_exp_wrt_ptyp_rec n1 Xpt2 (subst_ptyp_in_exp A1 Xpt1 (open_exp_wrt_ptyp_rec n1 (ptyp_var_f Xpt2) e1))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ptyp_in_exp_close_exp_wrt_ptyp_rec_open_exp_wrt_ptyp_rec :
forall e1 A1 Xpt1 Xpt2 n1,
  Xpt2 `notin` ftvar_in_exp e1 ->
  Xpt2 `notin` ftvar_in_ptyp A1 ->
  Xpt2 <> Xpt1 ->
  degree_ptyp_wrt_ptyp n1 A1 ->
  subst_ptyp_in_exp A1 Xpt1 e1 = close_exp_wrt_ptyp_rec n1 Xpt2 (subst_ptyp_in_exp A1 Xpt1 (open_exp_wrt_ptyp_rec n1 (ptyp_var_f Xpt2) e1)).
Proof.
pose proof subst_ptyp_in_exp_close_exp_wrt_ptyp_rec_open_exp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_close_exp_wrt_ptyp_rec_open_exp_wrt_ptyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ptyp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e1 A1 Xpt1 x1 n1,
  x1 `notin` fvar_in_exp e1 ->
  subst_ptyp_in_exp A1 Xpt1 e1 = close_exp_wrt_exp_rec n1 x1 (subst_ptyp_in_exp A1 Xpt1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ptyp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e1 A1 Xpt1 x1 n1,
  x1 `notin` fvar_in_exp e1 ->
  subst_ptyp_in_exp A1 Xpt1 e1 = close_exp_wrt_exp_rec n1 x1 (subst_ptyp_in_exp A1 Xpt1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1)).
Proof.
pose proof subst_ptyp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_ptyp_rec_open_exp_wrt_ptyp_rec_mutual :
(forall e2 e1 x1 Xpt1 n1,
  Xpt1 `notin` ftvar_in_exp e2 ->
  Xpt1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_ptyp n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_ptyp_rec n1 Xpt1 (subst_exp_in_exp e1 x1 (open_exp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) e2))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_ptyp_rec_open_exp_wrt_ptyp_rec :
forall e2 e1 x1 Xpt1 n1,
  Xpt1 `notin` ftvar_in_exp e2 ->
  Xpt1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_ptyp n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_ptyp_rec n1 Xpt1 (subst_exp_in_exp e1 x1 (open_exp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) e2)).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_ptyp_rec_open_exp_wrt_ptyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_ptyp_rec_open_exp_wrt_ptyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  x2 `notin` fvar_in_exp e2 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x2) e2))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` fvar_in_exp e2 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x2) e2)).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma subst_ptyp_in_ptyp_close_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp :
forall A2 A1 Xpt1 Xpt2,
  Xpt2 `notin` ftvar_in_ptyp A2 ->
  Xpt2 `notin` ftvar_in_ptyp A1 ->
  Xpt2 <> Xpt1 ->
  lc_ptyp A1 ->
  subst_ptyp_in_ptyp A1 Xpt1 A2 = close_ptyp_wrt_ptyp Xpt2 (subst_ptyp_in_ptyp A1 Xpt1 (open_ptyp_wrt_ptyp A2 (ptyp_var_f Xpt2))).
Proof.
unfold close_ptyp_wrt_ptyp; unfold open_ptyp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve subst_ptyp_in_ptyp_close_ptyp_wrt_ptyp_open_ptyp_wrt_ptyp : lngen.

Lemma subst_btyp_in_btyp_close_btyp_wrt_btyp_open_btyp_wrt_btyp :
forall B2 B1 Xbt1 Xbt2,
  Xbt2 `notin` ftvar_in_btyp B2 ->
  Xbt2 `notin` ftvar_in_btyp B1 ->
  Xbt2 <> Xbt1 ->
  lc_btyp B1 ->
  subst_btyp_in_btyp B1 Xbt1 B2 = close_btyp_wrt_btyp Xbt2 (subst_btyp_in_btyp B1 Xbt1 (open_btyp_wrt_btyp B2 (btyp_var_f Xbt2))).
Proof.
unfold close_btyp_wrt_btyp; unfold open_btyp_wrt_btyp; default_simp.
Qed.

#[export] Hint Resolve subst_btyp_in_btyp_close_btyp_wrt_btyp_open_btyp_wrt_btyp : lngen.

Lemma subst_utyp_in_utyp_close_utyp_wrt_utyp_open_utyp_wrt_utyp :
forall C2 C1 Xut1 Xut2,
  Xut2 `notin` ftvar_in_utyp C2 ->
  Xut2 `notin` ftvar_in_utyp C1 ->
  Xut2 <> Xut1 ->
  lc_utyp C1 ->
  subst_utyp_in_utyp C1 Xut1 C2 = close_utyp_wrt_utyp Xut2 (subst_utyp_in_utyp C1 Xut1 (open_utyp_wrt_utyp C2 (utyp_var_f Xut2))).
Proof.
unfold close_utyp_wrt_utyp; unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_close_utyp_wrt_utyp_open_utyp_wrt_utyp : lngen.

Lemma subst_pskl_in_pskel_close_pskel_wrt_pskel_open_pskel_wrt_pskel :
forall P2 P1 Xps1 Xps2,
  Xps2 `notin` ftvar_in_pskel P2 ->
  Xps2 `notin` ftvar_in_pskel P1 ->
  Xps2 <> Xps1 ->
  lc_pskel P1 ->
  subst_pskl_in_pskel P1 Xps1 P2 = close_pskel_wrt_pskel Xps2 (subst_pskl_in_pskel P1 Xps1 (open_pskel_wrt_pskel P2 (pskel_var_f Xps2))).
Proof.
unfold close_pskel_wrt_pskel; unfold open_pskel_wrt_pskel; default_simp.
Qed.

#[export] Hint Resolve subst_pskl_in_pskel_close_pskel_wrt_pskel_open_pskel_wrt_pskel : lngen.

Lemma subst_bskl_in_bskel_close_bskel_wrt_bskel_open_bskel_wrt_bskel :
forall Q2 Q1 Xbs1 Xbs2,
  Xbs2 `notin` ftvar_in_bskel Q2 ->
  Xbs2 `notin` ftvar_in_bskel Q1 ->
  Xbs2 <> Xbs1 ->
  lc_bskel Q1 ->
  subst_bskl_in_bskel Q1 Xbs1 Q2 = close_bskel_wrt_bskel Xbs2 (subst_bskl_in_bskel Q1 Xbs1 (open_bskel_wrt_bskel Q2 (bskel_var_f Xbs2))).
Proof.
unfold close_bskel_wrt_bskel; unfold open_bskel_wrt_bskel; default_simp.
Qed.

#[export] Hint Resolve subst_bskl_in_bskel_close_bskel_wrt_bskel_open_bskel_wrt_bskel : lngen.

Lemma subst_bskl_in_uskel_close_uskel_wrt_uskel_open_uskel_wrt_uskel :
forall R2 R1 Xus1 Xus2,
  Xus2 `notin` ftvar_in_uskel R2 ->
  Xus2 `notin` ftvar_in_uskel R1 ->
  Xus2 <> Xus1 ->
  lc_uskel R1 ->
  subst_bskl_in_uskel R1 Xus1 R2 = close_uskel_wrt_uskel Xus2 (subst_bskl_in_uskel R1 Xus1 (open_uskel_wrt_uskel R2 (uskel_var_f Xus2))).
Proof.
unfold close_uskel_wrt_uskel; unfold open_uskel_wrt_uskel; default_simp.
Qed.

#[export] Hint Resolve subst_bskl_in_uskel_close_uskel_wrt_uskel_open_uskel_wrt_uskel : lngen.

Lemma subst_ptyp_in_exp_close_exp_wrt_ptyp_open_exp_wrt_ptyp :
forall e1 A1 Xpt1 Xpt2,
  Xpt2 `notin` ftvar_in_exp e1 ->
  Xpt2 `notin` ftvar_in_ptyp A1 ->
  Xpt2 <> Xpt1 ->
  lc_ptyp A1 ->
  subst_ptyp_in_exp A1 Xpt1 e1 = close_exp_wrt_ptyp Xpt2 (subst_ptyp_in_exp A1 Xpt1 (open_exp_wrt_ptyp e1 (ptyp_var_f Xpt2))).
Proof.
unfold close_exp_wrt_ptyp; unfold open_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_close_exp_wrt_ptyp_open_exp_wrt_ptyp : lngen.

Lemma subst_ptyp_in_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 A1 Xpt1 x1,
  x1 `notin` fvar_in_exp e1 ->
  lc_ptyp A1 ->
  subst_ptyp_in_exp A1 Xpt1 e1 = close_exp_wrt_exp x1 (subst_ptyp_in_exp A1 Xpt1 (open_exp_wrt_exp e1 (exp_var_f x1))).
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_ptyp_open_exp_wrt_ptyp :
forall e2 e1 x1 Xpt1,
  Xpt1 `notin` ftvar_in_exp e2 ->
  Xpt1 `notin` ftvar_in_exp e1 ->
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_ptyp Xpt1 (subst_exp_in_exp e1 x1 (open_exp_wrt_ptyp e2 (ptyp_var_f Xpt1))).
Proof.
unfold close_exp_wrt_ptyp; unfold open_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_ptyp_open_exp_wrt_ptyp : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall e2 e1 x1 x2,
  x2 `notin` fvar_in_exp e2 ->
  x2 `notin` fvar_in_exp e1 ->
  x2 <> x1 ->
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_exp x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2))).
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma subst_ptyp_in_ptyp_ptyp_all :
forall Xpt2 A2 A1 Xpt1,
  lc_ptyp A1 ->
  Xpt2 `notin` ftvar_in_ptyp A1 `union` ftvar_in_ptyp A2 `union` singleton Xpt1 ->
  subst_ptyp_in_ptyp A1 Xpt1 (ptyp_all A2) = ptyp_all (close_ptyp_wrt_ptyp Xpt2 (subst_ptyp_in_ptyp A1 Xpt1 (open_ptyp_wrt_ptyp A2 (ptyp_var_f Xpt2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_ptyp_in_ptyp_ptyp_all : lngen.

Lemma subst_btyp_in_btyp_btyp_all_syn :
forall Xbt2 B2 B1 Xbt1,
  lc_btyp B1 ->
  Xbt2 `notin` ftvar_in_btyp B1 `union` ftvar_in_btyp B2 `union` singleton Xbt1 ->
  subst_btyp_in_btyp B1 Xbt1 (btyp_all_syn B2) = btyp_all_syn (close_btyp_wrt_btyp Xbt2 (subst_btyp_in_btyp B1 Xbt1 (open_btyp_wrt_btyp B2 (btyp_var_f Xbt2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_btyp_in_btyp_btyp_all_syn : lngen.

Lemma subst_btyp_in_btyp_btyp_all_inh :
forall Xbt2 B2 B1 Xbt1,
  lc_btyp B1 ->
  Xbt2 `notin` ftvar_in_btyp B1 `union` ftvar_in_btyp B2 `union` singleton Xbt1 ->
  subst_btyp_in_btyp B1 Xbt1 (btyp_all_inh B2) = btyp_all_inh (close_btyp_wrt_btyp Xbt2 (subst_btyp_in_btyp B1 Xbt1 (open_btyp_wrt_btyp B2 (btyp_var_f Xbt2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_btyp_in_btyp_btyp_all_inh : lngen.

Lemma subst_utyp_in_utyp_utyp_all_syn :
forall Xut2 C2 C1 Xut1,
  lc_utyp C1 ->
  Xut2 `notin` ftvar_in_utyp C1 `union` ftvar_in_utyp C2 `union` singleton Xut1 ->
  subst_utyp_in_utyp C1 Xut1 (utyp_all_syn C2) = utyp_all_syn (close_utyp_wrt_utyp Xut2 (subst_utyp_in_utyp C1 Xut1 (open_utyp_wrt_utyp C2 (utyp_var_f Xut2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_utyp_all_syn : lngen.

Lemma subst_utyp_in_utyp_utyp_all_etag :
forall Xut2 ε1 C2 C1 Xut1,
  lc_utyp C1 ->
  Xut2 `notin` ftvar_in_utyp C1 `union` ftvar_in_utyp C2 `union` singleton Xut1 ->
  subst_utyp_in_utyp C1 Xut1 (utyp_all_etag ε1 C2) = utyp_all_etag (ε1) (close_utyp_wrt_utyp Xut2 (subst_utyp_in_utyp C1 Xut1 (open_utyp_wrt_utyp C2 (utyp_var_f Xut2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_utyp_all_etag : lngen.

Lemma subst_pskl_in_pskel_pskel_all_syn :
forall Xps2 P2 P1 Xps1,
  lc_pskel P1 ->
  Xps2 `notin` ftvar_in_pskel P1 `union` ftvar_in_pskel P2 `union` singleton Xps1 ->
  subst_pskl_in_pskel P1 Xps1 (pskel_all_syn P2) = pskel_all_syn (close_pskel_wrt_pskel Xps2 (subst_pskl_in_pskel P1 Xps1 (open_pskel_wrt_pskel P2 (pskel_var_f Xps2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_pskl_in_pskel_pskel_all_syn : lngen.

Lemma subst_bskl_in_bskel_bskel_all_syn :
forall Xbs2 Q2 Q1 Xbs1,
  lc_bskel Q1 ->
  Xbs2 `notin` ftvar_in_bskel Q1 `union` ftvar_in_bskel Q2 `union` singleton Xbs1 ->
  subst_bskl_in_bskel Q1 Xbs1 (bskel_all_syn Q2) = bskel_all_syn (close_bskel_wrt_bskel Xbs2 (subst_bskl_in_bskel Q1 Xbs1 (open_bskel_wrt_bskel Q2 (bskel_var_f Xbs2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_bskl_in_bskel_bskel_all_syn : lngen.

Lemma subst_bskl_in_bskel_bskel_all_inh :
forall Xbs2 Q2 Q1 Xbs1,
  lc_bskel Q1 ->
  Xbs2 `notin` ftvar_in_bskel Q1 `union` ftvar_in_bskel Q2 `union` singleton Xbs1 ->
  subst_bskl_in_bskel Q1 Xbs1 (bskel_all_inh Q2) = bskel_all_inh (close_bskel_wrt_bskel Xbs2 (subst_bskl_in_bskel Q1 Xbs1 (open_bskel_wrt_bskel Q2 (bskel_var_f Xbs2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_bskl_in_bskel_bskel_all_inh : lngen.

Lemma subst_bskl_in_uskel_uskel_all_syn :
forall Xus2 R2 R1 Xus1,
  lc_uskel R1 ->
  Xus2 `notin` ftvar_in_uskel R1 `union` ftvar_in_uskel R2 `union` singleton Xus1 ->
  subst_bskl_in_uskel R1 Xus1 (uskel_all_syn R2) = uskel_all_syn (close_uskel_wrt_uskel Xus2 (subst_bskl_in_uskel R1 Xus1 (open_uskel_wrt_uskel R2 (uskel_var_f Xus2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_bskl_in_uskel_uskel_all_syn : lngen.

Lemma subst_bskl_in_uskel_uskel_all_etag :
forall Xus2 ε1 R2 R1 Xus1,
  lc_uskel R1 ->
  Xus2 `notin` ftvar_in_uskel R1 `union` ftvar_in_uskel R2 `union` singleton Xus1 ->
  subst_bskl_in_uskel R1 Xus1 (uskel_all_etag ε1 R2) = uskel_all_etag (ε1) (close_uskel_wrt_uskel Xus2 (subst_bskl_in_uskel R1 Xus1 (open_uskel_wrt_uskel R2 (uskel_var_f Xus2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_bskl_in_uskel_uskel_all_etag : lngen.

Lemma subst_ptyp_in_exp_exp_abs :
forall x1 e1 A1 Xpt1,
  lc_ptyp A1 ->
  x1 `notin` fvar_in_exp e1 ->
  subst_ptyp_in_exp A1 Xpt1 (exp_abs e1) = exp_abs (close_exp_wrt_exp x1 (subst_ptyp_in_exp A1 Xpt1 (open_exp_wrt_exp e1 (exp_var_f x1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_exp_abs : lngen.

Lemma subst_ptyp_in_exp_exp_abs_anno :
forall x1 A2 e1 A1 Xpt1,
  lc_ptyp A1 ->
  x1 `notin` fvar_in_exp e1 ->
  subst_ptyp_in_exp A1 Xpt1 (exp_abs_anno A2 e1) = exp_abs_anno (subst_ptyp_in_ptyp A1 Xpt1 A2) (close_exp_wrt_exp x1 (subst_ptyp_in_exp A1 Xpt1 (open_exp_wrt_exp e1 (exp_var_f x1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_exp_abs_anno : lngen.

Lemma subst_exp_in_exp_exp_abs :
forall x2 e2 e1 x1,
  lc_exp e1 ->
  x2 `notin` fvar_in_exp e1 `union` fvar_in_exp e2 `union` singleton x1 ->
  subst_exp_in_exp e1 x1 (exp_abs e2) = exp_abs (close_exp_wrt_exp x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_exp_abs : lngen.

Lemma subst_exp_in_exp_exp_abs_anno :
forall x2 A1 e2 e1 x1,
  lc_exp e1 ->
  x2 `notin` fvar_in_exp e1 `union` fvar_in_exp e2 `union` singleton x1 ->
  subst_exp_in_exp e1 x1 (exp_abs_anno A1 e2) = exp_abs_anno (A1) (close_exp_wrt_exp x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_exp_abs_anno : lngen.

(* begin hide *)

Lemma subst_ptyp_in_ptyp_intro_rec_mutual :
(forall A1 Xpt1 A2 n1,
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  open_ptyp_wrt_ptyp_rec n1 A2 A1 = subst_ptyp_in_ptyp A2 Xpt1 (open_ptyp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) A1)).
Proof.
apply_mutual_ind ptyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ptyp_in_ptyp_intro_rec :
forall A1 Xpt1 A2 n1,
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  open_ptyp_wrt_ptyp_rec n1 A2 A1 = subst_ptyp_in_ptyp A2 Xpt1 (open_ptyp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) A1).
Proof.
pose proof subst_ptyp_in_ptyp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_ptyp_intro_rec : lngen.
#[export] Hint Rewrite subst_ptyp_in_ptyp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_btyp_in_btyp_intro_rec_mutual :
(forall B1 Xbt1 B2 n1,
  Xbt1 `notin` ftvar_in_btyp B1 ->
  open_btyp_wrt_btyp_rec n1 B2 B1 = subst_btyp_in_btyp B2 Xbt1 (open_btyp_wrt_btyp_rec n1 (btyp_var_f Xbt1) B1)).
Proof.
apply_mutual_ind btyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_btyp_in_btyp_intro_rec :
forall B1 Xbt1 B2 n1,
  Xbt1 `notin` ftvar_in_btyp B1 ->
  open_btyp_wrt_btyp_rec n1 B2 B1 = subst_btyp_in_btyp B2 Xbt1 (open_btyp_wrt_btyp_rec n1 (btyp_var_f Xbt1) B1).
Proof.
pose proof subst_btyp_in_btyp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_btyp_in_btyp_intro_rec : lngen.
#[export] Hint Rewrite subst_btyp_in_btyp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_utyp_in_utyp_intro_rec_mutual :
(forall C1 Xut1 C2 n1,
  Xut1 `notin` ftvar_in_utyp C1 ->
  open_utyp_wrt_utyp_rec n1 C2 C1 = subst_utyp_in_utyp C2 Xut1 (open_utyp_wrt_utyp_rec n1 (utyp_var_f Xut1) C1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_utyp_in_utyp_intro_rec :
forall C1 Xut1 C2 n1,
  Xut1 `notin` ftvar_in_utyp C1 ->
  open_utyp_wrt_utyp_rec n1 C2 C1 = subst_utyp_in_utyp C2 Xut1 (open_utyp_wrt_utyp_rec n1 (utyp_var_f Xut1) C1).
Proof.
pose proof subst_utyp_in_utyp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_intro_rec : lngen.
#[export] Hint Rewrite subst_utyp_in_utyp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_pskl_in_pskel_intro_rec_mutual :
(forall P1 Xps1 P2 n1,
  Xps1 `notin` ftvar_in_pskel P1 ->
  open_pskel_wrt_pskel_rec n1 P2 P1 = subst_pskl_in_pskel P2 Xps1 (open_pskel_wrt_pskel_rec n1 (pskel_var_f Xps1) P1)).
Proof.
apply_mutual_ind pskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pskl_in_pskel_intro_rec :
forall P1 Xps1 P2 n1,
  Xps1 `notin` ftvar_in_pskel P1 ->
  open_pskel_wrt_pskel_rec n1 P2 P1 = subst_pskl_in_pskel P2 Xps1 (open_pskel_wrt_pskel_rec n1 (pskel_var_f Xps1) P1).
Proof.
pose proof subst_pskl_in_pskel_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pskl_in_pskel_intro_rec : lngen.
#[export] Hint Rewrite subst_pskl_in_pskel_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_bskl_in_bskel_intro_rec_mutual :
(forall Q1 Xbs1 Q2 n1,
  Xbs1 `notin` ftvar_in_bskel Q1 ->
  open_bskel_wrt_bskel_rec n1 Q2 Q1 = subst_bskl_in_bskel Q2 Xbs1 (open_bskel_wrt_bskel_rec n1 (bskel_var_f Xbs1) Q1)).
Proof.
apply_mutual_ind bskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_bskl_in_bskel_intro_rec :
forall Q1 Xbs1 Q2 n1,
  Xbs1 `notin` ftvar_in_bskel Q1 ->
  open_bskel_wrt_bskel_rec n1 Q2 Q1 = subst_bskl_in_bskel Q2 Xbs1 (open_bskel_wrt_bskel_rec n1 (bskel_var_f Xbs1) Q1).
Proof.
pose proof subst_bskl_in_bskel_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bskl_in_bskel_intro_rec : lngen.
#[export] Hint Rewrite subst_bskl_in_bskel_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_bskl_in_uskel_intro_rec_mutual :
(forall R1 Xus1 R2 n1,
  Xus1 `notin` ftvar_in_uskel R1 ->
  open_uskel_wrt_uskel_rec n1 R2 R1 = subst_bskl_in_uskel R2 Xus1 (open_uskel_wrt_uskel_rec n1 (uskel_var_f Xus1) R1)).
Proof.
apply_mutual_ind uskel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_bskl_in_uskel_intro_rec :
forall R1 Xus1 R2 n1,
  Xus1 `notin` ftvar_in_uskel R1 ->
  open_uskel_wrt_uskel_rec n1 R2 R1 = subst_bskl_in_uskel R2 Xus1 (open_uskel_wrt_uskel_rec n1 (uskel_var_f Xus1) R1).
Proof.
pose proof subst_bskl_in_uskel_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bskl_in_uskel_intro_rec : lngen.
#[export] Hint Rewrite subst_bskl_in_uskel_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_ptyp_in_exp_intro_rec_mutual :
(forall e1 Xpt1 A1 n1,
  Xpt1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_ptyp_rec n1 A1 e1 = subst_ptyp_in_exp A1 Xpt1 (open_exp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ptyp_in_exp_intro_rec :
forall e1 Xpt1 A1 n1,
  Xpt1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_ptyp_rec n1 A1 e1 = subst_ptyp_in_exp A1 Xpt1 (open_exp_wrt_ptyp_rec n1 (ptyp_var_f Xpt1) e1).
Proof.
pose proof subst_ptyp_in_exp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_intro_rec : lngen.
#[export] Hint Rewrite subst_ptyp_in_exp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_intro_rec_mutual :
(forall e1 x1 e2 n1,
  x1 `notin` fvar_in_exp e1 ->
  open_exp_wrt_exp_rec n1 e2 e1 = subst_exp_in_exp e2 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` fvar_in_exp e1 ->
  open_exp_wrt_exp_rec n1 e2 e1 = subst_exp_in_exp e2 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1).
Proof.
pose proof subst_exp_in_exp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_intro_rec : lngen.
#[export] Hint Rewrite subst_exp_in_exp_intro_rec using solve [auto] : lngen.

Lemma subst_ptyp_in_ptyp_intro :
forall Xpt1 A1 A2,
  Xpt1 `notin` ftvar_in_ptyp A1 ->
  open_ptyp_wrt_ptyp A1 A2 = subst_ptyp_in_ptyp A2 Xpt1 (open_ptyp_wrt_ptyp A1 (ptyp_var_f Xpt1)).
Proof.
unfold open_ptyp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve subst_ptyp_in_ptyp_intro : lngen.

Lemma subst_btyp_in_btyp_intro :
forall Xbt1 B1 B2,
  Xbt1 `notin` ftvar_in_btyp B1 ->
  open_btyp_wrt_btyp B1 B2 = subst_btyp_in_btyp B2 Xbt1 (open_btyp_wrt_btyp B1 (btyp_var_f Xbt1)).
Proof.
unfold open_btyp_wrt_btyp; default_simp.
Qed.

#[export] Hint Resolve subst_btyp_in_btyp_intro : lngen.

Lemma subst_utyp_in_utyp_intro :
forall Xut1 C1 C2,
  Xut1 `notin` ftvar_in_utyp C1 ->
  open_utyp_wrt_utyp C1 C2 = subst_utyp_in_utyp C2 Xut1 (open_utyp_wrt_utyp C1 (utyp_var_f Xut1)).
Proof.
unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_intro : lngen.

Lemma subst_pskl_in_pskel_intro :
forall Xps1 P1 P2,
  Xps1 `notin` ftvar_in_pskel P1 ->
  open_pskel_wrt_pskel P1 P2 = subst_pskl_in_pskel P2 Xps1 (open_pskel_wrt_pskel P1 (pskel_var_f Xps1)).
Proof.
unfold open_pskel_wrt_pskel; default_simp.
Qed.

#[export] Hint Resolve subst_pskl_in_pskel_intro : lngen.

Lemma subst_bskl_in_bskel_intro :
forall Xbs1 Q1 Q2,
  Xbs1 `notin` ftvar_in_bskel Q1 ->
  open_bskel_wrt_bskel Q1 Q2 = subst_bskl_in_bskel Q2 Xbs1 (open_bskel_wrt_bskel Q1 (bskel_var_f Xbs1)).
Proof.
unfold open_bskel_wrt_bskel; default_simp.
Qed.

#[export] Hint Resolve subst_bskl_in_bskel_intro : lngen.

Lemma subst_bskl_in_uskel_intro :
forall Xus1 R1 R2,
  Xus1 `notin` ftvar_in_uskel R1 ->
  open_uskel_wrt_uskel R1 R2 = subst_bskl_in_uskel R2 Xus1 (open_uskel_wrt_uskel R1 (uskel_var_f Xus1)).
Proof.
unfold open_uskel_wrt_uskel; default_simp.
Qed.

#[export] Hint Resolve subst_bskl_in_uskel_intro : lngen.

Lemma subst_ptyp_in_exp_intro :
forall Xpt1 e1 A1,
  Xpt1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_ptyp e1 A1 = subst_ptyp_in_exp A1 Xpt1 (open_exp_wrt_ptyp e1 (ptyp_var_f Xpt1)).
Proof.
unfold open_exp_wrt_ptyp; default_simp.
Qed.

#[export] Hint Resolve subst_ptyp_in_exp_intro : lngen.

Lemma subst_exp_in_exp_intro :
forall x1 e1 e2,
  x1 `notin` fvar_in_exp e1 ->
  open_exp_wrt_exp e1 e2 = subst_exp_in_exp e2 x1 (open_exp_wrt_exp e1 (exp_var_f x1)).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
