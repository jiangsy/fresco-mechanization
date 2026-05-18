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

Scheme colour_ind' := Induction for colour Sort Prop.

Combined Scheme colour_mutind from colour_ind'.

Scheme colour_rec' := Induction for colour Sort Set.

Combined Scheme colour_mutrec from colour_rec'.

Scheme typ_ind' := Induction for typ Sort Prop.

Combined Scheme typ_mutind from typ_ind'.

Scheme typ_rec' := Induction for typ Sort Set.

Combined Scheme typ_mutrec from typ_rec'.

Scheme bid_ind' := Induction for bid Sort Prop.

Combined Scheme bid_mutind from bid_ind'.

Scheme bid_rec' := Induction for bid Sort Set.

Combined Scheme bid_mutrec from bid_rec'.

Scheme utyp_ind' := Induction for utyp Sort Prop.

Combined Scheme utyp_mutind from utyp_ind'.

Scheme utyp_rec' := Induction for utyp Sort Set.

Combined Scheme utyp_mutrec from utyp_rec'.

Scheme ctyp_ind' := Induction for ctyp Sort Prop.

Combined Scheme ctyp_mutind from ctyp_ind'.

Scheme ctyp_rec' := Induction for ctyp Sort Set.

Combined Scheme ctyp_mutrec from ctyp_rec'.

Scheme skel_ind' := Induction for skel Sort Prop.

Combined Scheme skel_mutind from skel_ind'.

Scheme skel_rec' := Induction for skel Sort Set.

Combined Scheme skel_mutrec from skel_rec'.

Scheme dbind_ind' := Induction for dbind Sort Prop.

Combined Scheme dbind_mutind from dbind_ind'.

Scheme dbind_rec' := Induction for dbind Sort Set.

Combined Scheme dbind_mutrec from dbind_rec'.

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

Fixpoint close_typ_wrt_typ_rec (n1 : nat) (X1 : typvar) (A1 : typ) {struct A1} : typ :=
  match A1 with
    | typ_unit => typ_unit
    | typ_var_f X2 => if (X1 == X2) then (typ_var_b n1) else (typ_var_f X2)
    | typ_var_b n2 => if (lt_ge_dec n2 n1) then (typ_var_b n2) else (typ_var_b (S n2))
    | typ_arrow A2 A3 => typ_arrow (close_typ_wrt_typ_rec n1 X1 A2) (close_typ_wrt_typ_rec n1 X1 A3)
    | typ_all_col c1 A2 => typ_all_col c1 (close_typ_wrt_typ_rec (S n1) X1 A2)
    | typ_all_etag ε1 A2 => typ_all_etag ε1 (close_typ_wrt_typ_rec (S n1) X1 A2)
    | typ_hole => typ_hole
    | typ_tophole A2 => typ_tophole (close_typ_wrt_typ_rec n1 X1 A2)
  end.

Definition close_typ_wrt_typ X1 A1 := close_typ_wrt_typ_rec 0 X1 A1.

Fixpoint close_bid_wrt_bid_rec (n1 : nat) (Xd1 : bidvar) (D1 : bid) {struct D1} : bid :=
  match D1 with
    | bid_unit => bid_unit
    | bid_var_f Xd2 => if (Xd1 == Xd2) then (bid_var_b n1) else (bid_var_f Xd2)
    | bid_var_b n2 => if (lt_ge_dec n2 n1) then (bid_var_b n2) else (bid_var_b (S n2))
    | bid_arrow D2 D3 => bid_arrow (close_bid_wrt_bid_rec n1 Xd1 D2) (close_bid_wrt_bid_rec n1 Xd1 D3)
    | bid_all_syn D2 => bid_all_syn (close_bid_wrt_bid_rec (S n1) Xd1 D2)
    | bid_all_inh D2 => bid_all_inh (close_bid_wrt_bid_rec (S n1) Xd1 D2)
    | bid_all_etag ε1 D2 => bid_all_etag ε1 (close_bid_wrt_bid_rec (S n1) Xd1 D2)
  end.

Definition close_bid_wrt_bid Xd1 D1 := close_bid_wrt_bid_rec 0 Xd1 D1.

Fixpoint close_utyp_wrt_utyp_rec (n1 : nat) (Xf1 : utypvar) (F1 : utyp) {struct F1} : utyp :=
  match F1 with
    | utyp_unit => utyp_unit
    | utyp_var_f Xf2 => if (Xf1 == Xf2) then (utyp_var_b n1) else (utyp_var_f Xf2)
    | utyp_var_b n2 => if (lt_ge_dec n2 n1) then (utyp_var_b n2) else (utyp_var_b (S n2))
    | utyp_arrow F2 F3 => utyp_arrow (close_utyp_wrt_utyp_rec n1 Xf1 F2) (close_utyp_wrt_utyp_rec n1 Xf1 F3)
    | utyp_all_syn F2 => utyp_all_syn (close_utyp_wrt_utyp_rec (S n1) Xf1 F2)
    | utyp_all_etag ε1 F2 => utyp_all_etag ε1 (close_utyp_wrt_utyp_rec (S n1) Xf1 F2)
  end.

Definition close_utyp_wrt_utyp Xf1 F1 := close_utyp_wrt_utyp_rec 0 Xf1 F1.

Fixpoint close_ctyp_wrt_ctyp_rec (n1 : nat) (U1 : ctypvar) (K1 : ctyp) {struct K1} : ctyp :=
  match K1 with
    | ctyp_unit => ctyp_unit
    | ctyp_var_f U2 => if (U1 == U2) then (ctyp_var_b n1) else (ctyp_var_f U2)
    | ctyp_var_b n2 => if (lt_ge_dec n2 n1) then (ctyp_var_b n2) else (ctyp_var_b (S n2))
    | ctyp_arrow K2 K3 => ctyp_arrow (close_ctyp_wrt_ctyp_rec n1 U1 K2) (close_ctyp_wrt_ctyp_rec n1 U1 K3)
    | ctyp_all K2 => ctyp_all (close_ctyp_wrt_ctyp_rec (S n1) U1 K2)
    | ctyp_hole => ctyp_hole
    | ctyp_tophole K2 => ctyp_tophole (close_ctyp_wrt_ctyp_rec n1 U1 K2)
  end.

Definition close_ctyp_wrt_ctyp U1 K1 := close_ctyp_wrt_ctyp_rec 0 U1 K1.

Fixpoint close_skel_wrt_skel_rec (n1 : nat) (Xr1 : skelvar) (R1 : skel) {struct R1} : skel :=
  match R1 with
    | skel_unit => skel_unit
    | skel_var_f Xr2 => if (Xr1 == Xr2) then (skel_var_b n1) else (skel_var_f Xr2)
    | skel_var_b n2 => if (lt_ge_dec n2 n1) then (skel_var_b n2) else (skel_var_b (S n2))
    | skel_arrow R2 R3 => skel_arrow (close_skel_wrt_skel_rec n1 Xr1 R2) (close_skel_wrt_skel_rec n1 Xr1 R3)
    | skel_all_syn R2 => skel_all_syn (close_skel_wrt_skel_rec (S n1) Xr1 R2)
    | skel_all_inh R2 => skel_all_inh (close_skel_wrt_skel_rec (S n1) Xr1 R2)
    | skel_all_etag ε1 R2 => skel_all_etag ε1 (close_skel_wrt_skel_rec (S n1) Xr1 R2)
    | skel_hole => skel_hole
    | skel_tophole R2 => skel_tophole (close_skel_wrt_skel_rec n1 Xr1 R2)
  end.

Definition close_skel_wrt_skel Xr1 R1 := close_skel_wrt_skel_rec 0 Xr1 R1.

Fixpoint close_dbind_wrt_typ_rec (n1 : nat) (X1 : typvar) (db1 : dbind) {struct db1} : dbind :=
  match db1 with
    | dbind_tvar => dbind_tvar
    | dbind_typ A1 => dbind_typ (close_typ_wrt_typ_rec n1 X1 A1)
    | dbind_skel P1 => dbind_skel (close_typ_wrt_typ_rec n1 X1 P1)
  end.

Definition close_dbind_wrt_typ X1 db1 := close_dbind_wrt_typ_rec 0 X1 db1.

Fixpoint close_exp_wrt_typ_rec (n1 : nat) (X1 : typvar) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | exp_unit => exp_unit
    | exp_var_f x1 => exp_var_f x1
    | exp_var_b n2 => exp_var_b n2
    | exp_abs e2 => exp_abs (close_exp_wrt_typ_rec n1 X1 e2)
    | exp_abs_anno A1 e2 => exp_abs_anno (close_typ_wrt_typ_rec n1 X1 A1) (close_exp_wrt_typ_rec n1 X1 e2)
    | exp_app e2 e3 => exp_app (close_exp_wrt_typ_rec n1 X1 e2) (close_exp_wrt_typ_rec n1 X1 e3)
    | exp_anno e2 A1 => exp_anno (close_exp_wrt_typ_rec n1 X1 e2) (close_typ_wrt_typ_rec n1 X1 A1)
    | exp_freeze e2 => exp_freeze (close_exp_wrt_typ_rec n1 X1 e2)
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

Definition close_exp_wrt_typ X1 e1 := close_exp_wrt_typ_rec 0 X1 e1.

Definition close_exp_wrt_exp x1 e1 := close_exp_wrt_exp_rec 0 x1 e1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_colour (c1 : colour) {struct c1} : nat :=
  match c1 with
    | colour_syn => 1
    | colour_inh => 1
  end.

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | typ_unit => 1
    | typ_var_f X1 => 1
    | typ_var_b n1 => 1
    | typ_arrow A2 A3 => 1 + (size_typ A2) + (size_typ A3)
    | typ_all_col c1 A2 => 1 + (size_colour c1) + (size_typ A2)
    | typ_all_etag ε1 A2 => 1 + (size_typ A2)
    | typ_hole => 1
    | typ_tophole A2 => 1 + (size_typ A2)
  end.

Fixpoint size_bid (D1 : bid) {struct D1} : nat :=
  match D1 with
    | bid_unit => 1
    | bid_var_f Xd1 => 1
    | bid_var_b n1 => 1
    | bid_arrow D2 D3 => 1 + (size_bid D2) + (size_bid D3)
    | bid_all_syn D2 => 1 + (size_bid D2)
    | bid_all_inh D2 => 1 + (size_bid D2)
    | bid_all_etag ε1 D2 => 1 + (size_bid D2)
  end.

Fixpoint size_utyp (F1 : utyp) {struct F1} : nat :=
  match F1 with
    | utyp_unit => 1
    | utyp_var_f Xf1 => 1
    | utyp_var_b n1 => 1
    | utyp_arrow F2 F3 => 1 + (size_utyp F2) + (size_utyp F3)
    | utyp_all_syn F2 => 1 + (size_utyp F2)
    | utyp_all_etag ε1 F2 => 1 + (size_utyp F2)
  end.

Fixpoint size_ctyp (K1 : ctyp) {struct K1} : nat :=
  match K1 with
    | ctyp_unit => 1
    | ctyp_var_f U1 => 1
    | ctyp_var_b n1 => 1
    | ctyp_arrow K2 K3 => 1 + (size_ctyp K2) + (size_ctyp K3)
    | ctyp_all K2 => 1 + (size_ctyp K2)
    | ctyp_hole => 1
    | ctyp_tophole K2 => 1 + (size_ctyp K2)
  end.

Fixpoint size_skel (R1 : skel) {struct R1} : nat :=
  match R1 with
    | skel_unit => 1
    | skel_var_f Xr1 => 1
    | skel_var_b n1 => 1
    | skel_arrow R2 R3 => 1 + (size_skel R2) + (size_skel R3)
    | skel_all_syn R2 => 1 + (size_skel R2)
    | skel_all_inh R2 => 1 + (size_skel R2)
    | skel_all_etag ε1 R2 => 1 + (size_skel R2)
    | skel_hole => 1
    | skel_tophole R2 => 1 + (size_skel R2)
  end.

Fixpoint size_dbind (db1 : dbind) {struct db1} : nat :=
  match db1 with
    | dbind_tvar => 1
    | dbind_typ A1 => 1 + (size_typ A1)
    | dbind_skel P1 => 1 + (size_typ P1)
  end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | exp_unit => 1
    | exp_var_f x1 => 1
    | exp_var_b n1 => 1
    | exp_abs e2 => 1 + (size_exp e2)
    | exp_abs_anno A1 e2 => 1 + (size_typ A1) + (size_exp e2)
    | exp_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | exp_anno e2 A1 => 1 + (size_exp e2) + (size_typ A1)
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

Inductive degree_typ_wrt_typ : nat -> typ -> Prop :=
  | degree_wrt_typ_typ_unit : forall n1,
    degree_typ_wrt_typ n1 (typ_unit)
  | degree_wrt_typ_typ_var_f : forall n1 X1,
    degree_typ_wrt_typ n1 (typ_var_f X1)
  | degree_wrt_typ_typ_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_typ_wrt_typ n1 (typ_var_b n2)
  | degree_wrt_typ_typ_arrow : forall n1 A1 A2,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_typ_wrt_typ n1 (typ_arrow A1 A2)
  | degree_wrt_typ_typ_all_col : forall n1 c1 A1,
    degree_typ_wrt_typ (S n1) A1 ->
    degree_typ_wrt_typ n1 (typ_all_col c1 A1)
  | degree_wrt_typ_typ_all_etag : forall n1 ε1 A1,
    degree_typ_wrt_typ (S n1) A1 ->
    degree_typ_wrt_typ n1 (typ_all_etag ε1 A1)
  | degree_wrt_typ_typ_hole : forall n1,
    degree_typ_wrt_typ n1 (typ_hole)
  | degree_wrt_typ_typ_tophole : forall n1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 (typ_tophole A1).

Scheme degree_typ_wrt_typ_ind' := Induction for degree_typ_wrt_typ Sort Prop.

Combined Scheme degree_typ_wrt_typ_mutind from degree_typ_wrt_typ_ind'.

#[export] Hint Constructors degree_typ_wrt_typ : core lngen.

Inductive degree_bid_wrt_bid : nat -> bid -> Prop :=
  | degree_wrt_bid_bid_unit : forall n1,
    degree_bid_wrt_bid n1 (bid_unit)
  | degree_wrt_bid_bid_var_f : forall n1 Xd1,
    degree_bid_wrt_bid n1 (bid_var_f Xd1)
  | degree_wrt_bid_bid_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_bid_wrt_bid n1 (bid_var_b n2)
  | degree_wrt_bid_bid_arrow : forall n1 D1 D2,
    degree_bid_wrt_bid n1 D1 ->
    degree_bid_wrt_bid n1 D2 ->
    degree_bid_wrt_bid n1 (bid_arrow D1 D2)
  | degree_wrt_bid_bid_all_syn : forall n1 D1,
    degree_bid_wrt_bid (S n1) D1 ->
    degree_bid_wrt_bid n1 (bid_all_syn D1)
  | degree_wrt_bid_bid_all_inh : forall n1 D1,
    degree_bid_wrt_bid (S n1) D1 ->
    degree_bid_wrt_bid n1 (bid_all_inh D1)
  | degree_wrt_bid_bid_all_etag : forall n1 ε1 D1,
    degree_bid_wrt_bid (S n1) D1 ->
    degree_bid_wrt_bid n1 (bid_all_etag ε1 D1).

Scheme degree_bid_wrt_bid_ind' := Induction for degree_bid_wrt_bid Sort Prop.

Combined Scheme degree_bid_wrt_bid_mutind from degree_bid_wrt_bid_ind'.

#[export] Hint Constructors degree_bid_wrt_bid : core lngen.

Inductive degree_utyp_wrt_utyp : nat -> utyp -> Prop :=
  | degree_wrt_utyp_utyp_unit : forall n1,
    degree_utyp_wrt_utyp n1 (utyp_unit)
  | degree_wrt_utyp_utyp_var_f : forall n1 Xf1,
    degree_utyp_wrt_utyp n1 (utyp_var_f Xf1)
  | degree_wrt_utyp_utyp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_utyp_wrt_utyp n1 (utyp_var_b n2)
  | degree_wrt_utyp_utyp_arrow : forall n1 F1 F2,
    degree_utyp_wrt_utyp n1 F1 ->
    degree_utyp_wrt_utyp n1 F2 ->
    degree_utyp_wrt_utyp n1 (utyp_arrow F1 F2)
  | degree_wrt_utyp_utyp_all_syn : forall n1 F1,
    degree_utyp_wrt_utyp (S n1) F1 ->
    degree_utyp_wrt_utyp n1 (utyp_all_syn F1)
  | degree_wrt_utyp_utyp_all_etag : forall n1 ε1 F1,
    degree_utyp_wrt_utyp (S n1) F1 ->
    degree_utyp_wrt_utyp n1 (utyp_all_etag ε1 F1).

Scheme degree_utyp_wrt_utyp_ind' := Induction for degree_utyp_wrt_utyp Sort Prop.

Combined Scheme degree_utyp_wrt_utyp_mutind from degree_utyp_wrt_utyp_ind'.

#[export] Hint Constructors degree_utyp_wrt_utyp : core lngen.

Inductive degree_ctyp_wrt_ctyp : nat -> ctyp -> Prop :=
  | degree_wrt_ctyp_ctyp_unit : forall n1,
    degree_ctyp_wrt_ctyp n1 (ctyp_unit)
  | degree_wrt_ctyp_ctyp_var_f : forall n1 U1,
    degree_ctyp_wrt_ctyp n1 (ctyp_var_f U1)
  | degree_wrt_ctyp_ctyp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_ctyp_wrt_ctyp n1 (ctyp_var_b n2)
  | degree_wrt_ctyp_ctyp_arrow : forall n1 K1 K2,
    degree_ctyp_wrt_ctyp n1 K1 ->
    degree_ctyp_wrt_ctyp n1 K2 ->
    degree_ctyp_wrt_ctyp n1 (ctyp_arrow K1 K2)
  | degree_wrt_ctyp_ctyp_all : forall n1 K1,
    degree_ctyp_wrt_ctyp (S n1) K1 ->
    degree_ctyp_wrt_ctyp n1 (ctyp_all K1)
  | degree_wrt_ctyp_ctyp_hole : forall n1,
    degree_ctyp_wrt_ctyp n1 (ctyp_hole)
  | degree_wrt_ctyp_ctyp_tophole : forall n1 K1,
    degree_ctyp_wrt_ctyp n1 K1 ->
    degree_ctyp_wrt_ctyp n1 (ctyp_tophole K1).

Scheme degree_ctyp_wrt_ctyp_ind' := Induction for degree_ctyp_wrt_ctyp Sort Prop.

Combined Scheme degree_ctyp_wrt_ctyp_mutind from degree_ctyp_wrt_ctyp_ind'.

#[export] Hint Constructors degree_ctyp_wrt_ctyp : core lngen.

Inductive degree_skel_wrt_skel : nat -> skel -> Prop :=
  | degree_wrt_skel_skel_unit : forall n1,
    degree_skel_wrt_skel n1 (skel_unit)
  | degree_wrt_skel_skel_var_f : forall n1 Xr1,
    degree_skel_wrt_skel n1 (skel_var_f Xr1)
  | degree_wrt_skel_skel_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_skel_wrt_skel n1 (skel_var_b n2)
  | degree_wrt_skel_skel_arrow : forall n1 R1 R2,
    degree_skel_wrt_skel n1 R1 ->
    degree_skel_wrt_skel n1 R2 ->
    degree_skel_wrt_skel n1 (skel_arrow R1 R2)
  | degree_wrt_skel_skel_all_syn : forall n1 R1,
    degree_skel_wrt_skel (S n1) R1 ->
    degree_skel_wrt_skel n1 (skel_all_syn R1)
  | degree_wrt_skel_skel_all_inh : forall n1 R1,
    degree_skel_wrt_skel (S n1) R1 ->
    degree_skel_wrt_skel n1 (skel_all_inh R1)
  | degree_wrt_skel_skel_all_etag : forall n1 ε1 R1,
    degree_skel_wrt_skel (S n1) R1 ->
    degree_skel_wrt_skel n1 (skel_all_etag ε1 R1)
  | degree_wrt_skel_skel_hole : forall n1,
    degree_skel_wrt_skel n1 (skel_hole)
  | degree_wrt_skel_skel_tophole : forall n1 R1,
    degree_skel_wrt_skel n1 R1 ->
    degree_skel_wrt_skel n1 (skel_tophole R1).

Scheme degree_skel_wrt_skel_ind' := Induction for degree_skel_wrt_skel Sort Prop.

Combined Scheme degree_skel_wrt_skel_mutind from degree_skel_wrt_skel_ind'.

#[export] Hint Constructors degree_skel_wrt_skel : core lngen.

Inductive degree_dbind_wrt_typ : nat -> dbind -> Prop :=
  | degree_wrt_typ_dbind_tvar : forall n1,
    degree_dbind_wrt_typ n1 (dbind_tvar)
  | degree_wrt_typ_dbind_typ : forall n1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_dbind_wrt_typ n1 (dbind_typ A1)
  | degree_wrt_typ_dbind_skel : forall n1 P1,
    degree_typ_wrt_typ n1 P1 ->
    degree_dbind_wrt_typ n1 (dbind_skel P1).

Scheme degree_dbind_wrt_typ_ind' := Induction for degree_dbind_wrt_typ Sort Prop.

Combined Scheme degree_dbind_wrt_typ_mutind from degree_dbind_wrt_typ_ind'.

#[export] Hint Constructors degree_dbind_wrt_typ : core lngen.

Inductive degree_exp_wrt_typ : nat -> exp -> Prop :=
  | degree_wrt_typ_exp_unit : forall n1,
    degree_exp_wrt_typ n1 (exp_unit)
  | degree_wrt_typ_exp_var_f : forall n1 x1,
    degree_exp_wrt_typ n1 (exp_var_f x1)
  | degree_wrt_typ_exp_var_b : forall n1 n2,
    degree_exp_wrt_typ n1 (exp_var_b n2)
  | degree_wrt_typ_exp_abs : forall n1 e1,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (exp_abs e1)
  | degree_wrt_typ_exp_abs_anno : forall n1 A1 e1,
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (exp_abs_anno A1 e1)
  | degree_wrt_typ_exp_app : forall n1 e1 e2,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 e2 ->
    degree_exp_wrt_typ n1 (exp_app e1 e2)
  | degree_wrt_typ_exp_anno : forall n1 e1 A1,
    degree_exp_wrt_typ n1 e1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 (exp_anno e1 A1)
  | degree_wrt_typ_exp_freeze : forall n1 e1,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (exp_freeze e1).

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

Scheme degree_exp_wrt_typ_ind' := Induction for degree_exp_wrt_typ Sort Prop.

Combined Scheme degree_exp_wrt_typ_mutind from degree_exp_wrt_typ_ind'.

Scheme degree_exp_wrt_exp_ind' := Induction for degree_exp_wrt_exp Sort Prop.

Combined Scheme degree_exp_wrt_exp_mutind from degree_exp_wrt_exp_ind'.

#[export] Hint Constructors degree_exp_wrt_typ : core lngen.

#[export] Hint Constructors degree_exp_wrt_exp : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_typ : typ -> Set :=
  | lc_set_typ_unit :
    lc_set_typ (typ_unit)
  | lc_set_typ_var_f : forall X1,
    lc_set_typ (typ_var_f X1)
  | lc_set_typ_arrow : forall A1 A2,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_typ (typ_arrow A1 A2)
  | lc_set_typ_all_col : forall c1 A1,
    (forall X1 : typvar, lc_set_typ (open_typ_wrt_typ A1 (typ_var_f X1))) ->
    lc_set_typ (typ_all_col c1 A1)
  | lc_set_typ_all_etag : forall ε1 A1,
    (forall X1 : typvar, lc_set_typ (open_typ_wrt_typ A1 (typ_var_f X1))) ->
    lc_set_typ (typ_all_etag ε1 A1)
  | lc_set_typ_hole :
    lc_set_typ (typ_hole)
  | lc_set_typ_tophole : forall A1,
    lc_set_typ A1 ->
    lc_set_typ (typ_tophole A1).
Scheme lc_typ_ind' := Induction for lc_typ Sort Prop.

Combined Scheme lc_typ_mutind from lc_typ_ind'.

Scheme lc_set_typ_ind' := Induction for lc_set_typ Sort Prop.

Combined Scheme lc_set_typ_mutind from lc_set_typ_ind'.

Scheme lc_set_typ_rec' := Induction for lc_set_typ Sort Set.

Combined Scheme lc_set_typ_mutrec from lc_set_typ_rec'.

#[export] Hint Constructors lc_typ : core lngen.

#[export] Hint Constructors lc_set_typ : core lngen.

Inductive lc_set_bid : bid -> Set :=
  | lc_set_bid_unit :
    lc_set_bid (bid_unit)
  | lc_set_bid_var_f : forall Xd1,
    lc_set_bid (bid_var_f Xd1)
  | lc_set_bid_arrow : forall D1 D2,
    lc_set_bid D1 ->
    lc_set_bid D2 ->
    lc_set_bid (bid_arrow D1 D2)
  | lc_set_bid_all_syn : forall D1,
    (forall Xd1 : bidvar, lc_set_bid (open_bid_wrt_bid D1 (bid_var_f Xd1))) ->
    lc_set_bid (bid_all_syn D1)
  | lc_set_bid_all_inh : forall D1,
    (forall Xd1 : bidvar, lc_set_bid (open_bid_wrt_bid D1 (bid_var_f Xd1))) ->
    lc_set_bid (bid_all_inh D1)
  | lc_set_bid_all_etag : forall ε1 D1,
    (forall Xd1 : bidvar, lc_set_bid (open_bid_wrt_bid D1 (bid_var_f Xd1))) ->
    lc_set_bid (bid_all_etag ε1 D1).
Scheme lc_bid_ind' := Induction for lc_bid Sort Prop.

Combined Scheme lc_bid_mutind from lc_bid_ind'.

Scheme lc_set_bid_ind' := Induction for lc_set_bid Sort Prop.

Combined Scheme lc_set_bid_mutind from lc_set_bid_ind'.

Scheme lc_set_bid_rec' := Induction for lc_set_bid Sort Set.

Combined Scheme lc_set_bid_mutrec from lc_set_bid_rec'.

#[export] Hint Constructors lc_bid : core lngen.

#[export] Hint Constructors lc_set_bid : core lngen.

Inductive lc_set_utyp : utyp -> Set :=
  | lc_set_utyp_unit :
    lc_set_utyp (utyp_unit)
  | lc_set_utyp_var_f : forall Xf1,
    lc_set_utyp (utyp_var_f Xf1)
  | lc_set_utyp_arrow : forall F1 F2,
    lc_set_utyp F1 ->
    lc_set_utyp F2 ->
    lc_set_utyp (utyp_arrow F1 F2)
  | lc_set_utyp_all_syn : forall F1,
    (forall Xf1 : utypvar, lc_set_utyp (open_utyp_wrt_utyp F1 (utyp_var_f Xf1))) ->
    lc_set_utyp (utyp_all_syn F1)
  | lc_set_utyp_all_etag : forall ε1 F1,
    (forall Xf1 : utypvar, lc_set_utyp (open_utyp_wrt_utyp F1 (utyp_var_f Xf1))) ->
    lc_set_utyp (utyp_all_etag ε1 F1).
Scheme lc_utyp_ind' := Induction for lc_utyp Sort Prop.

Combined Scheme lc_utyp_mutind from lc_utyp_ind'.

Scheme lc_set_utyp_ind' := Induction for lc_set_utyp Sort Prop.

Combined Scheme lc_set_utyp_mutind from lc_set_utyp_ind'.

Scheme lc_set_utyp_rec' := Induction for lc_set_utyp Sort Set.

Combined Scheme lc_set_utyp_mutrec from lc_set_utyp_rec'.

#[export] Hint Constructors lc_utyp : core lngen.

#[export] Hint Constructors lc_set_utyp : core lngen.

Inductive lc_set_ctyp : ctyp -> Set :=
  | lc_set_ctyp_unit :
    lc_set_ctyp (ctyp_unit)
  | lc_set_ctyp_var_f : forall U1,
    lc_set_ctyp (ctyp_var_f U1)
  | lc_set_ctyp_arrow : forall K1 K2,
    lc_set_ctyp K1 ->
    lc_set_ctyp K2 ->
    lc_set_ctyp (ctyp_arrow K1 K2)
  | lc_set_ctyp_all : forall K1,
    (forall U1 : ctypvar, lc_set_ctyp (open_ctyp_wrt_ctyp K1 (ctyp_var_f U1))) ->
    lc_set_ctyp (ctyp_all K1)
  | lc_set_ctyp_hole :
    lc_set_ctyp (ctyp_hole)
  | lc_set_ctyp_tophole : forall K1,
    lc_set_ctyp K1 ->
    lc_set_ctyp (ctyp_tophole K1).
Scheme lc_ctyp_ind' := Induction for lc_ctyp Sort Prop.

Combined Scheme lc_ctyp_mutind from lc_ctyp_ind'.

Scheme lc_set_ctyp_ind' := Induction for lc_set_ctyp Sort Prop.

Combined Scheme lc_set_ctyp_mutind from lc_set_ctyp_ind'.

Scheme lc_set_ctyp_rec' := Induction for lc_set_ctyp Sort Set.

Combined Scheme lc_set_ctyp_mutrec from lc_set_ctyp_rec'.

#[export] Hint Constructors lc_ctyp : core lngen.

#[export] Hint Constructors lc_set_ctyp : core lngen.

Inductive lc_set_skel : skel -> Set :=
  | lc_set_skel_unit :
    lc_set_skel (skel_unit)
  | lc_set_skel_var_f : forall Xr1,
    lc_set_skel (skel_var_f Xr1)
  | lc_set_skel_arrow : forall R1 R2,
    lc_set_skel R1 ->
    lc_set_skel R2 ->
    lc_set_skel (skel_arrow R1 R2)
  | lc_set_skel_all_syn : forall R1,
    (forall Xr1 : skelvar, lc_set_skel (open_skel_wrt_skel R1 (skel_var_f Xr1))) ->
    lc_set_skel (skel_all_syn R1)
  | lc_set_skel_all_inh : forall R1,
    (forall Xr1 : skelvar, lc_set_skel (open_skel_wrt_skel R1 (skel_var_f Xr1))) ->
    lc_set_skel (skel_all_inh R1)
  | lc_set_skel_all_etag : forall ε1 R1,
    (forall Xr1 : skelvar, lc_set_skel (open_skel_wrt_skel R1 (skel_var_f Xr1))) ->
    lc_set_skel (skel_all_etag ε1 R1)
  | lc_set_skel_hole :
    lc_set_skel (skel_hole)
  | lc_set_skel_tophole : forall R1,
    lc_set_skel R1 ->
    lc_set_skel (skel_tophole R1).
Scheme lc_skel_ind' := Induction for lc_skel Sort Prop.

Combined Scheme lc_skel_mutind from lc_skel_ind'.

Scheme lc_set_skel_ind' := Induction for lc_set_skel Sort Prop.

Combined Scheme lc_set_skel_mutind from lc_set_skel_ind'.

Scheme lc_set_skel_rec' := Induction for lc_set_skel Sort Set.

Combined Scheme lc_set_skel_mutrec from lc_set_skel_rec'.

#[export] Hint Constructors lc_skel : core lngen.

#[export] Hint Constructors lc_set_skel : core lngen.

Inductive lc_set_dbind : dbind -> Set :=
  | lc_set_dbind_tvar :
    lc_set_dbind (dbind_tvar)
  | lc_set_dbind_typ : forall A1,
    lc_set_typ A1 ->
    lc_set_dbind (dbind_typ A1)
  | lc_set_dbind_skel : forall P1,
    lc_set_typ P1 ->
    lc_set_dbind (dbind_skel P1).
Scheme lc_dbind_ind' := Induction for lc_dbind Sort Prop.

Combined Scheme lc_dbind_mutind from lc_dbind_ind'.

Scheme lc_set_dbind_ind' := Induction for lc_set_dbind Sort Prop.

Combined Scheme lc_set_dbind_mutind from lc_set_dbind_ind'.

Scheme lc_set_dbind_rec' := Induction for lc_set_dbind Sort Set.

Combined Scheme lc_set_dbind_mutrec from lc_set_dbind_rec'.

#[export] Hint Constructors lc_dbind : core lngen.

#[export] Hint Constructors lc_set_dbind : core lngen.

Inductive lc_set_exp : exp -> Set :=
  | lc_set_exp_unit :
    lc_set_exp (exp_unit)
  | lc_set_exp_var_f : forall x1,
    lc_set_exp (exp_var_f x1)
  | lc_set_exp_abs : forall e1,
    (forall x1 : expvar, lc_set_exp (open_exp_wrt_exp e1 (exp_var_f x1))) ->
    lc_set_exp (exp_abs e1)
  | lc_set_exp_abs_anno : forall A1 e1,
    lc_set_typ A1 ->
    (forall x1 : expvar, lc_set_exp (open_exp_wrt_exp e1 (exp_var_f x1))) ->
    lc_set_exp (exp_abs_anno A1 e1)
  | lc_set_exp_app : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (exp_app e1 e2)
  | lc_set_exp_anno : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_typ A1 ->
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

Definition body_typ_wrt_typ A1 := forall X1, lc_typ (open_typ_wrt_typ A1 (typ_var_f X1)).

#[export] Hint Unfold body_typ_wrt_typ : core.

Definition body_bid_wrt_bid D1 := forall Xd1, lc_bid (open_bid_wrt_bid D1 (bid_var_f Xd1)).

#[export] Hint Unfold body_bid_wrt_bid : core.

Definition body_utyp_wrt_utyp F1 := forall Xf1, lc_utyp (open_utyp_wrt_utyp F1 (utyp_var_f Xf1)).

#[export] Hint Unfold body_utyp_wrt_utyp : core.

Definition body_ctyp_wrt_ctyp K1 := forall U1, lc_ctyp (open_ctyp_wrt_ctyp K1 (ctyp_var_f U1)).

#[export] Hint Unfold body_ctyp_wrt_ctyp : core.

Definition body_skel_wrt_skel R1 := forall Xr1, lc_skel (open_skel_wrt_skel R1 (skel_var_f Xr1)).

#[export] Hint Unfold body_skel_wrt_skel : core.

Definition body_dbind_wrt_typ db1 := forall X1, lc_dbind (open_dbind_wrt_typ db1 (typ_var_f X1)).

#[export] Hint Unfold body_dbind_wrt_typ : core.

Definition body_exp_wrt_typ e1 := forall X1, lc_exp (open_exp_wrt_typ e1 (typ_var_f X1)).

Definition body_exp_wrt_exp e1 := forall x1, lc_exp (open_exp_wrt_exp e1 (exp_var_f x1)).

#[export] Hint Unfold body_exp_wrt_typ : core.

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

Lemma size_colour_min_mutual :
(forall c1, 1 <= size_colour c1).
Proof.
apply_mutual_ind colour_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_colour_min :
forall c1, 1 <= size_colour c1.
Proof.
pose proof size_colour_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_colour_min : lngen.

(* begin hide *)

Lemma size_typ_min_mutual :
(forall A1, 1 <= size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_typ_min :
forall A1, 1 <= size_typ A1.
Proof.
pose proof size_typ_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_typ_min : lngen.

(* begin hide *)

Lemma size_bid_min_mutual :
(forall D1, 1 <= size_bid D1).
Proof.
apply_mutual_ind bid_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_bid_min :
forall D1, 1 <= size_bid D1.
Proof.
pose proof size_bid_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_bid_min : lngen.

(* begin hide *)

Lemma size_utyp_min_mutual :
(forall F1, 1 <= size_utyp F1).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_utyp_min :
forall F1, 1 <= size_utyp F1.
Proof.
pose proof size_utyp_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_utyp_min : lngen.

(* begin hide *)

Lemma size_ctyp_min_mutual :
(forall K1, 1 <= size_ctyp K1).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_ctyp_min :
forall K1, 1 <= size_ctyp K1.
Proof.
pose proof size_ctyp_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ctyp_min : lngen.

(* begin hide *)

Lemma size_skel_min_mutual :
(forall R1, 1 <= size_skel R1).
Proof.
apply_mutual_ind skel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_skel_min :
forall R1, 1 <= size_skel R1.
Proof.
pose proof size_skel_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_skel_min : lngen.

(* begin hide *)

Lemma size_dbind_min_mutual :
(forall db1, 1 <= size_dbind db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_dbind_min :
forall db1, 1 <= size_dbind db1.
Proof.
pose proof size_dbind_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dbind_min : lngen.

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

Lemma size_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  size_typ (close_typ_wrt_typ_rec n1 X1 A1) = size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  size_typ (close_typ_wrt_typ_rec n1 X1 A1) = size_typ A1.
Proof.
pose proof size_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_typ_close_typ_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_typ_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_bid_close_bid_wrt_bid_rec_mutual :
(forall D1 Xd1 n1,
  size_bid (close_bid_wrt_bid_rec n1 Xd1 D1) = size_bid D1).
Proof.
apply_mutual_ind bid_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_bid_close_bid_wrt_bid_rec :
forall D1 Xd1 n1,
  size_bid (close_bid_wrt_bid_rec n1 Xd1 D1) = size_bid D1.
Proof.
pose proof size_bid_close_bid_wrt_bid_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_bid_close_bid_wrt_bid_rec : lngen.
#[export] Hint Rewrite size_bid_close_bid_wrt_bid_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_utyp_close_utyp_wrt_utyp_rec_mutual :
(forall F1 Xf1 n1,
  size_utyp (close_utyp_wrt_utyp_rec n1 Xf1 F1) = size_utyp F1).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_utyp_close_utyp_wrt_utyp_rec :
forall F1 Xf1 n1,
  size_utyp (close_utyp_wrt_utyp_rec n1 Xf1 F1) = size_utyp F1.
Proof.
pose proof size_utyp_close_utyp_wrt_utyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_utyp_close_utyp_wrt_utyp_rec : lngen.
#[export] Hint Rewrite size_utyp_close_utyp_wrt_utyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_ctyp_close_ctyp_wrt_ctyp_rec_mutual :
(forall K1 U1 n1,
  size_ctyp (close_ctyp_wrt_ctyp_rec n1 U1 K1) = size_ctyp K1).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_ctyp_close_ctyp_wrt_ctyp_rec :
forall K1 U1 n1,
  size_ctyp (close_ctyp_wrt_ctyp_rec n1 U1 K1) = size_ctyp K1.
Proof.
pose proof size_ctyp_close_ctyp_wrt_ctyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ctyp_close_ctyp_wrt_ctyp_rec : lngen.
#[export] Hint Rewrite size_ctyp_close_ctyp_wrt_ctyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_skel_close_skel_wrt_skel_rec_mutual :
(forall R1 Xr1 n1,
  size_skel (close_skel_wrt_skel_rec n1 Xr1 R1) = size_skel R1).
Proof.
apply_mutual_ind skel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_skel_close_skel_wrt_skel_rec :
forall R1 Xr1 n1,
  size_skel (close_skel_wrt_skel_rec n1 Xr1 R1) = size_skel R1.
Proof.
pose proof size_skel_close_skel_wrt_skel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_skel_close_skel_wrt_skel_rec : lngen.
#[export] Hint Rewrite size_skel_close_skel_wrt_skel_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dbind_close_dbind_wrt_typ_rec_mutual :
(forall db1 X1 n1,
  size_dbind (close_dbind_wrt_typ_rec n1 X1 db1) = size_dbind db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dbind_close_dbind_wrt_typ_rec :
forall db1 X1 n1,
  size_dbind (close_dbind_wrt_typ_rec n1 X1 db1) = size_dbind db1.
Proof.
pose proof size_dbind_close_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dbind_close_dbind_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_dbind_close_dbind_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  size_exp (close_exp_wrt_typ_rec n1 X1 e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  size_exp (close_exp_wrt_typ_rec n1 X1 e1) = size_exp e1.
Proof.
pose proof size_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

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

Lemma size_typ_close_typ_wrt_typ :
forall A1 X1,
  size_typ (close_typ_wrt_typ X1 A1) = size_typ A1.
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_typ_close_typ_wrt_typ : lngen.
#[export] Hint Rewrite size_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma size_bid_close_bid_wrt_bid :
forall D1 Xd1,
  size_bid (close_bid_wrt_bid Xd1 D1) = size_bid D1.
Proof.
unfold close_bid_wrt_bid; default_simp.
Qed.

#[export] Hint Resolve size_bid_close_bid_wrt_bid : lngen.
#[export] Hint Rewrite size_bid_close_bid_wrt_bid using solve [auto] : lngen.

Lemma size_utyp_close_utyp_wrt_utyp :
forall F1 Xf1,
  size_utyp (close_utyp_wrt_utyp Xf1 F1) = size_utyp F1.
Proof.
unfold close_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve size_utyp_close_utyp_wrt_utyp : lngen.
#[export] Hint Rewrite size_utyp_close_utyp_wrt_utyp using solve [auto] : lngen.

Lemma size_ctyp_close_ctyp_wrt_ctyp :
forall K1 U1,
  size_ctyp (close_ctyp_wrt_ctyp U1 K1) = size_ctyp K1.
Proof.
unfold close_ctyp_wrt_ctyp; default_simp.
Qed.

#[export] Hint Resolve size_ctyp_close_ctyp_wrt_ctyp : lngen.
#[export] Hint Rewrite size_ctyp_close_ctyp_wrt_ctyp using solve [auto] : lngen.

Lemma size_skel_close_skel_wrt_skel :
forall R1 Xr1,
  size_skel (close_skel_wrt_skel Xr1 R1) = size_skel R1.
Proof.
unfold close_skel_wrt_skel; default_simp.
Qed.

#[export] Hint Resolve size_skel_close_skel_wrt_skel : lngen.
#[export] Hint Rewrite size_skel_close_skel_wrt_skel using solve [auto] : lngen.

Lemma size_dbind_close_dbind_wrt_typ :
forall db1 X1,
  size_dbind (close_dbind_wrt_typ X1 db1) = size_dbind db1.
Proof.
unfold close_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_dbind_close_dbind_wrt_typ : lngen.
#[export] Hint Rewrite size_dbind_close_dbind_wrt_typ using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_typ :
forall e1 X1,
  size_exp (close_exp_wrt_typ X1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_typ : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_exp :
forall e1 x1,
  size_exp (close_exp_wrt_exp x1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_mutual :
(forall A1 A2 n1,
  size_typ A1 <= size_typ (open_typ_wrt_typ_rec n1 A2 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec :
forall A1 A2 n1,
  size_typ A1 <= size_typ (open_typ_wrt_typ_rec n1 A2 A1).
Proof.
pose proof size_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_bid_open_bid_wrt_bid_rec_mutual :
(forall D1 D2 n1,
  size_bid D1 <= size_bid (open_bid_wrt_bid_rec n1 D2 D1)).
Proof.
apply_mutual_ind bid_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_bid_open_bid_wrt_bid_rec :
forall D1 D2 n1,
  size_bid D1 <= size_bid (open_bid_wrt_bid_rec n1 D2 D1).
Proof.
pose proof size_bid_open_bid_wrt_bid_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_bid_open_bid_wrt_bid_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_utyp_open_utyp_wrt_utyp_rec_mutual :
(forall F1 F2 n1,
  size_utyp F1 <= size_utyp (open_utyp_wrt_utyp_rec n1 F2 F1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_utyp_open_utyp_wrt_utyp_rec :
forall F1 F2 n1,
  size_utyp F1 <= size_utyp (open_utyp_wrt_utyp_rec n1 F2 F1).
Proof.
pose proof size_utyp_open_utyp_wrt_utyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_utyp_open_utyp_wrt_utyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_ctyp_open_ctyp_wrt_ctyp_rec_mutual :
(forall K1 K2 n1,
  size_ctyp K1 <= size_ctyp (open_ctyp_wrt_ctyp_rec n1 K2 K1)).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_ctyp_open_ctyp_wrt_ctyp_rec :
forall K1 K2 n1,
  size_ctyp K1 <= size_ctyp (open_ctyp_wrt_ctyp_rec n1 K2 K1).
Proof.
pose proof size_ctyp_open_ctyp_wrt_ctyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ctyp_open_ctyp_wrt_ctyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_skel_open_skel_wrt_skel_rec_mutual :
(forall R1 R2 n1,
  size_skel R1 <= size_skel (open_skel_wrt_skel_rec n1 R2 R1)).
Proof.
apply_mutual_ind skel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_skel_open_skel_wrt_skel_rec :
forall R1 R2 n1,
  size_skel R1 <= size_skel (open_skel_wrt_skel_rec n1 R2 R1).
Proof.
pose proof size_skel_open_skel_wrt_skel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_skel_open_skel_wrt_skel_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dbind_open_dbind_wrt_typ_rec_mutual :
(forall db1 A1 n1,
  size_dbind db1 <= size_dbind (open_dbind_wrt_typ_rec n1 A1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dbind_open_dbind_wrt_typ_rec :
forall db1 A1 n1,
  size_dbind db1 <= size_dbind (open_dbind_wrt_typ_rec n1 A1 db1).
Proof.
pose proof size_dbind_open_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dbind_open_dbind_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_typ_rec n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec :
forall e1 A1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_typ_rec n1 A1 e1).
Proof.
pose proof size_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_typ_rec : lngen.

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

Lemma size_typ_open_typ_wrt_typ :
forall A1 A2,
  size_typ A1 <= size_typ (open_typ_wrt_typ A1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_typ_open_typ_wrt_typ : lngen.

Lemma size_bid_open_bid_wrt_bid :
forall D1 D2,
  size_bid D1 <= size_bid (open_bid_wrt_bid D1 D2).
Proof.
unfold open_bid_wrt_bid; default_simp.
Qed.

#[export] Hint Resolve size_bid_open_bid_wrt_bid : lngen.

Lemma size_utyp_open_utyp_wrt_utyp :
forall F1 F2,
  size_utyp F1 <= size_utyp (open_utyp_wrt_utyp F1 F2).
Proof.
unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve size_utyp_open_utyp_wrt_utyp : lngen.

Lemma size_ctyp_open_ctyp_wrt_ctyp :
forall K1 K2,
  size_ctyp K1 <= size_ctyp (open_ctyp_wrt_ctyp K1 K2).
Proof.
unfold open_ctyp_wrt_ctyp; default_simp.
Qed.

#[export] Hint Resolve size_ctyp_open_ctyp_wrt_ctyp : lngen.

Lemma size_skel_open_skel_wrt_skel :
forall R1 R2,
  size_skel R1 <= size_skel (open_skel_wrt_skel R1 R2).
Proof.
unfold open_skel_wrt_skel; default_simp.
Qed.

#[export] Hint Resolve size_skel_open_skel_wrt_skel : lngen.

Lemma size_dbind_open_dbind_wrt_typ :
forall db1 A1,
  size_dbind db1 <= size_dbind (open_dbind_wrt_typ db1 A1).
Proof.
unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_dbind_open_dbind_wrt_typ : lngen.

Lemma size_exp_open_exp_wrt_typ :
forall e1 A1,
  size_exp e1 <= size_exp (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_typ : lngen.

Lemma size_exp_open_exp_wrt_exp :
forall e1 e2,
  size_exp e1 <= size_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_exp : lngen.

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_var_mutual :
(forall A1 X1 n1,
  size_typ (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1) = size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_var :
forall A1 X1 n1,
  size_typ (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1) = size_typ A1.
Proof.
pose proof size_typ_open_typ_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_typ_open_typ_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_typ_open_typ_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_bid_open_bid_wrt_bid_rec_var_mutual :
(forall D1 Xd1 n1,
  size_bid (open_bid_wrt_bid_rec n1 (bid_var_f Xd1) D1) = size_bid D1).
Proof.
apply_mutual_ind bid_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_bid_open_bid_wrt_bid_rec_var :
forall D1 Xd1 n1,
  size_bid (open_bid_wrt_bid_rec n1 (bid_var_f Xd1) D1) = size_bid D1.
Proof.
pose proof size_bid_open_bid_wrt_bid_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_bid_open_bid_wrt_bid_rec_var : lngen.
#[export] Hint Rewrite size_bid_open_bid_wrt_bid_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_utyp_open_utyp_wrt_utyp_rec_var_mutual :
(forall F1 Xf1 n1,
  size_utyp (open_utyp_wrt_utyp_rec n1 (utyp_var_f Xf1) F1) = size_utyp F1).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_utyp_open_utyp_wrt_utyp_rec_var :
forall F1 Xf1 n1,
  size_utyp (open_utyp_wrt_utyp_rec n1 (utyp_var_f Xf1) F1) = size_utyp F1.
Proof.
pose proof size_utyp_open_utyp_wrt_utyp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_utyp_open_utyp_wrt_utyp_rec_var : lngen.
#[export] Hint Rewrite size_utyp_open_utyp_wrt_utyp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_ctyp_open_ctyp_wrt_ctyp_rec_var_mutual :
(forall K1 U1 n1,
  size_ctyp (open_ctyp_wrt_ctyp_rec n1 (ctyp_var_f U1) K1) = size_ctyp K1).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_ctyp_open_ctyp_wrt_ctyp_rec_var :
forall K1 U1 n1,
  size_ctyp (open_ctyp_wrt_ctyp_rec n1 (ctyp_var_f U1) K1) = size_ctyp K1.
Proof.
pose proof size_ctyp_open_ctyp_wrt_ctyp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ctyp_open_ctyp_wrt_ctyp_rec_var : lngen.
#[export] Hint Rewrite size_ctyp_open_ctyp_wrt_ctyp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_skel_open_skel_wrt_skel_rec_var_mutual :
(forall R1 Xr1 n1,
  size_skel (open_skel_wrt_skel_rec n1 (skel_var_f Xr1) R1) = size_skel R1).
Proof.
apply_mutual_ind skel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_skel_open_skel_wrt_skel_rec_var :
forall R1 Xr1 n1,
  size_skel (open_skel_wrt_skel_rec n1 (skel_var_f Xr1) R1) = size_skel R1.
Proof.
pose proof size_skel_open_skel_wrt_skel_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_skel_open_skel_wrt_skel_rec_var : lngen.
#[export] Hint Rewrite size_skel_open_skel_wrt_skel_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_dbind_open_dbind_wrt_typ_rec_var_mutual :
(forall db1 X1 n1,
  size_dbind (open_dbind_wrt_typ_rec n1 (typ_var_f X1) db1) = size_dbind db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dbind_open_dbind_wrt_typ_rec_var :
forall db1 X1 n1,
  size_dbind (open_dbind_wrt_typ_rec n1 (typ_var_f X1) db1) = size_dbind db1.
Proof.
pose proof size_dbind_open_dbind_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_dbind_open_dbind_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_dbind_open_dbind_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec_var_mutual :
(forall e1 X1 n1,
  size_exp (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec_var :
forall e1 X1 n1,
  size_exp (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1) = size_exp e1.
Proof.
pose proof size_exp_open_exp_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_typ_rec_var using solve [auto] : lngen.

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

Lemma size_typ_open_typ_wrt_typ_var :
forall A1 X1,
  size_typ (open_typ_wrt_typ A1 (typ_var_f X1)) = size_typ A1.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_typ_open_typ_wrt_typ_var : lngen.
#[export] Hint Rewrite size_typ_open_typ_wrt_typ_var using solve [auto] : lngen.

Lemma size_bid_open_bid_wrt_bid_var :
forall D1 Xd1,
  size_bid (open_bid_wrt_bid D1 (bid_var_f Xd1)) = size_bid D1.
Proof.
unfold open_bid_wrt_bid; default_simp.
Qed.

#[export] Hint Resolve size_bid_open_bid_wrt_bid_var : lngen.
#[export] Hint Rewrite size_bid_open_bid_wrt_bid_var using solve [auto] : lngen.

Lemma size_utyp_open_utyp_wrt_utyp_var :
forall F1 Xf1,
  size_utyp (open_utyp_wrt_utyp F1 (utyp_var_f Xf1)) = size_utyp F1.
Proof.
unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve size_utyp_open_utyp_wrt_utyp_var : lngen.
#[export] Hint Rewrite size_utyp_open_utyp_wrt_utyp_var using solve [auto] : lngen.

Lemma size_ctyp_open_ctyp_wrt_ctyp_var :
forall K1 U1,
  size_ctyp (open_ctyp_wrt_ctyp K1 (ctyp_var_f U1)) = size_ctyp K1.
Proof.
unfold open_ctyp_wrt_ctyp; default_simp.
Qed.

#[export] Hint Resolve size_ctyp_open_ctyp_wrt_ctyp_var : lngen.
#[export] Hint Rewrite size_ctyp_open_ctyp_wrt_ctyp_var using solve [auto] : lngen.

Lemma size_skel_open_skel_wrt_skel_var :
forall R1 Xr1,
  size_skel (open_skel_wrt_skel R1 (skel_var_f Xr1)) = size_skel R1.
Proof.
unfold open_skel_wrt_skel; default_simp.
Qed.

#[export] Hint Resolve size_skel_open_skel_wrt_skel_var : lngen.
#[export] Hint Rewrite size_skel_open_skel_wrt_skel_var using solve [auto] : lngen.

Lemma size_dbind_open_dbind_wrt_typ_var :
forall db1 X1,
  size_dbind (open_dbind_wrt_typ db1 (typ_var_f X1)) = size_dbind db1.
Proof.
unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_dbind_open_dbind_wrt_typ_var : lngen.
#[export] Hint Rewrite size_dbind_open_dbind_wrt_typ_var using solve [auto] : lngen.

Lemma size_exp_open_exp_wrt_typ_var :
forall e1 X1,
  size_exp (open_exp_wrt_typ e1 (typ_var_f X1)) = size_exp e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_typ_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_typ_var using solve [auto] : lngen.

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

Lemma degree_typ_wrt_typ_S_mutual :
(forall n1 A1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) A1).
Proof.
apply_mutual_ind degree_typ_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_typ_wrt_typ_S :
forall n1 A1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) A1.
Proof.
pose proof degree_typ_wrt_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_bid_wrt_bid_S_mutual :
(forall n1 D1,
  degree_bid_wrt_bid n1 D1 ->
  degree_bid_wrt_bid (S n1) D1).
Proof.
apply_mutual_ind degree_bid_wrt_bid_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_bid_wrt_bid_S :
forall n1 D1,
  degree_bid_wrt_bid n1 D1 ->
  degree_bid_wrt_bid (S n1) D1.
Proof.
pose proof degree_bid_wrt_bid_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_bid_wrt_bid_S : lngen.

(* begin hide *)

Lemma degree_utyp_wrt_utyp_S_mutual :
(forall n1 F1,
  degree_utyp_wrt_utyp n1 F1 ->
  degree_utyp_wrt_utyp (S n1) F1).
Proof.
apply_mutual_ind degree_utyp_wrt_utyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_utyp_wrt_utyp_S :
forall n1 F1,
  degree_utyp_wrt_utyp n1 F1 ->
  degree_utyp_wrt_utyp (S n1) F1.
Proof.
pose proof degree_utyp_wrt_utyp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_utyp_wrt_utyp_S : lngen.

(* begin hide *)

Lemma degree_ctyp_wrt_ctyp_S_mutual :
(forall n1 K1,
  degree_ctyp_wrt_ctyp n1 K1 ->
  degree_ctyp_wrt_ctyp (S n1) K1).
Proof.
apply_mutual_ind degree_ctyp_wrt_ctyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_ctyp_wrt_ctyp_S :
forall n1 K1,
  degree_ctyp_wrt_ctyp n1 K1 ->
  degree_ctyp_wrt_ctyp (S n1) K1.
Proof.
pose proof degree_ctyp_wrt_ctyp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ctyp_wrt_ctyp_S : lngen.

(* begin hide *)

Lemma degree_skel_wrt_skel_S_mutual :
(forall n1 R1,
  degree_skel_wrt_skel n1 R1 ->
  degree_skel_wrt_skel (S n1) R1).
Proof.
apply_mutual_ind degree_skel_wrt_skel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_skel_wrt_skel_S :
forall n1 R1,
  degree_skel_wrt_skel n1 R1 ->
  degree_skel_wrt_skel (S n1) R1.
Proof.
pose proof degree_skel_wrt_skel_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_skel_wrt_skel_S : lngen.

(* begin hide *)

Lemma degree_dbind_wrt_typ_S_mutual :
(forall n1 db1,
  degree_dbind_wrt_typ n1 db1 ->
  degree_dbind_wrt_typ (S n1) db1).
Proof.
apply_mutual_ind degree_dbind_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_dbind_wrt_typ_S :
forall n1 db1,
  degree_dbind_wrt_typ n1 db1 ->
  degree_dbind_wrt_typ (S n1) db1.
Proof.
pose proof degree_dbind_wrt_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dbind_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_exp_wrt_typ_S_mutual :
(forall n1 e1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) e1).
Proof.
apply_mutual_ind degree_exp_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_exp_wrt_typ_S :
forall n1 e1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) e1.
Proof.
pose proof degree_exp_wrt_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_S : lngen.

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

Lemma degree_typ_wrt_typ_O :
forall n1 A1,
  degree_typ_wrt_typ O A1 ->
  degree_typ_wrt_typ n1 A1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_O : lngen.

Lemma degree_bid_wrt_bid_O :
forall n1 D1,
  degree_bid_wrt_bid O D1 ->
  degree_bid_wrt_bid n1 D1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_bid_wrt_bid_O : lngen.

Lemma degree_utyp_wrt_utyp_O :
forall n1 F1,
  degree_utyp_wrt_utyp O F1 ->
  degree_utyp_wrt_utyp n1 F1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_utyp_wrt_utyp_O : lngen.

Lemma degree_ctyp_wrt_ctyp_O :
forall n1 K1,
  degree_ctyp_wrt_ctyp O K1 ->
  degree_ctyp_wrt_ctyp n1 K1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_ctyp_wrt_ctyp_O : lngen.

Lemma degree_skel_wrt_skel_O :
forall n1 R1,
  degree_skel_wrt_skel O R1 ->
  degree_skel_wrt_skel n1 R1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_skel_wrt_skel_O : lngen.

Lemma degree_dbind_wrt_typ_O :
forall n1 db1,
  degree_dbind_wrt_typ O db1 ->
  degree_dbind_wrt_typ n1 db1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_dbind_wrt_typ_O : lngen.

Lemma degree_exp_wrt_typ_O :
forall n1 e1,
  degree_exp_wrt_typ O e1 ->
  degree_exp_wrt_typ n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_O : lngen.

Lemma degree_exp_wrt_exp_O :
forall n1 e1,
  degree_exp_wrt_exp O e1 ->
  degree_exp_wrt_exp n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_O : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1).
Proof.
pose proof degree_typ_wrt_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_close_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_bid_wrt_bid_close_bid_wrt_bid_rec_mutual :
(forall D1 Xd1 n1,
  degree_bid_wrt_bid n1 D1 ->
  degree_bid_wrt_bid (S n1) (close_bid_wrt_bid_rec n1 Xd1 D1)).
Proof.
apply_mutual_ind bid_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_bid_wrt_bid_close_bid_wrt_bid_rec :
forall D1 Xd1 n1,
  degree_bid_wrt_bid n1 D1 ->
  degree_bid_wrt_bid (S n1) (close_bid_wrt_bid_rec n1 Xd1 D1).
Proof.
pose proof degree_bid_wrt_bid_close_bid_wrt_bid_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_bid_wrt_bid_close_bid_wrt_bid_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_utyp_wrt_utyp_close_utyp_wrt_utyp_rec_mutual :
(forall F1 Xf1 n1,
  degree_utyp_wrt_utyp n1 F1 ->
  degree_utyp_wrt_utyp (S n1) (close_utyp_wrt_utyp_rec n1 Xf1 F1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_utyp_wrt_utyp_close_utyp_wrt_utyp_rec :
forall F1 Xf1 n1,
  degree_utyp_wrt_utyp n1 F1 ->
  degree_utyp_wrt_utyp (S n1) (close_utyp_wrt_utyp_rec n1 Xf1 F1).
Proof.
pose proof degree_utyp_wrt_utyp_close_utyp_wrt_utyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_utyp_wrt_utyp_close_utyp_wrt_utyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_ctyp_wrt_ctyp_close_ctyp_wrt_ctyp_rec_mutual :
(forall K1 U1 n1,
  degree_ctyp_wrt_ctyp n1 K1 ->
  degree_ctyp_wrt_ctyp (S n1) (close_ctyp_wrt_ctyp_rec n1 U1 K1)).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ctyp_wrt_ctyp_close_ctyp_wrt_ctyp_rec :
forall K1 U1 n1,
  degree_ctyp_wrt_ctyp n1 K1 ->
  degree_ctyp_wrt_ctyp (S n1) (close_ctyp_wrt_ctyp_rec n1 U1 K1).
Proof.
pose proof degree_ctyp_wrt_ctyp_close_ctyp_wrt_ctyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ctyp_wrt_ctyp_close_ctyp_wrt_ctyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_skel_wrt_skel_close_skel_wrt_skel_rec_mutual :
(forall R1 Xr1 n1,
  degree_skel_wrt_skel n1 R1 ->
  degree_skel_wrt_skel (S n1) (close_skel_wrt_skel_rec n1 Xr1 R1)).
Proof.
apply_mutual_ind skel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_skel_wrt_skel_close_skel_wrt_skel_rec :
forall R1 Xr1 n1,
  degree_skel_wrt_skel n1 R1 ->
  degree_skel_wrt_skel (S n1) (close_skel_wrt_skel_rec n1 Xr1 R1).
Proof.
pose proof degree_skel_wrt_skel_close_skel_wrt_skel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_skel_wrt_skel_close_skel_wrt_skel_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbind_wrt_typ_close_dbind_wrt_typ_rec_mutual :
(forall db1 X1 n1,
  degree_dbind_wrt_typ n1 db1 ->
  degree_dbind_wrt_typ (S n1) (close_dbind_wrt_typ_rec n1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbind_wrt_typ_close_dbind_wrt_typ_rec :
forall db1 X1 n1,
  degree_dbind_wrt_typ n1 db1 ->
  degree_dbind_wrt_typ (S n1) (close_dbind_wrt_typ_rec n1 X1 db1).
Proof.
pose proof degree_dbind_wrt_typ_close_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dbind_wrt_typ_close_dbind_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1).
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 e1 ->
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec :
forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 e1 ->
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1).
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_typ_rec : lngen.

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

Lemma degree_typ_wrt_typ_close_typ_wrt_typ :
forall A1 X1,
  degree_typ_wrt_typ 0 A1 ->
  degree_typ_wrt_typ 1 (close_typ_wrt_typ X1 A1).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_close_typ_wrt_typ : lngen.

Lemma degree_bid_wrt_bid_close_bid_wrt_bid :
forall D1 Xd1,
  degree_bid_wrt_bid 0 D1 ->
  degree_bid_wrt_bid 1 (close_bid_wrt_bid Xd1 D1).
Proof.
unfold close_bid_wrt_bid; default_simp.
Qed.

#[export] Hint Resolve degree_bid_wrt_bid_close_bid_wrt_bid : lngen.

Lemma degree_utyp_wrt_utyp_close_utyp_wrt_utyp :
forall F1 Xf1,
  degree_utyp_wrt_utyp 0 F1 ->
  degree_utyp_wrt_utyp 1 (close_utyp_wrt_utyp Xf1 F1).
Proof.
unfold close_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve degree_utyp_wrt_utyp_close_utyp_wrt_utyp : lngen.

Lemma degree_ctyp_wrt_ctyp_close_ctyp_wrt_ctyp :
forall K1 U1,
  degree_ctyp_wrt_ctyp 0 K1 ->
  degree_ctyp_wrt_ctyp 1 (close_ctyp_wrt_ctyp U1 K1).
Proof.
unfold close_ctyp_wrt_ctyp; default_simp.
Qed.

#[export] Hint Resolve degree_ctyp_wrt_ctyp_close_ctyp_wrt_ctyp : lngen.

Lemma degree_skel_wrt_skel_close_skel_wrt_skel :
forall R1 Xr1,
  degree_skel_wrt_skel 0 R1 ->
  degree_skel_wrt_skel 1 (close_skel_wrt_skel Xr1 R1).
Proof.
unfold close_skel_wrt_skel; default_simp.
Qed.

#[export] Hint Resolve degree_skel_wrt_skel_close_skel_wrt_skel : lngen.

Lemma degree_dbind_wrt_typ_close_dbind_wrt_typ :
forall db1 X1,
  degree_dbind_wrt_typ 0 db1 ->
  degree_dbind_wrt_typ 1 (close_dbind_wrt_typ X1 db1).
Proof.
unfold close_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_dbind_wrt_typ_close_dbind_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_typ :
forall e1 X1,
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_typ 1 (close_exp_wrt_typ X1 e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_exp : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_typ :
forall e1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (close_exp_wrt_typ X1 e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  degree_exp_wrt_exp 0 e1 ->
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1) ->
  degree_typ_wrt_typ n1 A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv :
forall A1 X1 n1,
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1) ->
  degree_typ_wrt_typ n1 A1.
Proof.
pose proof degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_bid_wrt_bid_close_bid_wrt_bid_rec_inv_mutual :
(forall D1 Xd1 n1,
  degree_bid_wrt_bid (S n1) (close_bid_wrt_bid_rec n1 Xd1 D1) ->
  degree_bid_wrt_bid n1 D1).
Proof.
apply_mutual_ind bid_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_bid_wrt_bid_close_bid_wrt_bid_rec_inv :
forall D1 Xd1 n1,
  degree_bid_wrt_bid (S n1) (close_bid_wrt_bid_rec n1 Xd1 D1) ->
  degree_bid_wrt_bid n1 D1.
Proof.
pose proof degree_bid_wrt_bid_close_bid_wrt_bid_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_bid_wrt_bid_close_bid_wrt_bid_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_utyp_wrt_utyp_close_utyp_wrt_utyp_rec_inv_mutual :
(forall F1 Xf1 n1,
  degree_utyp_wrt_utyp (S n1) (close_utyp_wrt_utyp_rec n1 Xf1 F1) ->
  degree_utyp_wrt_utyp n1 F1).
Proof.
apply_mutual_ind utyp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_utyp_wrt_utyp_close_utyp_wrt_utyp_rec_inv :
forall F1 Xf1 n1,
  degree_utyp_wrt_utyp (S n1) (close_utyp_wrt_utyp_rec n1 Xf1 F1) ->
  degree_utyp_wrt_utyp n1 F1.
Proof.
pose proof degree_utyp_wrt_utyp_close_utyp_wrt_utyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_utyp_wrt_utyp_close_utyp_wrt_utyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_ctyp_wrt_ctyp_close_ctyp_wrt_ctyp_rec_inv_mutual :
(forall K1 U1 n1,
  degree_ctyp_wrt_ctyp (S n1) (close_ctyp_wrt_ctyp_rec n1 U1 K1) ->
  degree_ctyp_wrt_ctyp n1 K1).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ctyp_wrt_ctyp_close_ctyp_wrt_ctyp_rec_inv :
forall K1 U1 n1,
  degree_ctyp_wrt_ctyp (S n1) (close_ctyp_wrt_ctyp_rec n1 U1 K1) ->
  degree_ctyp_wrt_ctyp n1 K1.
Proof.
pose proof degree_ctyp_wrt_ctyp_close_ctyp_wrt_ctyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_ctyp_wrt_ctyp_close_ctyp_wrt_ctyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_skel_wrt_skel_close_skel_wrt_skel_rec_inv_mutual :
(forall R1 Xr1 n1,
  degree_skel_wrt_skel (S n1) (close_skel_wrt_skel_rec n1 Xr1 R1) ->
  degree_skel_wrt_skel n1 R1).
Proof.
apply_mutual_ind skel_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_skel_wrt_skel_close_skel_wrt_skel_rec_inv :
forall R1 Xr1 n1,
  degree_skel_wrt_skel (S n1) (close_skel_wrt_skel_rec n1 Xr1 R1) ->
  degree_skel_wrt_skel n1 R1.
Proof.
pose proof degree_skel_wrt_skel_close_skel_wrt_skel_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_skel_wrt_skel_close_skel_wrt_skel_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbind_wrt_typ_close_dbind_wrt_typ_rec_inv_mutual :
(forall db1 X1 n1,
  degree_dbind_wrt_typ (S n1) (close_dbind_wrt_typ_rec n1 X1 db1) ->
  degree_dbind_wrt_typ n1 db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbind_wrt_typ_close_dbind_wrt_typ_rec_inv :
forall db1 X1 n1,
  degree_dbind_wrt_typ (S n1) (close_dbind_wrt_typ_rec n1 X1 db1) ->
  degree_dbind_wrt_typ n1 db1.
Proof.
pose proof degree_dbind_wrt_typ_close_dbind_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dbind_wrt_typ_close_dbind_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_typ n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv :
forall e1 X1 n1,
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_typ n2 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_typ n2 e1.
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv_mutual :
(forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_exp n2 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv :
forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_exp n2 e1.
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv : lngen.

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

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_inv :
forall A1 X1,
  degree_typ_wrt_typ 1 (close_typ_wrt_typ X1 A1) ->
  degree_typ_wrt_typ 0 A1.
Proof.
unfold close_typ_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_typ_wrt_typ_close_typ_wrt_typ_inv : lngen.

Lemma degree_bid_wrt_bid_close_bid_wrt_bid_inv :
forall D1 Xd1,
  degree_bid_wrt_bid 1 (close_bid_wrt_bid Xd1 D1) ->
  degree_bid_wrt_bid 0 D1.
Proof.
unfold close_bid_wrt_bid; eauto with lngen.
Qed.

#[export] Hint Immediate degree_bid_wrt_bid_close_bid_wrt_bid_inv : lngen.

Lemma degree_utyp_wrt_utyp_close_utyp_wrt_utyp_inv :
forall F1 Xf1,
  degree_utyp_wrt_utyp 1 (close_utyp_wrt_utyp Xf1 F1) ->
  degree_utyp_wrt_utyp 0 F1.
Proof.
unfold close_utyp_wrt_utyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_utyp_wrt_utyp_close_utyp_wrt_utyp_inv : lngen.

Lemma degree_ctyp_wrt_ctyp_close_ctyp_wrt_ctyp_inv :
forall K1 U1,
  degree_ctyp_wrt_ctyp 1 (close_ctyp_wrt_ctyp U1 K1) ->
  degree_ctyp_wrt_ctyp 0 K1.
Proof.
unfold close_ctyp_wrt_ctyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_ctyp_wrt_ctyp_close_ctyp_wrt_ctyp_inv : lngen.

Lemma degree_skel_wrt_skel_close_skel_wrt_skel_inv :
forall R1 Xr1,
  degree_skel_wrt_skel 1 (close_skel_wrt_skel Xr1 R1) ->
  degree_skel_wrt_skel 0 R1.
Proof.
unfold close_skel_wrt_skel; eauto with lngen.
Qed.

#[export] Hint Immediate degree_skel_wrt_skel_close_skel_wrt_skel_inv : lngen.

Lemma degree_dbind_wrt_typ_close_dbind_wrt_typ_inv :
forall db1 X1,
  degree_dbind_wrt_typ 1 (close_dbind_wrt_typ X1 db1) ->
  degree_dbind_wrt_typ 0 db1.
Proof.
unfold close_dbind_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dbind_wrt_typ_close_dbind_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_inv :
forall e1 X1,
  degree_exp_wrt_typ 1 (close_exp_wrt_typ X1 e1) ->
  degree_exp_wrt_typ 0 e1.
Proof.
unfold close_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_inv :
forall e1 x1 n1,
  degree_exp_wrt_typ n1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_inv :
forall e1 X1 n1,
  degree_exp_wrt_exp n1 (close_exp_wrt_typ X1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
unfold close_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_inv :
forall e1 x1,
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_exp 0 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_inv : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_mutual :
(forall A1 A2 n1,
  degree_typ_wrt_typ (S n1) A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec :
forall A1 A2 n1,
  degree_typ_wrt_typ (S n1) A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1).
Proof.
pose proof degree_typ_wrt_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_bid_wrt_bid_open_bid_wrt_bid_rec_mutual :
(forall D1 D2 n1,
  degree_bid_wrt_bid (S n1) D1 ->
  degree_bid_wrt_bid n1 D2 ->
  degree_bid_wrt_bid n1 (open_bid_wrt_bid_rec n1 D2 D1)).
Proof.
apply_mutual_ind bid_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_bid_wrt_bid_open_bid_wrt_bid_rec :
forall D1 D2 n1,
  degree_bid_wrt_bid (S n1) D1 ->
  degree_bid_wrt_bid n1 D2 ->
  degree_bid_wrt_bid n1 (open_bid_wrt_bid_rec n1 D2 D1).
Proof.
pose proof degree_bid_wrt_bid_open_bid_wrt_bid_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_bid_wrt_bid_open_bid_wrt_bid_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_utyp_wrt_utyp_open_utyp_wrt_utyp_rec_mutual :
(forall F1 F2 n1,
  degree_utyp_wrt_utyp (S n1) F1 ->
  degree_utyp_wrt_utyp n1 F2 ->
  degree_utyp_wrt_utyp n1 (open_utyp_wrt_utyp_rec n1 F2 F1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_utyp_wrt_utyp_open_utyp_wrt_utyp_rec :
forall F1 F2 n1,
  degree_utyp_wrt_utyp (S n1) F1 ->
  degree_utyp_wrt_utyp n1 F2 ->
  degree_utyp_wrt_utyp n1 (open_utyp_wrt_utyp_rec n1 F2 F1).
Proof.
pose proof degree_utyp_wrt_utyp_open_utyp_wrt_utyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_utyp_wrt_utyp_open_utyp_wrt_utyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_ctyp_wrt_ctyp_open_ctyp_wrt_ctyp_rec_mutual :
(forall K1 K2 n1,
  degree_ctyp_wrt_ctyp (S n1) K1 ->
  degree_ctyp_wrt_ctyp n1 K2 ->
  degree_ctyp_wrt_ctyp n1 (open_ctyp_wrt_ctyp_rec n1 K2 K1)).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ctyp_wrt_ctyp_open_ctyp_wrt_ctyp_rec :
forall K1 K2 n1,
  degree_ctyp_wrt_ctyp (S n1) K1 ->
  degree_ctyp_wrt_ctyp n1 K2 ->
  degree_ctyp_wrt_ctyp n1 (open_ctyp_wrt_ctyp_rec n1 K2 K1).
Proof.
pose proof degree_ctyp_wrt_ctyp_open_ctyp_wrt_ctyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ctyp_wrt_ctyp_open_ctyp_wrt_ctyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_skel_wrt_skel_open_skel_wrt_skel_rec_mutual :
(forall R1 R2 n1,
  degree_skel_wrt_skel (S n1) R1 ->
  degree_skel_wrt_skel n1 R2 ->
  degree_skel_wrt_skel n1 (open_skel_wrt_skel_rec n1 R2 R1)).
Proof.
apply_mutual_ind skel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_skel_wrt_skel_open_skel_wrt_skel_rec :
forall R1 R2 n1,
  degree_skel_wrt_skel (S n1) R1 ->
  degree_skel_wrt_skel n1 R2 ->
  degree_skel_wrt_skel n1 (open_skel_wrt_skel_rec n1 R2 R1).
Proof.
pose proof degree_skel_wrt_skel_open_skel_wrt_skel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_skel_wrt_skel_open_skel_wrt_skel_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbind_wrt_typ_open_dbind_wrt_typ_rec_mutual :
(forall db1 A1 n1,
  degree_dbind_wrt_typ (S n1) db1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_dbind_wrt_typ n1 (open_dbind_wrt_typ_rec n1 A1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbind_wrt_typ_open_dbind_wrt_typ_rec :
forall db1 A1 n1,
  degree_dbind_wrt_typ (S n1) db1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_dbind_wrt_typ n1 (open_dbind_wrt_typ_rec n1 A1 db1).
Proof.
pose proof degree_dbind_wrt_typ_open_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dbind_wrt_typ_open_dbind_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 n1,
  degree_exp_wrt_typ (S n1) e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec :
forall e1 A1 n1,
  degree_exp_wrt_typ (S n1) e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1).
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec :
forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1).
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec :
forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1).
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_typ_rec : lngen.

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

Lemma degree_typ_wrt_typ_open_typ_wrt_typ :
forall A1 A2,
  degree_typ_wrt_typ 1 A1 ->
  degree_typ_wrt_typ 0 A2 ->
  degree_typ_wrt_typ 0 (open_typ_wrt_typ A1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_open_typ_wrt_typ : lngen.

Lemma degree_bid_wrt_bid_open_bid_wrt_bid :
forall D1 D2,
  degree_bid_wrt_bid 1 D1 ->
  degree_bid_wrt_bid 0 D2 ->
  degree_bid_wrt_bid 0 (open_bid_wrt_bid D1 D2).
Proof.
unfold open_bid_wrt_bid; default_simp.
Qed.

#[export] Hint Resolve degree_bid_wrt_bid_open_bid_wrt_bid : lngen.

Lemma degree_utyp_wrt_utyp_open_utyp_wrt_utyp :
forall F1 F2,
  degree_utyp_wrt_utyp 1 F1 ->
  degree_utyp_wrt_utyp 0 F2 ->
  degree_utyp_wrt_utyp 0 (open_utyp_wrt_utyp F1 F2).
Proof.
unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve degree_utyp_wrt_utyp_open_utyp_wrt_utyp : lngen.

Lemma degree_ctyp_wrt_ctyp_open_ctyp_wrt_ctyp :
forall K1 K2,
  degree_ctyp_wrt_ctyp 1 K1 ->
  degree_ctyp_wrt_ctyp 0 K2 ->
  degree_ctyp_wrt_ctyp 0 (open_ctyp_wrt_ctyp K1 K2).
Proof.
unfold open_ctyp_wrt_ctyp; default_simp.
Qed.

#[export] Hint Resolve degree_ctyp_wrt_ctyp_open_ctyp_wrt_ctyp : lngen.

Lemma degree_skel_wrt_skel_open_skel_wrt_skel :
forall R1 R2,
  degree_skel_wrt_skel 1 R1 ->
  degree_skel_wrt_skel 0 R2 ->
  degree_skel_wrt_skel 0 (open_skel_wrt_skel R1 R2).
Proof.
unfold open_skel_wrt_skel; default_simp.
Qed.

#[export] Hint Resolve degree_skel_wrt_skel_open_skel_wrt_skel : lngen.

Lemma degree_dbind_wrt_typ_open_dbind_wrt_typ :
forall db1 A1,
  degree_dbind_wrt_typ 1 db1 ->
  degree_typ_wrt_typ 0 A1 ->
  degree_dbind_wrt_typ 0 (open_dbind_wrt_typ db1 A1).
Proof.
unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_dbind_wrt_typ_open_dbind_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_typ :
forall e1 A1,
  degree_exp_wrt_typ 1 e1 ->
  degree_typ_wrt_typ 0 A1 ->
  degree_exp_wrt_typ 0 (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_exp :
forall e1 e2 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_exp : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_typ :
forall e1 A1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_typ : lngen.

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

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv_mutual :
(forall A1 A2 n1,
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1) ->
  degree_typ_wrt_typ (S n1) A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv :
forall A1 A2 n1,
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1) ->
  degree_typ_wrt_typ (S n1) A1.
Proof.
pose proof degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_bid_wrt_bid_open_bid_wrt_bid_rec_inv_mutual :
(forall D1 D2 n1,
  degree_bid_wrt_bid n1 (open_bid_wrt_bid_rec n1 D2 D1) ->
  degree_bid_wrt_bid (S n1) D1).
Proof.
apply_mutual_ind bid_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_bid_wrt_bid_open_bid_wrt_bid_rec_inv :
forall D1 D2 n1,
  degree_bid_wrt_bid n1 (open_bid_wrt_bid_rec n1 D2 D1) ->
  degree_bid_wrt_bid (S n1) D1.
Proof.
pose proof degree_bid_wrt_bid_open_bid_wrt_bid_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_bid_wrt_bid_open_bid_wrt_bid_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_utyp_wrt_utyp_open_utyp_wrt_utyp_rec_inv_mutual :
(forall F1 F2 n1,
  degree_utyp_wrt_utyp n1 (open_utyp_wrt_utyp_rec n1 F2 F1) ->
  degree_utyp_wrt_utyp (S n1) F1).
Proof.
apply_mutual_ind utyp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_utyp_wrt_utyp_open_utyp_wrt_utyp_rec_inv :
forall F1 F2 n1,
  degree_utyp_wrt_utyp n1 (open_utyp_wrt_utyp_rec n1 F2 F1) ->
  degree_utyp_wrt_utyp (S n1) F1.
Proof.
pose proof degree_utyp_wrt_utyp_open_utyp_wrt_utyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_utyp_wrt_utyp_open_utyp_wrt_utyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_ctyp_wrt_ctyp_open_ctyp_wrt_ctyp_rec_inv_mutual :
(forall K1 K2 n1,
  degree_ctyp_wrt_ctyp n1 (open_ctyp_wrt_ctyp_rec n1 K2 K1) ->
  degree_ctyp_wrt_ctyp (S n1) K1).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ctyp_wrt_ctyp_open_ctyp_wrt_ctyp_rec_inv :
forall K1 K2 n1,
  degree_ctyp_wrt_ctyp n1 (open_ctyp_wrt_ctyp_rec n1 K2 K1) ->
  degree_ctyp_wrt_ctyp (S n1) K1.
Proof.
pose proof degree_ctyp_wrt_ctyp_open_ctyp_wrt_ctyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_ctyp_wrt_ctyp_open_ctyp_wrt_ctyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_skel_wrt_skel_open_skel_wrt_skel_rec_inv_mutual :
(forall R1 R2 n1,
  degree_skel_wrt_skel n1 (open_skel_wrt_skel_rec n1 R2 R1) ->
  degree_skel_wrt_skel (S n1) R1).
Proof.
apply_mutual_ind skel_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_skel_wrt_skel_open_skel_wrt_skel_rec_inv :
forall R1 R2 n1,
  degree_skel_wrt_skel n1 (open_skel_wrt_skel_rec n1 R2 R1) ->
  degree_skel_wrt_skel (S n1) R1.
Proof.
pose proof degree_skel_wrt_skel_open_skel_wrt_skel_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_skel_wrt_skel_open_skel_wrt_skel_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_dbind_wrt_typ_open_dbind_wrt_typ_rec_inv_mutual :
(forall db1 A1 n1,
  degree_dbind_wrt_typ n1 (open_dbind_wrt_typ_rec n1 A1 db1) ->
  degree_dbind_wrt_typ (S n1) db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dbind_wrt_typ_open_dbind_wrt_typ_rec_inv :
forall db1 A1 n1,
  degree_dbind_wrt_typ n1 (open_dbind_wrt_typ_rec n1 A1 db1) ->
  degree_dbind_wrt_typ (S n1) db1.
Proof.
pose proof degree_dbind_wrt_typ_open_dbind_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_dbind_wrt_typ_open_dbind_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv_mutual :
(forall e1 A1 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1) ->
  degree_exp_wrt_typ (S n1) e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv :
forall e1 A1 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1) ->
  degree_exp_wrt_typ (S n1) e1.
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_typ n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv_mutual :
(forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv :
forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv : lngen.

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

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_inv :
forall A1 A2,
  degree_typ_wrt_typ 0 (open_typ_wrt_typ A1 A2) ->
  degree_typ_wrt_typ 1 A1.
Proof.
unfold open_typ_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_typ_wrt_typ_open_typ_wrt_typ_inv : lngen.

Lemma degree_bid_wrt_bid_open_bid_wrt_bid_inv :
forall D1 D2,
  degree_bid_wrt_bid 0 (open_bid_wrt_bid D1 D2) ->
  degree_bid_wrt_bid 1 D1.
Proof.
unfold open_bid_wrt_bid; eauto with lngen.
Qed.

#[export] Hint Immediate degree_bid_wrt_bid_open_bid_wrt_bid_inv : lngen.

Lemma degree_utyp_wrt_utyp_open_utyp_wrt_utyp_inv :
forall F1 F2,
  degree_utyp_wrt_utyp 0 (open_utyp_wrt_utyp F1 F2) ->
  degree_utyp_wrt_utyp 1 F1.
Proof.
unfold open_utyp_wrt_utyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_utyp_wrt_utyp_open_utyp_wrt_utyp_inv : lngen.

Lemma degree_ctyp_wrt_ctyp_open_ctyp_wrt_ctyp_inv :
forall K1 K2,
  degree_ctyp_wrt_ctyp 0 (open_ctyp_wrt_ctyp K1 K2) ->
  degree_ctyp_wrt_ctyp 1 K1.
Proof.
unfold open_ctyp_wrt_ctyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_ctyp_wrt_ctyp_open_ctyp_wrt_ctyp_inv : lngen.

Lemma degree_skel_wrt_skel_open_skel_wrt_skel_inv :
forall R1 R2,
  degree_skel_wrt_skel 0 (open_skel_wrt_skel R1 R2) ->
  degree_skel_wrt_skel 1 R1.
Proof.
unfold open_skel_wrt_skel; eauto with lngen.
Qed.

#[export] Hint Immediate degree_skel_wrt_skel_open_skel_wrt_skel_inv : lngen.

Lemma degree_dbind_wrt_typ_open_dbind_wrt_typ_inv :
forall db1 A1,
  degree_dbind_wrt_typ 0 (open_dbind_wrt_typ db1 A1) ->
  degree_dbind_wrt_typ 1 db1.
Proof.
unfold open_dbind_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_dbind_wrt_typ_open_dbind_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_inv :
forall e1 A1,
  degree_exp_wrt_typ 0 (open_exp_wrt_typ e1 A1) ->
  degree_exp_wrt_typ 1 e1.
Proof.
unfold open_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_inv :
forall e1 e2 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_typ n1 e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_inv :
forall e1 A1 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_typ e1 A1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
unfold open_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_typ_inv : lngen.

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

Lemma close_typ_wrt_typ_rec_inj_mutual :
(forall A1 A2 X1 n1,
  close_typ_wrt_typ_rec n1 X1 A1 = close_typ_wrt_typ_rec n1 X1 A2 ->
  A1 = A2).
Proof.
apply_mutual_ind typ_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_inj :
forall A1 A2 X1 n1,
  close_typ_wrt_typ_rec n1 X1 A1 = close_typ_wrt_typ_rec n1 X1 A2 ->
  A1 = A2.
Proof.
pose proof close_typ_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_typ_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_bid_wrt_bid_rec_inj_mutual :
(forall D1 D2 Xd1 n1,
  close_bid_wrt_bid_rec n1 Xd1 D1 = close_bid_wrt_bid_rec n1 Xd1 D2 ->
  D1 = D2).
Proof.
apply_mutual_ind bid_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_bid_wrt_bid_rec_inj :
forall D1 D2 Xd1 n1,
  close_bid_wrt_bid_rec n1 Xd1 D1 = close_bid_wrt_bid_rec n1 Xd1 D2 ->
  D1 = D2.
Proof.
pose proof close_bid_wrt_bid_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_bid_wrt_bid_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_utyp_wrt_utyp_rec_inj_mutual :
(forall F1 F2 Xf1 n1,
  close_utyp_wrt_utyp_rec n1 Xf1 F1 = close_utyp_wrt_utyp_rec n1 Xf1 F2 ->
  F1 = F2).
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
forall F1 F2 Xf1 n1,
  close_utyp_wrt_utyp_rec n1 Xf1 F1 = close_utyp_wrt_utyp_rec n1 Xf1 F2 ->
  F1 = F2.
Proof.
pose proof close_utyp_wrt_utyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_utyp_wrt_utyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_ctyp_wrt_ctyp_rec_inj_mutual :
(forall K1 K2 U1 n1,
  close_ctyp_wrt_ctyp_rec n1 U1 K1 = close_ctyp_wrt_ctyp_rec n1 U1 K2 ->
  K1 = K2).
Proof.
apply_mutual_ind ctyp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_ctyp_wrt_ctyp_rec_inj :
forall K1 K2 U1 n1,
  close_ctyp_wrt_ctyp_rec n1 U1 K1 = close_ctyp_wrt_ctyp_rec n1 U1 K2 ->
  K1 = K2.
Proof.
pose proof close_ctyp_wrt_ctyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_ctyp_wrt_ctyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_skel_wrt_skel_rec_inj_mutual :
(forall R1 R2 Xr1 n1,
  close_skel_wrt_skel_rec n1 Xr1 R1 = close_skel_wrt_skel_rec n1 Xr1 R2 ->
  R1 = R2).
Proof.
apply_mutual_ind skel_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_skel_wrt_skel_rec_inj :
forall R1 R2 Xr1 n1,
  close_skel_wrt_skel_rec n1 Xr1 R1 = close_skel_wrt_skel_rec n1 Xr1 R2 ->
  R1 = R2.
Proof.
pose proof close_skel_wrt_skel_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_skel_wrt_skel_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dbind_wrt_typ_rec_inj_mutual :
(forall db1 db2 X1 n1,
  close_dbind_wrt_typ_rec n1 X1 db1 = close_dbind_wrt_typ_rec n1 X1 db2 ->
  db1 = db2).
Proof.
apply_mutual_ind dbind_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dbind_wrt_typ_rec_inj :
forall db1 db2 X1 n1,
  close_dbind_wrt_typ_rec n1 X1 db1 = close_dbind_wrt_typ_rec n1 X1 db2 ->
  db1 = db2.
Proof.
pose proof close_dbind_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_dbind_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_inj_mutual :
(forall e1 e2 X1 n1,
  close_exp_wrt_typ_rec n1 X1 e1 = close_exp_wrt_typ_rec n1 X1 e2 ->
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

Lemma close_exp_wrt_typ_rec_inj :
forall e1 e2 X1 n1,
  close_exp_wrt_typ_rec n1 X1 e1 = close_exp_wrt_typ_rec n1 X1 e2 ->
  e1 = e2.
Proof.
pose proof close_exp_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_exp_wrt_typ_rec_inj : lngen.

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

Lemma close_typ_wrt_typ_inj :
forall A1 A2 X1,
  close_typ_wrt_typ X1 A1 = close_typ_wrt_typ X1 A2 ->
  A1 = A2.
Proof.
unfold close_typ_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_typ_wrt_typ_inj : lngen.

Lemma close_bid_wrt_bid_inj :
forall D1 D2 Xd1,
  close_bid_wrt_bid Xd1 D1 = close_bid_wrt_bid Xd1 D2 ->
  D1 = D2.
Proof.
unfold close_bid_wrt_bid; eauto with lngen.
Qed.

#[export] Hint Immediate close_bid_wrt_bid_inj : lngen.

Lemma close_utyp_wrt_utyp_inj :
forall F1 F2 Xf1,
  close_utyp_wrt_utyp Xf1 F1 = close_utyp_wrt_utyp Xf1 F2 ->
  F1 = F2.
Proof.
unfold close_utyp_wrt_utyp; eauto with lngen.
Qed.

#[export] Hint Immediate close_utyp_wrt_utyp_inj : lngen.

Lemma close_ctyp_wrt_ctyp_inj :
forall K1 K2 U1,
  close_ctyp_wrt_ctyp U1 K1 = close_ctyp_wrt_ctyp U1 K2 ->
  K1 = K2.
Proof.
unfold close_ctyp_wrt_ctyp; eauto with lngen.
Qed.

#[export] Hint Immediate close_ctyp_wrt_ctyp_inj : lngen.

Lemma close_skel_wrt_skel_inj :
forall R1 R2 Xr1,
  close_skel_wrt_skel Xr1 R1 = close_skel_wrt_skel Xr1 R2 ->
  R1 = R2.
Proof.
unfold close_skel_wrt_skel; eauto with lngen.
Qed.

#[export] Hint Immediate close_skel_wrt_skel_inj : lngen.

Lemma close_dbind_wrt_typ_inj :
forall db1 db2 X1,
  close_dbind_wrt_typ X1 db1 = close_dbind_wrt_typ X1 db2 ->
  db1 = db2.
Proof.
unfold close_dbind_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_dbind_wrt_typ_inj : lngen.

Lemma close_exp_wrt_typ_inj :
forall e1 e2 X1,
  close_exp_wrt_typ X1 e1 = close_exp_wrt_typ X1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_exp_wrt_typ_inj : lngen.

Lemma close_exp_wrt_exp_inj :
forall e1 e2 x1,
  close_exp_wrt_exp x1 e1 = close_exp_wrt_exp x1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate close_exp_wrt_exp_inj : lngen.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  X1 `notin` ftvar_in_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1) = A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_open_typ_wrt_typ_rec :
forall A1 X1 n1,
  X1 `notin` ftvar_in_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1) = A1.
Proof.
pose proof close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_typ_wrt_typ_rec_open_typ_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_typ_wrt_typ_rec_open_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_bid_wrt_bid_rec_open_bid_wrt_bid_rec_mutual :
(forall D1 Xd1 n1,
  Xd1 `notin` ftvar_in_bid D1 ->
  close_bid_wrt_bid_rec n1 Xd1 (open_bid_wrt_bid_rec n1 (bid_var_f Xd1) D1) = D1).
Proof.
apply_mutual_ind bid_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_bid_wrt_bid_rec_open_bid_wrt_bid_rec :
forall D1 Xd1 n1,
  Xd1 `notin` ftvar_in_bid D1 ->
  close_bid_wrt_bid_rec n1 Xd1 (open_bid_wrt_bid_rec n1 (bid_var_f Xd1) D1) = D1.
Proof.
pose proof close_bid_wrt_bid_rec_open_bid_wrt_bid_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_bid_wrt_bid_rec_open_bid_wrt_bid_rec : lngen.
#[export] Hint Rewrite close_bid_wrt_bid_rec_open_bid_wrt_bid_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_utyp_wrt_utyp_rec_open_utyp_wrt_utyp_rec_mutual :
(forall F1 Xf1 n1,
  Xf1 `notin` ftvar_in_utyp F1 ->
  close_utyp_wrt_utyp_rec n1 Xf1 (open_utyp_wrt_utyp_rec n1 (utyp_var_f Xf1) F1) = F1).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_utyp_wrt_utyp_rec_open_utyp_wrt_utyp_rec :
forall F1 Xf1 n1,
  Xf1 `notin` ftvar_in_utyp F1 ->
  close_utyp_wrt_utyp_rec n1 Xf1 (open_utyp_wrt_utyp_rec n1 (utyp_var_f Xf1) F1) = F1.
Proof.
pose proof close_utyp_wrt_utyp_rec_open_utyp_wrt_utyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_utyp_wrt_utyp_rec_open_utyp_wrt_utyp_rec : lngen.
#[export] Hint Rewrite close_utyp_wrt_utyp_rec_open_utyp_wrt_utyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_ctyp_wrt_ctyp_rec_open_ctyp_wrt_ctyp_rec_mutual :
(forall K1 U1 n1,
  U1 `notin` ftvar_in_ctyp K1 ->
  close_ctyp_wrt_ctyp_rec n1 U1 (open_ctyp_wrt_ctyp_rec n1 (ctyp_var_f U1) K1) = K1).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_ctyp_wrt_ctyp_rec_open_ctyp_wrt_ctyp_rec :
forall K1 U1 n1,
  U1 `notin` ftvar_in_ctyp K1 ->
  close_ctyp_wrt_ctyp_rec n1 U1 (open_ctyp_wrt_ctyp_rec n1 (ctyp_var_f U1) K1) = K1.
Proof.
pose proof close_ctyp_wrt_ctyp_rec_open_ctyp_wrt_ctyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_ctyp_wrt_ctyp_rec_open_ctyp_wrt_ctyp_rec : lngen.
#[export] Hint Rewrite close_ctyp_wrt_ctyp_rec_open_ctyp_wrt_ctyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_skel_wrt_skel_rec_open_skel_wrt_skel_rec_mutual :
(forall R1 Xr1 n1,
  Xr1 `notin` ftvar_in_skel R1 ->
  close_skel_wrt_skel_rec n1 Xr1 (open_skel_wrt_skel_rec n1 (skel_var_f Xr1) R1) = R1).
Proof.
apply_mutual_ind skel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_skel_wrt_skel_rec_open_skel_wrt_skel_rec :
forall R1 Xr1 n1,
  Xr1 `notin` ftvar_in_skel R1 ->
  close_skel_wrt_skel_rec n1 Xr1 (open_skel_wrt_skel_rec n1 (skel_var_f Xr1) R1) = R1.
Proof.
pose proof close_skel_wrt_skel_rec_open_skel_wrt_skel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_skel_wrt_skel_rec_open_skel_wrt_skel_rec : lngen.
#[export] Hint Rewrite close_skel_wrt_skel_rec_open_skel_wrt_skel_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec_mutual :
(forall db1 X1 n1,
  X1 `notin` ftvar_in_dbind db1 ->
  close_dbind_wrt_typ_rec n1 X1 (open_dbind_wrt_typ_rec n1 (typ_var_f X1) db1) = db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec :
forall db1 X1 n1,
  X1 `notin` ftvar_in_dbind db1 ->
  close_dbind_wrt_typ_rec n1 X1 (open_dbind_wrt_typ_rec n1 (typ_var_f X1) db1) = db1.
Proof.
pose proof close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e1 X1 n1,
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1) = e1.
Proof.
pose proof close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_exp_wrt_typ_rec_open_exp_wrt_typ_rec using solve [auto] : lngen.

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

Lemma close_typ_wrt_typ_open_typ_wrt_typ :
forall A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  close_typ_wrt_typ X1 (open_typ_wrt_typ A1 (typ_var_f X1)) = A1.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_typ_wrt_typ_open_typ_wrt_typ : lngen.
#[export] Hint Rewrite close_typ_wrt_typ_open_typ_wrt_typ using solve [auto] : lngen.

Lemma close_bid_wrt_bid_open_bid_wrt_bid :
forall D1 Xd1,
  Xd1 `notin` ftvar_in_bid D1 ->
  close_bid_wrt_bid Xd1 (open_bid_wrt_bid D1 (bid_var_f Xd1)) = D1.
Proof.
unfold close_bid_wrt_bid; unfold open_bid_wrt_bid; default_simp.
Qed.

#[export] Hint Resolve close_bid_wrt_bid_open_bid_wrt_bid : lngen.
#[export] Hint Rewrite close_bid_wrt_bid_open_bid_wrt_bid using solve [auto] : lngen.

Lemma close_utyp_wrt_utyp_open_utyp_wrt_utyp :
forall F1 Xf1,
  Xf1 `notin` ftvar_in_utyp F1 ->
  close_utyp_wrt_utyp Xf1 (open_utyp_wrt_utyp F1 (utyp_var_f Xf1)) = F1.
Proof.
unfold close_utyp_wrt_utyp; unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve close_utyp_wrt_utyp_open_utyp_wrt_utyp : lngen.
#[export] Hint Rewrite close_utyp_wrt_utyp_open_utyp_wrt_utyp using solve [auto] : lngen.

Lemma close_ctyp_wrt_ctyp_open_ctyp_wrt_ctyp :
forall K1 U1,
  U1 `notin` ftvar_in_ctyp K1 ->
  close_ctyp_wrt_ctyp U1 (open_ctyp_wrt_ctyp K1 (ctyp_var_f U1)) = K1.
Proof.
unfold close_ctyp_wrt_ctyp; unfold open_ctyp_wrt_ctyp; default_simp.
Qed.

#[export] Hint Resolve close_ctyp_wrt_ctyp_open_ctyp_wrt_ctyp : lngen.
#[export] Hint Rewrite close_ctyp_wrt_ctyp_open_ctyp_wrt_ctyp using solve [auto] : lngen.

Lemma close_skel_wrt_skel_open_skel_wrt_skel :
forall R1 Xr1,
  Xr1 `notin` ftvar_in_skel R1 ->
  close_skel_wrt_skel Xr1 (open_skel_wrt_skel R1 (skel_var_f Xr1)) = R1.
Proof.
unfold close_skel_wrt_skel; unfold open_skel_wrt_skel; default_simp.
Qed.

#[export] Hint Resolve close_skel_wrt_skel_open_skel_wrt_skel : lngen.
#[export] Hint Rewrite close_skel_wrt_skel_open_skel_wrt_skel using solve [auto] : lngen.

Lemma close_dbind_wrt_typ_open_dbind_wrt_typ :
forall db1 X1,
  X1 `notin` ftvar_in_dbind db1 ->
  close_dbind_wrt_typ X1 (open_dbind_wrt_typ db1 (typ_var_f X1)) = db1.
Proof.
unfold close_dbind_wrt_typ; unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_dbind_wrt_typ_open_dbind_wrt_typ : lngen.
#[export] Hint Rewrite close_dbind_wrt_typ_open_dbind_wrt_typ using solve [auto] : lngen.

Lemma close_exp_wrt_typ_open_exp_wrt_typ :
forall e1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_typ X1 (open_exp_wrt_typ e1 (typ_var_f X1)) = e1.
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_exp_wrt_typ_open_exp_wrt_typ : lngen.
#[export] Hint Rewrite close_exp_wrt_typ_open_exp_wrt_typ using solve [auto] : lngen.

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

Lemma open_typ_wrt_typ_rec_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  open_typ_wrt_typ_rec n1 (typ_var_f X1) (close_typ_wrt_typ_rec n1 X1 A1) = A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  open_typ_wrt_typ_rec n1 (typ_var_f X1) (close_typ_wrt_typ_rec n1 X1 A1) = A1.
Proof.
pose proof open_typ_wrt_typ_rec_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_typ_wrt_typ_rec_close_typ_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_bid_wrt_bid_rec_close_bid_wrt_bid_rec_mutual :
(forall D1 Xd1 n1,
  open_bid_wrt_bid_rec n1 (bid_var_f Xd1) (close_bid_wrt_bid_rec n1 Xd1 D1) = D1).
Proof.
apply_mutual_ind bid_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_bid_wrt_bid_rec_close_bid_wrt_bid_rec :
forall D1 Xd1 n1,
  open_bid_wrt_bid_rec n1 (bid_var_f Xd1) (close_bid_wrt_bid_rec n1 Xd1 D1) = D1.
Proof.
pose proof open_bid_wrt_bid_rec_close_bid_wrt_bid_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_bid_wrt_bid_rec_close_bid_wrt_bid_rec : lngen.
#[export] Hint Rewrite open_bid_wrt_bid_rec_close_bid_wrt_bid_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_utyp_wrt_utyp_rec_close_utyp_wrt_utyp_rec_mutual :
(forall F1 Xf1 n1,
  open_utyp_wrt_utyp_rec n1 (utyp_var_f Xf1) (close_utyp_wrt_utyp_rec n1 Xf1 F1) = F1).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_utyp_wrt_utyp_rec_close_utyp_wrt_utyp_rec :
forall F1 Xf1 n1,
  open_utyp_wrt_utyp_rec n1 (utyp_var_f Xf1) (close_utyp_wrt_utyp_rec n1 Xf1 F1) = F1.
Proof.
pose proof open_utyp_wrt_utyp_rec_close_utyp_wrt_utyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_utyp_wrt_utyp_rec_close_utyp_wrt_utyp_rec : lngen.
#[export] Hint Rewrite open_utyp_wrt_utyp_rec_close_utyp_wrt_utyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_ctyp_wrt_ctyp_rec_close_ctyp_wrt_ctyp_rec_mutual :
(forall K1 U1 n1,
  open_ctyp_wrt_ctyp_rec n1 (ctyp_var_f U1) (close_ctyp_wrt_ctyp_rec n1 U1 K1) = K1).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_ctyp_wrt_ctyp_rec_close_ctyp_wrt_ctyp_rec :
forall K1 U1 n1,
  open_ctyp_wrt_ctyp_rec n1 (ctyp_var_f U1) (close_ctyp_wrt_ctyp_rec n1 U1 K1) = K1.
Proof.
pose proof open_ctyp_wrt_ctyp_rec_close_ctyp_wrt_ctyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_ctyp_wrt_ctyp_rec_close_ctyp_wrt_ctyp_rec : lngen.
#[export] Hint Rewrite open_ctyp_wrt_ctyp_rec_close_ctyp_wrt_ctyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_skel_wrt_skel_rec_close_skel_wrt_skel_rec_mutual :
(forall R1 Xr1 n1,
  open_skel_wrt_skel_rec n1 (skel_var_f Xr1) (close_skel_wrt_skel_rec n1 Xr1 R1) = R1).
Proof.
apply_mutual_ind skel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_skel_wrt_skel_rec_close_skel_wrt_skel_rec :
forall R1 Xr1 n1,
  open_skel_wrt_skel_rec n1 (skel_var_f Xr1) (close_skel_wrt_skel_rec n1 Xr1 R1) = R1.
Proof.
pose proof open_skel_wrt_skel_rec_close_skel_wrt_skel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_skel_wrt_skel_rec_close_skel_wrt_skel_rec : lngen.
#[export] Hint Rewrite open_skel_wrt_skel_rec_close_skel_wrt_skel_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dbind_wrt_typ_rec_close_dbind_wrt_typ_rec_mutual :
(forall db1 X1 n1,
  open_dbind_wrt_typ_rec n1 (typ_var_f X1) (close_dbind_wrt_typ_rec n1 X1 db1) = db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dbind_wrt_typ_rec_close_dbind_wrt_typ_rec :
forall db1 X1 n1,
  open_dbind_wrt_typ_rec n1 (typ_var_f X1) (close_dbind_wrt_typ_rec n1 X1 db1) = db1.
Proof.
pose proof open_dbind_wrt_typ_rec_close_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_dbind_wrt_typ_rec_close_dbind_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_dbind_wrt_typ_rec_close_dbind_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  open_exp_wrt_typ_rec n1 (typ_var_f X1) (close_exp_wrt_typ_rec n1 X1 e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  open_exp_wrt_typ_rec n1 (typ_var_f X1) (close_exp_wrt_typ_rec n1 X1 e1) = e1.
Proof.
pose proof open_exp_wrt_typ_rec_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_exp_wrt_typ_rec_close_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_exp_wrt_typ_rec_close_exp_wrt_typ_rec using solve [auto] : lngen.

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

Lemma open_typ_wrt_typ_close_typ_wrt_typ :
forall A1 X1,
  open_typ_wrt_typ (close_typ_wrt_typ X1 A1) (typ_var_f X1) = A1.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_typ_wrt_typ_close_typ_wrt_typ : lngen.
#[export] Hint Rewrite open_typ_wrt_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma open_bid_wrt_bid_close_bid_wrt_bid :
forall D1 Xd1,
  open_bid_wrt_bid (close_bid_wrt_bid Xd1 D1) (bid_var_f Xd1) = D1.
Proof.
unfold close_bid_wrt_bid; unfold open_bid_wrt_bid; default_simp.
Qed.

#[export] Hint Resolve open_bid_wrt_bid_close_bid_wrt_bid : lngen.
#[export] Hint Rewrite open_bid_wrt_bid_close_bid_wrt_bid using solve [auto] : lngen.

Lemma open_utyp_wrt_utyp_close_utyp_wrt_utyp :
forall F1 Xf1,
  open_utyp_wrt_utyp (close_utyp_wrt_utyp Xf1 F1) (utyp_var_f Xf1) = F1.
Proof.
unfold close_utyp_wrt_utyp; unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve open_utyp_wrt_utyp_close_utyp_wrt_utyp : lngen.
#[export] Hint Rewrite open_utyp_wrt_utyp_close_utyp_wrt_utyp using solve [auto] : lngen.

Lemma open_ctyp_wrt_ctyp_close_ctyp_wrt_ctyp :
forall K1 U1,
  open_ctyp_wrt_ctyp (close_ctyp_wrt_ctyp U1 K1) (ctyp_var_f U1) = K1.
Proof.
unfold close_ctyp_wrt_ctyp; unfold open_ctyp_wrt_ctyp; default_simp.
Qed.

#[export] Hint Resolve open_ctyp_wrt_ctyp_close_ctyp_wrt_ctyp : lngen.
#[export] Hint Rewrite open_ctyp_wrt_ctyp_close_ctyp_wrt_ctyp using solve [auto] : lngen.

Lemma open_skel_wrt_skel_close_skel_wrt_skel :
forall R1 Xr1,
  open_skel_wrt_skel (close_skel_wrt_skel Xr1 R1) (skel_var_f Xr1) = R1.
Proof.
unfold close_skel_wrt_skel; unfold open_skel_wrt_skel; default_simp.
Qed.

#[export] Hint Resolve open_skel_wrt_skel_close_skel_wrt_skel : lngen.
#[export] Hint Rewrite open_skel_wrt_skel_close_skel_wrt_skel using solve [auto] : lngen.

Lemma open_dbind_wrt_typ_close_dbind_wrt_typ :
forall db1 X1,
  open_dbind_wrt_typ (close_dbind_wrt_typ X1 db1) (typ_var_f X1) = db1.
Proof.
unfold close_dbind_wrt_typ; unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_dbind_wrt_typ_close_dbind_wrt_typ : lngen.
#[export] Hint Rewrite open_dbind_wrt_typ_close_dbind_wrt_typ using solve [auto] : lngen.

Lemma open_exp_wrt_typ_close_exp_wrt_typ :
forall e1 X1,
  open_exp_wrt_typ (close_exp_wrt_typ X1 e1) (typ_var_f X1) = e1.
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_typ_close_exp_wrt_typ : lngen.
#[export] Hint Rewrite open_exp_wrt_typ_close_exp_wrt_typ using solve [auto] : lngen.

Lemma open_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  open_exp_wrt_exp (close_exp_wrt_exp x1 e1) (exp_var_f x1) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_inj_mutual :
(forall A2 A1 X1 n1,
  X1 `notin` ftvar_in_typ A2 ->
  X1 `notin` ftvar_in_typ A1 ->
  open_typ_wrt_typ_rec n1 (typ_var_f X1) A2 = open_typ_wrt_typ_rec n1 (typ_var_f X1) A1 ->
  A2 = A1).
Proof.
apply_mutual_ind typ_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_inj :
forall A2 A1 X1 n1,
  X1 `notin` ftvar_in_typ A2 ->
  X1 `notin` ftvar_in_typ A1 ->
  open_typ_wrt_typ_rec n1 (typ_var_f X1) A2 = open_typ_wrt_typ_rec n1 (typ_var_f X1) A1 ->
  A2 = A1.
Proof.
pose proof open_typ_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_typ_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_bid_wrt_bid_rec_inj_mutual :
(forall D2 D1 Xd1 n1,
  Xd1 `notin` ftvar_in_bid D2 ->
  Xd1 `notin` ftvar_in_bid D1 ->
  open_bid_wrt_bid_rec n1 (bid_var_f Xd1) D2 = open_bid_wrt_bid_rec n1 (bid_var_f Xd1) D1 ->
  D2 = D1).
Proof.
apply_mutual_ind bid_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_bid_wrt_bid_rec_inj :
forall D2 D1 Xd1 n1,
  Xd1 `notin` ftvar_in_bid D2 ->
  Xd1 `notin` ftvar_in_bid D1 ->
  open_bid_wrt_bid_rec n1 (bid_var_f Xd1) D2 = open_bid_wrt_bid_rec n1 (bid_var_f Xd1) D1 ->
  D2 = D1.
Proof.
pose proof open_bid_wrt_bid_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_bid_wrt_bid_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_utyp_wrt_utyp_rec_inj_mutual :
(forall F2 F1 Xf1 n1,
  Xf1 `notin` ftvar_in_utyp F2 ->
  Xf1 `notin` ftvar_in_utyp F1 ->
  open_utyp_wrt_utyp_rec n1 (utyp_var_f Xf1) F2 = open_utyp_wrt_utyp_rec n1 (utyp_var_f Xf1) F1 ->
  F2 = F1).
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
forall F2 F1 Xf1 n1,
  Xf1 `notin` ftvar_in_utyp F2 ->
  Xf1 `notin` ftvar_in_utyp F1 ->
  open_utyp_wrt_utyp_rec n1 (utyp_var_f Xf1) F2 = open_utyp_wrt_utyp_rec n1 (utyp_var_f Xf1) F1 ->
  F2 = F1.
Proof.
pose proof open_utyp_wrt_utyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_utyp_wrt_utyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_ctyp_wrt_ctyp_rec_inj_mutual :
(forall K2 K1 U1 n1,
  U1 `notin` ftvar_in_ctyp K2 ->
  U1 `notin` ftvar_in_ctyp K1 ->
  open_ctyp_wrt_ctyp_rec n1 (ctyp_var_f U1) K2 = open_ctyp_wrt_ctyp_rec n1 (ctyp_var_f U1) K1 ->
  K2 = K1).
Proof.
apply_mutual_ind ctyp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_ctyp_wrt_ctyp_rec_inj :
forall K2 K1 U1 n1,
  U1 `notin` ftvar_in_ctyp K2 ->
  U1 `notin` ftvar_in_ctyp K1 ->
  open_ctyp_wrt_ctyp_rec n1 (ctyp_var_f U1) K2 = open_ctyp_wrt_ctyp_rec n1 (ctyp_var_f U1) K1 ->
  K2 = K1.
Proof.
pose proof open_ctyp_wrt_ctyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_ctyp_wrt_ctyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_skel_wrt_skel_rec_inj_mutual :
(forall R2 R1 Xr1 n1,
  Xr1 `notin` ftvar_in_skel R2 ->
  Xr1 `notin` ftvar_in_skel R1 ->
  open_skel_wrt_skel_rec n1 (skel_var_f Xr1) R2 = open_skel_wrt_skel_rec n1 (skel_var_f Xr1) R1 ->
  R2 = R1).
Proof.
apply_mutual_ind skel_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_skel_wrt_skel_rec_inj :
forall R2 R1 Xr1 n1,
  Xr1 `notin` ftvar_in_skel R2 ->
  Xr1 `notin` ftvar_in_skel R1 ->
  open_skel_wrt_skel_rec n1 (skel_var_f Xr1) R2 = open_skel_wrt_skel_rec n1 (skel_var_f Xr1) R1 ->
  R2 = R1.
Proof.
pose proof open_skel_wrt_skel_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_skel_wrt_skel_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dbind_wrt_typ_rec_inj_mutual :
(forall db2 db1 X1 n1,
  X1 `notin` ftvar_in_dbind db2 ->
  X1 `notin` ftvar_in_dbind db1 ->
  open_dbind_wrt_typ_rec n1 (typ_var_f X1) db2 = open_dbind_wrt_typ_rec n1 (typ_var_f X1) db1 ->
  db2 = db1).
Proof.
apply_mutual_ind dbind_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dbind_wrt_typ_rec_inj :
forall db2 db1 X1 n1,
  X1 `notin` ftvar_in_dbind db2 ->
  X1 `notin` ftvar_in_dbind db1 ->
  open_dbind_wrt_typ_rec n1 (typ_var_f X1) db2 = open_dbind_wrt_typ_rec n1 (typ_var_f X1) db1 ->
  db2 = db1.
Proof.
pose proof open_dbind_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_dbind_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_inj_mutual :
(forall e2 e1 X1 n1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_typ_rec n1 (typ_var_f X1) e2 = open_exp_wrt_typ_rec n1 (typ_var_f X1) e1 ->
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

Lemma open_exp_wrt_typ_rec_inj :
forall e2 e1 X1 n1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_typ_rec n1 (typ_var_f X1) e2 = open_exp_wrt_typ_rec n1 (typ_var_f X1) e1 ->
  e2 = e1.
Proof.
pose proof open_exp_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_exp_wrt_typ_rec_inj : lngen.

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

Lemma open_typ_wrt_typ_inj :
forall A2 A1 X1,
  X1 `notin` ftvar_in_typ A2 ->
  X1 `notin` ftvar_in_typ A1 ->
  open_typ_wrt_typ A2 (typ_var_f X1) = open_typ_wrt_typ A1 (typ_var_f X1) ->
  A2 = A1.
Proof.
unfold open_typ_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_typ_wrt_typ_inj : lngen.

Lemma open_bid_wrt_bid_inj :
forall D2 D1 Xd1,
  Xd1 `notin` ftvar_in_bid D2 ->
  Xd1 `notin` ftvar_in_bid D1 ->
  open_bid_wrt_bid D2 (bid_var_f Xd1) = open_bid_wrt_bid D1 (bid_var_f Xd1) ->
  D2 = D1.
Proof.
unfold open_bid_wrt_bid; eauto with lngen.
Qed.

#[export] Hint Immediate open_bid_wrt_bid_inj : lngen.

Lemma open_utyp_wrt_utyp_inj :
forall F2 F1 Xf1,
  Xf1 `notin` ftvar_in_utyp F2 ->
  Xf1 `notin` ftvar_in_utyp F1 ->
  open_utyp_wrt_utyp F2 (utyp_var_f Xf1) = open_utyp_wrt_utyp F1 (utyp_var_f Xf1) ->
  F2 = F1.
Proof.
unfold open_utyp_wrt_utyp; eauto with lngen.
Qed.

#[export] Hint Immediate open_utyp_wrt_utyp_inj : lngen.

Lemma open_ctyp_wrt_ctyp_inj :
forall K2 K1 U1,
  U1 `notin` ftvar_in_ctyp K2 ->
  U1 `notin` ftvar_in_ctyp K1 ->
  open_ctyp_wrt_ctyp K2 (ctyp_var_f U1) = open_ctyp_wrt_ctyp K1 (ctyp_var_f U1) ->
  K2 = K1.
Proof.
unfold open_ctyp_wrt_ctyp; eauto with lngen.
Qed.

#[export] Hint Immediate open_ctyp_wrt_ctyp_inj : lngen.

Lemma open_skel_wrt_skel_inj :
forall R2 R1 Xr1,
  Xr1 `notin` ftvar_in_skel R2 ->
  Xr1 `notin` ftvar_in_skel R1 ->
  open_skel_wrt_skel R2 (skel_var_f Xr1) = open_skel_wrt_skel R1 (skel_var_f Xr1) ->
  R2 = R1.
Proof.
unfold open_skel_wrt_skel; eauto with lngen.
Qed.

#[export] Hint Immediate open_skel_wrt_skel_inj : lngen.

Lemma open_dbind_wrt_typ_inj :
forall db2 db1 X1,
  X1 `notin` ftvar_in_dbind db2 ->
  X1 `notin` ftvar_in_dbind db1 ->
  open_dbind_wrt_typ db2 (typ_var_f X1) = open_dbind_wrt_typ db1 (typ_var_f X1) ->
  db2 = db1.
Proof.
unfold open_dbind_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_dbind_wrt_typ_inj : lngen.

Lemma open_exp_wrt_typ_inj :
forall e2 e1 X1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_typ e2 (typ_var_f X1) = open_exp_wrt_typ e1 (typ_var_f X1) ->
  e2 = e1.
Proof.
unfold open_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_exp_wrt_typ_inj : lngen.

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

Lemma degree_typ_wrt_typ_of_lc_typ_mutual :
(forall A1,
  lc_typ A1 ->
  degree_typ_wrt_typ 0 A1).
Proof.
apply_mutual_ind lc_typ_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_typ_wrt_typ_of_lc_typ :
forall A1,
  lc_typ A1 ->
  degree_typ_wrt_typ 0 A1.
Proof.
pose proof degree_typ_wrt_typ_of_lc_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_of_lc_typ : lngen.

(* begin hide *)

Lemma degree_bid_wrt_bid_of_lc_bid_mutual :
(forall D1,
  lc_bid D1 ->
  degree_bid_wrt_bid 0 D1).
Proof.
apply_mutual_ind lc_bid_mutind;
intros;
let Xd1 := fresh "Xd1" in pick_fresh Xd1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_bid_wrt_bid_of_lc_bid :
forall D1,
  lc_bid D1 ->
  degree_bid_wrt_bid 0 D1.
Proof.
pose proof degree_bid_wrt_bid_of_lc_bid_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_bid_wrt_bid_of_lc_bid : lngen.

(* begin hide *)

Lemma degree_utyp_wrt_utyp_of_lc_utyp_mutual :
(forall F1,
  lc_utyp F1 ->
  degree_utyp_wrt_utyp 0 F1).
Proof.
apply_mutual_ind lc_utyp_mutind;
intros;
let Xf1 := fresh "Xf1" in pick_fresh Xf1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_utyp_wrt_utyp_of_lc_utyp :
forall F1,
  lc_utyp F1 ->
  degree_utyp_wrt_utyp 0 F1.
Proof.
pose proof degree_utyp_wrt_utyp_of_lc_utyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_utyp_wrt_utyp_of_lc_utyp : lngen.

(* begin hide *)

Lemma degree_ctyp_wrt_ctyp_of_lc_ctyp_mutual :
(forall K1,
  lc_ctyp K1 ->
  degree_ctyp_wrt_ctyp 0 K1).
Proof.
apply_mutual_ind lc_ctyp_mutind;
intros;
let U1 := fresh "U1" in pick_fresh U1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_ctyp_wrt_ctyp_of_lc_ctyp :
forall K1,
  lc_ctyp K1 ->
  degree_ctyp_wrt_ctyp 0 K1.
Proof.
pose proof degree_ctyp_wrt_ctyp_of_lc_ctyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ctyp_wrt_ctyp_of_lc_ctyp : lngen.

(* begin hide *)

Lemma degree_skel_wrt_skel_of_lc_skel_mutual :
(forall R1,
  lc_skel R1 ->
  degree_skel_wrt_skel 0 R1).
Proof.
apply_mutual_ind lc_skel_mutind;
intros;
let Xr1 := fresh "Xr1" in pick_fresh Xr1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_skel_wrt_skel_of_lc_skel :
forall R1,
  lc_skel R1 ->
  degree_skel_wrt_skel 0 R1.
Proof.
pose proof degree_skel_wrt_skel_of_lc_skel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_skel_wrt_skel_of_lc_skel : lngen.

(* begin hide *)

Lemma degree_dbind_wrt_typ_of_lc_dbind_mutual :
(forall db1,
  lc_dbind db1 ->
  degree_dbind_wrt_typ 0 db1).
Proof.
apply_mutual_ind lc_dbind_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_dbind_wrt_typ_of_lc_dbind :
forall db1,
  lc_dbind db1 ->
  degree_dbind_wrt_typ 0 db1.
Proof.
pose proof degree_dbind_wrt_typ_of_lc_dbind_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_dbind_wrt_typ_of_lc_dbind : lngen.

(* begin hide *)

Lemma degree_exp_wrt_typ_of_lc_exp_mutual :
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_typ 0 e1).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_exp_wrt_typ_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_typ 0 e1.
Proof.
pose proof degree_exp_wrt_typ_of_lc_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_of_lc_exp : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_of_lc_exp_mutual :
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
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

Lemma lc_typ_of_degree_size_mutual :
forall i1,
(forall A1,
  size_typ A1 = i1 ->
  degree_typ_wrt_typ 0 A1 ->
  lc_typ A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind typ_mutind;
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

Lemma lc_typ_of_degree :
forall A1,
  degree_typ_wrt_typ 0 A1 ->
  lc_typ A1.
Proof.
intros A1; intros;
pose proof (lc_typ_of_degree_size_mutual (size_typ A1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_typ_of_degree : lngen.

(* begin hide *)

Lemma lc_bid_of_degree_size_mutual :
forall i1,
(forall D1,
  size_bid D1 = i1 ->
  degree_bid_wrt_bid 0 D1 ->
  lc_bid D1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind bid_mutind;
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

Lemma lc_bid_of_degree :
forall D1,
  degree_bid_wrt_bid 0 D1 ->
  lc_bid D1.
Proof.
intros D1; intros;
pose proof (lc_bid_of_degree_size_mutual (size_bid D1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_bid_of_degree : lngen.

(* begin hide *)

Lemma lc_utyp_of_degree_size_mutual :
forall i1,
(forall F1,
  size_utyp F1 = i1 ->
  degree_utyp_wrt_utyp 0 F1 ->
  lc_utyp F1).
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
forall F1,
  degree_utyp_wrt_utyp 0 F1 ->
  lc_utyp F1.
Proof.
intros F1; intros;
pose proof (lc_utyp_of_degree_size_mutual (size_utyp F1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_utyp_of_degree : lngen.

(* begin hide *)

Lemma lc_ctyp_of_degree_size_mutual :
forall i1,
(forall K1,
  size_ctyp K1 = i1 ->
  degree_ctyp_wrt_ctyp 0 K1 ->
  lc_ctyp K1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind ctyp_mutind;
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

Lemma lc_ctyp_of_degree :
forall K1,
  degree_ctyp_wrt_ctyp 0 K1 ->
  lc_ctyp K1.
Proof.
intros K1; intros;
pose proof (lc_ctyp_of_degree_size_mutual (size_ctyp K1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_ctyp_of_degree : lngen.

(* begin hide *)

Lemma lc_skel_of_degree_size_mutual :
forall i1,
(forall R1,
  size_skel R1 = i1 ->
  degree_skel_wrt_skel 0 R1 ->
  lc_skel R1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind skel_mutind;
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

Lemma lc_skel_of_degree :
forall R1,
  degree_skel_wrt_skel 0 R1 ->
  lc_skel R1.
Proof.
intros R1; intros;
pose proof (lc_skel_of_degree_size_mutual (size_skel R1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_skel_of_degree : lngen.

(* begin hide *)

Lemma lc_dbind_of_degree_size_mutual :
forall i1,
(forall db1,
  size_dbind db1 = i1 ->
  degree_dbind_wrt_typ 0 db1 ->
  lc_dbind db1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind dbind_mutind;
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

Lemma lc_dbind_of_degree :
forall db1,
  degree_dbind_wrt_typ 0 db1 ->
  lc_dbind db1.
Proof.
intros db1; intros;
pose proof (lc_dbind_of_degree_size_mutual (size_dbind db1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_dbind_of_degree : lngen.

(* begin hide *)

Lemma lc_exp_of_degree_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  degree_exp_wrt_typ 0 e1 ->
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
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1.
Proof.
intros e1; intros;
pose proof (lc_exp_of_degree_size_mutual (size_exp e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_exp_of_degree : lngen.

Ltac colour_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac typ_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_typ_wrt_typ_of_lc_typ in J1; clear H
          end).

Ltac bid_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_bid_wrt_bid_of_lc_bid in J1; clear H
          end).

Ltac utyp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_utyp_wrt_utyp_of_lc_utyp in J1; clear H
          end).

Ltac ctyp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_ctyp_wrt_ctyp_of_lc_ctyp in J1; clear H
          end).

Ltac skel_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_skel_wrt_skel_of_lc_skel in J1; clear H
          end).

Ltac dbind_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_dbind_wrt_typ_of_lc_dbind in J1; clear H
          end).

Ltac exp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_exp_wrt_typ_of_lc_exp in J1;
              let J2 := fresh in pose proof H as J2; apply degree_exp_wrt_exp_of_lc_exp in J2; clear H
          end).

Ltac mode_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Lemma lc_typ_all_col_exists :
forall X1 c1 A1,
  lc_typ (open_typ_wrt_typ A1 (typ_var_f X1)) ->
  lc_typ (typ_all_col c1 A1).
Proof.
intros; typ_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_typ_all_etag_exists :
forall X1 ε1 A1,
  lc_typ (open_typ_wrt_typ A1 (typ_var_f X1)) ->
  lc_typ (typ_all_etag ε1 A1).
Proof.
intros; typ_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_bid_all_syn_exists :
forall Xd1 D1,
  lc_bid (open_bid_wrt_bid D1 (bid_var_f Xd1)) ->
  lc_bid (bid_all_syn D1).
Proof.
intros; bid_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_bid_all_inh_exists :
forall Xd1 D1,
  lc_bid (open_bid_wrt_bid D1 (bid_var_f Xd1)) ->
  lc_bid (bid_all_inh D1).
Proof.
intros; bid_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_bid_all_etag_exists :
forall Xd1 ε1 D1,
  lc_bid (open_bid_wrt_bid D1 (bid_var_f Xd1)) ->
  lc_bid (bid_all_etag ε1 D1).
Proof.
intros; bid_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_utyp_all_syn_exists :
forall Xf1 F1,
  lc_utyp (open_utyp_wrt_utyp F1 (utyp_var_f Xf1)) ->
  lc_utyp (utyp_all_syn F1).
Proof.
intros; utyp_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_utyp_all_etag_exists :
forall Xf1 ε1 F1,
  lc_utyp (open_utyp_wrt_utyp F1 (utyp_var_f Xf1)) ->
  lc_utyp (utyp_all_etag ε1 F1).
Proof.
intros; utyp_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_ctyp_all_exists :
forall U1 K1,
  lc_ctyp (open_ctyp_wrt_ctyp K1 (ctyp_var_f U1)) ->
  lc_ctyp (ctyp_all K1).
Proof.
intros; ctyp_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_skel_all_syn_exists :
forall Xr1 R1,
  lc_skel (open_skel_wrt_skel R1 (skel_var_f Xr1)) ->
  lc_skel (skel_all_syn R1).
Proof.
intros; skel_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_skel_all_inh_exists :
forall Xr1 R1,
  lc_skel (open_skel_wrt_skel R1 (skel_var_f Xr1)) ->
  lc_skel (skel_all_inh R1).
Proof.
intros; skel_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_skel_all_etag_exists :
forall Xr1 ε1 R1,
  lc_skel (open_skel_wrt_skel R1 (skel_var_f Xr1)) ->
  lc_skel (skel_all_etag ε1 R1).
Proof.
intros; skel_lc_exists_tac; eauto 6 with lngen.
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
  lc_typ A1 ->
  lc_exp (open_exp_wrt_exp e1 (exp_var_f x1)) ->
  lc_exp (exp_abs_anno A1 e1).
Proof.
intros; exp_lc_exists_tac; eauto 6 with lngen.
Qed.

#[export] Hint Extern 1 (lc_typ (typ_all_col _ _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_typ_all_col_exists X1) : core.

#[export] Hint Extern 1 (lc_typ (typ_all_etag _ _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_typ_all_etag_exists X1) : core.

#[export] Hint Extern 1 (lc_bid (bid_all_syn _)) =>
  let Xd1 := fresh in
  pick_fresh Xd1;
  apply (lc_bid_all_syn_exists Xd1) : core.

#[export] Hint Extern 1 (lc_bid (bid_all_inh _)) =>
  let Xd1 := fresh in
  pick_fresh Xd1;
  apply (lc_bid_all_inh_exists Xd1) : core.

#[export] Hint Extern 1 (lc_bid (bid_all_etag _ _)) =>
  let Xd1 := fresh in
  pick_fresh Xd1;
  apply (lc_bid_all_etag_exists Xd1) : core.

#[export] Hint Extern 1 (lc_utyp (utyp_all_syn _)) =>
  let Xf1 := fresh in
  pick_fresh Xf1;
  apply (lc_utyp_all_syn_exists Xf1) : core.

#[export] Hint Extern 1 (lc_utyp (utyp_all_etag _ _)) =>
  let Xf1 := fresh in
  pick_fresh Xf1;
  apply (lc_utyp_all_etag_exists Xf1) : core.

#[export] Hint Extern 1 (lc_ctyp (ctyp_all _)) =>
  let U1 := fresh in
  pick_fresh U1;
  apply (lc_ctyp_all_exists U1) : core.

#[export] Hint Extern 1 (lc_skel (skel_all_syn _)) =>
  let Xr1 := fresh in
  pick_fresh Xr1;
  apply (lc_skel_all_syn_exists Xr1) : core.

#[export] Hint Extern 1 (lc_skel (skel_all_inh _)) =>
  let Xr1 := fresh in
  pick_fresh Xr1;
  apply (lc_skel_all_inh_exists Xr1) : core.

#[export] Hint Extern 1 (lc_skel (skel_all_etag _ _)) =>
  let Xr1 := fresh in
  pick_fresh Xr1;
  apply (lc_skel_all_etag_exists Xr1) : core.

#[export] Hint Extern 1 (lc_exp (exp_abs _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_exp_abs_exists x1) : core.

#[export] Hint Extern 1 (lc_exp (exp_abs_anno _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_exp_abs_anno_exists x1) : core.

Lemma lc_body_typ_wrt_typ :
forall A1 A2,
  body_typ_wrt_typ A1 ->
  lc_typ A2 ->
  lc_typ (open_typ_wrt_typ A1 A2).
Proof.
unfold body_typ_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
typ_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_typ_wrt_typ : lngen.

Lemma lc_body_bid_wrt_bid :
forall D1 D2,
  body_bid_wrt_bid D1 ->
  lc_bid D2 ->
  lc_bid (open_bid_wrt_bid D1 D2).
Proof.
unfold body_bid_wrt_bid;
default_simp;
let Xd1 := fresh "x" in
pick_fresh Xd1;
specialize_all Xd1;
bid_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_bid_wrt_bid : lngen.

Lemma lc_body_utyp_wrt_utyp :
forall F1 F2,
  body_utyp_wrt_utyp F1 ->
  lc_utyp F2 ->
  lc_utyp (open_utyp_wrt_utyp F1 F2).
Proof.
unfold body_utyp_wrt_utyp;
default_simp;
let Xf1 := fresh "x" in
pick_fresh Xf1;
specialize_all Xf1;
utyp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_utyp_wrt_utyp : lngen.

Lemma lc_body_ctyp_wrt_ctyp :
forall K1 K2,
  body_ctyp_wrt_ctyp K1 ->
  lc_ctyp K2 ->
  lc_ctyp (open_ctyp_wrt_ctyp K1 K2).
Proof.
unfold body_ctyp_wrt_ctyp;
default_simp;
let U1 := fresh "x" in
pick_fresh U1;
specialize_all U1;
ctyp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_ctyp_wrt_ctyp : lngen.

Lemma lc_body_skel_wrt_skel :
forall R1 R2,
  body_skel_wrt_skel R1 ->
  lc_skel R2 ->
  lc_skel (open_skel_wrt_skel R1 R2).
Proof.
unfold body_skel_wrt_skel;
default_simp;
let Xr1 := fresh "x" in
pick_fresh Xr1;
specialize_all Xr1;
skel_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_skel_wrt_skel : lngen.

Lemma lc_body_dbind_wrt_typ :
forall db1 A1,
  body_dbind_wrt_typ db1 ->
  lc_typ A1 ->
  lc_dbind (open_dbind_wrt_typ db1 A1).
Proof.
unfold body_dbind_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
dbind_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_dbind_wrt_typ : lngen.

Lemma lc_body_exp_wrt_typ :
forall e1 A1,
  body_exp_wrt_typ e1 ->
  lc_typ A1 ->
  lc_exp (open_exp_wrt_typ e1 A1).
Proof.
unfold body_exp_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
exp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_exp_wrt_typ : lngen.

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

Lemma lc_body_typ_all_col_2 :
forall c1 A1,
  lc_typ (typ_all_col c1 A1) ->
  body_typ_wrt_typ A1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_typ_all_col_2 : lngen.

Lemma lc_body_typ_all_etag_2 :
forall ε1 A1,
  lc_typ (typ_all_etag ε1 A1) ->
  body_typ_wrt_typ A1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_typ_all_etag_2 : lngen.

Lemma lc_body_bid_all_syn_1 :
forall D1,
  lc_bid (bid_all_syn D1) ->
  body_bid_wrt_bid D1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_bid_all_syn_1 : lngen.

Lemma lc_body_bid_all_inh_1 :
forall D1,
  lc_bid (bid_all_inh D1) ->
  body_bid_wrt_bid D1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_bid_all_inh_1 : lngen.

Lemma lc_body_bid_all_etag_2 :
forall ε1 D1,
  lc_bid (bid_all_etag ε1 D1) ->
  body_bid_wrt_bid D1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_bid_all_etag_2 : lngen.

Lemma lc_body_utyp_all_syn_1 :
forall F1,
  lc_utyp (utyp_all_syn F1) ->
  body_utyp_wrt_utyp F1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_utyp_all_syn_1 : lngen.

Lemma lc_body_utyp_all_etag_2 :
forall ε1 F1,
  lc_utyp (utyp_all_etag ε1 F1) ->
  body_utyp_wrt_utyp F1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_utyp_all_etag_2 : lngen.

Lemma lc_body_ctyp_all_1 :
forall K1,
  lc_ctyp (ctyp_all K1) ->
  body_ctyp_wrt_ctyp K1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_ctyp_all_1 : lngen.

Lemma lc_body_skel_all_syn_1 :
forall R1,
  lc_skel (skel_all_syn R1) ->
  body_skel_wrt_skel R1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_skel_all_syn_1 : lngen.

Lemma lc_body_skel_all_inh_1 :
forall R1,
  lc_skel (skel_all_inh R1) ->
  body_skel_wrt_skel R1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_skel_all_inh_1 : lngen.

Lemma lc_body_skel_all_etag_2 :
forall ε1 R1,
  lc_skel (skel_all_etag ε1 R1) ->
  body_skel_wrt_skel R1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_skel_all_etag_2 : lngen.

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

Lemma lc_typ_unique_mutual :
(forall A1 (proof2 proof3 : lc_typ A1), proof2 = proof3).
Proof.
apply_mutual_ind lc_typ_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_typ_unique :
forall A1 (proof2 proof3 : lc_typ A1), proof2 = proof3.
Proof.
pose proof lc_typ_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_typ_unique : lngen.

(* begin hide *)

Lemma lc_bid_unique_mutual :
(forall D1 (proof2 proof3 : lc_bid D1), proof2 = proof3).
Proof.
apply_mutual_ind lc_bid_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_bid_unique :
forall D1 (proof2 proof3 : lc_bid D1), proof2 = proof3.
Proof.
pose proof lc_bid_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_bid_unique : lngen.

(* begin hide *)

Lemma lc_utyp_unique_mutual :
(forall F1 (proof2 proof3 : lc_utyp F1), proof2 = proof3).
Proof.
apply_mutual_ind lc_utyp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_utyp_unique :
forall F1 (proof2 proof3 : lc_utyp F1), proof2 = proof3.
Proof.
pose proof lc_utyp_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_utyp_unique : lngen.

(* begin hide *)

Lemma lc_ctyp_unique_mutual :
(forall K1 (proof2 proof3 : lc_ctyp K1), proof2 = proof3).
Proof.
apply_mutual_ind lc_ctyp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_ctyp_unique :
forall K1 (proof2 proof3 : lc_ctyp K1), proof2 = proof3.
Proof.
pose proof lc_ctyp_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_ctyp_unique : lngen.

(* begin hide *)

Lemma lc_skel_unique_mutual :
(forall R1 (proof2 proof3 : lc_skel R1), proof2 = proof3).
Proof.
apply_mutual_ind lc_skel_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_skel_unique :
forall R1 (proof2 proof3 : lc_skel R1), proof2 = proof3.
Proof.
pose proof lc_skel_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_skel_unique : lngen.

(* begin hide *)

Lemma lc_dbind_unique_mutual :
(forall db1 (proof2 proof3 : lc_dbind db1), proof2 = proof3).
Proof.
apply_mutual_ind lc_dbind_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_dbind_unique :
forall db1 (proof2 proof3 : lc_dbind db1), proof2 = proof3.
Proof.
pose proof lc_dbind_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_dbind_unique : lngen.

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

Lemma lc_typ_of_lc_set_typ_mutual :
(forall A1, lc_set_typ A1 -> lc_typ A1).
Proof.
apply_mutual_ind lc_set_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_typ_of_lc_set_typ :
forall A1, lc_set_typ A1 -> lc_typ A1.
Proof.
pose proof lc_typ_of_lc_set_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_typ_of_lc_set_typ : lngen.

(* begin hide *)

Lemma lc_bid_of_lc_set_bid_mutual :
(forall D1, lc_set_bid D1 -> lc_bid D1).
Proof.
apply_mutual_ind lc_set_bid_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_bid_of_lc_set_bid :
forall D1, lc_set_bid D1 -> lc_bid D1.
Proof.
pose proof lc_bid_of_lc_set_bid_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_bid_of_lc_set_bid : lngen.

(* begin hide *)

Lemma lc_utyp_of_lc_set_utyp_mutual :
(forall F1, lc_set_utyp F1 -> lc_utyp F1).
Proof.
apply_mutual_ind lc_set_utyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_utyp_of_lc_set_utyp :
forall F1, lc_set_utyp F1 -> lc_utyp F1.
Proof.
pose proof lc_utyp_of_lc_set_utyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_utyp_of_lc_set_utyp : lngen.

(* begin hide *)

Lemma lc_ctyp_of_lc_set_ctyp_mutual :
(forall K1, lc_set_ctyp K1 -> lc_ctyp K1).
Proof.
apply_mutual_ind lc_set_ctyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_ctyp_of_lc_set_ctyp :
forall K1, lc_set_ctyp K1 -> lc_ctyp K1.
Proof.
pose proof lc_ctyp_of_lc_set_ctyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_ctyp_of_lc_set_ctyp : lngen.

(* begin hide *)

Lemma lc_skel_of_lc_set_skel_mutual :
(forall R1, lc_set_skel R1 -> lc_skel R1).
Proof.
apply_mutual_ind lc_set_skel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_skel_of_lc_set_skel :
forall R1, lc_set_skel R1 -> lc_skel R1.
Proof.
pose proof lc_skel_of_lc_set_skel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_skel_of_lc_set_skel : lngen.

(* begin hide *)

Lemma lc_dbind_of_lc_set_dbind_mutual :
(forall db1, lc_set_dbind db1 -> lc_dbind db1).
Proof.
apply_mutual_ind lc_set_dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_dbind_of_lc_set_dbind :
forall db1, lc_set_dbind db1 -> lc_dbind db1.
Proof.
pose proof lc_dbind_of_lc_set_dbind_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_dbind_of_lc_set_dbind : lngen.

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

Lemma lc_set_typ_of_lc_typ_size_mutual :
forall i1,
(forall A1,
  size_typ A1 = i1 ->
  lc_typ A1 ->
  lc_set_typ A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind typ_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_colour_of_lc_colour];
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

Lemma lc_set_typ_of_lc_typ :
forall A1,
  lc_typ A1 ->
  lc_set_typ A1.
Proof.
intros A1; intros;
pose proof (lc_set_typ_of_lc_typ_size_mutual (size_typ A1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_typ_of_lc_typ : lngen.

(* begin hide *)

Lemma lc_set_bid_of_lc_bid_size_mutual :
forall i1,
(forall D1,
  size_bid D1 = i1 ->
  lc_bid D1 ->
  lc_set_bid D1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind bid_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_bid_of_lc_bid];
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

Lemma lc_set_bid_of_lc_bid :
forall D1,
  lc_bid D1 ->
  lc_set_bid D1.
Proof.
intros D1; intros;
pose proof (lc_set_bid_of_lc_bid_size_mutual (size_bid D1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_bid_of_lc_bid : lngen.

(* begin hide *)

Lemma lc_set_utyp_of_lc_utyp_size_mutual :
forall i1,
(forall F1,
  size_utyp F1 = i1 ->
  lc_utyp F1 ->
  lc_set_utyp F1).
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
forall F1,
  lc_utyp F1 ->
  lc_set_utyp F1.
Proof.
intros F1; intros;
pose proof (lc_set_utyp_of_lc_utyp_size_mutual (size_utyp F1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_utyp_of_lc_utyp : lngen.

(* begin hide *)

Lemma lc_set_ctyp_of_lc_ctyp_size_mutual :
forall i1,
(forall K1,
  size_ctyp K1 = i1 ->
  lc_ctyp K1 ->
  lc_set_ctyp K1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind ctyp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_ctyp_of_lc_ctyp];
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

Lemma lc_set_ctyp_of_lc_ctyp :
forall K1,
  lc_ctyp K1 ->
  lc_set_ctyp K1.
Proof.
intros K1; intros;
pose proof (lc_set_ctyp_of_lc_ctyp_size_mutual (size_ctyp K1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_ctyp_of_lc_ctyp : lngen.

(* begin hide *)

Lemma lc_set_skel_of_lc_skel_size_mutual :
forall i1,
(forall R1,
  size_skel R1 = i1 ->
  lc_skel R1 ->
  lc_set_skel R1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind skel_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_skel_of_lc_skel];
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

Lemma lc_set_skel_of_lc_skel :
forall R1,
  lc_skel R1 ->
  lc_set_skel R1.
Proof.
intros R1; intros;
pose proof (lc_set_skel_of_lc_skel_size_mutual (size_skel R1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_skel_of_lc_skel : lngen.

(* begin hide *)

Lemma lc_set_dbind_of_lc_dbind_size_mutual :
forall i1,
(forall db1,
  size_dbind db1 = i1 ->
  lc_dbind db1 ->
  lc_set_dbind db1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind dbind_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_colour_of_lc_colour
 | apply lc_set_dbind_of_lc_dbind];
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

Lemma lc_set_dbind_of_lc_dbind :
forall db1,
  lc_dbind db1 ->
  lc_set_dbind db1.
Proof.
intros db1; intros;
pose proof (lc_set_dbind_of_lc_dbind_size_mutual (size_dbind db1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_dbind_of_lc_dbind : lngen.

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
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_colour_of_lc_colour
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

Lemma close_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 `notin` ftvar_in_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 A1 = A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_degree_typ_wrt_typ :
forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 `notin` ftvar_in_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 A1 = A1.
Proof.
pose proof close_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_typ_wrt_typ_rec_degree_typ_wrt_typ : lngen.
#[export] Hint Rewrite close_typ_wrt_typ_rec_degree_typ_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_bid_wrt_bid_rec_degree_bid_wrt_bid_mutual :
(forall D1 Xd1 n1,
  degree_bid_wrt_bid n1 D1 ->
  Xd1 `notin` ftvar_in_bid D1 ->
  close_bid_wrt_bid_rec n1 Xd1 D1 = D1).
Proof.
apply_mutual_ind bid_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_bid_wrt_bid_rec_degree_bid_wrt_bid :
forall D1 Xd1 n1,
  degree_bid_wrt_bid n1 D1 ->
  Xd1 `notin` ftvar_in_bid D1 ->
  close_bid_wrt_bid_rec n1 Xd1 D1 = D1.
Proof.
pose proof close_bid_wrt_bid_rec_degree_bid_wrt_bid_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_bid_wrt_bid_rec_degree_bid_wrt_bid : lngen.
#[export] Hint Rewrite close_bid_wrt_bid_rec_degree_bid_wrt_bid using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_utyp_wrt_utyp_rec_degree_utyp_wrt_utyp_mutual :
(forall F1 Xf1 n1,
  degree_utyp_wrt_utyp n1 F1 ->
  Xf1 `notin` ftvar_in_utyp F1 ->
  close_utyp_wrt_utyp_rec n1 Xf1 F1 = F1).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_utyp_wrt_utyp_rec_degree_utyp_wrt_utyp :
forall F1 Xf1 n1,
  degree_utyp_wrt_utyp n1 F1 ->
  Xf1 `notin` ftvar_in_utyp F1 ->
  close_utyp_wrt_utyp_rec n1 Xf1 F1 = F1.
Proof.
pose proof close_utyp_wrt_utyp_rec_degree_utyp_wrt_utyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_utyp_wrt_utyp_rec_degree_utyp_wrt_utyp : lngen.
#[export] Hint Rewrite close_utyp_wrt_utyp_rec_degree_utyp_wrt_utyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_ctyp_wrt_ctyp_rec_degree_ctyp_wrt_ctyp_mutual :
(forall K1 U1 n1,
  degree_ctyp_wrt_ctyp n1 K1 ->
  U1 `notin` ftvar_in_ctyp K1 ->
  close_ctyp_wrt_ctyp_rec n1 U1 K1 = K1).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_ctyp_wrt_ctyp_rec_degree_ctyp_wrt_ctyp :
forall K1 U1 n1,
  degree_ctyp_wrt_ctyp n1 K1 ->
  U1 `notin` ftvar_in_ctyp K1 ->
  close_ctyp_wrt_ctyp_rec n1 U1 K1 = K1.
Proof.
pose proof close_ctyp_wrt_ctyp_rec_degree_ctyp_wrt_ctyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_ctyp_wrt_ctyp_rec_degree_ctyp_wrt_ctyp : lngen.
#[export] Hint Rewrite close_ctyp_wrt_ctyp_rec_degree_ctyp_wrt_ctyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_skel_wrt_skel_rec_degree_skel_wrt_skel_mutual :
(forall R1 Xr1 n1,
  degree_skel_wrt_skel n1 R1 ->
  Xr1 `notin` ftvar_in_skel R1 ->
  close_skel_wrt_skel_rec n1 Xr1 R1 = R1).
Proof.
apply_mutual_ind skel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_skel_wrt_skel_rec_degree_skel_wrt_skel :
forall R1 Xr1 n1,
  degree_skel_wrt_skel n1 R1 ->
  Xr1 `notin` ftvar_in_skel R1 ->
  close_skel_wrt_skel_rec n1 Xr1 R1 = R1.
Proof.
pose proof close_skel_wrt_skel_rec_degree_skel_wrt_skel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_skel_wrt_skel_rec_degree_skel_wrt_skel : lngen.
#[export] Hint Rewrite close_skel_wrt_skel_rec_degree_skel_wrt_skel using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_dbind_wrt_typ_rec_degree_dbind_wrt_typ_mutual :
(forall db1 X1 n1,
  degree_dbind_wrt_typ n1 db1 ->
  X1 `notin` ftvar_in_dbind db1 ->
  close_dbind_wrt_typ_rec n1 X1 db1 = db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dbind_wrt_typ_rec_degree_dbind_wrt_typ :
forall db1 X1 n1,
  degree_dbind_wrt_typ n1 db1 ->
  X1 `notin` ftvar_in_dbind db1 ->
  close_dbind_wrt_typ_rec n1 X1 db1 = db1.
Proof.
pose proof close_dbind_wrt_typ_rec_degree_dbind_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_dbind_wrt_typ_rec_degree_dbind_wrt_typ : lngen.
#[export] Hint Rewrite close_dbind_wrt_typ_rec_degree_dbind_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_degree_exp_wrt_typ :
forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 e1 = e1.
Proof.
pose proof close_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_exp_wrt_typ_rec_degree_exp_wrt_typ : lngen.
#[export] Hint Rewrite close_exp_wrt_typ_rec_degree_exp_wrt_typ using solve [auto] : lngen.

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

Lemma close_typ_wrt_typ_lc_typ :
forall A1 X1,
  lc_typ A1 ->
  X1 `notin` ftvar_in_typ A1 ->
  close_typ_wrt_typ X1 A1 = A1.
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_typ_wrt_typ_lc_typ : lngen.
#[export] Hint Rewrite close_typ_wrt_typ_lc_typ using solve [auto] : lngen.

Lemma close_bid_wrt_bid_lc_bid :
forall D1 Xd1,
  lc_bid D1 ->
  Xd1 `notin` ftvar_in_bid D1 ->
  close_bid_wrt_bid Xd1 D1 = D1.
Proof.
unfold close_bid_wrt_bid; default_simp.
Qed.

#[export] Hint Resolve close_bid_wrt_bid_lc_bid : lngen.
#[export] Hint Rewrite close_bid_wrt_bid_lc_bid using solve [auto] : lngen.

Lemma close_utyp_wrt_utyp_lc_utyp :
forall F1 Xf1,
  lc_utyp F1 ->
  Xf1 `notin` ftvar_in_utyp F1 ->
  close_utyp_wrt_utyp Xf1 F1 = F1.
Proof.
unfold close_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve close_utyp_wrt_utyp_lc_utyp : lngen.
#[export] Hint Rewrite close_utyp_wrt_utyp_lc_utyp using solve [auto] : lngen.

Lemma close_ctyp_wrt_ctyp_lc_ctyp :
forall K1 U1,
  lc_ctyp K1 ->
  U1 `notin` ftvar_in_ctyp K1 ->
  close_ctyp_wrt_ctyp U1 K1 = K1.
Proof.
unfold close_ctyp_wrt_ctyp; default_simp.
Qed.

#[export] Hint Resolve close_ctyp_wrt_ctyp_lc_ctyp : lngen.
#[export] Hint Rewrite close_ctyp_wrt_ctyp_lc_ctyp using solve [auto] : lngen.

Lemma close_skel_wrt_skel_lc_skel :
forall R1 Xr1,
  lc_skel R1 ->
  Xr1 `notin` ftvar_in_skel R1 ->
  close_skel_wrt_skel Xr1 R1 = R1.
Proof.
unfold close_skel_wrt_skel; default_simp.
Qed.

#[export] Hint Resolve close_skel_wrt_skel_lc_skel : lngen.
#[export] Hint Rewrite close_skel_wrt_skel_lc_skel using solve [auto] : lngen.

Lemma close_dbind_wrt_typ_lc_dbind :
forall db1 X1,
  lc_dbind db1 ->
  X1 `notin` ftvar_in_dbind db1 ->
  close_dbind_wrt_typ X1 db1 = db1.
Proof.
unfold close_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_dbind_wrt_typ_lc_dbind : lngen.
#[export] Hint Rewrite close_dbind_wrt_typ_lc_dbind using solve [auto] : lngen.

Lemma close_exp_wrt_typ_lc_exp :
forall e1 X1,
  lc_exp e1 ->
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_typ X1 e1 = e1.
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_exp_wrt_typ_lc_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_typ_lc_exp using solve [auto] : lngen.

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

Lemma open_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual :
(forall A2 A1 n1,
  degree_typ_wrt_typ n1 A2 ->
  open_typ_wrt_typ_rec n1 A1 A2 = A2).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_degree_typ_wrt_typ :
forall A2 A1 n1,
  degree_typ_wrt_typ n1 A2 ->
  open_typ_wrt_typ_rec n1 A1 A2 = A2.
Proof.
pose proof open_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_typ_wrt_typ_rec_degree_typ_wrt_typ : lngen.
#[export] Hint Rewrite open_typ_wrt_typ_rec_degree_typ_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_bid_wrt_bid_rec_degree_bid_wrt_bid_mutual :
(forall D2 D1 n1,
  degree_bid_wrt_bid n1 D2 ->
  open_bid_wrt_bid_rec n1 D1 D2 = D2).
Proof.
apply_mutual_ind bid_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_bid_wrt_bid_rec_degree_bid_wrt_bid :
forall D2 D1 n1,
  degree_bid_wrt_bid n1 D2 ->
  open_bid_wrt_bid_rec n1 D1 D2 = D2.
Proof.
pose proof open_bid_wrt_bid_rec_degree_bid_wrt_bid_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_bid_wrt_bid_rec_degree_bid_wrt_bid : lngen.
#[export] Hint Rewrite open_bid_wrt_bid_rec_degree_bid_wrt_bid using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_utyp_wrt_utyp_rec_degree_utyp_wrt_utyp_mutual :
(forall F2 F1 n1,
  degree_utyp_wrt_utyp n1 F2 ->
  open_utyp_wrt_utyp_rec n1 F1 F2 = F2).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_utyp_wrt_utyp_rec_degree_utyp_wrt_utyp :
forall F2 F1 n1,
  degree_utyp_wrt_utyp n1 F2 ->
  open_utyp_wrt_utyp_rec n1 F1 F2 = F2.
Proof.
pose proof open_utyp_wrt_utyp_rec_degree_utyp_wrt_utyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_utyp_wrt_utyp_rec_degree_utyp_wrt_utyp : lngen.
#[export] Hint Rewrite open_utyp_wrt_utyp_rec_degree_utyp_wrt_utyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_ctyp_wrt_ctyp_rec_degree_ctyp_wrt_ctyp_mutual :
(forall K2 K1 n1,
  degree_ctyp_wrt_ctyp n1 K2 ->
  open_ctyp_wrt_ctyp_rec n1 K1 K2 = K2).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_ctyp_wrt_ctyp_rec_degree_ctyp_wrt_ctyp :
forall K2 K1 n1,
  degree_ctyp_wrt_ctyp n1 K2 ->
  open_ctyp_wrt_ctyp_rec n1 K1 K2 = K2.
Proof.
pose proof open_ctyp_wrt_ctyp_rec_degree_ctyp_wrt_ctyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_ctyp_wrt_ctyp_rec_degree_ctyp_wrt_ctyp : lngen.
#[export] Hint Rewrite open_ctyp_wrt_ctyp_rec_degree_ctyp_wrt_ctyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_skel_wrt_skel_rec_degree_skel_wrt_skel_mutual :
(forall R2 R1 n1,
  degree_skel_wrt_skel n1 R2 ->
  open_skel_wrt_skel_rec n1 R1 R2 = R2).
Proof.
apply_mutual_ind skel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_skel_wrt_skel_rec_degree_skel_wrt_skel :
forall R2 R1 n1,
  degree_skel_wrt_skel n1 R2 ->
  open_skel_wrt_skel_rec n1 R1 R2 = R2.
Proof.
pose proof open_skel_wrt_skel_rec_degree_skel_wrt_skel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_skel_wrt_skel_rec_degree_skel_wrt_skel : lngen.
#[export] Hint Rewrite open_skel_wrt_skel_rec_degree_skel_wrt_skel using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_dbind_wrt_typ_rec_degree_dbind_wrt_typ_mutual :
(forall db1 A1 n1,
  degree_dbind_wrt_typ n1 db1 ->
  open_dbind_wrt_typ_rec n1 A1 db1 = db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dbind_wrt_typ_rec_degree_dbind_wrt_typ :
forall db1 A1 n1,
  degree_dbind_wrt_typ n1 db1 ->
  open_dbind_wrt_typ_rec n1 A1 db1 = db1.
Proof.
pose proof open_dbind_wrt_typ_rec_degree_dbind_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_dbind_wrt_typ_rec_degree_dbind_wrt_typ : lngen.
#[export] Hint Rewrite open_dbind_wrt_typ_rec_degree_dbind_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual :
(forall e1 A1 n1,
  degree_exp_wrt_typ n1 e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_degree_exp_wrt_typ :
forall e1 A1 n1,
  degree_exp_wrt_typ n1 e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = e1.
Proof.
pose proof open_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_exp_wrt_typ_rec_degree_exp_wrt_typ : lngen.
#[export] Hint Rewrite open_exp_wrt_typ_rec_degree_exp_wrt_typ using solve [auto] : lngen.

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

Lemma open_typ_wrt_typ_lc_typ :
forall A2 A1,
  lc_typ A2 ->
  open_typ_wrt_typ A2 A1 = A2.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_typ_wrt_typ_lc_typ : lngen.
#[export] Hint Rewrite open_typ_wrt_typ_lc_typ using solve [auto] : lngen.

Lemma open_bid_wrt_bid_lc_bid :
forall D2 D1,
  lc_bid D2 ->
  open_bid_wrt_bid D2 D1 = D2.
Proof.
unfold open_bid_wrt_bid; default_simp.
Qed.

#[export] Hint Resolve open_bid_wrt_bid_lc_bid : lngen.
#[export] Hint Rewrite open_bid_wrt_bid_lc_bid using solve [auto] : lngen.

Lemma open_utyp_wrt_utyp_lc_utyp :
forall F2 F1,
  lc_utyp F2 ->
  open_utyp_wrt_utyp F2 F1 = F2.
Proof.
unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve open_utyp_wrt_utyp_lc_utyp : lngen.
#[export] Hint Rewrite open_utyp_wrt_utyp_lc_utyp using solve [auto] : lngen.

Lemma open_ctyp_wrt_ctyp_lc_ctyp :
forall K2 K1,
  lc_ctyp K2 ->
  open_ctyp_wrt_ctyp K2 K1 = K2.
Proof.
unfold open_ctyp_wrt_ctyp; default_simp.
Qed.

#[export] Hint Resolve open_ctyp_wrt_ctyp_lc_ctyp : lngen.
#[export] Hint Rewrite open_ctyp_wrt_ctyp_lc_ctyp using solve [auto] : lngen.

Lemma open_skel_wrt_skel_lc_skel :
forall R2 R1,
  lc_skel R2 ->
  open_skel_wrt_skel R2 R1 = R2.
Proof.
unfold open_skel_wrt_skel; default_simp.
Qed.

#[export] Hint Resolve open_skel_wrt_skel_lc_skel : lngen.
#[export] Hint Rewrite open_skel_wrt_skel_lc_skel using solve [auto] : lngen.

Lemma open_dbind_wrt_typ_lc_dbind :
forall db1 A1,
  lc_dbind db1 ->
  open_dbind_wrt_typ db1 A1 = db1.
Proof.
unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_dbind_wrt_typ_lc_dbind : lngen.
#[export] Hint Rewrite open_dbind_wrt_typ_lc_dbind using solve [auto] : lngen.

Lemma open_exp_wrt_typ_lc_exp :
forall e1 A1,
  lc_exp e1 ->
  open_exp_wrt_typ e1 A1 = e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_typ_lc_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_typ_lc_exp using solve [auto] : lngen.

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

Lemma ftvar_in_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  ftvar_in_typ (close_typ_wrt_typ_rec n1 X1 A1) [=] remove X1 (ftvar_in_typ A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  ftvar_in_typ (close_typ_wrt_typ_rec n1 X1 A1) [=] remove X1 (ftvar_in_typ A1).
Proof.
pose proof ftvar_in_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_close_typ_wrt_typ_rec : lngen.
#[export] Hint Rewrite ftvar_in_typ_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bid_close_bid_wrt_bid_rec_mutual :
(forall D1 Xd1 n1,
  ftvar_in_bid (close_bid_wrt_bid_rec n1 Xd1 D1) [=] remove Xd1 (ftvar_in_bid D1)).
Proof.
apply_mutual_ind bid_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bid_close_bid_wrt_bid_rec :
forall D1 Xd1 n1,
  ftvar_in_bid (close_bid_wrt_bid_rec n1 Xd1 D1) [=] remove Xd1 (ftvar_in_bid D1).
Proof.
pose proof ftvar_in_bid_close_bid_wrt_bid_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bid_close_bid_wrt_bid_rec : lngen.
#[export] Hint Rewrite ftvar_in_bid_close_bid_wrt_bid_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_utyp_close_utyp_wrt_utyp_rec_mutual :
(forall F1 Xf1 n1,
  ftvar_in_utyp (close_utyp_wrt_utyp_rec n1 Xf1 F1) [=] remove Xf1 (ftvar_in_utyp F1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_utyp_close_utyp_wrt_utyp_rec :
forall F1 Xf1 n1,
  ftvar_in_utyp (close_utyp_wrt_utyp_rec n1 Xf1 F1) [=] remove Xf1 (ftvar_in_utyp F1).
Proof.
pose proof ftvar_in_utyp_close_utyp_wrt_utyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_utyp_close_utyp_wrt_utyp_rec : lngen.
#[export] Hint Rewrite ftvar_in_utyp_close_utyp_wrt_utyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_ctyp_close_ctyp_wrt_ctyp_rec_mutual :
(forall K1 U1 n1,
  ftvar_in_ctyp (close_ctyp_wrt_ctyp_rec n1 U1 K1) [=] remove U1 (ftvar_in_ctyp K1)).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_ctyp_close_ctyp_wrt_ctyp_rec :
forall K1 U1 n1,
  ftvar_in_ctyp (close_ctyp_wrt_ctyp_rec n1 U1 K1) [=] remove U1 (ftvar_in_ctyp K1).
Proof.
pose proof ftvar_in_ctyp_close_ctyp_wrt_ctyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_ctyp_close_ctyp_wrt_ctyp_rec : lngen.
#[export] Hint Rewrite ftvar_in_ctyp_close_ctyp_wrt_ctyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_skel_close_skel_wrt_skel_rec_mutual :
(forall R1 Xr1 n1,
  ftvar_in_skel (close_skel_wrt_skel_rec n1 Xr1 R1) [=] remove Xr1 (ftvar_in_skel R1)).
Proof.
apply_mutual_ind skel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_skel_close_skel_wrt_skel_rec :
forall R1 Xr1 n1,
  ftvar_in_skel (close_skel_wrt_skel_rec n1 Xr1 R1) [=] remove Xr1 (ftvar_in_skel R1).
Proof.
pose proof ftvar_in_skel_close_skel_wrt_skel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_skel_close_skel_wrt_skel_rec : lngen.
#[export] Hint Rewrite ftvar_in_skel_close_skel_wrt_skel_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_dbind_close_dbind_wrt_typ_rec_mutual :
(forall db1 X1 n1,
  ftvar_in_dbind (close_dbind_wrt_typ_rec n1 X1 db1) [=] remove X1 (ftvar_in_dbind db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_dbind_close_dbind_wrt_typ_rec :
forall db1 X1 n1,
  ftvar_in_dbind (close_dbind_wrt_typ_rec n1 X1 db1) [=] remove X1 (ftvar_in_dbind db1).
Proof.
pose proof ftvar_in_dbind_close_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_dbind_close_dbind_wrt_typ_rec : lngen.
#[export] Hint Rewrite ftvar_in_dbind_close_dbind_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  ftvar_in_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] remove X1 (ftvar_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  ftvar_in_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] remove X1 (ftvar_in_exp e1).
Proof.
pose proof ftvar_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_close_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite ftvar_in_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

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

Lemma fvar_in_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  fvar_in_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] fvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  fvar_in_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] fvar_in_exp e1.
Proof.
pose proof fvar_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_close_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite fvar_in_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

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

Lemma ftvar_in_typ_close_typ_wrt_typ :
forall A1 X1,
  ftvar_in_typ (close_typ_wrt_typ X1 A1) [=] remove X1 (ftvar_in_typ A1).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_typ_close_typ_wrt_typ : lngen.
#[export] Hint Rewrite ftvar_in_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma ftvar_in_bid_close_bid_wrt_bid :
forall D1 Xd1,
  ftvar_in_bid (close_bid_wrt_bid Xd1 D1) [=] remove Xd1 (ftvar_in_bid D1).
Proof.
unfold close_bid_wrt_bid; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_bid_close_bid_wrt_bid : lngen.
#[export] Hint Rewrite ftvar_in_bid_close_bid_wrt_bid using solve [auto] : lngen.

Lemma ftvar_in_utyp_close_utyp_wrt_utyp :
forall F1 Xf1,
  ftvar_in_utyp (close_utyp_wrt_utyp Xf1 F1) [=] remove Xf1 (ftvar_in_utyp F1).
Proof.
unfold close_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_utyp_close_utyp_wrt_utyp : lngen.
#[export] Hint Rewrite ftvar_in_utyp_close_utyp_wrt_utyp using solve [auto] : lngen.

Lemma ftvar_in_ctyp_close_ctyp_wrt_ctyp :
forall K1 U1,
  ftvar_in_ctyp (close_ctyp_wrt_ctyp U1 K1) [=] remove U1 (ftvar_in_ctyp K1).
Proof.
unfold close_ctyp_wrt_ctyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_ctyp_close_ctyp_wrt_ctyp : lngen.
#[export] Hint Rewrite ftvar_in_ctyp_close_ctyp_wrt_ctyp using solve [auto] : lngen.

Lemma ftvar_in_skel_close_skel_wrt_skel :
forall R1 Xr1,
  ftvar_in_skel (close_skel_wrt_skel Xr1 R1) [=] remove Xr1 (ftvar_in_skel R1).
Proof.
unfold close_skel_wrt_skel; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_skel_close_skel_wrt_skel : lngen.
#[export] Hint Rewrite ftvar_in_skel_close_skel_wrt_skel using solve [auto] : lngen.

Lemma ftvar_in_dbind_close_dbind_wrt_typ :
forall db1 X1,
  ftvar_in_dbind (close_dbind_wrt_typ X1 db1) [=] remove X1 (ftvar_in_dbind db1).
Proof.
unfold close_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_dbind_close_dbind_wrt_typ : lngen.
#[export] Hint Rewrite ftvar_in_dbind_close_dbind_wrt_typ using solve [auto] : lngen.

Lemma ftvar_in_exp_close_exp_wrt_typ :
forall e1 X1,
  ftvar_in_exp (close_exp_wrt_typ X1 e1) [=] remove X1 (ftvar_in_exp e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_close_exp_wrt_typ : lngen.
#[export] Hint Rewrite ftvar_in_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma ftvar_in_exp_close_exp_wrt_exp :
forall e1 x1,
  ftvar_in_exp (close_exp_wrt_exp x1 e1) [=] ftvar_in_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite ftvar_in_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma fvar_in_exp_close_exp_wrt_typ :
forall e1 X1,
  fvar_in_exp (close_exp_wrt_typ X1 e1) [=] fvar_in_exp e1.
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_close_exp_wrt_typ : lngen.
#[export] Hint Rewrite fvar_in_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma fvar_in_exp_close_exp_wrt_exp :
forall e1 x1,
  fvar_in_exp (close_exp_wrt_exp x1 e1) [=] remove x1 (fvar_in_exp e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite fvar_in_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_typ_open_typ_wrt_typ_rec_lower_mutual :
(forall A1 A2 n1,
  ftvar_in_typ A1 [<=] ftvar_in_typ (open_typ_wrt_typ_rec n1 A2 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_typ_open_typ_wrt_typ_rec_lower :
forall A1 A2 n1,
  ftvar_in_typ A1 [<=] ftvar_in_typ (open_typ_wrt_typ_rec n1 A2 A1).
Proof.
pose proof ftvar_in_typ_open_typ_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_open_typ_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bid_open_bid_wrt_bid_rec_lower_mutual :
(forall D1 D2 n1,
  ftvar_in_bid D1 [<=] ftvar_in_bid (open_bid_wrt_bid_rec n1 D2 D1)).
Proof.
apply_mutual_ind bid_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bid_open_bid_wrt_bid_rec_lower :
forall D1 D2 n1,
  ftvar_in_bid D1 [<=] ftvar_in_bid (open_bid_wrt_bid_rec n1 D2 D1).
Proof.
pose proof ftvar_in_bid_open_bid_wrt_bid_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bid_open_bid_wrt_bid_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_utyp_open_utyp_wrt_utyp_rec_lower_mutual :
(forall F1 F2 n1,
  ftvar_in_utyp F1 [<=] ftvar_in_utyp (open_utyp_wrt_utyp_rec n1 F2 F1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_utyp_open_utyp_wrt_utyp_rec_lower :
forall F1 F2 n1,
  ftvar_in_utyp F1 [<=] ftvar_in_utyp (open_utyp_wrt_utyp_rec n1 F2 F1).
Proof.
pose proof ftvar_in_utyp_open_utyp_wrt_utyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_utyp_open_utyp_wrt_utyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_ctyp_open_ctyp_wrt_ctyp_rec_lower_mutual :
(forall K1 K2 n1,
  ftvar_in_ctyp K1 [<=] ftvar_in_ctyp (open_ctyp_wrt_ctyp_rec n1 K2 K1)).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_ctyp_open_ctyp_wrt_ctyp_rec_lower :
forall K1 K2 n1,
  ftvar_in_ctyp K1 [<=] ftvar_in_ctyp (open_ctyp_wrt_ctyp_rec n1 K2 K1).
Proof.
pose proof ftvar_in_ctyp_open_ctyp_wrt_ctyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_ctyp_open_ctyp_wrt_ctyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_skel_open_skel_wrt_skel_rec_lower_mutual :
(forall R1 R2 n1,
  ftvar_in_skel R1 [<=] ftvar_in_skel (open_skel_wrt_skel_rec n1 R2 R1)).
Proof.
apply_mutual_ind skel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_skel_open_skel_wrt_skel_rec_lower :
forall R1 R2 n1,
  ftvar_in_skel R1 [<=] ftvar_in_skel (open_skel_wrt_skel_rec n1 R2 R1).
Proof.
pose proof ftvar_in_skel_open_skel_wrt_skel_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_skel_open_skel_wrt_skel_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_dbind_open_dbind_wrt_typ_rec_lower_mutual :
(forall db1 A1 n1,
  ftvar_in_dbind db1 [<=] ftvar_in_dbind (open_dbind_wrt_typ_rec n1 A1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_dbind_open_dbind_wrt_typ_rec_lower :
forall db1 A1 n1,
  ftvar_in_dbind db1 [<=] ftvar_in_dbind (open_dbind_wrt_typ_rec n1 A1 db1).
Proof.
pose proof ftvar_in_dbind_open_dbind_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_dbind_open_dbind_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_typ_rec_lower_mutual :
(forall e1 A1 n1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_typ_rec_lower :
forall e1 A1 n1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1).
Proof.
pose proof ftvar_in_exp_open_exp_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_typ_rec_lower : lngen.

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

Lemma fvar_in_exp_open_exp_wrt_typ_rec_lower_mutual :
(forall e1 A1 n1,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_typ_rec_lower :
forall e1 A1 n1,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1).
Proof.
pose proof fvar_in_exp_open_exp_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_typ_rec_lower : lngen.

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

Lemma ftvar_in_typ_open_typ_wrt_typ_lower :
forall A1 A2,
  ftvar_in_typ A1 [<=] ftvar_in_typ (open_typ_wrt_typ A1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_typ_open_typ_wrt_typ_lower : lngen.

Lemma ftvar_in_bid_open_bid_wrt_bid_lower :
forall D1 D2,
  ftvar_in_bid D1 [<=] ftvar_in_bid (open_bid_wrt_bid D1 D2).
Proof.
unfold open_bid_wrt_bid; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_bid_open_bid_wrt_bid_lower : lngen.

Lemma ftvar_in_utyp_open_utyp_wrt_utyp_lower :
forall F1 F2,
  ftvar_in_utyp F1 [<=] ftvar_in_utyp (open_utyp_wrt_utyp F1 F2).
Proof.
unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_utyp_open_utyp_wrt_utyp_lower : lngen.

Lemma ftvar_in_ctyp_open_ctyp_wrt_ctyp_lower :
forall K1 K2,
  ftvar_in_ctyp K1 [<=] ftvar_in_ctyp (open_ctyp_wrt_ctyp K1 K2).
Proof.
unfold open_ctyp_wrt_ctyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_ctyp_open_ctyp_wrt_ctyp_lower : lngen.

Lemma ftvar_in_skel_open_skel_wrt_skel_lower :
forall R1 R2,
  ftvar_in_skel R1 [<=] ftvar_in_skel (open_skel_wrt_skel R1 R2).
Proof.
unfold open_skel_wrt_skel; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_skel_open_skel_wrt_skel_lower : lngen.

Lemma ftvar_in_dbind_open_dbind_wrt_typ_lower :
forall db1 A1,
  ftvar_in_dbind db1 [<=] ftvar_in_dbind (open_dbind_wrt_typ db1 A1).
Proof.
unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_dbind_open_dbind_wrt_typ_lower : lngen.

Lemma ftvar_in_exp_open_exp_wrt_typ_lower :
forall e1 A1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_typ_lower : lngen.

Lemma ftvar_in_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_exp_lower : lngen.

Lemma fvar_in_exp_open_exp_wrt_typ_lower :
forall e1 A1,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_typ_lower : lngen.

Lemma fvar_in_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_exp_lower : lngen.

(* begin hide *)

Lemma ftvar_in_typ_open_typ_wrt_typ_rec_upper_mutual :
(forall A1 A2 n1,
  ftvar_in_typ (open_typ_wrt_typ_rec n1 A2 A1) [<=] ftvar_in_typ A2 `union` ftvar_in_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_typ_open_typ_wrt_typ_rec_upper :
forall A1 A2 n1,
  ftvar_in_typ (open_typ_wrt_typ_rec n1 A2 A1) [<=] ftvar_in_typ A2 `union` ftvar_in_typ A1.
Proof.
pose proof ftvar_in_typ_open_typ_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_open_typ_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bid_open_bid_wrt_bid_rec_upper_mutual :
(forall D1 D2 n1,
  ftvar_in_bid (open_bid_wrt_bid_rec n1 D2 D1) [<=] ftvar_in_bid D2 `union` ftvar_in_bid D1).
Proof.
apply_mutual_ind bid_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bid_open_bid_wrt_bid_rec_upper :
forall D1 D2 n1,
  ftvar_in_bid (open_bid_wrt_bid_rec n1 D2 D1) [<=] ftvar_in_bid D2 `union` ftvar_in_bid D1.
Proof.
pose proof ftvar_in_bid_open_bid_wrt_bid_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bid_open_bid_wrt_bid_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_utyp_open_utyp_wrt_utyp_rec_upper_mutual :
(forall F1 F2 n1,
  ftvar_in_utyp (open_utyp_wrt_utyp_rec n1 F2 F1) [<=] ftvar_in_utyp F2 `union` ftvar_in_utyp F1).
Proof.
apply_mutual_ind utyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_utyp_open_utyp_wrt_utyp_rec_upper :
forall F1 F2 n1,
  ftvar_in_utyp (open_utyp_wrt_utyp_rec n1 F2 F1) [<=] ftvar_in_utyp F2 `union` ftvar_in_utyp F1.
Proof.
pose proof ftvar_in_utyp_open_utyp_wrt_utyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_utyp_open_utyp_wrt_utyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_ctyp_open_ctyp_wrt_ctyp_rec_upper_mutual :
(forall K1 K2 n1,
  ftvar_in_ctyp (open_ctyp_wrt_ctyp_rec n1 K2 K1) [<=] ftvar_in_ctyp K2 `union` ftvar_in_ctyp K1).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_ctyp_open_ctyp_wrt_ctyp_rec_upper :
forall K1 K2 n1,
  ftvar_in_ctyp (open_ctyp_wrt_ctyp_rec n1 K2 K1) [<=] ftvar_in_ctyp K2 `union` ftvar_in_ctyp K1.
Proof.
pose proof ftvar_in_ctyp_open_ctyp_wrt_ctyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_ctyp_open_ctyp_wrt_ctyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_skel_open_skel_wrt_skel_rec_upper_mutual :
(forall R1 R2 n1,
  ftvar_in_skel (open_skel_wrt_skel_rec n1 R2 R1) [<=] ftvar_in_skel R2 `union` ftvar_in_skel R1).
Proof.
apply_mutual_ind skel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_skel_open_skel_wrt_skel_rec_upper :
forall R1 R2 n1,
  ftvar_in_skel (open_skel_wrt_skel_rec n1 R2 R1) [<=] ftvar_in_skel R2 `union` ftvar_in_skel R1.
Proof.
pose proof ftvar_in_skel_open_skel_wrt_skel_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_skel_open_skel_wrt_skel_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_dbind_open_dbind_wrt_typ_rec_upper_mutual :
(forall db1 A1 n1,
  ftvar_in_dbind (open_dbind_wrt_typ_rec n1 A1 db1) [<=] ftvar_in_typ A1 `union` ftvar_in_dbind db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_dbind_open_dbind_wrt_typ_rec_upper :
forall db1 A1 n1,
  ftvar_in_dbind (open_dbind_wrt_typ_rec n1 A1 db1) [<=] ftvar_in_typ A1 `union` ftvar_in_dbind db1.
Proof.
pose proof ftvar_in_dbind_open_dbind_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_dbind_open_dbind_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_typ_rec_upper_mutual :
(forall e1 A1 n1,
  ftvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] ftvar_in_typ A1 `union` ftvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_typ_rec_upper :
forall e1 A1 n1,
  ftvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] ftvar_in_typ A1 `union` ftvar_in_exp e1.
Proof.
pose proof ftvar_in_exp_open_exp_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_typ_rec_upper : lngen.

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

Lemma fvar_in_exp_open_exp_wrt_typ_rec_upper_mutual :
(forall e1 A1 n1,
  fvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] fvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_typ_rec_upper :
forall e1 A1 n1,
  fvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] fvar_in_exp e1.
Proof.
pose proof fvar_in_exp_open_exp_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_typ_rec_upper : lngen.

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

Lemma ftvar_in_typ_open_typ_wrt_typ_upper :
forall A1 A2,
  ftvar_in_typ (open_typ_wrt_typ A1 A2) [<=] ftvar_in_typ A2 `union` ftvar_in_typ A1.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_typ_open_typ_wrt_typ_upper : lngen.

Lemma ftvar_in_bid_open_bid_wrt_bid_upper :
forall D1 D2,
  ftvar_in_bid (open_bid_wrt_bid D1 D2) [<=] ftvar_in_bid D2 `union` ftvar_in_bid D1.
Proof.
unfold open_bid_wrt_bid; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_bid_open_bid_wrt_bid_upper : lngen.

Lemma ftvar_in_utyp_open_utyp_wrt_utyp_upper :
forall F1 F2,
  ftvar_in_utyp (open_utyp_wrt_utyp F1 F2) [<=] ftvar_in_utyp F2 `union` ftvar_in_utyp F1.
Proof.
unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_utyp_open_utyp_wrt_utyp_upper : lngen.

Lemma ftvar_in_ctyp_open_ctyp_wrt_ctyp_upper :
forall K1 K2,
  ftvar_in_ctyp (open_ctyp_wrt_ctyp K1 K2) [<=] ftvar_in_ctyp K2 `union` ftvar_in_ctyp K1.
Proof.
unfold open_ctyp_wrt_ctyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_ctyp_open_ctyp_wrt_ctyp_upper : lngen.

Lemma ftvar_in_skel_open_skel_wrt_skel_upper :
forall R1 R2,
  ftvar_in_skel (open_skel_wrt_skel R1 R2) [<=] ftvar_in_skel R2 `union` ftvar_in_skel R1.
Proof.
unfold open_skel_wrt_skel; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_skel_open_skel_wrt_skel_upper : lngen.

Lemma ftvar_in_dbind_open_dbind_wrt_typ_upper :
forall db1 A1,
  ftvar_in_dbind (open_dbind_wrt_typ db1 A1) [<=] ftvar_in_typ A1 `union` ftvar_in_dbind db1.
Proof.
unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_dbind_open_dbind_wrt_typ_upper : lngen.

Lemma ftvar_in_exp_open_exp_wrt_typ_upper :
forall e1 A1,
  ftvar_in_exp (open_exp_wrt_typ e1 A1) [<=] ftvar_in_typ A1 `union` ftvar_in_exp e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_typ_upper : lngen.

Lemma ftvar_in_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  ftvar_in_exp (open_exp_wrt_exp e1 e2) [<=] ftvar_in_exp e2 `union` ftvar_in_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_exp_upper : lngen.

Lemma fvar_in_exp_open_exp_wrt_typ_upper :
forall e1 A1,
  fvar_in_exp (open_exp_wrt_typ e1 A1) [<=] fvar_in_exp e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_typ_upper : lngen.

Lemma fvar_in_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  fvar_in_exp (open_exp_wrt_exp e1 e2) [<=] fvar_in_exp e2 `union` fvar_in_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_exp_upper : lngen.

(* begin hide *)

Lemma ftvar_in_typ_subst_typ_in_typ_fresh_mutual :
(forall A1 A2 X1,
  X1 `notin` ftvar_in_typ A1 ->
  ftvar_in_typ (subst_typ_in_typ A2 X1 A1) [=] ftvar_in_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_typ_subst_typ_in_typ_fresh :
forall A1 A2 X1,
  X1 `notin` ftvar_in_typ A1 ->
  ftvar_in_typ (subst_typ_in_typ A2 X1 A1) [=] ftvar_in_typ A1.
Proof.
pose proof ftvar_in_typ_subst_typ_in_typ_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_subst_typ_in_typ_fresh : lngen.
#[export] Hint Rewrite ftvar_in_typ_subst_typ_in_typ_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_bid_subst_bid_in_bid_fresh_mutual :
(forall D1 D2 Xd1,
  Xd1 `notin` ftvar_in_bid D1 ->
  ftvar_in_bid (subst_bid_in_bid D2 Xd1 D1) [=] ftvar_in_bid D1).
Proof.
apply_mutual_ind bid_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_bid_subst_bid_in_bid_fresh :
forall D1 D2 Xd1,
  Xd1 `notin` ftvar_in_bid D1 ->
  ftvar_in_bid (subst_bid_in_bid D2 Xd1 D1) [=] ftvar_in_bid D1.
Proof.
pose proof ftvar_in_bid_subst_bid_in_bid_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bid_subst_bid_in_bid_fresh : lngen.
#[export] Hint Rewrite ftvar_in_bid_subst_bid_in_bid_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_utyp_subst_utyp_in_utyp_fresh_mutual :
(forall F1 F2 Xf1,
  Xf1 `notin` ftvar_in_utyp F1 ->
  ftvar_in_utyp (subst_utyp_in_utyp F2 Xf1 F1) [=] ftvar_in_utyp F1).
Proof.
apply_mutual_ind utyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_utyp_subst_utyp_in_utyp_fresh :
forall F1 F2 Xf1,
  Xf1 `notin` ftvar_in_utyp F1 ->
  ftvar_in_utyp (subst_utyp_in_utyp F2 Xf1 F1) [=] ftvar_in_utyp F1.
Proof.
pose proof ftvar_in_utyp_subst_utyp_in_utyp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_utyp_subst_utyp_in_utyp_fresh : lngen.
#[export] Hint Rewrite ftvar_in_utyp_subst_utyp_in_utyp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_ctyp_subst_ctyp_in_ctyp_fresh_mutual :
(forall K1 K2 U1,
  U1 `notin` ftvar_in_ctyp K1 ->
  ftvar_in_ctyp (subst_ctyp_in_ctyp K2 U1 K1) [=] ftvar_in_ctyp K1).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_ctyp_subst_ctyp_in_ctyp_fresh :
forall K1 K2 U1,
  U1 `notin` ftvar_in_ctyp K1 ->
  ftvar_in_ctyp (subst_ctyp_in_ctyp K2 U1 K1) [=] ftvar_in_ctyp K1.
Proof.
pose proof ftvar_in_ctyp_subst_ctyp_in_ctyp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_ctyp_subst_ctyp_in_ctyp_fresh : lngen.
#[export] Hint Rewrite ftvar_in_ctyp_subst_ctyp_in_ctyp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_skel_subst_skel_in_skel_fresh_mutual :
(forall R1 R2 Xr1,
  Xr1 `notin` ftvar_in_skel R1 ->
  ftvar_in_skel (subst_skel_in_skel R2 Xr1 R1) [=] ftvar_in_skel R1).
Proof.
apply_mutual_ind skel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_skel_subst_skel_in_skel_fresh :
forall R1 R2 Xr1,
  Xr1 `notin` ftvar_in_skel R1 ->
  ftvar_in_skel (subst_skel_in_skel R2 Xr1 R1) [=] ftvar_in_skel R1.
Proof.
pose proof ftvar_in_skel_subst_skel_in_skel_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_skel_subst_skel_in_skel_fresh : lngen.
#[export] Hint Rewrite ftvar_in_skel_subst_skel_in_skel_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_dbind_subst_typ_in_dbind_fresh_mutual :
(forall db1 A1 X1,
  X1 `notin` ftvar_in_dbind db1 ->
  ftvar_in_dbind (subst_typ_in_dbind A1 X1 db1) [=] ftvar_in_dbind db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_dbind_subst_typ_in_dbind_fresh :
forall db1 A1 X1,
  X1 `notin` ftvar_in_dbind db1 ->
  ftvar_in_dbind (subst_typ_in_dbind A1 X1 db1) [=] ftvar_in_dbind db1.
Proof.
pose proof ftvar_in_dbind_subst_typ_in_dbind_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_dbind_subst_typ_in_dbind_fresh : lngen.
#[export] Hint Rewrite ftvar_in_dbind_subst_typ_in_dbind_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_typ_in_exp_fresh_mutual :
(forall e1 A1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  ftvar_in_exp (subst_typ_in_exp A1 X1 e1) [=] ftvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_typ_in_exp_fresh :
forall e1 A1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  ftvar_in_exp (subst_typ_in_exp A1 X1 e1) [=] ftvar_in_exp e1.
Proof.
pose proof ftvar_in_exp_subst_typ_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_typ_in_exp_fresh : lngen.
#[export] Hint Rewrite ftvar_in_exp_subst_typ_in_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_fresh_mutual :
(forall e1 A1 X1,
  fvar_in_exp (subst_typ_in_exp A1 X1 e1) [=] fvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_fresh :
forall e1 A1 X1,
  fvar_in_exp (subst_typ_in_exp A1 X1 e1) [=] fvar_in_exp e1.
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

Lemma ftvar_in_typ_subst_typ_in_typ_lower_mutual :
(forall A1 A2 X1,
  remove X1 (ftvar_in_typ A1) [<=] ftvar_in_typ (subst_typ_in_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_typ_subst_typ_in_typ_lower :
forall A1 A2 X1,
  remove X1 (ftvar_in_typ A1) [<=] ftvar_in_typ (subst_typ_in_typ A2 X1 A1).
Proof.
pose proof ftvar_in_typ_subst_typ_in_typ_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_subst_typ_in_typ_lower : lngen.

(* begin hide *)

Lemma ftvar_in_bid_subst_bid_in_bid_lower_mutual :
(forall D1 D2 Xd1,
  remove Xd1 (ftvar_in_bid D1) [<=] ftvar_in_bid (subst_bid_in_bid D2 Xd1 D1)).
Proof.
apply_mutual_ind bid_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_bid_subst_bid_in_bid_lower :
forall D1 D2 Xd1,
  remove Xd1 (ftvar_in_bid D1) [<=] ftvar_in_bid (subst_bid_in_bid D2 Xd1 D1).
Proof.
pose proof ftvar_in_bid_subst_bid_in_bid_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bid_subst_bid_in_bid_lower : lngen.

(* begin hide *)

Lemma ftvar_in_utyp_subst_utyp_in_utyp_lower_mutual :
(forall F1 F2 Xf1,
  remove Xf1 (ftvar_in_utyp F1) [<=] ftvar_in_utyp (subst_utyp_in_utyp F2 Xf1 F1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_utyp_subst_utyp_in_utyp_lower :
forall F1 F2 Xf1,
  remove Xf1 (ftvar_in_utyp F1) [<=] ftvar_in_utyp (subst_utyp_in_utyp F2 Xf1 F1).
Proof.
pose proof ftvar_in_utyp_subst_utyp_in_utyp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_utyp_subst_utyp_in_utyp_lower : lngen.

(* begin hide *)

Lemma ftvar_in_ctyp_subst_ctyp_in_ctyp_lower_mutual :
(forall K1 K2 U1,
  remove U1 (ftvar_in_ctyp K1) [<=] ftvar_in_ctyp (subst_ctyp_in_ctyp K2 U1 K1)).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_ctyp_subst_ctyp_in_ctyp_lower :
forall K1 K2 U1,
  remove U1 (ftvar_in_ctyp K1) [<=] ftvar_in_ctyp (subst_ctyp_in_ctyp K2 U1 K1).
Proof.
pose proof ftvar_in_ctyp_subst_ctyp_in_ctyp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_ctyp_subst_ctyp_in_ctyp_lower : lngen.

(* begin hide *)

Lemma ftvar_in_skel_subst_skel_in_skel_lower_mutual :
(forall R1 R2 Xr1,
  remove Xr1 (ftvar_in_skel R1) [<=] ftvar_in_skel (subst_skel_in_skel R2 Xr1 R1)).
Proof.
apply_mutual_ind skel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_skel_subst_skel_in_skel_lower :
forall R1 R2 Xr1,
  remove Xr1 (ftvar_in_skel R1) [<=] ftvar_in_skel (subst_skel_in_skel R2 Xr1 R1).
Proof.
pose proof ftvar_in_skel_subst_skel_in_skel_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_skel_subst_skel_in_skel_lower : lngen.

(* begin hide *)

Lemma ftvar_in_dbind_subst_typ_in_dbind_lower_mutual :
(forall db1 A1 X1,
  remove X1 (ftvar_in_dbind db1) [<=] ftvar_in_dbind (subst_typ_in_dbind A1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_dbind_subst_typ_in_dbind_lower :
forall db1 A1 X1,
  remove X1 (ftvar_in_dbind db1) [<=] ftvar_in_dbind (subst_typ_in_dbind A1 X1 db1).
Proof.
pose proof ftvar_in_dbind_subst_typ_in_dbind_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_dbind_subst_typ_in_dbind_lower : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_typ_in_exp_lower_mutual :
(forall e1 A1 X1,
  remove X1 (ftvar_in_exp e1) [<=] ftvar_in_exp (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_typ_in_exp_lower :
forall e1 A1 X1,
  remove X1 (ftvar_in_exp e1) [<=] ftvar_in_exp (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof ftvar_in_exp_subst_typ_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_typ_in_exp_lower : lngen.

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

Lemma fvar_in_exp_subst_typ_in_exp_lower_mutual :
(forall e1 A1 X1,
  fvar_in_exp e1 [<=] fvar_in_exp (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_exp_subst_typ_in_exp_lower :
forall e1 A1 X1,
  fvar_in_exp e1 [<=] fvar_in_exp (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof fvar_in_exp_subst_typ_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_typ_in_exp_lower : lngen.

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

Lemma ftvar_in_typ_subst_typ_in_typ_notin_mutual :
(forall A1 A2 X1 X2,
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_typ A2 ->
  X2 `notin` ftvar_in_typ (subst_typ_in_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_typ_subst_typ_in_typ_notin :
forall A1 A2 X1 X2,
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_typ A2 ->
  X2 `notin` ftvar_in_typ (subst_typ_in_typ A2 X1 A1).
Proof.
pose proof ftvar_in_typ_subst_typ_in_typ_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_subst_typ_in_typ_notin : lngen.

(* begin hide *)

Lemma ftvar_in_bid_subst_bid_in_bid_notin_mutual :
(forall D1 D2 Xd1 Xd2,
  Xd2 `notin` ftvar_in_bid D1 ->
  Xd2 `notin` ftvar_in_bid D2 ->
  Xd2 `notin` ftvar_in_bid (subst_bid_in_bid D2 Xd1 D1)).
Proof.
apply_mutual_ind bid_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_bid_subst_bid_in_bid_notin :
forall D1 D2 Xd1 Xd2,
  Xd2 `notin` ftvar_in_bid D1 ->
  Xd2 `notin` ftvar_in_bid D2 ->
  Xd2 `notin` ftvar_in_bid (subst_bid_in_bid D2 Xd1 D1).
Proof.
pose proof ftvar_in_bid_subst_bid_in_bid_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bid_subst_bid_in_bid_notin : lngen.

(* begin hide *)

Lemma ftvar_in_utyp_subst_utyp_in_utyp_notin_mutual :
(forall F1 F2 Xf1 Xf2,
  Xf2 `notin` ftvar_in_utyp F1 ->
  Xf2 `notin` ftvar_in_utyp F2 ->
  Xf2 `notin` ftvar_in_utyp (subst_utyp_in_utyp F2 Xf1 F1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_utyp_subst_utyp_in_utyp_notin :
forall F1 F2 Xf1 Xf2,
  Xf2 `notin` ftvar_in_utyp F1 ->
  Xf2 `notin` ftvar_in_utyp F2 ->
  Xf2 `notin` ftvar_in_utyp (subst_utyp_in_utyp F2 Xf1 F1).
Proof.
pose proof ftvar_in_utyp_subst_utyp_in_utyp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_utyp_subst_utyp_in_utyp_notin : lngen.

(* begin hide *)

Lemma ftvar_in_ctyp_subst_ctyp_in_ctyp_notin_mutual :
(forall K1 K2 U1 U2,
  U2 `notin` ftvar_in_ctyp K1 ->
  U2 `notin` ftvar_in_ctyp K2 ->
  U2 `notin` ftvar_in_ctyp (subst_ctyp_in_ctyp K2 U1 K1)).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_ctyp_subst_ctyp_in_ctyp_notin :
forall K1 K2 U1 U2,
  U2 `notin` ftvar_in_ctyp K1 ->
  U2 `notin` ftvar_in_ctyp K2 ->
  U2 `notin` ftvar_in_ctyp (subst_ctyp_in_ctyp K2 U1 K1).
Proof.
pose proof ftvar_in_ctyp_subst_ctyp_in_ctyp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_ctyp_subst_ctyp_in_ctyp_notin : lngen.

(* begin hide *)

Lemma ftvar_in_skel_subst_skel_in_skel_notin_mutual :
(forall R1 R2 Xr1 Xr2,
  Xr2 `notin` ftvar_in_skel R1 ->
  Xr2 `notin` ftvar_in_skel R2 ->
  Xr2 `notin` ftvar_in_skel (subst_skel_in_skel R2 Xr1 R1)).
Proof.
apply_mutual_ind skel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_skel_subst_skel_in_skel_notin :
forall R1 R2 Xr1 Xr2,
  Xr2 `notin` ftvar_in_skel R1 ->
  Xr2 `notin` ftvar_in_skel R2 ->
  Xr2 `notin` ftvar_in_skel (subst_skel_in_skel R2 Xr1 R1).
Proof.
pose proof ftvar_in_skel_subst_skel_in_skel_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_skel_subst_skel_in_skel_notin : lngen.

(* begin hide *)

Lemma ftvar_in_dbind_subst_typ_in_dbind_notin_mutual :
(forall db1 A1 X1 X2,
  X2 `notin` ftvar_in_dbind db1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_dbind (subst_typ_in_dbind A1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_dbind_subst_typ_in_dbind_notin :
forall db1 A1 X1 X2,
  X2 `notin` ftvar_in_dbind db1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_dbind (subst_typ_in_dbind A1 X1 db1).
Proof.
pose proof ftvar_in_dbind_subst_typ_in_dbind_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_dbind_subst_typ_in_dbind_notin : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_typ_in_exp_notin_mutual :
(forall e1 A1 X1 X2,
  X2 `notin` ftvar_in_exp e1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_exp (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_typ_in_exp_notin :
forall e1 A1 X1 X2,
  X2 `notin` ftvar_in_exp e1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 `notin` ftvar_in_exp (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof ftvar_in_exp_subst_typ_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_typ_in_exp_notin : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_notin_mutual :
(forall e1 e2 x1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_notin :
forall e1 e2 x1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof ftvar_in_exp_subst_exp_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_exp_in_exp_notin : lngen.

(* begin hide *)

Lemma fvar_in_exp_subst_typ_in_exp_notin_mutual :
(forall e1 A1 X1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_exp_subst_typ_in_exp_notin :
forall e1 A1 X1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof fvar_in_exp_subst_typ_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_typ_in_exp_notin : lngen.

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

Lemma ftvar_in_typ_subst_typ_in_typ_upper_mutual :
(forall A1 A2 X1,
  ftvar_in_typ (subst_typ_in_typ A2 X1 A1) [<=] ftvar_in_typ A2 `union` remove X1 (ftvar_in_typ A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_typ_subst_typ_in_typ_upper :
forall A1 A2 X1,
  ftvar_in_typ (subst_typ_in_typ A2 X1 A1) [<=] ftvar_in_typ A2 `union` remove X1 (ftvar_in_typ A1).
Proof.
pose proof ftvar_in_typ_subst_typ_in_typ_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_typ_subst_typ_in_typ_upper : lngen.

(* begin hide *)

Lemma ftvar_in_bid_subst_bid_in_bid_upper_mutual :
(forall D1 D2 Xd1,
  ftvar_in_bid (subst_bid_in_bid D2 Xd1 D1) [<=] ftvar_in_bid D2 `union` remove Xd1 (ftvar_in_bid D1)).
Proof.
apply_mutual_ind bid_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_bid_subst_bid_in_bid_upper :
forall D1 D2 Xd1,
  ftvar_in_bid (subst_bid_in_bid D2 Xd1 D1) [<=] ftvar_in_bid D2 `union` remove Xd1 (ftvar_in_bid D1).
Proof.
pose proof ftvar_in_bid_subst_bid_in_bid_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bid_subst_bid_in_bid_upper : lngen.

(* begin hide *)

Lemma ftvar_in_utyp_subst_utyp_in_utyp_upper_mutual :
(forall F1 F2 Xf1,
  ftvar_in_utyp (subst_utyp_in_utyp F2 Xf1 F1) [<=] ftvar_in_utyp F2 `union` remove Xf1 (ftvar_in_utyp F1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_utyp_subst_utyp_in_utyp_upper :
forall F1 F2 Xf1,
  ftvar_in_utyp (subst_utyp_in_utyp F2 Xf1 F1) [<=] ftvar_in_utyp F2 `union` remove Xf1 (ftvar_in_utyp F1).
Proof.
pose proof ftvar_in_utyp_subst_utyp_in_utyp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_utyp_subst_utyp_in_utyp_upper : lngen.

(* begin hide *)

Lemma ftvar_in_ctyp_subst_ctyp_in_ctyp_upper_mutual :
(forall K1 K2 U1,
  ftvar_in_ctyp (subst_ctyp_in_ctyp K2 U1 K1) [<=] ftvar_in_ctyp K2 `union` remove U1 (ftvar_in_ctyp K1)).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_ctyp_subst_ctyp_in_ctyp_upper :
forall K1 K2 U1,
  ftvar_in_ctyp (subst_ctyp_in_ctyp K2 U1 K1) [<=] ftvar_in_ctyp K2 `union` remove U1 (ftvar_in_ctyp K1).
Proof.
pose proof ftvar_in_ctyp_subst_ctyp_in_ctyp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_ctyp_subst_ctyp_in_ctyp_upper : lngen.

(* begin hide *)

Lemma ftvar_in_skel_subst_skel_in_skel_upper_mutual :
(forall R1 R2 Xr1,
  ftvar_in_skel (subst_skel_in_skel R2 Xr1 R1) [<=] ftvar_in_skel R2 `union` remove Xr1 (ftvar_in_skel R1)).
Proof.
apply_mutual_ind skel_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_skel_subst_skel_in_skel_upper :
forall R1 R2 Xr1,
  ftvar_in_skel (subst_skel_in_skel R2 Xr1 R1) [<=] ftvar_in_skel R2 `union` remove Xr1 (ftvar_in_skel R1).
Proof.
pose proof ftvar_in_skel_subst_skel_in_skel_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_skel_subst_skel_in_skel_upper : lngen.

(* begin hide *)

Lemma ftvar_in_dbind_subst_typ_in_dbind_upper_mutual :
(forall db1 A1 X1,
  ftvar_in_dbind (subst_typ_in_dbind A1 X1 db1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_dbind db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_dbind_subst_typ_in_dbind_upper :
forall db1 A1 X1,
  ftvar_in_dbind (subst_typ_in_dbind A1 X1 db1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_dbind db1).
Proof.
pose proof ftvar_in_dbind_subst_typ_in_dbind_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_dbind_subst_typ_in_dbind_upper : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_typ_in_exp_upper_mutual :
(forall e1 A1 X1,
  ftvar_in_exp (subst_typ_in_exp A1 X1 e1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_typ_in_exp_upper :
forall e1 A1 X1,
  ftvar_in_exp (subst_typ_in_exp A1 X1 e1) [<=] ftvar_in_typ A1 `union` remove X1 (ftvar_in_exp e1).
Proof.
pose proof ftvar_in_exp_subst_typ_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_typ_in_exp_upper : lngen.

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

Lemma fvar_in_exp_subst_typ_in_exp_upper_mutual :
(forall e1 A1 X1,
  fvar_in_exp (subst_typ_in_exp A1 X1 e1) [<=] fvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_exp_subst_typ_in_exp_upper :
forall e1 A1 X1,
  fvar_in_exp (subst_typ_in_exp A1 X1 e1) [<=] fvar_in_exp e1.
Proof.
pose proof fvar_in_exp_subst_typ_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_typ_in_exp_upper : lngen.

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

Lemma subst_typ_in_typ_close_typ_wrt_typ_rec_mutual :
(forall A2 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_typ A1 X1 (close_typ_wrt_typ_rec n1 X2 A2) = close_typ_wrt_typ_rec n1 X2 (subst_typ_in_typ A1 X1 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_close_typ_wrt_typ_rec :
forall A2 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_typ A1 X1 (close_typ_wrt_typ_rec n1 X2 A2) = close_typ_wrt_typ_rec n1 X2 (subst_typ_in_typ A1 X1 A2).
Proof.
pose proof subst_typ_in_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_close_typ_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_bid_in_bid_close_bid_wrt_bid_rec_mutual :
(forall D2 D1 Xd1 Xd2 n1,
  degree_bid_wrt_bid n1 D1 ->
  Xd1 <> Xd2 ->
  Xd2 `notin` ftvar_in_bid D1 ->
  subst_bid_in_bid D1 Xd1 (close_bid_wrt_bid_rec n1 Xd2 D2) = close_bid_wrt_bid_rec n1 Xd2 (subst_bid_in_bid D1 Xd1 D2)).
Proof.
apply_mutual_ind bid_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_bid_in_bid_close_bid_wrt_bid_rec :
forall D2 D1 Xd1 Xd2 n1,
  degree_bid_wrt_bid n1 D1 ->
  Xd1 <> Xd2 ->
  Xd2 `notin` ftvar_in_bid D1 ->
  subst_bid_in_bid D1 Xd1 (close_bid_wrt_bid_rec n1 Xd2 D2) = close_bid_wrt_bid_rec n1 Xd2 (subst_bid_in_bid D1 Xd1 D2).
Proof.
pose proof subst_bid_in_bid_close_bid_wrt_bid_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bid_in_bid_close_bid_wrt_bid_rec : lngen.

(* begin hide *)

Lemma subst_utyp_in_utyp_close_utyp_wrt_utyp_rec_mutual :
(forall F2 F1 Xf1 Xf2 n1,
  degree_utyp_wrt_utyp n1 F1 ->
  Xf1 <> Xf2 ->
  Xf2 `notin` ftvar_in_utyp F1 ->
  subst_utyp_in_utyp F1 Xf1 (close_utyp_wrt_utyp_rec n1 Xf2 F2) = close_utyp_wrt_utyp_rec n1 Xf2 (subst_utyp_in_utyp F1 Xf1 F2)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_utyp_in_utyp_close_utyp_wrt_utyp_rec :
forall F2 F1 Xf1 Xf2 n1,
  degree_utyp_wrt_utyp n1 F1 ->
  Xf1 <> Xf2 ->
  Xf2 `notin` ftvar_in_utyp F1 ->
  subst_utyp_in_utyp F1 Xf1 (close_utyp_wrt_utyp_rec n1 Xf2 F2) = close_utyp_wrt_utyp_rec n1 Xf2 (subst_utyp_in_utyp F1 Xf1 F2).
Proof.
pose proof subst_utyp_in_utyp_close_utyp_wrt_utyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_close_utyp_wrt_utyp_rec : lngen.

(* begin hide *)

Lemma subst_ctyp_in_ctyp_close_ctyp_wrt_ctyp_rec_mutual :
(forall K2 K1 U1 U2 n1,
  degree_ctyp_wrt_ctyp n1 K1 ->
  U1 <> U2 ->
  U2 `notin` ftvar_in_ctyp K1 ->
  subst_ctyp_in_ctyp K1 U1 (close_ctyp_wrt_ctyp_rec n1 U2 K2) = close_ctyp_wrt_ctyp_rec n1 U2 (subst_ctyp_in_ctyp K1 U1 K2)).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ctyp_in_ctyp_close_ctyp_wrt_ctyp_rec :
forall K2 K1 U1 U2 n1,
  degree_ctyp_wrt_ctyp n1 K1 ->
  U1 <> U2 ->
  U2 `notin` ftvar_in_ctyp K1 ->
  subst_ctyp_in_ctyp K1 U1 (close_ctyp_wrt_ctyp_rec n1 U2 K2) = close_ctyp_wrt_ctyp_rec n1 U2 (subst_ctyp_in_ctyp K1 U1 K2).
Proof.
pose proof subst_ctyp_in_ctyp_close_ctyp_wrt_ctyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ctyp_in_ctyp_close_ctyp_wrt_ctyp_rec : lngen.

(* begin hide *)

Lemma subst_skel_in_skel_close_skel_wrt_skel_rec_mutual :
(forall R2 R1 Xr1 Xr2 n1,
  degree_skel_wrt_skel n1 R1 ->
  Xr1 <> Xr2 ->
  Xr2 `notin` ftvar_in_skel R1 ->
  subst_skel_in_skel R1 Xr1 (close_skel_wrt_skel_rec n1 Xr2 R2) = close_skel_wrt_skel_rec n1 Xr2 (subst_skel_in_skel R1 Xr1 R2)).
Proof.
apply_mutual_ind skel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skel_in_skel_close_skel_wrt_skel_rec :
forall R2 R1 Xr1 Xr2 n1,
  degree_skel_wrt_skel n1 R1 ->
  Xr1 <> Xr2 ->
  Xr2 `notin` ftvar_in_skel R1 ->
  subst_skel_in_skel R1 Xr1 (close_skel_wrt_skel_rec n1 Xr2 R2) = close_skel_wrt_skel_rec n1 Xr2 (subst_skel_in_skel R1 Xr1 R2).
Proof.
pose proof subst_skel_in_skel_close_skel_wrt_skel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skel_in_skel_close_skel_wrt_skel_rec : lngen.

(* begin hide *)

Lemma subst_typ_in_dbind_close_dbind_wrt_typ_rec_mutual :
(forall db1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_dbind A1 X1 (close_dbind_wrt_typ_rec n1 X2 db1) = close_dbind_wrt_typ_rec n1 X2 (subst_typ_in_dbind A1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_dbind_close_dbind_wrt_typ_rec :
forall db1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_dbind A1 X1 (close_dbind_wrt_typ_rec n1 X2 db1) = close_dbind_wrt_typ_rec n1 X2 (subst_typ_in_dbind A1 X1 db1).
Proof.
pose proof subst_typ_in_dbind_close_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_close_dbind_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_exp A1 X1 (close_exp_wrt_typ_rec n1 X2 e1) = close_exp_wrt_typ_rec n1 X2 (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_close_exp_wrt_typ_rec :
forall e1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_exp A1 X1 (close_exp_wrt_typ_rec n1 X2 e1) = close_exp_wrt_typ_rec n1 X2 (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof subst_typ_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 A1 x1 X1 n1,
  subst_typ_in_exp A1 x1 (close_exp_wrt_exp_rec n1 X1 e1) = close_exp_wrt_exp_rec n1 X1 (subst_typ_in_exp A1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_close_exp_wrt_exp_rec :
forall e1 A1 x1 X1 n1,
  subst_typ_in_exp A1 x1 (close_exp_wrt_exp_rec n1 X1 e1) = close_exp_wrt_exp_rec n1 X1 (subst_typ_in_exp A1 x1 e1).
Proof.
pose proof subst_typ_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_exp_rec : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_typ_rec_mutual :
(forall e2 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_exp e1 X1 (close_exp_wrt_typ_rec n1 x1 e2) = close_exp_wrt_typ_rec n1 x1 (subst_exp_in_exp e1 X1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_close_exp_wrt_typ_rec :
forall e2 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_exp e1 X1 (close_exp_wrt_typ_rec n1 x1 e2) = close_exp_wrt_typ_rec n1 x1 (subst_exp_in_exp e1 X1 e2).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_typ_rec : lngen.

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

Lemma subst_typ_in_typ_close_typ_wrt_typ :
forall A2 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_typ A1 X1 (close_typ_wrt_typ X2 A2) = close_typ_wrt_typ X2 (subst_typ_in_typ A1 X1 A2).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_close_typ_wrt_typ : lngen.

Lemma subst_bid_in_bid_close_bid_wrt_bid :
forall D2 D1 Xd1 Xd2,
  lc_bid D1 ->  Xd1 <> Xd2 ->
  Xd2 `notin` ftvar_in_bid D1 ->
  subst_bid_in_bid D1 Xd1 (close_bid_wrt_bid Xd2 D2) = close_bid_wrt_bid Xd2 (subst_bid_in_bid D1 Xd1 D2).
Proof.
unfold close_bid_wrt_bid; default_simp.
Qed.

#[export] Hint Resolve subst_bid_in_bid_close_bid_wrt_bid : lngen.

Lemma subst_utyp_in_utyp_close_utyp_wrt_utyp :
forall F2 F1 Xf1 Xf2,
  lc_utyp F1 ->  Xf1 <> Xf2 ->
  Xf2 `notin` ftvar_in_utyp F1 ->
  subst_utyp_in_utyp F1 Xf1 (close_utyp_wrt_utyp Xf2 F2) = close_utyp_wrt_utyp Xf2 (subst_utyp_in_utyp F1 Xf1 F2).
Proof.
unfold close_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_close_utyp_wrt_utyp : lngen.

Lemma subst_ctyp_in_ctyp_close_ctyp_wrt_ctyp :
forall K2 K1 U1 U2,
  lc_ctyp K1 ->  U1 <> U2 ->
  U2 `notin` ftvar_in_ctyp K1 ->
  subst_ctyp_in_ctyp K1 U1 (close_ctyp_wrt_ctyp U2 K2) = close_ctyp_wrt_ctyp U2 (subst_ctyp_in_ctyp K1 U1 K2).
Proof.
unfold close_ctyp_wrt_ctyp; default_simp.
Qed.

#[export] Hint Resolve subst_ctyp_in_ctyp_close_ctyp_wrt_ctyp : lngen.

Lemma subst_skel_in_skel_close_skel_wrt_skel :
forall R2 R1 Xr1 Xr2,
  lc_skel R1 ->  Xr1 <> Xr2 ->
  Xr2 `notin` ftvar_in_skel R1 ->
  subst_skel_in_skel R1 Xr1 (close_skel_wrt_skel Xr2 R2) = close_skel_wrt_skel Xr2 (subst_skel_in_skel R1 Xr1 R2).
Proof.
unfold close_skel_wrt_skel; default_simp.
Qed.

#[export] Hint Resolve subst_skel_in_skel_close_skel_wrt_skel : lngen.

Lemma subst_typ_in_dbind_close_dbind_wrt_typ :
forall db1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_dbind A1 X1 (close_dbind_wrt_typ X2 db1) = close_dbind_wrt_typ X2 (subst_typ_in_dbind A1 X1 db1).
Proof.
unfold close_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_close_dbind_wrt_typ : lngen.

Lemma subst_typ_in_exp_close_exp_wrt_typ :
forall e1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_typ A1 ->
  subst_typ_in_exp A1 X1 (close_exp_wrt_typ X2 e1) = close_exp_wrt_typ X2 (subst_typ_in_exp A1 X1 e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_typ : lngen.

Lemma subst_typ_in_exp_close_exp_wrt_exp :
forall e1 A1 x1 X1,
  lc_typ A1 ->  subst_typ_in_exp A1 x1 (close_exp_wrt_exp X1 e1) = close_exp_wrt_exp X1 (subst_typ_in_exp A1 x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_exp : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_typ :
forall e2 e1 X1 x1,
  lc_exp e1 ->  x1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_exp e1 X1 (close_exp_wrt_typ x1 e2) = close_exp_wrt_typ x1 (subst_exp_in_exp e1 X1 e2).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_typ : lngen.

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

Lemma subst_typ_in_typ_degree_typ_wrt_typ_mutual :
(forall A1 A2 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (subst_typ_in_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_degree_typ_wrt_typ :
forall A1 A2 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (subst_typ_in_typ A2 X1 A1).
Proof.
pose proof subst_typ_in_typ_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_degree_typ_wrt_typ : lngen.

(* begin hide *)

Lemma subst_bid_in_bid_degree_bid_wrt_bid_mutual :
(forall D1 D2 Xd1 n1,
  degree_bid_wrt_bid n1 D1 ->
  degree_bid_wrt_bid n1 D2 ->
  degree_bid_wrt_bid n1 (subst_bid_in_bid D2 Xd1 D1)).
Proof.
apply_mutual_ind bid_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_bid_in_bid_degree_bid_wrt_bid :
forall D1 D2 Xd1 n1,
  degree_bid_wrt_bid n1 D1 ->
  degree_bid_wrt_bid n1 D2 ->
  degree_bid_wrt_bid n1 (subst_bid_in_bid D2 Xd1 D1).
Proof.
pose proof subst_bid_in_bid_degree_bid_wrt_bid_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bid_in_bid_degree_bid_wrt_bid : lngen.

(* begin hide *)

Lemma subst_utyp_in_utyp_degree_utyp_wrt_utyp_mutual :
(forall F1 F2 Xf1 n1,
  degree_utyp_wrt_utyp n1 F1 ->
  degree_utyp_wrt_utyp n1 F2 ->
  degree_utyp_wrt_utyp n1 (subst_utyp_in_utyp F2 Xf1 F1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_utyp_in_utyp_degree_utyp_wrt_utyp :
forall F1 F2 Xf1 n1,
  degree_utyp_wrt_utyp n1 F1 ->
  degree_utyp_wrt_utyp n1 F2 ->
  degree_utyp_wrt_utyp n1 (subst_utyp_in_utyp F2 Xf1 F1).
Proof.
pose proof subst_utyp_in_utyp_degree_utyp_wrt_utyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_degree_utyp_wrt_utyp : lngen.

(* begin hide *)

Lemma subst_ctyp_in_ctyp_degree_ctyp_wrt_ctyp_mutual :
(forall K1 K2 U1 n1,
  degree_ctyp_wrt_ctyp n1 K1 ->
  degree_ctyp_wrt_ctyp n1 K2 ->
  degree_ctyp_wrt_ctyp n1 (subst_ctyp_in_ctyp K2 U1 K1)).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ctyp_in_ctyp_degree_ctyp_wrt_ctyp :
forall K1 K2 U1 n1,
  degree_ctyp_wrt_ctyp n1 K1 ->
  degree_ctyp_wrt_ctyp n1 K2 ->
  degree_ctyp_wrt_ctyp n1 (subst_ctyp_in_ctyp K2 U1 K1).
Proof.
pose proof subst_ctyp_in_ctyp_degree_ctyp_wrt_ctyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ctyp_in_ctyp_degree_ctyp_wrt_ctyp : lngen.

(* begin hide *)

Lemma subst_skel_in_skel_degree_skel_wrt_skel_mutual :
(forall R1 R2 Xr1 n1,
  degree_skel_wrt_skel n1 R1 ->
  degree_skel_wrt_skel n1 R2 ->
  degree_skel_wrt_skel n1 (subst_skel_in_skel R2 Xr1 R1)).
Proof.
apply_mutual_ind skel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skel_in_skel_degree_skel_wrt_skel :
forall R1 R2 Xr1 n1,
  degree_skel_wrt_skel n1 R1 ->
  degree_skel_wrt_skel n1 R2 ->
  degree_skel_wrt_skel n1 (subst_skel_in_skel R2 Xr1 R1).
Proof.
pose proof subst_skel_in_skel_degree_skel_wrt_skel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skel_in_skel_degree_skel_wrt_skel : lngen.

(* begin hide *)

Lemma subst_typ_in_dbind_degree_dbind_wrt_typ_mutual :
(forall db1 A1 X1 n1,
  degree_dbind_wrt_typ n1 db1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_dbind_wrt_typ n1 (subst_typ_in_dbind A1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_dbind_degree_dbind_wrt_typ :
forall db1 A1 X1 n1,
  degree_dbind_wrt_typ n1 db1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_dbind_wrt_typ n1 (subst_typ_in_dbind A1 X1 db1).
Proof.
pose proof subst_typ_in_dbind_degree_dbind_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_degree_dbind_wrt_typ : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_degree_exp_wrt_typ_mutual :
(forall e1 A1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_degree_exp_wrt_typ :
forall e1 A1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof subst_typ_in_exp_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_degree_exp_wrt_typ : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_degree_exp_wrt_exp_mutual :
(forall e1 A1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_degree_exp_wrt_exp :
forall e1 A1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof subst_typ_in_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_typ_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_typ :
forall e1 e2 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_degree_exp_wrt_typ : lngen.

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

Lemma subst_typ_in_typ_fresh_eq_mutual :
(forall A2 A1 X1,
  X1 `notin` ftvar_in_typ A2 ->
  subst_typ_in_typ A1 X1 A2 = A2).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_fresh_eq :
forall A2 A1 X1,
  X1 `notin` ftvar_in_typ A2 ->
  subst_typ_in_typ A1 X1 A2 = A2.
Proof.
pose proof subst_typ_in_typ_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_fresh_eq : lngen.
#[export] Hint Rewrite subst_typ_in_typ_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_bid_in_bid_fresh_eq_mutual :
(forall D2 D1 Xd1,
  Xd1 `notin` ftvar_in_bid D2 ->
  subst_bid_in_bid D1 Xd1 D2 = D2).
Proof.
apply_mutual_ind bid_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_bid_in_bid_fresh_eq :
forall D2 D1 Xd1,
  Xd1 `notin` ftvar_in_bid D2 ->
  subst_bid_in_bid D1 Xd1 D2 = D2.
Proof.
pose proof subst_bid_in_bid_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bid_in_bid_fresh_eq : lngen.
#[export] Hint Rewrite subst_bid_in_bid_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_utyp_in_utyp_fresh_eq_mutual :
(forall F2 F1 Xf1,
  Xf1 `notin` ftvar_in_utyp F2 ->
  subst_utyp_in_utyp F1 Xf1 F2 = F2).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_utyp_in_utyp_fresh_eq :
forall F2 F1 Xf1,
  Xf1 `notin` ftvar_in_utyp F2 ->
  subst_utyp_in_utyp F1 Xf1 F2 = F2.
Proof.
pose proof subst_utyp_in_utyp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_fresh_eq : lngen.
#[export] Hint Rewrite subst_utyp_in_utyp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_ctyp_in_ctyp_fresh_eq_mutual :
(forall K2 K1 U1,
  U1 `notin` ftvar_in_ctyp K2 ->
  subst_ctyp_in_ctyp K1 U1 K2 = K2).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ctyp_in_ctyp_fresh_eq :
forall K2 K1 U1,
  U1 `notin` ftvar_in_ctyp K2 ->
  subst_ctyp_in_ctyp K1 U1 K2 = K2.
Proof.
pose proof subst_ctyp_in_ctyp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ctyp_in_ctyp_fresh_eq : lngen.
#[export] Hint Rewrite subst_ctyp_in_ctyp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_skel_in_skel_fresh_eq_mutual :
(forall R2 R1 Xr1,
  Xr1 `notin` ftvar_in_skel R2 ->
  subst_skel_in_skel R1 Xr1 R2 = R2).
Proof.
apply_mutual_ind skel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skel_in_skel_fresh_eq :
forall R2 R1 Xr1,
  Xr1 `notin` ftvar_in_skel R2 ->
  subst_skel_in_skel R1 Xr1 R2 = R2.
Proof.
pose proof subst_skel_in_skel_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skel_in_skel_fresh_eq : lngen.
#[export] Hint Rewrite subst_skel_in_skel_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_dbind_fresh_eq_mutual :
(forall db1 A1 X1,
  X1 `notin` ftvar_in_dbind db1 ->
  subst_typ_in_dbind A1 X1 db1 = db1).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_dbind_fresh_eq :
forall db1 A1 X1,
  X1 `notin` ftvar_in_dbind db1 ->
  subst_typ_in_dbind A1 X1 db1 = db1.
Proof.
pose proof subst_typ_in_dbind_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_fresh_eq : lngen.
#[export] Hint Rewrite subst_typ_in_dbind_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_fresh_eq_mutual :
(forall e1 A1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_typ_in_exp A1 X1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_fresh_eq :
forall e1 A1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_typ_in_exp A1 X1 e1 = e1.
Proof.
pose proof subst_typ_in_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_fresh_eq : lngen.
#[export] Hint Rewrite subst_typ_in_exp_fresh_eq using solve [auto] : lngen.

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

Lemma subst_typ_in_typ_fresh_same_mutual :
(forall A2 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_typ (subst_typ_in_typ A1 X1 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_fresh_same :
forall A2 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_typ (subst_typ_in_typ A1 X1 A2).
Proof.
pose proof subst_typ_in_typ_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_fresh_same : lngen.

(* begin hide *)

Lemma subst_bid_in_bid_fresh_same_mutual :
(forall D2 D1 Xd1,
  Xd1 `notin` ftvar_in_bid D1 ->
  Xd1 `notin` ftvar_in_bid (subst_bid_in_bid D1 Xd1 D2)).
Proof.
apply_mutual_ind bid_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_bid_in_bid_fresh_same :
forall D2 D1 Xd1,
  Xd1 `notin` ftvar_in_bid D1 ->
  Xd1 `notin` ftvar_in_bid (subst_bid_in_bid D1 Xd1 D2).
Proof.
pose proof subst_bid_in_bid_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bid_in_bid_fresh_same : lngen.

(* begin hide *)

Lemma subst_utyp_in_utyp_fresh_same_mutual :
(forall F2 F1 Xf1,
  Xf1 `notin` ftvar_in_utyp F1 ->
  Xf1 `notin` ftvar_in_utyp (subst_utyp_in_utyp F1 Xf1 F2)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_utyp_in_utyp_fresh_same :
forall F2 F1 Xf1,
  Xf1 `notin` ftvar_in_utyp F1 ->
  Xf1 `notin` ftvar_in_utyp (subst_utyp_in_utyp F1 Xf1 F2).
Proof.
pose proof subst_utyp_in_utyp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_fresh_same : lngen.

(* begin hide *)

Lemma subst_ctyp_in_ctyp_fresh_same_mutual :
(forall K2 K1 U1,
  U1 `notin` ftvar_in_ctyp K1 ->
  U1 `notin` ftvar_in_ctyp (subst_ctyp_in_ctyp K1 U1 K2)).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ctyp_in_ctyp_fresh_same :
forall K2 K1 U1,
  U1 `notin` ftvar_in_ctyp K1 ->
  U1 `notin` ftvar_in_ctyp (subst_ctyp_in_ctyp K1 U1 K2).
Proof.
pose proof subst_ctyp_in_ctyp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ctyp_in_ctyp_fresh_same : lngen.

(* begin hide *)

Lemma subst_skel_in_skel_fresh_same_mutual :
(forall R2 R1 Xr1,
  Xr1 `notin` ftvar_in_skel R1 ->
  Xr1 `notin` ftvar_in_skel (subst_skel_in_skel R1 Xr1 R2)).
Proof.
apply_mutual_ind skel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skel_in_skel_fresh_same :
forall R2 R1 Xr1,
  Xr1 `notin` ftvar_in_skel R1 ->
  Xr1 `notin` ftvar_in_skel (subst_skel_in_skel R1 Xr1 R2).
Proof.
pose proof subst_skel_in_skel_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skel_in_skel_fresh_same : lngen.

(* begin hide *)

Lemma subst_typ_in_dbind_fresh_same_mutual :
(forall db1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_dbind (subst_typ_in_dbind A1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_dbind_fresh_same :
forall db1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_dbind (subst_typ_in_dbind A1 X1 db1).
Proof.
pose proof subst_typ_in_dbind_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_fresh_same : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_fresh_same_mutual :
(forall e1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_exp (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_fresh_same :
forall e1 A1 X1,
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_exp (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof subst_typ_in_exp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_fresh_same : lngen.

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

Lemma subst_typ_in_typ_fresh_mutual :
(forall A2 A1 X1 X2,
  X1 `notin` ftvar_in_typ A2 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_typ (subst_typ_in_typ A1 X2 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_fresh :
forall A2 A1 X1 X2,
  X1 `notin` ftvar_in_typ A2 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_typ (subst_typ_in_typ A1 X2 A2).
Proof.
pose proof subst_typ_in_typ_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_fresh : lngen.

(* begin hide *)

Lemma subst_bid_in_bid_fresh_mutual :
(forall D2 D1 Xd1 Xd2,
  Xd1 `notin` ftvar_in_bid D2 ->
  Xd1 `notin` ftvar_in_bid D1 ->
  Xd1 `notin` ftvar_in_bid (subst_bid_in_bid D1 Xd2 D2)).
Proof.
apply_mutual_ind bid_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_bid_in_bid_fresh :
forall D2 D1 Xd1 Xd2,
  Xd1 `notin` ftvar_in_bid D2 ->
  Xd1 `notin` ftvar_in_bid D1 ->
  Xd1 `notin` ftvar_in_bid (subst_bid_in_bid D1 Xd2 D2).
Proof.
pose proof subst_bid_in_bid_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bid_in_bid_fresh : lngen.

(* begin hide *)

Lemma subst_utyp_in_utyp_fresh_mutual :
(forall F2 F1 Xf1 Xf2,
  Xf1 `notin` ftvar_in_utyp F2 ->
  Xf1 `notin` ftvar_in_utyp F1 ->
  Xf1 `notin` ftvar_in_utyp (subst_utyp_in_utyp F1 Xf2 F2)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_utyp_in_utyp_fresh :
forall F2 F1 Xf1 Xf2,
  Xf1 `notin` ftvar_in_utyp F2 ->
  Xf1 `notin` ftvar_in_utyp F1 ->
  Xf1 `notin` ftvar_in_utyp (subst_utyp_in_utyp F1 Xf2 F2).
Proof.
pose proof subst_utyp_in_utyp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_fresh : lngen.

(* begin hide *)

Lemma subst_ctyp_in_ctyp_fresh_mutual :
(forall K2 K1 U1 U2,
  U1 `notin` ftvar_in_ctyp K2 ->
  U1 `notin` ftvar_in_ctyp K1 ->
  U1 `notin` ftvar_in_ctyp (subst_ctyp_in_ctyp K1 U2 K2)).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ctyp_in_ctyp_fresh :
forall K2 K1 U1 U2,
  U1 `notin` ftvar_in_ctyp K2 ->
  U1 `notin` ftvar_in_ctyp K1 ->
  U1 `notin` ftvar_in_ctyp (subst_ctyp_in_ctyp K1 U2 K2).
Proof.
pose proof subst_ctyp_in_ctyp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ctyp_in_ctyp_fresh : lngen.

(* begin hide *)

Lemma subst_skel_in_skel_fresh_mutual :
(forall R2 R1 Xr1 Xr2,
  Xr1 `notin` ftvar_in_skel R2 ->
  Xr1 `notin` ftvar_in_skel R1 ->
  Xr1 `notin` ftvar_in_skel (subst_skel_in_skel R1 Xr2 R2)).
Proof.
apply_mutual_ind skel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skel_in_skel_fresh :
forall R2 R1 Xr1 Xr2,
  Xr1 `notin` ftvar_in_skel R2 ->
  Xr1 `notin` ftvar_in_skel R1 ->
  Xr1 `notin` ftvar_in_skel (subst_skel_in_skel R1 Xr2 R2).
Proof.
pose proof subst_skel_in_skel_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skel_in_skel_fresh : lngen.

(* begin hide *)

Lemma subst_typ_in_dbind_fresh_mutual :
(forall db1 A1 X1 X2,
  X1 `notin` ftvar_in_dbind db1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_dbind (subst_typ_in_dbind A1 X2 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_dbind_fresh :
forall db1 A1 X1 X2,
  X1 `notin` ftvar_in_dbind db1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_dbind (subst_typ_in_dbind A1 X2 db1).
Proof.
pose proof subst_typ_in_dbind_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_fresh : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_fresh_mutual :
(forall e1 A1 X1 X2,
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_exp (subst_typ_in_exp A1 X2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_fresh :
forall e1 A1 X1 X2,
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_typ A1 ->
  X1 `notin` ftvar_in_exp (subst_typ_in_exp A1 X2 e1).
Proof.
pose proof subst_typ_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_fresh : lngen.

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

Lemma subst_typ_in_typ_lc_typ :
forall A1 A2 X1,
  lc_typ A1 ->
  lc_typ A2 ->
  lc_typ (subst_typ_in_typ A2 X1 A1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_lc_typ : lngen.

Lemma subst_bid_in_bid_lc_bid :
forall D1 D2 Xd1,
  lc_bid D1 ->
  lc_bid D2 ->
  lc_bid (subst_bid_in_bid D2 Xd1 D1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_bid_in_bid_lc_bid : lngen.

Lemma subst_utyp_in_utyp_lc_utyp :
forall F1 F2 Xf1,
  lc_utyp F1 ->
  lc_utyp F2 ->
  lc_utyp (subst_utyp_in_utyp F2 Xf1 F1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_lc_utyp : lngen.

Lemma subst_ctyp_in_ctyp_lc_ctyp :
forall K1 K2 U1,
  lc_ctyp K1 ->
  lc_ctyp K2 ->
  lc_ctyp (subst_ctyp_in_ctyp K2 U1 K1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_ctyp_in_ctyp_lc_ctyp : lngen.

Lemma subst_skel_in_skel_lc_skel :
forall R1 R2 Xr1,
  lc_skel R1 ->
  lc_skel R2 ->
  lc_skel (subst_skel_in_skel R2 Xr1 R1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_skel_in_skel_lc_skel : lngen.

Lemma subst_typ_in_dbind_lc_dbind :
forall db1 A1 X1,
  lc_dbind db1 ->
  lc_typ A1 ->
  lc_dbind (subst_typ_in_dbind A1 X1 db1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_lc_dbind : lngen.

Lemma subst_typ_in_exp_lc_exp :
forall e1 A1 X1,
  lc_exp e1 ->
  lc_typ A1 ->
  lc_exp (subst_typ_in_exp A1 X1 e1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_lc_exp : lngen.

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

Lemma subst_typ_in_typ_open_typ_wrt_typ_rec_mutual :
(forall A3 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_typ A1 X1 (open_typ_wrt_typ_rec n1 A2 A3) = open_typ_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_typ A1 X1 A3)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_typ_open_typ_wrt_typ_rec :
forall A3 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_typ A1 X1 (open_typ_wrt_typ_rec n1 A2 A3) = open_typ_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_typ A1 X1 A3).
Proof.
pose proof subst_typ_in_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_bid_in_bid_open_bid_wrt_bid_rec_mutual :
(forall D3 D1 D2 Xd1 n1,
  lc_bid D1 ->
  subst_bid_in_bid D1 Xd1 (open_bid_wrt_bid_rec n1 D2 D3) = open_bid_wrt_bid_rec n1 (subst_bid_in_bid D1 Xd1 D2) (subst_bid_in_bid D1 Xd1 D3)).
Proof.
apply_mutual_ind bid_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_bid_in_bid_open_bid_wrt_bid_rec :
forall D3 D1 D2 Xd1 n1,
  lc_bid D1 ->
  subst_bid_in_bid D1 Xd1 (open_bid_wrt_bid_rec n1 D2 D3) = open_bid_wrt_bid_rec n1 (subst_bid_in_bid D1 Xd1 D2) (subst_bid_in_bid D1 Xd1 D3).
Proof.
pose proof subst_bid_in_bid_open_bid_wrt_bid_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bid_in_bid_open_bid_wrt_bid_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_utyp_in_utyp_open_utyp_wrt_utyp_rec_mutual :
(forall F3 F1 F2 Xf1 n1,
  lc_utyp F1 ->
  subst_utyp_in_utyp F1 Xf1 (open_utyp_wrt_utyp_rec n1 F2 F3) = open_utyp_wrt_utyp_rec n1 (subst_utyp_in_utyp F1 Xf1 F2) (subst_utyp_in_utyp F1 Xf1 F3)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_utyp_in_utyp_open_utyp_wrt_utyp_rec :
forall F3 F1 F2 Xf1 n1,
  lc_utyp F1 ->
  subst_utyp_in_utyp F1 Xf1 (open_utyp_wrt_utyp_rec n1 F2 F3) = open_utyp_wrt_utyp_rec n1 (subst_utyp_in_utyp F1 Xf1 F2) (subst_utyp_in_utyp F1 Xf1 F3).
Proof.
pose proof subst_utyp_in_utyp_open_utyp_wrt_utyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_open_utyp_wrt_utyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ctyp_in_ctyp_open_ctyp_wrt_ctyp_rec_mutual :
(forall K3 K1 K2 U1 n1,
  lc_ctyp K1 ->
  subst_ctyp_in_ctyp K1 U1 (open_ctyp_wrt_ctyp_rec n1 K2 K3) = open_ctyp_wrt_ctyp_rec n1 (subst_ctyp_in_ctyp K1 U1 K2) (subst_ctyp_in_ctyp K1 U1 K3)).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ctyp_in_ctyp_open_ctyp_wrt_ctyp_rec :
forall K3 K1 K2 U1 n1,
  lc_ctyp K1 ->
  subst_ctyp_in_ctyp K1 U1 (open_ctyp_wrt_ctyp_rec n1 K2 K3) = open_ctyp_wrt_ctyp_rec n1 (subst_ctyp_in_ctyp K1 U1 K2) (subst_ctyp_in_ctyp K1 U1 K3).
Proof.
pose proof subst_ctyp_in_ctyp_open_ctyp_wrt_ctyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ctyp_in_ctyp_open_ctyp_wrt_ctyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_skel_in_skel_open_skel_wrt_skel_rec_mutual :
(forall R3 R1 R2 Xr1 n1,
  lc_skel R1 ->
  subst_skel_in_skel R1 Xr1 (open_skel_wrt_skel_rec n1 R2 R3) = open_skel_wrt_skel_rec n1 (subst_skel_in_skel R1 Xr1 R2) (subst_skel_in_skel R1 Xr1 R3)).
Proof.
apply_mutual_ind skel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_skel_in_skel_open_skel_wrt_skel_rec :
forall R3 R1 R2 Xr1 n1,
  lc_skel R1 ->
  subst_skel_in_skel R1 Xr1 (open_skel_wrt_skel_rec n1 R2 R3) = open_skel_wrt_skel_rec n1 (subst_skel_in_skel R1 Xr1 R2) (subst_skel_in_skel R1 Xr1 R3).
Proof.
pose proof subst_skel_in_skel_open_skel_wrt_skel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skel_in_skel_open_skel_wrt_skel_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_dbind_open_dbind_wrt_typ_rec_mutual :
(forall db1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_dbind A1 X1 (open_dbind_wrt_typ_rec n1 A2 db1) = open_dbind_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_dbind A1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_dbind_open_dbind_wrt_typ_rec :
forall db1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_dbind A1 X1 (open_dbind_wrt_typ_rec n1 A2 db1) = open_dbind_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_dbind A1 X1 db1).
Proof.
pose proof subst_typ_in_dbind_open_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_open_dbind_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_exp A1 X1 (open_exp_wrt_typ_rec n1 A2 e1) = open_exp_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_open_exp_wrt_typ_rec :
forall e1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_exp A1 X1 (open_exp_wrt_typ_rec n1 A2 e1) = open_exp_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof subst_typ_in_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_open_exp_wrt_exp_rec_mutual :
(forall e2 A1 e1 X1 n1,
  subst_typ_in_exp A1 X1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (subst_typ_in_exp A1 X1 e1) (subst_typ_in_exp A1 X1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_open_exp_wrt_exp_rec :
forall e2 A1 e1 X1 n1,
  subst_typ_in_exp A1 X1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (subst_typ_in_exp A1 X1 e1) (subst_typ_in_exp A1 X1 e2).
Proof.
pose proof subst_typ_in_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_typ_rec_mutual :
(forall e2 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_typ_rec n1 A1 e2) = open_exp_wrt_typ_rec n1 A1 (subst_exp_in_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_typ_rec :
forall e2 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_typ_rec n1 A1 e2) = open_exp_wrt_typ_rec n1 A1 (subst_exp_in_exp e1 x1 e2).
Proof.
pose proof subst_exp_in_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_typ_rec : lngen.

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

Lemma subst_typ_in_typ_open_typ_wrt_typ :
forall A3 A1 A2 X1,
  lc_typ A1 ->
  subst_typ_in_typ A1 X1 (open_typ_wrt_typ A3 A2) = open_typ_wrt_typ (subst_typ_in_typ A1 X1 A3) (subst_typ_in_typ A1 X1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_open_typ_wrt_typ : lngen.

Lemma subst_bid_in_bid_open_bid_wrt_bid :
forall D3 D1 D2 Xd1,
  lc_bid D1 ->
  subst_bid_in_bid D1 Xd1 (open_bid_wrt_bid D3 D2) = open_bid_wrt_bid (subst_bid_in_bid D1 Xd1 D3) (subst_bid_in_bid D1 Xd1 D2).
Proof.
unfold open_bid_wrt_bid; default_simp.
Qed.

#[export] Hint Resolve subst_bid_in_bid_open_bid_wrt_bid : lngen.

Lemma subst_utyp_in_utyp_open_utyp_wrt_utyp :
forall F3 F1 F2 Xf1,
  lc_utyp F1 ->
  subst_utyp_in_utyp F1 Xf1 (open_utyp_wrt_utyp F3 F2) = open_utyp_wrt_utyp (subst_utyp_in_utyp F1 Xf1 F3) (subst_utyp_in_utyp F1 Xf1 F2).
Proof.
unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_open_utyp_wrt_utyp : lngen.

Lemma subst_ctyp_in_ctyp_open_ctyp_wrt_ctyp :
forall K3 K1 K2 U1,
  lc_ctyp K1 ->
  subst_ctyp_in_ctyp K1 U1 (open_ctyp_wrt_ctyp K3 K2) = open_ctyp_wrt_ctyp (subst_ctyp_in_ctyp K1 U1 K3) (subst_ctyp_in_ctyp K1 U1 K2).
Proof.
unfold open_ctyp_wrt_ctyp; default_simp.
Qed.

#[export] Hint Resolve subst_ctyp_in_ctyp_open_ctyp_wrt_ctyp : lngen.

Lemma subst_skel_in_skel_open_skel_wrt_skel :
forall R3 R1 R2 Xr1,
  lc_skel R1 ->
  subst_skel_in_skel R1 Xr1 (open_skel_wrt_skel R3 R2) = open_skel_wrt_skel (subst_skel_in_skel R1 Xr1 R3) (subst_skel_in_skel R1 Xr1 R2).
Proof.
unfold open_skel_wrt_skel; default_simp.
Qed.

#[export] Hint Resolve subst_skel_in_skel_open_skel_wrt_skel : lngen.

Lemma subst_typ_in_dbind_open_dbind_wrt_typ :
forall db1 A1 A2 X1,
  lc_typ A1 ->
  subst_typ_in_dbind A1 X1 (open_dbind_wrt_typ db1 A2) = open_dbind_wrt_typ (subst_typ_in_dbind A1 X1 db1) (subst_typ_in_typ A1 X1 A2).
Proof.
unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_open_dbind_wrt_typ : lngen.

Lemma subst_typ_in_exp_open_exp_wrt_typ :
forall e1 A1 A2 X1,
  lc_typ A1 ->
  subst_typ_in_exp A1 X1 (open_exp_wrt_typ e1 A2) = open_exp_wrt_typ (subst_typ_in_exp A1 X1 e1) (subst_typ_in_typ A1 X1 A2).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_open_exp_wrt_typ : lngen.

Lemma subst_typ_in_exp_open_exp_wrt_exp :
forall e2 A1 e1 X1,
  subst_typ_in_exp A1 X1 (open_exp_wrt_exp e2 e1) = open_exp_wrt_exp (subst_typ_in_exp A1 X1 e2) (subst_typ_in_exp A1 X1 e1).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_typ :
forall e2 e1 A1 x1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_typ e2 A1) = open_exp_wrt_typ (subst_exp_in_exp e1 x1 e2) A1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_typ : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_exp :
forall e3 e1 e2 x1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_exp e3 e2) = open_exp_wrt_exp (subst_exp_in_exp e1 x1 e3) (subst_exp_in_exp e1 x1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_exp : lngen.

Lemma subst_typ_in_typ_open_typ_wrt_typ_var :
forall A2 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_typ_wrt_typ (subst_typ_in_typ A1 X1 A2) (typ_var_f X2) = subst_typ_in_typ A1 X1 (open_typ_wrt_typ A2 (typ_var_f X2)).
Proof.
intros; rewrite subst_typ_in_typ_open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_open_typ_wrt_typ_var : lngen.

Lemma subst_bid_in_bid_open_bid_wrt_bid_var :
forall D2 D1 Xd1 Xd2,
  Xd1 <> Xd2 ->
  lc_bid D1 ->
  open_bid_wrt_bid (subst_bid_in_bid D1 Xd1 D2) (bid_var_f Xd2) = subst_bid_in_bid D1 Xd1 (open_bid_wrt_bid D2 (bid_var_f Xd2)).
Proof.
intros; rewrite subst_bid_in_bid_open_bid_wrt_bid; default_simp.
Qed.

#[export] Hint Resolve subst_bid_in_bid_open_bid_wrt_bid_var : lngen.

Lemma subst_utyp_in_utyp_open_utyp_wrt_utyp_var :
forall F2 F1 Xf1 Xf2,
  Xf1 <> Xf2 ->
  lc_utyp F1 ->
  open_utyp_wrt_utyp (subst_utyp_in_utyp F1 Xf1 F2) (utyp_var_f Xf2) = subst_utyp_in_utyp F1 Xf1 (open_utyp_wrt_utyp F2 (utyp_var_f Xf2)).
Proof.
intros; rewrite subst_utyp_in_utyp_open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_open_utyp_wrt_utyp_var : lngen.

Lemma subst_ctyp_in_ctyp_open_ctyp_wrt_ctyp_var :
forall K2 K1 U1 U2,
  U1 <> U2 ->
  lc_ctyp K1 ->
  open_ctyp_wrt_ctyp (subst_ctyp_in_ctyp K1 U1 K2) (ctyp_var_f U2) = subst_ctyp_in_ctyp K1 U1 (open_ctyp_wrt_ctyp K2 (ctyp_var_f U2)).
Proof.
intros; rewrite subst_ctyp_in_ctyp_open_ctyp_wrt_ctyp; default_simp.
Qed.

#[export] Hint Resolve subst_ctyp_in_ctyp_open_ctyp_wrt_ctyp_var : lngen.

Lemma subst_skel_in_skel_open_skel_wrt_skel_var :
forall R2 R1 Xr1 Xr2,
  Xr1 <> Xr2 ->
  lc_skel R1 ->
  open_skel_wrt_skel (subst_skel_in_skel R1 Xr1 R2) (skel_var_f Xr2) = subst_skel_in_skel R1 Xr1 (open_skel_wrt_skel R2 (skel_var_f Xr2)).
Proof.
intros; rewrite subst_skel_in_skel_open_skel_wrt_skel; default_simp.
Qed.

#[export] Hint Resolve subst_skel_in_skel_open_skel_wrt_skel_var : lngen.

Lemma subst_typ_in_dbind_open_dbind_wrt_typ_var :
forall db1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_dbind_wrt_typ (subst_typ_in_dbind A1 X1 db1) (typ_var_f X2) = subst_typ_in_dbind A1 X1 (open_dbind_wrt_typ db1 (typ_var_f X2)).
Proof.
intros; rewrite subst_typ_in_dbind_open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_open_dbind_wrt_typ_var : lngen.

Lemma subst_typ_in_exp_open_exp_wrt_typ_var :
forall e1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_exp_wrt_typ (subst_typ_in_exp A1 X1 e1) (typ_var_f X2) = subst_typ_in_exp A1 X1 (open_exp_wrt_typ e1 (typ_var_f X2)).
Proof.
intros; rewrite subst_typ_in_exp_open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_open_exp_wrt_typ_var : lngen.

Lemma subst_typ_in_exp_open_exp_wrt_exp_var :
forall e1 A1 X1 x1,
  open_exp_wrt_exp (subst_typ_in_exp A1 X1 e1) (exp_var_f x1) = subst_typ_in_exp A1 X1 (open_exp_wrt_exp e1 (exp_var_f x1)).
Proof.
intros; rewrite subst_typ_in_exp_open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_open_exp_wrt_exp_var : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_typ_var :
forall e2 e1 x1 X1,
  lc_exp e1 ->
  open_exp_wrt_typ (subst_exp_in_exp e1 x1 e2) (typ_var_f X1) = subst_exp_in_exp e1 x1 (open_exp_wrt_typ e2 (typ_var_f X1)).
Proof.
intros; rewrite subst_exp_in_exp_open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_typ_var : lngen.

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

Lemma subst_typ_in_typ_spec_rec_mutual :
(forall A1 A2 X1 n1,
  subst_typ_in_typ A2 X1 A1 = open_typ_wrt_typ_rec n1 A2 (close_typ_wrt_typ_rec n1 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_typ_spec_rec :
forall A1 A2 X1 n1,
  subst_typ_in_typ A2 X1 A1 = open_typ_wrt_typ_rec n1 A2 (close_typ_wrt_typ_rec n1 X1 A1).
Proof.
pose proof subst_typ_in_typ_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_bid_in_bid_spec_rec_mutual :
(forall D1 D2 Xd1 n1,
  subst_bid_in_bid D2 Xd1 D1 = open_bid_wrt_bid_rec n1 D2 (close_bid_wrt_bid_rec n1 Xd1 D1)).
Proof.
apply_mutual_ind bid_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_bid_in_bid_spec_rec :
forall D1 D2 Xd1 n1,
  subst_bid_in_bid D2 Xd1 D1 = open_bid_wrt_bid_rec n1 D2 (close_bid_wrt_bid_rec n1 Xd1 D1).
Proof.
pose proof subst_bid_in_bid_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bid_in_bid_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_utyp_in_utyp_spec_rec_mutual :
(forall F1 F2 Xf1 n1,
  subst_utyp_in_utyp F2 Xf1 F1 = open_utyp_wrt_utyp_rec n1 F2 (close_utyp_wrt_utyp_rec n1 Xf1 F1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_utyp_in_utyp_spec_rec :
forall F1 F2 Xf1 n1,
  subst_utyp_in_utyp F2 Xf1 F1 = open_utyp_wrt_utyp_rec n1 F2 (close_utyp_wrt_utyp_rec n1 Xf1 F1).
Proof.
pose proof subst_utyp_in_utyp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ctyp_in_ctyp_spec_rec_mutual :
(forall K1 K2 U1 n1,
  subst_ctyp_in_ctyp K2 U1 K1 = open_ctyp_wrt_ctyp_rec n1 K2 (close_ctyp_wrt_ctyp_rec n1 U1 K1)).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ctyp_in_ctyp_spec_rec :
forall K1 K2 U1 n1,
  subst_ctyp_in_ctyp K2 U1 K1 = open_ctyp_wrt_ctyp_rec n1 K2 (close_ctyp_wrt_ctyp_rec n1 U1 K1).
Proof.
pose proof subst_ctyp_in_ctyp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ctyp_in_ctyp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_skel_in_skel_spec_rec_mutual :
(forall R1 R2 Xr1 n1,
  subst_skel_in_skel R2 Xr1 R1 = open_skel_wrt_skel_rec n1 R2 (close_skel_wrt_skel_rec n1 Xr1 R1)).
Proof.
apply_mutual_ind skel_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_skel_in_skel_spec_rec :
forall R1 R2 Xr1 n1,
  subst_skel_in_skel R2 Xr1 R1 = open_skel_wrt_skel_rec n1 R2 (close_skel_wrt_skel_rec n1 Xr1 R1).
Proof.
pose proof subst_skel_in_skel_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skel_in_skel_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_dbind_spec_rec_mutual :
(forall db1 A1 X1 n1,
  subst_typ_in_dbind A1 X1 db1 = open_dbind_wrt_typ_rec n1 A1 (close_dbind_wrt_typ_rec n1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_dbind_spec_rec :
forall db1 A1 X1 n1,
  subst_typ_in_dbind A1 X1 db1 = open_dbind_wrt_typ_rec n1 A1 (close_dbind_wrt_typ_rec n1 X1 db1).
Proof.
pose proof subst_typ_in_dbind_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_spec_rec_mutual :
(forall e1 A1 X1 n1,
  subst_typ_in_exp A1 X1 e1 = open_exp_wrt_typ_rec n1 A1 (close_exp_wrt_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_spec_rec :
forall e1 A1 X1 n1,
  subst_typ_in_exp A1 X1 e1 = open_exp_wrt_typ_rec n1 A1 (close_exp_wrt_typ_rec n1 X1 e1).
Proof.
pose proof subst_typ_in_exp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_spec_rec : lngen.

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

Lemma subst_typ_in_typ_spec :
forall A1 A2 X1,
  subst_typ_in_typ A2 X1 A1 = open_typ_wrt_typ (close_typ_wrt_typ X1 A1) A2.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_spec : lngen.

Lemma subst_bid_in_bid_spec :
forall D1 D2 Xd1,
  subst_bid_in_bid D2 Xd1 D1 = open_bid_wrt_bid (close_bid_wrt_bid Xd1 D1) D2.
Proof.
unfold close_bid_wrt_bid; unfold open_bid_wrt_bid; default_simp.
Qed.

#[export] Hint Resolve subst_bid_in_bid_spec : lngen.

Lemma subst_utyp_in_utyp_spec :
forall F1 F2 Xf1,
  subst_utyp_in_utyp F2 Xf1 F1 = open_utyp_wrt_utyp (close_utyp_wrt_utyp Xf1 F1) F2.
Proof.
unfold close_utyp_wrt_utyp; unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_spec : lngen.

Lemma subst_ctyp_in_ctyp_spec :
forall K1 K2 U1,
  subst_ctyp_in_ctyp K2 U1 K1 = open_ctyp_wrt_ctyp (close_ctyp_wrt_ctyp U1 K1) K2.
Proof.
unfold close_ctyp_wrt_ctyp; unfold open_ctyp_wrt_ctyp; default_simp.
Qed.

#[export] Hint Resolve subst_ctyp_in_ctyp_spec : lngen.

Lemma subst_skel_in_skel_spec :
forall R1 R2 Xr1,
  subst_skel_in_skel R2 Xr1 R1 = open_skel_wrt_skel (close_skel_wrt_skel Xr1 R1) R2.
Proof.
unfold close_skel_wrt_skel; unfold open_skel_wrt_skel; default_simp.
Qed.

#[export] Hint Resolve subst_skel_in_skel_spec : lngen.

Lemma subst_typ_in_dbind_spec :
forall db1 A1 X1,
  subst_typ_in_dbind A1 X1 db1 = open_dbind_wrt_typ (close_dbind_wrt_typ X1 db1) A1.
Proof.
unfold close_dbind_wrt_typ; unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_spec : lngen.

Lemma subst_typ_in_exp_spec :
forall e1 A1 X1,
  subst_typ_in_exp A1 X1 e1 = open_exp_wrt_typ (close_exp_wrt_typ X1 e1) A1.
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_spec : lngen.

Lemma subst_exp_in_exp_spec :
forall e1 e2 x1,
  subst_exp_in_exp e2 x1 e1 = open_exp_wrt_exp (close_exp_wrt_exp x1 e1) e2.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_spec : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_subst_typ_in_typ_mutual :
(forall A1 A2 A3 X2 X1,
  X2 `notin` ftvar_in_typ A2 ->
  X2 <> X1 ->
  subst_typ_in_typ A2 X1 (subst_typ_in_typ A3 X2 A1) = subst_typ_in_typ (subst_typ_in_typ A2 X1 A3) X2 (subst_typ_in_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_subst_typ_in_typ :
forall A1 A2 A3 X2 X1,
  X2 `notin` ftvar_in_typ A2 ->
  X2 <> X1 ->
  subst_typ_in_typ A2 X1 (subst_typ_in_typ A3 X2 A1) = subst_typ_in_typ (subst_typ_in_typ A2 X1 A3) X2 (subst_typ_in_typ A2 X1 A1).
Proof.
pose proof subst_typ_in_typ_subst_typ_in_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_subst_typ_in_typ : lngen.

(* begin hide *)

Lemma subst_bid_in_bid_subst_bid_in_bid_mutual :
(forall D1 D2 D3 Xd2 Xd1,
  Xd2 `notin` ftvar_in_bid D2 ->
  Xd2 <> Xd1 ->
  subst_bid_in_bid D2 Xd1 (subst_bid_in_bid D3 Xd2 D1) = subst_bid_in_bid (subst_bid_in_bid D2 Xd1 D3) Xd2 (subst_bid_in_bid D2 Xd1 D1)).
Proof.
apply_mutual_ind bid_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_bid_in_bid_subst_bid_in_bid :
forall D1 D2 D3 Xd2 Xd1,
  Xd2 `notin` ftvar_in_bid D2 ->
  Xd2 <> Xd1 ->
  subst_bid_in_bid D2 Xd1 (subst_bid_in_bid D3 Xd2 D1) = subst_bid_in_bid (subst_bid_in_bid D2 Xd1 D3) Xd2 (subst_bid_in_bid D2 Xd1 D1).
Proof.
pose proof subst_bid_in_bid_subst_bid_in_bid_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bid_in_bid_subst_bid_in_bid : lngen.

(* begin hide *)

Lemma subst_utyp_in_utyp_subst_utyp_in_utyp_mutual :
(forall F1 F2 F3 Xf2 Xf1,
  Xf2 `notin` ftvar_in_utyp F2 ->
  Xf2 <> Xf1 ->
  subst_utyp_in_utyp F2 Xf1 (subst_utyp_in_utyp F3 Xf2 F1) = subst_utyp_in_utyp (subst_utyp_in_utyp F2 Xf1 F3) Xf2 (subst_utyp_in_utyp F2 Xf1 F1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_utyp_in_utyp_subst_utyp_in_utyp :
forall F1 F2 F3 Xf2 Xf1,
  Xf2 `notin` ftvar_in_utyp F2 ->
  Xf2 <> Xf1 ->
  subst_utyp_in_utyp F2 Xf1 (subst_utyp_in_utyp F3 Xf2 F1) = subst_utyp_in_utyp (subst_utyp_in_utyp F2 Xf1 F3) Xf2 (subst_utyp_in_utyp F2 Xf1 F1).
Proof.
pose proof subst_utyp_in_utyp_subst_utyp_in_utyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_subst_utyp_in_utyp : lngen.

(* begin hide *)

Lemma subst_ctyp_in_ctyp_subst_ctyp_in_ctyp_mutual :
(forall K1 K2 K3 U2 U1,
  U2 `notin` ftvar_in_ctyp K2 ->
  U2 <> U1 ->
  subst_ctyp_in_ctyp K2 U1 (subst_ctyp_in_ctyp K3 U2 K1) = subst_ctyp_in_ctyp (subst_ctyp_in_ctyp K2 U1 K3) U2 (subst_ctyp_in_ctyp K2 U1 K1)).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ctyp_in_ctyp_subst_ctyp_in_ctyp :
forall K1 K2 K3 U2 U1,
  U2 `notin` ftvar_in_ctyp K2 ->
  U2 <> U1 ->
  subst_ctyp_in_ctyp K2 U1 (subst_ctyp_in_ctyp K3 U2 K1) = subst_ctyp_in_ctyp (subst_ctyp_in_ctyp K2 U1 K3) U2 (subst_ctyp_in_ctyp K2 U1 K1).
Proof.
pose proof subst_ctyp_in_ctyp_subst_ctyp_in_ctyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ctyp_in_ctyp_subst_ctyp_in_ctyp : lngen.

(* begin hide *)

Lemma subst_skel_in_skel_subst_skel_in_skel_mutual :
(forall R1 R2 R3 Xr2 Xr1,
  Xr2 `notin` ftvar_in_skel R2 ->
  Xr2 <> Xr1 ->
  subst_skel_in_skel R2 Xr1 (subst_skel_in_skel R3 Xr2 R1) = subst_skel_in_skel (subst_skel_in_skel R2 Xr1 R3) Xr2 (subst_skel_in_skel R2 Xr1 R1)).
Proof.
apply_mutual_ind skel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skel_in_skel_subst_skel_in_skel :
forall R1 R2 R3 Xr2 Xr1,
  Xr2 `notin` ftvar_in_skel R2 ->
  Xr2 <> Xr1 ->
  subst_skel_in_skel R2 Xr1 (subst_skel_in_skel R3 Xr2 R1) = subst_skel_in_skel (subst_skel_in_skel R2 Xr1 R3) Xr2 (subst_skel_in_skel R2 Xr1 R1).
Proof.
pose proof subst_skel_in_skel_subst_skel_in_skel_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skel_in_skel_subst_skel_in_skel : lngen.

(* begin hide *)

Lemma subst_typ_in_dbind_subst_typ_in_dbind_mutual :
(forall db1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_typ_in_dbind A1 X1 (subst_typ_in_dbind A2 X2 db1) = subst_typ_in_dbind (subst_typ_in_typ A1 X1 A2) X2 (subst_typ_in_dbind A1 X1 db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_dbind_subst_typ_in_dbind :
forall db1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_typ_in_dbind A1 X1 (subst_typ_in_dbind A2 X2 db1) = subst_typ_in_dbind (subst_typ_in_typ A1 X1 A2) X2 (subst_typ_in_dbind A1 X1 db1).
Proof.
pose proof subst_typ_in_dbind_subst_typ_in_dbind_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_subst_typ_in_dbind : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_subst_typ_in_exp_mutual :
(forall e1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_typ_in_exp A1 X1 (subst_typ_in_exp A2 X2 e1) = subst_typ_in_exp (subst_typ_in_typ A1 X1 A2) X2 (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_subst_typ_in_exp :
forall e1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  subst_typ_in_exp A1 X1 (subst_typ_in_exp A2 X2 e1) = subst_typ_in_exp (subst_typ_in_typ A1 X1 A2) X2 (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof subst_typ_in_exp_subst_typ_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_subst_typ_in_exp : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_subst_exp_in_exp_mutual :
(forall e1 A1 e2 x1 X1,
  subst_typ_in_exp A1 X1 (subst_exp_in_exp e2 x1 e1) = subst_exp_in_exp (subst_typ_in_exp A1 X1 e2) x1 (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_subst_exp_in_exp :
forall e1 A1 e2 x1 X1,
  subst_typ_in_exp A1 X1 (subst_exp_in_exp e2 x1 e1) = subst_exp_in_exp (subst_typ_in_exp A1 X1 e2) x1 (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof subst_typ_in_exp_subst_exp_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_subst_exp_in_exp : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_subst_typ_in_exp_mutual :
(forall e1 e2 A1 X1 x1,
  X1 `notin` ftvar_in_exp e2 ->
  subst_exp_in_exp e2 x1 (subst_typ_in_exp A1 X1 e1) = subst_typ_in_exp A1 X1 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_subst_typ_in_exp :
forall e1 e2 A1 X1 x1,
  X1 `notin` ftvar_in_exp e2 ->
  subst_exp_in_exp e2 x1 (subst_typ_in_exp A1 X1 e1) = subst_typ_in_exp A1 X1 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_subst_typ_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_subst_typ_in_exp : lngen.

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

Lemma subst_typ_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual :
(forall A2 A1 X1 X2 n1,
  X2 `notin` ftvar_in_typ A2 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_typ A1 X1 A2 = close_typ_wrt_typ_rec n1 X2 (subst_typ_in_typ A1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X2) A2))).
Proof.
apply_mutual_ind typ_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec :
forall A2 A1 X1 X2 n1,
  X2 `notin` ftvar_in_typ A2 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_typ A1 X1 A2 = close_typ_wrt_typ_rec n1 X2 (subst_typ_in_typ A1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X2) A2)).
Proof.
pose proof subst_typ_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_bid_in_bid_close_bid_wrt_bid_rec_open_bid_wrt_bid_rec_mutual :
(forall D2 D1 Xd1 Xd2 n1,
  Xd2 `notin` ftvar_in_bid D2 ->
  Xd2 `notin` ftvar_in_bid D1 ->
  Xd2 <> Xd1 ->
  degree_bid_wrt_bid n1 D1 ->
  subst_bid_in_bid D1 Xd1 D2 = close_bid_wrt_bid_rec n1 Xd2 (subst_bid_in_bid D1 Xd1 (open_bid_wrt_bid_rec n1 (bid_var_f Xd2) D2))).
Proof.
apply_mutual_ind bid_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_bid_in_bid_close_bid_wrt_bid_rec_open_bid_wrt_bid_rec :
forall D2 D1 Xd1 Xd2 n1,
  Xd2 `notin` ftvar_in_bid D2 ->
  Xd2 `notin` ftvar_in_bid D1 ->
  Xd2 <> Xd1 ->
  degree_bid_wrt_bid n1 D1 ->
  subst_bid_in_bid D1 Xd1 D2 = close_bid_wrt_bid_rec n1 Xd2 (subst_bid_in_bid D1 Xd1 (open_bid_wrt_bid_rec n1 (bid_var_f Xd2) D2)).
Proof.
pose proof subst_bid_in_bid_close_bid_wrt_bid_rec_open_bid_wrt_bid_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bid_in_bid_close_bid_wrt_bid_rec_open_bid_wrt_bid_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_utyp_in_utyp_close_utyp_wrt_utyp_rec_open_utyp_wrt_utyp_rec_mutual :
(forall F2 F1 Xf1 Xf2 n1,
  Xf2 `notin` ftvar_in_utyp F2 ->
  Xf2 `notin` ftvar_in_utyp F1 ->
  Xf2 <> Xf1 ->
  degree_utyp_wrt_utyp n1 F1 ->
  subst_utyp_in_utyp F1 Xf1 F2 = close_utyp_wrt_utyp_rec n1 Xf2 (subst_utyp_in_utyp F1 Xf1 (open_utyp_wrt_utyp_rec n1 (utyp_var_f Xf2) F2))).
Proof.
apply_mutual_ind utyp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_utyp_in_utyp_close_utyp_wrt_utyp_rec_open_utyp_wrt_utyp_rec :
forall F2 F1 Xf1 Xf2 n1,
  Xf2 `notin` ftvar_in_utyp F2 ->
  Xf2 `notin` ftvar_in_utyp F1 ->
  Xf2 <> Xf1 ->
  degree_utyp_wrt_utyp n1 F1 ->
  subst_utyp_in_utyp F1 Xf1 F2 = close_utyp_wrt_utyp_rec n1 Xf2 (subst_utyp_in_utyp F1 Xf1 (open_utyp_wrt_utyp_rec n1 (utyp_var_f Xf2) F2)).
Proof.
pose proof subst_utyp_in_utyp_close_utyp_wrt_utyp_rec_open_utyp_wrt_utyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_close_utyp_wrt_utyp_rec_open_utyp_wrt_utyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ctyp_in_ctyp_close_ctyp_wrt_ctyp_rec_open_ctyp_wrt_ctyp_rec_mutual :
(forall K2 K1 U1 U2 n1,
  U2 `notin` ftvar_in_ctyp K2 ->
  U2 `notin` ftvar_in_ctyp K1 ->
  U2 <> U1 ->
  degree_ctyp_wrt_ctyp n1 K1 ->
  subst_ctyp_in_ctyp K1 U1 K2 = close_ctyp_wrt_ctyp_rec n1 U2 (subst_ctyp_in_ctyp K1 U1 (open_ctyp_wrt_ctyp_rec n1 (ctyp_var_f U2) K2))).
Proof.
apply_mutual_ind ctyp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ctyp_in_ctyp_close_ctyp_wrt_ctyp_rec_open_ctyp_wrt_ctyp_rec :
forall K2 K1 U1 U2 n1,
  U2 `notin` ftvar_in_ctyp K2 ->
  U2 `notin` ftvar_in_ctyp K1 ->
  U2 <> U1 ->
  degree_ctyp_wrt_ctyp n1 K1 ->
  subst_ctyp_in_ctyp K1 U1 K2 = close_ctyp_wrt_ctyp_rec n1 U2 (subst_ctyp_in_ctyp K1 U1 (open_ctyp_wrt_ctyp_rec n1 (ctyp_var_f U2) K2)).
Proof.
pose proof subst_ctyp_in_ctyp_close_ctyp_wrt_ctyp_rec_open_ctyp_wrt_ctyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ctyp_in_ctyp_close_ctyp_wrt_ctyp_rec_open_ctyp_wrt_ctyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_skel_in_skel_close_skel_wrt_skel_rec_open_skel_wrt_skel_rec_mutual :
(forall R2 R1 Xr1 Xr2 n1,
  Xr2 `notin` ftvar_in_skel R2 ->
  Xr2 `notin` ftvar_in_skel R1 ->
  Xr2 <> Xr1 ->
  degree_skel_wrt_skel n1 R1 ->
  subst_skel_in_skel R1 Xr1 R2 = close_skel_wrt_skel_rec n1 Xr2 (subst_skel_in_skel R1 Xr1 (open_skel_wrt_skel_rec n1 (skel_var_f Xr2) R2))).
Proof.
apply_mutual_ind skel_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_skel_in_skel_close_skel_wrt_skel_rec_open_skel_wrt_skel_rec :
forall R2 R1 Xr1 Xr2 n1,
  Xr2 `notin` ftvar_in_skel R2 ->
  Xr2 `notin` ftvar_in_skel R1 ->
  Xr2 <> Xr1 ->
  degree_skel_wrt_skel n1 R1 ->
  subst_skel_in_skel R1 Xr1 R2 = close_skel_wrt_skel_rec n1 Xr2 (subst_skel_in_skel R1 Xr1 (open_skel_wrt_skel_rec n1 (skel_var_f Xr2) R2)).
Proof.
pose proof subst_skel_in_skel_close_skel_wrt_skel_rec_open_skel_wrt_skel_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skel_in_skel_close_skel_wrt_skel_rec_open_skel_wrt_skel_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_dbind_close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec_mutual :
(forall db1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_dbind db1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_dbind A1 X1 db1 = close_dbind_wrt_typ_rec n1 X2 (subst_typ_in_dbind A1 X1 (open_dbind_wrt_typ_rec n1 (typ_var_f X2) db1))).
Proof.
apply_mutual_ind dbind_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_dbind_close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec :
forall db1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_dbind db1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_dbind A1 X1 db1 = close_dbind_wrt_typ_rec n1 X2 (subst_typ_in_dbind A1 X1 (open_dbind_wrt_typ_rec n1 (typ_var_f X2) db1)).
Proof.
pose proof subst_typ_in_dbind_close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_close_dbind_wrt_typ_rec_open_dbind_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_exp e1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_exp A1 X1 e1 = close_exp_wrt_typ_rec n1 X2 (subst_typ_in_exp A1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X2) e1))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_exp e1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_exp A1 X1 e1 = close_exp_wrt_typ_rec n1 X2 (subst_typ_in_exp A1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X2) e1)).
Proof.
pose proof subst_typ_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e1 A1 X1 x1 n1,
  x1 `notin` fvar_in_exp e1 ->
  subst_typ_in_exp A1 X1 e1 = close_exp_wrt_exp_rec n1 x1 (subst_typ_in_exp A1 X1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e1 A1 X1 x1 n1,
  x1 `notin` fvar_in_exp e1 ->
  subst_typ_in_exp A1 X1 e1 = close_exp_wrt_exp_rec n1 x1 (subst_typ_in_exp A1 X1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1)).
Proof.
pose proof subst_typ_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e2 e1 x1 X1 n1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_typ_rec n1 X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e2))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e2 e1 x1 X1 n1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_typ_rec n1 X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e2)).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.

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

Lemma subst_typ_in_typ_close_typ_wrt_typ_open_typ_wrt_typ :
forall A2 A1 X1 X2,
  X2 `notin` ftvar_in_typ A2 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_typ_in_typ A1 X1 A2 = close_typ_wrt_typ X2 (subst_typ_in_typ A1 X1 (open_typ_wrt_typ A2 (typ_var_f X2))).
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_close_typ_wrt_typ_open_typ_wrt_typ : lngen.

Lemma subst_bid_in_bid_close_bid_wrt_bid_open_bid_wrt_bid :
forall D2 D1 Xd1 Xd2,
  Xd2 `notin` ftvar_in_bid D2 ->
  Xd2 `notin` ftvar_in_bid D1 ->
  Xd2 <> Xd1 ->
  lc_bid D1 ->
  subst_bid_in_bid D1 Xd1 D2 = close_bid_wrt_bid Xd2 (subst_bid_in_bid D1 Xd1 (open_bid_wrt_bid D2 (bid_var_f Xd2))).
Proof.
unfold close_bid_wrt_bid; unfold open_bid_wrt_bid; default_simp.
Qed.

#[export] Hint Resolve subst_bid_in_bid_close_bid_wrt_bid_open_bid_wrt_bid : lngen.

Lemma subst_utyp_in_utyp_close_utyp_wrt_utyp_open_utyp_wrt_utyp :
forall F2 F1 Xf1 Xf2,
  Xf2 `notin` ftvar_in_utyp F2 ->
  Xf2 `notin` ftvar_in_utyp F1 ->
  Xf2 <> Xf1 ->
  lc_utyp F1 ->
  subst_utyp_in_utyp F1 Xf1 F2 = close_utyp_wrt_utyp Xf2 (subst_utyp_in_utyp F1 Xf1 (open_utyp_wrt_utyp F2 (utyp_var_f Xf2))).
Proof.
unfold close_utyp_wrt_utyp; unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_close_utyp_wrt_utyp_open_utyp_wrt_utyp : lngen.

Lemma subst_ctyp_in_ctyp_close_ctyp_wrt_ctyp_open_ctyp_wrt_ctyp :
forall K2 K1 U1 U2,
  U2 `notin` ftvar_in_ctyp K2 ->
  U2 `notin` ftvar_in_ctyp K1 ->
  U2 <> U1 ->
  lc_ctyp K1 ->
  subst_ctyp_in_ctyp K1 U1 K2 = close_ctyp_wrt_ctyp U2 (subst_ctyp_in_ctyp K1 U1 (open_ctyp_wrt_ctyp K2 (ctyp_var_f U2))).
Proof.
unfold close_ctyp_wrt_ctyp; unfold open_ctyp_wrt_ctyp; default_simp.
Qed.

#[export] Hint Resolve subst_ctyp_in_ctyp_close_ctyp_wrt_ctyp_open_ctyp_wrt_ctyp : lngen.

Lemma subst_skel_in_skel_close_skel_wrt_skel_open_skel_wrt_skel :
forall R2 R1 Xr1 Xr2,
  Xr2 `notin` ftvar_in_skel R2 ->
  Xr2 `notin` ftvar_in_skel R1 ->
  Xr2 <> Xr1 ->
  lc_skel R1 ->
  subst_skel_in_skel R1 Xr1 R2 = close_skel_wrt_skel Xr2 (subst_skel_in_skel R1 Xr1 (open_skel_wrt_skel R2 (skel_var_f Xr2))).
Proof.
unfold close_skel_wrt_skel; unfold open_skel_wrt_skel; default_simp.
Qed.

#[export] Hint Resolve subst_skel_in_skel_close_skel_wrt_skel_open_skel_wrt_skel : lngen.

Lemma subst_typ_in_dbind_close_dbind_wrt_typ_open_dbind_wrt_typ :
forall db1 A1 X1 X2,
  X2 `notin` ftvar_in_dbind db1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_typ_in_dbind A1 X1 db1 = close_dbind_wrt_typ X2 (subst_typ_in_dbind A1 X1 (open_dbind_wrt_typ db1 (typ_var_f X2))).
Proof.
unfold close_dbind_wrt_typ; unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_close_dbind_wrt_typ_open_dbind_wrt_typ : lngen.

Lemma subst_typ_in_exp_close_exp_wrt_typ_open_exp_wrt_typ :
forall e1 A1 X1 X2,
  X2 `notin` ftvar_in_exp e1 ->
  X2 `notin` ftvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_typ_in_exp A1 X1 e1 = close_exp_wrt_typ X2 (subst_typ_in_exp A1 X1 (open_exp_wrt_typ e1 (typ_var_f X2))).
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_typ_open_exp_wrt_typ : lngen.

Lemma subst_typ_in_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 A1 X1 x1,
  x1 `notin` fvar_in_exp e1 ->
  lc_typ A1 ->
  subst_typ_in_exp A1 X1 e1 = close_exp_wrt_exp x1 (subst_typ_in_exp A1 X1 (open_exp_wrt_exp e1 (exp_var_f x1))).
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_typ_open_exp_wrt_typ :
forall e2 e1 x1 X1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_typ X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_typ e2 (typ_var_f X1))).
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_typ_open_exp_wrt_typ : lngen.

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

Lemma subst_typ_in_typ_typ_all_col :
forall X2 c1 A2 A1 X1,
  lc_typ A1 ->
  X2 `notin` ftvar_in_typ A1 `union` ftvar_in_typ A2 `union` singleton X1 ->
  subst_typ_in_typ A1 X1 (typ_all_col c1 A2) = typ_all_col (c1) (close_typ_wrt_typ X2 (subst_typ_in_typ A1 X1 (open_typ_wrt_typ A2 (typ_var_f X2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_typ_all_col : lngen.

Lemma subst_typ_in_typ_typ_all_etag :
forall X2 ε1 A2 A1 X1,
  lc_typ A1 ->
  X2 `notin` ftvar_in_typ A1 `union` ftvar_in_typ A2 `union` singleton X1 ->
  subst_typ_in_typ A1 X1 (typ_all_etag ε1 A2) = typ_all_etag (ε1) (close_typ_wrt_typ X2 (subst_typ_in_typ A1 X1 (open_typ_wrt_typ A2 (typ_var_f X2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_typ_all_etag : lngen.

Lemma subst_bid_in_bid_bid_all_syn :
forall Xd2 D2 D1 Xd1,
  lc_bid D1 ->
  Xd2 `notin` ftvar_in_bid D1 `union` ftvar_in_bid D2 `union` singleton Xd1 ->
  subst_bid_in_bid D1 Xd1 (bid_all_syn D2) = bid_all_syn (close_bid_wrt_bid Xd2 (subst_bid_in_bid D1 Xd1 (open_bid_wrt_bid D2 (bid_var_f Xd2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_bid_in_bid_bid_all_syn : lngen.

Lemma subst_bid_in_bid_bid_all_inh :
forall Xd2 D2 D1 Xd1,
  lc_bid D1 ->
  Xd2 `notin` ftvar_in_bid D1 `union` ftvar_in_bid D2 `union` singleton Xd1 ->
  subst_bid_in_bid D1 Xd1 (bid_all_inh D2) = bid_all_inh (close_bid_wrt_bid Xd2 (subst_bid_in_bid D1 Xd1 (open_bid_wrt_bid D2 (bid_var_f Xd2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_bid_in_bid_bid_all_inh : lngen.

Lemma subst_bid_in_bid_bid_all_etag :
forall Xd2 ε1 D2 D1 Xd1,
  lc_bid D1 ->
  Xd2 `notin` ftvar_in_bid D1 `union` ftvar_in_bid D2 `union` singleton Xd1 ->
  subst_bid_in_bid D1 Xd1 (bid_all_etag ε1 D2) = bid_all_etag (ε1) (close_bid_wrt_bid Xd2 (subst_bid_in_bid D1 Xd1 (open_bid_wrt_bid D2 (bid_var_f Xd2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_bid_in_bid_bid_all_etag : lngen.

Lemma subst_utyp_in_utyp_utyp_all_syn :
forall Xf2 F2 F1 Xf1,
  lc_utyp F1 ->
  Xf2 `notin` ftvar_in_utyp F1 `union` ftvar_in_utyp F2 `union` singleton Xf1 ->
  subst_utyp_in_utyp F1 Xf1 (utyp_all_syn F2) = utyp_all_syn (close_utyp_wrt_utyp Xf2 (subst_utyp_in_utyp F1 Xf1 (open_utyp_wrt_utyp F2 (utyp_var_f Xf2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_utyp_all_syn : lngen.

Lemma subst_utyp_in_utyp_utyp_all_etag :
forall Xf2 ε1 F2 F1 Xf1,
  lc_utyp F1 ->
  Xf2 `notin` ftvar_in_utyp F1 `union` ftvar_in_utyp F2 `union` singleton Xf1 ->
  subst_utyp_in_utyp F1 Xf1 (utyp_all_etag ε1 F2) = utyp_all_etag (ε1) (close_utyp_wrt_utyp Xf2 (subst_utyp_in_utyp F1 Xf1 (open_utyp_wrt_utyp F2 (utyp_var_f Xf2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_utyp_all_etag : lngen.

Lemma subst_ctyp_in_ctyp_ctyp_all :
forall U2 K2 K1 U1,
  lc_ctyp K1 ->
  U2 `notin` ftvar_in_ctyp K1 `union` ftvar_in_ctyp K2 `union` singleton U1 ->
  subst_ctyp_in_ctyp K1 U1 (ctyp_all K2) = ctyp_all (close_ctyp_wrt_ctyp U2 (subst_ctyp_in_ctyp K1 U1 (open_ctyp_wrt_ctyp K2 (ctyp_var_f U2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_ctyp_in_ctyp_ctyp_all : lngen.

Lemma subst_skel_in_skel_skel_all_syn :
forall Xr2 R2 R1 Xr1,
  lc_skel R1 ->
  Xr2 `notin` ftvar_in_skel R1 `union` ftvar_in_skel R2 `union` singleton Xr1 ->
  subst_skel_in_skel R1 Xr1 (skel_all_syn R2) = skel_all_syn (close_skel_wrt_skel Xr2 (subst_skel_in_skel R1 Xr1 (open_skel_wrt_skel R2 (skel_var_f Xr2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_skel_in_skel_skel_all_syn : lngen.

Lemma subst_skel_in_skel_skel_all_inh :
forall Xr2 R2 R1 Xr1,
  lc_skel R1 ->
  Xr2 `notin` ftvar_in_skel R1 `union` ftvar_in_skel R2 `union` singleton Xr1 ->
  subst_skel_in_skel R1 Xr1 (skel_all_inh R2) = skel_all_inh (close_skel_wrt_skel Xr2 (subst_skel_in_skel R1 Xr1 (open_skel_wrt_skel R2 (skel_var_f Xr2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_skel_in_skel_skel_all_inh : lngen.

Lemma subst_skel_in_skel_skel_all_etag :
forall Xr2 ε1 R2 R1 Xr1,
  lc_skel R1 ->
  Xr2 `notin` ftvar_in_skel R1 `union` ftvar_in_skel R2 `union` singleton Xr1 ->
  subst_skel_in_skel R1 Xr1 (skel_all_etag ε1 R2) = skel_all_etag (ε1) (close_skel_wrt_skel Xr2 (subst_skel_in_skel R1 Xr1 (open_skel_wrt_skel R2 (skel_var_f Xr2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_skel_in_skel_skel_all_etag : lngen.

Lemma subst_typ_in_exp_exp_abs :
forall x1 e1 A1 X1,
  lc_typ A1 ->
  x1 `notin` fvar_in_exp e1 ->
  subst_typ_in_exp A1 X1 (exp_abs e1) = exp_abs (close_exp_wrt_exp x1 (subst_typ_in_exp A1 X1 (open_exp_wrt_exp e1 (exp_var_f x1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_exp_abs : lngen.

Lemma subst_typ_in_exp_exp_abs_anno :
forall x1 A2 e1 A1 X1,
  lc_typ A1 ->
  x1 `notin` fvar_in_exp e1 ->
  subst_typ_in_exp A1 X1 (exp_abs_anno A2 e1) = exp_abs_anno (subst_typ_in_typ A1 X1 A2) (close_exp_wrt_exp x1 (subst_typ_in_exp A1 X1 (open_exp_wrt_exp e1 (exp_var_f x1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_exp_abs_anno : lngen.

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

Lemma subst_typ_in_typ_intro_rec_mutual :
(forall A1 X1 A2 n1,
  X1 `notin` ftvar_in_typ A1 ->
  open_typ_wrt_typ_rec n1 A2 A1 = subst_typ_in_typ A2 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_intro_rec :
forall A1 X1 A2 n1,
  X1 `notin` ftvar_in_typ A1 ->
  open_typ_wrt_typ_rec n1 A2 A1 = subst_typ_in_typ A2 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1).
Proof.
pose proof subst_typ_in_typ_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_intro_rec : lngen.
#[export] Hint Rewrite subst_typ_in_typ_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_bid_in_bid_intro_rec_mutual :
(forall D1 Xd1 D2 n1,
  Xd1 `notin` ftvar_in_bid D1 ->
  open_bid_wrt_bid_rec n1 D2 D1 = subst_bid_in_bid D2 Xd1 (open_bid_wrt_bid_rec n1 (bid_var_f Xd1) D1)).
Proof.
apply_mutual_ind bid_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_bid_in_bid_intro_rec :
forall D1 Xd1 D2 n1,
  Xd1 `notin` ftvar_in_bid D1 ->
  open_bid_wrt_bid_rec n1 D2 D1 = subst_bid_in_bid D2 Xd1 (open_bid_wrt_bid_rec n1 (bid_var_f Xd1) D1).
Proof.
pose proof subst_bid_in_bid_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_bid_in_bid_intro_rec : lngen.
#[export] Hint Rewrite subst_bid_in_bid_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_utyp_in_utyp_intro_rec_mutual :
(forall F1 Xf1 F2 n1,
  Xf1 `notin` ftvar_in_utyp F1 ->
  open_utyp_wrt_utyp_rec n1 F2 F1 = subst_utyp_in_utyp F2 Xf1 (open_utyp_wrt_utyp_rec n1 (utyp_var_f Xf1) F1)).
Proof.
apply_mutual_ind utyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_utyp_in_utyp_intro_rec :
forall F1 Xf1 F2 n1,
  Xf1 `notin` ftvar_in_utyp F1 ->
  open_utyp_wrt_utyp_rec n1 F2 F1 = subst_utyp_in_utyp F2 Xf1 (open_utyp_wrt_utyp_rec n1 (utyp_var_f Xf1) F1).
Proof.
pose proof subst_utyp_in_utyp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_intro_rec : lngen.
#[export] Hint Rewrite subst_utyp_in_utyp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_ctyp_in_ctyp_intro_rec_mutual :
(forall K1 U1 K2 n1,
  U1 `notin` ftvar_in_ctyp K1 ->
  open_ctyp_wrt_ctyp_rec n1 K2 K1 = subst_ctyp_in_ctyp K2 U1 (open_ctyp_wrt_ctyp_rec n1 (ctyp_var_f U1) K1)).
Proof.
apply_mutual_ind ctyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ctyp_in_ctyp_intro_rec :
forall K1 U1 K2 n1,
  U1 `notin` ftvar_in_ctyp K1 ->
  open_ctyp_wrt_ctyp_rec n1 K2 K1 = subst_ctyp_in_ctyp K2 U1 (open_ctyp_wrt_ctyp_rec n1 (ctyp_var_f U1) K1).
Proof.
pose proof subst_ctyp_in_ctyp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ctyp_in_ctyp_intro_rec : lngen.
#[export] Hint Rewrite subst_ctyp_in_ctyp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_skel_in_skel_intro_rec_mutual :
(forall R1 Xr1 R2 n1,
  Xr1 `notin` ftvar_in_skel R1 ->
  open_skel_wrt_skel_rec n1 R2 R1 = subst_skel_in_skel R2 Xr1 (open_skel_wrt_skel_rec n1 (skel_var_f Xr1) R1)).
Proof.
apply_mutual_ind skel_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_skel_in_skel_intro_rec :
forall R1 Xr1 R2 n1,
  Xr1 `notin` ftvar_in_skel R1 ->
  open_skel_wrt_skel_rec n1 R2 R1 = subst_skel_in_skel R2 Xr1 (open_skel_wrt_skel_rec n1 (skel_var_f Xr1) R1).
Proof.
pose proof subst_skel_in_skel_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_skel_in_skel_intro_rec : lngen.
#[export] Hint Rewrite subst_skel_in_skel_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_dbind_intro_rec_mutual :
(forall db1 X1 A1 n1,
  X1 `notin` ftvar_in_dbind db1 ->
  open_dbind_wrt_typ_rec n1 A1 db1 = subst_typ_in_dbind A1 X1 (open_dbind_wrt_typ_rec n1 (typ_var_f X1) db1)).
Proof.
apply_mutual_ind dbind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_dbind_intro_rec :
forall db1 X1 A1 n1,
  X1 `notin` ftvar_in_dbind db1 ->
  open_dbind_wrt_typ_rec n1 A1 db1 = subst_typ_in_dbind A1 X1 (open_dbind_wrt_typ_rec n1 (typ_var_f X1) db1).
Proof.
pose proof subst_typ_in_dbind_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_intro_rec : lngen.
#[export] Hint Rewrite subst_typ_in_dbind_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_intro_rec_mutual :
(forall e1 X1 A1 n1,
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = subst_typ_in_exp A1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_intro_rec :
forall e1 X1 A1 n1,
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = subst_typ_in_exp A1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1).
Proof.
pose proof subst_typ_in_exp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_intro_rec : lngen.
#[export] Hint Rewrite subst_typ_in_exp_intro_rec using solve [auto] : lngen.

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

Lemma subst_typ_in_typ_intro :
forall X1 A1 A2,
  X1 `notin` ftvar_in_typ A1 ->
  open_typ_wrt_typ A1 A2 = subst_typ_in_typ A2 X1 (open_typ_wrt_typ A1 (typ_var_f X1)).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_intro : lngen.

Lemma subst_bid_in_bid_intro :
forall Xd1 D1 D2,
  Xd1 `notin` ftvar_in_bid D1 ->
  open_bid_wrt_bid D1 D2 = subst_bid_in_bid D2 Xd1 (open_bid_wrt_bid D1 (bid_var_f Xd1)).
Proof.
unfold open_bid_wrt_bid; default_simp.
Qed.

#[export] Hint Resolve subst_bid_in_bid_intro : lngen.

Lemma subst_utyp_in_utyp_intro :
forall Xf1 F1 F2,
  Xf1 `notin` ftvar_in_utyp F1 ->
  open_utyp_wrt_utyp F1 F2 = subst_utyp_in_utyp F2 Xf1 (open_utyp_wrt_utyp F1 (utyp_var_f Xf1)).
Proof.
unfold open_utyp_wrt_utyp; default_simp.
Qed.

#[export] Hint Resolve subst_utyp_in_utyp_intro : lngen.

Lemma subst_ctyp_in_ctyp_intro :
forall U1 K1 K2,
  U1 `notin` ftvar_in_ctyp K1 ->
  open_ctyp_wrt_ctyp K1 K2 = subst_ctyp_in_ctyp K2 U1 (open_ctyp_wrt_ctyp K1 (ctyp_var_f U1)).
Proof.
unfold open_ctyp_wrt_ctyp; default_simp.
Qed.

#[export] Hint Resolve subst_ctyp_in_ctyp_intro : lngen.

Lemma subst_skel_in_skel_intro :
forall Xr1 R1 R2,
  Xr1 `notin` ftvar_in_skel R1 ->
  open_skel_wrt_skel R1 R2 = subst_skel_in_skel R2 Xr1 (open_skel_wrt_skel R1 (skel_var_f Xr1)).
Proof.
unfold open_skel_wrt_skel; default_simp.
Qed.

#[export] Hint Resolve subst_skel_in_skel_intro : lngen.

Lemma subst_typ_in_dbind_intro :
forall X1 db1 A1,
  X1 `notin` ftvar_in_dbind db1 ->
  open_dbind_wrt_typ db1 A1 = subst_typ_in_dbind A1 X1 (open_dbind_wrt_typ db1 (typ_var_f X1)).
Proof.
unfold open_dbind_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_dbind_intro : lngen.

Lemma subst_typ_in_exp_intro :
forall X1 e1 A1,
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_typ e1 A1 = subst_typ_in_exp A1 X1 (open_exp_wrt_typ e1 (typ_var_f X1)).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_intro : lngen.

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
