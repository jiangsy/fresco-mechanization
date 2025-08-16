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

Scheme pattern_ind' := Induction for pattern Sort Prop.

Combined Scheme pattern_mutind from pattern_ind'.

Scheme pattern_rec' := Induction for pattern Sort Set.

Combined Scheme pattern_mutrec from pattern_rec'.

Scheme bind_ind' := Induction for bind Sort Prop.

Combined Scheme bind_mutind from bind_ind'.

Scheme bind_rec' := Induction for bind Sort Set.

Combined Scheme bind_mutrec from bind_rec'.

Scheme exp_ind' := Induction for exp Sort Prop.

Combined Scheme exp_mutind from exp_ind'.

Scheme exp_rec' := Induction for exp Sort Set.

Combined Scheme exp_mutrec from exp_rec'.

Scheme pat_row_ind' := Induction for pat_row Sort Prop.

Combined Scheme pat_row_mutind from pat_row_ind'.

Scheme pat_row_rec' := Induction for pat_row Sort Set.

Combined Scheme pat_row_mutrec from pat_row_rec'.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_pattern_wrt_pattern_rec (n1 : nat) (X1 : typvar) (P1 : pattern) {struct P1} : pattern :=
  match P1 with
    | pattern_var_f X2 => if (X1 == X2) then (pattern_var_b n1) else (pattern_var_f X2)
    | pattern_var_b n2 => if (lt_ge_dec n2 n1) then (pattern_var_b n2) else (pattern_var_b (S n2))
    | pattern_arrow P2 Q1 => pattern_arrow (close_pattern_wrt_pattern_rec n1 X1 P2) (close_pattern_wrt_pattern_rec n1 X1 Q1)
    | pattern_all P2 => pattern_all (close_pattern_wrt_pattern_rec (S n1) X1 P2)
    | pattern_ghost => pattern_ghost
    | pattern_topghost P2 => pattern_topghost (close_pattern_wrt_pattern_rec n1 X1 P2)
  end.

Definition close_pattern_wrt_pattern X1 P1 := close_pattern_wrt_pattern_rec 0 X1 P1.

Fixpoint close_bind_wrt_pattern_rec (n1 : nat) (X1 : typvar) (b1 : bind) {struct b1} : bind :=
  match b1 with
    | bind_tvar_empty => bind_tvar_empty
    | bind_pattern A1 => bind_pattern (close_pattern_wrt_pattern_rec n1 X1 A1)
  end.

Definition close_bind_wrt_pattern X1 b1 := close_bind_wrt_pattern_rec 0 X1 b1.

Fixpoint close_exp_wrt_pattern_rec (n1 : nat) (X1 : typvar) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | exp_var_f x1 => exp_var_f x1
    | exp_var_b n2 => exp_var_b n2
    | exp_abs e2 => exp_abs (close_exp_wrt_pattern_rec n1 X1 e2)
    | exp_abs_anno A1 e2 => exp_abs_anno (close_pattern_wrt_pattern_rec n1 X1 A1) (close_exp_wrt_pattern_rec n1 X1 e2)
    | exp_app e2 e3 => exp_app (close_exp_wrt_pattern_rec n1 X1 e2) (close_exp_wrt_pattern_rec n1 X1 e3)
    | exp_let e2 e3 => exp_let (close_exp_wrt_pattern_rec n1 X1 e2) (close_exp_wrt_pattern_rec n1 X1 e3)
    | exp_anno e2 A1 => exp_anno (close_exp_wrt_pattern_rec n1 X1 e2) (close_pattern_wrt_pattern_rec n1 X1 A1)
    | exp_freeze e2 => exp_freeze (close_exp_wrt_pattern_rec n1 X1 e2)
  end.

Fixpoint close_exp_wrt_exp_rec (n1 : nat) (x1 : expvar) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | exp_var_f x2 => if (x1 == x2) then (exp_var_b n1) else (exp_var_f x2)
    | exp_var_b n2 => if (lt_ge_dec n2 n1) then (exp_var_b n2) else (exp_var_b (S n2))
    | exp_abs e2 => exp_abs (close_exp_wrt_exp_rec (S n1) x1 e2)
    | exp_abs_anno A1 e2 => exp_abs_anno A1 (close_exp_wrt_exp_rec (S n1) x1 e2)
    | exp_app e2 e3 => exp_app (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
    | exp_let e2 e3 => exp_let (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec (S n1) x1 e3)
    | exp_anno e2 A1 => exp_anno (close_exp_wrt_exp_rec n1 x1 e2) A1
    | exp_freeze e2 => exp_freeze (close_exp_wrt_exp_rec n1 x1 e2)
  end.

Definition close_exp_wrt_pattern X1 e1 := close_exp_wrt_pattern_rec 0 X1 e1.

Definition close_exp_wrt_exp x1 e1 := close_exp_wrt_exp_rec 0 x1 e1.

Fixpoint close_pat_row_wrt_pattern_rec (n1 : nat) (X1 : typvar) (p1 : pat_row) {struct p1} : pat_row :=
  match p1 with
    | pattern_row_nil => pattern_row_nil
    | pattern_row_cons P1 p2 => pattern_row_cons (close_pattern_wrt_pattern_rec n1 X1 P1) (close_pat_row_wrt_pattern_rec n1 X1 p2)
  end.

Definition close_pat_row_wrt_pattern X1 p1 := close_pat_row_wrt_pattern_rec 0 X1 p1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_pattern (P1 : pattern) {struct P1} : nat :=
  match P1 with
    | pattern_var_f X1 => 1
    | pattern_var_b n1 => 1
    | pattern_arrow P2 Q1 => 1 + (size_pattern P2) + (size_pattern Q1)
    | pattern_all P2 => 1 + (size_pattern P2)
    | pattern_ghost => 1
    | pattern_topghost P2 => 1 + (size_pattern P2)
  end.

Fixpoint size_bind (b1 : bind) {struct b1} : nat :=
  match b1 with
    | bind_tvar_empty => 1
    | bind_pattern A1 => 1 + (size_pattern A1)
  end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | exp_var_f x1 => 1
    | exp_var_b n1 => 1
    | exp_abs e2 => 1 + (size_exp e2)
    | exp_abs_anno A1 e2 => 1 + (size_pattern A1) + (size_exp e2)
    | exp_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | exp_let e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | exp_anno e2 A1 => 1 + (size_exp e2) + (size_pattern A1)
    | exp_freeze e2 => 1 + (size_exp e2)
  end.

Fixpoint size_pat_row (p1 : pat_row) {struct p1} : nat :=
  match p1 with
    | pattern_row_nil => 1
    | pattern_row_cons P1 p2 => 1 + (size_pattern P1) + (size_pat_row p2)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_pattern_wrt_pattern : nat -> pattern -> Prop :=
  | degree_wrt_pattern_pattern_var_f : forall n1 X1,
    degree_pattern_wrt_pattern n1 (pattern_var_f X1)
  | degree_wrt_pattern_pattern_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_pattern_wrt_pattern n1 (pattern_var_b n2)
  | degree_wrt_pattern_pattern_arrow : forall n1 P1 Q1,
    degree_pattern_wrt_pattern n1 P1 ->
    degree_pattern_wrt_pattern n1 Q1 ->
    degree_pattern_wrt_pattern n1 (pattern_arrow P1 Q1)
  | degree_wrt_pattern_pattern_all : forall n1 P1,
    degree_pattern_wrt_pattern (S n1) P1 ->
    degree_pattern_wrt_pattern n1 (pattern_all P1)
  | degree_wrt_pattern_pattern_ghost : forall n1,
    degree_pattern_wrt_pattern n1 (pattern_ghost)
  | degree_wrt_pattern_pattern_topghost : forall n1 P1,
    degree_pattern_wrt_pattern n1 P1 ->
    degree_pattern_wrt_pattern n1 (pattern_topghost P1).

Scheme degree_pattern_wrt_pattern_ind' := Induction for degree_pattern_wrt_pattern Sort Prop.

Combined Scheme degree_pattern_wrt_pattern_mutind from degree_pattern_wrt_pattern_ind'.

#[export] Hint Constructors degree_pattern_wrt_pattern : core lngen.

Inductive degree_bind_wrt_pattern : nat -> bind -> Prop :=
  | degree_wrt_pattern_bind_tvar_empty : forall n1,
    degree_bind_wrt_pattern n1 (bind_tvar_empty)
  | degree_wrt_pattern_bind_pattern : forall n1 A1,
    degree_pattern_wrt_pattern n1 A1 ->
    degree_bind_wrt_pattern n1 (bind_pattern A1).

Scheme degree_bind_wrt_pattern_ind' := Induction for degree_bind_wrt_pattern Sort Prop.

Combined Scheme degree_bind_wrt_pattern_mutind from degree_bind_wrt_pattern_ind'.

#[export] Hint Constructors degree_bind_wrt_pattern : core lngen.

Inductive degree_exp_wrt_pattern : nat -> exp -> Prop :=
  | degree_wrt_pattern_exp_var_f : forall n1 x1,
    degree_exp_wrt_pattern n1 (exp_var_f x1)
  | degree_wrt_pattern_exp_var_b : forall n1 n2,
    degree_exp_wrt_pattern n1 (exp_var_b n2)
  | degree_wrt_pattern_exp_abs : forall n1 e1,
    degree_exp_wrt_pattern n1 e1 ->
    degree_exp_wrt_pattern n1 (exp_abs e1)
  | degree_wrt_pattern_exp_abs_anno : forall n1 A1 e1,
    degree_pattern_wrt_pattern n1 A1 ->
    degree_exp_wrt_pattern n1 e1 ->
    degree_exp_wrt_pattern n1 (exp_abs_anno A1 e1)
  | degree_wrt_pattern_exp_app : forall n1 e1 e2,
    degree_exp_wrt_pattern n1 e1 ->
    degree_exp_wrt_pattern n1 e2 ->
    degree_exp_wrt_pattern n1 (exp_app e1 e2)
  | degree_wrt_pattern_exp_let : forall n1 e1 e2,
    degree_exp_wrt_pattern n1 e1 ->
    degree_exp_wrt_pattern n1 e2 ->
    degree_exp_wrt_pattern n1 (exp_let e1 e2)
  | degree_wrt_pattern_exp_anno : forall n1 e1 A1,
    degree_exp_wrt_pattern n1 e1 ->
    degree_pattern_wrt_pattern n1 A1 ->
    degree_exp_wrt_pattern n1 (exp_anno e1 A1)
  | degree_wrt_pattern_exp_freeze : forall n1 e1,
    degree_exp_wrt_pattern n1 e1 ->
    degree_exp_wrt_pattern n1 (exp_freeze e1).

Inductive degree_exp_wrt_exp : nat -> exp -> Prop :=
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
  | degree_wrt_exp_exp_let : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp (S n1) e2 ->
    degree_exp_wrt_exp n1 (exp_let e1 e2)
  | degree_wrt_exp_exp_anno : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_anno e1 A1)
  | degree_wrt_exp_exp_freeze : forall n1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_freeze e1).

Scheme degree_exp_wrt_pattern_ind' := Induction for degree_exp_wrt_pattern Sort Prop.

Combined Scheme degree_exp_wrt_pattern_mutind from degree_exp_wrt_pattern_ind'.

Scheme degree_exp_wrt_exp_ind' := Induction for degree_exp_wrt_exp Sort Prop.

Combined Scheme degree_exp_wrt_exp_mutind from degree_exp_wrt_exp_ind'.

#[export] Hint Constructors degree_exp_wrt_pattern : core lngen.

#[export] Hint Constructors degree_exp_wrt_exp : core lngen.

Inductive degree_pat_row_wrt_pattern : nat -> pat_row -> Prop :=
  | degree_wrt_pattern_pattern_row_nil : forall n1,
    degree_pat_row_wrt_pattern n1 (pattern_row_nil)
  | degree_wrt_pattern_pattern_row_cons : forall n1 P1 p1,
    degree_pattern_wrt_pattern n1 P1 ->
    degree_pat_row_wrt_pattern n1 p1 ->
    degree_pat_row_wrt_pattern n1 (pattern_row_cons P1 p1).

Scheme degree_pat_row_wrt_pattern_ind' := Induction for degree_pat_row_wrt_pattern Sort Prop.

Combined Scheme degree_pat_row_wrt_pattern_mutind from degree_pat_row_wrt_pattern_ind'.

#[export] Hint Constructors degree_pat_row_wrt_pattern : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_pattern : pattern -> Set :=
  | lc_set_pattern_var_f : forall X1,
    lc_set_pattern (pattern_var_f X1)
  | lc_set_pattern_arrow : forall P1 Q1,
    lc_set_pattern P1 ->
    lc_set_pattern Q1 ->
    lc_set_pattern (pattern_arrow P1 Q1)
  | lc_set_pattern_all : forall P1,
    (forall X1 : typvar, lc_set_pattern (open_pattern_wrt_pattern P1 (pattern_var_f X1))) ->
    lc_set_pattern (pattern_all P1)
  | lc_set_pattern_ghost :
    lc_set_pattern (pattern_ghost)
  | lc_set_pattern_topghost : forall P1,
    lc_set_pattern P1 ->
    lc_set_pattern (pattern_topghost P1).
Scheme lc_pattern_ind' := Induction for lc_pattern Sort Prop.

Combined Scheme lc_pattern_mutind from lc_pattern_ind'.

Scheme lc_set_pattern_ind' := Induction for lc_set_pattern Sort Prop.

Combined Scheme lc_set_pattern_mutind from lc_set_pattern_ind'.

Scheme lc_set_pattern_rec' := Induction for lc_set_pattern Sort Set.

Combined Scheme lc_set_pattern_mutrec from lc_set_pattern_rec'.

#[export] Hint Constructors lc_pattern : core lngen.

#[export] Hint Constructors lc_set_pattern : core lngen.

Inductive lc_set_bind : bind -> Set :=
  | lc_set_bind_tvar_empty :
    lc_set_bind (bind_tvar_empty)
  | lc_set_bind_pattern : forall A1,
    lc_set_pattern A1 ->
    lc_set_bind (bind_pattern A1).
Scheme lc_bind_ind' := Induction for lc_bind Sort Prop.

Combined Scheme lc_bind_mutind from lc_bind_ind'.

Scheme lc_set_bind_ind' := Induction for lc_set_bind Sort Prop.

Combined Scheme lc_set_bind_mutind from lc_set_bind_ind'.

Scheme lc_set_bind_rec' := Induction for lc_set_bind Sort Set.

Combined Scheme lc_set_bind_mutrec from lc_set_bind_rec'.

#[export] Hint Constructors lc_bind : core lngen.

#[export] Hint Constructors lc_set_bind : core lngen.

Inductive lc_set_exp : exp -> Set :=
  | lc_set_exp_var_f : forall x1,
    lc_set_exp (exp_var_f x1)
  | lc_set_exp_abs : forall e1,
    (forall x1 : expvar, lc_set_exp (open_exp_wrt_exp e1 (exp_var_f x1))) ->
    lc_set_exp (exp_abs e1)
  | lc_set_exp_abs_anno : forall A1 e1,
    lc_set_pattern A1 ->
    (forall x1 : expvar, lc_set_exp (open_exp_wrt_exp e1 (exp_var_f x1))) ->
    lc_set_exp (exp_abs_anno A1 e1)
  | lc_set_exp_app : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (exp_app e1 e2)
  | lc_set_exp_let : forall e1 e2,
    lc_set_exp e1 ->
    (forall x1 : expvar, lc_set_exp (open_exp_wrt_exp e2 (exp_var_f x1))) ->
    lc_set_exp (exp_let e1 e2)
  | lc_set_exp_anno : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_pattern A1 ->
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

Inductive lc_set_pat_row : pat_row -> Set :=
  | lc_set_pattern_row_nil :
    lc_set_pat_row (pattern_row_nil)
  | lc_set_pattern_row_cons : forall P1 p1,
    lc_set_pattern P1 ->
    lc_set_pat_row p1 ->
    lc_set_pat_row (pattern_row_cons P1 p1).
Scheme lc_pat_row_ind' := Induction for lc_pat_row Sort Prop.

Combined Scheme lc_pat_row_mutind from lc_pat_row_ind'.

Scheme lc_set_pat_row_ind' := Induction for lc_set_pat_row Sort Prop.

Combined Scheme lc_set_pat_row_mutind from lc_set_pat_row_ind'.

Scheme lc_set_pat_row_rec' := Induction for lc_set_pat_row Sort Set.

Combined Scheme lc_set_pat_row_mutrec from lc_set_pat_row_rec'.

#[export] Hint Constructors lc_pat_row : core lngen.

#[export] Hint Constructors lc_set_pat_row : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_pattern_wrt_pattern P1 := forall X1, lc_pattern (open_pattern_wrt_pattern P1 (pattern_var_f X1)).

#[export] Hint Unfold body_pattern_wrt_pattern : core.

Definition body_bind_wrt_pattern b1 := forall X1, lc_bind (open_bind_wrt_pattern b1 (pattern_var_f X1)).

#[export] Hint Unfold body_bind_wrt_pattern : core.

Definition body_exp_wrt_pattern e1 := forall X1, lc_exp (open_exp_wrt_pattern e1 (pattern_var_f X1)).

Definition body_exp_wrt_exp e1 := forall x1, lc_exp (open_exp_wrt_exp e1 (exp_var_f x1)).

#[export] Hint Unfold body_exp_wrt_pattern : core.

#[export] Hint Unfold body_exp_wrt_exp : core.

Definition body_pat_row_wrt_pattern p1 := forall X1, lc_pat_row (open_pat_row_wrt_pattern p1 (pattern_var_f X1)).

#[export] Hint Unfold body_pat_row_wrt_pattern : core.


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

Lemma size_pattern_min_mutual :
(forall P1, 1 <= size_pattern P1).
Proof.
apply_mutual_ind pattern_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_pattern_min :
forall P1, 1 <= size_pattern P1.
Proof.
pose proof size_pattern_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_pattern_min : lngen.

(* begin hide *)

Lemma size_bind_min_mutual :
(forall b1, 1 <= size_bind b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_bind_min :
forall b1, 1 <= size_bind b1.
Proof.
pose proof size_bind_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_bind_min : lngen.

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

Lemma size_pat_row_min_mutual :
(forall p1, 1 <= size_pat_row p1).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_pat_row_min :
forall p1, 1 <= size_pat_row p1.
Proof.
pose proof size_pat_row_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_pat_row_min : lngen.

(* begin hide *)

Lemma size_pattern_close_pattern_wrt_pattern_rec_mutual :
(forall P1 X1 n1,
  size_pattern (close_pattern_wrt_pattern_rec n1 X1 P1) = size_pattern P1).
Proof.
apply_mutual_ind pattern_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_pattern_close_pattern_wrt_pattern_rec :
forall P1 X1 n1,
  size_pattern (close_pattern_wrt_pattern_rec n1 X1 P1) = size_pattern P1.
Proof.
pose proof size_pattern_close_pattern_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_pattern_close_pattern_wrt_pattern_rec : lngen.
#[export] Hint Rewrite size_pattern_close_pattern_wrt_pattern_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_bind_close_bind_wrt_pattern_rec_mutual :
(forall b1 X1 n1,
  size_bind (close_bind_wrt_pattern_rec n1 X1 b1) = size_bind b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_bind_close_bind_wrt_pattern_rec :
forall b1 X1 n1,
  size_bind (close_bind_wrt_pattern_rec n1 X1 b1) = size_bind b1.
Proof.
pose proof size_bind_close_bind_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_bind_close_bind_wrt_pattern_rec : lngen.
#[export] Hint Rewrite size_bind_close_bind_wrt_pattern_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_pattern_rec_mutual :
(forall e1 X1 n1,
  size_exp (close_exp_wrt_pattern_rec n1 X1 e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_pattern_rec :
forall e1 X1 n1,
  size_exp (close_exp_wrt_pattern_rec n1 X1 e1) = size_exp e1.
Proof.
pose proof size_exp_close_exp_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_pattern_rec : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_pattern_rec using solve [auto] : lngen.

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

(* begin hide *)

Lemma size_pat_row_close_pat_row_wrt_pattern_rec_mutual :
(forall p1 X1 n1,
  size_pat_row (close_pat_row_wrt_pattern_rec n1 X1 p1) = size_pat_row p1).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_pat_row_close_pat_row_wrt_pattern_rec :
forall p1 X1 n1,
  size_pat_row (close_pat_row_wrt_pattern_rec n1 X1 p1) = size_pat_row p1.
Proof.
pose proof size_pat_row_close_pat_row_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_pat_row_close_pat_row_wrt_pattern_rec : lngen.
#[export] Hint Rewrite size_pat_row_close_pat_row_wrt_pattern_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_pattern_close_pattern_wrt_pattern :
forall P1 X1,
  size_pattern (close_pattern_wrt_pattern X1 P1) = size_pattern P1.
Proof.
unfold close_pattern_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve size_pattern_close_pattern_wrt_pattern : lngen.
#[export] Hint Rewrite size_pattern_close_pattern_wrt_pattern using solve [auto] : lngen.

Lemma size_bind_close_bind_wrt_pattern :
forall b1 X1,
  size_bind (close_bind_wrt_pattern X1 b1) = size_bind b1.
Proof.
unfold close_bind_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve size_bind_close_bind_wrt_pattern : lngen.
#[export] Hint Rewrite size_bind_close_bind_wrt_pattern using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_pattern :
forall e1 X1,
  size_exp (close_exp_wrt_pattern X1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_pattern : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_pattern using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_exp :
forall e1 x1,
  size_exp (close_exp_wrt_exp x1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma size_pat_row_close_pat_row_wrt_pattern :
forall p1 X1,
  size_pat_row (close_pat_row_wrt_pattern X1 p1) = size_pat_row p1.
Proof.
unfold close_pat_row_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve size_pat_row_close_pat_row_wrt_pattern : lngen.
#[export] Hint Rewrite size_pat_row_close_pat_row_wrt_pattern using solve [auto] : lngen.

(* begin hide *)

Lemma size_pattern_open_pattern_wrt_pattern_rec_mutual :
(forall P1 P2 n1,
  size_pattern P1 <= size_pattern (open_pattern_wrt_pattern_rec n1 P2 P1)).
Proof.
apply_mutual_ind pattern_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_pattern_open_pattern_wrt_pattern_rec :
forall P1 P2 n1,
  size_pattern P1 <= size_pattern (open_pattern_wrt_pattern_rec n1 P2 P1).
Proof.
pose proof size_pattern_open_pattern_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_pattern_open_pattern_wrt_pattern_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_bind_open_bind_wrt_pattern_rec_mutual :
(forall b1 P1 n1,
  size_bind b1 <= size_bind (open_bind_wrt_pattern_rec n1 P1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_bind_open_bind_wrt_pattern_rec :
forall b1 P1 n1,
  size_bind b1 <= size_bind (open_bind_wrt_pattern_rec n1 P1 b1).
Proof.
pose proof size_bind_open_bind_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_bind_open_bind_wrt_pattern_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_pattern_rec_mutual :
(forall e1 P1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_pattern_rec n1 P1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_pattern_rec :
forall e1 P1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_pattern_rec n1 P1 e1).
Proof.
pose proof size_exp_open_exp_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_pattern_rec : lngen.

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

(* begin hide *)

Lemma size_pat_row_open_pat_row_wrt_pattern_rec_mutual :
(forall p1 P1 n1,
  size_pat_row p1 <= size_pat_row (open_pat_row_wrt_pattern_rec n1 P1 p1)).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_pat_row_open_pat_row_wrt_pattern_rec :
forall p1 P1 n1,
  size_pat_row p1 <= size_pat_row (open_pat_row_wrt_pattern_rec n1 P1 p1).
Proof.
pose proof size_pat_row_open_pat_row_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_pat_row_open_pat_row_wrt_pattern_rec : lngen.

(* end hide *)

Lemma size_pattern_open_pattern_wrt_pattern :
forall P1 P2,
  size_pattern P1 <= size_pattern (open_pattern_wrt_pattern P1 P2).
Proof.
unfold open_pattern_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve size_pattern_open_pattern_wrt_pattern : lngen.

Lemma size_bind_open_bind_wrt_pattern :
forall b1 P1,
  size_bind b1 <= size_bind (open_bind_wrt_pattern b1 P1).
Proof.
unfold open_bind_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve size_bind_open_bind_wrt_pattern : lngen.

Lemma size_exp_open_exp_wrt_pattern :
forall e1 P1,
  size_exp e1 <= size_exp (open_exp_wrt_pattern e1 P1).
Proof.
unfold open_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_pattern : lngen.

Lemma size_exp_open_exp_wrt_exp :
forall e1 e2,
  size_exp e1 <= size_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_exp : lngen.

Lemma size_pat_row_open_pat_row_wrt_pattern :
forall p1 P1,
  size_pat_row p1 <= size_pat_row (open_pat_row_wrt_pattern p1 P1).
Proof.
unfold open_pat_row_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve size_pat_row_open_pat_row_wrt_pattern : lngen.

(* begin hide *)

Lemma size_pattern_open_pattern_wrt_pattern_rec_var_mutual :
(forall P1 X1 n1,
  size_pattern (open_pattern_wrt_pattern_rec n1 (pattern_var_f X1) P1) = size_pattern P1).
Proof.
apply_mutual_ind pattern_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_pattern_open_pattern_wrt_pattern_rec_var :
forall P1 X1 n1,
  size_pattern (open_pattern_wrt_pattern_rec n1 (pattern_var_f X1) P1) = size_pattern P1.
Proof.
pose proof size_pattern_open_pattern_wrt_pattern_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_pattern_open_pattern_wrt_pattern_rec_var : lngen.
#[export] Hint Rewrite size_pattern_open_pattern_wrt_pattern_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_bind_open_bind_wrt_pattern_rec_var_mutual :
(forall b1 X1 n1,
  size_bind (open_bind_wrt_pattern_rec n1 (pattern_var_f X1) b1) = size_bind b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_bind_open_bind_wrt_pattern_rec_var :
forall b1 X1 n1,
  size_bind (open_bind_wrt_pattern_rec n1 (pattern_var_f X1) b1) = size_bind b1.
Proof.
pose proof size_bind_open_bind_wrt_pattern_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_bind_open_bind_wrt_pattern_rec_var : lngen.
#[export] Hint Rewrite size_bind_open_bind_wrt_pattern_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_pattern_rec_var_mutual :
(forall e1 X1 n1,
  size_exp (open_exp_wrt_pattern_rec n1 (pattern_var_f X1) e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_pattern_rec_var :
forall e1 X1 n1,
  size_exp (open_exp_wrt_pattern_rec n1 (pattern_var_f X1) e1) = size_exp e1.
Proof.
pose proof size_exp_open_exp_wrt_pattern_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_pattern_rec_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_pattern_rec_var using solve [auto] : lngen.

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

(* begin hide *)

Lemma size_pat_row_open_pat_row_wrt_pattern_rec_var_mutual :
(forall p1 X1 n1,
  size_pat_row (open_pat_row_wrt_pattern_rec n1 (pattern_var_f X1) p1) = size_pat_row p1).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_pat_row_open_pat_row_wrt_pattern_rec_var :
forall p1 X1 n1,
  size_pat_row (open_pat_row_wrt_pattern_rec n1 (pattern_var_f X1) p1) = size_pat_row p1.
Proof.
pose proof size_pat_row_open_pat_row_wrt_pattern_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_pat_row_open_pat_row_wrt_pattern_rec_var : lngen.
#[export] Hint Rewrite size_pat_row_open_pat_row_wrt_pattern_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_pattern_open_pattern_wrt_pattern_var :
forall P1 X1,
  size_pattern (open_pattern_wrt_pattern P1 (pattern_var_f X1)) = size_pattern P1.
Proof.
unfold open_pattern_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve size_pattern_open_pattern_wrt_pattern_var : lngen.
#[export] Hint Rewrite size_pattern_open_pattern_wrt_pattern_var using solve [auto] : lngen.

Lemma size_bind_open_bind_wrt_pattern_var :
forall b1 X1,
  size_bind (open_bind_wrt_pattern b1 (pattern_var_f X1)) = size_bind b1.
Proof.
unfold open_bind_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve size_bind_open_bind_wrt_pattern_var : lngen.
#[export] Hint Rewrite size_bind_open_bind_wrt_pattern_var using solve [auto] : lngen.

Lemma size_exp_open_exp_wrt_pattern_var :
forall e1 X1,
  size_exp (open_exp_wrt_pattern e1 (pattern_var_f X1)) = size_exp e1.
Proof.
unfold open_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_pattern_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_pattern_var using solve [auto] : lngen.

Lemma size_exp_open_exp_wrt_exp_var :
forall e1 x1,
  size_exp (open_exp_wrt_exp e1 (exp_var_f x1)) = size_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_exp_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_exp_var using solve [auto] : lngen.

Lemma size_pat_row_open_pat_row_wrt_pattern_var :
forall p1 X1,
  size_pat_row (open_pat_row_wrt_pattern p1 (pattern_var_f X1)) = size_pat_row p1.
Proof.
unfold open_pat_row_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve size_pat_row_open_pat_row_wrt_pattern_var : lngen.
#[export] Hint Rewrite size_pat_row_open_pat_row_wrt_pattern_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_pattern_wrt_pattern_S_mutual :
(forall n1 P1,
  degree_pattern_wrt_pattern n1 P1 ->
  degree_pattern_wrt_pattern (S n1) P1).
Proof.
apply_mutual_ind degree_pattern_wrt_pattern_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_pattern_wrt_pattern_S :
forall n1 P1,
  degree_pattern_wrt_pattern n1 P1 ->
  degree_pattern_wrt_pattern (S n1) P1.
Proof.
pose proof degree_pattern_wrt_pattern_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_pattern_wrt_pattern_S : lngen.

(* begin hide *)

Lemma degree_bind_wrt_pattern_S_mutual :
(forall n1 b1,
  degree_bind_wrt_pattern n1 b1 ->
  degree_bind_wrt_pattern (S n1) b1).
Proof.
apply_mutual_ind degree_bind_wrt_pattern_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_bind_wrt_pattern_S :
forall n1 b1,
  degree_bind_wrt_pattern n1 b1 ->
  degree_bind_wrt_pattern (S n1) b1.
Proof.
pose proof degree_bind_wrt_pattern_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_bind_wrt_pattern_S : lngen.

(* begin hide *)

Lemma degree_exp_wrt_pattern_S_mutual :
(forall n1 e1,
  degree_exp_wrt_pattern n1 e1 ->
  degree_exp_wrt_pattern (S n1) e1).
Proof.
apply_mutual_ind degree_exp_wrt_pattern_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_exp_wrt_pattern_S :
forall n1 e1,
  degree_exp_wrt_pattern n1 e1 ->
  degree_exp_wrt_pattern (S n1) e1.
Proof.
pose proof degree_exp_wrt_pattern_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_pattern_S : lngen.

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

(* begin hide *)

Lemma degree_pat_row_wrt_pattern_S_mutual :
(forall n1 p1,
  degree_pat_row_wrt_pattern n1 p1 ->
  degree_pat_row_wrt_pattern (S n1) p1).
Proof.
apply_mutual_ind degree_pat_row_wrt_pattern_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_pat_row_wrt_pattern_S :
forall n1 p1,
  degree_pat_row_wrt_pattern n1 p1 ->
  degree_pat_row_wrt_pattern (S n1) p1.
Proof.
pose proof degree_pat_row_wrt_pattern_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_pat_row_wrt_pattern_S : lngen.

Lemma degree_pattern_wrt_pattern_O :
forall n1 P1,
  degree_pattern_wrt_pattern O P1 ->
  degree_pattern_wrt_pattern n1 P1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_pattern_wrt_pattern_O : lngen.

Lemma degree_bind_wrt_pattern_O :
forall n1 b1,
  degree_bind_wrt_pattern O b1 ->
  degree_bind_wrt_pattern n1 b1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_bind_wrt_pattern_O : lngen.

Lemma degree_exp_wrt_pattern_O :
forall n1 e1,
  degree_exp_wrt_pattern O e1 ->
  degree_exp_wrt_pattern n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_pattern_O : lngen.

Lemma degree_exp_wrt_exp_O :
forall n1 e1,
  degree_exp_wrt_exp O e1 ->
  degree_exp_wrt_exp n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_O : lngen.

Lemma degree_pat_row_wrt_pattern_O :
forall n1 p1,
  degree_pat_row_wrt_pattern O p1 ->
  degree_pat_row_wrt_pattern n1 p1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_pat_row_wrt_pattern_O : lngen.

(* begin hide *)

Lemma degree_pattern_wrt_pattern_close_pattern_wrt_pattern_rec_mutual :
(forall P1 X1 n1,
  degree_pattern_wrt_pattern n1 P1 ->
  degree_pattern_wrt_pattern (S n1) (close_pattern_wrt_pattern_rec n1 X1 P1)).
Proof.
apply_mutual_ind pattern_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_pattern_wrt_pattern_close_pattern_wrt_pattern_rec :
forall P1 X1 n1,
  degree_pattern_wrt_pattern n1 P1 ->
  degree_pattern_wrt_pattern (S n1) (close_pattern_wrt_pattern_rec n1 X1 P1).
Proof.
pose proof degree_pattern_wrt_pattern_close_pattern_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_pattern_wrt_pattern_close_pattern_wrt_pattern_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_bind_wrt_pattern_close_bind_wrt_pattern_rec_mutual :
(forall b1 X1 n1,
  degree_bind_wrt_pattern n1 b1 ->
  degree_bind_wrt_pattern (S n1) (close_bind_wrt_pattern_rec n1 X1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_bind_wrt_pattern_close_bind_wrt_pattern_rec :
forall b1 X1 n1,
  degree_bind_wrt_pattern n1 b1 ->
  degree_bind_wrt_pattern (S n1) (close_bind_wrt_pattern_rec n1 X1 b1).
Proof.
pose proof degree_bind_wrt_pattern_close_bind_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_bind_wrt_pattern_close_bind_wrt_pattern_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_pattern_close_exp_wrt_pattern_rec_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_pattern n1 e1 ->
  degree_exp_wrt_pattern (S n1) (close_exp_wrt_pattern_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_pattern_close_exp_wrt_pattern_rec :
forall e1 X1 n1,
  degree_exp_wrt_pattern n1 e1 ->
  degree_exp_wrt_pattern (S n1) (close_exp_wrt_pattern_rec n1 X1 e1).
Proof.
pose proof degree_exp_wrt_pattern_close_exp_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_pattern_close_exp_wrt_pattern_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_pattern_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_pattern n2 e1 ->
  degree_exp_wrt_pattern n2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_pattern_close_exp_wrt_exp_rec :
forall e1 x1 n1 n2,
  degree_exp_wrt_pattern n2 e1 ->
  degree_exp_wrt_pattern n2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof degree_exp_wrt_pattern_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_pattern_close_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_pattern_rec_mutual :
(forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_pattern_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_pattern_rec :
forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_pattern_rec n1 X1 e1).
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_pattern_rec : lngen.

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

(* begin hide *)

Lemma degree_pat_row_wrt_pattern_close_pat_row_wrt_pattern_rec_mutual :
(forall p1 X1 n1,
  degree_pat_row_wrt_pattern n1 p1 ->
  degree_pat_row_wrt_pattern (S n1) (close_pat_row_wrt_pattern_rec n1 X1 p1)).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_pat_row_wrt_pattern_close_pat_row_wrt_pattern_rec :
forall p1 X1 n1,
  degree_pat_row_wrt_pattern n1 p1 ->
  degree_pat_row_wrt_pattern (S n1) (close_pat_row_wrt_pattern_rec n1 X1 p1).
Proof.
pose proof degree_pat_row_wrt_pattern_close_pat_row_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_pat_row_wrt_pattern_close_pat_row_wrt_pattern_rec : lngen.

(* end hide *)

Lemma degree_pattern_wrt_pattern_close_pattern_wrt_pattern :
forall P1 X1,
  degree_pattern_wrt_pattern 0 P1 ->
  degree_pattern_wrt_pattern 1 (close_pattern_wrt_pattern X1 P1).
Proof.
unfold close_pattern_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve degree_pattern_wrt_pattern_close_pattern_wrt_pattern : lngen.

Lemma degree_bind_wrt_pattern_close_bind_wrt_pattern :
forall b1 X1,
  degree_bind_wrt_pattern 0 b1 ->
  degree_bind_wrt_pattern 1 (close_bind_wrt_pattern X1 b1).
Proof.
unfold close_bind_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve degree_bind_wrt_pattern_close_bind_wrt_pattern : lngen.

Lemma degree_exp_wrt_pattern_close_exp_wrt_pattern :
forall e1 X1,
  degree_exp_wrt_pattern 0 e1 ->
  degree_exp_wrt_pattern 1 (close_exp_wrt_pattern X1 e1).
Proof.
unfold close_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_pattern_close_exp_wrt_pattern : lngen.

Lemma degree_exp_wrt_pattern_close_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_pattern n1 e1 ->
  degree_exp_wrt_pattern n1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_pattern_close_exp_wrt_exp : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_pattern :
forall e1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (close_exp_wrt_pattern X1 e1).
Proof.
unfold close_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_pattern : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  degree_exp_wrt_exp 0 e1 ->
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp : lngen.

Lemma degree_pat_row_wrt_pattern_close_pat_row_wrt_pattern :
forall p1 X1,
  degree_pat_row_wrt_pattern 0 p1 ->
  degree_pat_row_wrt_pattern 1 (close_pat_row_wrt_pattern X1 p1).
Proof.
unfold close_pat_row_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve degree_pat_row_wrt_pattern_close_pat_row_wrt_pattern : lngen.

(* begin hide *)

Lemma degree_pattern_wrt_pattern_close_pattern_wrt_pattern_rec_inv_mutual :
(forall P1 X1 n1,
  degree_pattern_wrt_pattern (S n1) (close_pattern_wrt_pattern_rec n1 X1 P1) ->
  degree_pattern_wrt_pattern n1 P1).
Proof.
apply_mutual_ind pattern_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_pattern_wrt_pattern_close_pattern_wrt_pattern_rec_inv :
forall P1 X1 n1,
  degree_pattern_wrt_pattern (S n1) (close_pattern_wrt_pattern_rec n1 X1 P1) ->
  degree_pattern_wrt_pattern n1 P1.
Proof.
pose proof degree_pattern_wrt_pattern_close_pattern_wrt_pattern_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_pattern_wrt_pattern_close_pattern_wrt_pattern_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_bind_wrt_pattern_close_bind_wrt_pattern_rec_inv_mutual :
(forall b1 X1 n1,
  degree_bind_wrt_pattern (S n1) (close_bind_wrt_pattern_rec n1 X1 b1) ->
  degree_bind_wrt_pattern n1 b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_bind_wrt_pattern_close_bind_wrt_pattern_rec_inv :
forall b1 X1 n1,
  degree_bind_wrt_pattern (S n1) (close_bind_wrt_pattern_rec n1 X1 b1) ->
  degree_bind_wrt_pattern n1 b1.
Proof.
pose proof degree_bind_wrt_pattern_close_bind_wrt_pattern_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_bind_wrt_pattern_close_bind_wrt_pattern_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_pattern_close_exp_wrt_pattern_rec_inv_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_pattern (S n1) (close_exp_wrt_pattern_rec n1 X1 e1) ->
  degree_exp_wrt_pattern n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_pattern_close_exp_wrt_pattern_rec_inv :
forall e1 X1 n1,
  degree_exp_wrt_pattern (S n1) (close_exp_wrt_pattern_rec n1 X1 e1) ->
  degree_exp_wrt_pattern n1 e1.
Proof.
pose proof degree_exp_wrt_pattern_close_exp_wrt_pattern_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_pattern_close_exp_wrt_pattern_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_pattern_close_exp_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_pattern n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_pattern n2 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_pattern_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1 n2,
  degree_exp_wrt_pattern n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_pattern n2 e1.
Proof.
pose proof degree_exp_wrt_pattern_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_pattern_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_pattern_rec_inv_mutual :
(forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_pattern_rec n1 X1 e1) ->
  degree_exp_wrt_exp n2 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_pattern_rec_inv :
forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_pattern_rec n1 X1 e1) ->
  degree_exp_wrt_exp n2 e1.
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_pattern_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_pattern_rec_inv : lngen.

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

(* begin hide *)

Lemma degree_pat_row_wrt_pattern_close_pat_row_wrt_pattern_rec_inv_mutual :
(forall p1 X1 n1,
  degree_pat_row_wrt_pattern (S n1) (close_pat_row_wrt_pattern_rec n1 X1 p1) ->
  degree_pat_row_wrt_pattern n1 p1).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_pat_row_wrt_pattern_close_pat_row_wrt_pattern_rec_inv :
forall p1 X1 n1,
  degree_pat_row_wrt_pattern (S n1) (close_pat_row_wrt_pattern_rec n1 X1 p1) ->
  degree_pat_row_wrt_pattern n1 p1.
Proof.
pose proof degree_pat_row_wrt_pattern_close_pat_row_wrt_pattern_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_pat_row_wrt_pattern_close_pat_row_wrt_pattern_rec_inv : lngen.

(* end hide *)

Lemma degree_pattern_wrt_pattern_close_pattern_wrt_pattern_inv :
forall P1 X1,
  degree_pattern_wrt_pattern 1 (close_pattern_wrt_pattern X1 P1) ->
  degree_pattern_wrt_pattern 0 P1.
Proof.
unfold close_pattern_wrt_pattern; eauto with lngen.
Qed.

#[export] Hint Immediate degree_pattern_wrt_pattern_close_pattern_wrt_pattern_inv : lngen.

Lemma degree_bind_wrt_pattern_close_bind_wrt_pattern_inv :
forall b1 X1,
  degree_bind_wrt_pattern 1 (close_bind_wrt_pattern X1 b1) ->
  degree_bind_wrt_pattern 0 b1.
Proof.
unfold close_bind_wrt_pattern; eauto with lngen.
Qed.

#[export] Hint Immediate degree_bind_wrt_pattern_close_bind_wrt_pattern_inv : lngen.

Lemma degree_exp_wrt_pattern_close_exp_wrt_pattern_inv :
forall e1 X1,
  degree_exp_wrt_pattern 1 (close_exp_wrt_pattern X1 e1) ->
  degree_exp_wrt_pattern 0 e1.
Proof.
unfold close_exp_wrt_pattern; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_pattern_close_exp_wrt_pattern_inv : lngen.

Lemma degree_exp_wrt_pattern_close_exp_wrt_exp_inv :
forall e1 x1 n1,
  degree_exp_wrt_pattern n1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_pattern n1 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_pattern_close_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_pattern_inv :
forall e1 X1 n1,
  degree_exp_wrt_exp n1 (close_exp_wrt_pattern X1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
unfold close_exp_wrt_pattern; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_pattern_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_inv :
forall e1 x1,
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_exp 0 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_inv : lngen.

Lemma degree_pat_row_wrt_pattern_close_pat_row_wrt_pattern_inv :
forall p1 X1,
  degree_pat_row_wrt_pattern 1 (close_pat_row_wrt_pattern X1 p1) ->
  degree_pat_row_wrt_pattern 0 p1.
Proof.
unfold close_pat_row_wrt_pattern; eauto with lngen.
Qed.

#[export] Hint Immediate degree_pat_row_wrt_pattern_close_pat_row_wrt_pattern_inv : lngen.

(* begin hide *)

Lemma degree_pattern_wrt_pattern_open_pattern_wrt_pattern_rec_mutual :
(forall P1 P2 n1,
  degree_pattern_wrt_pattern (S n1) P1 ->
  degree_pattern_wrt_pattern n1 P2 ->
  degree_pattern_wrt_pattern n1 (open_pattern_wrt_pattern_rec n1 P2 P1)).
Proof.
apply_mutual_ind pattern_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_pattern_wrt_pattern_open_pattern_wrt_pattern_rec :
forall P1 P2 n1,
  degree_pattern_wrt_pattern (S n1) P1 ->
  degree_pattern_wrt_pattern n1 P2 ->
  degree_pattern_wrt_pattern n1 (open_pattern_wrt_pattern_rec n1 P2 P1).
Proof.
pose proof degree_pattern_wrt_pattern_open_pattern_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_pattern_wrt_pattern_open_pattern_wrt_pattern_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_bind_wrt_pattern_open_bind_wrt_pattern_rec_mutual :
(forall b1 P1 n1,
  degree_bind_wrt_pattern (S n1) b1 ->
  degree_pattern_wrt_pattern n1 P1 ->
  degree_bind_wrt_pattern n1 (open_bind_wrt_pattern_rec n1 P1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_bind_wrt_pattern_open_bind_wrt_pattern_rec :
forall b1 P1 n1,
  degree_bind_wrt_pattern (S n1) b1 ->
  degree_pattern_wrt_pattern n1 P1 ->
  degree_bind_wrt_pattern n1 (open_bind_wrt_pattern_rec n1 P1 b1).
Proof.
pose proof degree_bind_wrt_pattern_open_bind_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_bind_wrt_pattern_open_bind_wrt_pattern_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_pattern_open_exp_wrt_pattern_rec_mutual :
(forall e1 P1 n1,
  degree_exp_wrt_pattern (S n1) e1 ->
  degree_pattern_wrt_pattern n1 P1 ->
  degree_exp_wrt_pattern n1 (open_exp_wrt_pattern_rec n1 P1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_pattern_open_exp_wrt_pattern_rec :
forall e1 P1 n1,
  degree_exp_wrt_pattern (S n1) e1 ->
  degree_pattern_wrt_pattern n1 P1 ->
  degree_exp_wrt_pattern n1 (open_exp_wrt_pattern_rec n1 P1 e1).
Proof.
pose proof degree_exp_wrt_pattern_open_exp_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_pattern_open_exp_wrt_pattern_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_pattern_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_pattern n1 e1 ->
  degree_exp_wrt_pattern n1 e2 ->
  degree_exp_wrt_pattern n1 (open_exp_wrt_exp_rec n2 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_pattern_open_exp_wrt_exp_rec :
forall e1 e2 n1 n2,
  degree_exp_wrt_pattern n1 e1 ->
  degree_exp_wrt_pattern n1 e2 ->
  degree_exp_wrt_pattern n1 (open_exp_wrt_exp_rec n2 e2 e1).
Proof.
pose proof degree_exp_wrt_pattern_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_pattern_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_pattern_rec_mutual :
(forall e1 P1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_pattern_rec n2 P1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_pattern_rec :
forall e1 P1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_pattern_rec n2 P1 e1).
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_pattern_rec : lngen.

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

(* begin hide *)

Lemma degree_pat_row_wrt_pattern_open_pat_row_wrt_pattern_rec_mutual :
(forall p1 P1 n1,
  degree_pat_row_wrt_pattern (S n1) p1 ->
  degree_pattern_wrt_pattern n1 P1 ->
  degree_pat_row_wrt_pattern n1 (open_pat_row_wrt_pattern_rec n1 P1 p1)).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_pat_row_wrt_pattern_open_pat_row_wrt_pattern_rec :
forall p1 P1 n1,
  degree_pat_row_wrt_pattern (S n1) p1 ->
  degree_pattern_wrt_pattern n1 P1 ->
  degree_pat_row_wrt_pattern n1 (open_pat_row_wrt_pattern_rec n1 P1 p1).
Proof.
pose proof degree_pat_row_wrt_pattern_open_pat_row_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_pat_row_wrt_pattern_open_pat_row_wrt_pattern_rec : lngen.

(* end hide *)

Lemma degree_pattern_wrt_pattern_open_pattern_wrt_pattern :
forall P1 P2,
  degree_pattern_wrt_pattern 1 P1 ->
  degree_pattern_wrt_pattern 0 P2 ->
  degree_pattern_wrt_pattern 0 (open_pattern_wrt_pattern P1 P2).
Proof.
unfold open_pattern_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve degree_pattern_wrt_pattern_open_pattern_wrt_pattern : lngen.

Lemma degree_bind_wrt_pattern_open_bind_wrt_pattern :
forall b1 P1,
  degree_bind_wrt_pattern 1 b1 ->
  degree_pattern_wrt_pattern 0 P1 ->
  degree_bind_wrt_pattern 0 (open_bind_wrt_pattern b1 P1).
Proof.
unfold open_bind_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve degree_bind_wrt_pattern_open_bind_wrt_pattern : lngen.

Lemma degree_exp_wrt_pattern_open_exp_wrt_pattern :
forall e1 P1,
  degree_exp_wrt_pattern 1 e1 ->
  degree_pattern_wrt_pattern 0 P1 ->
  degree_exp_wrt_pattern 0 (open_exp_wrt_pattern e1 P1).
Proof.
unfold open_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_pattern_open_exp_wrt_pattern : lngen.

Lemma degree_exp_wrt_pattern_open_exp_wrt_exp :
forall e1 e2 n1,
  degree_exp_wrt_pattern n1 e1 ->
  degree_exp_wrt_pattern n1 e2 ->
  degree_exp_wrt_pattern n1 (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_pattern_open_exp_wrt_exp : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_pattern :
forall e1 P1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_pattern e1 P1).
Proof.
unfold open_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_pattern : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_exp :
forall e1 e2,
  degree_exp_wrt_exp 1 e1 ->
  degree_exp_wrt_exp 0 e2 ->
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma degree_pat_row_wrt_pattern_open_pat_row_wrt_pattern :
forall p1 P1,
  degree_pat_row_wrt_pattern 1 p1 ->
  degree_pattern_wrt_pattern 0 P1 ->
  degree_pat_row_wrt_pattern 0 (open_pat_row_wrt_pattern p1 P1).
Proof.
unfold open_pat_row_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve degree_pat_row_wrt_pattern_open_pat_row_wrt_pattern : lngen.

(* begin hide *)

Lemma degree_pattern_wrt_pattern_open_pattern_wrt_pattern_rec_inv_mutual :
(forall P1 P2 n1,
  degree_pattern_wrt_pattern n1 (open_pattern_wrt_pattern_rec n1 P2 P1) ->
  degree_pattern_wrt_pattern (S n1) P1).
Proof.
apply_mutual_ind pattern_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_pattern_wrt_pattern_open_pattern_wrt_pattern_rec_inv :
forall P1 P2 n1,
  degree_pattern_wrt_pattern n1 (open_pattern_wrt_pattern_rec n1 P2 P1) ->
  degree_pattern_wrt_pattern (S n1) P1.
Proof.
pose proof degree_pattern_wrt_pattern_open_pattern_wrt_pattern_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_pattern_wrt_pattern_open_pattern_wrt_pattern_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_bind_wrt_pattern_open_bind_wrt_pattern_rec_inv_mutual :
(forall b1 P1 n1,
  degree_bind_wrt_pattern n1 (open_bind_wrt_pattern_rec n1 P1 b1) ->
  degree_bind_wrt_pattern (S n1) b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_bind_wrt_pattern_open_bind_wrt_pattern_rec_inv :
forall b1 P1 n1,
  degree_bind_wrt_pattern n1 (open_bind_wrt_pattern_rec n1 P1 b1) ->
  degree_bind_wrt_pattern (S n1) b1.
Proof.
pose proof degree_bind_wrt_pattern_open_bind_wrt_pattern_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_bind_wrt_pattern_open_bind_wrt_pattern_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_pattern_open_exp_wrt_pattern_rec_inv_mutual :
(forall e1 P1 n1,
  degree_exp_wrt_pattern n1 (open_exp_wrt_pattern_rec n1 P1 e1) ->
  degree_exp_wrt_pattern (S n1) e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_pattern_open_exp_wrt_pattern_rec_inv :
forall e1 P1 n1,
  degree_exp_wrt_pattern n1 (open_exp_wrt_pattern_rec n1 P1 e1) ->
  degree_exp_wrt_pattern (S n1) e1.
Proof.
pose proof degree_exp_wrt_pattern_open_exp_wrt_pattern_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_pattern_open_exp_wrt_pattern_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_pattern_open_exp_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_pattern n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_pattern n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_pattern_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1 n2,
  degree_exp_wrt_pattern n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_pattern n1 e1.
Proof.
pose proof degree_exp_wrt_pattern_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_pattern_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_pattern_rec_inv_mutual :
(forall e1 P1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_pattern_rec n2 P1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_pattern_rec_inv :
forall e1 P1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_pattern_rec n2 P1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_pattern_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_pattern_rec_inv : lngen.

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

(* begin hide *)

Lemma degree_pat_row_wrt_pattern_open_pat_row_wrt_pattern_rec_inv_mutual :
(forall p1 P1 n1,
  degree_pat_row_wrt_pattern n1 (open_pat_row_wrt_pattern_rec n1 P1 p1) ->
  degree_pat_row_wrt_pattern (S n1) p1).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_pat_row_wrt_pattern_open_pat_row_wrt_pattern_rec_inv :
forall p1 P1 n1,
  degree_pat_row_wrt_pattern n1 (open_pat_row_wrt_pattern_rec n1 P1 p1) ->
  degree_pat_row_wrt_pattern (S n1) p1.
Proof.
pose proof degree_pat_row_wrt_pattern_open_pat_row_wrt_pattern_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_pat_row_wrt_pattern_open_pat_row_wrt_pattern_rec_inv : lngen.

(* end hide *)

Lemma degree_pattern_wrt_pattern_open_pattern_wrt_pattern_inv :
forall P1 P2,
  degree_pattern_wrt_pattern 0 (open_pattern_wrt_pattern P1 P2) ->
  degree_pattern_wrt_pattern 1 P1.
Proof.
unfold open_pattern_wrt_pattern; eauto with lngen.
Qed.

#[export] Hint Immediate degree_pattern_wrt_pattern_open_pattern_wrt_pattern_inv : lngen.

Lemma degree_bind_wrt_pattern_open_bind_wrt_pattern_inv :
forall b1 P1,
  degree_bind_wrt_pattern 0 (open_bind_wrt_pattern b1 P1) ->
  degree_bind_wrt_pattern 1 b1.
Proof.
unfold open_bind_wrt_pattern; eauto with lngen.
Qed.

#[export] Hint Immediate degree_bind_wrt_pattern_open_bind_wrt_pattern_inv : lngen.

Lemma degree_exp_wrt_pattern_open_exp_wrt_pattern_inv :
forall e1 P1,
  degree_exp_wrt_pattern 0 (open_exp_wrt_pattern e1 P1) ->
  degree_exp_wrt_pattern 1 e1.
Proof.
unfold open_exp_wrt_pattern; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_pattern_open_exp_wrt_pattern_inv : lngen.

Lemma degree_exp_wrt_pattern_open_exp_wrt_exp_inv :
forall e1 e2 n1,
  degree_exp_wrt_pattern n1 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_pattern n1 e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_pattern_open_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_pattern_inv :
forall e1 P1 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_pattern e1 P1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
unfold open_exp_wrt_pattern; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_pattern_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_inv :
forall e1 e2,
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_exp 1 e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_inv : lngen.

Lemma degree_pat_row_wrt_pattern_open_pat_row_wrt_pattern_inv :
forall p1 P1,
  degree_pat_row_wrt_pattern 0 (open_pat_row_wrt_pattern p1 P1) ->
  degree_pat_row_wrt_pattern 1 p1.
Proof.
unfold open_pat_row_wrt_pattern; eauto with lngen.
Qed.

#[export] Hint Immediate degree_pat_row_wrt_pattern_open_pat_row_wrt_pattern_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_pattern_wrt_pattern_rec_inj_mutual :
(forall P1 P2 X1 n1,
  close_pattern_wrt_pattern_rec n1 X1 P1 = close_pattern_wrt_pattern_rec n1 X1 P2 ->
  P1 = P2).
Proof.
apply_mutual_ind pattern_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_pattern_wrt_pattern_rec_inj :
forall P1 P2 X1 n1,
  close_pattern_wrt_pattern_rec n1 X1 P1 = close_pattern_wrt_pattern_rec n1 X1 P2 ->
  P1 = P2.
Proof.
pose proof close_pattern_wrt_pattern_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_pattern_wrt_pattern_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_bind_wrt_pattern_rec_inj_mutual :
(forall b1 b2 X1 n1,
  close_bind_wrt_pattern_rec n1 X1 b1 = close_bind_wrt_pattern_rec n1 X1 b2 ->
  b1 = b2).
Proof.
apply_mutual_ind bind_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_bind_wrt_pattern_rec_inj :
forall b1 b2 X1 n1,
  close_bind_wrt_pattern_rec n1 X1 b1 = close_bind_wrt_pattern_rec n1 X1 b2 ->
  b1 = b2.
Proof.
pose proof close_bind_wrt_pattern_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_bind_wrt_pattern_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_pattern_rec_inj_mutual :
(forall e1 e2 X1 n1,
  close_exp_wrt_pattern_rec n1 X1 e1 = close_exp_wrt_pattern_rec n1 X1 e2 ->
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

Lemma close_exp_wrt_pattern_rec_inj :
forall e1 e2 X1 n1,
  close_exp_wrt_pattern_rec n1 X1 e1 = close_exp_wrt_pattern_rec n1 X1 e2 ->
  e1 = e2.
Proof.
pose proof close_exp_wrt_pattern_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_exp_wrt_pattern_rec_inj : lngen.

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

(* begin hide *)

Lemma close_pat_row_wrt_pattern_rec_inj_mutual :
(forall p1 p2 X1 n1,
  close_pat_row_wrt_pattern_rec n1 X1 p1 = close_pat_row_wrt_pattern_rec n1 X1 p2 ->
  p1 = p2).
Proof.
apply_mutual_ind pat_row_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_pat_row_wrt_pattern_rec_inj :
forall p1 p2 X1 n1,
  close_pat_row_wrt_pattern_rec n1 X1 p1 = close_pat_row_wrt_pattern_rec n1 X1 p2 ->
  p1 = p2.
Proof.
pose proof close_pat_row_wrt_pattern_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_pat_row_wrt_pattern_rec_inj : lngen.

(* end hide *)

Lemma close_pattern_wrt_pattern_inj :
forall P1 P2 X1,
  close_pattern_wrt_pattern X1 P1 = close_pattern_wrt_pattern X1 P2 ->
  P1 = P2.
Proof.
unfold close_pattern_wrt_pattern; eauto with lngen.
Qed.

#[export] Hint Immediate close_pattern_wrt_pattern_inj : lngen.

Lemma close_bind_wrt_pattern_inj :
forall b1 b2 X1,
  close_bind_wrt_pattern X1 b1 = close_bind_wrt_pattern X1 b2 ->
  b1 = b2.
Proof.
unfold close_bind_wrt_pattern; eauto with lngen.
Qed.

#[export] Hint Immediate close_bind_wrt_pattern_inj : lngen.

Lemma close_exp_wrt_pattern_inj :
forall e1 e2 X1,
  close_exp_wrt_pattern X1 e1 = close_exp_wrt_pattern X1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_pattern; eauto with lngen.
Qed.

#[export] Hint Immediate close_exp_wrt_pattern_inj : lngen.

Lemma close_exp_wrt_exp_inj :
forall e1 e2 x1,
  close_exp_wrt_exp x1 e1 = close_exp_wrt_exp x1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate close_exp_wrt_exp_inj : lngen.

Lemma close_pat_row_wrt_pattern_inj :
forall p1 p2 X1,
  close_pat_row_wrt_pattern X1 p1 = close_pat_row_wrt_pattern X1 p2 ->
  p1 = p2.
Proof.
unfold close_pat_row_wrt_pattern; eauto with lngen.
Qed.

#[export] Hint Immediate close_pat_row_wrt_pattern_inj : lngen.

(* begin hide *)

Lemma close_pattern_wrt_pattern_rec_open_pattern_wrt_pattern_rec_mutual :
(forall P1 X1 n1,
  X1 `notin` ftvar_in_pattern P1 ->
  close_pattern_wrt_pattern_rec n1 X1 (open_pattern_wrt_pattern_rec n1 (pattern_var_f X1) P1) = P1).
Proof.
apply_mutual_ind pattern_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_pattern_wrt_pattern_rec_open_pattern_wrt_pattern_rec :
forall P1 X1 n1,
  X1 `notin` ftvar_in_pattern P1 ->
  close_pattern_wrt_pattern_rec n1 X1 (open_pattern_wrt_pattern_rec n1 (pattern_var_f X1) P1) = P1.
Proof.
pose proof close_pattern_wrt_pattern_rec_open_pattern_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_pattern_wrt_pattern_rec_open_pattern_wrt_pattern_rec : lngen.
#[export] Hint Rewrite close_pattern_wrt_pattern_rec_open_pattern_wrt_pattern_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_bind_wrt_pattern_rec_open_bind_wrt_pattern_rec_mutual :
(forall b1 X1 n1,
  X1 `notin` ftvar_in_bind b1 ->
  close_bind_wrt_pattern_rec n1 X1 (open_bind_wrt_pattern_rec n1 (pattern_var_f X1) b1) = b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_bind_wrt_pattern_rec_open_bind_wrt_pattern_rec :
forall b1 X1 n1,
  X1 `notin` ftvar_in_bind b1 ->
  close_bind_wrt_pattern_rec n1 X1 (open_bind_wrt_pattern_rec n1 (pattern_var_f X1) b1) = b1.
Proof.
pose proof close_bind_wrt_pattern_rec_open_bind_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_bind_wrt_pattern_rec_open_bind_wrt_pattern_rec : lngen.
#[export] Hint Rewrite close_bind_wrt_pattern_rec_open_bind_wrt_pattern_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_pattern_rec_open_exp_wrt_pattern_rec_mutual :
(forall e1 X1 n1,
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_pattern_rec n1 X1 (open_exp_wrt_pattern_rec n1 (pattern_var_f X1) e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_pattern_rec_open_exp_wrt_pattern_rec :
forall e1 X1 n1,
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_pattern_rec n1 X1 (open_exp_wrt_pattern_rec n1 (pattern_var_f X1) e1) = e1.
Proof.
pose proof close_exp_wrt_pattern_rec_open_exp_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_exp_wrt_pattern_rec_open_exp_wrt_pattern_rec : lngen.
#[export] Hint Rewrite close_exp_wrt_pattern_rec_open_exp_wrt_pattern_rec using solve [auto] : lngen.

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

(* begin hide *)

Lemma close_pat_row_wrt_pattern_rec_open_pat_row_wrt_pattern_rec_mutual :
(forall p1 X1 n1,
  X1 `notin` ftvar_in_pat_row p1 ->
  close_pat_row_wrt_pattern_rec n1 X1 (open_pat_row_wrt_pattern_rec n1 (pattern_var_f X1) p1) = p1).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_pat_row_wrt_pattern_rec_open_pat_row_wrt_pattern_rec :
forall p1 X1 n1,
  X1 `notin` ftvar_in_pat_row p1 ->
  close_pat_row_wrt_pattern_rec n1 X1 (open_pat_row_wrt_pattern_rec n1 (pattern_var_f X1) p1) = p1.
Proof.
pose proof close_pat_row_wrt_pattern_rec_open_pat_row_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_pat_row_wrt_pattern_rec_open_pat_row_wrt_pattern_rec : lngen.
#[export] Hint Rewrite close_pat_row_wrt_pattern_rec_open_pat_row_wrt_pattern_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_pattern_wrt_pattern_open_pattern_wrt_pattern :
forall P1 X1,
  X1 `notin` ftvar_in_pattern P1 ->
  close_pattern_wrt_pattern X1 (open_pattern_wrt_pattern P1 (pattern_var_f X1)) = P1.
Proof.
unfold close_pattern_wrt_pattern; unfold open_pattern_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve close_pattern_wrt_pattern_open_pattern_wrt_pattern : lngen.
#[export] Hint Rewrite close_pattern_wrt_pattern_open_pattern_wrt_pattern using solve [auto] : lngen.

Lemma close_bind_wrt_pattern_open_bind_wrt_pattern :
forall b1 X1,
  X1 `notin` ftvar_in_bind b1 ->
  close_bind_wrt_pattern X1 (open_bind_wrt_pattern b1 (pattern_var_f X1)) = b1.
Proof.
unfold close_bind_wrt_pattern; unfold open_bind_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve close_bind_wrt_pattern_open_bind_wrt_pattern : lngen.
#[export] Hint Rewrite close_bind_wrt_pattern_open_bind_wrt_pattern using solve [auto] : lngen.

Lemma close_exp_wrt_pattern_open_exp_wrt_pattern :
forall e1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_pattern X1 (open_exp_wrt_pattern e1 (pattern_var_f X1)) = e1.
Proof.
unfold close_exp_wrt_pattern; unfold open_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve close_exp_wrt_pattern_open_exp_wrt_pattern : lngen.
#[export] Hint Rewrite close_exp_wrt_pattern_open_exp_wrt_pattern using solve [auto] : lngen.

Lemma close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 x1,
  x1 `notin` fvar_in_exp e1 ->
  close_exp_wrt_exp x1 (open_exp_wrt_exp e1 (exp_var_f x1)) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve close_exp_wrt_exp_open_exp_wrt_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_open_exp_wrt_exp using solve [auto] : lngen.

Lemma close_pat_row_wrt_pattern_open_pat_row_wrt_pattern :
forall p1 X1,
  X1 `notin` ftvar_in_pat_row p1 ->
  close_pat_row_wrt_pattern X1 (open_pat_row_wrt_pattern p1 (pattern_var_f X1)) = p1.
Proof.
unfold close_pat_row_wrt_pattern; unfold open_pat_row_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve close_pat_row_wrt_pattern_open_pat_row_wrt_pattern : lngen.
#[export] Hint Rewrite close_pat_row_wrt_pattern_open_pat_row_wrt_pattern using solve [auto] : lngen.

(* begin hide *)

Lemma open_pattern_wrt_pattern_rec_close_pattern_wrt_pattern_rec_mutual :
(forall P1 X1 n1,
  open_pattern_wrt_pattern_rec n1 (pattern_var_f X1) (close_pattern_wrt_pattern_rec n1 X1 P1) = P1).
Proof.
apply_mutual_ind pattern_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_pattern_wrt_pattern_rec_close_pattern_wrt_pattern_rec :
forall P1 X1 n1,
  open_pattern_wrt_pattern_rec n1 (pattern_var_f X1) (close_pattern_wrt_pattern_rec n1 X1 P1) = P1.
Proof.
pose proof open_pattern_wrt_pattern_rec_close_pattern_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_pattern_wrt_pattern_rec_close_pattern_wrt_pattern_rec : lngen.
#[export] Hint Rewrite open_pattern_wrt_pattern_rec_close_pattern_wrt_pattern_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_bind_wrt_pattern_rec_close_bind_wrt_pattern_rec_mutual :
(forall b1 X1 n1,
  open_bind_wrt_pattern_rec n1 (pattern_var_f X1) (close_bind_wrt_pattern_rec n1 X1 b1) = b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_bind_wrt_pattern_rec_close_bind_wrt_pattern_rec :
forall b1 X1 n1,
  open_bind_wrt_pattern_rec n1 (pattern_var_f X1) (close_bind_wrt_pattern_rec n1 X1 b1) = b1.
Proof.
pose proof open_bind_wrt_pattern_rec_close_bind_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_bind_wrt_pattern_rec_close_bind_wrt_pattern_rec : lngen.
#[export] Hint Rewrite open_bind_wrt_pattern_rec_close_bind_wrt_pattern_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_pattern_rec_close_exp_wrt_pattern_rec_mutual :
(forall e1 X1 n1,
  open_exp_wrt_pattern_rec n1 (pattern_var_f X1) (close_exp_wrt_pattern_rec n1 X1 e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_pattern_rec_close_exp_wrt_pattern_rec :
forall e1 X1 n1,
  open_exp_wrt_pattern_rec n1 (pattern_var_f X1) (close_exp_wrt_pattern_rec n1 X1 e1) = e1.
Proof.
pose proof open_exp_wrt_pattern_rec_close_exp_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_exp_wrt_pattern_rec_close_exp_wrt_pattern_rec : lngen.
#[export] Hint Rewrite open_exp_wrt_pattern_rec_close_exp_wrt_pattern_rec using solve [auto] : lngen.

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

(* begin hide *)

Lemma open_pat_row_wrt_pattern_rec_close_pat_row_wrt_pattern_rec_mutual :
(forall p1 X1 n1,
  open_pat_row_wrt_pattern_rec n1 (pattern_var_f X1) (close_pat_row_wrt_pattern_rec n1 X1 p1) = p1).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_pat_row_wrt_pattern_rec_close_pat_row_wrt_pattern_rec :
forall p1 X1 n1,
  open_pat_row_wrt_pattern_rec n1 (pattern_var_f X1) (close_pat_row_wrt_pattern_rec n1 X1 p1) = p1.
Proof.
pose proof open_pat_row_wrt_pattern_rec_close_pat_row_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_pat_row_wrt_pattern_rec_close_pat_row_wrt_pattern_rec : lngen.
#[export] Hint Rewrite open_pat_row_wrt_pattern_rec_close_pat_row_wrt_pattern_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_pattern_wrt_pattern_close_pattern_wrt_pattern :
forall P1 X1,
  open_pattern_wrt_pattern (close_pattern_wrt_pattern X1 P1) (pattern_var_f X1) = P1.
Proof.
unfold close_pattern_wrt_pattern; unfold open_pattern_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve open_pattern_wrt_pattern_close_pattern_wrt_pattern : lngen.
#[export] Hint Rewrite open_pattern_wrt_pattern_close_pattern_wrt_pattern using solve [auto] : lngen.

Lemma open_bind_wrt_pattern_close_bind_wrt_pattern :
forall b1 X1,
  open_bind_wrt_pattern (close_bind_wrt_pattern X1 b1) (pattern_var_f X1) = b1.
Proof.
unfold close_bind_wrt_pattern; unfold open_bind_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve open_bind_wrt_pattern_close_bind_wrt_pattern : lngen.
#[export] Hint Rewrite open_bind_wrt_pattern_close_bind_wrt_pattern using solve [auto] : lngen.

Lemma open_exp_wrt_pattern_close_exp_wrt_pattern :
forall e1 X1,
  open_exp_wrt_pattern (close_exp_wrt_pattern X1 e1) (pattern_var_f X1) = e1.
Proof.
unfold close_exp_wrt_pattern; unfold open_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_pattern_close_exp_wrt_pattern : lngen.
#[export] Hint Rewrite open_exp_wrt_pattern_close_exp_wrt_pattern using solve [auto] : lngen.

Lemma open_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  open_exp_wrt_exp (close_exp_wrt_exp x1 e1) (exp_var_f x1) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma open_pat_row_wrt_pattern_close_pat_row_wrt_pattern :
forall p1 X1,
  open_pat_row_wrt_pattern (close_pat_row_wrt_pattern X1 p1) (pattern_var_f X1) = p1.
Proof.
unfold close_pat_row_wrt_pattern; unfold open_pat_row_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve open_pat_row_wrt_pattern_close_pat_row_wrt_pattern : lngen.
#[export] Hint Rewrite open_pat_row_wrt_pattern_close_pat_row_wrt_pattern using solve [auto] : lngen.

(* begin hide *)

Lemma open_pattern_wrt_pattern_rec_inj_mutual :
(forall P2 P1 X1 n1,
  X1 `notin` ftvar_in_pattern P2 ->
  X1 `notin` ftvar_in_pattern P1 ->
  open_pattern_wrt_pattern_rec n1 (pattern_var_f X1) P2 = open_pattern_wrt_pattern_rec n1 (pattern_var_f X1) P1 ->
  P2 = P1).
Proof.
apply_mutual_ind pattern_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_pattern_wrt_pattern_rec_inj :
forall P2 P1 X1 n1,
  X1 `notin` ftvar_in_pattern P2 ->
  X1 `notin` ftvar_in_pattern P1 ->
  open_pattern_wrt_pattern_rec n1 (pattern_var_f X1) P2 = open_pattern_wrt_pattern_rec n1 (pattern_var_f X1) P1 ->
  P2 = P1.
Proof.
pose proof open_pattern_wrt_pattern_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_pattern_wrt_pattern_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_bind_wrt_pattern_rec_inj_mutual :
(forall b2 b1 X1 n1,
  X1 `notin` ftvar_in_bind b2 ->
  X1 `notin` ftvar_in_bind b1 ->
  open_bind_wrt_pattern_rec n1 (pattern_var_f X1) b2 = open_bind_wrt_pattern_rec n1 (pattern_var_f X1) b1 ->
  b2 = b1).
Proof.
apply_mutual_ind bind_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_bind_wrt_pattern_rec_inj :
forall b2 b1 X1 n1,
  X1 `notin` ftvar_in_bind b2 ->
  X1 `notin` ftvar_in_bind b1 ->
  open_bind_wrt_pattern_rec n1 (pattern_var_f X1) b2 = open_bind_wrt_pattern_rec n1 (pattern_var_f X1) b1 ->
  b2 = b1.
Proof.
pose proof open_bind_wrt_pattern_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_bind_wrt_pattern_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_pattern_rec_inj_mutual :
(forall e2 e1 X1 n1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_pattern_rec n1 (pattern_var_f X1) e2 = open_exp_wrt_pattern_rec n1 (pattern_var_f X1) e1 ->
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

Lemma open_exp_wrt_pattern_rec_inj :
forall e2 e1 X1 n1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_pattern_rec n1 (pattern_var_f X1) e2 = open_exp_wrt_pattern_rec n1 (pattern_var_f X1) e1 ->
  e2 = e1.
Proof.
pose proof open_exp_wrt_pattern_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_exp_wrt_pattern_rec_inj : lngen.

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

(* begin hide *)

Lemma open_pat_row_wrt_pattern_rec_inj_mutual :
(forall p2 p1 X1 n1,
  X1 `notin` ftvar_in_pat_row p2 ->
  X1 `notin` ftvar_in_pat_row p1 ->
  open_pat_row_wrt_pattern_rec n1 (pattern_var_f X1) p2 = open_pat_row_wrt_pattern_rec n1 (pattern_var_f X1) p1 ->
  p2 = p1).
Proof.
apply_mutual_ind pat_row_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_pat_row_wrt_pattern_rec_inj :
forall p2 p1 X1 n1,
  X1 `notin` ftvar_in_pat_row p2 ->
  X1 `notin` ftvar_in_pat_row p1 ->
  open_pat_row_wrt_pattern_rec n1 (pattern_var_f X1) p2 = open_pat_row_wrt_pattern_rec n1 (pattern_var_f X1) p1 ->
  p2 = p1.
Proof.
pose proof open_pat_row_wrt_pattern_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_pat_row_wrt_pattern_rec_inj : lngen.

(* end hide *)

Lemma open_pattern_wrt_pattern_inj :
forall P2 P1 X1,
  X1 `notin` ftvar_in_pattern P2 ->
  X1 `notin` ftvar_in_pattern P1 ->
  open_pattern_wrt_pattern P2 (pattern_var_f X1) = open_pattern_wrt_pattern P1 (pattern_var_f X1) ->
  P2 = P1.
Proof.
unfold open_pattern_wrt_pattern; eauto with lngen.
Qed.

#[export] Hint Immediate open_pattern_wrt_pattern_inj : lngen.

Lemma open_bind_wrt_pattern_inj :
forall b2 b1 X1,
  X1 `notin` ftvar_in_bind b2 ->
  X1 `notin` ftvar_in_bind b1 ->
  open_bind_wrt_pattern b2 (pattern_var_f X1) = open_bind_wrt_pattern b1 (pattern_var_f X1) ->
  b2 = b1.
Proof.
unfold open_bind_wrt_pattern; eauto with lngen.
Qed.

#[export] Hint Immediate open_bind_wrt_pattern_inj : lngen.

Lemma open_exp_wrt_pattern_inj :
forall e2 e1 X1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_pattern e2 (pattern_var_f X1) = open_exp_wrt_pattern e1 (pattern_var_f X1) ->
  e2 = e1.
Proof.
unfold open_exp_wrt_pattern; eauto with lngen.
Qed.

#[export] Hint Immediate open_exp_wrt_pattern_inj : lngen.

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

Lemma open_pat_row_wrt_pattern_inj :
forall p2 p1 X1,
  X1 `notin` ftvar_in_pat_row p2 ->
  X1 `notin` ftvar_in_pat_row p1 ->
  open_pat_row_wrt_pattern p2 (pattern_var_f X1) = open_pat_row_wrt_pattern p1 (pattern_var_f X1) ->
  p2 = p1.
Proof.
unfold open_pat_row_wrt_pattern; eauto with lngen.
Qed.

#[export] Hint Immediate open_pat_row_wrt_pattern_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_pattern_wrt_pattern_of_lc_pattern_mutual :
(forall P1,
  lc_pattern P1 ->
  degree_pattern_wrt_pattern 0 P1).
Proof.
apply_mutual_ind lc_pattern_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_pattern_wrt_pattern_of_lc_pattern :
forall P1,
  lc_pattern P1 ->
  degree_pattern_wrt_pattern 0 P1.
Proof.
pose proof degree_pattern_wrt_pattern_of_lc_pattern_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_pattern_wrt_pattern_of_lc_pattern : lngen.

(* begin hide *)

Lemma degree_bind_wrt_pattern_of_lc_bind_mutual :
(forall b1,
  lc_bind b1 ->
  degree_bind_wrt_pattern 0 b1).
Proof.
apply_mutual_ind lc_bind_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_bind_wrt_pattern_of_lc_bind :
forall b1,
  lc_bind b1 ->
  degree_bind_wrt_pattern 0 b1.
Proof.
pose proof degree_bind_wrt_pattern_of_lc_bind_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_bind_wrt_pattern_of_lc_bind : lngen.

(* begin hide *)

Lemma degree_exp_wrt_pattern_of_lc_exp_mutual :
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_pattern 0 e1).
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

Lemma degree_exp_wrt_pattern_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_pattern 0 e1.
Proof.
pose proof degree_exp_wrt_pattern_of_lc_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_pattern_of_lc_exp : lngen.

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

Lemma degree_pat_row_wrt_pattern_of_lc_pat_row_mutual :
(forall p1,
  lc_pat_row p1 ->
  degree_pat_row_wrt_pattern 0 p1).
Proof.
apply_mutual_ind lc_pat_row_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_pat_row_wrt_pattern_of_lc_pat_row :
forall p1,
  lc_pat_row p1 ->
  degree_pat_row_wrt_pattern 0 p1.
Proof.
pose proof degree_pat_row_wrt_pattern_of_lc_pat_row_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_pat_row_wrt_pattern_of_lc_pat_row : lngen.

(* begin hide *)

Lemma lc_pattern_of_degree_size_mutual :
forall i1,
(forall P1,
  size_pattern P1 = i1 ->
  degree_pattern_wrt_pattern 0 P1 ->
  lc_pattern P1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind pattern_mutind;
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

Lemma lc_pattern_of_degree :
forall P1,
  degree_pattern_wrt_pattern 0 P1 ->
  lc_pattern P1.
Proof.
intros P1; intros;
pose proof (lc_pattern_of_degree_size_mutual (size_pattern P1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_pattern_of_degree : lngen.

(* begin hide *)

Lemma lc_bind_of_degree_size_mutual :
forall i1,
(forall b1,
  size_bind b1 = i1 ->
  degree_bind_wrt_pattern 0 b1 ->
  lc_bind b1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind bind_mutind;
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

Lemma lc_bind_of_degree :
forall b1,
  degree_bind_wrt_pattern 0 b1 ->
  lc_bind b1.
Proof.
intros b1; intros;
pose proof (lc_bind_of_degree_size_mutual (size_bind b1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_bind_of_degree : lngen.

(* begin hide *)

Lemma lc_exp_of_degree_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  degree_exp_wrt_pattern 0 e1 ->
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
  degree_exp_wrt_pattern 0 e1 ->
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1.
Proof.
intros e1; intros;
pose proof (lc_exp_of_degree_size_mutual (size_exp e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_exp_of_degree : lngen.

(* begin hide *)

Lemma lc_pat_row_of_degree_size_mutual :
forall i1,
(forall p1,
  size_pat_row p1 = i1 ->
  degree_pat_row_wrt_pattern 0 p1 ->
  lc_pat_row p1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind pat_row_mutind;
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

Lemma lc_pat_row_of_degree :
forall p1,
  degree_pat_row_wrt_pattern 0 p1 ->
  lc_pat_row p1.
Proof.
intros p1; intros;
pose proof (lc_pat_row_of_degree_size_mutual (size_pat_row p1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_pat_row_of_degree : lngen.

Ltac pattern_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_pattern_wrt_pattern_of_lc_pattern in J1; clear H
          end).

Ltac bind_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_bind_wrt_pattern_of_lc_bind in J1; clear H
          end).

Ltac exp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_exp_wrt_pattern_of_lc_exp in J1;
              let J2 := fresh in pose proof H as J2; apply degree_exp_wrt_exp_of_lc_exp in J2; clear H
          end).

Ltac pat_row_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_pat_row_wrt_pattern_of_lc_pat_row in J1; clear H
          end).

Lemma lc_pattern_all_exists :
forall X1 P1,
  lc_pattern (open_pattern_wrt_pattern P1 (pattern_var_f X1)) ->
  lc_pattern (pattern_all P1).
Proof.
intros; pattern_lc_exists_tac; eauto 6 with lngen.
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
  lc_pattern A1 ->
  lc_exp (open_exp_wrt_exp e1 (exp_var_f x1)) ->
  lc_exp (exp_abs_anno A1 e1).
Proof.
intros; exp_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_exp_let_exists :
forall x1 e1 e2,
  lc_exp e1 ->
  lc_exp (open_exp_wrt_exp e2 (exp_var_f x1)) ->
  lc_exp (exp_let e1 e2).
Proof.
intros; exp_lc_exists_tac; eauto 6 with lngen.
Qed.

#[export] Hint Extern 1 (lc_pattern (pattern_all _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_pattern_all_exists X1) : core.

#[export] Hint Extern 1 (lc_exp (exp_abs _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_exp_abs_exists x1) : core.

#[export] Hint Extern 1 (lc_exp (exp_abs_anno _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_exp_abs_anno_exists x1) : core.

#[export] Hint Extern 1 (lc_exp (exp_let _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_exp_let_exists x1) : core.

Lemma lc_body_pattern_wrt_pattern :
forall P1 P2,
  body_pattern_wrt_pattern P1 ->
  lc_pattern P2 ->
  lc_pattern (open_pattern_wrt_pattern P1 P2).
Proof.
unfold body_pattern_wrt_pattern;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
pattern_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_pattern_wrt_pattern : lngen.

Lemma lc_body_bind_wrt_pattern :
forall b1 P1,
  body_bind_wrt_pattern b1 ->
  lc_pattern P1 ->
  lc_bind (open_bind_wrt_pattern b1 P1).
Proof.
unfold body_bind_wrt_pattern;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
bind_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_bind_wrt_pattern : lngen.

Lemma lc_body_exp_wrt_pattern :
forall e1 P1,
  body_exp_wrt_pattern e1 ->
  lc_pattern P1 ->
  lc_exp (open_exp_wrt_pattern e1 P1).
Proof.
unfold body_exp_wrt_pattern;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
exp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_exp_wrt_pattern : lngen.

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

Lemma lc_body_pat_row_wrt_pattern :
forall p1 P1,
  body_pat_row_wrt_pattern p1 ->
  lc_pattern P1 ->
  lc_pat_row (open_pat_row_wrt_pattern p1 P1).
Proof.
unfold body_pat_row_wrt_pattern;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
pat_row_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_pat_row_wrt_pattern : lngen.

Lemma lc_body_pattern_all_1 :
forall P1,
  lc_pattern (pattern_all P1) ->
  body_pattern_wrt_pattern P1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_pattern_all_1 : lngen.

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

Lemma lc_body_exp_let_2 :
forall e1 e2,
  lc_exp (exp_let e1 e2) ->
  body_exp_wrt_exp e2.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_exp_let_2 : lngen.

(* begin hide *)

Lemma lc_pattern_unique_mutual :
(forall P1 (proof2 proof3 : lc_pattern P1), proof2 = proof3).
Proof.
apply_mutual_ind lc_pattern_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_pattern_unique :
forall P1 (proof2 proof3 : lc_pattern P1), proof2 = proof3.
Proof.
pose proof lc_pattern_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_pattern_unique : lngen.

(* begin hide *)

Lemma lc_bind_unique_mutual :
(forall b1 (proof2 proof3 : lc_bind b1), proof2 = proof3).
Proof.
apply_mutual_ind lc_bind_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_bind_unique :
forall b1 (proof2 proof3 : lc_bind b1), proof2 = proof3.
Proof.
pose proof lc_bind_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_bind_unique : lngen.

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

Lemma lc_pat_row_unique_mutual :
(forall p1 (proof2 proof3 : lc_pat_row p1), proof2 = proof3).
Proof.
apply_mutual_ind lc_pat_row_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_pat_row_unique :
forall p1 (proof2 proof3 : lc_pat_row p1), proof2 = proof3.
Proof.
pose proof lc_pat_row_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_pat_row_unique : lngen.

(* begin hide *)

Lemma lc_pattern_of_lc_set_pattern_mutual :
(forall P1, lc_set_pattern P1 -> lc_pattern P1).
Proof.
apply_mutual_ind lc_set_pattern_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_pattern_of_lc_set_pattern :
forall P1, lc_set_pattern P1 -> lc_pattern P1.
Proof.
pose proof lc_pattern_of_lc_set_pattern_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_pattern_of_lc_set_pattern : lngen.

(* begin hide *)

Lemma lc_bind_of_lc_set_bind_mutual :
(forall b1, lc_set_bind b1 -> lc_bind b1).
Proof.
apply_mutual_ind lc_set_bind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_bind_of_lc_set_bind :
forall b1, lc_set_bind b1 -> lc_bind b1.
Proof.
pose proof lc_bind_of_lc_set_bind_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_bind_of_lc_set_bind : lngen.

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

Lemma lc_pat_row_of_lc_set_pat_row_mutual :
(forall p1, lc_set_pat_row p1 -> lc_pat_row p1).
Proof.
apply_mutual_ind lc_set_pat_row_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_pat_row_of_lc_set_pat_row :
forall p1, lc_set_pat_row p1 -> lc_pat_row p1.
Proof.
pose proof lc_pat_row_of_lc_set_pat_row_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_pat_row_of_lc_set_pat_row : lngen.

(* begin hide *)

Lemma lc_set_pattern_of_lc_pattern_size_mutual :
forall i1,
(forall P1,
  size_pattern P1 = i1 ->
  lc_pattern P1 ->
  lc_set_pattern P1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind pattern_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_pattern_of_lc_pattern];
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

Lemma lc_set_pattern_of_lc_pattern :
forall P1,
  lc_pattern P1 ->
  lc_set_pattern P1.
Proof.
intros P1; intros;
pose proof (lc_set_pattern_of_lc_pattern_size_mutual (size_pattern P1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_pattern_of_lc_pattern : lngen.

(* begin hide *)

Lemma lc_set_bind_of_lc_bind_size_mutual :
forall i1,
(forall b1,
  size_bind b1 = i1 ->
  lc_bind b1 ->
  lc_set_bind b1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind bind_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_pattern_of_lc_pattern
 | apply lc_set_bind_of_lc_bind];
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

Lemma lc_set_bind_of_lc_bind :
forall b1,
  lc_bind b1 ->
  lc_set_bind b1.
Proof.
intros b1; intros;
pose proof (lc_set_bind_of_lc_bind_size_mutual (size_bind b1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_bind_of_lc_bind : lngen.

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
try first [apply lc_set_pattern_of_lc_pattern
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

(* begin hide *)

Lemma lc_set_pat_row_of_lc_pat_row_size_mutual :
forall i1,
(forall p1,
  size_pat_row p1 = i1 ->
  lc_pat_row p1 ->
  lc_set_pat_row p1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind pat_row_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_pattern_of_lc_pattern
 | apply lc_set_pat_row_of_lc_pat_row];
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

Lemma lc_set_pat_row_of_lc_pat_row :
forall p1,
  lc_pat_row p1 ->
  lc_set_pat_row p1.
Proof.
intros p1; intros;
pose proof (lc_set_pat_row_of_lc_pat_row_size_mutual (size_pat_row p1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_pat_row_of_lc_pat_row : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_pattern_wrt_pattern_rec_degree_pattern_wrt_pattern_mutual :
(forall P1 X1 n1,
  degree_pattern_wrt_pattern n1 P1 ->
  X1 `notin` ftvar_in_pattern P1 ->
  close_pattern_wrt_pattern_rec n1 X1 P1 = P1).
Proof.
apply_mutual_ind pattern_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_pattern_wrt_pattern_rec_degree_pattern_wrt_pattern :
forall P1 X1 n1,
  degree_pattern_wrt_pattern n1 P1 ->
  X1 `notin` ftvar_in_pattern P1 ->
  close_pattern_wrt_pattern_rec n1 X1 P1 = P1.
Proof.
pose proof close_pattern_wrt_pattern_rec_degree_pattern_wrt_pattern_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_pattern_wrt_pattern_rec_degree_pattern_wrt_pattern : lngen.
#[export] Hint Rewrite close_pattern_wrt_pattern_rec_degree_pattern_wrt_pattern using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_bind_wrt_pattern_rec_degree_bind_wrt_pattern_mutual :
(forall b1 X1 n1,
  degree_bind_wrt_pattern n1 b1 ->
  X1 `notin` ftvar_in_bind b1 ->
  close_bind_wrt_pattern_rec n1 X1 b1 = b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_bind_wrt_pattern_rec_degree_bind_wrt_pattern :
forall b1 X1 n1,
  degree_bind_wrt_pattern n1 b1 ->
  X1 `notin` ftvar_in_bind b1 ->
  close_bind_wrt_pattern_rec n1 X1 b1 = b1.
Proof.
pose proof close_bind_wrt_pattern_rec_degree_bind_wrt_pattern_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_bind_wrt_pattern_rec_degree_bind_wrt_pattern : lngen.
#[export] Hint Rewrite close_bind_wrt_pattern_rec_degree_bind_wrt_pattern using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_pattern_rec_degree_exp_wrt_pattern_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_pattern n1 e1 ->
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_pattern_rec n1 X1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_pattern_rec_degree_exp_wrt_pattern :
forall e1 X1 n1,
  degree_exp_wrt_pattern n1 e1 ->
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_pattern_rec n1 X1 e1 = e1.
Proof.
pose proof close_exp_wrt_pattern_rec_degree_exp_wrt_pattern_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_exp_wrt_pattern_rec_degree_exp_wrt_pattern : lngen.
#[export] Hint Rewrite close_exp_wrt_pattern_rec_degree_exp_wrt_pattern using solve [auto] : lngen.

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

(* begin hide *)

Lemma close_pat_row_wrt_pattern_rec_degree_pat_row_wrt_pattern_mutual :
(forall p1 X1 n1,
  degree_pat_row_wrt_pattern n1 p1 ->
  X1 `notin` ftvar_in_pat_row p1 ->
  close_pat_row_wrt_pattern_rec n1 X1 p1 = p1).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_pat_row_wrt_pattern_rec_degree_pat_row_wrt_pattern :
forall p1 X1 n1,
  degree_pat_row_wrt_pattern n1 p1 ->
  X1 `notin` ftvar_in_pat_row p1 ->
  close_pat_row_wrt_pattern_rec n1 X1 p1 = p1.
Proof.
pose proof close_pat_row_wrt_pattern_rec_degree_pat_row_wrt_pattern_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_pat_row_wrt_pattern_rec_degree_pat_row_wrt_pattern : lngen.
#[export] Hint Rewrite close_pat_row_wrt_pattern_rec_degree_pat_row_wrt_pattern using solve [auto] : lngen.

(* end hide *)

Lemma close_pattern_wrt_pattern_lc_pattern :
forall P1 X1,
  lc_pattern P1 ->
  X1 `notin` ftvar_in_pattern P1 ->
  close_pattern_wrt_pattern X1 P1 = P1.
Proof.
unfold close_pattern_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve close_pattern_wrt_pattern_lc_pattern : lngen.
#[export] Hint Rewrite close_pattern_wrt_pattern_lc_pattern using solve [auto] : lngen.

Lemma close_bind_wrt_pattern_lc_bind :
forall b1 X1,
  lc_bind b1 ->
  X1 `notin` ftvar_in_bind b1 ->
  close_bind_wrt_pattern X1 b1 = b1.
Proof.
unfold close_bind_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve close_bind_wrt_pattern_lc_bind : lngen.
#[export] Hint Rewrite close_bind_wrt_pattern_lc_bind using solve [auto] : lngen.

Lemma close_exp_wrt_pattern_lc_exp :
forall e1 X1,
  lc_exp e1 ->
  X1 `notin` ftvar_in_exp e1 ->
  close_exp_wrt_pattern X1 e1 = e1.
Proof.
unfold close_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve close_exp_wrt_pattern_lc_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_pattern_lc_exp using solve [auto] : lngen.

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

Lemma close_pat_row_wrt_pattern_lc_pat_row :
forall p1 X1,
  lc_pat_row p1 ->
  X1 `notin` ftvar_in_pat_row p1 ->
  close_pat_row_wrt_pattern X1 p1 = p1.
Proof.
unfold close_pat_row_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve close_pat_row_wrt_pattern_lc_pat_row : lngen.
#[export] Hint Rewrite close_pat_row_wrt_pattern_lc_pat_row using solve [auto] : lngen.

(* begin hide *)

Lemma open_pattern_wrt_pattern_rec_degree_pattern_wrt_pattern_mutual :
(forall P2 P1 n1,
  degree_pattern_wrt_pattern n1 P2 ->
  open_pattern_wrt_pattern_rec n1 P1 P2 = P2).
Proof.
apply_mutual_ind pattern_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_pattern_wrt_pattern_rec_degree_pattern_wrt_pattern :
forall P2 P1 n1,
  degree_pattern_wrt_pattern n1 P2 ->
  open_pattern_wrt_pattern_rec n1 P1 P2 = P2.
Proof.
pose proof open_pattern_wrt_pattern_rec_degree_pattern_wrt_pattern_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_pattern_wrt_pattern_rec_degree_pattern_wrt_pattern : lngen.
#[export] Hint Rewrite open_pattern_wrt_pattern_rec_degree_pattern_wrt_pattern using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_bind_wrt_pattern_rec_degree_bind_wrt_pattern_mutual :
(forall b1 P1 n1,
  degree_bind_wrt_pattern n1 b1 ->
  open_bind_wrt_pattern_rec n1 P1 b1 = b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_bind_wrt_pattern_rec_degree_bind_wrt_pattern :
forall b1 P1 n1,
  degree_bind_wrt_pattern n1 b1 ->
  open_bind_wrt_pattern_rec n1 P1 b1 = b1.
Proof.
pose proof open_bind_wrt_pattern_rec_degree_bind_wrt_pattern_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_bind_wrt_pattern_rec_degree_bind_wrt_pattern : lngen.
#[export] Hint Rewrite open_bind_wrt_pattern_rec_degree_bind_wrt_pattern using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_pattern_rec_degree_exp_wrt_pattern_mutual :
(forall e1 P1 n1,
  degree_exp_wrt_pattern n1 e1 ->
  open_exp_wrt_pattern_rec n1 P1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_pattern_rec_degree_exp_wrt_pattern :
forall e1 P1 n1,
  degree_exp_wrt_pattern n1 e1 ->
  open_exp_wrt_pattern_rec n1 P1 e1 = e1.
Proof.
pose proof open_exp_wrt_pattern_rec_degree_exp_wrt_pattern_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_exp_wrt_pattern_rec_degree_exp_wrt_pattern : lngen.
#[export] Hint Rewrite open_exp_wrt_pattern_rec_degree_exp_wrt_pattern using solve [auto] : lngen.

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

(* begin hide *)

Lemma open_pat_row_wrt_pattern_rec_degree_pat_row_wrt_pattern_mutual :
(forall p1 P1 n1,
  degree_pat_row_wrt_pattern n1 p1 ->
  open_pat_row_wrt_pattern_rec n1 P1 p1 = p1).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_pat_row_wrt_pattern_rec_degree_pat_row_wrt_pattern :
forall p1 P1 n1,
  degree_pat_row_wrt_pattern n1 p1 ->
  open_pat_row_wrt_pattern_rec n1 P1 p1 = p1.
Proof.
pose proof open_pat_row_wrt_pattern_rec_degree_pat_row_wrt_pattern_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_pat_row_wrt_pattern_rec_degree_pat_row_wrt_pattern : lngen.
#[export] Hint Rewrite open_pat_row_wrt_pattern_rec_degree_pat_row_wrt_pattern using solve [auto] : lngen.

(* end hide *)

Lemma open_pattern_wrt_pattern_lc_pattern :
forall P2 P1,
  lc_pattern P2 ->
  open_pattern_wrt_pattern P2 P1 = P2.
Proof.
unfold open_pattern_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve open_pattern_wrt_pattern_lc_pattern : lngen.
#[export] Hint Rewrite open_pattern_wrt_pattern_lc_pattern using solve [auto] : lngen.

Lemma open_bind_wrt_pattern_lc_bind :
forall b1 P1,
  lc_bind b1 ->
  open_bind_wrt_pattern b1 P1 = b1.
Proof.
unfold open_bind_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve open_bind_wrt_pattern_lc_bind : lngen.
#[export] Hint Rewrite open_bind_wrt_pattern_lc_bind using solve [auto] : lngen.

Lemma open_exp_wrt_pattern_lc_exp :
forall e1 P1,
  lc_exp e1 ->
  open_exp_wrt_pattern e1 P1 = e1.
Proof.
unfold open_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_pattern_lc_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_pattern_lc_exp using solve [auto] : lngen.

Lemma open_exp_wrt_exp_lc_exp :
forall e2 e1,
  lc_exp e2 ->
  open_exp_wrt_exp e2 e1 = e2.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_exp_lc_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_lc_exp using solve [auto] : lngen.

Lemma open_pat_row_wrt_pattern_lc_pat_row :
forall p1 P1,
  lc_pat_row p1 ->
  open_pat_row_wrt_pattern p1 P1 = p1.
Proof.
unfold open_pat_row_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve open_pat_row_wrt_pattern_lc_pat_row : lngen.
#[export] Hint Rewrite open_pat_row_wrt_pattern_lc_pat_row using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma ftvar_in_pattern_close_pattern_wrt_pattern_rec_mutual :
(forall P1 X1 n1,
  ftvar_in_pattern (close_pattern_wrt_pattern_rec n1 X1 P1) [=] remove X1 (ftvar_in_pattern P1)).
Proof.
apply_mutual_ind pattern_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_pattern_close_pattern_wrt_pattern_rec :
forall P1 X1 n1,
  ftvar_in_pattern (close_pattern_wrt_pattern_rec n1 X1 P1) [=] remove X1 (ftvar_in_pattern P1).
Proof.
pose proof ftvar_in_pattern_close_pattern_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_pattern_close_pattern_wrt_pattern_rec : lngen.
#[export] Hint Rewrite ftvar_in_pattern_close_pattern_wrt_pattern_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bind_close_bind_wrt_pattern_rec_mutual :
(forall b1 X1 n1,
  ftvar_in_bind (close_bind_wrt_pattern_rec n1 X1 b1) [=] remove X1 (ftvar_in_bind b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bind_close_bind_wrt_pattern_rec :
forall b1 X1 n1,
  ftvar_in_bind (close_bind_wrt_pattern_rec n1 X1 b1) [=] remove X1 (ftvar_in_bind b1).
Proof.
pose proof ftvar_in_bind_close_bind_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bind_close_bind_wrt_pattern_rec : lngen.
#[export] Hint Rewrite ftvar_in_bind_close_bind_wrt_pattern_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_close_exp_wrt_pattern_rec_mutual :
(forall e1 X1 n1,
  ftvar_in_exp (close_exp_wrt_pattern_rec n1 X1 e1) [=] remove X1 (ftvar_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_close_exp_wrt_pattern_rec :
forall e1 X1 n1,
  ftvar_in_exp (close_exp_wrt_pattern_rec n1 X1 e1) [=] remove X1 (ftvar_in_exp e1).
Proof.
pose proof ftvar_in_exp_close_exp_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_close_exp_wrt_pattern_rec : lngen.
#[export] Hint Rewrite ftvar_in_exp_close_exp_wrt_pattern_rec using solve [auto] : lngen.

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

Lemma fvar_in_exp_close_exp_wrt_pattern_rec_mutual :
(forall e1 X1 n1,
  fvar_in_exp (close_exp_wrt_pattern_rec n1 X1 e1) [=] fvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_close_exp_wrt_pattern_rec :
forall e1 X1 n1,
  fvar_in_exp (close_exp_wrt_pattern_rec n1 X1 e1) [=] fvar_in_exp e1.
Proof.
pose proof fvar_in_exp_close_exp_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_close_exp_wrt_pattern_rec : lngen.
#[export] Hint Rewrite fvar_in_exp_close_exp_wrt_pattern_rec using solve [auto] : lngen.

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

(* begin hide *)

Lemma ftvar_in_pat_row_close_pat_row_wrt_pattern_rec_mutual :
(forall p1 X1 n1,
  ftvar_in_pat_row (close_pat_row_wrt_pattern_rec n1 X1 p1) [=] remove X1 (ftvar_in_pat_row p1)).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_pat_row_close_pat_row_wrt_pattern_rec :
forall p1 X1 n1,
  ftvar_in_pat_row (close_pat_row_wrt_pattern_rec n1 X1 p1) [=] remove X1 (ftvar_in_pat_row p1).
Proof.
pose proof ftvar_in_pat_row_close_pat_row_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_pat_row_close_pat_row_wrt_pattern_rec : lngen.
#[export] Hint Rewrite ftvar_in_pat_row_close_pat_row_wrt_pattern_rec using solve [auto] : lngen.

(* end hide *)

Lemma ftvar_in_pattern_close_pattern_wrt_pattern :
forall P1 X1,
  ftvar_in_pattern (close_pattern_wrt_pattern X1 P1) [=] remove X1 (ftvar_in_pattern P1).
Proof.
unfold close_pattern_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_pattern_close_pattern_wrt_pattern : lngen.
#[export] Hint Rewrite ftvar_in_pattern_close_pattern_wrt_pattern using solve [auto] : lngen.

Lemma ftvar_in_bind_close_bind_wrt_pattern :
forall b1 X1,
  ftvar_in_bind (close_bind_wrt_pattern X1 b1) [=] remove X1 (ftvar_in_bind b1).
Proof.
unfold close_bind_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_bind_close_bind_wrt_pattern : lngen.
#[export] Hint Rewrite ftvar_in_bind_close_bind_wrt_pattern using solve [auto] : lngen.

Lemma ftvar_in_exp_close_exp_wrt_pattern :
forall e1 X1,
  ftvar_in_exp (close_exp_wrt_pattern X1 e1) [=] remove X1 (ftvar_in_exp e1).
Proof.
unfold close_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_close_exp_wrt_pattern : lngen.
#[export] Hint Rewrite ftvar_in_exp_close_exp_wrt_pattern using solve [auto] : lngen.

Lemma ftvar_in_exp_close_exp_wrt_exp :
forall e1 x1,
  ftvar_in_exp (close_exp_wrt_exp x1 e1) [=] ftvar_in_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite ftvar_in_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma fvar_in_exp_close_exp_wrt_pattern :
forall e1 X1,
  fvar_in_exp (close_exp_wrt_pattern X1 e1) [=] fvar_in_exp e1.
Proof.
unfold close_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_close_exp_wrt_pattern : lngen.
#[export] Hint Rewrite fvar_in_exp_close_exp_wrt_pattern using solve [auto] : lngen.

Lemma fvar_in_exp_close_exp_wrt_exp :
forall e1 x1,
  fvar_in_exp (close_exp_wrt_exp x1 e1) [=] remove x1 (fvar_in_exp e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite fvar_in_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma ftvar_in_pat_row_close_pat_row_wrt_pattern :
forall p1 X1,
  ftvar_in_pat_row (close_pat_row_wrt_pattern X1 p1) [=] remove X1 (ftvar_in_pat_row p1).
Proof.
unfold close_pat_row_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_pat_row_close_pat_row_wrt_pattern : lngen.
#[export] Hint Rewrite ftvar_in_pat_row_close_pat_row_wrt_pattern using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_pattern_open_pattern_wrt_pattern_rec_lower_mutual :
(forall P1 P2 n1,
  ftvar_in_pattern P1 [<=] ftvar_in_pattern (open_pattern_wrt_pattern_rec n1 P2 P1)).
Proof.
apply_mutual_ind pattern_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_pattern_open_pattern_wrt_pattern_rec_lower :
forall P1 P2 n1,
  ftvar_in_pattern P1 [<=] ftvar_in_pattern (open_pattern_wrt_pattern_rec n1 P2 P1).
Proof.
pose proof ftvar_in_pattern_open_pattern_wrt_pattern_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_pattern_open_pattern_wrt_pattern_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bind_open_bind_wrt_pattern_rec_lower_mutual :
(forall b1 P1 n1,
  ftvar_in_bind b1 [<=] ftvar_in_bind (open_bind_wrt_pattern_rec n1 P1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bind_open_bind_wrt_pattern_rec_lower :
forall b1 P1 n1,
  ftvar_in_bind b1 [<=] ftvar_in_bind (open_bind_wrt_pattern_rec n1 P1 b1).
Proof.
pose proof ftvar_in_bind_open_bind_wrt_pattern_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bind_open_bind_wrt_pattern_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_pattern_rec_lower_mutual :
(forall e1 P1 n1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_pattern_rec n1 P1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_pattern_rec_lower :
forall e1 P1 n1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_pattern_rec n1 P1 e1).
Proof.
pose proof ftvar_in_exp_open_exp_wrt_pattern_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_pattern_rec_lower : lngen.

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

Lemma fvar_in_exp_open_exp_wrt_pattern_rec_lower_mutual :
(forall e1 P1 n1,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_pattern_rec n1 P1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_pattern_rec_lower :
forall e1 P1 n1,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_pattern_rec n1 P1 e1).
Proof.
pose proof fvar_in_exp_open_exp_wrt_pattern_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_pattern_rec_lower : lngen.

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

(* begin hide *)

Lemma ftvar_in_pat_row_open_pat_row_wrt_pattern_rec_lower_mutual :
(forall p1 P1 n1,
  ftvar_in_pat_row p1 [<=] ftvar_in_pat_row (open_pat_row_wrt_pattern_rec n1 P1 p1)).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_pat_row_open_pat_row_wrt_pattern_rec_lower :
forall p1 P1 n1,
  ftvar_in_pat_row p1 [<=] ftvar_in_pat_row (open_pat_row_wrt_pattern_rec n1 P1 p1).
Proof.
pose proof ftvar_in_pat_row_open_pat_row_wrt_pattern_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_pat_row_open_pat_row_wrt_pattern_rec_lower : lngen.

(* end hide *)

Lemma ftvar_in_pattern_open_pattern_wrt_pattern_lower :
forall P1 P2,
  ftvar_in_pattern P1 [<=] ftvar_in_pattern (open_pattern_wrt_pattern P1 P2).
Proof.
unfold open_pattern_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_pattern_open_pattern_wrt_pattern_lower : lngen.

Lemma ftvar_in_bind_open_bind_wrt_pattern_lower :
forall b1 P1,
  ftvar_in_bind b1 [<=] ftvar_in_bind (open_bind_wrt_pattern b1 P1).
Proof.
unfold open_bind_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_bind_open_bind_wrt_pattern_lower : lngen.

Lemma ftvar_in_exp_open_exp_wrt_pattern_lower :
forall e1 P1,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_pattern e1 P1).
Proof.
unfold open_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_pattern_lower : lngen.

Lemma ftvar_in_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  ftvar_in_exp e1 [<=] ftvar_in_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_exp_lower : lngen.

Lemma fvar_in_exp_open_exp_wrt_pattern_lower :
forall e1 P1,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_pattern e1 P1).
Proof.
unfold open_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_pattern_lower : lngen.

Lemma fvar_in_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  fvar_in_exp e1 [<=] fvar_in_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_exp_lower : lngen.

Lemma ftvar_in_pat_row_open_pat_row_wrt_pattern_lower :
forall p1 P1,
  ftvar_in_pat_row p1 [<=] ftvar_in_pat_row (open_pat_row_wrt_pattern p1 P1).
Proof.
unfold open_pat_row_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_pat_row_open_pat_row_wrt_pattern_lower : lngen.

(* begin hide *)

Lemma ftvar_in_pattern_open_pattern_wrt_pattern_rec_upper_mutual :
(forall P1 P2 n1,
  ftvar_in_pattern (open_pattern_wrt_pattern_rec n1 P2 P1) [<=] ftvar_in_pattern P2 `union` ftvar_in_pattern P1).
Proof.
apply_mutual_ind pattern_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_pattern_open_pattern_wrt_pattern_rec_upper :
forall P1 P2 n1,
  ftvar_in_pattern (open_pattern_wrt_pattern_rec n1 P2 P1) [<=] ftvar_in_pattern P2 `union` ftvar_in_pattern P1.
Proof.
pose proof ftvar_in_pattern_open_pattern_wrt_pattern_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_pattern_open_pattern_wrt_pattern_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bind_open_bind_wrt_pattern_rec_upper_mutual :
(forall b1 P1 n1,
  ftvar_in_bind (open_bind_wrt_pattern_rec n1 P1 b1) [<=] ftvar_in_pattern P1 `union` ftvar_in_bind b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_bind_open_bind_wrt_pattern_rec_upper :
forall b1 P1 n1,
  ftvar_in_bind (open_bind_wrt_pattern_rec n1 P1 b1) [<=] ftvar_in_pattern P1 `union` ftvar_in_bind b1.
Proof.
pose proof ftvar_in_bind_open_bind_wrt_pattern_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bind_open_bind_wrt_pattern_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_pattern_rec_upper_mutual :
(forall e1 P1 n1,
  ftvar_in_exp (open_exp_wrt_pattern_rec n1 P1 e1) [<=] ftvar_in_pattern P1 `union` ftvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_exp_open_exp_wrt_pattern_rec_upper :
forall e1 P1 n1,
  ftvar_in_exp (open_exp_wrt_pattern_rec n1 P1 e1) [<=] ftvar_in_pattern P1 `union` ftvar_in_exp e1.
Proof.
pose proof ftvar_in_exp_open_exp_wrt_pattern_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_pattern_rec_upper : lngen.

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

Lemma fvar_in_exp_open_exp_wrt_pattern_rec_upper_mutual :
(forall e1 P1 n1,
  fvar_in_exp (open_exp_wrt_pattern_rec n1 P1 e1) [<=] fvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_exp_open_exp_wrt_pattern_rec_upper :
forall e1 P1 n1,
  fvar_in_exp (open_exp_wrt_pattern_rec n1 P1 e1) [<=] fvar_in_exp e1.
Proof.
pose proof fvar_in_exp_open_exp_wrt_pattern_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_pattern_rec_upper : lngen.

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

(* begin hide *)

Lemma ftvar_in_pat_row_open_pat_row_wrt_pattern_rec_upper_mutual :
(forall p1 P1 n1,
  ftvar_in_pat_row (open_pat_row_wrt_pattern_rec n1 P1 p1) [<=] ftvar_in_pattern P1 `union` ftvar_in_pat_row p1).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_pat_row_open_pat_row_wrt_pattern_rec_upper :
forall p1 P1 n1,
  ftvar_in_pat_row (open_pat_row_wrt_pattern_rec n1 P1 p1) [<=] ftvar_in_pattern P1 `union` ftvar_in_pat_row p1.
Proof.
pose proof ftvar_in_pat_row_open_pat_row_wrt_pattern_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_pat_row_open_pat_row_wrt_pattern_rec_upper : lngen.

(* end hide *)

Lemma ftvar_in_pattern_open_pattern_wrt_pattern_upper :
forall P1 P2,
  ftvar_in_pattern (open_pattern_wrt_pattern P1 P2) [<=] ftvar_in_pattern P2 `union` ftvar_in_pattern P1.
Proof.
unfold open_pattern_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_pattern_open_pattern_wrt_pattern_upper : lngen.

Lemma ftvar_in_bind_open_bind_wrt_pattern_upper :
forall b1 P1,
  ftvar_in_bind (open_bind_wrt_pattern b1 P1) [<=] ftvar_in_pattern P1 `union` ftvar_in_bind b1.
Proof.
unfold open_bind_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_bind_open_bind_wrt_pattern_upper : lngen.

Lemma ftvar_in_exp_open_exp_wrt_pattern_upper :
forall e1 P1,
  ftvar_in_exp (open_exp_wrt_pattern e1 P1) [<=] ftvar_in_pattern P1 `union` ftvar_in_exp e1.
Proof.
unfold open_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_pattern_upper : lngen.

Lemma ftvar_in_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  ftvar_in_exp (open_exp_wrt_exp e1 e2) [<=] ftvar_in_exp e2 `union` ftvar_in_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_exp_open_exp_wrt_exp_upper : lngen.

Lemma fvar_in_exp_open_exp_wrt_pattern_upper :
forall e1 P1,
  fvar_in_exp (open_exp_wrt_pattern e1 P1) [<=] fvar_in_exp e1.
Proof.
unfold open_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_pattern_upper : lngen.

Lemma fvar_in_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  fvar_in_exp (open_exp_wrt_exp e1 e2) [<=] fvar_in_exp e2 `union` fvar_in_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_exp_open_exp_wrt_exp_upper : lngen.

Lemma ftvar_in_pat_row_open_pat_row_wrt_pattern_upper :
forall p1 P1,
  ftvar_in_pat_row (open_pat_row_wrt_pattern p1 P1) [<=] ftvar_in_pattern P1 `union` ftvar_in_pat_row p1.
Proof.
unfold open_pat_row_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_pat_row_open_pat_row_wrt_pattern_upper : lngen.

(* begin hide *)

Lemma ftvar_in_pattern_subst_pattern_in_pattern_fresh_mutual :
(forall P1 P2 X1,
  X1 `notin` ftvar_in_pattern P1 ->
  ftvar_in_pattern (subst_pattern_in_pattern P2 X1 P1) [=] ftvar_in_pattern P1).
Proof.
apply_mutual_ind pattern_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_pattern_subst_pattern_in_pattern_fresh :
forall P1 P2 X1,
  X1 `notin` ftvar_in_pattern P1 ->
  ftvar_in_pattern (subst_pattern_in_pattern P2 X1 P1) [=] ftvar_in_pattern P1.
Proof.
pose proof ftvar_in_pattern_subst_pattern_in_pattern_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_pattern_subst_pattern_in_pattern_fresh : lngen.
#[export] Hint Rewrite ftvar_in_pattern_subst_pattern_in_pattern_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_bind_subst_pattern_in_bind_fresh_mutual :
(forall b1 P1 X1,
  X1 `notin` ftvar_in_bind b1 ->
  ftvar_in_bind (subst_pattern_in_bind P1 X1 b1) [=] ftvar_in_bind b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_bind_subst_pattern_in_bind_fresh :
forall b1 P1 X1,
  X1 `notin` ftvar_in_bind b1 ->
  ftvar_in_bind (subst_pattern_in_bind P1 X1 b1) [=] ftvar_in_bind b1.
Proof.
pose proof ftvar_in_bind_subst_pattern_in_bind_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bind_subst_pattern_in_bind_fresh : lngen.
#[export] Hint Rewrite ftvar_in_bind_subst_pattern_in_bind_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_pattern_in_exp_fresh_mutual :
(forall e1 P1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  ftvar_in_exp (subst_pattern_in_exp P1 X1 e1) [=] ftvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_pattern_in_exp_fresh :
forall e1 P1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  ftvar_in_exp (subst_pattern_in_exp P1 X1 e1) [=] ftvar_in_exp e1.
Proof.
pose proof ftvar_in_exp_subst_pattern_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_pattern_in_exp_fresh : lngen.
#[export] Hint Rewrite ftvar_in_exp_subst_pattern_in_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_fresh_mutual :
(forall e1 P1 X1,
  fvar_in_exp (subst_pattern_in_exp P1 X1 e1) [=] fvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_exp_in_exp_fresh :
forall e1 P1 X1,
  fvar_in_exp (subst_pattern_in_exp P1 X1 e1) [=] fvar_in_exp e1.
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

Lemma ftvar_in_pat_row_subst_pattern_in_pat_row_fresh_mutual :
(forall p1 P1 X1,
  X1 `notin` ftvar_in_pat_row p1 ->
  ftvar_in_pat_row (subst_pattern_in_pat_row P1 X1 p1) [=] ftvar_in_pat_row p1).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_pat_row_subst_pattern_in_pat_row_fresh :
forall p1 P1 X1,
  X1 `notin` ftvar_in_pat_row p1 ->
  ftvar_in_pat_row (subst_pattern_in_pat_row P1 X1 p1) [=] ftvar_in_pat_row p1.
Proof.
pose proof ftvar_in_pat_row_subst_pattern_in_pat_row_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_pat_row_subst_pattern_in_pat_row_fresh : lngen.
#[export] Hint Rewrite ftvar_in_pat_row_subst_pattern_in_pat_row_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_pattern_subst_pattern_in_pattern_lower_mutual :
(forall P1 P2 X1,
  remove X1 (ftvar_in_pattern P1) [<=] ftvar_in_pattern (subst_pattern_in_pattern P2 X1 P1)).
Proof.
apply_mutual_ind pattern_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_pattern_subst_pattern_in_pattern_lower :
forall P1 P2 X1,
  remove X1 (ftvar_in_pattern P1) [<=] ftvar_in_pattern (subst_pattern_in_pattern P2 X1 P1).
Proof.
pose proof ftvar_in_pattern_subst_pattern_in_pattern_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_pattern_subst_pattern_in_pattern_lower : lngen.

(* begin hide *)

Lemma ftvar_in_bind_subst_pattern_in_bind_lower_mutual :
(forall b1 P1 X1,
  remove X1 (ftvar_in_bind b1) [<=] ftvar_in_bind (subst_pattern_in_bind P1 X1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_bind_subst_pattern_in_bind_lower :
forall b1 P1 X1,
  remove X1 (ftvar_in_bind b1) [<=] ftvar_in_bind (subst_pattern_in_bind P1 X1 b1).
Proof.
pose proof ftvar_in_bind_subst_pattern_in_bind_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bind_subst_pattern_in_bind_lower : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_pattern_in_exp_lower_mutual :
(forall e1 P1 X1,
  remove X1 (ftvar_in_exp e1) [<=] ftvar_in_exp (subst_pattern_in_exp P1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_pattern_in_exp_lower :
forall e1 P1 X1,
  remove X1 (ftvar_in_exp e1) [<=] ftvar_in_exp (subst_pattern_in_exp P1 X1 e1).
Proof.
pose proof ftvar_in_exp_subst_pattern_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_pattern_in_exp_lower : lngen.

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

Lemma fvar_in_exp_subst_pattern_in_exp_lower_mutual :
(forall e1 P1 X1,
  fvar_in_exp e1 [<=] fvar_in_exp (subst_pattern_in_exp P1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_exp_subst_pattern_in_exp_lower :
forall e1 P1 X1,
  fvar_in_exp e1 [<=] fvar_in_exp (subst_pattern_in_exp P1 X1 e1).
Proof.
pose proof fvar_in_exp_subst_pattern_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_pattern_in_exp_lower : lngen.

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

Lemma ftvar_in_pat_row_subst_pattern_in_pat_row_lower_mutual :
(forall p1 P1 X1,
  remove X1 (ftvar_in_pat_row p1) [<=] ftvar_in_pat_row (subst_pattern_in_pat_row P1 X1 p1)).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_pat_row_subst_pattern_in_pat_row_lower :
forall p1 P1 X1,
  remove X1 (ftvar_in_pat_row p1) [<=] ftvar_in_pat_row (subst_pattern_in_pat_row P1 X1 p1).
Proof.
pose proof ftvar_in_pat_row_subst_pattern_in_pat_row_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_pat_row_subst_pattern_in_pat_row_lower : lngen.

(* begin hide *)

Lemma ftvar_in_pattern_subst_pattern_in_pattern_notin_mutual :
(forall P1 P2 X1 X2,
  X2 `notin` ftvar_in_pattern P1 ->
  X2 `notin` ftvar_in_pattern P2 ->
  X2 `notin` ftvar_in_pattern (subst_pattern_in_pattern P2 X1 P1)).
Proof.
apply_mutual_ind pattern_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_pattern_subst_pattern_in_pattern_notin :
forall P1 P2 X1 X2,
  X2 `notin` ftvar_in_pattern P1 ->
  X2 `notin` ftvar_in_pattern P2 ->
  X2 `notin` ftvar_in_pattern (subst_pattern_in_pattern P2 X1 P1).
Proof.
pose proof ftvar_in_pattern_subst_pattern_in_pattern_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_pattern_subst_pattern_in_pattern_notin : lngen.

(* begin hide *)

Lemma ftvar_in_bind_subst_pattern_in_bind_notin_mutual :
(forall b1 P1 X1 X2,
  X2 `notin` ftvar_in_bind b1 ->
  X2 `notin` ftvar_in_pattern P1 ->
  X2 `notin` ftvar_in_bind (subst_pattern_in_bind P1 X1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_bind_subst_pattern_in_bind_notin :
forall b1 P1 X1 X2,
  X2 `notin` ftvar_in_bind b1 ->
  X2 `notin` ftvar_in_pattern P1 ->
  X2 `notin` ftvar_in_bind (subst_pattern_in_bind P1 X1 b1).
Proof.
pose proof ftvar_in_bind_subst_pattern_in_bind_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bind_subst_pattern_in_bind_notin : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_pattern_in_exp_notin_mutual :
(forall e1 P1 X1 X2,
  X2 `notin` ftvar_in_exp e1 ->
  X2 `notin` ftvar_in_pattern P1 ->
  X2 `notin` ftvar_in_exp (subst_pattern_in_exp P1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_pattern_in_exp_notin :
forall e1 P1 X1 X2,
  X2 `notin` ftvar_in_exp e1 ->
  X2 `notin` ftvar_in_pattern P1 ->
  X2 `notin` ftvar_in_exp (subst_pattern_in_exp P1 X1 e1).
Proof.
pose proof ftvar_in_exp_subst_pattern_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_pattern_in_exp_notin : lngen.

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

Lemma fvar_in_exp_subst_pattern_in_exp_notin_mutual :
(forall e1 P1 X1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_pattern_in_exp P1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_exp_subst_pattern_in_exp_notin :
forall e1 P1 X1 x1,
  x1 `notin` fvar_in_exp e1 ->
  x1 `notin` fvar_in_exp (subst_pattern_in_exp P1 X1 e1).
Proof.
pose proof fvar_in_exp_subst_pattern_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_pattern_in_exp_notin : lngen.

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

Lemma ftvar_in_pat_row_subst_pattern_in_pat_row_notin_mutual :
(forall p1 P1 X1 X2,
  X2 `notin` ftvar_in_pat_row p1 ->
  X2 `notin` ftvar_in_pattern P1 ->
  X2 `notin` ftvar_in_pat_row (subst_pattern_in_pat_row P1 X1 p1)).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_pat_row_subst_pattern_in_pat_row_notin :
forall p1 P1 X1 X2,
  X2 `notin` ftvar_in_pat_row p1 ->
  X2 `notin` ftvar_in_pattern P1 ->
  X2 `notin` ftvar_in_pat_row (subst_pattern_in_pat_row P1 X1 p1).
Proof.
pose proof ftvar_in_pat_row_subst_pattern_in_pat_row_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_pat_row_subst_pattern_in_pat_row_notin : lngen.

(* begin hide *)

Lemma ftvar_in_pattern_subst_pattern_in_pattern_upper_mutual :
(forall P1 P2 X1,
  ftvar_in_pattern (subst_pattern_in_pattern P2 X1 P1) [<=] ftvar_in_pattern P2 `union` remove X1 (ftvar_in_pattern P1)).
Proof.
apply_mutual_ind pattern_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_pattern_subst_pattern_in_pattern_upper :
forall P1 P2 X1,
  ftvar_in_pattern (subst_pattern_in_pattern P2 X1 P1) [<=] ftvar_in_pattern P2 `union` remove X1 (ftvar_in_pattern P1).
Proof.
pose proof ftvar_in_pattern_subst_pattern_in_pattern_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_pattern_subst_pattern_in_pattern_upper : lngen.

(* begin hide *)

Lemma ftvar_in_bind_subst_pattern_in_bind_upper_mutual :
(forall b1 P1 X1,
  ftvar_in_bind (subst_pattern_in_bind P1 X1 b1) [<=] ftvar_in_pattern P1 `union` remove X1 (ftvar_in_bind b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_bind_subst_pattern_in_bind_upper :
forall b1 P1 X1,
  ftvar_in_bind (subst_pattern_in_bind P1 X1 b1) [<=] ftvar_in_pattern P1 `union` remove X1 (ftvar_in_bind b1).
Proof.
pose proof ftvar_in_bind_subst_pattern_in_bind_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_bind_subst_pattern_in_bind_upper : lngen.

(* begin hide *)

Lemma ftvar_in_exp_subst_pattern_in_exp_upper_mutual :
(forall e1 P1 X1,
  ftvar_in_exp (subst_pattern_in_exp P1 X1 e1) [<=] ftvar_in_pattern P1 `union` remove X1 (ftvar_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_exp_subst_pattern_in_exp_upper :
forall e1 P1 X1,
  ftvar_in_exp (subst_pattern_in_exp P1 X1 e1) [<=] ftvar_in_pattern P1 `union` remove X1 (ftvar_in_exp e1).
Proof.
pose proof ftvar_in_exp_subst_pattern_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_exp_subst_pattern_in_exp_upper : lngen.

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

Lemma fvar_in_exp_subst_pattern_in_exp_upper_mutual :
(forall e1 P1 X1,
  fvar_in_exp (subst_pattern_in_exp P1 X1 e1) [<=] fvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_exp_subst_pattern_in_exp_upper :
forall e1 P1 X1,
  fvar_in_exp (subst_pattern_in_exp P1 X1 e1) [<=] fvar_in_exp e1.
Proof.
pose proof fvar_in_exp_subst_pattern_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_exp_subst_pattern_in_exp_upper : lngen.

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

(* begin hide *)

Lemma ftvar_in_pat_row_subst_pattern_in_pat_row_upper_mutual :
(forall p1 P1 X1,
  ftvar_in_pat_row (subst_pattern_in_pat_row P1 X1 p1) [<=] ftvar_in_pattern P1 `union` remove X1 (ftvar_in_pat_row p1)).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_pat_row_subst_pattern_in_pat_row_upper :
forall p1 P1 X1,
  ftvar_in_pat_row (subst_pattern_in_pat_row P1 X1 p1) [<=] ftvar_in_pattern P1 `union` remove X1 (ftvar_in_pat_row p1).
Proof.
pose proof ftvar_in_pat_row_subst_pattern_in_pat_row_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_pat_row_subst_pattern_in_pat_row_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_pattern_in_pattern_close_pattern_wrt_pattern_rec_mutual :
(forall P2 P1 X1 X2 n1,
  degree_pattern_wrt_pattern n1 P1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_pattern P1 ->
  subst_pattern_in_pattern P1 X1 (close_pattern_wrt_pattern_rec n1 X2 P2) = close_pattern_wrt_pattern_rec n1 X2 (subst_pattern_in_pattern P1 X1 P2)).
Proof.
apply_mutual_ind pattern_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_pattern_close_pattern_wrt_pattern_rec :
forall P2 P1 X1 X2 n1,
  degree_pattern_wrt_pattern n1 P1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_pattern P1 ->
  subst_pattern_in_pattern P1 X1 (close_pattern_wrt_pattern_rec n1 X2 P2) = close_pattern_wrt_pattern_rec n1 X2 (subst_pattern_in_pattern P1 X1 P2).
Proof.
pose proof subst_pattern_in_pattern_close_pattern_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_pattern_close_pattern_wrt_pattern_rec : lngen.

(* begin hide *)

Lemma subst_pattern_in_bind_close_bind_wrt_pattern_rec_mutual :
(forall b1 P1 X1 X2 n1,
  degree_pattern_wrt_pattern n1 P1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_pattern P1 ->
  subst_pattern_in_bind P1 X1 (close_bind_wrt_pattern_rec n1 X2 b1) = close_bind_wrt_pattern_rec n1 X2 (subst_pattern_in_bind P1 X1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_bind_close_bind_wrt_pattern_rec :
forall b1 P1 X1 X2 n1,
  degree_pattern_wrt_pattern n1 P1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_pattern P1 ->
  subst_pattern_in_bind P1 X1 (close_bind_wrt_pattern_rec n1 X2 b1) = close_bind_wrt_pattern_rec n1 X2 (subst_pattern_in_bind P1 X1 b1).
Proof.
pose proof subst_pattern_in_bind_close_bind_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_bind_close_bind_wrt_pattern_rec : lngen.

(* begin hide *)

Lemma subst_pattern_in_exp_close_exp_wrt_pattern_rec_mutual :
(forall e1 P1 X1 X2 n1,
  degree_pattern_wrt_pattern n1 P1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_pattern P1 ->
  subst_pattern_in_exp P1 X1 (close_exp_wrt_pattern_rec n1 X2 e1) = close_exp_wrt_pattern_rec n1 X2 (subst_pattern_in_exp P1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_exp_close_exp_wrt_pattern_rec :
forall e1 P1 X1 X2 n1,
  degree_pattern_wrt_pattern n1 P1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_pattern P1 ->
  subst_pattern_in_exp P1 X1 (close_exp_wrt_pattern_rec n1 X2 e1) = close_exp_wrt_pattern_rec n1 X2 (subst_pattern_in_exp P1 X1 e1).
Proof.
pose proof subst_pattern_in_exp_close_exp_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_close_exp_wrt_pattern_rec : lngen.

(* begin hide *)

Lemma subst_pattern_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 P1 x1 X1 n1,
  subst_pattern_in_exp P1 x1 (close_exp_wrt_exp_rec n1 X1 e1) = close_exp_wrt_exp_rec n1 X1 (subst_pattern_in_exp P1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_exp_close_exp_wrt_exp_rec :
forall e1 P1 x1 X1 n1,
  subst_pattern_in_exp P1 x1 (close_exp_wrt_exp_rec n1 X1 e1) = close_exp_wrt_exp_rec n1 X1 (subst_pattern_in_exp P1 x1 e1).
Proof.
pose proof subst_pattern_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_close_exp_wrt_exp_rec : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_pattern_rec_mutual :
(forall e2 e1 X1 x1 n1,
  degree_exp_wrt_pattern n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_exp e1 X1 (close_exp_wrt_pattern_rec n1 x1 e2) = close_exp_wrt_pattern_rec n1 x1 (subst_exp_in_exp e1 X1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_close_exp_wrt_pattern_rec :
forall e2 e1 X1 x1 n1,
  degree_exp_wrt_pattern n1 e1 ->
  x1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_exp e1 X1 (close_exp_wrt_pattern_rec n1 x1 e2) = close_exp_wrt_pattern_rec n1 x1 (subst_exp_in_exp e1 X1 e2).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_pattern_rec : lngen.

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

(* begin hide *)

Lemma subst_pattern_in_pat_row_close_pat_row_wrt_pattern_rec_mutual :
(forall p1 P1 X1 X2 n1,
  degree_pattern_wrt_pattern n1 P1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_pattern P1 ->
  subst_pattern_in_pat_row P1 X1 (close_pat_row_wrt_pattern_rec n1 X2 p1) = close_pat_row_wrt_pattern_rec n1 X2 (subst_pattern_in_pat_row P1 X1 p1)).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_pat_row_close_pat_row_wrt_pattern_rec :
forall p1 P1 X1 X2 n1,
  degree_pattern_wrt_pattern n1 P1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_pattern P1 ->
  subst_pattern_in_pat_row P1 X1 (close_pat_row_wrt_pattern_rec n1 X2 p1) = close_pat_row_wrt_pattern_rec n1 X2 (subst_pattern_in_pat_row P1 X1 p1).
Proof.
pose proof subst_pattern_in_pat_row_close_pat_row_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_pat_row_close_pat_row_wrt_pattern_rec : lngen.

Lemma subst_pattern_in_pattern_close_pattern_wrt_pattern :
forall P2 P1 X1 X2,
  lc_pattern P1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_pattern P1 ->
  subst_pattern_in_pattern P1 X1 (close_pattern_wrt_pattern X2 P2) = close_pattern_wrt_pattern X2 (subst_pattern_in_pattern P1 X1 P2).
Proof.
unfold close_pattern_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_pattern_close_pattern_wrt_pattern : lngen.

Lemma subst_pattern_in_bind_close_bind_wrt_pattern :
forall b1 P1 X1 X2,
  lc_pattern P1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_pattern P1 ->
  subst_pattern_in_bind P1 X1 (close_bind_wrt_pattern X2 b1) = close_bind_wrt_pattern X2 (subst_pattern_in_bind P1 X1 b1).
Proof.
unfold close_bind_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_bind_close_bind_wrt_pattern : lngen.

Lemma subst_pattern_in_exp_close_exp_wrt_pattern :
forall e1 P1 X1 X2,
  lc_pattern P1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_pattern P1 ->
  subst_pattern_in_exp P1 X1 (close_exp_wrt_pattern X2 e1) = close_exp_wrt_pattern X2 (subst_pattern_in_exp P1 X1 e1).
Proof.
unfold close_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_close_exp_wrt_pattern : lngen.

Lemma subst_pattern_in_exp_close_exp_wrt_exp :
forall e1 P1 x1 X1,
  lc_pattern P1 ->  subst_pattern_in_exp P1 x1 (close_exp_wrt_exp X1 e1) = close_exp_wrt_exp X1 (subst_pattern_in_exp P1 x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_close_exp_wrt_exp : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_pattern :
forall e2 e1 X1 x1,
  lc_exp e1 ->  x1 `notin` ftvar_in_exp e1 ->
  subst_exp_in_exp e1 X1 (close_exp_wrt_pattern x1 e2) = close_exp_wrt_pattern x1 (subst_exp_in_exp e1 X1 e2).
Proof.
unfold close_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_pattern : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_exp :
forall e2 e1 x1 x2,
  lc_exp e1 ->  x1 <> x2 ->
  x2 `notin` fvar_in_exp e1 ->
  subst_exp_in_exp e1 x1 (close_exp_wrt_exp x2 e2) = close_exp_wrt_exp x2 (subst_exp_in_exp e1 x1 e2).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_exp : lngen.

Lemma subst_pattern_in_pat_row_close_pat_row_wrt_pattern :
forall p1 P1 X1 X2,
  lc_pattern P1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_pattern P1 ->
  subst_pattern_in_pat_row P1 X1 (close_pat_row_wrt_pattern X2 p1) = close_pat_row_wrt_pattern X2 (subst_pattern_in_pat_row P1 X1 p1).
Proof.
unfold close_pat_row_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_pat_row_close_pat_row_wrt_pattern : lngen.

(* begin hide *)

Lemma subst_pattern_in_pattern_degree_pattern_wrt_pattern_mutual :
(forall P1 P2 X1 n1,
  degree_pattern_wrt_pattern n1 P1 ->
  degree_pattern_wrt_pattern n1 P2 ->
  degree_pattern_wrt_pattern n1 (subst_pattern_in_pattern P2 X1 P1)).
Proof.
apply_mutual_ind pattern_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_pattern_degree_pattern_wrt_pattern :
forall P1 P2 X1 n1,
  degree_pattern_wrt_pattern n1 P1 ->
  degree_pattern_wrt_pattern n1 P2 ->
  degree_pattern_wrt_pattern n1 (subst_pattern_in_pattern P2 X1 P1).
Proof.
pose proof subst_pattern_in_pattern_degree_pattern_wrt_pattern_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_pattern_degree_pattern_wrt_pattern : lngen.

(* begin hide *)

Lemma subst_pattern_in_bind_degree_bind_wrt_pattern_mutual :
(forall b1 P1 X1 n1,
  degree_bind_wrt_pattern n1 b1 ->
  degree_pattern_wrt_pattern n1 P1 ->
  degree_bind_wrt_pattern n1 (subst_pattern_in_bind P1 X1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_bind_degree_bind_wrt_pattern :
forall b1 P1 X1 n1,
  degree_bind_wrt_pattern n1 b1 ->
  degree_pattern_wrt_pattern n1 P1 ->
  degree_bind_wrt_pattern n1 (subst_pattern_in_bind P1 X1 b1).
Proof.
pose proof subst_pattern_in_bind_degree_bind_wrt_pattern_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_bind_degree_bind_wrt_pattern : lngen.

(* begin hide *)

Lemma subst_pattern_in_exp_degree_exp_wrt_pattern_mutual :
(forall e1 P1 X1 n1,
  degree_exp_wrt_pattern n1 e1 ->
  degree_pattern_wrt_pattern n1 P1 ->
  degree_exp_wrt_pattern n1 (subst_pattern_in_exp P1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_exp_degree_exp_wrt_pattern :
forall e1 P1 X1 n1,
  degree_exp_wrt_pattern n1 e1 ->
  degree_pattern_wrt_pattern n1 P1 ->
  degree_exp_wrt_pattern n1 (subst_pattern_in_exp P1 X1 e1).
Proof.
pose proof subst_pattern_in_exp_degree_exp_wrt_pattern_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_degree_exp_wrt_pattern : lngen.

(* begin hide *)

Lemma subst_pattern_in_exp_degree_exp_wrt_exp_mutual :
(forall e1 P1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (subst_pattern_in_exp P1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_exp_degree_exp_wrt_exp :
forall e1 P1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (subst_pattern_in_exp P1 X1 e1).
Proof.
pose proof subst_pattern_in_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_pattern_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_pattern n1 e1 ->
  degree_exp_wrt_pattern n1 e2 ->
  degree_exp_wrt_pattern n1 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_pattern :
forall e1 e2 x1 n1,
  degree_exp_wrt_pattern n1 e1 ->
  degree_exp_wrt_pattern n1 e2 ->
  degree_exp_wrt_pattern n1 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_degree_exp_wrt_pattern_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_degree_exp_wrt_pattern : lngen.

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

Lemma subst_pattern_in_pat_row_degree_pat_row_wrt_pattern_mutual :
(forall p1 P1 X1 n1,
  degree_pat_row_wrt_pattern n1 p1 ->
  degree_pattern_wrt_pattern n1 P1 ->
  degree_pat_row_wrt_pattern n1 (subst_pattern_in_pat_row P1 X1 p1)).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_pat_row_degree_pat_row_wrt_pattern :
forall p1 P1 X1 n1,
  degree_pat_row_wrt_pattern n1 p1 ->
  degree_pattern_wrt_pattern n1 P1 ->
  degree_pat_row_wrt_pattern n1 (subst_pattern_in_pat_row P1 X1 p1).
Proof.
pose proof subst_pattern_in_pat_row_degree_pat_row_wrt_pattern_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_pat_row_degree_pat_row_wrt_pattern : lngen.

(* begin hide *)

Lemma subst_pattern_in_pattern_fresh_eq_mutual :
(forall P2 P1 X1,
  X1 `notin` ftvar_in_pattern P2 ->
  subst_pattern_in_pattern P1 X1 P2 = P2).
Proof.
apply_mutual_ind pattern_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_pattern_fresh_eq :
forall P2 P1 X1,
  X1 `notin` ftvar_in_pattern P2 ->
  subst_pattern_in_pattern P1 X1 P2 = P2.
Proof.
pose proof subst_pattern_in_pattern_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_pattern_fresh_eq : lngen.
#[export] Hint Rewrite subst_pattern_in_pattern_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_pattern_in_bind_fresh_eq_mutual :
(forall b1 P1 X1,
  X1 `notin` ftvar_in_bind b1 ->
  subst_pattern_in_bind P1 X1 b1 = b1).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_bind_fresh_eq :
forall b1 P1 X1,
  X1 `notin` ftvar_in_bind b1 ->
  subst_pattern_in_bind P1 X1 b1 = b1.
Proof.
pose proof subst_pattern_in_bind_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_bind_fresh_eq : lngen.
#[export] Hint Rewrite subst_pattern_in_bind_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_pattern_in_exp_fresh_eq_mutual :
(forall e1 P1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_pattern_in_exp P1 X1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_exp_fresh_eq :
forall e1 P1 X1,
  X1 `notin` ftvar_in_exp e1 ->
  subst_pattern_in_exp P1 X1 e1 = e1.
Proof.
pose proof subst_pattern_in_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_fresh_eq : lngen.
#[export] Hint Rewrite subst_pattern_in_exp_fresh_eq using solve [auto] : lngen.

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

Lemma subst_pattern_in_pat_row_fresh_eq_mutual :
(forall p1 P1 X1,
  X1 `notin` ftvar_in_pat_row p1 ->
  subst_pattern_in_pat_row P1 X1 p1 = p1).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_pat_row_fresh_eq :
forall p1 P1 X1,
  X1 `notin` ftvar_in_pat_row p1 ->
  subst_pattern_in_pat_row P1 X1 p1 = p1.
Proof.
pose proof subst_pattern_in_pat_row_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_pat_row_fresh_eq : lngen.
#[export] Hint Rewrite subst_pattern_in_pat_row_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_pattern_in_pattern_fresh_same_mutual :
(forall P2 P1 X1,
  X1 `notin` ftvar_in_pattern P1 ->
  X1 `notin` ftvar_in_pattern (subst_pattern_in_pattern P1 X1 P2)).
Proof.
apply_mutual_ind pattern_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_pattern_fresh_same :
forall P2 P1 X1,
  X1 `notin` ftvar_in_pattern P1 ->
  X1 `notin` ftvar_in_pattern (subst_pattern_in_pattern P1 X1 P2).
Proof.
pose proof subst_pattern_in_pattern_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_pattern_fresh_same : lngen.

(* begin hide *)

Lemma subst_pattern_in_bind_fresh_same_mutual :
(forall b1 P1 X1,
  X1 `notin` ftvar_in_pattern P1 ->
  X1 `notin` ftvar_in_bind (subst_pattern_in_bind P1 X1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_bind_fresh_same :
forall b1 P1 X1,
  X1 `notin` ftvar_in_pattern P1 ->
  X1 `notin` ftvar_in_bind (subst_pattern_in_bind P1 X1 b1).
Proof.
pose proof subst_pattern_in_bind_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_bind_fresh_same : lngen.

(* begin hide *)

Lemma subst_pattern_in_exp_fresh_same_mutual :
(forall e1 P1 X1,
  X1 `notin` ftvar_in_pattern P1 ->
  X1 `notin` ftvar_in_exp (subst_pattern_in_exp P1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_exp_fresh_same :
forall e1 P1 X1,
  X1 `notin` ftvar_in_pattern P1 ->
  X1 `notin` ftvar_in_exp (subst_pattern_in_exp P1 X1 e1).
Proof.
pose proof subst_pattern_in_exp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_fresh_same : lngen.

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

Lemma subst_pattern_in_pat_row_fresh_same_mutual :
(forall p1 P1 X1,
  X1 `notin` ftvar_in_pattern P1 ->
  X1 `notin` ftvar_in_pat_row (subst_pattern_in_pat_row P1 X1 p1)).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_pat_row_fresh_same :
forall p1 P1 X1,
  X1 `notin` ftvar_in_pattern P1 ->
  X1 `notin` ftvar_in_pat_row (subst_pattern_in_pat_row P1 X1 p1).
Proof.
pose proof subst_pattern_in_pat_row_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_pat_row_fresh_same : lngen.

(* begin hide *)

Lemma subst_pattern_in_pattern_fresh_mutual :
(forall P2 P1 X1 X2,
  X1 `notin` ftvar_in_pattern P2 ->
  X1 `notin` ftvar_in_pattern P1 ->
  X1 `notin` ftvar_in_pattern (subst_pattern_in_pattern P1 X2 P2)).
Proof.
apply_mutual_ind pattern_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_pattern_fresh :
forall P2 P1 X1 X2,
  X1 `notin` ftvar_in_pattern P2 ->
  X1 `notin` ftvar_in_pattern P1 ->
  X1 `notin` ftvar_in_pattern (subst_pattern_in_pattern P1 X2 P2).
Proof.
pose proof subst_pattern_in_pattern_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_pattern_fresh : lngen.

(* begin hide *)

Lemma subst_pattern_in_bind_fresh_mutual :
(forall b1 P1 X1 X2,
  X1 `notin` ftvar_in_bind b1 ->
  X1 `notin` ftvar_in_pattern P1 ->
  X1 `notin` ftvar_in_bind (subst_pattern_in_bind P1 X2 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_bind_fresh :
forall b1 P1 X1 X2,
  X1 `notin` ftvar_in_bind b1 ->
  X1 `notin` ftvar_in_pattern P1 ->
  X1 `notin` ftvar_in_bind (subst_pattern_in_bind P1 X2 b1).
Proof.
pose proof subst_pattern_in_bind_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_bind_fresh : lngen.

(* begin hide *)

Lemma subst_pattern_in_exp_fresh_mutual :
(forall e1 P1 X1 X2,
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_pattern P1 ->
  X1 `notin` ftvar_in_exp (subst_pattern_in_exp P1 X2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_exp_fresh :
forall e1 P1 X1 X2,
  X1 `notin` ftvar_in_exp e1 ->
  X1 `notin` ftvar_in_pattern P1 ->
  X1 `notin` ftvar_in_exp (subst_pattern_in_exp P1 X2 e1).
Proof.
pose proof subst_pattern_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_fresh : lngen.

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

(* begin hide *)

Lemma subst_pattern_in_pat_row_fresh_mutual :
(forall p1 P1 X1 X2,
  X1 `notin` ftvar_in_pat_row p1 ->
  X1 `notin` ftvar_in_pattern P1 ->
  X1 `notin` ftvar_in_pat_row (subst_pattern_in_pat_row P1 X2 p1)).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_pat_row_fresh :
forall p1 P1 X1 X2,
  X1 `notin` ftvar_in_pat_row p1 ->
  X1 `notin` ftvar_in_pattern P1 ->
  X1 `notin` ftvar_in_pat_row (subst_pattern_in_pat_row P1 X2 p1).
Proof.
pose proof subst_pattern_in_pat_row_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_pat_row_fresh : lngen.

Lemma subst_pattern_in_pattern_lc_pattern :
forall P1 P2 X1,
  lc_pattern P1 ->
  lc_pattern P2 ->
  lc_pattern (subst_pattern_in_pattern P2 X1 P1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_pattern_lc_pattern : lngen.

Lemma subst_pattern_in_bind_lc_bind :
forall b1 P1 X1,
  lc_bind b1 ->
  lc_pattern P1 ->
  lc_bind (subst_pattern_in_bind P1 X1 b1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_bind_lc_bind : lngen.

Lemma subst_pattern_in_exp_lc_exp :
forall e1 P1 X1,
  lc_exp e1 ->
  lc_pattern P1 ->
  lc_exp (subst_pattern_in_exp P1 X1 e1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_lc_exp : lngen.

Lemma subst_exp_in_exp_lc_exp :
forall e1 e2 x1,
  lc_exp e1 ->
  lc_exp e2 ->
  lc_exp (subst_exp_in_exp e2 x1 e1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_lc_exp : lngen.

Lemma subst_pattern_in_pat_row_lc_pat_row :
forall p1 P1 X1,
  lc_pat_row p1 ->
  lc_pattern P1 ->
  lc_pat_row (subst_pattern_in_pat_row P1 X1 p1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_pat_row_lc_pat_row : lngen.

(* begin hide *)

Lemma subst_pattern_in_pattern_open_pattern_wrt_pattern_rec_mutual :
(forall P3 P1 P2 X1 n1,
  lc_pattern P1 ->
  subst_pattern_in_pattern P1 X1 (open_pattern_wrt_pattern_rec n1 P2 P3) = open_pattern_wrt_pattern_rec n1 (subst_pattern_in_pattern P1 X1 P2) (subst_pattern_in_pattern P1 X1 P3)).
Proof.
apply_mutual_ind pattern_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_pattern_open_pattern_wrt_pattern_rec :
forall P3 P1 P2 X1 n1,
  lc_pattern P1 ->
  subst_pattern_in_pattern P1 X1 (open_pattern_wrt_pattern_rec n1 P2 P3) = open_pattern_wrt_pattern_rec n1 (subst_pattern_in_pattern P1 X1 P2) (subst_pattern_in_pattern P1 X1 P3).
Proof.
pose proof subst_pattern_in_pattern_open_pattern_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_pattern_open_pattern_wrt_pattern_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_bind_open_bind_wrt_pattern_rec_mutual :
(forall b1 P1 P2 X1 n1,
  lc_pattern P1 ->
  subst_pattern_in_bind P1 X1 (open_bind_wrt_pattern_rec n1 P2 b1) = open_bind_wrt_pattern_rec n1 (subst_pattern_in_pattern P1 X1 P2) (subst_pattern_in_bind P1 X1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_bind_open_bind_wrt_pattern_rec :
forall b1 P1 P2 X1 n1,
  lc_pattern P1 ->
  subst_pattern_in_bind P1 X1 (open_bind_wrt_pattern_rec n1 P2 b1) = open_bind_wrt_pattern_rec n1 (subst_pattern_in_pattern P1 X1 P2) (subst_pattern_in_bind P1 X1 b1).
Proof.
pose proof subst_pattern_in_bind_open_bind_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_bind_open_bind_wrt_pattern_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_exp_open_exp_wrt_pattern_rec_mutual :
(forall e1 P1 P2 X1 n1,
  lc_pattern P1 ->
  subst_pattern_in_exp P1 X1 (open_exp_wrt_pattern_rec n1 P2 e1) = open_exp_wrt_pattern_rec n1 (subst_pattern_in_pattern P1 X1 P2) (subst_pattern_in_exp P1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_exp_open_exp_wrt_pattern_rec :
forall e1 P1 P2 X1 n1,
  lc_pattern P1 ->
  subst_pattern_in_exp P1 X1 (open_exp_wrt_pattern_rec n1 P2 e1) = open_exp_wrt_pattern_rec n1 (subst_pattern_in_pattern P1 X1 P2) (subst_pattern_in_exp P1 X1 e1).
Proof.
pose proof subst_pattern_in_exp_open_exp_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_open_exp_wrt_pattern_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_exp_open_exp_wrt_exp_rec_mutual :
(forall e2 P1 e1 X1 n1,
  subst_pattern_in_exp P1 X1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (subst_pattern_in_exp P1 X1 e1) (subst_pattern_in_exp P1 X1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_exp_open_exp_wrt_exp_rec :
forall e2 P1 e1 X1 n1,
  subst_pattern_in_exp P1 X1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (subst_pattern_in_exp P1 X1 e1) (subst_pattern_in_exp P1 X1 e2).
Proof.
pose proof subst_pattern_in_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_pattern_rec_mutual :
(forall e2 e1 P1 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_pattern_rec n1 P1 e2) = open_exp_wrt_pattern_rec n1 P1 (subst_exp_in_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_pattern_rec :
forall e2 e1 P1 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_pattern_rec n1 P1 e2) = open_exp_wrt_pattern_rec n1 P1 (subst_exp_in_exp e1 x1 e2).
Proof.
pose proof subst_exp_in_exp_open_exp_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_pattern_rec : lngen.

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

(* begin hide *)

Lemma subst_pattern_in_pat_row_open_pat_row_wrt_pattern_rec_mutual :
(forall p1 P1 P2 X1 n1,
  lc_pattern P1 ->
  subst_pattern_in_pat_row P1 X1 (open_pat_row_wrt_pattern_rec n1 P2 p1) = open_pat_row_wrt_pattern_rec n1 (subst_pattern_in_pattern P1 X1 P2) (subst_pattern_in_pat_row P1 X1 p1)).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_pat_row_open_pat_row_wrt_pattern_rec :
forall p1 P1 P2 X1 n1,
  lc_pattern P1 ->
  subst_pattern_in_pat_row P1 X1 (open_pat_row_wrt_pattern_rec n1 P2 p1) = open_pat_row_wrt_pattern_rec n1 (subst_pattern_in_pattern P1 X1 P2) (subst_pattern_in_pat_row P1 X1 p1).
Proof.
pose proof subst_pattern_in_pat_row_open_pat_row_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_pat_row_open_pat_row_wrt_pattern_rec : lngen.

(* end hide *)

Lemma subst_pattern_in_pattern_open_pattern_wrt_pattern :
forall P3 P1 P2 X1,
  lc_pattern P1 ->
  subst_pattern_in_pattern P1 X1 (open_pattern_wrt_pattern P3 P2) = open_pattern_wrt_pattern (subst_pattern_in_pattern P1 X1 P3) (subst_pattern_in_pattern P1 X1 P2).
Proof.
unfold open_pattern_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_pattern_open_pattern_wrt_pattern : lngen.

Lemma subst_pattern_in_bind_open_bind_wrt_pattern :
forall b1 P1 P2 X1,
  lc_pattern P1 ->
  subst_pattern_in_bind P1 X1 (open_bind_wrt_pattern b1 P2) = open_bind_wrt_pattern (subst_pattern_in_bind P1 X1 b1) (subst_pattern_in_pattern P1 X1 P2).
Proof.
unfold open_bind_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_bind_open_bind_wrt_pattern : lngen.

Lemma subst_pattern_in_exp_open_exp_wrt_pattern :
forall e1 P1 P2 X1,
  lc_pattern P1 ->
  subst_pattern_in_exp P1 X1 (open_exp_wrt_pattern e1 P2) = open_exp_wrt_pattern (subst_pattern_in_exp P1 X1 e1) (subst_pattern_in_pattern P1 X1 P2).
Proof.
unfold open_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_open_exp_wrt_pattern : lngen.

Lemma subst_pattern_in_exp_open_exp_wrt_exp :
forall e2 P1 e1 X1,
  subst_pattern_in_exp P1 X1 (open_exp_wrt_exp e2 e1) = open_exp_wrt_exp (subst_pattern_in_exp P1 X1 e2) (subst_pattern_in_exp P1 X1 e1).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_pattern :
forall e2 e1 P1 x1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_pattern e2 P1) = open_exp_wrt_pattern (subst_exp_in_exp e1 x1 e2) P1.
Proof.
unfold open_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_pattern : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_exp :
forall e3 e1 e2 x1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_exp e3 e2) = open_exp_wrt_exp (subst_exp_in_exp e1 x1 e3) (subst_exp_in_exp e1 x1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_exp : lngen.

Lemma subst_pattern_in_pat_row_open_pat_row_wrt_pattern :
forall p1 P1 P2 X1,
  lc_pattern P1 ->
  subst_pattern_in_pat_row P1 X1 (open_pat_row_wrt_pattern p1 P2) = open_pat_row_wrt_pattern (subst_pattern_in_pat_row P1 X1 p1) (subst_pattern_in_pattern P1 X1 P2).
Proof.
unfold open_pat_row_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_pat_row_open_pat_row_wrt_pattern : lngen.

Lemma subst_pattern_in_pattern_open_pattern_wrt_pattern_var :
forall P2 P1 X1 X2,
  X1 <> X2 ->
  lc_pattern P1 ->
  open_pattern_wrt_pattern (subst_pattern_in_pattern P1 X1 P2) (pattern_var_f X2) = subst_pattern_in_pattern P1 X1 (open_pattern_wrt_pattern P2 (pattern_var_f X2)).
Proof.
intros; rewrite subst_pattern_in_pattern_open_pattern_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_pattern_open_pattern_wrt_pattern_var : lngen.

Lemma subst_pattern_in_bind_open_bind_wrt_pattern_var :
forall b1 P1 X1 X2,
  X1 <> X2 ->
  lc_pattern P1 ->
  open_bind_wrt_pattern (subst_pattern_in_bind P1 X1 b1) (pattern_var_f X2) = subst_pattern_in_bind P1 X1 (open_bind_wrt_pattern b1 (pattern_var_f X2)).
Proof.
intros; rewrite subst_pattern_in_bind_open_bind_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_bind_open_bind_wrt_pattern_var : lngen.

Lemma subst_pattern_in_exp_open_exp_wrt_pattern_var :
forall e1 P1 X1 X2,
  X1 <> X2 ->
  lc_pattern P1 ->
  open_exp_wrt_pattern (subst_pattern_in_exp P1 X1 e1) (pattern_var_f X2) = subst_pattern_in_exp P1 X1 (open_exp_wrt_pattern e1 (pattern_var_f X2)).
Proof.
intros; rewrite subst_pattern_in_exp_open_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_open_exp_wrt_pattern_var : lngen.

Lemma subst_pattern_in_exp_open_exp_wrt_exp_var :
forall e1 P1 X1 x1,
  open_exp_wrt_exp (subst_pattern_in_exp P1 X1 e1) (exp_var_f x1) = subst_pattern_in_exp P1 X1 (open_exp_wrt_exp e1 (exp_var_f x1)).
Proof.
intros; rewrite subst_pattern_in_exp_open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_open_exp_wrt_exp_var : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_pattern_var :
forall e2 e1 x1 X1,
  lc_exp e1 ->
  open_exp_wrt_pattern (subst_exp_in_exp e1 x1 e2) (pattern_var_f X1) = subst_exp_in_exp e1 x1 (open_exp_wrt_pattern e2 (pattern_var_f X1)).
Proof.
intros; rewrite subst_exp_in_exp_open_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_pattern_var : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_exp_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_exp e1 ->
  open_exp_wrt_exp (subst_exp_in_exp e1 x1 e2) (exp_var_f x2) = subst_exp_in_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2)).
Proof.
intros; rewrite subst_exp_in_exp_open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_exp_var : lngen.

Lemma subst_pattern_in_pat_row_open_pat_row_wrt_pattern_var :
forall p1 P1 X1 X2,
  X1 <> X2 ->
  lc_pattern P1 ->
  open_pat_row_wrt_pattern (subst_pattern_in_pat_row P1 X1 p1) (pattern_var_f X2) = subst_pattern_in_pat_row P1 X1 (open_pat_row_wrt_pattern p1 (pattern_var_f X2)).
Proof.
intros; rewrite subst_pattern_in_pat_row_open_pat_row_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_pat_row_open_pat_row_wrt_pattern_var : lngen.

(* begin hide *)

Lemma subst_pattern_in_pattern_spec_rec_mutual :
(forall P1 P2 X1 n1,
  subst_pattern_in_pattern P2 X1 P1 = open_pattern_wrt_pattern_rec n1 P2 (close_pattern_wrt_pattern_rec n1 X1 P1)).
Proof.
apply_mutual_ind pattern_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_pattern_spec_rec :
forall P1 P2 X1 n1,
  subst_pattern_in_pattern P2 X1 P1 = open_pattern_wrt_pattern_rec n1 P2 (close_pattern_wrt_pattern_rec n1 X1 P1).
Proof.
pose proof subst_pattern_in_pattern_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_pattern_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_bind_spec_rec_mutual :
(forall b1 P1 X1 n1,
  subst_pattern_in_bind P1 X1 b1 = open_bind_wrt_pattern_rec n1 P1 (close_bind_wrt_pattern_rec n1 X1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_bind_spec_rec :
forall b1 P1 X1 n1,
  subst_pattern_in_bind P1 X1 b1 = open_bind_wrt_pattern_rec n1 P1 (close_bind_wrt_pattern_rec n1 X1 b1).
Proof.
pose proof subst_pattern_in_bind_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_bind_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_exp_spec_rec_mutual :
(forall e1 P1 X1 n1,
  subst_pattern_in_exp P1 X1 e1 = open_exp_wrt_pattern_rec n1 P1 (close_exp_wrt_pattern_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_exp_spec_rec :
forall e1 P1 X1 n1,
  subst_pattern_in_exp P1 X1 e1 = open_exp_wrt_pattern_rec n1 P1 (close_exp_wrt_pattern_rec n1 X1 e1).
Proof.
pose proof subst_pattern_in_exp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_spec_rec : lngen.

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

(* begin hide *)

Lemma subst_pattern_in_pat_row_spec_rec_mutual :
(forall p1 P1 X1 n1,
  subst_pattern_in_pat_row P1 X1 p1 = open_pat_row_wrt_pattern_rec n1 P1 (close_pat_row_wrt_pattern_rec n1 X1 p1)).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_pat_row_spec_rec :
forall p1 P1 X1 n1,
  subst_pattern_in_pat_row P1 X1 p1 = open_pat_row_wrt_pattern_rec n1 P1 (close_pat_row_wrt_pattern_rec n1 X1 p1).
Proof.
pose proof subst_pattern_in_pat_row_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_pat_row_spec_rec : lngen.

(* end hide *)

Lemma subst_pattern_in_pattern_spec :
forall P1 P2 X1,
  subst_pattern_in_pattern P2 X1 P1 = open_pattern_wrt_pattern (close_pattern_wrt_pattern X1 P1) P2.
Proof.
unfold close_pattern_wrt_pattern; unfold open_pattern_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_pattern_spec : lngen.

Lemma subst_pattern_in_bind_spec :
forall b1 P1 X1,
  subst_pattern_in_bind P1 X1 b1 = open_bind_wrt_pattern (close_bind_wrt_pattern X1 b1) P1.
Proof.
unfold close_bind_wrt_pattern; unfold open_bind_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_bind_spec : lngen.

Lemma subst_pattern_in_exp_spec :
forall e1 P1 X1,
  subst_pattern_in_exp P1 X1 e1 = open_exp_wrt_pattern (close_exp_wrt_pattern X1 e1) P1.
Proof.
unfold close_exp_wrt_pattern; unfold open_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_spec : lngen.

Lemma subst_exp_in_exp_spec :
forall e1 e2 x1,
  subst_exp_in_exp e2 x1 e1 = open_exp_wrt_exp (close_exp_wrt_exp x1 e1) e2.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_spec : lngen.

Lemma subst_pattern_in_pat_row_spec :
forall p1 P1 X1,
  subst_pattern_in_pat_row P1 X1 p1 = open_pat_row_wrt_pattern (close_pat_row_wrt_pattern X1 p1) P1.
Proof.
unfold close_pat_row_wrt_pattern; unfold open_pat_row_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_pat_row_spec : lngen.

(* begin hide *)

Lemma subst_pattern_in_pattern_subst_pattern_in_pattern_mutual :
(forall P1 P2 P3 X2 X1,
  X2 `notin` ftvar_in_pattern P2 ->
  X2 <> X1 ->
  subst_pattern_in_pattern P2 X1 (subst_pattern_in_pattern P3 X2 P1) = subst_pattern_in_pattern (subst_pattern_in_pattern P2 X1 P3) X2 (subst_pattern_in_pattern P2 X1 P1)).
Proof.
apply_mutual_ind pattern_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_pattern_subst_pattern_in_pattern :
forall P1 P2 P3 X2 X1,
  X2 `notin` ftvar_in_pattern P2 ->
  X2 <> X1 ->
  subst_pattern_in_pattern P2 X1 (subst_pattern_in_pattern P3 X2 P1) = subst_pattern_in_pattern (subst_pattern_in_pattern P2 X1 P3) X2 (subst_pattern_in_pattern P2 X1 P1).
Proof.
pose proof subst_pattern_in_pattern_subst_pattern_in_pattern_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_pattern_subst_pattern_in_pattern : lngen.

(* begin hide *)

Lemma subst_pattern_in_bind_subst_pattern_in_bind_mutual :
(forall b1 P1 P2 X2 X1,
  X2 `notin` ftvar_in_pattern P1 ->
  X2 <> X1 ->
  subst_pattern_in_bind P1 X1 (subst_pattern_in_bind P2 X2 b1) = subst_pattern_in_bind (subst_pattern_in_pattern P1 X1 P2) X2 (subst_pattern_in_bind P1 X1 b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_bind_subst_pattern_in_bind :
forall b1 P1 P2 X2 X1,
  X2 `notin` ftvar_in_pattern P1 ->
  X2 <> X1 ->
  subst_pattern_in_bind P1 X1 (subst_pattern_in_bind P2 X2 b1) = subst_pattern_in_bind (subst_pattern_in_pattern P1 X1 P2) X2 (subst_pattern_in_bind P1 X1 b1).
Proof.
pose proof subst_pattern_in_bind_subst_pattern_in_bind_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_bind_subst_pattern_in_bind : lngen.

(* begin hide *)

Lemma subst_pattern_in_exp_subst_pattern_in_exp_mutual :
(forall e1 P1 P2 X2 X1,
  X2 `notin` ftvar_in_pattern P1 ->
  X2 <> X1 ->
  subst_pattern_in_exp P1 X1 (subst_pattern_in_exp P2 X2 e1) = subst_pattern_in_exp (subst_pattern_in_pattern P1 X1 P2) X2 (subst_pattern_in_exp P1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_exp_subst_pattern_in_exp :
forall e1 P1 P2 X2 X1,
  X2 `notin` ftvar_in_pattern P1 ->
  X2 <> X1 ->
  subst_pattern_in_exp P1 X1 (subst_pattern_in_exp P2 X2 e1) = subst_pattern_in_exp (subst_pattern_in_pattern P1 X1 P2) X2 (subst_pattern_in_exp P1 X1 e1).
Proof.
pose proof subst_pattern_in_exp_subst_pattern_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_subst_pattern_in_exp : lngen.

(* begin hide *)

Lemma subst_pattern_in_exp_subst_exp_in_exp_mutual :
(forall e1 P1 e2 x1 X1,
  subst_pattern_in_exp P1 X1 (subst_exp_in_exp e2 x1 e1) = subst_exp_in_exp (subst_pattern_in_exp P1 X1 e2) x1 (subst_pattern_in_exp P1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_exp_subst_exp_in_exp :
forall e1 P1 e2 x1 X1,
  subst_pattern_in_exp P1 X1 (subst_exp_in_exp e2 x1 e1) = subst_exp_in_exp (subst_pattern_in_exp P1 X1 e2) x1 (subst_pattern_in_exp P1 X1 e1).
Proof.
pose proof subst_pattern_in_exp_subst_exp_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_subst_exp_in_exp : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_subst_pattern_in_exp_mutual :
(forall e1 e2 P1 X1 x1,
  X1 `notin` ftvar_in_exp e2 ->
  subst_exp_in_exp e2 x1 (subst_pattern_in_exp P1 X1 e1) = subst_pattern_in_exp P1 X1 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_subst_pattern_in_exp :
forall e1 e2 P1 X1 x1,
  X1 `notin` ftvar_in_exp e2 ->
  subst_exp_in_exp e2 x1 (subst_pattern_in_exp P1 X1 e1) = subst_pattern_in_exp P1 X1 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_subst_pattern_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_subst_pattern_in_exp : lngen.

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

Lemma subst_pattern_in_pat_row_subst_pattern_in_pat_row_mutual :
(forall p1 P1 P2 X2 X1,
  X2 `notin` ftvar_in_pattern P1 ->
  X2 <> X1 ->
  subst_pattern_in_pat_row P1 X1 (subst_pattern_in_pat_row P2 X2 p1) = subst_pattern_in_pat_row (subst_pattern_in_pattern P1 X1 P2) X2 (subst_pattern_in_pat_row P1 X1 p1)).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_pat_row_subst_pattern_in_pat_row :
forall p1 P1 P2 X2 X1,
  X2 `notin` ftvar_in_pattern P1 ->
  X2 <> X1 ->
  subst_pattern_in_pat_row P1 X1 (subst_pattern_in_pat_row P2 X2 p1) = subst_pattern_in_pat_row (subst_pattern_in_pattern P1 X1 P2) X2 (subst_pattern_in_pat_row P1 X1 p1).
Proof.
pose proof subst_pattern_in_pat_row_subst_pattern_in_pat_row_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_pat_row_subst_pattern_in_pat_row : lngen.

(* begin hide *)

Lemma subst_pattern_in_pattern_close_pattern_wrt_pattern_rec_open_pattern_wrt_pattern_rec_mutual :
(forall P2 P1 X1 X2 n1,
  X2 `notin` ftvar_in_pattern P2 ->
  X2 `notin` ftvar_in_pattern P1 ->
  X2 <> X1 ->
  degree_pattern_wrt_pattern n1 P1 ->
  subst_pattern_in_pattern P1 X1 P2 = close_pattern_wrt_pattern_rec n1 X2 (subst_pattern_in_pattern P1 X1 (open_pattern_wrt_pattern_rec n1 (pattern_var_f X2) P2))).
Proof.
apply_mutual_ind pattern_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_pattern_close_pattern_wrt_pattern_rec_open_pattern_wrt_pattern_rec :
forall P2 P1 X1 X2 n1,
  X2 `notin` ftvar_in_pattern P2 ->
  X2 `notin` ftvar_in_pattern P1 ->
  X2 <> X1 ->
  degree_pattern_wrt_pattern n1 P1 ->
  subst_pattern_in_pattern P1 X1 P2 = close_pattern_wrt_pattern_rec n1 X2 (subst_pattern_in_pattern P1 X1 (open_pattern_wrt_pattern_rec n1 (pattern_var_f X2) P2)).
Proof.
pose proof subst_pattern_in_pattern_close_pattern_wrt_pattern_rec_open_pattern_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_pattern_close_pattern_wrt_pattern_rec_open_pattern_wrt_pattern_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_bind_close_bind_wrt_pattern_rec_open_bind_wrt_pattern_rec_mutual :
(forall b1 P1 X1 X2 n1,
  X2 `notin` ftvar_in_bind b1 ->
  X2 `notin` ftvar_in_pattern P1 ->
  X2 <> X1 ->
  degree_pattern_wrt_pattern n1 P1 ->
  subst_pattern_in_bind P1 X1 b1 = close_bind_wrt_pattern_rec n1 X2 (subst_pattern_in_bind P1 X1 (open_bind_wrt_pattern_rec n1 (pattern_var_f X2) b1))).
Proof.
apply_mutual_ind bind_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_bind_close_bind_wrt_pattern_rec_open_bind_wrt_pattern_rec :
forall b1 P1 X1 X2 n1,
  X2 `notin` ftvar_in_bind b1 ->
  X2 `notin` ftvar_in_pattern P1 ->
  X2 <> X1 ->
  degree_pattern_wrt_pattern n1 P1 ->
  subst_pattern_in_bind P1 X1 b1 = close_bind_wrt_pattern_rec n1 X2 (subst_pattern_in_bind P1 X1 (open_bind_wrt_pattern_rec n1 (pattern_var_f X2) b1)).
Proof.
pose proof subst_pattern_in_bind_close_bind_wrt_pattern_rec_open_bind_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_bind_close_bind_wrt_pattern_rec_open_bind_wrt_pattern_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_exp_close_exp_wrt_pattern_rec_open_exp_wrt_pattern_rec_mutual :
(forall e1 P1 X1 X2 n1,
  X2 `notin` ftvar_in_exp e1 ->
  X2 `notin` ftvar_in_pattern P1 ->
  X2 <> X1 ->
  degree_pattern_wrt_pattern n1 P1 ->
  subst_pattern_in_exp P1 X1 e1 = close_exp_wrt_pattern_rec n1 X2 (subst_pattern_in_exp P1 X1 (open_exp_wrt_pattern_rec n1 (pattern_var_f X2) e1))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_exp_close_exp_wrt_pattern_rec_open_exp_wrt_pattern_rec :
forall e1 P1 X1 X2 n1,
  X2 `notin` ftvar_in_exp e1 ->
  X2 `notin` ftvar_in_pattern P1 ->
  X2 <> X1 ->
  degree_pattern_wrt_pattern n1 P1 ->
  subst_pattern_in_exp P1 X1 e1 = close_exp_wrt_pattern_rec n1 X2 (subst_pattern_in_exp P1 X1 (open_exp_wrt_pattern_rec n1 (pattern_var_f X2) e1)).
Proof.
pose proof subst_pattern_in_exp_close_exp_wrt_pattern_rec_open_exp_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_close_exp_wrt_pattern_rec_open_exp_wrt_pattern_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e1 P1 X1 x1 n1,
  x1 `notin` fvar_in_exp e1 ->
  subst_pattern_in_exp P1 X1 e1 = close_exp_wrt_exp_rec n1 x1 (subst_pattern_in_exp P1 X1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e1 P1 X1 x1 n1,
  x1 `notin` fvar_in_exp e1 ->
  subst_pattern_in_exp P1 X1 e1 = close_exp_wrt_exp_rec n1 x1 (subst_pattern_in_exp P1 X1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1)).
Proof.
pose proof subst_pattern_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_pattern_rec_open_exp_wrt_pattern_rec_mutual :
(forall e2 e1 x1 X1 n1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_pattern n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_pattern_rec n1 X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_pattern_rec n1 (pattern_var_f X1) e2))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_pattern_rec_open_exp_wrt_pattern_rec :
forall e2 e1 x1 X1 n1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  degree_exp_wrt_pattern n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_pattern_rec n1 X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_pattern_rec n1 (pattern_var_f X1) e2)).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_pattern_rec_open_exp_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_pattern_rec_open_exp_wrt_pattern_rec : lngen.

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

(* begin hide *)

Lemma subst_pattern_in_pat_row_close_pat_row_wrt_pattern_rec_open_pat_row_wrt_pattern_rec_mutual :
(forall p1 P1 X1 X2 n1,
  X2 `notin` ftvar_in_pat_row p1 ->
  X2 `notin` ftvar_in_pattern P1 ->
  X2 <> X1 ->
  degree_pattern_wrt_pattern n1 P1 ->
  subst_pattern_in_pat_row P1 X1 p1 = close_pat_row_wrt_pattern_rec n1 X2 (subst_pattern_in_pat_row P1 X1 (open_pat_row_wrt_pattern_rec n1 (pattern_var_f X2) p1))).
Proof.
apply_mutual_ind pat_row_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_pattern_in_pat_row_close_pat_row_wrt_pattern_rec_open_pat_row_wrt_pattern_rec :
forall p1 P1 X1 X2 n1,
  X2 `notin` ftvar_in_pat_row p1 ->
  X2 `notin` ftvar_in_pattern P1 ->
  X2 <> X1 ->
  degree_pattern_wrt_pattern n1 P1 ->
  subst_pattern_in_pat_row P1 X1 p1 = close_pat_row_wrt_pattern_rec n1 X2 (subst_pattern_in_pat_row P1 X1 (open_pat_row_wrt_pattern_rec n1 (pattern_var_f X2) p1)).
Proof.
pose proof subst_pattern_in_pat_row_close_pat_row_wrt_pattern_rec_open_pat_row_wrt_pattern_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_pat_row_close_pat_row_wrt_pattern_rec_open_pat_row_wrt_pattern_rec : lngen.

(* end hide *)

Lemma subst_pattern_in_pattern_close_pattern_wrt_pattern_open_pattern_wrt_pattern :
forall P2 P1 X1 X2,
  X2 `notin` ftvar_in_pattern P2 ->
  X2 `notin` ftvar_in_pattern P1 ->
  X2 <> X1 ->
  lc_pattern P1 ->
  subst_pattern_in_pattern P1 X1 P2 = close_pattern_wrt_pattern X2 (subst_pattern_in_pattern P1 X1 (open_pattern_wrt_pattern P2 (pattern_var_f X2))).
Proof.
unfold close_pattern_wrt_pattern; unfold open_pattern_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_pattern_close_pattern_wrt_pattern_open_pattern_wrt_pattern : lngen.

Lemma subst_pattern_in_bind_close_bind_wrt_pattern_open_bind_wrt_pattern :
forall b1 P1 X1 X2,
  X2 `notin` ftvar_in_bind b1 ->
  X2 `notin` ftvar_in_pattern P1 ->
  X2 <> X1 ->
  lc_pattern P1 ->
  subst_pattern_in_bind P1 X1 b1 = close_bind_wrt_pattern X2 (subst_pattern_in_bind P1 X1 (open_bind_wrt_pattern b1 (pattern_var_f X2))).
Proof.
unfold close_bind_wrt_pattern; unfold open_bind_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_bind_close_bind_wrt_pattern_open_bind_wrt_pattern : lngen.

Lemma subst_pattern_in_exp_close_exp_wrt_pattern_open_exp_wrt_pattern :
forall e1 P1 X1 X2,
  X2 `notin` ftvar_in_exp e1 ->
  X2 `notin` ftvar_in_pattern P1 ->
  X2 <> X1 ->
  lc_pattern P1 ->
  subst_pattern_in_exp P1 X1 e1 = close_exp_wrt_pattern X2 (subst_pattern_in_exp P1 X1 (open_exp_wrt_pattern e1 (pattern_var_f X2))).
Proof.
unfold close_exp_wrt_pattern; unfold open_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_close_exp_wrt_pattern_open_exp_wrt_pattern : lngen.

Lemma subst_pattern_in_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 P1 X1 x1,
  x1 `notin` fvar_in_exp e1 ->
  lc_pattern P1 ->
  subst_pattern_in_exp P1 X1 e1 = close_exp_wrt_exp x1 (subst_pattern_in_exp P1 X1 (open_exp_wrt_exp e1 (exp_var_f x1))).
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_pattern_open_exp_wrt_pattern :
forall e2 e1 x1 X1,
  X1 `notin` ftvar_in_exp e2 ->
  X1 `notin` ftvar_in_exp e1 ->
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_pattern X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_pattern e2 (pattern_var_f X1))).
Proof.
unfold close_exp_wrt_pattern; unfold open_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_pattern_open_exp_wrt_pattern : lngen.

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

Lemma subst_pattern_in_pat_row_close_pat_row_wrt_pattern_open_pat_row_wrt_pattern :
forall p1 P1 X1 X2,
  X2 `notin` ftvar_in_pat_row p1 ->
  X2 `notin` ftvar_in_pattern P1 ->
  X2 <> X1 ->
  lc_pattern P1 ->
  subst_pattern_in_pat_row P1 X1 p1 = close_pat_row_wrt_pattern X2 (subst_pattern_in_pat_row P1 X1 (open_pat_row_wrt_pattern p1 (pattern_var_f X2))).
Proof.
unfold close_pat_row_wrt_pattern; unfold open_pat_row_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_pat_row_close_pat_row_wrt_pattern_open_pat_row_wrt_pattern : lngen.

Lemma subst_pattern_in_pattern_pattern_all :
forall X2 P2 P1 X1,
  lc_pattern P1 ->
  X2 `notin` ftvar_in_pattern P1 `union` ftvar_in_pattern P2 `union` singleton X1 ->
  subst_pattern_in_pattern P1 X1 (pattern_all P2) = pattern_all (close_pattern_wrt_pattern X2 (subst_pattern_in_pattern P1 X1 (open_pattern_wrt_pattern P2 (pattern_var_f X2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_pattern_pattern_all : lngen.

Lemma subst_pattern_in_exp_exp_abs :
forall x1 e1 P1 X1,
  lc_pattern P1 ->
  x1 `notin` fvar_in_exp e1 ->
  subst_pattern_in_exp P1 X1 (exp_abs e1) = exp_abs (close_exp_wrt_exp x1 (subst_pattern_in_exp P1 X1 (open_exp_wrt_exp e1 (exp_var_f x1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_exp_abs : lngen.

Lemma subst_pattern_in_exp_exp_abs_anno :
forall x1 A1 e1 P1 X1,
  lc_pattern P1 ->
  x1 `notin` fvar_in_exp e1 ->
  subst_pattern_in_exp P1 X1 (exp_abs_anno A1 e1) = exp_abs_anno (subst_pattern_in_pattern P1 X1 A1) (close_exp_wrt_exp x1 (subst_pattern_in_exp P1 X1 (open_exp_wrt_exp e1 (exp_var_f x1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_exp_abs_anno : lngen.

Lemma subst_pattern_in_exp_exp_let :
forall x1 e1 e2 P1 X1,
  lc_pattern P1 ->
  x1 `notin` fvar_in_exp e2 ->
  subst_pattern_in_exp P1 X1 (exp_let e1 e2) = exp_let (subst_pattern_in_exp P1 X1 e1) (close_exp_wrt_exp x1 (subst_pattern_in_exp P1 X1 (open_exp_wrt_exp e2 (exp_var_f x1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_exp_let : lngen.

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

Lemma subst_exp_in_exp_exp_let :
forall x2 e2 e3 e1 x1,
  lc_exp e1 ->
  x2 `notin` fvar_in_exp e1 `union` fvar_in_exp e3 `union` singleton x1 ->
  subst_exp_in_exp e1 x1 (exp_let e2 e3) = exp_let (subst_exp_in_exp e1 x1 e2) (close_exp_wrt_exp x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp e3 (exp_var_f x2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_exp_let : lngen.

(* begin hide *)

Lemma subst_pattern_in_pattern_intro_rec_mutual :
(forall P1 X1 P2 n1,
  X1 `notin` ftvar_in_pattern P1 ->
  open_pattern_wrt_pattern_rec n1 P2 P1 = subst_pattern_in_pattern P2 X1 (open_pattern_wrt_pattern_rec n1 (pattern_var_f X1) P1)).
Proof.
apply_mutual_ind pattern_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_pattern_intro_rec :
forall P1 X1 P2 n1,
  X1 `notin` ftvar_in_pattern P1 ->
  open_pattern_wrt_pattern_rec n1 P2 P1 = subst_pattern_in_pattern P2 X1 (open_pattern_wrt_pattern_rec n1 (pattern_var_f X1) P1).
Proof.
pose proof subst_pattern_in_pattern_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_pattern_intro_rec : lngen.
#[export] Hint Rewrite subst_pattern_in_pattern_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_pattern_in_bind_intro_rec_mutual :
(forall b1 X1 P1 n1,
  X1 `notin` ftvar_in_bind b1 ->
  open_bind_wrt_pattern_rec n1 P1 b1 = subst_pattern_in_bind P1 X1 (open_bind_wrt_pattern_rec n1 (pattern_var_f X1) b1)).
Proof.
apply_mutual_ind bind_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_bind_intro_rec :
forall b1 X1 P1 n1,
  X1 `notin` ftvar_in_bind b1 ->
  open_bind_wrt_pattern_rec n1 P1 b1 = subst_pattern_in_bind P1 X1 (open_bind_wrt_pattern_rec n1 (pattern_var_f X1) b1).
Proof.
pose proof subst_pattern_in_bind_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_bind_intro_rec : lngen.
#[export] Hint Rewrite subst_pattern_in_bind_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_pattern_in_exp_intro_rec_mutual :
(forall e1 X1 P1 n1,
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_pattern_rec n1 P1 e1 = subst_pattern_in_exp P1 X1 (open_exp_wrt_pattern_rec n1 (pattern_var_f X1) e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_exp_intro_rec :
forall e1 X1 P1 n1,
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_pattern_rec n1 P1 e1 = subst_pattern_in_exp P1 X1 (open_exp_wrt_pattern_rec n1 (pattern_var_f X1) e1).
Proof.
pose proof subst_pattern_in_exp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_intro_rec : lngen.
#[export] Hint Rewrite subst_pattern_in_exp_intro_rec using solve [auto] : lngen.

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

(* begin hide *)

Lemma subst_pattern_in_pat_row_intro_rec_mutual :
(forall p1 X1 P1 n1,
  X1 `notin` ftvar_in_pat_row p1 ->
  open_pat_row_wrt_pattern_rec n1 P1 p1 = subst_pattern_in_pat_row P1 X1 (open_pat_row_wrt_pattern_rec n1 (pattern_var_f X1) p1)).
Proof.
apply_mutual_ind pat_row_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_pattern_in_pat_row_intro_rec :
forall p1 X1 P1 n1,
  X1 `notin` ftvar_in_pat_row p1 ->
  open_pat_row_wrt_pattern_rec n1 P1 p1 = subst_pattern_in_pat_row P1 X1 (open_pat_row_wrt_pattern_rec n1 (pattern_var_f X1) p1).
Proof.
pose proof subst_pattern_in_pat_row_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_pattern_in_pat_row_intro_rec : lngen.
#[export] Hint Rewrite subst_pattern_in_pat_row_intro_rec using solve [auto] : lngen.

Lemma subst_pattern_in_pattern_intro :
forall X1 P1 P2,
  X1 `notin` ftvar_in_pattern P1 ->
  open_pattern_wrt_pattern P1 P2 = subst_pattern_in_pattern P2 X1 (open_pattern_wrt_pattern P1 (pattern_var_f X1)).
Proof.
unfold open_pattern_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_pattern_intro : lngen.

Lemma subst_pattern_in_bind_intro :
forall X1 b1 P1,
  X1 `notin` ftvar_in_bind b1 ->
  open_bind_wrt_pattern b1 P1 = subst_pattern_in_bind P1 X1 (open_bind_wrt_pattern b1 (pattern_var_f X1)).
Proof.
unfold open_bind_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_bind_intro : lngen.

Lemma subst_pattern_in_exp_intro :
forall X1 e1 P1,
  X1 `notin` ftvar_in_exp e1 ->
  open_exp_wrt_pattern e1 P1 = subst_pattern_in_exp P1 X1 (open_exp_wrt_pattern e1 (pattern_var_f X1)).
Proof.
unfold open_exp_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_exp_intro : lngen.

Lemma subst_exp_in_exp_intro :
forall x1 e1 e2,
  x1 `notin` fvar_in_exp e1 ->
  open_exp_wrt_exp e1 e2 = subst_exp_in_exp e2 x1 (open_exp_wrt_exp e1 (exp_var_f x1)).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_intro : lngen.

Lemma subst_pattern_in_pat_row_intro :
forall X1 p1 P1,
  X1 `notin` ftvar_in_pat_row p1 ->
  open_pat_row_wrt_pattern p1 P1 = subst_pattern_in_pat_row P1 X1 (open_pat_row_wrt_pattern p1 (pattern_var_f X1)).
Proof.
unfold open_pat_row_wrt_pattern; default_simp.
Qed.

#[export] Hint Resolve subst_pattern_in_pat_row_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
