(** Coercions and explicit paintings between Frost's current type
    hierarchy categories.

    Current syntax is generated as:
    - [ptyp] : plain source types;
    - [btyp] : bidirectional/coloured types;
    - [utyp] : unresolved synthesised types;
    - [gutyp] : generalised unresolved types;
    - [pskl] : plain skeletons;
    - [bskl] : bidirectional skeletons;
    - [uskl] : unresolved skeletons.

    The only implicit embeddings used by rule statements are the
    established [utyp >-> btyp] map and the two erasing coercions
    requested by the refactor: [btyp >-> ptyp] and [bskl >-> pskl].
    Colour choices from [ptyp] remain explicit.

    The [*_to_gutyp] maps are explicit injections into the paper's
    generalized-unresolved syntax.  They are intentionally not declared
    as Coercions: [utyp -> btyp] and [btyp -> ptyp] are existing erasure
    paths, and adding [utyp -> gutyp] / [btyp -> gutyp] as ambient
    coercions makes Coq's coercion graph ambiguous and obscures where the
    generalized syntax is being used. *)

Require Import Metalib.Metatheory.

Require Import src.frost.def_extra.

(** ===== explicit injections into generalized unresolved types ===== *)

Fixpoint utyp_to_gutyp (C : utyp) : gutyp :=
  match C with
  | utyp_unit => gutyp_unit
  | utyp_var_b n => gutyp_var_b n
  | utyp_var_f X => gutyp_var_f X
  | utyp_arrow C1 C2 => gutyp_arrow (utyp_to_gutyp C1) (utyp_to_gutyp C2)
  | utyp_all_syn C0 => gutyp_all_syn (utyp_to_gutyp C0)
  | utyp_all_etag ε C0 => gutyp_all_etag ε (utyp_to_gutyp C0)
  end.

Fixpoint btyp_to_gutyp (B : btyp) : gutyp :=
  match B with
  | btyp_unit => gutyp_unit
  | btyp_var_b n => gutyp_var_b n
  | btyp_var_f X => gutyp_var_f X
  | btyp_arrow B1 B2 => gutyp_arrow (btyp_to_gutyp B1) (btyp_to_gutyp B2)
  | btyp_all_syn B0 => gutyp_all_syn (btyp_to_gutyp B0)
  | btyp_all_inh B0 => gutyp_all_inh (btyp_to_gutyp B0)
  end.

Fixpoint btyp_to_utyp_syn (B : btyp) : utyp :=
  match B with
  | btyp_unit => utyp_unit
  | btyp_var_b n => utyp_var_b n
  | btyp_var_f X => utyp_var_f X
  | btyp_arrow B1 B2 => utyp_arrow (btyp_to_utyp_syn B1) (btyp_to_utyp_syn B2)
  | btyp_all_syn B0 => utyp_all_syn (btyp_to_utyp_syn B0)
  | btyp_all_inh B0 => utyp_all_syn (btyp_to_utyp_syn B0)
  end.

Lemma utyp_to_gutyp_open_rec : forall C1 C2 k,
    utyp_to_gutyp (open_utyp_wrt_utyp_rec k C2 C1) =
    open_gutyp_wrt_gutyp_rec k (utyp_to_gutyp C2) (utyp_to_gutyp C1).
Proof.
  induction C1; intros C2 k; simpl; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
  - rewrite IHC1_1. rewrite IHC1_2. reflexivity.
  - rewrite IHC1. reflexivity.
  - rewrite IHC1. reflexivity.
Qed.

Lemma utyp_to_gutyp_open : forall C1 C2,
    utyp_to_gutyp (open_utyp_wrt_utyp C1 C2) =
    open_gutyp_wrt_gutyp (utyp_to_gutyp C1) (utyp_to_gutyp C2).
Proof.
  intros C1 C2.
  unfold open_utyp_wrt_utyp, open_gutyp_wrt_gutyp.
  apply utyp_to_gutyp_open_rec.
Qed.

Fixpoint gutyp_to_btyp (G : gutyp) : btyp :=
  match G with
  | gutyp_unit => btyp_unit
  | gutyp_var_b n => btyp_var_b n
  | gutyp_var_f X => btyp_var_f X
  | gutyp_arrow G1 G2 => btyp_arrow (gutyp_to_btyp G1) (gutyp_to_btyp G2)
  | gutyp_all_syn G0 => btyp_all_syn (gutyp_to_btyp G0)
  | gutyp_all_inh G0 => btyp_all_inh (gutyp_to_btyp G0)
  | gutyp_all_etag _ G0 => btyp_all_syn (gutyp_to_btyp G0)
  end.

Lemma btyp_to_gutyp_open_rec : forall B1 B2 k,
    btyp_to_gutyp (open_btyp_wrt_btyp_rec k B2 B1) =
    open_gutyp_wrt_gutyp_rec k (btyp_to_gutyp B2) (btyp_to_gutyp B1).
Proof.
  induction B1; intros B2 k; simpl; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
  - rewrite IHB1_1. rewrite IHB1_2. reflexivity.
  - rewrite IHB1. reflexivity.
  - rewrite IHB1. reflexivity.
Qed.

Lemma btyp_to_gutyp_open : forall B1 B2,
    btyp_to_gutyp (open_btyp_wrt_btyp B1 B2) =
    open_gutyp_wrt_gutyp (btyp_to_gutyp B1) (btyp_to_gutyp B2).
Proof.
  intros B1 B2.
  unfold open_btyp_wrt_btyp, open_gutyp_wrt_gutyp.
  apply btyp_to_gutyp_open_rec.
Qed.

Lemma btyp_to_utyp_syn_open_rec : forall B1 B2 k,
    btyp_to_utyp_syn (open_btyp_wrt_btyp_rec k B2 B1) =
    open_utyp_wrt_utyp_rec k (btyp_to_utyp_syn B2) (btyp_to_utyp_syn B1).
Proof.
  induction B1; intros B2 k; simpl; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
  - rewrite IHB1_1. rewrite IHB1_2. reflexivity.
  - rewrite IHB1. reflexivity.
  - rewrite IHB1. reflexivity.
Qed.

Lemma btyp_to_utyp_syn_open : forall B1 B2,
    btyp_to_utyp_syn (open_btyp_wrt_btyp B1 B2) =
    open_utyp_wrt_utyp (btyp_to_utyp_syn B1) (btyp_to_utyp_syn B2).
Proof.
  intros B1 B2.
  unfold open_btyp_wrt_btyp, open_utyp_wrt_utyp.
  apply btyp_to_utyp_syn_open_rec.
Qed.

(** ===== utyp -> btyp (implicit erasure into bidirectional types) ===== *)

Fixpoint utyp_to_btyp (C : utyp) : btyp :=
  match C with
  | utyp_unit => btyp_unit
  | utyp_var_b n => btyp_var_b n
  | utyp_var_f X => btyp_var_f X
  | utyp_arrow C1 C2 => btyp_arrow (utyp_to_btyp C1) (utyp_to_btyp C2)
  | utyp_all_syn C0 => btyp_all_syn (utyp_to_btyp C0)
  | utyp_all_etag _ C0 => btyp_all_syn (utyp_to_btyp C0)
  end.

Coercion utyp_to_btyp : utyp >-> btyp.

(** ===== btyp -> ptyp (implicit erasure) ===== *)

Fixpoint btyp_to_ptyp (B : btyp) : ptyp :=
  match B with
  | btyp_unit => ptyp_unit
  | btyp_var_b n => ptyp_var_b n
  | btyp_var_f X => ptyp_var_f X
  | btyp_arrow B1 B2 => ptyp_arrow (btyp_to_ptyp B1) (btyp_to_ptyp B2)
  | btyp_all_syn B0 => ptyp_all (btyp_to_ptyp B0)
  | btyp_all_inh B0 => ptyp_all (btyp_to_ptyp B0)
  end.

Coercion btyp_to_ptyp : btyp >-> ptyp.

(** ===== ptyp -> btyp / utyp (explicit paintings) ===== *)

Fixpoint ptyp_to_btyp_syn (A : ptyp) : btyp :=
  match A with
  | ptyp_unit => btyp_unit
  | ptyp_var_b n => btyp_var_b n
  | ptyp_var_f X => btyp_var_f X
  | ptyp_arrow A1 A2 => btyp_arrow (ptyp_to_btyp_syn A1) (ptyp_to_btyp_syn A2)
  | ptyp_all A0 => btyp_all_syn (ptyp_to_btyp_syn A0)
  end.

Fixpoint ptyp_to_btyp_inh (A : ptyp) : btyp :=
  match A with
  | ptyp_unit => btyp_unit
  | ptyp_var_b n => btyp_var_b n
  | ptyp_var_f X => btyp_var_f X
  | ptyp_arrow A1 A2 => btyp_arrow (ptyp_to_btyp_inh A1) (ptyp_to_btyp_inh A2)
  | ptyp_all A0 => btyp_all_inh (ptyp_to_btyp_inh A0)
  end.

Fixpoint ptyp_to_utyp_syn (A : ptyp) : utyp :=
  match A with
  | ptyp_unit => utyp_unit
  | ptyp_var_b n => utyp_var_b n
  | ptyp_var_f X => utyp_var_f X
  | ptyp_arrow A1 A2 => utyp_arrow (ptyp_to_utyp_syn A1) (ptyp_to_utyp_syn A2)
  | ptyp_all A0 => utyp_all_syn (ptyp_to_utyp_syn A0)
  end.

Definition ptyp_to_gutyp_syn (A : ptyp) : gutyp :=
  utyp_to_gutyp (ptyp_to_utyp_syn A).

Lemma ptyp_to_gutyp_syn_btyp_to_gutyp : forall A,
    ptyp_to_gutyp_syn A = btyp_to_gutyp (ptyp_to_btyp_syn A).
Proof.
  induction A; unfold ptyp_to_gutyp_syn in *; simpl; try reflexivity.
  - rewrite IHA1. rewrite IHA2. reflexivity.
  - rewrite IHA. reflexivity.
Qed.

Lemma ptyp_to_utyp_syn_btyp_to_ptyp_syn : forall A,
    ptyp_to_utyp_syn (ptyp_to_btyp_syn A) = ptyp_to_utyp_syn A.
Proof.
  induction A; simpl; try reflexivity.
  - rewrite IHA1. rewrite IHA2. reflexivity.
  - rewrite IHA. reflexivity.
Qed.

Lemma ptyp_to_btyp_syn_open_rec : forall A1 A2 k,
    ptyp_to_btyp_syn (open_ptyp_wrt_ptyp_rec k A2 A1) =
    open_btyp_wrt_btyp_rec k (ptyp_to_btyp_syn A2) (ptyp_to_btyp_syn A1).
Proof.
  induction A1; intros A2 k; simpl; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
  - rewrite IHA1_1. rewrite IHA1_2. reflexivity.
  - rewrite IHA1. reflexivity.
Qed.

Lemma ptyp_to_btyp_syn_open : forall A1 A2,
    ptyp_to_btyp_syn (open_ptyp_wrt_ptyp A1 A2) =
    open_btyp_wrt_btyp (ptyp_to_btyp_syn A1) (ptyp_to_btyp_syn A2).
Proof.
  intros A1 A2.
  unfold open_ptyp_wrt_ptyp, open_btyp_wrt_btyp.
  apply ptyp_to_btyp_syn_open_rec.
Qed.

Lemma ptyp_to_utyp_syn_open_rec : forall A1 A2 k,
    ptyp_to_utyp_syn (open_ptyp_wrt_ptyp_rec k A2 A1) =
    open_utyp_wrt_utyp_rec k (ptyp_to_utyp_syn A2) (ptyp_to_utyp_syn A1).
Proof.
  induction A1; intros A2 k; simpl; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
  - rewrite IHA1_1. rewrite IHA1_2. reflexivity.
  - rewrite IHA1. reflexivity.
Qed.

Lemma ptyp_to_utyp_syn_open : forall A1 A2,
    ptyp_to_utyp_syn (open_ptyp_wrt_ptyp A1 A2) =
    open_utyp_wrt_utyp (ptyp_to_utyp_syn A1) (ptyp_to_utyp_syn A2).
Proof.
  intros A1 A2.
  unfold open_ptyp_wrt_ptyp, open_utyp_wrt_utyp.
  apply ptyp_to_utyp_syn_open_rec.
Qed.

(** ===== ptyp -> pskl ===== *)

Fixpoint ptyp_to_pskl (A : ptyp) : pskl :=
  match A with
  | ptyp_unit => pskl_unit
  | ptyp_var_b n => pskl_var_b n
  | ptyp_var_f X => pskl_var_f X
  | ptyp_arrow A1 A2 => pskl_arrow (ptyp_to_pskl A1) (ptyp_to_pskl A2)
  | ptyp_all A0 => pskl_all_syn (ptyp_to_pskl A0)
  end.

(** ===== pskl / bskl / uskl conversions ===== *)

Fixpoint pskl_to_bskl_syn (P : pskl) : bskl :=
  match P with
  | pskl_unit => bskl_unit
  | pskl_var_b n => bskl_var_b n
  | pskl_var_f X => bskl_var_f X
  | pskl_arrow P1 P2 => bskl_arrow (pskl_to_bskl_syn P1) (pskl_to_bskl_syn P2)
  | pskl_all_syn P0 => bskl_all_syn (pskl_to_bskl_syn P0)
  | pskl_hole => bskl_hole
  | pskl_tophole P0 => bskl_tophole (pskl_to_bskl_syn P0)
  end.

(** Inherited painting of a (synthesised-only) skeleton: same base
    skeleton as [pskl_to_bskl_syn], with every concrete quantifier
    painted inherited.  Used where the paper refines an inherited
    skeleton [inh{P}] (the same [bskl] as the synthesised view, just
    repainted). *)
Fixpoint pskl_to_bskl_inh (P : pskl) : bskl :=
  match P with
  | pskl_unit => bskl_unit
  | pskl_var_b n => bskl_var_b n
  | pskl_var_f X => bskl_var_f X
  | pskl_arrow P1 P2 => bskl_arrow (pskl_to_bskl_inh P1) (pskl_to_bskl_inh P2)
  | pskl_all_syn P0 => bskl_all_inh (pskl_to_bskl_inh P0)
  | pskl_hole => bskl_hole
  | pskl_tophole P0 => bskl_tophole (pskl_to_bskl_inh P0)
  end.

Fixpoint bskl_to_pskl (Q : bskl) : pskl :=
  match Q with
  | bskl_unit => pskl_unit
  | bskl_var_b n => pskl_var_b n
  | bskl_var_f X => pskl_var_f X
  | bskl_arrow Q1 Q2 => pskl_arrow (bskl_to_pskl Q1) (bskl_to_pskl Q2)
  | bskl_all_syn Q0 => pskl_all_syn (bskl_to_pskl Q0)
  | bskl_all_inh Q0 => pskl_all_syn (bskl_to_pskl Q0)
  | bskl_hole => pskl_hole
  | bskl_tophole Q0 => pskl_tophole (bskl_to_pskl Q0)
  end.

Coercion bskl_to_pskl : bskl >-> pskl.

Fixpoint bskl_to_uskl (Q : bskl) : uskl :=
  match Q with
  | bskl_unit => uskl_unit
  | bskl_var_b n => uskl_var_b n
  | bskl_var_f X => uskl_var_f X
  | bskl_arrow Q1 Q2 => uskl_arrow (bskl_to_uskl Q1) (bskl_to_uskl Q2)
  | bskl_all_syn Q0 => uskl_all_syn (bskl_to_uskl Q0)
  | bskl_all_inh Q0 => uskl_all_syn (bskl_to_uskl Q0)
  | bskl_hole => uskl_hole
  | bskl_tophole Q0 => uskl_tophole (bskl_to_uskl Q0)
  end.

Fixpoint uskl_to_bskl (R : uskl) : bskl :=
  match R with
  | uskl_unit => bskl_unit
  | uskl_var_b n => bskl_var_b n
  | uskl_var_f X => bskl_var_f X
  | uskl_arrow R1 R2 => bskl_arrow (uskl_to_bskl R1) (uskl_to_bskl R2)
  | uskl_all_syn R0 => bskl_all_syn (uskl_to_bskl R0)
  | uskl_all_etag _ R0 => bskl_all_syn (uskl_to_bskl R0)
  | uskl_hole => bskl_hole
  | uskl_tophole R0 => bskl_tophole (uskl_to_bskl R0)
  end.

Coercion uskl_to_bskl : uskl >-> bskl.
