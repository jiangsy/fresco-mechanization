(** Coercions and explicit paintings between Frost's current type
    hierarchy categories.

    Current syntax is generated as:
    - [ptyp] : plain source types;
    - [btyp] : bidirectional/coloured types;
    - [utyp] : unresolved synthesised types;
    - [pskl] : plain skeletons;
    - [bskl] : bidirectional skeletons;
    - [uskl] : unresolved skeletons.

    The only implicit embeddings used by rule statements are the
    established [utyp >-> btyp] map and the two erasing coercions
    requested by the refactor: [btyp >-> ptyp] and [bskl >-> pskl].
    Colour choices from [ptyp] remain explicit. *)

Require Import Metalib.Metatheory.

Require Import src.frost.def_extra.

(** ===== btyp -> utyp (synthesised erasure) ===== *)

Fixpoint btyp_to_utyp_syn (B : btyp) : utyp :=
  match B with
  | btyp_unit => utyp_unit
  | btyp_var_b n => utyp_var_b n
  | btyp_var_f α => utyp_var_f α
  | btyp_arrow B1 B2 => utyp_arrow (btyp_to_utyp_syn B1) (btyp_to_utyp_syn B2)
  | btyp_all_syn B0 => utyp_all_syn (btyp_to_utyp_syn B0)
  | btyp_all_inh B0 => utyp_all_syn (btyp_to_utyp_syn B0)
  end.

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
  | utyp_var_f α => btyp_var_f α
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
  | btyp_var_f α => ptyp_var_f α
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
  | ptyp_var_f α => btyp_var_f α
  | ptyp_arrow A1 A2 => btyp_arrow (ptyp_to_btyp_syn A1) (ptyp_to_btyp_syn A2)
  | ptyp_all A0 => btyp_all_syn (ptyp_to_btyp_syn A0)
  end.

Fixpoint ptyp_to_btyp_inh (A : ptyp) : btyp :=
  match A with
  | ptyp_unit => btyp_unit
  | ptyp_var_b n => btyp_var_b n
  | ptyp_var_f α => btyp_var_f α
  | ptyp_arrow A1 A2 => btyp_arrow (ptyp_to_btyp_inh A1) (ptyp_to_btyp_inh A2)
  | ptyp_all A0 => btyp_all_inh (ptyp_to_btyp_inh A0)
  end.

Fixpoint ptyp_to_utyp_syn (A : ptyp) : utyp :=
  match A with
  | ptyp_unit => utyp_unit
  | ptyp_var_b n => utyp_var_b n
  | ptyp_var_f α => utyp_var_f α
  | ptyp_arrow A1 A2 => utyp_arrow (ptyp_to_utyp_syn A1) (ptyp_to_utyp_syn A2)
  | ptyp_all A0 => utyp_all_syn (ptyp_to_utyp_syn A0)
  end.


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

Lemma ptyp_to_btyp_inh_open_rec : forall A1 A2 k,
    ptyp_to_btyp_inh (open_ptyp_wrt_ptyp_rec k A2 A1) =
    open_btyp_wrt_btyp_rec k (ptyp_to_btyp_inh A2) (ptyp_to_btyp_inh A1).
Proof.
  induction A1; intros A2 k; simpl; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
  - rewrite IHA1_1. rewrite IHA1_2. reflexivity.
  - rewrite IHA1. reflexivity.
Qed.

Lemma ptyp_to_btyp_inh_open : forall A1 A2,
    ptyp_to_btyp_inh (open_ptyp_wrt_ptyp A1 A2) =
    open_btyp_wrt_btyp (ptyp_to_btyp_inh A1) (ptyp_to_btyp_inh A2).
Proof.
  intros A1 A2.
  unfold open_ptyp_wrt_ptyp, open_btyp_wrt_btyp.
  apply ptyp_to_btyp_inh_open_rec.
Qed.


Lemma btyp_to_ptyp_open_rec : forall B1 B2 k,
    btyp_to_ptyp (open_btyp_wrt_btyp_rec k B2 B1) =
    open_ptyp_wrt_ptyp_rec k (btyp_to_ptyp B2) (btyp_to_ptyp B1).
Proof.
  induction B1; intros B2 k; simpl; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[|]|]; reflexivity.
  - rewrite IHB1_1, IHB1_2; reflexivity.
  - rewrite IHB1; reflexivity.
  - rewrite IHB1; reflexivity.
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
  | ptyp_var_f α => pskl_var_f α
  | ptyp_arrow A1 A2 => pskl_arrow (ptyp_to_pskl A1) (ptyp_to_pskl A2)
  | ptyp_all A0 => pskl_all_syn (ptyp_to_pskl A0)
  end.

(** A term-variable binding's skeleton view: a [dbind_skl] carries its skeleton
    directly; a [dbind_typ A] doubles as the (hole-free) skeleton [ptyp_to_pskl
    A] — "a type is a skeleton".  Used by [d_pat__var] so skeleton inference can
    read either binding kind, letting one [Γ] serve both [d_typing] (reads the
    type) and [d_pat] (reads the type-as-skeleton). *)
Definition dbind_to_pskl (d : dbind) : option pskl :=
  match d with
  | dbind_skl P => Some P
  | dbind_typ A => Some (ptyp_to_pskl A)
  | dbind_tvar => None
  end.

(** ===== pskl / bskl / uskl conversions ===== *)

Fixpoint pskl_to_bskl_syn (P : pskl) : bskl :=
  match P with
  | pskl_unit => bskl_unit
  | pskl_var_b n => bskl_var_b n
  | pskl_var_f α => bskl_var_f α
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
  | pskl_var_f α => bskl_var_f α
  | pskl_arrow P1 P2 => bskl_arrow (pskl_to_bskl_inh P1) (pskl_to_bskl_inh P2)
  | pskl_all_syn P0 => bskl_all_inh (pskl_to_bskl_inh P0)
  | pskl_hole => bskl_hole
  | pskl_tophole P0 => bskl_tophole (pskl_to_bskl_inh P0)
  end.

(** Colour-preserving skeleton of a [btyp]: same shape and the SAME
    synthesised/inherited colour at every quantifier (a [btyp] has no holes).
    Used by [App] so the refinement output [inh{P} ⊳ btyp_to_bskl B1] is exactly
    the skeleton of the function domain [B1] — tying the two together. *)
Fixpoint btyp_to_bskl (B : btyp) : bskl :=
  match B with
  | btyp_unit => bskl_unit
  | btyp_var_b n => bskl_var_b n
  | btyp_var_f α => bskl_var_f α
  | btyp_arrow B1 B2 => bskl_arrow (btyp_to_bskl B1) (btyp_to_bskl B2)
  | btyp_all_syn B0 => bskl_all_syn (btyp_to_bskl B0)
  | btyp_all_inh B0 => bskl_all_inh (btyp_to_bskl B0)
  end.

Fixpoint bskl_to_pskl (Q : bskl) : pskl :=
  match Q with
  | bskl_unit => pskl_unit
  | bskl_var_b n => pskl_var_b n
  | bskl_var_f α => pskl_var_f α
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
  | bskl_var_f α => uskl_var_f α
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
  | uskl_var_f α => bskl_var_f α
  | uskl_arrow R1 R2 => bskl_arrow (uskl_to_bskl R1) (uskl_to_bskl R2)
  | uskl_all_syn R0 => bskl_all_syn (uskl_to_bskl R0)
  | uskl_all_etag _ R0 => bskl_all_syn (uskl_to_bskl R0)
  | uskl_hole => bskl_hole
  | uskl_tophole R0 => bskl_tophole (uskl_to_bskl R0)
  (* dotted ghosts erase to their plain counterparts (HoleG ~ Hole,
     TopHoleG ~ TopHole) on the resolved/bidirectional side. *)
  | uskl_holeg => bskl_hole
  | uskl_topholeg R0 => bskl_tophole (uskl_to_bskl R0)
  end.

Coercion uskl_to_bskl : uskl >-> bskl.

(* RESTART NOTE (deleted 2026-08-09, cleanup audit §5.2) — [pskl_to_tskl],
   the DOTTED witness conversion, plus its [_open_rec] / [_open] lemmas.  It
   sent a pskl's ghost holes to DOTTED ghosts ([holeg] / [topholeg], which are
   [is_tskl]) and was written for the ∀-instantiation in the pattern producer.
   It had ZERO uses outside this file; whatever consumed it is gone.

   ⚠️ It is NOT the same map as [pskl_to_uskl] (decorated_algo/def_decorated.v),
   which is live: that one sends [pskl_hole] to the PLAIN [uskl_hole] and
   [pskl_tophole] to [uskl_tophole].  If a dotted witness is ever needed again,
   re-derive it here — the two lemmas were three-line inductions. *)
