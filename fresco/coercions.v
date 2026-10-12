Require Import Metalib.Metatheory.

Require Import src.fresco.def_shapes.

Fixpoint btyp_to_utyp_syn (B : btyp) : utyp :=
  match B with
  | btyp_unit => utyp_unit
  | btyp_var_b n => utyp_var_b n
  | btyp_var_f α => utyp_var_f α
  | btyp_arrow B1 B2 => utyp_arrow (btyp_to_utyp_syn B1) (btyp_to_utyp_syn B2)
  | btyp_all_syn B0 => utyp_all_syn (btyp_to_utyp_syn B0)
  | btyp_all_inh B0 => utyp_all_syn (btyp_to_utyp_syn B0)
  end.

Fixpoint utyp_to_btyp (C : utyp) : btyp :=
  match C with
  | utyp_unit => btyp_unit
  | utyp_var_b n => btyp_var_b n
  | utyp_var_f α => btyp_var_f α
  | utyp_arrow C1 C2 => btyp_arrow (utyp_to_btyp C1) (utyp_to_btyp C2)
  | utyp_all_syn C0 => btyp_all_syn (utyp_to_btyp C0)
  | utyp_all_tag _ C0 => btyp_all_syn (utyp_to_btyp C0)
  end.

Coercion utyp_to_btyp : utyp >-> btyp.

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

Fixpoint ptyp_to_pskl (A : ptyp) : pskl :=
  match A with
  | ptyp_unit => pskl_unit
  | ptyp_var_b n => pskl_var_b n
  | ptyp_var_f α => pskl_var_f α
  | ptyp_arrow A1 A2 => pskl_arrow (ptyp_to_pskl A1) (ptyp_to_pskl A2)
  | ptyp_all A0 => pskl_all_syn (ptyp_to_pskl A0)
  end.

Definition dbind_to_pskl (d : dbind) : option pskl :=
  match d with
  | dbind_skl P => Some P
  | dbind_typ A => Some (ptyp_to_pskl A)
  | dbind_tvar => None
  end.

Fixpoint pskl_to_bskl_syn (P : pskl) : bskl :=
  match P with
  | pskl_unit => bskl_unit
  | pskl_var_b n => bskl_var_b n
  | pskl_var_f α => bskl_var_f α
  | pskl_arrow P1 P2 => bskl_arrow (pskl_to_bskl_syn P1) (pskl_to_bskl_syn P2)
  | pskl_all_syn P0 => bskl_all_syn (pskl_to_bskl_syn P0)
  | pskl_ghost => bskl_ghost
  | pskl_univ_ghost P0 => bskl_univ_ghost (pskl_to_bskl_syn P0)
  end.

Fixpoint pskl_to_bskl_inh (P : pskl) : bskl :=
  match P with
  | pskl_unit => bskl_unit
  | pskl_var_b n => bskl_var_b n
  | pskl_var_f α => bskl_var_f α
  | pskl_arrow P1 P2 => bskl_arrow (pskl_to_bskl_inh P1) (pskl_to_bskl_inh P2)
  | pskl_all_syn P0 => bskl_all_inh (pskl_to_bskl_inh P0)
  | pskl_ghost => bskl_ghost
  | pskl_univ_ghost P0 => bskl_univ_ghost (pskl_to_bskl_inh P0)
  end.

Fixpoint btyp_to_bskl (B : btyp) : bskl :=
  match B with
  | btyp_unit => bskl_unit
  | btyp_var_b n => bskl_var_b n
  | btyp_var_f α => bskl_var_f α
  | btyp_arrow B1 B2 => bskl_arrow (btyp_to_bskl B1) (btyp_to_bskl B2)
  | btyp_all_syn B0 => bskl_all_syn (btyp_to_bskl B0)
  | btyp_all_inh B0 => bskl_all_inh (btyp_to_bskl B0)
  end.

Fixpoint uskl_to_pskl (R : uskl) : pskl :=
  match R with
  | uskl_unit => pskl_unit
  | uskl_var_b n => pskl_var_b n
  | uskl_var_f α => pskl_var_f α
  | uskl_arrow R1 R2 => pskl_arrow (uskl_to_pskl R1) (uskl_to_pskl R2)
  | uskl_all_syn R0 => pskl_all_syn (uskl_to_pskl R0)
  | uskl_all_tag _ R0 => pskl_all_syn (uskl_to_pskl R0)
  | uskl_ghost => pskl_ghost
  | uskl_univ_ghost R0 => pskl_univ_ghost (uskl_to_pskl R0)
  | uskl_dot_ghost => pskl_ghost
  | uskl_dot_univ_ghost R0 => pskl_univ_ghost (uskl_to_pskl R0)
  end.

Notation "⌊ R ⌋ˢ" := (uskl_to_pskl R) (at level 0, R at level 99).

Fixpoint pskl_to_uskl (P : pskl) : uskl :=
  match P with
  | pskl_unit => uskl_unit
  | pskl_var_b n => uskl_var_b n
  | pskl_var_f α => uskl_var_f α
  | pskl_arrow P1 P2 => uskl_arrow (pskl_to_uskl P1) (pskl_to_uskl P2)
  | pskl_all_syn P0 => uskl_all_syn (pskl_to_uskl P0)
  | pskl_ghost => uskl_ghost
  | pskl_univ_ghost P0 => uskl_univ_ghost (pskl_to_uskl P0)
  end.

Fixpoint bskl_to_pskl (Q : bskl) : pskl :=
  match Q with
  | bskl_unit => pskl_unit
  | bskl_var_b n => pskl_var_b n
  | bskl_var_f α => pskl_var_f α
  | bskl_arrow Q1 Q2 => pskl_arrow (bskl_to_pskl Q1) (bskl_to_pskl Q2)
  | bskl_all_syn Q0 => pskl_all_syn (bskl_to_pskl Q0)
  | bskl_all_inh Q0 => pskl_all_syn (bskl_to_pskl Q0)
  | bskl_ghost => pskl_ghost
  | bskl_univ_ghost Q0 => pskl_univ_ghost (bskl_to_pskl Q0)
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
  | bskl_ghost => uskl_ghost
  | bskl_univ_ghost Q0 => uskl_univ_ghost (bskl_to_uskl Q0)
  end.

Fixpoint uskl_to_bskl (R : uskl) : bskl :=
  match R with
  | uskl_unit => bskl_unit
  | uskl_var_b n => bskl_var_b n
  | uskl_var_f α => bskl_var_f α
  | uskl_arrow R1 R2 => bskl_arrow (uskl_to_bskl R1) (uskl_to_bskl R2)
  | uskl_all_syn R0 => bskl_all_syn (uskl_to_bskl R0)
  | uskl_all_tag _ R0 => bskl_all_syn (uskl_to_bskl R0)
  | uskl_ghost => bskl_ghost
  | uskl_univ_ghost R0 => bskl_univ_ghost (uskl_to_bskl R0)
  | uskl_dot_ghost => bskl_ghost
  | uskl_dot_univ_ghost R0 => bskl_univ_ghost (uskl_to_bskl R0)
  end.

Coercion uskl_to_bskl : uskl >-> bskl.

Fixpoint utyp_to_uskl (C : utyp) : uskl :=
  match C with
  | utyp_unit => uskl_unit
  | utyp_var_b n => uskl_var_b n
  | utyp_var_f α => uskl_var_f α
  | utyp_arrow C1 C2 => uskl_arrow (utyp_to_uskl C1) (utyp_to_uskl C2)
  | utyp_all_syn C0 => uskl_all_syn (utyp_to_uskl C0)
  | utyp_all_tag ε C0 => uskl_all_tag ε (utyp_to_uskl C0)
  end.

Fixpoint uskl_to_utyp (R : uskl) : utyp :=
  match R with
  | uskl_unit => utyp_unit
  | uskl_var_b n => utyp_var_b n
  | uskl_var_f α => utyp_var_f α
  | uskl_arrow R1 R2 => utyp_arrow (uskl_to_utyp R1) (uskl_to_utyp R2)
  | uskl_all_syn R0 => utyp_all_syn (uskl_to_utyp R0)
  | uskl_all_tag ε R0 => utyp_all_tag ε (uskl_to_utyp R0)
  | uskl_ghost => utyp_unit
  | uskl_univ_ghost _ => utyp_unit
  | uskl_dot_ghost => utyp_unit
  | uskl_dot_univ_ghost _ => utyp_unit
  end.

Definition ptyp_to_bskl_syn (A : ptyp) : bskl :=
  pskl_to_bskl_syn (ptyp_to_pskl A).
Definition ptyp_to_uskl_syn (A : ptyp) : uskl :=
  bskl_to_uskl (ptyp_to_bskl_syn A).
