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
    unambiguous subset embeddings and the two erasing coercions requested
    by the refactor: [btyp >-> ptyp] and [bskl >-> pskl]. Colour choices
    from [ptyp] remain explicit. *)

Require Import Metalib.Metatheory.

Require Import src.frost.def_extra.

(** ===== utyp -> btyp (implicit subset embedding) ===== *)

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
