(** Coercions and explicit paintings between Fresco's current type
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

Require Import src.fresco.def_shapes.

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

(** ===== utyp -> btyp (implicit erasure into bidirectional types) ===== *)

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
    directly; a [dbind_typ A] doubles as the (ghost-free) skeleton [ptyp_to_pskl
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
  | pskl_ghost => bskl_ghost
  | pskl_univ_ghost P0 => bskl_univ_ghost (pskl_to_bskl_syn P0)
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
  | pskl_ghost => bskl_ghost
  | pskl_univ_ghost P0 => bskl_univ_ghost (pskl_to_bskl_inh P0)
  end.

(** Colour-preserving skeleton of a [btyp]: same shape and the SAME
    synthesised/inherited colour at every quantifier (a [btyp] has no ghosts).
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

(* ===================================================================== *)
(*  Erasure  ⌊R⌋ˢ : uskl → pskl  (decorated-algosub.tex:27-38)            *)
(*  Homomorphic; non-trivial cases: ∀^β1 ↦ ∀, HoleG ↦ □, TopHoleG ↦ ∀◇     *)
(* ===================================================================== *)

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

(** Plain skeletons as (untagged) unresolved skeletons: the embedding used
    by the flexible-variable rules, which are inherited unchanged from the
    ordinary algorithmic consistency (their subjects are plain skeletons). *)
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
  (* dotted ghosts erase to their plain counterparts (HoleG ~ Hole,
     TopHoleG ~ TopHole) on the resolved/bidirectional side. *)
  | uskl_dot_ghost => bskl_ghost
  | uskl_dot_univ_ghost R0 => bskl_univ_ghost (uskl_to_bskl R0)
  end.

Coercion uskl_to_bskl : uskl >-> bskl.

(** ===== utyp <-> uskl (the SORT INCLUSION and its retraction) =====

    A [utyp] IS a [uskl] with no ghosts: the grammars agree constructor for
    constructor and [uskl] only adds the four ghost forms.  The declarative
    system keeps the two sorts in SEPARATE judgments ([d_consis] / [d_sub] over
    [utyp], [d_pat_consis] / [d_pat_sub] over [uskl]) while the paper's
    decl-in-algo layer fuses them into ONE relation indexed by the sort
    ([ad_pat_consis], [ad_pat_sub]'s [N]), so relating the two systems needs
    this inclusion.  ⚠️ NOT the same map as [utyp_to_btyp], which collapses the
    ε tag: tags are what [d_tags] counts, so they must survive.

    [uskl_to_utyp] is the retraction, defined on all of [uskl] by sending every
    ghost to [1] — an arbitrary choice, meaningful only on the ghost-free part
    ([uskl_ghost_free_utyp_to_uskl], algo_decl/prop_conservativity.v). *)

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

(** Monotype embeddings into the skeleton sorts — used by the
    definition-lookup rules (algo_decl/def_consis_refine.v).  ⚙ Moved here
    from that file 2026-10-10, so that fresco/prop_shapes.v's
    monotype-substitution lemmas can be stated over them. *)
Definition ptyp_to_bskl_syn (A : ptyp) : bskl :=
  pskl_to_bskl_syn (ptyp_to_pskl A).
Definition ptyp_to_uskl_syn (A : ptyp) : uskl :=
  bskl_to_uskl (ptyp_to_bskl_syn A).
