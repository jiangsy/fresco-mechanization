(** ε-TAG EQUIVARIANCE, the syntactic layer.

    The paper's ForallL side condition is the single word *fresh* on the
    instantiation's tags Ψ', and it means GLOBAL freshness — in particular
    freshness from the tags already in the SUBJECT, which is what
    [lemma:precision-substitution] needs (docs/DESIGN-completeness-subtyping.md
    §5.2).  Every subtyping judgment in the tree renders it that way, and
    making that affordable rests on being able to MOVE a
    derivation's instantiation tags: this file is the syntactic half of that
    primitive, decl/prop_tag_swap.v the judgmental half.

    §0 is the other half of "affordable", and the cheaper one: the hygiene
    premise has to survive every structural lemma, and all but one of them
    substitute a TYPE variable — which cannot touch a tag.

    ⭐ THE PRIMITIVE IS A TRANSPOSITION.  A one-way rename [ε1 ↦ ε2] is sound
    only when ε2 is fresh for the WHOLE derivation, and "the tags of a
    derivation" is not something a [Prop] lets us collect; a swap is a
    bijection, so it is an automorphism unconditionally — the same reason
    algo/prop_swap.v takes equivariance as the renaming primitive for TYPE
    variables.

    ⭐ §1 IS SORT-AGNOSTIC AND SHARED.  A transposition of two ATOMS knows
    nothing about ε tags, so [swap_atom] / [swap_atoms] and their spec live
    here ONCE and algo/prop_swap.v — the TYPE-variable equivariance kit —
    imports them — do not redefine them there.

    ⚙ ε tags are plain atoms occupying a slot in [utyp_all_tag] /
    [uskl_all_tag], not a locally-nameless sort, so lngen generates nothing
    for them: the swap, its action on atom SETS (tag contexts are [atoms]) and
    every transport lemma below are hand-written.

    ⚙ §2 has no [uskl] half: nothing consumes a skeleton-sort tag swap
    (the CST repair runs at the TYPE sort).  If one is needed, copy the
    [utyp] half and add the four ghost constructors. *)

Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.ltac_utils.
Require Import src.fresco.def_shapes.

(* ===================================================================== *)
(*  §0  ε TAGS ARE BLIND TO TYPE-VARIABLE SUBSTITUTION                    *)
(*                                                                        *)
(*  ⭐ The reason the GLOBAL reading of [fresh Ψ'] costs the tree almost   *)
(*  nothing: a rule premise [Ψ' ∩ ftag(subject) = ∅] has to survive every  *)
(*  structural lemma, and all but one of them substitute a TYPE variable — *)
(*  which cannot touch a tag, whatever it substitutes, as long as the      *)
(*  replacement carries no tags of its own.  Stated once, in its strongest *)
(*  form; the [_var] / [_unit] / [_mono] instances downstream read off it. *)
(* ===================================================================== *)

Lemma ftag_in_utyp_subst_tagfree : forall C C' α,
  ftag_in_utyp C' [=] empty ->
  ftag_in_utyp (subst_utyp_in_utyp C' α C) [=] ftag_in_utyp C.
Proof.
  induction C; intros C' α0 Hf; simpl;
    try solve [ reflexivity
              | destruct_if; [ exact Hf | reflexivity ]
              | rewrite IHC by exact Hf; reflexivity
              | rewrite IHC1, IHC2 by exact Hf; reflexivity ].
Qed.

Lemma ftag_in_uskl_subst_tagfree : forall R R' α,
  ftag_in_uskl R' [=] empty ->
  ftag_in_uskl (subst_uskl_in_uskl R' α R) [=] ftag_in_uskl R.
Proof.
  induction R; intros R' α0 Hf; simpl;
    try solve [ reflexivity
              | destruct_if; [ exact Hf | reflexivity ]
              | rewrite IHR by exact Hf; reflexivity
              | rewrite IHR1, IHR2 by exact Hf; reflexivity ].
Qed.

(** Opening by a VARIABLE adds no tag; opening by anything adds at most its
    tags.  (The [uskl] twins are in algo/consis/prop_consis_precise.v.) *)
Lemma ftag_in_utyp_open_rec_var : forall α' C k,
  ftag_in_utyp (open_utyp_wrt_utyp_rec k (utyp_var_f α') C) [=] ftag_in_utyp C.
Proof.
  intros α' C; induction C; intros k; simpl; try reflexivity.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; reflexivity.
  - rewrite IHC1, IHC2; reflexivity.
  - rewrite IHC; reflexivity.
  - rewrite IHC; reflexivity.
Qed.

Lemma ftag_in_utyp_open_var : forall C α,
  ftag_in_utyp (open_utyp_wrt_utyp C (utyp_var_f α)) [=] ftag_in_utyp C.
Proof. intros; unfold open_utyp_wrt_utyp; apply ftag_in_utyp_open_rec_var. Qed.

Lemma ftag_in_utyp_open_rec_upper : forall C C' k,
  ftag_in_utyp (open_utyp_wrt_utyp_rec k C' C) [<=]
  ftag_in_utyp C `union` ftag_in_utyp C'.
Proof.
  intros C C'; induction C; intros k; simpl; try fsetdec.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; fsetdec.
  - specialize (IHC1 k); specialize (IHC2 k); fsetdec.
  - specialize (IHC (S k)); fsetdec.
  - specialize (IHC (S k)); fsetdec.
Qed.

Lemma ftag_in_utyp_open_upper : forall C C',
  ftag_in_utyp (open_utyp_wrt_utyp C C') [<=]
  ftag_in_utyp C `union` ftag_in_utyp C'.
Proof. intros; unfold open_utyp_wrt_utyp; apply ftag_in_utyp_open_rec_upper. Qed.

(* ===================================================================== *)
(*  §1  THE TRANSPOSITION, on atoms and on atom SETS                      *)
(* ===================================================================== *)

Definition swap_atom (ε1 ε2 α : atom) : atom :=
  if α == ε1 then ε2 else if α == ε2 then ε1 else α.

(** ⚙ [simpl] must never unfold [swap_atom] into its if-form: [algo/prop_swap.v]
    destructs and rewrites on [swap_atom _ _ _] syntactically. *)
Global Arguments swap_atom : simpl never.

(** The action on a tag CONTEXT.  Written as a union rather than an image
    ([atoms] has no map), and used only through [swap_atoms_spec] below —
    every fact about it is a pointwise consequence of that one. *)
Definition swap_atoms (ε1 ε2 : atom) (S : atoms) : atoms :=
  union (union (if mem ε1 S then singleton ε2 else empty)
               (if mem ε2 S then singleton ε1 else empty))
        (remove ε1 (remove ε2 S)).

Lemma swap_atom_invol : forall ε1 ε2 α,
  swap_atom ε1 ε2 (swap_atom ε1 ε2 α) = α.
Proof.
  intros ε1 ε2 α. unfold swap_atom.
  destruct (α == ε1) as [ -> | Hne1 ].
  - destruct (ε2 == ε1) as [ -> | _ ]; [ reflexivity | ].
    destruct (ε2 == ε2) as [ _ | Hc ]; [ reflexivity | contradiction ].
  - destruct (α == ε2) as [ -> | Hne2 ].
    + destruct (ε1 == ε1) as [ _ | Hc ]; [ reflexivity | contradiction ].
    + destruct (α == ε1) as [ Hc | _ ]; [ contradiction | ].
      destruct (α == ε2) as [ Hc | _ ]; [ contradiction | reflexivity ].
Qed.

Lemma swap_atom_other : forall ε1 ε2 α,
  α <> ε1 -> α <> ε2 -> swap_atom ε1 ε2 α = α.
Proof.
  intros ε1 ε2 α H1 H2. unfold swap_atom.
  destruct (α == ε1) as [ Hc | _ ]; [ contradiction | ].
  destruct (α == ε2) as [ Hc | _ ]; [ contradiction | reflexivity ].
Qed.

(** ⭐ THE ONLY FACT ABOUT [swap_atoms] THAT IS PROVED BY UNFOLDING.  Every
    other one below reads membership through it and then closes by [fsetdec]
    on the atoms. *)
Lemma swap_atoms_spec : forall ε1 ε2 S α,
  α `in` swap_atoms ε1 ε2 S <-> (swap_atom ε1 ε2 α) `in` S.
Proof.
  intros ε1 ε2 S α. unfold swap_atoms, swap_atom.
  destruct (mem ε1 S) eqn:Hm1; destruct (mem ε2 S) eqn:Hm2;
    (try rewrite <- AtomSetFacts.mem_iff in Hm1);
    (try rewrite <- AtomSetFacts.not_mem_iff in Hm1);
    (try rewrite <- AtomSetFacts.mem_iff in Hm2);
    (try rewrite <- AtomSetFacts.not_mem_iff in Hm2);
    destruct (α == ε1) as [ -> | Hne1 ];
    try destruct (α == ε2) as [ -> | Hne2 ];
    split; intros H; try assumption;
    solve [ clear - H Hm1 Hm2 Hne1; fsetdec
          | clear - H Hm1 Hm2; fsetdec
          | clear - H Hm1 Hm2 Hne1 Hne2; fsetdec ].
Qed.

Lemma swap_atoms_cong : forall ε1 ε2 S T,
  S [=] T -> swap_atoms ε1 ε2 S [=] swap_atoms ε1 ε2 T.
Proof.
  intros ε1 ε2 S T Heq α.
  rewrite !swap_atoms_spec. split; intros H; apply Heq; exact H.
Qed.

Lemma swap_atoms_empty : forall ε1 ε2, swap_atoms ε1 ε2 empty [=] empty.
Proof.
  intros ε1 ε2 α. rewrite swap_atoms_spec.
  split; intros H; clear - H; fsetdec.
Qed.

Lemma swap_atoms_union : forall ε1 ε2 S T,
  swap_atoms ε1 ε2 (S `union` T)
  [=] (swap_atoms ε1 ε2 S) `union` (swap_atoms ε1 ε2 T).
Proof.
  intros ε1 ε2 S T α.
  rewrite AtomSetFacts.union_iff, !swap_atoms_spec, AtomSetFacts.union_iff.
  reflexivity.
Qed.

Lemma swap_atoms_inter : forall ε1 ε2 S T,
  swap_atoms ε1 ε2 (S ∩ T) [=] (swap_atoms ε1 ε2 S) ∩ (swap_atoms ε1 ε2 T).
Proof.
  intros ε1 ε2 S T α.
  rewrite AtomSetFacts.inter_iff, !swap_atoms_spec, AtomSetFacts.inter_iff.
  reflexivity.
Qed.

Lemma swap_atoms_add : forall ε1 ε2 ε S,
  swap_atoms ε1 ε2 (add ε S) [=] add (swap_atom ε1 ε2 ε) (swap_atoms ε1 ε2 S).
Proof.
  intros ε1 ε2 ε S α. split; intros H.
  - apply swap_atoms_spec, AtomSetFacts.add_iff in H.
    apply AtomSetFacts.add_iff. destruct H as [ Heq | Hin ];
      [ left; rewrite Heq; apply swap_atom_invol
      | right; apply swap_atoms_spec; exact Hin ].
  - apply AtomSetFacts.add_iff in H.
    apply swap_atoms_spec, AtomSetFacts.add_iff. destruct H as [ Heq | Hin ];
      [ left; rewrite <- Heq, swap_atom_invol; reflexivity
      | right; apply swap_atoms_spec in Hin; exact Hin ].
Qed.

(** Untouched sets stay untouched — how a swap keeps a CONCLUSION fixed while
    moving the tags inside a derivation. *)
Lemma swap_atoms_notin : forall ε1 ε2 S,
  ε1 `notin` S -> ε2 `notin` S -> swap_atoms ε1 ε2 S [=] S.
Proof.
  intros ε1 ε2 S H1 H2 α. rewrite swap_atoms_spec. unfold swap_atom.
  destruct (α == ε1) as [ -> | Hne1 ];
    [ split; intros H; [ contradiction | contradiction ] | ].
  destruct (α == ε2) as [ -> | Hne2 ];
    [ split; intros H; [ contradiction | contradiction ] | ].
  reflexivity.
Qed.

Lemma swap_atoms_notin_of : forall ε1 ε2 S α,
  α `notin` S -> (swap_atom ε1 ε2 α) `notin` swap_atoms ε1 ε2 S.
Proof.
  intros ε1 ε2 S α H Hin. rewrite swap_atoms_spec in Hin.
  rewrite swap_atom_invol in Hin. contradiction.
Qed.

Lemma swap_atoms_in : forall ε1 ε2 S α,
  α `in` S -> (swap_atom ε1 ε2 α) `in` swap_atoms ε1 ε2 S.
Proof.
  intros ε1 ε2 S α H. apply swap_atoms_spec. rewrite swap_atom_invol. exact H.
Qed.

(* ===================================================================== *)
(*  §2  THE ACTION ON TYPES                                               *)
(* ===================================================================== *)

Fixpoint swap_tag_in_utyp (ε1 ε2 : atom) (C : utyp) : utyp :=
  match C with
  | utyp_unit => utyp_unit
  | utyp_var_b n => utyp_var_b n
  | utyp_var_f α => utyp_var_f α
  | utyp_arrow C1 C2 =>
      utyp_arrow (swap_tag_in_utyp ε1 ε2 C1) (swap_tag_in_utyp ε1 ε2 C2)
  | utyp_all_syn C0 => utyp_all_syn (swap_tag_in_utyp ε1 ε2 C0)
  | utyp_all_tag ε C0 =>
      utyp_all_tag (swap_atom ε1 ε2 ε) (swap_tag_in_utyp ε1 ε2 C0)
  end.

(** ** Commutation with opening, and with type-variable substitution.
    A swap touches only the ε slots, which no type-level operation reads. *)

Lemma swap_tag_in_utyp_open_rec : forall ε1 ε2 C1 C2 k,
  swap_tag_in_utyp ε1 ε2 (open_utyp_wrt_utyp_rec k C2 C1)
  = open_utyp_wrt_utyp_rec k (swap_tag_in_utyp ε1 ε2 C2)
      (swap_tag_in_utyp ε1 ε2 C1).
Proof.
  intros ε1 ε2 C1. induction C1; intros C2 k; simpl; try reflexivity;
    try (rewrite IHC1; reflexivity);
    try (rewrite IHC1_1, IHC1_2; reflexivity).
  destruct (lt_eq_lt_dec n k) as [[?|?]|?]; reflexivity.
Qed.

Lemma swap_tag_in_utyp_open : forall ε1 ε2 C1 C2,
  swap_tag_in_utyp ε1 ε2 (open_utyp_wrt_utyp C1 C2)
  = open_utyp_wrt_utyp (swap_tag_in_utyp ε1 ε2 C1)
      (swap_tag_in_utyp ε1 ε2 C2).
Proof.
  intros. unfold open_utyp_wrt_utyp. apply swap_tag_in_utyp_open_rec.
Qed.

Lemma swap_tag_in_utyp_open_var : forall ε1 ε2 C α,
  swap_tag_in_utyp ε1 ε2 (open_utyp_wrt_utyp C (utyp_var_f α))
  = open_utyp_wrt_utyp (swap_tag_in_utyp ε1 ε2 C) (utyp_var_f α).
Proof.
  intros. unfold open_utyp_wrt_utyp. apply swap_tag_in_utyp_open_rec.
Qed.

(** ** Free TYPE variables and local closure are blind to the swap. *)

Lemma ftvar_swap_tag_in_utyp : forall ε1 ε2 C,
  ftvar_in_utyp (swap_tag_in_utyp ε1 ε2 C) = ftvar_in_utyp C.
Proof. induction C; simpl; congruence. Qed.

Lemma lc_swap_tag_in_utyp : forall ε1 ε2 C,
  lc_utyp C -> lc_utyp (swap_tag_in_utyp ε1 ε2 C).
Proof.
  intros ε1 ε2 C H; induction H; simpl; try solve [ constructor; auto ].
  - apply lc_utyp_all_syn. intros α.
    rewrite <- swap_tag_in_utyp_open_var. auto.
  - apply lc_utyp_all_tag. intros α.
    rewrite <- swap_tag_in_utyp_open_var. auto.
Qed.

(** ** The ε-tag collectors transport EXACTLY — this is the fact the whole
    freshening rests on. *)

Lemma ftag_swap_tag_in_utyp : forall ε1 ε2 C,
  ftag_in_utyp (swap_tag_in_utyp ε1 ε2 C)
  [=] swap_atoms ε1 ε2 (ftag_in_utyp C).
Proof.
  intros ε1 ε2 C. induction C; simpl;
    try solve [ rewrite swap_atoms_empty; reflexivity ].
  - rewrite IHC1, IHC2, swap_atoms_union. reflexivity.
  - exact IHC.
  - rewrite IHC, swap_atoms_add. reflexivity.
Qed.

(** A term with no tag to move is fixed by the swap. *)
Lemma swap_tag_in_utyp_fresh_eq : forall ε1 ε2 C,
  ε1 `notin` ftag_in_utyp C -> ε2 `notin` ftag_in_utyp C ->
  swap_tag_in_utyp ε1 ε2 C = C.
Proof.
  intros ε1 ε2 C. induction C; simpl; intros H1 H2; try reflexivity.
  - rewrite IHC1, IHC2; try reflexivity; clear - H1 H2; fsetdec.
  - rewrite IHC; try reflexivity; assumption.
  - rewrite IHC; try solve [ clear - H1 H2; fsetdec ].
    rewrite swap_atom_other; [ reflexivity | | ]; clear - H1 H2; fsetdec.
Qed.

(** ** The tagged-sort predicates transport. *)

Lemma is_dtyp_swap_tag : forall ε1 ε2 C,
  is_dtyp C -> is_dtyp (swap_tag_in_utyp ε1 ε2 C).
Proof.
  intros ε1 ε2 C H; induction H; simpl; try solve [ constructor; auto ].
  apply is_dtyp__all_tag with (L := L). intros α Hα.
  rewrite <- swap_tag_in_utyp_open_var. auto.
Qed.

Lemma guarded_utyp_swap_tag : forall ε1 ε2 C,
  guarded_utyp C -> guarded_utyp (swap_tag_in_utyp ε1 ε2 C).
Proof.
  intros ε1 ε2 C H; inversion H; subst; simpl;
    [ apply guarded_utyp__unit | apply guarded_utyp__var
    | apply guarded_utyp__arrow; apply lc_swap_tag_in_utyp; assumption ].
Qed.

(* ===================================================================== *)
(*  §3  PUSHING THE SWAP THROUGH A STATED TAG EQUATION.                   *)
(*                                                                        *)
(*  Every judgment states its tag context up to [ [=] ] rather than       *)
(*  syntactically, so an equivariance proof never applies the swap to a   *)
(*  term: it re-derives the rule's own equation for the swapped context.  *)
(*  These four are those re-derivations, one per shape the rules use.     *)
(* ===================================================================== *)

Lemma swap_atoms_empty_of : forall ε1 ε2 Ψ Ψs,
  Ψ [=] empty -> Ψs [=] swap_atoms ε1 ε2 Ψ -> Ψs [=] empty.
Proof.
  intros ε1 ε2 Ψ Ψs H Heq.
  rewrite Heq, (swap_atoms_cong ε1 ε2 _ _ H). apply swap_atoms_empty.
Qed.

Lemma swap_atoms_union_of : forall ε1 ε2 Ψ Ψ1 Ψ2 Ψs,
  Ψ [=] Ψ1 `union` Ψ2 -> Ψs [=] swap_atoms ε1 ε2 Ψ ->
  Ψs [=] (swap_atoms ε1 ε2 Ψ1) `union` (swap_atoms ε1 ε2 Ψ2).
Proof.
  intros ε1 ε2 Ψ Ψ1 Ψ2 Ψs H Heq.
  rewrite Heq, (swap_atoms_cong ε1 ε2 _ _ H). apply swap_atoms_union.
Qed.

Lemma swap_atoms_add_of : forall ε1 ε2 ε Ψ Ψ0 Ψs,
  Ψ [=] add ε Ψ0 -> Ψs [=] swap_atoms ε1 ε2 Ψ ->
  Ψs [=] add (swap_atom ε1 ε2 ε) (swap_atoms ε1 ε2 Ψ0).
Proof.
  intros ε1 ε2 ε Ψ Ψ0 Ψs H Heq.
  rewrite Heq, (swap_atoms_cong ε1 ε2 _ _ H). apply swap_atoms_add.
Qed.

Lemma swap_atoms_subset_of : forall ε1 ε2 S T,
  S [<=] T -> (swap_atoms ε1 ε2 S) [<=] (swap_atoms ε1 ε2 T).
Proof.
  intros ε1 ε2 S T H α Hα.
  apply swap_atoms_spec. apply H. apply swap_atoms_spec. exact Hα.
Qed.

Lemma swap_atoms_disjoint_of : forall ε1 ε2 S T,
  S ∩ T [=] empty ->
  (swap_atoms ε1 ε2 S) ∩ (swap_atoms ε1 ε2 T) [=] empty.
Proof.
  intros ε1 ε2 S T H.
  rewrite <- swap_atoms_inter, (swap_atoms_cong ε1 ε2 _ _ H).
  apply swap_atoms_empty.
Qed.

(** ⭐ THE TWO FACTS A FRESHENING STEP NEEDS.  A swap that leaves a set [T]
    alone preserves disjointness from it; and if it moves one member of
    [S ∩ T] to an atom outside both, the intersection strictly shrinks — which
    is the measure the iteration in decl/prop_tag_swap.v decreases. *)

Lemma swap_atoms_shrink : forall ε1 ε2 S T,
  ε1 `in` S -> ε1 `in` T -> ε2 `notin` S -> ε2 `notin` T ->
  cardinal ((swap_atoms ε1 ε2 S) ∩ T) < cardinal (S ∩ T).
Proof.
  intros ε1 ε2 S T Hin1S Hin1T Hni2S Hni2T.
  assert (Hout : ε1 `notin` swap_atoms ε1 ε2 S).
  { intros Hc. rewrite swap_atoms_spec in Hc. unfold swap_atom in Hc.
    destruct (ε1 == ε1) as [ _ | Hne ];
      [ apply Hni2S; exact Hc | apply Hne; reflexivity ]. }
  apply subset_cardinal_lt with (x := ε1).
  - intros α Hα. apply AtomSetFacts.inter_iff in Hα as [ Hs Ht ].
    apply AtomSetFacts.inter_iff. split; [ | exact Ht ].
    assert (Hne1 : α <> ε1) by (intros ->; contradiction).
    assert (Hne2 : α <> ε2) by (intros ->; contradiction).
    rewrite swap_atoms_spec in Hs.
    rewrite (swap_atom_other ε1 ε2 α Hne1 Hne2) in Hs. exact Hs.
  - apply AtomSetFacts.inter_iff. split; assumption.
  - intros Hc. apply AtomSetFacts.inter_iff in Hc as [ Hc _ ]. contradiction.
Qed.

(* ===================================================================== *)
(*  §4  [ftag_in_uskl] across opening                                     *)
(*                                                                        *)
(*  ⚙ Moved here 2026-10-10 from algo/consis/prop_consis_precise.v.       *)
(* ===================================================================== *)

Lemma ftag_in_uskl_open_rec_var : forall α' R k,
  ftag_in_uskl (open_uskl_wrt_uskl_rec k (uskl_var_f α') R) [=] ftag_in_uskl R.
Proof.
  intros α' R; induction R; intros k; simpl; try fsetdec.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; fsetdec.
  - pose proof (IHR1 k); pose proof (IHR2 k); fsetdec.
  - pose proof (IHR (S k)); fsetdec.
  - pose proof (IHR (S k)); fsetdec.
  - pose proof (IHR k); fsetdec.
  - pose proof (IHR k); fsetdec.
Qed.

Lemma ftag_in_uskl_open_var : forall R α,
  ftag_in_uskl (open_uskl_wrt_uskl R (uskl_var_f α)) [=] ftag_in_uskl R.
Proof.
  intros; unfold open_uskl_wrt_uskl; apply ftag_in_uskl_open_rec_var.
Qed.

Lemma ftag_in_uskl_open_rec_upper : forall R ψ k,
  ftag_in_uskl (open_uskl_wrt_uskl_rec k ψ R) [<=]
  ftag_in_uskl R `union` ftag_in_uskl ψ.
Proof.
  intros R ψ; induction R; intros k; simpl; try fsetdec.
  - destruct (lt_eq_lt_dec n k) as [[?|?]|?]; simpl; fsetdec.
  - pose proof (IHR1 k); pose proof (IHR2 k); fsetdec.
  - pose proof (IHR (S k)); fsetdec.
  - pose proof (IHR (S k)); fsetdec.
  - pose proof (IHR k); fsetdec.
  - pose proof (IHR k); fsetdec.
Qed.

Lemma ftag_in_uskl_open_upper : forall R ψ,
  ftag_in_uskl (open_uskl_wrt_uskl R ψ) [<=]
  ftag_in_uskl R `union` ftag_in_uskl ψ.
Proof.
  intros; unfold open_uskl_wrt_uskl; apply ftag_in_uskl_open_rec_upper.
Qed.
