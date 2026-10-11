(** Skeleton relations and iterated swaps used by lifting and threaded
    solver determinism. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.prop_ln.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_tag.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.prop_context.
Require Import src.fresco.algo.basic.prop_swap.
Require Import src.fresco.algo.subtyping.prop_solve_sub.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.subtyping.def_look.

Open Scope fresco_a_scope.

(* ===================================================================== *)
(*  §1  Equality up to an aligned fresh-pair list                         *)
(*                                                                        *)
(*  [rel_pskl ρ V P1 P2]: P1 and P2 coincide except that a variable may   *)
(*  be replaced along one of ρ's PAIRS; variables outside the pairs must  *)
(*  sit in the identity support [V].  ⚠️ DELIBERATELY RELATIONAL: the     *)
(*  a-side rules allow one derivation to guess the SAME flexible for two  *)
(*  ghosts ([a_guess_mono__arrow] runs both halves at Θ), so a functional  *)
(*  "renaming" does not exist in general — uniqueness of the columns is   *)
(*  used by lifting, where the runner-side block is [uniq] for free.      *)
(*  The derivation side carries its own uniqueness premise.              *)
(* ===================================================================== *)

Fixpoint cols_l (ρ : list (atom * atom)) : atoms :=
  match ρ with
  | nil => empty
  | p :: ρ' => add (fst p) (cols_l ρ')
  end.

Fixpoint cols_r (ρ : list (atom * atom)) : atoms :=
  match ρ with
  | nil => empty
  | p :: ρ' => add (snd p) (cols_r ρ')
  end.

Lemma cols_l_app : forall ρ1 ρ2,
  cols_l (ρ1 ++ ρ2) [=] cols_l ρ1 ∪ cols_l ρ2.
Proof.
  induction ρ1 as [ | p ρ1 IH ]; intros; simpl; [ fsetdec | ].
  rewrite IH. fsetdec.
Qed.

Lemma cols_r_app : forall ρ1 ρ2,
  cols_r (ρ1 ++ ρ2) [=] cols_r ρ1 ∪ cols_r ρ2.
Proof.
  induction ρ1 as [ | p ρ1 IH ]; intros; simpl; [ fsetdec | ].
  rewrite IH. fsetdec.
Qed.

Lemma cols_l_in : forall ρ α β, In (α, β) ρ -> α `in` cols_l ρ.
Proof.
  induction ρ as [ | [a b] ρ IH ]; intros * Hin; simpl in *;
    [ contradiction | ].
  destruct Hin as [E | Hin]; [ inversion E; subst; fsetdec | ].
  pose proof (IH _ _ Hin). fsetdec.
Qed.

Lemma cols_r_in : forall ρ α β, In (α, β) ρ -> β `in` cols_r ρ.
Proof.
  induction ρ as [ | [a b] ρ IH ]; intros * Hin; simpl in *;
    [ contradiction | ].
  destruct Hin as [E | Hin]; [ inversion E; subst; fsetdec | ].
  pose proof (IH _ _ Hin). fsetdec.
Qed.

Lemma cols_l_in_inv : forall ρ a,
  a `in` cols_l ρ -> exists b, In (a, b) ρ.
Proof.
  induction ρ as [ | [x y] ρ IH ]; intros a Ha; simpl in *.
  - exfalso. clear - Ha. fsetdec.
  - destruct (a == x) as [-> | Hne].
    + exists y. left. reflexivity.
    + assert (Ha' : a `in` cols_l ρ) by (clear - Ha Hne; fsetdec).
      destruct (IH _ Ha') as [b Hin]. exists b. right. exact Hin.
Qed.

Lemma cols_r_in_inv : forall ρ b,
  b `in` cols_r ρ -> exists a, In (a, b) ρ.
Proof.
  induction ρ as [ | [x y] ρ IH ]; intros b Hb; simpl in *.
  - exfalso. clear - Hb. fsetdec.
  - destruct (b == y) as [-> | Hne].
    + exists x. left. reflexivity.
    + assert (Hb' : b `in` cols_r ρ) by (clear - Hb Hne; fsetdec).
      destruct (IH _ Hb') as [a Hin]. exists a. right. exact Hin.
Qed.

Inductive rel_atom (ρ : list (atom * atom)) (V : atoms)
    : atom -> atom -> Prop :=
| rel_atom__pair : forall α β, In (α, β) ρ -> rel_atom ρ V α β
| rel_atom__id : forall α, α `in` V -> rel_atom ρ V α α.

Inductive rel_pskl (ρ : list (atom * atom)) (V : atoms)
    : pskl -> pskl -> Prop :=
| rel_pskl__unit : rel_pskl ρ V pskl_unit pskl_unit
| rel_pskl__var_b : forall n, rel_pskl ρ V (pskl_var_b n) (pskl_var_b n)
| rel_pskl__var_f : forall α β,
    rel_atom ρ V α β ->
    rel_pskl ρ V (pskl_var_f α) (pskl_var_f β)
| rel_pskl__arrow : forall P1 P2 Q1 Q2,
    rel_pskl ρ V P1 Q1 -> rel_pskl ρ V P2 Q2 ->
    rel_pskl ρ V (pskl_arrow P1 P2) (pskl_arrow Q1 Q2)
| rel_pskl__all_syn : forall P Q,
    rel_pskl ρ V P Q ->
    rel_pskl ρ V (pskl_all_syn P) (pskl_all_syn Q)
| rel_pskl__ghost : rel_pskl ρ V pskl_ghost pskl_ghost
| rel_pskl__univ_ghost : forall P Q,
    rel_pskl ρ V P Q ->
    rel_pskl ρ V (pskl_univ_ghost P) (pskl_univ_ghost Q).

(** One monotonicity lemma covers pair-append (either side) and
    V-weakening. *)
Lemma rel_pskl_mono : forall ρ ρ' V V' P1 P2,
  rel_pskl ρ V P1 P2 ->
  (forall α β, In (α, β) ρ -> In (α, β) ρ') ->
  V [<=] V' ->
  rel_pskl ρ' V' P1 P2.
Proof.
  intros * Hrel Hincl Hsub.
  induction Hrel; constructor; auto.
  match goal with
  | Ha : rel_atom _ _ _ _ |- _ =>
      inversion Ha; subst;
      [ apply rel_atom__pair; auto
      | apply rel_atom__id; fsetdec ]
  end.
Qed.

Lemma rel_pskl_refl : forall ρ V P,
  ftvar_in_pskl P [<=] V ->
  rel_pskl ρ V P P.
Proof.
  intros ρ V P; induction P; intros Hsub; simpl in *; constructor;
    try (apply IHP || (apply IHP1 + apply IHP2)); try fsetdec.
  apply rel_atom__id. fsetdec.
Qed.

Lemma rel_pskl_ftv_r : forall ρ V P1 P2,
  rel_pskl ρ V P1 P2 ->
  ftvar_in_pskl P2 [<=] V ∪ cols_r ρ.
Proof.
  intros * Hrel; induction Hrel; simpl; try fsetdec.
  match goal with
  | Ha : rel_atom _ _ _ _ |- _ =>
      inversion Ha; subst;
      [ match goal with
        | Hin : In _ _ |- _ => apply cols_r_in in Hin; fsetdec
        end
      | fsetdec ]
  end.
Qed.

(** Opening related bodies at a PAIR of names extends the relation by
    that pair — the §8c.9 pair induction's binder-row move: the two
    sides' openers are never renamed to a common atom, they are simply
    paired into ρ. *)
Lemma rel_pskl_open_rec_pair : forall ρ V P1 P2 β1 β2 k,
  rel_pskl ρ V P1 P2 ->
  rel_pskl ((β1, β2) :: ρ) V
    (open_pskl_wrt_pskl_rec k (pskl_var_f β1) P1)
    (open_pskl_wrt_pskl_rec k (pskl_var_f β2) P2).
Proof.
  intros * Hrel; revert k; induction Hrel; intros k; simpl;
    try (constructor; auto; fail).
  - (* var_b: below the binder both sides stay; AT it the pair enters *)
    destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt];
      [ constructor | | constructor ].
    apply rel_pskl__var_f. apply rel_atom__pair. left. reflexivity.
  - (* var_f: the old relation rides into the extended ρ *)
    apply rel_pskl__var_f.
    match goal with
    | Ha : rel_atom _ _ _ _ |- _ => inversion Ha; subst
    end.
    + apply rel_atom__pair. right. assumption.
    + apply rel_atom__id. assumption.
Qed.

Lemma rel_pskl_open_pair : forall ρ V P1 P2 β1 β2,
  rel_pskl ρ V P1 P2 ->
  rel_pskl ((β1, β2) :: ρ) V
    (open_pskl_wrt_pskl P1 (pskl_var_f β1))
    (open_pskl_wrt_pskl P2 (pskl_var_f β2)).
Proof.
  intros. unfold open_pskl_wrt_pskl. apply rel_pskl_open_rec_pair; auto.
Qed.

(** Opening both sides at ONE common name grows the identity support
    instead — the transports' binder rows (a globally fresh atom
    satisfies both sides' per-side freshness). *)
Lemma rel_pskl_open_rec_var : forall ρ V P1 P2 β k,
  rel_pskl ρ V P1 P2 ->
  rel_pskl ρ (add β V)
    (open_pskl_wrt_pskl_rec k (pskl_var_f β) P1)
    (open_pskl_wrt_pskl_rec k (pskl_var_f β) P2).
Proof.
  intros * Hrel; revert k; induction Hrel; intros k; simpl;
    try (constructor; auto; fail).
  - (* var_b *)
    destruct (lt_eq_lt_dec n k) as [[Hlt | Heq] | Hgt];
      [ constructor | | constructor ].
    apply rel_pskl__var_f. apply rel_atom__id. clear. fsetdec.
  - (* var_f *)
    apply rel_pskl__var_f.
    match goal with
    | Ha : rel_atom _ _ _ _ |- _ => inversion Ha; subst
    end.
    + apply rel_atom__pair. assumption.
    + apply rel_atom__id.
      match goal with
      | Hin : _ `in` V |- _ => clear - Hin; fsetdec
      end.
Qed.

Lemma rel_pskl_open_var : forall ρ V P1 P2 β,
  rel_pskl ρ V P1 P2 ->
  rel_pskl ρ (add β V)
    (open_pskl_wrt_pskl P1 (pskl_var_f β))
    (open_pskl_wrt_pskl P2 (pskl_var_f β)).
Proof.
  intros. unfold open_pskl_wrt_pskl. apply rel_pskl_open_rec_var; auto.
Qed.

(** [close] at a PAIR of names — the mirror of [rel_pskl_open_pair]: the
    two sides close their own opener in lockstep, and the pair leaves the
    relation.  The column-freshness side conditions say the pair's atoms
    have no OTHER role in the relation — which is what the rel-transports'
    binder rows (ext_algo/subtyping/prop_solve_rel.v) supply from the rules' own
    freshness. *)
Lemma rel_pskl_close_rec_pair : forall ρ V P1 P2 β1 β2 k,
  rel_pskl ((β1, β2) :: ρ) V P1 P2 ->
  β1 `notin` V -> β1 `notin` cols_l ρ ->
  β2 `notin` V -> β2 `notin` cols_r ρ ->
  rel_pskl ρ V (close_pskl_wrt_pskl_rec k β1 P1)
               (close_pskl_wrt_pskl_rec k β2 P2).
Proof.
  intros * Hrel Hb1V Hb1c Hb2V Hb2c.
  remember ((β1, β2) :: ρ) as ρ0 eqn:Hρ0. revert k.
  induction Hrel; subst; intros k; simpl; try (constructor; auto; fail).
  - (* var_b: both sides shift identically *)
    destruct (lt_ge_dec n k); constructor.
  - (* var_f *)
    match goal with
    | Ha : rel_atom _ _ _ _ |- _ => inversion Ha; subst
    end.
    + (* pair: the head pair closes in lockstep; a ρ-pair survives *)
      match goal with
      | Hx : In (?a, ?b) ((β1, β2) :: _) |- _ => rename Hx into HIn0
      end.
      destruct HIn0 as [E | HIn0]; [ inversion E; subst | ].
      * repeat match goal with
               | |- context [ if ?X then _ else _ ] => destruct X
               end;
          try (exfalso; congruence); constructor.
      * pose proof (cols_l_in _ _ _ HIn0) as Hcl.
        pose proof (cols_r_in _ _ _ HIn0) as Hcr.
        repeat match goal with
               | |- context [ if ?X then _ else _ ] => destruct X; subst
               end;
          try solve [ exfalso; clear - Hb1c Hcl; fsetdec
                    | exfalso; clear - Hb2c Hcr; fsetdec ];
          constructor; apply rel_atom__pair; exact HIn0.
    + (* id: the atom is in V, so it is neither β1 nor β2 *)
      match goal with
      | Hv : _ `in` V |- _ => rename Hv into HVin
      end.
      repeat match goal with
             | |- context [ if ?X then _ else _ ] => destruct X; subst
             end;
        try solve [ exfalso; clear - Hb1V HVin; fsetdec
                  | exfalso; clear - Hb2V HVin; fsetdec ];
        constructor; apply rel_atom__id; exact HVin.
Qed.

Lemma rel_pskl_close_pair : forall ρ V P1 P2 β1 β2,
  rel_pskl ((β1, β2) :: ρ) V P1 P2 ->
  β1 `notin` V -> β1 `notin` cols_l ρ ->
  β2 `notin` V -> β2 `notin` cols_r ρ ->
  rel_pskl ρ V (close_pskl_wrt_pskl β1 P1) (close_pskl_wrt_pskl β2 P2).
Proof.
  intros. unfold close_pskl_wrt_pskl. apply rel_pskl_close_rec_pair; auto.
Qed.

(* Iterated swaps. *)

Fixpoint swaps_atom (ps : list (atom * atom)) (α : atom) : atom :=
  match ps with
  | nil => α
  | (a, b) :: ps' => swaps_atom ps' (swap_atom a b α)
  end.

Fixpoint swaps_pskl (ps : list (atom * atom)) (P : pskl) : pskl :=
  match ps with
  | nil => P
  | (a, b) :: ps' => swaps_pskl ps' (swap_pskl a b P)
  end.

Fixpoint swaps_aenv (ps : list (atom * atom)) (Θ : aenv) : aenv :=
  match ps with
  | nil => Θ
  | (a, b) :: ps' => swaps_aenv ps' (swap_aenv a b Θ)
  end.

Fixpoint swaps_cstrs (ps : list (atom * atom)) (C : a_cstrs) : a_cstrs :=
  match ps with
  | nil => C
  | (a, b) :: ps' => swaps_cstrs ps' (swap_cstrs a b C)
  end.

(** ⚙ The [ptyp] member, added 2026-08-17 for §8c.10: [guess^TY] returns a
    [ptyp], and the consistency level relates the derivation's payload to
    the runner's along a chain. *)
Fixpoint swaps_ptyp (ps : list (atom * atom)) (A : ptyp) : ptyp :=
  match ps with
  | nil => A
  | (a, b) :: ps' => swaps_ptyp ps' (swap_ptyp a b A)
  end.

Lemma swaps_atom_app : forall ps1 ps2 α,
  swaps_atom (ps1 ++ ps2) α = swaps_atom ps2 (swaps_atom ps1 α).
Proof.
  induction ps1 as [ | [a b] ps1 IH ]; intros; simpl; auto.
Qed.

Lemma swaps_atom_notin : forall ps α,
  (forall a b, In (a, b) ps -> α <> a /\ α <> b) ->
  swaps_atom ps α = α.
Proof.
  induction ps as [ | [a b] ps IH ]; intros α Hav; simpl; auto.
  destruct (Hav a b (or_introl eq_refl)) as [Hna Hnb].
  rewrite (swap_atom_other a b α Hna Hnb).
  apply IH. intros a' b' Hin. apply Hav. right. exact Hin.
Qed.

Lemma swaps_pskl_ghost : forall ps, swaps_pskl ps pskl_ghost = pskl_ghost.
Proof. induction ps as [ | [a b] ps IH ]; simpl; auto. Qed.

Lemma swaps_pskl_var_f : forall ps α,
  swaps_pskl ps (pskl_var_f α) = pskl_var_f (swaps_atom ps α).
Proof. induction ps as [ | [a b] ps IH ]; simpl; auto. Qed.

Lemma swaps_pskl_arrow : forall ps P Q,
  swaps_pskl ps (pskl_arrow P Q)
  = pskl_arrow (swaps_pskl ps P) (swaps_pskl ps Q).
Proof. induction ps as [ | [a b] ps IH ]; simpl; auto. Qed.

Lemma swaps_pskl_all_syn : forall ps P,
  swaps_pskl ps (pskl_all_syn P) = pskl_all_syn (swaps_pskl ps P).
Proof. induction ps as [ | [a b] ps IH ]; simpl; auto. Qed.

Lemma swaps_pskl_univ_ghost : forall ps P,
  swaps_pskl ps (pskl_univ_ghost P) = pskl_univ_ghost (swaps_pskl ps P).
Proof. induction ps as [ | [a b] ps IH ]; simpl; auto. Qed.

Lemma swaps_pskl_fresh_id : forall ps P,
  (forall a b, In (a, b) ps ->
     a `notin` ftvar_in_pskl P /\ b `notin` ftvar_in_pskl P) ->
  swaps_pskl ps P = P.
Proof.
  induction ps as [ | [a b] ps IH ]; intros P Hav; simpl; auto.
  destruct (Hav a b (or_introl eq_refl)) as [Hna Hnb].
  rewrite (swap_pskl_fresh_id a b P Hna Hnb).
  apply IH. intros a' b' Hin. apply Hav. right. exact Hin.
Qed.

(** The atom-SET member of the [swaps_*] family.  ⚙ Added 2026-08-16 for
    §8c.10, whose judgements carry two set indexes (Δ1/Δ2) and a set-valued
    SUPPLY; the single-transposition [swap_atoms] and its congruence are
    upstream in fresco/prop_tag.v. *)
Fixpoint swaps_atoms (ps : list (atom * atom)) (S : atoms) : atoms :=
  match ps with
  | nil => S
  | (a, b) :: ps' => swaps_atoms ps' (swap_atoms a b S)
  end.

Lemma swaps_atoms_cong : forall ps S T,
  S [=] T -> swaps_atoms ps S [=] swaps_atoms ps T.
Proof.
  induction ps as [ | [a b] ps IH ]; intros S T Heq; simpl; auto.
  apply IH. apply swap_atoms_cong. exact Heq.
Qed.

(** A chain commutes with [add] — the set-level companion of
    [swaps_atom]'s action on a single name.  ⭐ THIS IS THE SHAPE EVERY
    SUPPLY OBLIGATION TAKES: the supplies a run threads are built by
    [add]ing the drawn names onto the input supply, so relating two of them
    across a chain means peeling the [add]s down to the common base, where
    [swaps_atoms_notin] finishes. *)
Lemma swaps_atoms_add : forall ps α (S : atoms),
  swaps_atoms ps (add α S) [=] add (swaps_atom ps α) (swaps_atoms ps S).
Proof.
  induction ps as [ | [a b] ps IH ]; intros α S; simpl; [ reflexivity | ].
  rewrite (swaps_atoms_cong ps _ _ (swap_atoms_add a b α S)). apply IH.
Qed.

Lemma swaps_aenv_app_dist : forall ps Θ1 Θ2,
  swaps_aenv ps (Θ1 ++ Θ2) = swaps_aenv ps Θ1 ++ swaps_aenv ps Θ2.
Proof.
  induction ps as [ | [a b] ps IH ]; intros; simpl; auto.
  rewrite swap_aenv_app. apply IH.
Qed.

(* ---- what §8c.10's level-5 induction adds (2026-08-17) ----------------
   The four sorts' [fresh_id] / structural / composition members.  A chain
   is applied LEFT TO RIGHT ([swaps_X (p :: ps) = swaps_X ps (swap_X p ·)]),
   which is why composition reads [swaps_X (ps1 ++ ps2) = swaps_X ps2 ∘
   swaps_X ps1] — the order the consistency level's [U-Arrow] needs. *)

Lemma swaps_pskl_app : forall ps1 ps2 P,
  swaps_pskl (ps1 ++ ps2) P = swaps_pskl ps2 (swaps_pskl ps1 P).
Proof. induction ps1 as [ | [a b] ps1 IH ]; intros; simpl; auto. Qed.

Lemma swaps_aenv_app : forall ps1 ps2 (Θ : aenv),
  swaps_aenv (ps1 ++ ps2) Θ = swaps_aenv ps2 (swaps_aenv ps1 Θ).
Proof. induction ps1 as [ | [a b] ps1 IH ]; intros; simpl; auto. Qed.

Lemma swaps_atoms_app : forall ps1 ps2 (S : atoms),
  swaps_atoms (ps1 ++ ps2) S = swaps_atoms ps2 (swaps_atoms ps1 S).
Proof. induction ps1 as [ | [a b] ps1 IH ]; intros; simpl; auto. Qed.

Lemma swaps_ptyp_app : forall ps1 ps2 A,
  swaps_ptyp (ps1 ++ ps2) A = swaps_ptyp ps2 (swaps_ptyp ps1 A).
Proof. induction ps1 as [ | [a b] ps1 IH ]; intros; simpl; auto. Qed.

Lemma swaps_ptyp_var_f : forall ps α,
  swaps_ptyp ps (ptyp_var_f α) = ptyp_var_f (swaps_atom ps α).
Proof. induction ps as [ | [a b] ps IH ]; simpl; auto. Qed.

Lemma swaps_ptyp_arrow : forall ps A B,
  swaps_ptyp ps (ptyp_arrow A B)
  = ptyp_arrow (swaps_ptyp ps A) (swaps_ptyp ps B).
Proof. induction ps as [ | [a b] ps IH ]; simpl; auto. Qed.

Lemma swaps_ptyp_all : forall ps A,
  swaps_ptyp ps (ptyp_all A) = ptyp_all (swaps_ptyp ps A).
Proof. induction ps as [ | [a b] ps IH ]; simpl; auto. Qed.

Lemma mono_ptyp_swaps : forall ps A,
  mono_ptyp A -> mono_ptyp (swaps_ptyp ps A).
Proof.
  induction ps as [ | [a b] ps IH ]; intros A H; simpl; auto.
  apply IH. apply mono_ptyp_swap. exact H.
Qed.

Lemma swaps_ptyp_close : forall ps c A,
  swaps_ptyp ps (close_ptyp_wrt_ptyp c A)
  = close_ptyp_wrt_ptyp (swaps_atom ps c) (swaps_ptyp ps A).
Proof.
  induction ps as [ | [a b] ps IH ]; intros; simpl; auto.
  rewrite swap_ptyp_close. apply IH.
Qed.

Lemma swaps_pskl_close : forall ps c P,
  swaps_pskl ps (close_pskl_wrt_pskl c P)
  = close_pskl_wrt_pskl (swaps_atom ps c) (swaps_pskl ps P).
Proof.
  induction ps as [ | [a b] ps IH ]; intros; simpl; auto.
  rewrite swap_pskl_close. apply IH.
Qed.

Lemma swaps_ptyp_fresh_id : forall ps A,
  (forall a b, In (a, b) ps ->
     a `notin` ftvar_in_ptyp A /\ b `notin` ftvar_in_ptyp A) ->
  swaps_ptyp ps A = A.
Proof.
  induction ps as [ | [a b] ps IH ]; intros A Hav; simpl; auto.
  destruct (Hav a b (or_introl eq_refl)) as [Hna Hnb].
  rewrite (swap_ptyp_fresh_id a b A Hna Hnb).
  apply IH. intros a' b' Hin. apply Hav. right. exact Hin.
Qed.

Lemma swaps_aenv_fresh_id : forall ps (Θ : aenv),
  (forall a b, In (a, b) ps ->
     a `notin` ftvar_in_aenv Θ /\ b `notin` ftvar_in_aenv Θ) ->
  swaps_aenv ps Θ = Θ.
Proof.
  induction ps as [ | [a b] ps IH ]; intros Θ Hav; simpl; auto.
  destruct (Hav a b (or_introl eq_refl)) as [Hna Hnb].
  rewrite (swap_aenv_fresh_id a b Θ Hna Hnb).
  apply IH. intros a' b' Hin. apply Hav. right. exact Hin.
Qed.

Lemma swaps_atoms_notin : forall ps (S : atoms),
  (forall a b, In (a, b) ps -> a `notin` S /\ b `notin` S) ->
  swaps_atoms ps S [=] S.
Proof.
  induction ps as [ | [a b] ps IH ]; intros S Hav; simpl;
    [ reflexivity | ].
  destruct (Hav a b (or_introl eq_refl)) as [Hna Hnb].
  assert (Hs : swaps_atoms ps (swap_atoms a b S) [=] swaps_atoms ps S)
    by (apply swaps_atoms_cong; apply swap_atoms_notin; assumption).
  rewrite Hs. apply IH. intros a' b' Hin. apply Hav. right. exact Hin.
Qed.

(* Flexible blocks indexed by pair columns. *)

Definition flex_pairs_l (ρ : list (atom * atom)) : aenv :=
  List.map (fun p => (fst p, abind_flex_mono)) ρ.

Definition flex_pairs_r (ρ : list (atom * atom)) : aenv :=
  List.map (fun p => (snd p, abind_flex_mono)) ρ.

Lemma flex_pairs_l_app : forall ρ1 ρ2,
  flex_pairs_l (ρ1 ++ ρ2) = flex_pairs_l ρ1 ++ flex_pairs_l ρ2.
Proof. intros. unfold flex_pairs_l. apply List.map_app. Qed.

Lemma flex_pairs_r_app : forall ρ1 ρ2,
  flex_pairs_r (ρ1 ++ ρ2) = flex_pairs_r ρ1 ++ flex_pairs_r ρ2.
Proof. intros. unfold flex_pairs_r. apply List.map_app. Qed.

Lemma dom_flex_pairs_l : forall ρ, dom (flex_pairs_l ρ) [=] cols_l ρ.
Proof.
  induction ρ as [ | [a b] ρ IH ]; simpl; [ fsetdec | ].
  rewrite IH. fsetdec.
Qed.

Lemma dom_flex_pairs_r : forall ρ, dom (flex_pairs_r ρ) [=] cols_r ρ.
Proof.
  induction ρ as [ | [a b] ρ IH ]; simpl; [ fsetdec | ].
  rewrite IH. fsetdec.
Qed.

Lemma ftvar_in_aenv_flex_pairs_r : forall ρ,
  ftvar_in_aenv (flex_pairs_r ρ) [=] cols_r ρ.
Proof.
  induction ρ as [ | [a b] ρ IH ]; simpl; [ fsetdec | ].
  rewrite IH. fsetdec.
Qed.

(** ⚠️ [map] is metalib's ENV-map; the list one is [List.map] — the columns
    are read off the pair list, not off the blocks. *)
Lemma in_map_fst_cols_l : forall (ρ : list (atom * atom)) α,
  In α (List.map fst ρ) -> α `in` cols_l ρ.
Proof.
  intros * Hin. apply List.in_map_iff in Hin.
  destruct Hin as [[a b] [Heq Hin]]. simpl in Heq; subst.
  eapply cols_l_in; eassumption.
Qed.

Lemma in_map_snd_cols_r : forall (ρ : list (atom * atom)) β,
  In β (List.map snd ρ) -> β `in` cols_r ρ.
Proof.
  intros * Hin. apply List.in_map_iff in Hin.
  destruct Hin as [[a b] [Heq Hin]]. simpl in Heq; subst.
  eapply cols_r_in; eassumption.
Qed.

Lemma uniq_flex_pairs_l_nodup : forall ρ,
  uniq (flex_pairs_l ρ) -> NoDup (List.map fst ρ).
Proof.
  induction ρ as [ | [a b] ρ IH ]; intros Hu; simpl; [ constructor | ].
  simpl in Hu. apply uniq_cons_iff in Hu. destruct Hu as [Hu Hn].
  constructor; [ | apply IH; exact Hu ].
  intro Hin. apply in_map_fst_cols_l in Hin.
  rewrite <- dom_flex_pairs_l in Hin. contradiction.
Qed.

Lemma uniq_flex_pairs_r_nodup : forall ρ,
  uniq (flex_pairs_r ρ) -> NoDup (List.map snd ρ).
Proof.
  induction ρ as [ | [a b] ρ IH ]; intros Hu; simpl; [ constructor | ].
  simpl in Hu. apply uniq_cons_iff in Hu. destruct Hu as [Hu Hn].
  constructor; [ | apply IH; exact Hu ].
  intro Hin. apply in_map_snd_cols_r in Hin.
  rewrite <- dom_flex_pairs_r in Hin. contradiction.
Qed.

Fixpoint swaps_abind (ps : list (atom * atom)) (bd : abind) : abind :=
  match ps with
  | nil => bd
  | (a, b) :: ps' => swaps_abind ps' (swap_abind a b bd)
  end.

Lemma swaps_abind_flex_mono : forall ps,
  swaps_abind ps abind_flex_mono = abind_flex_mono.
Proof. induction ps as [ | [a b] ps IH ]; simpl; auto. Qed.

Lemma swaps_abind_tvar : forall ps,
  swaps_abind ps abind_tvar = abind_tvar.
Proof. induction ps as [ | [a b] ps IH ]; simpl; auto. Qed.

Lemma swaps_aenv_nil : forall ps, swaps_aenv ps nil = nil.
Proof. induction ps as [ | [a b] ps IH ]; simpl; auto. Qed.

Lemma swaps_aenv_cons : forall ps x bd Θ,
  swaps_aenv ps ((x, bd) :: Θ)
  = (swaps_atom ps x, swaps_abind ps bd) :: swaps_aenv ps Θ.
Proof.
  induction ps as [ | [a b] ps IH ]; intros; simpl; auto.
Qed.

(** The rigid marker a ∀ row pushes, transported — the packaged form
    §8c.10's three ∀ rows read off ([split_tvar_head] wants the head
    literally). *)
Lemma swaps_aenv_cons_tvar : forall ps x (Θ : aenv),
  swaps_aenv ps ((x ~ abind_tvar) ++ Θ)
  = (swaps_atom ps x ~ abind_tvar) ++ swaps_aenv ps Θ.
Proof.
  intros. rewrite swaps_aenv_app_dist. f_equal.
  unfold one. rewrite swaps_aenv_cons, swaps_abind_tvar, swaps_aenv_nil.
  reflexivity.
Qed.

Lemma swaps_abind_def : forall ps τ,
  swaps_abind ps (abind_flex_mono_def τ)
  = abind_flex_mono_def (swaps_ptyp ps τ).
Proof. induction ps as [ | [a b] ps IH ]; intros; simpl; auto. Qed.

Lemma swaps_aenv_one_def : forall ps x τ,
  swaps_aenv ps (x ~ abind_flex_mono_def τ)
  = (swaps_atom ps x ~ abind_flex_mono_def (swaps_ptyp ps τ)).
Proof.
  intros. unfold one.
  rewrite swaps_aenv_cons, swaps_abind_def, swaps_aenv_nil. reflexivity.
Qed.

Lemma swaps_aenv_one_flex : forall ps x,
  swaps_aenv ps (x ~ abind_flex_mono)
  = (swaps_atom ps x ~ abind_flex_mono).
Proof.
  intros. unfold one.
  rewrite swaps_aenv_cons, swaps_abind_flex_mono, swaps_aenv_nil.
  reflexivity.
Qed.

(** [uniq] of a transported block: [swap_atom] is injective, so a single
    swap preserves it ([swap_aenv_uniq]) and the chain is its fold. *)
Lemma swaps_aenv_uniq : forall ps (Θ : aenv),
  uniq Θ -> uniq (swaps_aenv ps Θ).
Proof.
  induction ps as [ | [a b] ps IH ]; intros Θ Hu; simpl;
    [ exact Hu | apply IH; apply swap_aenv_uniq; exact Hu ].
Qed.

Lemma swaps_cstrs_fresh_id : forall ps C,
  (forall a b, In (a, b) ps ->
     a `notin` ftvar_in_a_cstrs C /\ b `notin` ftvar_in_a_cstrs C) ->
  swaps_cstrs ps C = C.
Proof.
  induction ps as [ | [a b] ps IH ]; intros C Hav; simpl; auto.
  destruct (Hav a b (or_introl eq_refl)) as [Hna Hnb].
  assert (Hfix : swap_cstrs a b C = C).
  { clear - Hna Hnb. induction C as [ | c C IHC ]; simpl; auto.
    simpl in Hna, Hnb.
    unfold swap_cstrs in *. simpl. rewrite IHC by fsetdec.
    destruct c as [m Q | Q]; simpl in *; f_equal;
      unfold swap_cstr; f_equal;
      apply swap_pskl_fresh_id; fsetdec. }
  rewrite Hfix.
  apply IH. intros a' b' Hin. apply Hav. right. exact Hin.
Qed.

Lemma swaps_pskl_ptyp_to_pskl : forall ps A,
  swaps_pskl ps (ptyp_to_pskl A) = ptyp_to_pskl (swaps_ptyp ps A).
Proof.
  induction ps as [ | [a b] ps IH ]; intros; simpl; auto.
  rewrite swap_pskl_ptyp_to_pskl. apply IH.
Qed.

(** Align fresh opener supplies before transporting a recursive derivation. *)
Lemma swap_atoms_fresh_add : forall α β S,
  α `notin` S -> β `notin` S ->
  add β S [=] swap_atoms α β (add α S).
Proof.
  intros * Hα Hβ. rewrite swap_atoms_add, swap_atom_l.
  rewrite (swap_atoms_notin α β S Hα Hβ). reflexivity.
Qed.

(** A recursive chain avoids the extended supply; prefixing the opener
    swap therefore still avoids the ambient supply. *)
Lemma swaps_fresh_cons : forall α β ps S,
  α `notin` S -> β `notin` S ->
  (forall a b, In (a, b) ps -> a `notin` add β S /\ b `notin` add β S) ->
  forall a b, In (a, b) ((α, β) :: ps) -> a `notin` S /\ b `notin` S.
Proof.
  intros * Hα Hβ Hav a b [Heq | Hin].
  - inversion Heq; subst; auto.
  - destruct (Hav _ _ Hin) as [Ha Hb]. split; clear - Ha Hb; fsetdec.
Qed.

(** A chain that dodges [S] dodges every subset of [S].  With the
    [swaps_*_fresh_id] family this fixes any object whose free names [S]
    covers: [apply swaps_pskl_fresh_id, (swaps_dodge_sub Hav)] leaves only
    the coverage [ftvar_in_pskl P [<=] S]. *)
Lemma swaps_dodge_sub {ps} {S T : atoms} :
  (forall a b, In (a, b) ps -> a `notin` S /\ b `notin` S) ->
  T [<=] S ->
  forall a b, In (a, b) ps -> a `notin` T /\ b `notin` T.
Proof.
  intros Hav HT a b Hin. destruct (Hav _ _ Hin) as [Ha Hb].
  split; clear - Ha Hb HT; fsetdec.
Qed.

(** Two chains run one after the other dodge whatever both of them dodge. *)
Lemma swaps_dodge_app {ps1 ps2} {S1 S2 T : atoms} :
  (forall a b, In (a, b) ps1 -> a `notin` S1 /\ b `notin` S1) ->
  (forall a b, In (a, b) ps2 -> a `notin` S2 /\ b `notin` S2) ->
  T [<=] S1 -> T [<=] S2 ->
  forall a b, In (a, b) (ps1 ++ ps2) -> a `notin` T /\ b `notin` T.
Proof.
  intros Hav1 Hav2 H1 H2 a b Hin. apply in_app_or in Hin.
  destruct Hin as [Hin | Hin].
  - exact (swaps_dodge_sub Hav1 H1 a b Hin).
  - exact (swaps_dodge_sub Hav2 H2 a b Hin).
Qed.

(** The common case: the first chain dodges exactly the set at hand. *)
Lemma swaps_dodge_app_l {ps1 ps2} {S2 T : atoms} :
  (forall a b, In (a, b) ps1 -> a `notin` T /\ b `notin` T) ->
  (forall a b, In (a, b) ps2 -> a `notin` S2 /\ b `notin` S2) ->
  T [<=] S2 ->
  forall a b, In (a, b) (ps1 ++ ps2) -> a `notin` T /\ b `notin` T.
Proof.
  intros Hav1 Hav2 H2. apply (swaps_dodge_app Hav1 Hav2).
  - reflexivity.
  - exact H2.
Qed.

(** A chain dodging [S] fixes every name inside [S]. *)
Lemma swaps_atom_dodge_in {ps} {S : atoms} {α} :
  (forall a b, In (a, b) ps -> a `notin` S /\ b `notin` S) ->
  α `in` S -> swaps_atom ps α = α.
Proof.
  intros Hav Hα. apply swaps_atom_notin. intros a b Hin.
  destruct (Hav _ _ Hin) as [Ha Hb]. split; intros ->; contradiction.
Qed.

Lemma swaps_atoms_cons_transport : forall α β ps S St S',
  St [=] swap_atoms α β S -> swaps_atoms ps St [=] S' ->
  swaps_atoms ((α, β) :: ps) S [=] S'.
Proof.
  intros * HSt HS. cbn [swaps_atoms]. rewrite <- HS.
  apply swaps_atoms_cong. symmetry; exact HSt.
Qed.

(** The same transport along a chain that runs [ps1] and then [ps2]: the
    shape of every threading row's supply obligation. *)
Lemma swaps_atoms_app_transport {ps1 ps2} {S St S' : atoms} :
  St [=] swaps_atoms ps1 S -> swaps_atoms ps2 St [=] S' ->
  swaps_atoms (ps1 ++ ps2) S [=] S'.
Proof.
  intros HSt HS. rewrite swaps_atoms_app, <- HS.
  apply swaps_atoms_cong. symmetry; exact HSt.
Qed.

(** Two transport steps compose into one along the concatenated chain. *)
Lemma swaps_atoms_app_compose {ps1 ps2} {S S1 S2 : atoms} :
  S2 [=] swaps_atoms ps2 S1 -> S1 [=] swaps_atoms ps1 S ->
  S2 [=] swaps_atoms (ps1 ++ ps2) S.
Proof.
  intros H2 H1. rewrite swaps_atoms_app, H2.
  apply swaps_atoms_cong. exact H1.
Qed.

(** The recursive chain fixes the new opener, so closing commutes with
    prefixing its alignment swap. *)
Lemma swaps_pskl_close_binder : forall α β ps S P Q,
  (forall a b, In (a, b) ps -> a `notin` add β S /\ b `notin` add β S) ->
  swaps_pskl ps (swap_pskl α β P) = Q ->
  swaps_pskl ((α, β) :: ps) (pskl_all_syn (close_pskl_wrt_pskl α P)) =
    pskl_all_syn (close_pskl_wrt_pskl β Q).
Proof.
  intros * Hav HQ.
  assert (Hfix : swaps_atom ps β = β)
    by (apply (swaps_atom_dodge_in Hav); fsetdec).
  cbn [swaps_pskl swap_pskl]. rewrite swap_pskl_close, swap_atom_l.
  rewrite swaps_pskl_all_syn, swaps_pskl_close, Hfix, HQ. reflexivity.
Qed.
