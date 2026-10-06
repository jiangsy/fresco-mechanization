(** ext_algo — DETERMINISM OF THE SOLVE LAYER UP TO FRESH RENAMING
    (campaign §8c.3; the ⛔ yield-mismatch design fork of §8c.6, RESOLVED
    as option (a), 2026-08-15, user decision).

    The cstr fold's tail runs at the RUNNER's yield where the inverted
    derivation's tail sits at the DERIVATION's yield; unlike contexts,
    yields are subjects, so [flex_agree] cannot absorb the mismatch.
    This file supplies the missing metatheory:

    §1  [rel_pskl ρ V P1 P2] — equality up to an aligned fresh-pair list
        ρ, with identity support V.  ⚠️ DELIBERATELY RELATIONAL: one
        derivation may guess the SAME flexible for two holes
        ([a_guess_mono__arrow] runs both halves at Θ), so a functional
        renaming does not exist in general; column uniqueness is paid
        only at the transport.
    §2  The PALINDROMIC swap chain [chain ρ zs] — (a,z) outermost,
        (z,b) innermost, one globally fresh z per pair — realizes the
        relation as an iterated swap ([rel_pskl_chain]), sends the
        left block to the right block entrywise ([chain_flex_pairs]),
        and transports whole fold derivations ([a_solve_cstr_swaps]).
        Swaps are the tree's one renaming primitive (USER DIRECTIVE,
        swap kit); no permutation datatype is introduced.
    §3  [a_guess_mono_det] — guess^TY is deterministic up to renaming.
    §4  [a_solve_eq_det] — the eq-solve is deterministic up to renaming,
        ⭐ HYPOTHESIS-FREE (any two contexts, no agreement, no scoping):
        each derivation's side conditions held for its own context, and
        the eq layer's rule choice is forced by the input shapes — the
        overlaps (SE-Var/SE-FlexR/SE-VacuousR/SE-GuardedGhost on a
        variable subject, the ghost/ghost corners) all produce identical
        outputs ([a_solve_eq_var_subject_inv]).  Size induction on
        [size P + size Q], so BOTH binder rows rebind to a common
        globally fresh opener by plain swaps, and [rel_pskl_close]
        DROPS the opener from the identity support on the way out (no
        strengthening lemma needed).

    The paper implicitly treats the algorithm as a FUNCTION; these
    lemmas are the mechanized justification, and prop_run_complete.v's
    cstr-fold completeness is their first consumer. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.prop_ln.
Require Import src.frost.prop_coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.prop_tag.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.prop_basic.
Require Import src.frost.algo.prop_swap.
Require Import src.frost.algo.sub.prop_solve_sub.
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_look.

Open Scope frost_a_scope.

(* ===================================================================== *)
(*  §1  Equality up to an aligned fresh-pair list                         *)
(*                                                                        *)
(*  [rel_pskl ρ V P1 P2]: P1 and P2 coincide except that a variable may   *)
(*  be replaced along one of ρ's PAIRS; variables outside the pairs must  *)
(*  sit in the identity support [V].  ⚠️ DELIBERATELY RELATIONAL: the     *)
(*  a-side rules allow one derivation to guess the SAME flexible for two  *)
(*  holes ([a_guess_mono__arrow] runs both halves at Θ), so a functional  *)
(*  "renaming" does not exist in general — uniqueness of the columns is   *)
(*  paid only at the TRANSPORT (§2), where the runner-side block is       *)
(*  [uniq] for free and the derivation side hypothesizes it.              *)
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
| rel_pskl__hole : rel_pskl ρ V pskl_hole pskl_hole
| rel_pskl__tophole : forall P Q,
    rel_pskl ρ V P Q ->
    rel_pskl ρ V (pskl_tophole P) (pskl_tophole Q).

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

(** ftv of the two sides, through the relation. *)
Lemma rel_pskl_ftv_l : forall ρ V P1 P2,
  rel_pskl ρ V P1 P2 ->
  ftvar_in_pskl P1 [<=] V ∪ cols_l ρ.
Proof.
  intros * Hrel; induction Hrel; simpl; try fsetdec.
  match goal with
  | Ha : rel_atom _ _ _ _ |- _ =>
      inversion Ha; subst;
      [ match goal with
        | Hin : In _ _ |- _ => apply cols_l_in in Hin; fsetdec
        end
      | fsetdec ]
  end.
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

(** [close] commutes with the relation at an atom the pairs never touch —
    and it DROPS that atom from the identity support: the c-occurrences
    are exactly the ones the close eliminates, so the binder-row dances
    need no strengthening lemma afterwards. *)
Lemma rel_pskl_close_rec : forall ρ V P1 P2 c k,
  rel_pskl ρ (add c V) P1 P2 ->
  c `notin` cols_l ρ -> c `notin` cols_r ρ ->
  rel_pskl ρ V (close_pskl_wrt_pskl_rec k c P1)
               (close_pskl_wrt_pskl_rec k c P2).
Proof.
  intros * Hrel Hcl Hcr.
  remember (add c V) as V' eqn:HV'. revert k.
  induction Hrel; subst; intros k; simpl; try (constructor; auto; fail).
  - (* var_b: both sides shift identically *)
    destruct (lt_ge_dec n k); constructor.
  - (* var_f *)
    match goal with
    | Ha : rel_atom _ _ _ _ |- _ => inversion Ha; subst
    end.
    + (* pair: neither side is c *)
      repeat match goal with
      | |- context [ if ?X then _ else _ ] => destruct X; subst
      end;
      first [ exfalso; apply Hcl; eapply cols_l_in; eassumption
            | exfalso; apply Hcr; eapply cols_r_in; eassumption
            | constructor; apply rel_atom__pair; assumption ].
    + (* id: the same atom on both sides closes in lockstep; a c-use
         becomes bound, any other id-atom survives in the SHRUNK support *)
      repeat match goal with
      | |- context [ if ?X then _ else _ ] => destruct X; subst
      end; constructor;
      match goal with
      | HV : _ `in` add c V |- rel_atom _ _ ?a ?a =>
          apply rel_atom__id;
          match goal with
          | Hne : c <> a |- _ => clear - HV Hne; fsetdec
          end
      end.
Qed.

Lemma rel_pskl_close : forall ρ V P1 P2 c,
  rel_pskl ρ (add c V) P1 P2 ->
  c `notin` cols_l ρ -> c `notin` cols_r ρ ->
  rel_pskl ρ V (close_pskl_wrt_pskl c P1) (close_pskl_wrt_pskl c P2).
Proof.
  intros. unfold close_pskl_wrt_pskl. apply rel_pskl_close_rec; auto.
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

(** The relation preserves size — the §8c.9 pair induction's measure moves
    freely between the two sides. *)
Lemma rel_pskl_size : forall ρ V P1 P2,
  rel_pskl ρ V P1 P2 -> size_pskl P1 = size_pskl P2.
Proof. intros * Hrel; induction Hrel; simpl; lia. Qed.

(** [close] at a PAIR of names — the mirror of [rel_pskl_open_pair]: the
    two sides close their own opener in lockstep, and the pair leaves the
    relation.  The column-freshness side conditions say the pair's atoms
    have no OTHER role in the relation — which is what the rel-transports'
    binder rows (ext_algo/prop_solve_rel.v) supply from the rules' own
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

(* ===================================================================== *)
(*  §2  The transport: a PALINDROMIC swap chain realizes the relation     *)
(*                                                                        *)
(*  [chain ρ zs] routes each pair (a,b) through its own globally fresh    *)
(*  intermediate z — (a,z) outermost, (z,b) innermost — so the second     *)
(*  pass can never disturb an atom the first pass still has to move.      *)
(*  Realization requires the pair columns to be duplicate-free: this is   *)
(*  where the fold pays its [uniq] hypotheses (§1's header).              *)
(* ===================================================================== *)

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

Fixpoint atoms_of (xs : list atom) : atoms :=
  match xs with
  | nil => empty
  | x :: xs' => add x (atoms_of xs')
  end.

Lemma atoms_of_in : forall xs x, In x xs -> x `in` atoms_of xs.
Proof.
  induction xs as [ | a xs IH ]; intros x Hin; simpl in *;
    [ contradiction | ].
  destruct Hin as [-> | Hin]; [ fsetdec | ].
  pose proof (IH _ Hin). fsetdec.
Qed.

Lemma atoms_of_notin : forall xs x, ~ In x xs -> x `notin` atoms_of xs.
Proof.
  induction xs as [ | a xs IH ]; intros x Hn; simpl; [ fsetdec | ].
  assert (Hxa : x <> a) by (intros ->; apply Hn; left; reflexivity).
  assert (Hxs : ~ In x xs) by (intro; apply Hn; right; assumption).
  pose proof (IH _ Hxs). fsetdec.
Qed.

(** A fresh LIST of a prescribed length — the chain's intermediates.
    Nothing in the tree provides one ([atom_fresh] gives a single atom),
    so it is built by iterating [atom_fresh] against the growing
    avoid-set. *)
Lemma atoms_fresh_list : forall n (L : atoms),
  exists zs, length zs = n /\ NoDup zs /\ atoms_of zs ∩ L [=] empty.
Proof.
  induction n as [ | n IH ]; intros L.
  - exists nil. simpl.
    split; [ reflexivity | split; [ constructor | fsetdec ] ].
  - destruct (IH L) as [zs [Hlen [Hnd Hdis]]].
    destruct (atom_fresh (L ∪ atoms_of zs)) as [z Hz].
    exists (z :: zs). simpl.
    split; [ auto | ].
    split.
    + constructor; [ | exact Hnd ].
      intro Hin. apply atoms_of_in in Hin. clear - Hz Hin. fsetdec.
    + clear - Hz Hdis. fsetdec.
Qed.

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

Lemma swaps_pskl_unit : forall ps, swaps_pskl ps pskl_unit = pskl_unit.
Proof. induction ps as [ | [a b] ps IH ]; simpl; auto. Qed.

Lemma swaps_pskl_hole : forall ps, swaps_pskl ps pskl_hole = pskl_hole.
Proof. induction ps as [ | [a b] ps IH ]; simpl; auto. Qed.

Lemma swaps_pskl_var_b : forall ps n,
  swaps_pskl ps (pskl_var_b n) = pskl_var_b n.
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

Lemma swaps_pskl_tophole : forall ps P,
  swaps_pskl ps (pskl_tophole P) = pskl_tophole (swaps_pskl ps P).
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
    upstream in frost/prop_tag.v. *)
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

Lemma swaps_ptyp_unit : forall ps, swaps_ptyp ps ptyp_unit = ptyp_unit.
Proof. induction ps as [ | [a b] ps IH ]; simpl; auto. Qed.

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

(** The chain: (a,z) outermost, (z,b) innermost, one z per pair. *)
Fixpoint chain (ρ : list (atom * atom)) (zs : list atom)
    : list (atom * atom) :=
  match ρ, zs with
  | (a, b) :: ρ', z :: zs' => (a, z) :: (chain ρ' zs' ++ (z, b) :: nil)
  | _, _ => nil
  end.

Lemma chain_atoms : forall (ρ : list (atom * atom)) (zs : list atom) (a b : atom),
  In (a, b) (chain ρ zs) ->
  (a `in` cols_l ρ ∪ atoms_of zs) /\ (b `in` atoms_of zs ∪ cols_r ρ).
Proof.
  induction ρ as [ | [x y] ρ IH ]; intros zs a b Hin; simpl in *;
    [ contradiction | ].
  destruct zs as [ | z zs' ]; simpl in Hin; [ contradiction | ].
  destruct Hin as [E | Hin].
  - inversion E; subst. simpl. split; fsetdec.
  - apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + destruct (IH _ _ _ Hin) as [Ha Hb]. simpl. split; fsetdec.
    + destruct Hin as [E | []]. inversion E; subst. simpl. split; fsetdec.
Qed.

(** The chain's action on an atom the pairs never mention. *)
Lemma chain_image_id : forall ρ zs α,
  α `notin` cols_l ρ ∪ cols_r ρ ∪ atoms_of zs ->
  swaps_atom (chain ρ zs) α = α.
Proof.
  intros * Hav. apply swaps_atom_notin.
  intros a b Hin. destruct (chain_atoms _ _ _ _ Hin) as [Ha Hb].
  split; intros ->; fsetdec.
Qed.

(** The chain's action on the i-th pair's left atom: through its own
    fresh z to the i-th right atom.  Duplicate-freedom of both columns
    is what pins "the i-th". *)
Lemma chain_image_pair : forall (ρ : list (atom * atom)) (zs : list atom) (α β : atom),
  In (α, β) ρ ->
  NoDup (List.map fst ρ) -> NoDup (List.map snd ρ) -> NoDup zs ->
  length zs = length ρ ->
  atoms_of zs ∩ (cols_l ρ ∪ cols_r ρ) [=] empty ->
  swaps_atom (chain ρ zs) α = β.
Proof.
  induction ρ as [ | [x y] ρ IH ]; intros zs α β Hin Hnl Hnr Hnz Hlen Hdis;
    simpl in *; [ contradiction | ].
  destruct zs as [ | z zs' ]; simpl in *; [ discriminate | ].
  apply NoDup_cons_iff in Hnl; destruct Hnl as [Hxl Hnl].
  apply NoDup_cons_iff in Hnr; destruct Hnr as [Hyr Hnr].
  apply NoDup_cons_iff in Hnz; destruct Hnz as [Hzz Hnz].
  pose proof (atoms_of_notin _ _ Hzz) as Hzzs.
  destruct Hin as [E | Hin].
  - (* the head pair: α = x ↦ z, ride the middle untouched, z ↦ β = y *)
    inversion E; subst.
    simpl. rewrite swap_atom_l.
    rewrite swaps_atom_app.
    rewrite (chain_image_id ρ zs' z) by (clear - Hdis Hzzs; fsetdec).
    simpl. rewrite swap_atom_l. reflexivity.
  - (* a later pair: the head swaps are invisible *)
    simpl.
    assert (Hαx : α <> x).
    { intros ->. apply Hxl.
      replace x with (fst (x, β)) by reflexivity.
      apply List.in_map. exact Hin. }
    assert (Hαz : α <> z)
      by (intros ->; pose proof (cols_l_in _ _ _ Hin); clear - Hdis H;
          fsetdec).
    rewrite (swap_atom_other x z α Hαx Hαz).
    rewrite swaps_atom_app.
    rewrite (IH zs' α β Hin Hnl Hnr Hnz ltac:(lia)
               ltac:(clear - Hdis; fsetdec)).
    simpl.
    assert (Hβz : β <> z)
      by (intros ->; pose proof (cols_r_in _ _ _ Hin); clear - Hdis H;
          fsetdec).
    assert (Hβy : β <> y).
    { intros ->. apply Hyr.
      replace y with (snd (α, y)) by reflexivity.
      apply List.in_map. exact Hin. }
    rewrite (swap_atom_other z y β Hβz Hβy). reflexivity.
Qed.

(** ⭐ The realization: the chain's image of the left component IS the
    right component, wherever the relation holds with duplicate-free
    columns and a fresh intermediate list. *)
Lemma rel_pskl_chain : forall ρ V P1 P2 zs,
  rel_pskl ρ V P1 P2 ->
  NoDup (List.map fst ρ) -> NoDup (List.map snd ρ) -> NoDup zs ->
  length zs = length ρ ->
  atoms_of zs ∩ (cols_l ρ ∪ cols_r ρ ∪ V) [=] empty ->
  V ∩ (cols_l ρ ∪ cols_r ρ) [=] empty ->
  swaps_pskl (chain ρ zs) P1 = P2.
Proof.
  intros * Hrel Hnl Hnr Hnz Hlen Hdisz HdisV.
  induction Hrel;
    try (rewrite ?swaps_pskl_unit, ?swaps_pskl_hole, ?swaps_pskl_var_b,
           ?swaps_pskl_arrow, ?swaps_pskl_all_syn, ?swaps_pskl_tophole;
         congruence).
  rewrite swaps_pskl_var_f.
  match goal with
  | Ha : rel_atom _ _ _ _ |- _ => inversion Ha; subst
  end.
  - match goal with
    | Hin : In _ _ |- _ =>
        rewrite (chain_image_pair _ zs _ _ Hin Hnl Hnr Hnz Hlen
                   ltac:(clear - Hdisz; fsetdec))
    end.
    reflexivity.
  - match goal with
    | HV : _ `in` V |- _ =>
        rewrite chain_image_id by (clear - Hdisz HdisV HV; fsetdec)
    end.
    reflexivity.
Qed.

(* --------------------------------------------------------------------- *)
(*  §2b  Block images, the fold-derivation transport, and the             *)
(*       close-rename identity the binder dances re-express closes with   *)
(* --------------------------------------------------------------------- *)

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

(** ⭐ The [uniq] hypotheses of §1's header, converted into the two NoDups
    [chain_image_pair] needs: duplicate-freedom of a block's domain IS
    duplicate-freedom of the corresponding column. *)
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

(** The chain sends the derivation's block to the runner's, entry by
    entry. *)
Lemma chain_flex_pairs : forall ρ0 ρ zs,
  (forall p, In p ρ0 -> In p ρ) ->
  NoDup (List.map fst ρ) -> NoDup (List.map snd ρ) -> NoDup zs ->
  length zs = length ρ ->
  atoms_of zs ∩ (cols_l ρ ∪ cols_r ρ) [=] empty ->
  swaps_aenv (chain ρ zs) (flex_pairs_l ρ0) = flex_pairs_r ρ0.
Proof.
  induction ρ0 as [ | [a b] ρ0 IH ]; intros * Hincl Hnl Hnr Hnz Hlen Hdis;
    simpl; [ apply swaps_aenv_nil | ].
  rewrite swaps_aenv_cons.
  rewrite swaps_abind_flex_mono.
  rewrite (chain_image_pair _ zs a b
             (Hincl _ (or_introl eq_refl)) Hnl Hnr Hnz Hlen Hdis).
  f_equal.
  apply IH; auto. intros p Hp. apply Hincl. right. exact Hp.
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

(** The fold-derivation transport: the single-swap equivariance, folded. *)
Lemma a_solve_cstr_swaps : forall ps Θ C P Ξ Q,
  {{ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}a ->
  {{ (swaps_aenv ps Θ) ⊩ (swaps_cstrs ps C) ⨾ (swaps_pskl ps P)
     ⤳ (swaps_aenv ps Ξ) ⨾ (swaps_pskl ps Q) }}a.
Proof.
  induction ps as [ | [a b] ps IH ]; intros; simpl; auto.
  apply IH. apply a_solve_cstr_swap. assumption.
Qed.

(** Re-expressing a close at a fresh atom: [close b P = close c (swap b c P)]
    whenever c avoids P — the identity every binder-row dance ends on. *)
Lemma close_pskl_rename : forall b c P,
  c `notin` ftvar_in_pskl P ->
  close_pskl_wrt_pskl b P = close_pskl_wrt_pskl c (swap_pskl b c P).
Proof.
  intros * Hc.
  destruct (b == c) as [-> | Hne];
    [ rewrite (swap_pskl_fresh_id c c P) by auto; reflexivity | ].
  pose proof (swap_pskl_close b c b P) as Hsc.
  rewrite swap_atom_l in Hsc.
  rewrite <- Hsc.
  apply eq_sym, swap_pskl_fresh_id;
    rewrite ftvar_in_pskl_close_pskl_wrt_pskl; fsetdec.
Qed.

(* ===================================================================== *)
(*  §3  Determinism of guess^TY up to fresh renaming                      *)
(*                                                                        *)
(*  ⚙ [ptyp_to_pskl_close{,_rec}] used to be re-proved here; they are     *)
(*  conversion facts and moved to frost/prop_coercions.v (2026-08-22),    *)
(*  which is where this header already said they belong.                  *)
(* ===================================================================== *)

(** A guess block binds nothing but undefined flexibles, so its support
    is its domain. *)
Lemma a_guess_mono_block_flex : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A ->
  forall x bd, In (x, bd) Ξ -> bd = abind_flex_mono.
Proof.
  intros Θ P Ξ A H; induction H; intros x bd Hin; simpl in *;
    try contradiction; eauto.
  - destruct Hin as [E | []]. inversion E; subst. reflexivity.
  - apply in_app_or in Hin. destruct Hin; eauto.
Qed.

Lemma flex_env_ftvar : forall (Ξ : aenv),
  (forall x bd, In (x, bd) Ξ -> bd = abind_flex_mono) ->
  ftvar_in_aenv Ξ [<=] dom Ξ.
Proof.
  induction Ξ as [ | [x bd] Ξ IH ]; intros Hflex; simpl; [ fsetdec | ].
  rewrite (Hflex x bd (or_introl eq_refl)). simpl.
  pose proof (IH ltac:(intros; eapply Hflex; right; eassumption)).
  fsetdec.
Qed.

Lemma a_guess_mono_det_n : forall n P, size_pskl P < n ->
  forall Θ1 Θ2 Ξ1 Ξ2 A1 A2,
  a_guess_mono Θ1 P Ξ1 A1 -> a_guess_mono Θ2 P Ξ2 A2 ->
  exists ρ, Ξ1 = flex_pairs_l ρ /\ Ξ2 = flex_pairs_r ρ /\
    forall V, ftvar_in_pskl P [<=] V ->
      rel_pskl ρ V (ptyp_to_pskl A1) (ptyp_to_pskl A2).
Proof.
  induction n as [ | n IHn ]; intros P Hsz * HG1 HG2; [ lia | ].
  destruct P as [ | m | α | P1 P2 | P0 | | P0 ].
  - (* unit *)
    inversion HG1; subst. inversion HG2; subst.
    exists nil. repeat split. intros V _. simpl. constructor.
  - (* var_b — no rule *)
    inversion HG1.
  - (* var_f *)
    inversion HG1; subst. inversion HG2; subst.
    exists nil. repeat split. intros V HV. simpl in HV |- *.
    constructor. apply rel_atom__id. clear - HV. fsetdec.
  - (* arrow *)
    inversion HG1; subst. inversion HG2; subst.
    simpl in Hsz.
    match goal with
    | Ga1 : a_guess_mono Θ1 P1 ?X1 ?B1, Gb1 : a_guess_mono Θ1 P2 ?Y1 ?C1,
      Ga2 : a_guess_mono Θ2 P1 ?X2 ?B2, Gb2 : a_guess_mono Θ2 P2 ?Y2 ?C2
      |- _ =>
        destruct (IHn P1 ltac:(lia) _ _ _ _ _ _ Ga1 Ga2)
          as [ρ1 [E1l [E1r Hrel1]]];
        destruct (IHn P2 ltac:(lia) _ _ _ _ _ _ Gb1 Gb2)
          as [ρ2 [E2l [E2r Hrel2]]]
    end.
    exists (ρ1 ++ ρ2). subst.
    rewrite ! flex_pairs_l_app, ! flex_pairs_r_app.
    repeat split.
    intros V HV. simpl in HV |- *.
    constructor.
    + eapply rel_pskl_mono;
        [ apply (Hrel1 V); clear - HV; fsetdec
        | intros; apply in_or_app; left; assumption
        | clear; fsetdec ].
    + eapply rel_pskl_mono;
        [ apply (Hrel2 V); clear - HV; fsetdec
        | intros; apply in_or_app; right; assumption
        | clear; fsetdec ].
  - (* all_syn — rebind both witnesses to a common fresh opener *)
    inversion HG1; subst. inversion HG2; subst.
    simpl in Hsz.
    match goal with
    | Hf1 : ?b1 `notin` _,
      G1 : a_guess_mono ((?b1 ~ abind_tvar) ++ Θ1) _ Ξ1 ?A1o,
      Hf2 : ?b2 `notin` _,
      G2 : a_guess_mono ((?b2 ~ abind_tvar) ++ Θ2) _ Ξ2 ?A2o |- _ =>
        destruct (atom_fresh (add b1 (add b2 (ftvar_in_pskl P0
                    ∪ ftvar_in_aenv Θ1 ∪ ftvar_in_aenv Θ2
                    ∪ dom Ξ1 ∪ dom Ξ2
                    ∪ ftvar_in_ptyp A1o ∪ ftvar_in_ptyp A2o)))) as [c Hc];
        pose proof (a_guess_mono_swap b1 c _ _ _ _ G1) as G1';
        pose proof (a_guess_mono_swap b2 c _ _ _ _ G2) as G2';
        rewrite swap_pskl_open_var, swap_atom_l in G1', G2';
        rewrite (swap_pskl_fresh_id b1 c P0) in G1'
          by (clear - Hf1 Hc; simpl in *; fsetdec);
        rewrite (swap_pskl_fresh_id b2 c P0) in G2'
          by (clear - Hf2 Hc; simpl in *; fsetdec);
        pose proof (a_guess_mono_block_flex _ _ _ _ G1) as Hbf1;
        pose proof (a_guess_mono_block_flex _ _ _ _ G2) as Hbf2;
        assert (Hb1d : b1 `notin` dom Ξ1)
          by (intro Hin;
              pose proof (a_guess_mono_generated_fresh G1 Hin)
                as Hgf; simpl in Hgf; clear - Hgf; fsetdec);
        assert (Hb2d : b2 `notin` dom Ξ2)
          by (intro Hin;
              pose proof (a_guess_mono_generated_fresh G2 Hin)
                as Hgf; simpl in Hgf; clear - Hgf; fsetdec);
        rewrite (swap_aenv_fresh_id b1 c Ξ1) in G1'
          by (pose proof (flex_env_ftvar _ Hbf1) as Hfe;
              clear - Hb1d Hc Hfe; fsetdec);
        rewrite (swap_aenv_fresh_id b2 c Ξ2) in G2'
          by (pose proof (flex_env_ftvar _ Hbf2) as Hfe;
              clear - Hb2d Hc Hfe; fsetdec);
        destruct (IHn (open_pskl_wrt_pskl P0 (pskl_var_f c))
                    ltac:(rewrite size_pskl_open_pskl_wrt_pskl_var; lia)
                    _ _ _ _ _ _ G1' G2')
          as [ρ [El [Er Hrel]]];
        exists ρ; subst; repeat split;
        intros V HV; simpl in HV |- *;
        rewrite ! ptyp_to_pskl_close;
        rewrite (close_pskl_rename b1 c (ptyp_to_pskl A1o))
          by (pose proof (ftvar_ptyp_to_pskl A1o) as Hft;
              clear - Hc Hft; fsetdec);
        rewrite (close_pskl_rename b2 c (ptyp_to_pskl A2o))
          by (pose proof (ftvar_ptyp_to_pskl A2o) as Hft;
              clear - Hc Hft; fsetdec);
        rewrite ! swap_pskl_ptyp_to_pskl;
        constructor;
        apply rel_pskl_close;
        [ apply Hrel;
          pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0
                        (pskl_var_f c)) as Hup;
          clear - Hup HV; simpl in *; fsetdec
        | rewrite <- dom_flex_pairs_l; clear - Hc; fsetdec
        | rewrite <- dom_flex_pairs_r; clear - Hc; fsetdec ]
    end.
  - (* hole *)
    inversion HG1; subst. inversion HG2; subst.
    match goal with
    | Hn1 : ?a1 `notin` ftvar_in_aenv Θ1,
      Hn2 : ?a2 `notin` ftvar_in_aenv Θ2 |- _ =>
        exists ((a1, a2) :: nil)
    end.
    repeat split. intros V _. simpl.
    constructor. apply rel_atom__pair. left. reflexivity.
  - (* tophole *)
    inversion HG1; subst. inversion HG2; subst.
    simpl in Hsz.
    match goal with
    | G1 : a_guess_mono Θ1 P0 Ξ1 A1, G2 : a_guess_mono Θ2 P0 Ξ2 A2 |- _ =>
        destruct (IHn P0 ltac:(lia) _ _ _ _ _ _ G1 G2)
          as [ρ [El [Er Hrel]]]
    end.
    exists ρ. repeat split; auto.
    (* the ∀V component is closed by [auto]: [ftv ⫯P0] is convertible
       to [ftv P0], so [Hrel] applies directly *)
Qed.

Lemma a_guess_mono_det : forall P Θ1 Θ2 Ξ1 Ξ2 A1 A2,
  a_guess_mono Θ1 P Ξ1 A1 -> a_guess_mono Θ2 P Ξ2 A2 ->
  exists ρ, Ξ1 = flex_pairs_l ρ /\ Ξ2 = flex_pairs_r ρ /\
    forall V, ftvar_in_pskl P [<=] V ->
      rel_pskl ρ V (ptyp_to_pskl A1) (ptyp_to_pskl A2).
Proof.
  intros. eapply a_guess_mono_det_n with (n := S (size_pskl P));
    eauto.
Qed.

(* ===================================================================== *)
(*  §4  Determinism of the eq-solve up to fresh renaming                  *)
(*                                                                        *)
(*  ⭐ HYPOTHESIS-FREE: two derivations on the same inputs, at ANY two    *)
(*  contexts.  No flex-agreement is needed — each derivation's own side   *)
(*  conditions held for its context, and the eq layer's rule choice is    *)
(*  forced by the input shapes (the few overlaps produce identical        *)
(*  outputs).  Size induction on the inputs (every eq rule strictly       *)
(*  shrinks [size P + size Q]), so BOTH derivations' binder rows rebind   *)
(*  to a common globally fresh opener with plain swaps.                   *)
(* ===================================================================== *)

Lemma a_solve_sub_eq_block_flex :
  (forall Θ m P Q Ξ P', {{ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}a ->
     forall x bd, In (x, bd) Ξ -> bd = abind_flex_mono) /\
  (forall Θ P Q Ξ P', {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a ->
     forall x bd, In (x, bd) Ξ -> bd = abind_flex_mono).
Proof.
  apply a_solve_sub_eq_mutind; intros;
    try solve [ match goal with
                | Hin : In _ nil |- _ => inversion Hin
                end
              | eauto
              | match goal with
                | Hin : In _ (_ ++ _) |- _ =>
                    apply in_app_or in Hin; destruct Hin; eauto
                end ].
  (* SE-FlexR — the guess block *)
  eapply a_guess_mono_block_flex; eassumption.
Qed.

Local Ltac det_absurd :=
  solve [ match goal with
          | Hg : nonghost_pskl (pskl_tophole _) |- _ => inversion Hg
          | Hg : nonghost_pskl pskl_hole |- _ => inversion Hg
          | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
          | Hg : guarded_pskl (pskl_tophole _) |- _ => inversion Hg
          | Hg : guarded_pskl pskl_hole |- _ => inversion Hg
          end ].

(** The uniform closer for the overlap crosses: both derivations answered
    with an input (or an input's variable), and no names were invented. *)
Local Ltac det_nil_refl :=
  exists nil; repeat split;
  intros V HV; apply rel_pskl_refl; clear - HV; simpl in *; fsetdec.

(** A variable subject answers itself, whatever the derivation did on
    the way (SE-Var / SE-FlexR-with-a-variable / SE-VacuousR /
    SE-GuardedGhost all agree) — the fact that makes the var-row
    overlaps trivial. *)
Lemma a_solve_eq_var_subject_inv : forall Θ P Q Ξ P',
  {{ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}a ->
  forall α, P = pskl_var_f α ->
  Ξ = nil /\ P' = pskl_var_f α.
Proof.
  intros Θ P Q Ξ P' HD.
  induction HD; intros α0 Heq; try discriminate.
  - (* SE-Var *) inversion Heq; subst. split; reflexivity.
  - (* SE-FlexR — the guess at a variable is the variable *)
    subst.
    match goal with
    | G : a_guess_mono _ (pskl_var_f _) _ _ |- _ => inversion G; subst
    end.
    split; reflexivity.
  - (* SE-VacuousR *) subst. split; reflexivity.
  - (* SE-GuardedGhost *) eauto.
Qed.

Lemma a_solve_eq_det_n : forall n P Q, size_pskl P + size_pskl Q < n ->
  forall Θ1 Θ2 Ξ1 Ξ2 P1' P2',
  {{ Θ1 ⊢ₑ P ∼ Q ⤳ Ξ1 ⨾ P1' }}a ->
  {{ Θ2 ⊢ₑ P ∼ Q ⤳ Ξ2 ⨾ P2' }}a ->
  exists ρ, Ξ1 = flex_pairs_l ρ /\ Ξ2 = flex_pairs_r ρ /\
    forall V, ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] V ->
      rel_pskl ρ V P1' P2'.
Proof.
  induction n as [ | n IHn ]; intros P Q Hsz * HD1 HD2; [ lia | ].
  inversion HD1; subst.
  - (* SE-Unit *)
    inversion HD2; subst; try det_absurd. det_nil_refl.
  - (* SE-Var/FlexL — any derivation on a variable subject answers it *)
    destruct (a_solve_eq_var_subject_inv _ _ _ _ _ HD2 α eq_refl)
      as [-> ->].
    det_nil_refl.
  - (* SE-FlexR vs {var, flex_r} *)
    inversion HD2; subst; try det_absurd.
    + (* the subject is a variable; D1's guess answers it verbatim *)
      match goal with
      | G : a_guess_mono _ (pskl_var_f _) _ _ |- _ => inversion G; subst
      end.
      det_nil_refl.
    + (* flex_r × flex_r — guess determinism *)
      match goal with
      | G1 : a_guess_mono Θ1 ?P0 Ξ1 ?B1, G2 : a_guess_mono Θ2 ?P0 Ξ2 ?B2
        |- _ =>
          destruct (a_guess_mono_det _ _ _ _ _ _ _ G1 G2)
            as [ρ [El [Er Hrel]]]
      end.
      exists ρ. repeat split; [ exact El | exact Er | ].
      intros V HV. apply (Hrel V). clear - HV. fsetdec.
  - (* SE-GhostL vs {hole_l, hole_r} *)
    inversion HD2; subst; try det_absurd; det_nil_refl.
  - (* SE-VacuousR vs {var, hole_l, hole_r} *)
    inversion HD2; subst; try det_absurd; det_nil_refl.
  - (* SE-Arrow × SE-Arrow *)
    inversion HD2; subst; try det_absurd.
    simpl in Hsz.
    match goal with
    | Ga1 : a_solve_eq Θ1 ?Pa ?Qa ?Xa ?Ya,
      Gb1 : a_solve_eq (?Xa ++ Θ1) ?Pb ?Qb ?Xb ?Yb,
      Ga2 : a_solve_eq Θ2 ?Pa ?Qa ?Xc ?Yc,
      Gb2 : a_solve_eq (?Xc ++ Θ2) ?Pb ?Qb ?Xd ?Yd |- _ =>
        destruct (IHn Pa Qa ltac:(simpl; lia) _ _ _ _ _ _ Ga1 Ga2)
          as [ρ1 [E1l [E1r Hrel1]]];
        destruct (IHn Pb Qb ltac:(simpl; lia) _ _ _ _ _ _ Gb1 Gb2)
          as [ρ2 [E2l [E2r Hrel2]]]
    end.
    exists (ρ2 ++ ρ1). subst.
    rewrite ! flex_pairs_l_app, ! flex_pairs_r_app.
    repeat split.
    intros V HV. simpl in HV |- *.
    constructor.
    + eapply rel_pskl_mono;
        [ apply (Hrel1 V); clear - HV; fsetdec
        | intros; apply in_or_app; right; assumption
        | clear; fsetdec ].
    + eapply rel_pskl_mono;
        [ apply (Hrel2 V); clear - HV; fsetdec
        | intros; apply in_or_app; left; assumption
        | clear; fsetdec ].
  - (* SE-Forall × SE-Forall — rebind both premises to a common opener *)
    inversion HD2; subst; try det_absurd.
    simpl in Hsz.
    match goal with
    | Hf1 : ?b1 `notin` _,
      G1 : a_solve_eq ((?b1 ~ abind_tvar) ++ Θ1)
             (open_pskl_wrt_pskl ?P0 (pskl_var_f ?b1))
             (open_pskl_wrt_pskl ?Q0 (pskl_var_f ?b1)) Ξ1 ?Y1,
      Hf2 : ?b2 `notin` _,
      G2 : a_solve_eq ((?b2 ~ abind_tvar) ++ Θ2)
             (open_pskl_wrt_pskl ?P0 (pskl_var_f ?b2))
             (open_pskl_wrt_pskl ?Q0 (pskl_var_f ?b2)) Ξ2 ?Y2 |- _ =>
        destruct (atom_fresh (add b1 (add b2 (ftvar_in_pskl P0
                    ∪ ftvar_in_pskl Q0
                    ∪ ftvar_in_aenv Θ1 ∪ ftvar_in_aenv Θ2
                    ∪ dom Ξ1 ∪ dom Ξ2
                    ∪ ftvar_in_pskl Y1 ∪ ftvar_in_pskl Y2)))) as [c Hc];
        pose proof (proj2 (a_solve_sub_eq_swap b1 c) _ _ _ _ _ G1) as G1';
        pose proof (proj2 (a_solve_sub_eq_swap b2 c) _ _ _ _ _ G2) as G2';
        rewrite ! swap_pskl_open_var in G1', G2';
        rewrite ! swap_atom_l in G1', G2';
        rewrite (swap_pskl_fresh_id b1 c P0) in G1'
          by (clear - Hf1 Hc; fsetdec);
        rewrite (swap_pskl_fresh_id b1 c Q0) in G1'
          by (clear - Hf1 Hc; fsetdec);
        rewrite (swap_pskl_fresh_id b2 c P0) in G2'
          by (clear - Hf2 Hc; fsetdec);
        rewrite (swap_pskl_fresh_id b2 c Q0) in G2'
          by (clear - Hf2 Hc; fsetdec);
        assert (Hbf1 : forall x bd, In (x, bd) Ξ1 -> bd = abind_flex_mono)
          by (intros x bd Hin;
              exact ((proj2 a_solve_sub_eq_block_flex) _ _ _ _ _ G1
                       x bd Hin));
        assert (Hbf2 : forall x bd, In (x, bd) Ξ2 -> bd = abind_flex_mono)
          by (intros x bd Hin;
              exact ((proj2 a_solve_sub_eq_block_flex) _ _ _ _ _ G2
                       x bd Hin));
        assert (Hb1Ξ : b1 `notin` dom Ξ1)
          by (pose proof ((proj2 a_solve_sub_eq_generated_fresh_set)
                            _ _ _ _ _ G1) as Hgf;
              simpl in Hgf; clear - Hgf; fsetdec);
        assert (Hb2Ξ : b2 `notin` dom Ξ2)
          by (pose proof ((proj2 a_solve_sub_eq_generated_fresh_set)
                            _ _ _ _ _ G2) as Hgf;
              simpl in Hgf; clear - Hgf; fsetdec);
        rewrite (swap_aenv_fresh_id b1 c Ξ1) in G1'
          by (pose proof (flex_env_ftvar _ Hbf1) as Hfe;
              clear - Hb1Ξ Hc Hfe; fsetdec);
        rewrite (swap_aenv_fresh_id b2 c Ξ2) in G2'
          by (pose proof (flex_env_ftvar _ Hbf2) as Hfe;
              clear - Hb2Ξ Hc Hfe; fsetdec);
        destruct (IHn (open_pskl_wrt_pskl P0 (pskl_var_f c))
                      (open_pskl_wrt_pskl Q0 (pskl_var_f c))
                    ltac:(rewrite ! size_pskl_open_pskl_wrt_pskl_var;
                          simpl; lia)
                    _ _ _ _ _ _ G1' G2')
          as [ρ [El [Er Hrel]]];
        exists ρ; subst; repeat split;
        intros V HV; simpl in HV |- *;
        rewrite (close_pskl_rename b1 c Y1) by (clear - Hc; fsetdec);
        rewrite (close_pskl_rename b2 c Y2) by (clear - Hc; fsetdec);
        constructor;
        apply rel_pskl_close;
        [ apply Hrel;
          pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0
                        (pskl_var_f c)) as Hu1;
          pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q0
                        (pskl_var_f c)) as Hu2;
          clear - Hu1 Hu2 HV; simpl in *; fsetdec
        | rewrite <- dom_flex_pairs_l; clear - Hc; fsetdec
        | rewrite <- dom_flex_pairs_r; clear - Hc; fsetdec ]
    end.
  - (* SE-UnivGhost × itself *)
    inversion HD2; subst; try det_absurd.
    simpl in Hsz.
    match goal with
    | G1 : a_solve_eq Θ1 ?P0 ?Q0 Ξ1 ?Y1, G2 : a_solve_eq Θ2 ?P0 ?Q0 Ξ2 ?Y2
      |- _ =>
        destruct (IHn P0 Q0 ltac:(simpl; lia) _ _ _ _ _ _ G1 G2)
          as [ρ [El [Er Hrel]]]
    end.
    exists ρ. repeat split; [ exact El | exact Er | ].
    intros V HV. simpl in HV |- *.
    constructor. apply (Hrel V). clear - HV. fsetdec.
  - (* SE-GhostForall × itself — the TARGET opener rebinds *)
    inversion HD2; subst; try det_absurd.
    simpl in Hsz.
    match goal with
    | Hf1 : ?b1 `notin` _,
      G1 : a_solve_eq ((?b1 ~ abind_tvar) ++ Θ1) (pskl_tophole ?P0)
             (open_pskl_wrt_pskl ?Q0 (pskl_var_f ?b1)) Ξ1 ?Y1,
      Hf2 : ?b2 `notin` _,
      G2 : a_solve_eq ((?b2 ~ abind_tvar) ++ Θ2) (pskl_tophole ?P0)
             (open_pskl_wrt_pskl ?Q0 (pskl_var_f ?b2)) Ξ2 ?Y2 |- _ =>
        destruct (atom_fresh (add b1 (add b2 (ftvar_in_pskl P0
                    ∪ ftvar_in_pskl Q0
                    ∪ ftvar_in_aenv Θ1 ∪ ftvar_in_aenv Θ2
                    ∪ dom Ξ1 ∪ dom Ξ2
                    ∪ ftvar_in_pskl Y1 ∪ ftvar_in_pskl Y2)))) as [c Hc];
        pose proof (proj2 (a_solve_sub_eq_swap b1 c) _ _ _ _ _ G1) as G1';
        pose proof (proj2 (a_solve_sub_eq_swap b2 c) _ _ _ _ _ G2) as G2';
        rewrite ! swap_pskl_open_var in G1', G2';
        rewrite ! swap_atom_l in G1', G2';
        rewrite (swap_pskl_fresh_id b1 c (pskl_tophole P0)) in G1'
          by (simpl; clear - Hf1 Hc; fsetdec);
        rewrite (swap_pskl_fresh_id b1 c Q0) in G1'
          by (clear - Hf1 Hc; fsetdec);
        rewrite (swap_pskl_fresh_id b2 c (pskl_tophole P0)) in G2'
          by (simpl; clear - Hf2 Hc; fsetdec);
        rewrite (swap_pskl_fresh_id b2 c Q0) in G2'
          by (clear - Hf2 Hc; fsetdec);
        assert (Hbf1 : forall x bd, In (x, bd) Ξ1 -> bd = abind_flex_mono)
          by (intros x bd Hin;
              exact ((proj2 a_solve_sub_eq_block_flex) _ _ _ _ _ G1
                       x bd Hin));
        assert (Hbf2 : forall x bd, In (x, bd) Ξ2 -> bd = abind_flex_mono)
          by (intros x bd Hin;
              exact ((proj2 a_solve_sub_eq_block_flex) _ _ _ _ _ G2
                       x bd Hin));
        assert (Hb1Ξ : b1 `notin` dom Ξ1)
          by (pose proof ((proj2 a_solve_sub_eq_generated_fresh_set)
                            _ _ _ _ _ G1) as Hgf;
              simpl in Hgf; clear - Hgf; fsetdec);
        assert (Hb2Ξ : b2 `notin` dom Ξ2)
          by (pose proof ((proj2 a_solve_sub_eq_generated_fresh_set)
                            _ _ _ _ _ G2) as Hgf;
              simpl in Hgf; clear - Hgf; fsetdec);
        rewrite (swap_aenv_fresh_id b1 c Ξ1) in G1'
          by (pose proof (flex_env_ftvar _ Hbf1) as Hfe;
              clear - Hb1Ξ Hc Hfe; fsetdec);
        rewrite (swap_aenv_fresh_id b2 c Ξ2) in G2'
          by (pose proof (flex_env_ftvar _ Hbf2) as Hfe;
              clear - Hb2Ξ Hc Hfe; fsetdec);
        destruct (IHn (pskl_tophole P0)
                      (open_pskl_wrt_pskl Q0 (pskl_var_f c))
                    ltac:(rewrite ! size_pskl_open_pskl_wrt_pskl_var;
                          simpl; lia)
                    _ _ _ _ _ _ G1' G2')
          as [ρ [El [Er Hrel]]];
        exists ρ; subst; repeat split;
        intros V HV; simpl in HV |- *;
        rewrite (close_pskl_rename b1 c Y1) by (clear - Hc; fsetdec);
        rewrite (close_pskl_rename b2 c Y2) by (clear - Hc; fsetdec);
        constructor;
        apply rel_pskl_close;
        [ apply Hrel;
          pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q0
                        (pskl_var_f c)) as Hu1;
          clear - Hu1 HV; simpl in *; fsetdec
        | rewrite <- dom_flex_pairs_l; clear - Hc; fsetdec
        | rewrite <- dom_flex_pairs_r; clear - Hc; fsetdec ]
    end.
  - (* SE-GhostGuarded × itself — the subject strips, yields pass *)
    inversion HD2; subst; try det_absurd.
    simpl in Hsz.
    match goal with
    | G1 : a_solve_eq Θ1 ?P0 ?Q0 Ξ1 P1', G2 : a_solve_eq Θ2 ?P0 ?Q0 Ξ2 P2'
      |- _ =>
        destruct (IHn P0 Q0 ltac:(simpl; lia) _ _ _ _ _ _ G1 G2)
          as [ρ [El [Er Hrel]]]
    end.
    exists ρ. repeat split; [ exact El | exact Er | ].
    intros V HV. apply (Hrel V). clear - HV. simpl in *. fsetdec.
  - (* SE-ForallGhost × itself — the SUBJECT opener rebinds *)
    inversion HD2; subst; try det_absurd.
    simpl in Hsz.
    match goal with
    | Hf1 : ?b1 `notin` _,
      G1 : a_solve_eq ((?b1 ~ abind_tvar) ++ Θ1)
             (open_pskl_wrt_pskl ?P0 (pskl_var_f ?b1))
             (pskl_tophole ?Q0) Ξ1 ?Y1,
      Hf2 : ?b2 `notin` _,
      G2 : a_solve_eq ((?b2 ~ abind_tvar) ++ Θ2)
             (open_pskl_wrt_pskl ?P0 (pskl_var_f ?b2))
             (pskl_tophole ?Q0) Ξ2 ?Y2 |- _ =>
        destruct (atom_fresh (add b1 (add b2 (ftvar_in_pskl P0
                    ∪ ftvar_in_pskl Q0
                    ∪ ftvar_in_aenv Θ1 ∪ ftvar_in_aenv Θ2
                    ∪ dom Ξ1 ∪ dom Ξ2
                    ∪ ftvar_in_pskl Y1 ∪ ftvar_in_pskl Y2)))) as [c Hc];
        pose proof (proj2 (a_solve_sub_eq_swap b1 c) _ _ _ _ _ G1) as G1';
        pose proof (proj2 (a_solve_sub_eq_swap b2 c) _ _ _ _ _ G2) as G2';
        rewrite ! swap_pskl_open_var in G1', G2';
        rewrite ! swap_atom_l in G1', G2';
        rewrite (swap_pskl_fresh_id b1 c P0) in G1'
          by (clear - Hf1 Hc; fsetdec);
        rewrite (swap_pskl_fresh_id b1 c (pskl_tophole Q0)) in G1'
          by (simpl; clear - Hf1 Hc; fsetdec);
        rewrite (swap_pskl_fresh_id b2 c P0) in G2'
          by (clear - Hf2 Hc; fsetdec);
        rewrite (swap_pskl_fresh_id b2 c (pskl_tophole Q0)) in G2'
          by (simpl; clear - Hf2 Hc; fsetdec);
        assert (Hbf1 : forall x bd, In (x, bd) Ξ1 -> bd = abind_flex_mono)
          by (intros x bd Hin;
              exact ((proj2 a_solve_sub_eq_block_flex) _ _ _ _ _ G1
                       x bd Hin));
        assert (Hbf2 : forall x bd, In (x, bd) Ξ2 -> bd = abind_flex_mono)
          by (intros x bd Hin;
              exact ((proj2 a_solve_sub_eq_block_flex) _ _ _ _ _ G2
                       x bd Hin));
        assert (Hb1Ξ : b1 `notin` dom Ξ1)
          by (pose proof ((proj2 a_solve_sub_eq_generated_fresh_set)
                            _ _ _ _ _ G1) as Hgf;
              simpl in Hgf; clear - Hgf; fsetdec);
        assert (Hb2Ξ : b2 `notin` dom Ξ2)
          by (pose proof ((proj2 a_solve_sub_eq_generated_fresh_set)
                            _ _ _ _ _ G2) as Hgf;
              simpl in Hgf; clear - Hgf; fsetdec);
        rewrite (swap_aenv_fresh_id b1 c Ξ1) in G1'
          by (pose proof (flex_env_ftvar _ Hbf1) as Hfe;
              clear - Hb1Ξ Hc Hfe; fsetdec);
        rewrite (swap_aenv_fresh_id b2 c Ξ2) in G2'
          by (pose proof (flex_env_ftvar _ Hbf2) as Hfe;
              clear - Hb2Ξ Hc Hfe; fsetdec);
        destruct (IHn (open_pskl_wrt_pskl P0 (pskl_var_f c))
                      (pskl_tophole Q0)
                    ltac:(rewrite ! size_pskl_open_pskl_wrt_pskl_var;
                          simpl; lia)
                    _ _ _ _ _ _ G1' G2')
          as [ρ [El [Er Hrel]]];
        exists ρ; subst; repeat split;
        intros V HV; simpl in HV |- *;
        rewrite (close_pskl_rename b1 c Y1) by (clear - Hc; fsetdec);
        rewrite (close_pskl_rename b2 c Y2) by (clear - Hc; fsetdec);
        constructor;
        apply rel_pskl_close;
        [ apply Hrel;
          pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P0
                        (pskl_var_f c)) as Hu1;
          clear - Hu1 HV; simpl in *; fsetdec
        | rewrite <- dom_flex_pairs_l; clear - Hc; fsetdec
        | rewrite <- dom_flex_pairs_r; clear - Hc; fsetdec ]
    end.
  - (* SE-GuardedGhost vs {var, itself} *)
    inversion HD2; subst; try det_absurd.
    + (* the subject is a variable: D1's premise answers it *)
      match goal with
      | D1p : a_solve_eq Θ1 (pskl_var_f ?av) _ Ξ1 P1' |- _ =>
          destruct (a_solve_eq_var_subject_inv _ _ _ _ _ D1p av eq_refl)
            as [-> ->]
      end.
      det_nil_refl.
    + (* diagonal — the target strips, the yields pass *)
      simpl in Hsz.
      match goal with
      | G1 : a_solve_eq Θ1 ?P0 ?Q0 Ξ1 P1', G2 : a_solve_eq Θ2 ?P0 ?Q0 Ξ2 P2'
        |- _ =>
          destruct (IHn P0 Q0 ltac:(simpl; lia) _ _ _ _ _ _ G1 G2)
            as [ρ [El [Er Hrel]]]
      end.
      exists ρ. repeat split; [ exact El | exact Er | ].
      intros V HV. apply (Hrel V). clear - HV. simpl in *. fsetdec.
Qed.

(** ⭐ Determinism of the eq-solve UP TO FRESH RENAMING — the design
    fork's option (a), hypothesis-free.  The paper implicitly treats the
    algorithm as a function; this is the mechanized justification, and
    the cstr fold's completeness is its first consumer. *)
Lemma a_solve_eq_det : forall P Q Θ1 Θ2 Ξ1 Ξ2 P1' P2',
  {{ Θ1 ⊢ₑ P ∼ Q ⤳ Ξ1 ⨾ P1' }}a ->
  {{ Θ2 ⊢ₑ P ∼ Q ⤳ Ξ2 ⨾ P2' }}a ->
  exists ρ, Ξ1 = flex_pairs_l ρ /\ Ξ2 = flex_pairs_r ρ /\
    forall V, ftvar_in_pskl P ∪ ftvar_in_pskl Q [<=] V ->
      rel_pskl ρ V P1' P2'.
Proof.
  intros.
  eapply a_solve_eq_det_n
    with (n := S (size_pskl P + size_pskl Q)); eauto.
Qed.

Lemma swaps_pskl_ptyp_to_pskl : forall ps A,
  swaps_pskl ps (ptyp_to_pskl A) = ptyp_to_pskl (swaps_ptyp ps A).
Proof.
  induction ps as [ | [a b] ps IH ]; intros; simpl; auto.
  rewrite swap_pskl_ptyp_to_pskl. apply IH.
Qed.
