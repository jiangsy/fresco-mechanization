(** ext_algo — TOWARDS THE MEASURE.  §1 of the termination argument.

    ⛔ TERMINATION IS THE ONE OBLIGATION NOBODY HAS DISCHARGED — not the paper
    (docs/HANDOFF-extractable-algo-encoding.md §7.3), not this tree.  It is
    also the only part of TODO (2) that could invalidate the rest: every
    Bove-Capretta runner exists WITHOUT it (§7.1), but none of them is TOTAL
    until it is proved, and decidability — the payoff of the paper's central
    design decision — hangs off totality.

    ⭐ WHAT THIS FILE PROVES, and why it is the right first step.  The paper's
    design principle is

        we never guess polytypes out of thin air; we only guess polytypes
        that can be determined by inherited type information
        (declarative.tex:856-860)

    and that principle is what the measure has to cash.  The row it has to
    cash it AT is [a_sub__forall_l], which instantiates the subject's binder
    at a skeleton [P1] the EXTRACTION produced and recurses on
    [open_pskl_wrt_pskl P P1] — so the subject can GROW, and neither it nor
    the mode visibly shrinks.  If [P1] could carry unbounded ∀-structure the
    walk could cycle; that is exactly the shape behind the undecidability of
    impredicative polymorphic subtyping, which the paper cites as its own
    motivation.

    §2 below proves the principle for [guess^TY], in the two forms a measure
    can use: the guessed type is no BIGGER than the skeleton it was guessed
    from, and it contains no MORE ∀s.  ⭐ Read the [∀] row of the proof and
    the principle is visible as a structural fact: [e_guess_mono__forall]
    rebuilds the [∀] the skeleton already had, and no other row produces one.
    [e_guess_mono__hole] — the only row that INVENTS anything — invents a
    flexible VARIABLE, which is ∀-free.

    ⚙ WHAT IS STILL OWED, precisely, so this file is not mistaken for more
    than it is.  [a_sub__forall_l]'s [P1] comes from [a_extract], which is
    collection -> solving -> [guess^N].  §2 bounds the LAST stage against ITS
    input.  The measure needs the bound against the extraction's input — i.e.
    the same statement carried through the collection and the fold, whose
    own inputs are the mode and the subject.  That is the next lemma, and it
    is the one that turns

        the polytypes we guess are determined by inherited information

    into a bound the recursion can decrease on.

    ⚙ AND THE SECOND HALF OF THE ARGUMENT IS NOT A SIZE BOUND AT ALL (user,
    2026-08-13): after an instantiation the walk falls back to CONSISTENCY at
    every position except the final contravariance — [a_sub__arrow] sends its
    DOMAIN to consistency and keeps only the CODOMAIN in [a_sub]
    (frost/algo/def_rules.v; the reference implementation does the same,
    benchmark/Fresco/lib/type.ml SI-Arrow).  So [a_sub] walks the arrow SPINE
    and nothing else, and a ∀ that an instantiation drops into a domain
    position can never fire [a_sub__forall_l] again.  A measure that counts
    ∀s ON THE SPINE is therefore the shape to try, and §2's bound is what
    keeps the spine's supply of ∀s finite. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_guess.

Set Implicit Arguments.

(* ===================================================================== *)
(*  §1  Counting ∀s                                                       *)
(*                                                                        *)
(*  [size_*] already exists (lngen, frost/prop_ln.v).  The ∀-COUNT does    *)
(*  not, and it is the sharper of the two: §7.3 predicts that what         *)
(*  decreases along a run is SKELETON structure — the ghosts and tagged    *)
(*  ∀s the skeleton supplies get consumed — and that a measure led by a    *)
(*  type SIZE is looking in the wrong place.                               *)
(* ===================================================================== *)

Fixpoint nall_ptyp (A : ptyp) : nat :=
  match A with
  | ptyp_arrow A1 A2 => nall_ptyp A1 + nall_ptyp A2
  | ptyp_all A1      => 1 + nall_ptyp A1
  | _                => 0
  end.

Fixpoint nall_pskl (P : pskl) : nat :=
  match P with
  | pskl_arrow P1 P2 => nall_pskl P1 + nall_pskl P2
  | pskl_all_syn P1  => 1 + nall_pskl P1
  | pskl_tophole P1  => nall_pskl P1
  | _                => 0
  end.

(** Opening at a VARIABLE cannot change the ∀-count — the substituted term is
    a variable, which has none.  ⚙ Proved over the [_rec] form because that is
    what [open_pskl_wrt_pskl] unfolds to. *)
(* ⚠️ The index is [k], not [n]: ott names [pskl_var_b]'s argument [n], so
   [induction P] manufactures that name and an [intros … n] then fails with
   "n is already used" (CLAUDE.md's rule-binder trap). *)
Lemma nall_pskl_open_rec : forall P β k,
  nall_pskl (open_pskl_wrt_pskl_rec k (pskl_var_f β) P) = nall_pskl P.
Proof.
  (* ⚙ The rows are closed by SHAPE rather than by naming the IHs: [induction]
     freshens them against the statement's own [A]/[P], so spelling them is a
     rename away from breaking. *)
  induction P; intros β k; simpl;
    try reflexivity;
    (* var_b — the one row that can actually substitute, and it lands on a
       variable, whose count is 0 *)
    try (match goal with
         | |- context [ lt_eq_lt_dec ?a ?b ] =>
             destruct (lt_eq_lt_dec a b) as [[?|?]|?]
         end; reflexivity);
    (* ⚠️ [solve [auto]] FIRST: the pass-through row ([tophole]) has the shape
       [nall (open … P) = nall P], where a bare [f_equal] strips [nall] from
       both sides and leaves the FALSE goal [open … P = P]. *)
    first [ solve [ auto ] | f_equal; auto ].
Qed.

Corollary nall_pskl_open : forall P β,
  nall_pskl (open_pskl_wrt_pskl P (pskl_var_f β)) = nall_pskl P.
Proof. intros. apply nall_pskl_open_rec. Qed.

(** Closing cannot change it either — it replaces a free variable by a bound
    index, and both have count 0. *)
Lemma nall_ptyp_close_rec : forall A β k,
  nall_ptyp (close_ptyp_wrt_ptyp_rec k β A) = nall_ptyp A.
Proof.
  induction A; intros β k; simpl;
    try reflexivity;
    (* var_f — closing lands on a bound index, count 0 either way *)
    try (match goal with |- context [ if ?c then _ else _ ] => destruct c end;
         reflexivity);
    first [ solve [ auto ] | f_equal; auto ].
Qed.

Corollary nall_ptyp_close : forall A β,
  nall_ptyp (close_ptyp_wrt_ptyp β A) = nall_ptyp A.
Proof. intros. apply nall_ptyp_close_rec. Qed.

(* ===================================================================== *)
(*  §2  ⭐ [guess^TY] NEVER GUESSES A POLYTYPE OUT OF THIN AIR             *)
(*                                                                        *)
(*  The paper's design principle, as two theorems.  Both are               *)
(*  HYPOTHESIS-FREE: they hold of the relation, not of a well-formed run.  *)
(* ===================================================================== *)

(** ⭐ THE ∀ BOUND — the load-bearing one.  Every ∀ in the guessed type was
    already in the skeleton.  ⚙ The proof is four trivial rows, one
    congruence, and the [∀] row, where [e_guess_mono__forall] REBUILDS the
    quantifier the skeleton had: [close] does not change the count and
    neither does the [open] on the other side, so the inequality is an
    equality-in-disguise there. *)
Lemma e_guess_mono_nall : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> nall_ptyp A <= nall_pskl P.
Proof.
  intros * H;
    induction H as [ S α Hα | S0 S1 P Ξ A H IH | S α | S
                   | S0 S1 S2 P Q Ξ1 Ξ2 A B H1 IH1 H2 IH2
                   | S0 S1 P Ξ A β Hβ H IH ];
    simpl in *; try lia.
  (* ∀ : the quantifier is COPIED, not invented *)
  rewrite nall_ptyp_close. rewrite nall_pskl_open in IH. lia.
Qed.

(** The size bound, for a measure that wants one.  ⚙ Weaker than the ∀ bound
    in the sense that matters (a run can be big and ∀-free), but it is what
    rules out the guess blowing the subject up at all. *)
Lemma e_guess_mono_size : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> size_ptyp A <= size_pskl P.
Proof.
  intros * H;
    induction H as [ S α Hα | S0 S1 P Ξ A H IH | S α | S
                   | S0 S1 S2 P Q Ξ1 Ξ2 A B H1 IH1 H2 IH2
                   | S0 S1 P Ξ A β Hβ H IH ];
    simpl in *; try lia.
  rewrite size_ptyp_close_ptyp_wrt_ptyp.
  rewrite size_pskl_open_pskl_wrt_pskl_var in IH. lia.
Qed.

(** The sort wrapper inherits both, since [guess^SK] is the identity. *)
Lemma e_guess_nall : forall S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' -> nall_pskl Q' <= nall_pskl Q.
Proof.
  intros * H; destruct H as [ | S0 S1 Q0 Ξ0 A Hg ]; [ lia | ].
  (* reading the guessed TYPE back into [pskl] preserves the count *)
  pose proof (e_guess_mono_nall Hg) as Hb.
  assert (Heq : nall_pskl (ptyp_to_pskl A) = nall_ptyp A)
    by (clear; induction A; simpl; lia).
  lia.
Qed.

(** ⭐ AND THE COROLLARY THE MEASURE WILL QUOTE: a ∀-free skeleton is guessed
    at a ∀-free type.  This is the case [a_sub__forall_l] needs to stay in,
    because an instantiation with no ∀ makes the subject's ∀-count strictly
    DROP across the row — the outer quantifier is consumed and nothing
    replaces it. *)
Corollary e_guess_mono_nall_free : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> nall_pskl P = 0 -> nall_ptyp A = 0.
Proof.
  intros * H Hz. pose proof (e_guess_mono_nall H). lia.
Qed.
