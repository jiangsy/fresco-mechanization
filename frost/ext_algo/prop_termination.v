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

    ⭐ §3–§6 CARRY THE BOUND THROUGH THE WHOLE EXTRACTION (phase 1b).
    [a_sub__forall_l]'s [P1] comes from [a_extract] = collection → solving
    fold → [guess^N]; §2 bounds only the last stage against ITS input.  §4
    bounds the collection's constraint yield by the COUNTERPART alone (the
    subject is only walked, never deposited), §5 bounds each solving step by
    its subject and its constraint, and §6 composes the three at
    [e_extract__solve], where the fold's seed is [◇]:

        e_extract_nall : nall_pskl Q' <= nall_pskl P'

    — the guessed instantiation has no more ∀s than the INHERITED SKELETON,
    which at the [e_sub__forall_l] call site is [P0].  That is the paper's

        the polytypes we guess are determined by inherited information

    with "inherited information" pinned to a single input, and it is the
    bound the measure charges against [P0].

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
Require Import src.frost.ext_algo.notations.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_guess.
Require Import src.frost.ext_algo.def_look.
Require Import src.frost.ext_algo.def_solve.
Require Import src.frost.ext_algo.def_extract.

Set Implicit Arguments.

Open Scope frost_e_scope.

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

(** The [pskl] twin, for the solving layer's close rows (SS-ForallL,
    SE-Forall, SE-GhostForall, SE-ForallGhost all rebuild their binder). *)
Lemma nall_pskl_close_rec : forall P β k,
  nall_pskl (close_pskl_wrt_pskl_rec k β P) = nall_pskl P.
Proof.
  induction P; intros β k; simpl;
    try reflexivity;
    try (match goal with |- context [ if ?c then _ else _ ] => destruct c end;
         reflexivity);
    first [ solve [ auto ] | f_equal; auto ].
Qed.

Corollary nall_pskl_close : forall P β,
  nall_pskl (close_pskl_wrt_pskl β P) = nall_pskl P.
Proof. intros. apply nall_pskl_close_rec. Qed.

(** Reading a guessed TYPE back into [pskl] preserves the count — [∀] maps to
    [∀-syn], node for node.  ⚙ A conversion fact, named by the house rule
    (<relation>_<conversion>); it lives here rather than in
    [frost/prop_coercions.v] because [nall_*] does — same rationale as
    [ftvar_in_a_cstrs] in def_look.v. *)
Lemma nall_ptyp_to_pskl : forall A,
  nall_pskl (ptyp_to_pskl A) = nall_ptyp A.
Proof. induction A; simpl; lia. Qed.

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
  rewrite nall_ptyp_to_pskl. apply (e_guess_mono_nall Hg).
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

(* ===================================================================== *)
(*  §3  Counting ∀s in a constraint list                                  *)
(*                                                                        *)
(*  The collection deposits skeleton FRAGMENTS of its two inputs into     *)
(*  [C]; the fold then replays them against the accumulated pattern.  So  *)
(*  the count of a constraint list is the ledger the bound moves through. *)
(* ===================================================================== *)

Definition nall_a_cstr (c : a_cstr) : nat :=
  match c with
  | a_cstr_sub _ P => nall_pskl P
  | a_cstr_eq P    => nall_pskl P
  end.

Fixpoint nall_a_cstrs (C : a_cstrs) : nat :=
  match C with
  | nil     => 0
  | c :: C' => nall_a_cstr c + nall_a_cstrs C'
  end.

Lemma nall_a_cstrs_app : forall C1 C2,
  nall_a_cstrs (C1 ++ C2) = nall_a_cstrs C1 + nall_a_cstrs C2.
Proof.
  induction C1 as [ | c C1' IH ]; intros; simpl; [ auto | rewrite IH; lia ].
Qed.

(* ===================================================================== *)
(*  §4  ⭐ EVERY ∀ THE COLLECTION DEPOSITS IS THE COUNTERPART'S            *)
(*                                                                        *)
(*  Sharper than "no ∀ of its own": the constraints are bounded by the    *)
(*  COUNTERPART alone, the subject contributes nothing.  Read the three   *)
(*  depositing rows and the reason is visible — LS-Var and LE-Var         *)
(*  deposit the counterpart standing opposite the looked-up variable,     *)
(*  and LE-FlexR deposits a fresh VARIABLE (∀-free, exactly as            *)
(*  [guess^TY]'s hole row).  The subject is only ever WALKED.             *)
(* ===================================================================== *)

Lemma e_looksub_lookeq_nall :
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
     nall_a_cstrs C <= nall_pskl P') /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
     nall_a_cstrs C <= nall_pskl P').
Proof.
  apply (e_looksub_lookeq_mutind
           (fun S0 Θ α m P P' S1 Ξ C _ => nall_a_cstrs C <= nall_pskl P')
           (fun S0 Θ α P P' S1 Ξ C _ => nall_a_cstrs C <= nall_pskl P'));
    intros; simpl in *;
    repeat rewrite nall_a_cstrs_app;
    repeat rewrite nall_pskl_open in *;
    lia.
Qed.

Corollary e_looksub_nall : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  nall_a_cstrs C <= nall_pskl P'.
Proof. apply e_looksub_lookeq_nall. Qed.

Corollary e_lookeq_nall : forall S0 Θ α P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
  nall_a_cstrs C <= nall_pskl P'.
Proof. apply e_looksub_lookeq_nall. Qed.

(* ===================================================================== *)
(*  §5  ⭐ THE SOLVING LAYER INVENTS NO ∀ EITHER                           *)
(*                                                                        *)
(*  Each step's yield is bounded by its subject plus its constraint.  The *)
(*  one generating row (SE-FlexR) hands the pattern to [guess^TY], which  *)
(*  is where §2's bound is CONSUMED — the theorem below is what the       *)
(*  paper's design principle buys downstream of the guess.                *)
(* ===================================================================== *)

Lemma e_solve_sub_eq_nall :
  (forall S0 Θ m P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
     nall_pskl P' <= nall_pskl P + nall_pskl Q) /\
  (forall S0 Θ P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
     nall_pskl P' <= nall_pskl P + nall_pskl Q).
Proof.
  apply (e_solve_sub_eq_mutind
           (fun S0 Θ m P Q S1 Ξ P' _ =>
              nall_pskl P' <= nall_pskl P + nall_pskl Q)
           (fun S0 Θ P Q S1 Ξ P' _ =>
              nall_pskl P' <= nall_pskl P + nall_pskl Q));
    intros; simpl in *;
    repeat rewrite nall_pskl_close;
    repeat rewrite nall_pskl_open in *;
    try rewrite nall_ptyp_to_pskl;
    (* SE-FlexR: the yield is [guess^TY]'s, so its bound is §2's *)
    try match goal with
        | Hg : e_guess_mono _ _ _ _ _ |- _ =>
            pose proof (e_guess_mono_nall Hg)
        end;
    lia.
Qed.

(** The fold: what comes out is bounded by the constraints plus the seed.
    ⚙ [a_extract] seeds with [◇], so the seed term vanishes there. *)
Lemma e_solve_cstr_nall : forall S0 Θ C P S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}e ->
  nall_pskl Q <= nall_a_cstrs C + nall_pskl P.
Proof.
  intros * H; induction H; simpl in *;
    repeat match goal with
           | Hs : e_solve_sub _ _ _ _ _ _ _ _ |- _ =>
               apply (proj1 e_solve_sub_eq_nall) in Hs
           | He : e_solve_eq _ _ _ _ _ _ _ |- _ =>
               apply (proj2 e_solve_sub_eq_nall) in He
           end;
    lia.
Qed.

(* ===================================================================== *)
(*  §6  ⭐⭐ THE EXTRACTION'S BOUND — phase 1b's deliverable                *)
(*                                                                        *)
(*  Collection, fold and guess composed at [e_extract__solve]: the        *)
(*  instantiation [a_sub__forall_l] recurses on carries no more ∀s than   *)
(*  the INHERITED SKELETON [P'] — the subject does not appear on the      *)
(*  right-hand side at all.  This is the paper's principle,               *)
(*                                                                        *)
(*      we only guess polytypes that can be determined by inherited       *)
(*      type information                     (declarative.tex:856-860)    *)
(*                                                                        *)
(*  as a theorem: "inherited type information" is exactly [P'], and the   *)
(*  ∀ the row consumed is gone for good — what replaces it was paid for   *)
(*  by [P'], which is what the spine measure (the file header) charges.   *)
(* ===================================================================== *)

Theorem e_extract_nall : forall S0 Θ0 NM α m P P' S1 Ξ Q',
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q' }}e ->
  nall_pskl Q' <= nall_pskl P'.
Proof.
  intros * H; destruct H.
  repeat match goal with
         | Hl : e_looksub _ _ _ _ _ _ _ _ _ |- _ =>
             apply e_looksub_nall in Hl
         | Hc : e_solve_cstr _ _ _ _ _ _ _ |- _ =>
             apply e_solve_cstr_nall in Hc
         | Hg : e_guess _ _ _ _ _ _ |- _ =>
             apply e_guess_nall in Hg
         end;
    simpl in *; lia.
Qed.
