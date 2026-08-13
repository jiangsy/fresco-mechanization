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

(* ===================================================================== *)
(*  §7  ⭐⭐ THE HEAD CHAIN — the count [a_sub__forall_l] actually consumes *)
(*                                                                        *)
(*  §8b.2 predicted "count ∀s on the CODOMAIN SPINE".  Working the rows   *)
(*  refines that: a spine count does NOT decrease at [e_sub__forall_l] —  *)
(*  an instantiation CAN put a ∀ on the spine (an eq-constraint hands a   *)
(*  counterpart fragment to the fold wholesale, SE-GhostL).  What is true *)
(*  is sharper, and it is what this section proves:                       *)
(*                                                                        *)
(*    - the count to take is the HEAD ∀/⫯-CHAIN length [hnall]: the ∀s    *)
(*      reachable from the root through ∀ and ⫯ nodes only.  A ∀ below an *)
(*      arrow is charged to the MODE instead — reaching it costs an       *)
(*      [e_sub__arrow] step, which consumes one FN of [M] (the check      *)
(*      rows cannot cross an arrow at all: subject arrow + TC is          *)
(*      [e_sub__check], which leaves for consistency).                    *)
(*    - the instantiation grafts onto the head chain ONLY when the ∀'s    *)
(*      body IS its head chain (∀/⫯ are unary, so a chain ending at the   *)
(*      bound variable is the whole body, §8's [chain_hits]).  In exactly *)
(*      that case the collection deposits at most ONE constraint — a sub  *)
(*      constraint carrying the inherited [P0] — and the ◇-seeded fold    *)
(*      then yields a GUARDED-or-⫯-arrow head (§9), so the graft carries  *)
(*      NO head ∀s.  The hypothesis this needs, [P0] guarded-or-◇, is     *)
(*      [e_sub__forall_l]'s own premise.                                  *)
(*                                                                        *)
(*  Net: hnall(subject) strictly decreases at every [e_sub__forall_l]     *)
(*  ([e_extract_forall_l_hnall], §9) — with [nall P0] (via §6) and the    *)
(*  FN-depth of [M] the remaining lexicographic components.               *)
(* ===================================================================== *)

Fixpoint hnall_ptyp (A : ptyp) : nat :=
  match A with
  | ptyp_all A1 => 1 + hnall_ptyp A1
  | _           => 0
  end.

Fixpoint hnall_pskl (P : pskl) : nat :=
  match P with
  | pskl_all_syn P1 => 1 + hnall_pskl P1
  | pskl_tophole P1 => hnall_pskl P1
  | _               => 0
  end.

(** The head chain is a prefix of the whole tree, so the head count is below
    the total one — which is how §6's [nall] bound reaches [hnall]. *)
Lemma hnall_le_nall_ptyp : forall A, hnall_ptyp A <= nall_ptyp A.
Proof. induction A; simpl; lia. Qed.

Lemma hnall_le_nall_pskl : forall P, hnall_pskl P <= nall_pskl P.
Proof. induction P; simpl; lia. Qed.

Lemma guarded_pskl_hnall : forall P, guarded_pskl P -> hnall_pskl P = 0.
Proof. intros * H; destruct H; reflexivity. Qed.

Lemma hnall_ptyp_to_pskl : forall A,
  hnall_pskl (ptyp_to_pskl A) = hnall_ptyp A.
Proof. induction A; simpl; lia. Qed.

(** Closing at a variable leaves the head chain alone — the chain's tail can
    only move between [var_f] and [var_b], both count 0. *)
Lemma hnall_ptyp_close_rec : forall A β k,
  hnall_ptyp (close_ptyp_wrt_ptyp_rec k β A) = hnall_ptyp A.
Proof.
  induction A; intros β k; simpl;
    try reflexivity;
    try (match goal with |- context [ if ?c then _ else _ ] => destruct c end;
         reflexivity);
    auto.
Qed.

Corollary hnall_ptyp_close : forall A β,
  hnall_ptyp (close_ptyp_wrt_ptyp β A) = hnall_ptyp A.
Proof. intros. apply hnall_ptyp_close_rec. Qed.

(* ===================================================================== *)
(*  §8  Where an opening grafts onto the head chain                       *)
(* ===================================================================== *)

(** [chain_hits_pskl k P]: the ∀/⫯ head chain of [P] ends at the bound
    variable [k] — the index [open_pskl_wrt_pskl_rec k] substitutes.  Because
    ∀ and ⫯ are UNARY, a chain that hits is the WHOLE term: [P] is literally
    [∀…⫯…∀. k], with nothing beside it. *)
Fixpoint chain_hits_pskl (k : nat) (P : pskl) : bool :=
  match P with
  | pskl_var_b j    => Nat.eqb j k
  | pskl_all_syn P1 => chain_hits_pskl (S k) P1
  | pskl_tophole P1 => chain_hits_pskl k P1
  | _               => false
  end.

(** ⭐ THE GRAFT FORMULA.  Opening adds the argument's head count exactly when
    the chain hits the opened index; everywhere else the argument lands off
    the chain and the head count is untouched. *)
Lemma hnall_pskl_open_rec_graft : forall P Q k,
  hnall_pskl (open_pskl_wrt_pskl_rec k Q P)
  = hnall_pskl P + (if chain_hits_pskl k P then hnall_pskl Q else 0).
Proof.
  induction P; intros Q k; simpl;
    try lia;
    (* all / tophole — the chain descends *)
    try (rewrite IHP; destruct (chain_hits_pskl _ P); lia);
    (* var_b — the graft point: the three-way comparison of the opening and
       the boolean of the chain must agree *)
    match goal with
    | |- context [ lt_eq_lt_dec ?j ?k0 ] =>
        destruct (lt_eq_lt_dec j k0) as [[?|?]|?];
        destruct (Nat.eqb_spec j k0); simpl; subst; lia
    end.
Qed.

Corollary hnall_pskl_open_graft : forall P Q,
  hnall_pskl (open_pskl_wrt_pskl P Q)
  = hnall_pskl P + (if chain_hits_pskl 0 P then hnall_pskl Q else 0).
Proof. intros. apply hnall_pskl_open_rec_graft. Qed.

Corollary hnall_pskl_open : forall P β,
  hnall_pskl (open_pskl_wrt_pskl P (pskl_var_f β)) = hnall_pskl P.
Proof.
  intros. rewrite hnall_pskl_open_graft. simpl.
  destruct (chain_hits_pskl 0 P); lia.
Qed.

(** [pure_chain_to α P]: the head chain ends at the FREE variable [α] — the
    shape [chain_hits_pskl] becomes after the opening, and the shape the
    collection lemma of §9 is stated over. *)
Fixpoint pure_chain_to (α : atom) (P : pskl) : Prop :=
  match P with
  | pskl_var_f β    => β = α
  | pskl_all_syn P1 => pure_chain_to α P1
  | pskl_tophole P1 => pure_chain_to α P1
  | _               => False
  end.

(** Opening at a DIFFERENT variable cannot break the chain: the tail [α] is
    free, and the chain's nodes are preserved verbatim. *)
Lemma pure_chain_to_open_rec : forall P α β k,
  pure_chain_to α P ->
  pure_chain_to α (open_pskl_wrt_pskl_rec k (pskl_var_f β) P).
Proof.
  (* [α0]/[β0]: [induction P] manufactures [pskl_var_f]'s ott binder [α] *)
  induction P; intros α0 β0 k Hc; simpl in *; try contradiction; auto.
Qed.

(** A hitting chain, opened at its own index, is a pure chain to the opened
    variable. *)
Lemma chain_hits_open_pure_chain : forall P α k,
  chain_hits_pskl k P = true ->
  pure_chain_to α (open_pskl_wrt_pskl_rec k (pskl_var_f α) P).
Proof.
  (* [α0]: [induction P] manufactures [pskl_var_f]'s ott binder [α] *)
  induction P; intros α0 k Hc; simpl in *; try discriminate; auto.
  match goal with
  | Hc : Nat.eqb ?j ?k0 = true |- _ =>
      destruct (Nat.eqb_spec j k0); [ subst | discriminate ];
      destruct (lt_eq_lt_dec k0 k0) as [[?|?]|?]; simpl; auto; lia
  end.
Qed.

(* ===================================================================== *)
(*  §9  ⭐⭐ THE CRUX: the graft carries NO head ∀                          *)
(*                                                                        *)
(*  Assembled in four steps along the extraction pipeline, each an        *)
(*  inversion or a one-hypothesis induction.                              *)
(* ===================================================================== *)

(** Step 1 — collection at a pure chain deposits AT MOST the one sub
    constraint carrying the counterpart.  The walk never leaves [e_looksub]:
    LS-Check needs a GUARDED subject that is not the variable itself, and a
    pure chain's every node is ∀, ⫯, or [α]; LS-ForallR needs a ∀-headed
    counterpart, excluded by [e_sub__forall_l]'s own guarded-or-◇ premise
    (the chain rows keep the counterpart untouched, so it stays excluded). *)
Lemma e_looksub_pure_chain_cstrs : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  pure_chain_to α P ->
  (guarded_pskl P' \/ P' = pskl_hole) ->
  C = (a_cstr_sub m P' :: nil) \/ C = nil.
Proof.
  intros * H; induction H; intros Hchain Hg; simpl in *;
    try contradiction;
    (* LS-ForallL descends under its binder, so its IH wants the chain fact
       at the OPENED body — [pure_chain_to_open_rec] transports it *)
    eauto using pure_chain_to_open_rec.
  - (* LS-Check: a pure chain's head is ∀, ⫯ or the variable itself — the
       guarded shapes are unit (no chain), a variable (must be [α] by the
       chain, contradicting the row's disequality), and an arrow (no chain) *)
    exfalso.
    match goal with
    | HgA : guarded_pskl ?A, Hne : ?A <> pskl_var_f _ |- _ =>
        destruct HgA; simpl in *; [ contradiction | congruence | contradiction ]
    end.
  - (* LS-ForallR: the counterpart is ∀-headed, excluded by guarded-or-◇ *)
    exfalso. destruct Hg as [ Hg | Hg ]; [ inversion Hg | discriminate ].
Qed.

(** Step 2 — the ◇-seeded solving of a guarded-or-◇ constraint yields a head
    with NO ∀ on it: the yield is ◇ (SS-Vacuous), a ⫯-arrow (SS-GhostLF), or
    a ⫯ over the guarded counterpart (SS-GhostL).  Pure inversion — a ◇
    subject has NO recursive row at all: SS-Check demands a GUARDED subject,
    so not even the drop into the eq layer is reachable, and SS-ForallR's
    ∀-headed counterpart is excluded by the guarded-or-◇ hypothesis. *)
Lemma e_solve_sub_hole_hnall : forall S0 Θ m Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ pskl_hole ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
  (guarded_pskl Q \/ Q = pskl_hole) ->
  hnall_pskl P' = 0.
Proof.
  intros * H Hg; inversion H; subst; simpl in *; try reflexivity;
    (* SS-Check: its subject is required GUARDED, absurd at ◇ *)
    try solve [ match goal with
                | Hga : guarded_pskl pskl_hole |- _ => inversion Hga
                end ];
    (* SS-ForallR: its counterpart is ∀-headed, absurd at guarded-or-◇ *)
    try solve [ exfalso; destruct Hg as [ Hg | Hg ];
                [ inversion Hg | discriminate ] ].
  (* SS-GhostL: the yield is ⫯ over the guarded counterpart *)
  apply guarded_pskl_hnall; assumption.
Qed.

(** Step 3 — [guess^N] never RAISES the head count: the ∀ row rebuilds the
    quantifier the input had ([close] moves the tail between [var_f] and
    [var_b], count 0 either way), the ⫯ row strips a transparent node, and
    the hole row invents a flexible. *)
Lemma e_guess_mono_hnall : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> hnall_ptyp A <= hnall_pskl P.
Proof.
  intros * H; induction H; simpl in *; try lia.
  rewrite hnall_ptyp_close. rewrite hnall_pskl_open in IHe_guess_mono. lia.
Qed.

Lemma e_guess_hnall : forall S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' -> hnall_pskl Q' <= hnall_pskl Q.
Proof.
  intros * H; destruct H as [ | S0 S1 Q0 Ξ0 A Hg ]; [ lia | ].
  rewrite hnall_ptyp_to_pskl. apply (e_guess_mono_hnall Hg).
Qed.

(** Step 4 — composed: an extraction whose subject is a pure chain to the
    looked-up variable, against a guarded-or-◇ counterpart, yields a head
    with NO ∀. *)
Theorem e_extract_pure_chain_hnall : forall S0 Θ0 NM α m P P' S1 Ξ Q',
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q' }}e ->
  pure_chain_to α P ->
  (guarded_pskl P' \/ P' = pskl_hole) ->
  hnall_pskl Q' = 0.
Proof.
  intros * H Hchain Hg; destruct H.
  match goal with
  | Hl : e_looksub _ _ _ _ _ _ _ _ ?C |- _ =>
      destruct (e_looksub_pure_chain_cstrs Hl Hchain Hg); subst C
  end;
  match goal with
  | Hc : e_solve_cstr _ _ _ _ _ _ _ |- _ => inversion Hc; subst
  end;
  match goal with
  | Hgs : e_guess _ _ ?Q _ _ _ |- _ =>
      pose proof (e_guess_hnall Hgs);
      assert (hnall_pskl Q = 0)
        by (solve [ eapply e_solve_sub_hole_hnall; eassumption
                  | reflexivity ]);
      lia
  end.
Qed.

(** ⭐⭐ THE DECREASE THEOREM — [e_sub__forall_l]'s recursion strictly drops
    the subject's head count, stated against the rule's own premises: the
    extraction premise (at the ∀'s body opened at the rule's fresh [α]) and
    the guarded-or-◇ premise on [P0].  Two cases: if the body's chain does
    not reach the bound variable, the instantiation lands off the head chain
    entirely; if it does, the body IS the chain, so the extraction's subject
    is a pure chain to [α] and §9 says the graft carries no head ∀. *)
Theorem e_extract_forall_l_hnall : forall S0 Θ0 NM α M P P0 S1 Ξ P1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ (open_pskl_wrt_pskl P (pskl_var_f α))
     ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ P1 }}e ->
  (guarded_pskl P0 \/ P0 = pskl_hole) ->
  hnall_pskl (open_pskl_wrt_pskl P P1) < hnall_pskl (pskl_all_syn P).
Proof.
  intros * Hx Hg. simpl.
  rewrite hnall_pskl_open_graft.
  destruct (chain_hits_pskl 0 P) eqn:Hhit; [ | lia ].
  pose proof (@chain_hits_open_pure_chain P α 0 Hhit) as Hpure.
  rewrite (e_extract_pure_chain_hnall Hx Hpure Hg).
  lia.
Qed.
