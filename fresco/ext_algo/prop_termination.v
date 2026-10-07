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
    (fresco/algo/def_rules.v; the reference implementation does the same,
    benchmark/Fresco/lib/type.ml SI-Arrow).  So [a_sub] walks the arrow SPINE
    and nothing else, and a ∀ that an instantiation drops into a domain
    position can never fire [a_sub__forall_l] again.  A measure that counts
    ∀s ON THE SPINE is therefore the shape to try, and §2's bound is what
    keeps the spine's supply of ∀s finite. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Wf_nat.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.algo.prop_metasubst.
Require Import src.fresco.algo.sub.prop_solve_sub.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_guess.
Require Import src.fresco.ext_algo.def_guess_impl.
Require Import src.fresco.ext_algo.def_consis.
Require Import src.fresco.ext_algo.def_look.
Require Import src.fresco.ext_algo.def_solve.
Require Import src.fresco.ext_algo.def_extract.
Require Import src.fresco.ext_algo.def_order.

Set Implicit Arguments.

Open Scope fresco_e_scope.

(* ===================================================================== *)
(*  §1  Counting ∀s                                                       *)
(*                                                                        *)
(*  [size_*] already exists (lngen, fresco/prop_ln.v).  The ∀-COUNT does    *)
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
    [fresco/prop_coercions.v] because [nall_*] does — same rationale as
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

(** ⭐ AND THE COROLLARY THE MEASURE WILL QUOTE: a ∀-free skeleton is guessed
    at a ∀-free type.  This is the case [a_sub__forall_l] needs to stay in,
    because an instantiation with no ∀ makes the subject's ∀-count strictly
    DROP across the row — the outer quantifier is consumed and nothing
    replaces it. *)

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

(* ===================================================================== *)
(*  §10  Local closure through the pipeline                               *)
(*                                                                        *)
(*  Needed by §11's totality lemmas for exactly one reason: [guess^TY]'s  *)
(*  domain predicate has no row for a dangling index (def_guess_impl.v),  *)
(*  so wherever a runner may GUESS — SE-FlexR on the accumulated pattern, *)
(*  and [guess^N] on the fold's yield — the input must be known locally   *)
(*  closed.  Mirrors [a_solve_sub_eq_lc] (algo/sub/prop_solve_sub.v),     *)
(*  whose kit this section imports rather than recreates.                 *)
(* ===================================================================== *)

Lemma e_guess_mono_lc : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> lc_ptyp A.
Proof.
  intros * H; induction H;
    try solve [ assumption | constructor; auto ].
  (* ∀ : the rule's OWN witness serves — close/open round trip *)
  match goal with
  | |- lc_ptyp (ptyp_all (close_ptyp_wrt_ptyp ?b _)) =>
      apply (lc_ptyp_all_exists b);
      rewrite open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp; assumption
  end.
Qed.

Corollary e_guess_mono_lc_pskl : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> lc_pskl (ptyp_to_pskl A).
Proof. intros. apply ptyp_to_pskl_lc. eauto using e_guess_mono_lc. Qed.

(** The constraints a collection deposits are locally closed — they are
    counterpart fragments, opened only at variables, or fresh variables. *)
Definition lc_a_cstr (c : a_cstr) : Prop :=
  match c with
  | a_cstr_sub _ P => lc_pskl P
  | a_cstr_eq P    => lc_pskl P
  end.

Lemma e_looksub_lookeq_cstrs_lc :
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
     lc_pskl P -> lc_pskl P' -> Forall lc_a_cstr C) /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e ->
     lc_pskl P -> lc_pskl P' -> Forall lc_a_cstr C).
Proof.
  apply (e_looksub_lookeq_mutind
           (fun S0 Θ α m P P' S1 Ξ C _ =>
              lc_pskl P -> lc_pskl P' -> Forall lc_a_cstr C)
           (fun S0 Θ α P P' S1 Ξ C _ =>
              lc_pskl P -> lc_pskl P' -> Forall lc_a_cstr C));
    intros;
    repeat match goal with
    | H : lc_pskl (pskl_arrow _ _) |- _ =>
        apply lc_pskl_arrow_inv in H; destruct H
    | H : lc_pskl (pskl_tophole _) |- _ => apply lc_pskl_tophole_inv in H
    end;
    (* deposits and empty lists *)
    try solve [ repeat (constructor; simpl; auto) ];
    (* the two arrow rows *)
    try solve [ rewrite Forall_app; split;
                eauto using lc_pskl_all_syn_inv, lc_pskl_tophole ];
    (* structural descents, re-wrapping what the saturation unpacked *)
    try solve [ eauto using lc_pskl_all_syn_inv, lc_pskl_tophole ].
Qed.

Corollary e_looksub_cstrs_lc : forall S0 Θ α m P P' S1 Ξ C,
  {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e ->
  lc_pskl P -> lc_pskl P' -> Forall lc_a_cstr C.
Proof. intros. eapply (proj1 e_looksub_lookeq_cstrs_lc); eassumption. Qed.

(** Solving preserves local closure — the e-side mirror of
    [a_solve_sub_eq_lc], row for row. *)
Lemma e_solve_sub_eq_lc :
  (forall S0 Θ m P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
     lc_pskl P -> lc_pskl Q -> lc_pskl P') /\
  (forall S0 Θ P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
     lc_pskl P -> lc_pskl Q -> lc_pskl P').
Proof.
  apply (e_solve_sub_eq_mutind
           (fun S0 Θ m P Q S1 Ξ P' _ => lc_pskl P -> lc_pskl Q -> lc_pskl P')
           (fun S0 Θ P Q S1 Ξ P' _ => lc_pskl P -> lc_pskl Q -> lc_pskl P'));
    intros;
    (* SE-FlexR's output is [guess^TY]'s *)
    try solve [ eapply e_guess_mono_lc_pskl; eassumption ];
    repeat match goal with
    | H : lc_pskl (pskl_arrow _ _) |- _ =>
        apply lc_pskl_arrow_inv in H; destruct H
    | H : lc_pskl (pskl_tophole _) |- _ => apply lc_pskl_tophole_inv in H
    | H : guarded_pskl _           |- _ => apply guarded_pskl_lc in H
    end;
    try solve
      [ assumption
      | eauto
      | constructor; eauto
      | apply lc_pskl_tophole; eauto
      | apply lc_pskl_tophole; constructor; eauto ];
    (* binder rows — the rule's own witness serves via the close/open
       round trip, exactly as in the a-side proof *)
    try match goal with
    | |- lc_pskl (pskl_all_syn (close_pskl_wrt_pskl ?b _)) =>
        apply (lc_pskl_all_syn_exists b);
        rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl
    end;
    match goal with
    | IH : lc_pskl _ -> lc_pskl _ -> lc_pskl _ |- _ =>
        apply IH;
        eauto using lc_pskl_all_syn_inv, lc_pskl_tophole
    end.
Qed.

Corollary e_solve_sub_lc : forall S0 Θ m P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e ->
  lc_pskl P -> lc_pskl Q -> lc_pskl P'.
Proof. intros. eapply (proj1 e_solve_sub_eq_lc); eassumption. Qed.

Corollary e_solve_eq_lc : forall S0 Θ P Q S1 Ξ P',
  {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e ->
  lc_pskl P -> lc_pskl Q -> lc_pskl P'.
Proof. intros. eapply (proj2 e_solve_sub_eq_lc); eassumption. Qed.

(** The fold's yield is locally closed when the seed and every payload are. *)
Lemma e_solve_cstr_lc : forall S0 Θ C P S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}e ->
  lc_pskl P -> Forall lc_a_cstr C -> lc_pskl Q.
Proof.
  intros * H; induction H; intros Hlc HC;
    try match goal with
        | HC0 : Forall lc_a_cstr (_ :: _) |- _ =>
            inversion HC0; subst; simpl in *
        end;
    eauto using e_solve_sub_lc, e_solve_eq_lc.
Qed.

(* ===================================================================== *)
(*  §11  ⭐ TOTALITY OF THE ROUTINE ORDERS                                 *)
(*                                                                        *)
(*  The collection is total UNCONDITIONALLY — it never guesses, so not    *)
(*  even local closure is needed (a dangling index just fires no row,     *)
(*  and the one-constructor orders cover it vacuously).  The solving      *)
(*  layer guesses at SE-FlexR, so its totality carries the subject's      *)
(*  local closure; the fold and the extraction inherit the condition      *)
(*  through §10's preservation lemmas.  Every measure here is the plain   *)
(*  size sum: the sub→eq drops (LS-Check, SS-Check) go to a judgement     *)
(*  whose totality is already established, so no lexicographic component  *)
(*  is needed in the mechanization even where the informal measure says   *)
(*  "eq before sub".                                                      *)
(* ===================================================================== *)

Lemma e_lookeq_order_total_n : forall n S0 Θ α P P',
  size_pskl P + size_pskl P' <= n ->
  e_lookeq_order S0 Θ α P P'.
Proof.
  induction n; intros * Hsz;
    [ pose proof (size_pskl_min P); pose proof (size_pskl_min P'); lia | ].
  constructor; intros; subst; simpl in Hsz;
    repeat match goal with |- _ /\ _ => split end; intros;
    apply IHn; repeat rewrite size_pskl_open_pskl_wrt_pskl_var; simpl; lia.
Qed.

Theorem e_lookeq_order_total : forall S0 Θ α P P',
  e_lookeq_order S0 Θ α P P'.
Proof. intros. eapply e_lookeq_order_total_n. apply le_n. Qed.

Lemma e_looksub_order_total_n : forall n S0 Θ α m P P',
  size_pskl P + size_pskl P' <= n ->
  e_looksub_order S0 Θ α m P P'.
Proof.
  induction n; intros * Hsz;
    [ pose proof (size_pskl_min P); pose proof (size_pskl_min P'); lia | ].
  constructor; intros; subst; simpl in Hsz;
    repeat match goal with |- _ /\ _ => split end; intros;
    try apply e_lookeq_order_total;
    apply IHn; repeat rewrite size_pskl_open_pskl_wrt_pskl_var; simpl; lia.
Qed.

Theorem e_looksub_order_total : forall S0 Θ α m P P',
  e_looksub_order S0 Θ α m P P'.
Proof. intros. eapply e_looksub_order_total_n. apply le_n. Qed.

Lemma e_solve_eq_order_total_n : forall n S0 Θ P Q,
  size_pskl P + size_pskl Q <= n ->
  lc_pskl P ->
  e_solve_eq_order S0 Θ P Q.
Proof.
  induction n; intros * Hsz Hlc;
    [ pose proof (size_pskl_min P); pose proof (size_pskl_min Q); lia | ].
  constructor; intros; subst; simpl in Hsz;
    (* SE-FlexR — the guess on the CURRENT subject, before the saturation
       below unpacks its local closure *)
    try solve [ apply e_guess_mono_order_total; assumption ];
    repeat match goal with
    | H : lc_pskl (pskl_arrow _ _) |- _ =>
        apply lc_pskl_arrow_inv in H; destruct H
    | H : lc_pskl (pskl_tophole _) |- _ => apply lc_pskl_tophole_inv in H
    end;
    repeat match goal with |- _ /\ _ => split end; intros;
    (apply IHn;
     [ repeat rewrite size_pskl_open_pskl_wrt_pskl_var; simpl; lia
     | eauto using lc_pskl_all_syn_inv, lc_pskl_tophole ]).
Qed.

Theorem e_solve_eq_order_total : forall S0 Θ P Q,
  lc_pskl P -> e_solve_eq_order S0 Θ P Q.
Proof. intros. eapply e_solve_eq_order_total_n; [ apply le_n | assumption ]. Qed.

Lemma e_solve_sub_order_total_n : forall n S0 Θ m P Q,
  size_pskl P + size_pskl Q <= n ->
  lc_pskl P ->
  e_solve_sub_order S0 Θ m P Q.
Proof.
  induction n; intros * Hsz Hlc;
    [ pose proof (size_pskl_min P); pose proof (size_pskl_min Q); lia | ].
  constructor; intros; subst; simpl in Hsz;
    (* SS-Check — the drop into the eq layer, whose totality stands *)
    try solve [ apply e_solve_eq_order_total; assumption ];
    repeat match goal with
    | H : lc_pskl (pskl_arrow _ _) |- _ =>
        apply lc_pskl_arrow_inv in H; destruct H
    | H : lc_pskl (pskl_tophole _) |- _ => apply lc_pskl_tophole_inv in H
    end;
    repeat match goal with |- _ /\ _ => split end; intros;
    (* the arrow rows' eq half *)
    try solve [ apply e_solve_eq_order_total;
                solve [ assumption | constructor ] ];
    (apply IHn;
     [ repeat rewrite size_pskl_open_pskl_wrt_pskl_var; simpl; lia
     | eauto using lc_pskl_all_syn_inv, lc_pskl_tophole;
       try solve [ constructor ] ]).
Qed.

Theorem e_solve_sub_order_total : forall S0 Θ m P Q,
  lc_pskl P -> e_solve_sub_order S0 Θ m P Q.
Proof. intros. eapply e_solve_sub_order_total_n; [ apply le_n | assumption ]. Qed.

Theorem e_solve_cstr_order_total : forall C S0 Θ P,
  lc_pskl P -> Forall lc_a_cstr C -> e_solve_cstr_order S0 Θ C P.
Proof.
  induction C as [ | c C' IH ]; intros * Hlc HC; constructor; intros;
    match goal with
    | Heq : nil = _ :: _ |- _ => discriminate Heq
    | Heq : _ :: _ = _ :: _ |- _ =>
        inversion Heq; subst; inversion HC; subst; simpl in *
    end.
  - (* the singleton sub constraint *)
    apply e_solve_sub_order_total; assumption.
  - (* an eq constraint, then the tail at the yield *)
    split; [ apply e_solve_eq_order_total; assumption | intros ].
    apply IH; [ eapply e_solve_eq_lc; eauto | assumption ].
Qed.

Theorem e_guess_order_total : forall S0 NM Q,
  lc_pskl Q -> e_guess_order S0 NM Q.
Proof.
  intros; constructor; intros _; apply e_guess_mono_order_total; assumption.
Qed.

(** ⭐ The extraction is total at locally-closed inputs — every stage of
    [e_sub__forall_l]'s instantiation pipeline terminates. *)
Theorem e_extract_order_total : forall S0 Θ0 NM α m P P',
  lc_pskl P -> lc_pskl P' -> e_extract_order S0 Θ0 NM α m P P'.
Proof.
  intros; constructor.
  - apply e_looksub_order_total.
  - intros. apply e_solve_cstr_order_total;
      [ constructor | eapply e_looksub_cstrs_lc; eassumption ].
  - intros. apply e_guess_order_total.
    eapply e_solve_cstr_lc;
      [ eassumption | constructor | eapply e_looksub_cstrs_lc; eassumption ].
Qed.

(* ===================================================================== *)
(*  §12  The remaining measure components, and their stability            *)
(*                                                                        *)
(*  The lexicographic measure of the subtyping walk (§13) is              *)
(*                                                                        *)
(*    ( fnd_mode M , nall P0 , hnall P , ndef Θ , size P , |Θ|-walk )     *)
(*                                                                        *)
(*  This section defines the two components not yet on file and proves    *)
(*  what each recursive edge needs: mono-substitution moves neither ∀     *)
(*  count (Flex-Assign), a generated block holds no defined flexible      *)
(*  (ForallL's context growth is ndef-neutral), and the consistency       *)
(*  block preserves the def-payloads-are-mono discipline (the Arrow row   *)
(*  runs its codomain at the domain's OUTPUT context).                    *)
(* ===================================================================== *)

Fixpoint fnd_mode (M : mode) : nat :=
  match M with
  | mode_fn M' => 1 + fnd_mode M'
  | _          => 0
  end.

Fixpoint ndef_aenv (Θ : aenv) : nat :=
  match Θ with
  | nil                                => 0
  | (_, abind_flex_mono_def _) :: Θ'   => 1 + ndef_aenv Θ'
  | _ :: Θ'                            => ndef_aenv Θ'
  end.

Lemma ndef_aenv_app : forall Θ1 Θ2,
  ndef_aenv (Θ1 ++ Θ2) = ndef_aenv Θ1 + ndef_aenv Θ2.
Proof.
  induction Θ1 as [ | [x b] Θ1' IH ]; intros; simpl; [ auto | ].
  destruct b; rewrite IH; lia.
Qed.

(** Def payloads are monotypes — the context discipline the measure rides
    on: it is what keeps Flex-Assign's substitution ∀-free.  [aenv] entries
    other than a defined flexible carry no payload obligation. *)
Definition entry_def_mono (xb : atom * abind) : Prop :=
  match snd xb with
  | abind_flex_mono_def τ => mono_ptyp τ
  | _                     => True
  end.

Notation aenv_defs_mono := (Forall entry_def_mono).

Lemma entry_def_mono_flex : forall α, entry_def_mono (α, abind_flex_mono).
Proof. intros; exact I. Qed.

Lemma entry_def_mono_tvar : forall α, entry_def_mono (α, abind_tvar).
Proof. intros; exact I. Qed.

Lemma entry_def_mono_var_typ : forall x A, entry_def_mono (x, abind_var_typ A).
Proof. intros; exact I. Qed.

Lemma entry_def_mono_var_skl : forall x Q, entry_def_mono (x, abind_var_skl Q).
Proof. intros; exact I. Qed.

Lemma entry_def_mono_def : forall α τ,
  mono_ptyp τ -> entry_def_mono (α, abind_flex_mono_def τ).
Proof. intros; exact H. Qed.

(** The head inversion, stated at the [(x ~ b) ++ Θ] spelling the rules
    use rather than at [::], so a walk row can read off both halves
    without an [unfold one] first. *)
Lemma aenv_defs_mono_cons_inv : forall x b (Θ : aenv),
  aenv_defs_mono ((x ~ b) ++ Θ) ->
  entry_def_mono (x, b) /\ aenv_defs_mono Θ.
Proof. intros * HF. inversion HF; subst. split; assumption. Qed.

Lemma Forall_app_intro : forall (X : Type) (Pr : X -> Prop) l1 l2,
  Forall Pr l1 -> Forall Pr l2 -> Forall Pr (l1 ++ l2).
Proof. intros; apply Forall_app; split; assumption. Qed.

(** A flex-only block ([all_flex_mono], algo/prop_metasubst.v) counts no
    defined flexible and trivially satisfies the payload discipline. *)
Lemma all_flex_mono_ndef : forall Ξ, all_flex_mono Ξ -> ndef_aenv Ξ = 0.
Proof.
  unfold all_flex_mono; induction 1 as [ | [x b] Ξ' Hb _ IH ];
    simpl in *; subst; auto.
Qed.

Lemma all_flex_mono_defs_mono : forall Ξ, all_flex_mono Ξ -> aenv_defs_mono Ξ.
Proof.
  unfold all_flex_mono; induction 1 as [ | [x b] Ξ' Hb _ IH ];
    constructor; simpl in *; subst; auto using entry_def_mono_flex.
Qed.

(** Every generated block along the extraction is flex-only. *)
Lemma e_guess_mono_block_flex : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> all_flex_mono Ξ.
Proof.
  intros * H; induction H;
    try solve [ repeat constructor ];
    try solve [ apply all_flex_mono_app; assumption ];
    assumption.
Qed.

Lemma e_guess_block_flex : forall S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' -> all_flex_mono Ξ.
Proof.
  intros * H; destruct H; [ constructor | ].
  eauto using e_guess_mono_block_flex.
Qed.

Lemma e_looksub_lookeq_block_flex :
  (forall S0 Θ α m P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ C }}e -> all_flex_mono Ξ) /\
  (forall S0 Θ α P P' S1 Ξ C,
     {{ S0 ↝ S1 ⊨ Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ C }}e -> all_flex_mono Ξ).
Proof.
  apply (e_looksub_lookeq_mutind
           (fun S0 Θ α m P P' S1 Ξ C _ => all_flex_mono Ξ)
           (fun S0 Θ α P P' S1 Ξ C _ => all_flex_mono Ξ));
    intros;
    try solve [ repeat constructor ];
    try solve [ apply all_flex_mono_app; assumption ];
    assumption.
Qed.

Lemma e_solve_sub_eq_block_flex :
  (forall S0 Θ m P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₛ P ≼[ m ] Q ⤳ Ξ ⨾ P' }}e -> all_flex_mono Ξ) /\
  (forall S0 Θ P Q S1 Ξ P',
     {{ S0 ↝ S1 ⊨ Θ ⊢ₑ P ∼ Q ⤳ Ξ ⨾ P' }}e -> all_flex_mono Ξ).
Proof.
  apply (e_solve_sub_eq_mutind
           (fun S0 Θ m P Q S1 Ξ P' _ => all_flex_mono Ξ)
           (fun S0 Θ P Q S1 Ξ P' _ => all_flex_mono Ξ));
    intros;
    try solve [ repeat constructor ];
    try solve [ apply all_flex_mono_app; assumption ];
    eauto using e_guess_mono_block_flex.
Qed.

Lemma e_solve_cstr_block_flex : forall S0 Θ C P S1 Ξ Q,
  {{ S0 ↝ S1 ⊨ Θ ⊩ C ⨾ P ⤳ Ξ ⨾ Q }}e -> all_flex_mono Ξ.
Proof.
  intros * H; induction H;
    eauto using all_flex_mono_app, (proj1 e_solve_sub_eq_block_flex),
      (proj2 e_solve_sub_eq_block_flex).
  constructor.
Qed.

Lemma e_extract_block_flex : forall S0 Θ0 NM α m P P' S1 Ξ Q',
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q' }}e ->
  all_flex_mono Ξ.
Proof.
  intros * H; destruct H.
  repeat apply all_flex_mono_app;
    eauto using (proj1 e_looksub_lookeq_block_flex),
      e_solve_cstr_block_flex, e_guess_block_flex.
Qed.

(** Mono substitution moves neither ∀ count. *)
Lemma mono_ptyp_nall : forall τ, mono_ptyp τ -> nall_ptyp τ = 0.
Proof. induction 1; simpl; lia. Qed.

Lemma mono_pskl_nall : forall τ,
  mono_ptyp τ -> nall_pskl (ptyp_to_pskl τ) = 0.
Proof. intros. rewrite nall_ptyp_to_pskl. auto using mono_ptyp_nall. Qed.

Lemma nall_pskl_subst_nallfree : forall P Q β,
  nall_pskl Q = 0 ->
  nall_pskl (subst_pskl_in_pskl Q β P) = nall_pskl P.
Proof.
  induction P; intros * Hz; simpl;
    try (match goal with |- context [ if ?c then _ else _ ] => destruct c end);
    repeat match goal with
    | IH : context [ subst_pskl_in_pskl ] |- _ => rewrite IH by assumption
    end;
    simpl; lia.
Qed.

(** ⭐ The consistency block PRESERVES the payload discipline: every def it
    installs is mono by its own rules (Assign-SolveM carries [mono_ptyp τ];
    the unify solutions are variables), and every def it re-attaches came
    from its input.  This is what lets §13's Arrow case hand the domain's
    output context to the codomain. *)
Lemma e_assign_unify_consis_defs_mono :
  (forall S0 Θ Ξ α P S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ' }}e ->
     aenv_defs_mono Θ -> aenv_defs_mono Ξ -> aenv_defs_mono Θ') /\
  (forall S0 Θ α β S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊲ α ≈ᵘ β ⊣ Θ' }}e ->
     aenv_defs_mono Θ -> aenv_defs_mono Θ') /\
  (forall Δ1 Δ2 S0 Θ P0 P Q S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}e ->
     aenv_defs_mono Θ -> aenv_defs_mono Θ').
Proof.
  apply (e_assign_unify_consis_mutind
           (fun S0 Θ Ξ α P S1 Θ' _ =>
              aenv_defs_mono Θ -> aenv_defs_mono Ξ -> aenv_defs_mono Θ')
           (fun S0 Θ α β S1 Θ' _ =>
              aenv_defs_mono Θ -> aenv_defs_mono Θ')
           (fun Δ1 Δ2 S0 Θ P0 P Q S1 Θ' _ =>
              aenv_defs_mono Θ -> aenv_defs_mono Θ'));
    intros;
    (* reduce the [(x ~ b) ++ Θ] spellings to cons form so the [Forall]
       patterns below see them *)
    simpl in *;
    (* unpack the input contexts *)
    repeat match goal with
    | H : Forall entry_def_mono (_ ++ _) |- _ =>
        apply Forall_app in H; destruct H
    | H : Forall entry_def_mono (_ :: _) |- _ =>
        inversion H; subst; clear H
    end;
    (* the ∀ rows' IH yields the output UNDER the fresh rigid entry —
       invert it back off *)
    repeat match goal with
    | IH : Forall entry_def_mono ?Θin -> Forall entry_def_mono (_ :: _)
      |- _ =>
        let HH := fresh "Hout" in
        assert (HH := IH ltac:(eauto using Forall_app_intro,
                                 entry_def_mono_tvar));
        inversion HH; subst; clear IH HH
    end;
    eauto 8 using Forall_app_intro, Forall_cons, Forall_nil,
      entry_def_mono_flex, entry_def_mono_tvar, entry_def_mono_def,
      entry_def_mono_var_typ, entry_def_mono_var_skl,
      all_flex_mono_defs_mono, e_guess_mono_block_flex,
      mono_ptyp__var.
Qed.

Corollary e_consis_defs_mono : forall Δ1 Δ2 S0 Θ P0 P Q S1 Θ',
  {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}e ->
  aenv_defs_mono Θ -> aenv_defs_mono Θ'.
Proof.
  intros. eapply (proj2 (proj2 e_assign_unify_consis_defs_mono)); eassumption.
Qed.

(** Local closure of the extraction's yield — §10 composed, in the shape
    §13's ForallL case consumes. *)
Lemma e_guess_lc : forall S0 NM Q S1 Ξ Q',
  e_guess S0 NM Q S1 Ξ Q' -> lc_pskl Q -> lc_pskl Q'.
Proof.
  intros * H Hlc; destruct H; eauto using e_guess_mono_lc_pskl.
Qed.

Lemma e_extract_lc : forall S0 Θ0 NM α m P P' S1 Ξ Q',
  {{ S0 ↝ S1 ⊨ Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ Q' }}e ->
  lc_pskl P -> lc_pskl P' -> lc_pskl Q'.
Proof.
  intros * H HP HP'; destruct H.
  eapply e_guess_lc; [ eassumption | ].
  eapply e_solve_cstr_lc;
    [ eassumption | constructor | eapply e_looksub_cstrs_lc; eassumption ].
Qed.

(* ===================================================================== *)
(*  §14  The consistency block's fuel: HOLES and UNDEFINED FLEXIBLES      *)
(*                                                                        *)
(*  The block's danger cycles are (i) the Arrow row, whose second premise *)
(*  runs at the first's OUTPUT context — which Assign-SolveM may have     *)
(*  GROWN — and (ii) the flexible walks, which substitute a defined       *)
(*  entry away and re-enter [e_consis] at a BIGGER pattern.  What pays    *)
(*  for both is one quantity:                                             *)
(*                                                                        *)
(*      W := nholes(pattern) + nholes(subject) + nundef(context)          *)
(*                                                                        *)
(*  ⭐ W NEVER INCREASES, because holes are the ONLY source of new         *)
(*  flexibles — Assign-SolveM's guess block is exactly the pattern's      *)
(*  holes ([e_guess_mono_block_nundef]), monotype substitution creates    *)
(*  neither a hole nor a flexible, and the unify solutions are            *)
(*  variables.  And any run that CREATES a def must have DEFINED an       *)
(*  undefined flexible, so W then strictly DROPS (§15's inequality) —    *)
(*  which is what pays for the Arrow row's grown output context.  The    *)
(*  def-crossings of the walks are paid by [ndef] (each crossing drops   *)
(*  the entry from the sub-run's context), and everything else by size   *)
(*  and the walk position.                                                *)
(* ===================================================================== *)

Fixpoint nholes_pskl (P : pskl) : nat :=
  match P with
  | pskl_hole        => 1
  | pskl_arrow P1 P2 => nholes_pskl P1 + nholes_pskl P2
  | pskl_all_syn P1  => nholes_pskl P1
  | pskl_tophole P1  => nholes_pskl P1
  | _                => 0
  end.

Fixpoint nundef_aenv (Θ : aenv) : nat :=
  match Θ with
  | nil                            => 0
  | (_, abind_flex_mono) :: Θ'     => 1 + nundef_aenv Θ'
  | _ :: Θ'                        => nundef_aenv Θ'
  end.

Lemma nundef_aenv_app : forall Θ1 Θ2,
  nundef_aenv (Θ1 ++ Θ2) = nundef_aenv Θ1 + nundef_aenv Θ2.
Proof.
  induction Θ1 as [ | [x b] Θ1' IH ]; intros; simpl; [ auto | ].
  destruct b; rewrite IH; lia.
Qed.

(** [ptyp] has no hole constructor at all, so any read-back is hole-free. *)
Lemma nholes_ptyp_to_pskl : forall A, nholes_pskl (ptyp_to_pskl A) = 0.
Proof. induction A; simpl; lia. Qed.

Lemma nholes_pskl_open_rec_var : forall P β k,
  nholes_pskl (open_pskl_wrt_pskl_rec k (pskl_var_f β) P) = nholes_pskl P.
Proof.
  induction P; intros β k; simpl;
    try reflexivity;
    try (match goal with
         | |- context [ lt_eq_lt_dec ?a ?b ] =>
             destruct (lt_eq_lt_dec a b) as [[?|?]|?]
         end; reflexivity);
    first [ solve [ auto ] | f_equal; auto ].
Qed.

Corollary nholes_pskl_open : forall P β,
  nholes_pskl (open_pskl_wrt_pskl P (pskl_var_f β)) = nholes_pskl P.
Proof. intros. apply nholes_pskl_open_rec_var. Qed.

Lemma nholes_pskl_subst_holefree : forall P Q β,
  nholes_pskl Q = 0 ->
  nholes_pskl (subst_pskl_in_pskl Q β P) = nholes_pskl P.
Proof.
  induction P; intros * Hz; simpl;
    try (match goal with |- context [ if ?c then _ else _ ] => destruct c end);
    repeat match goal with
    | IH : context [ subst_pskl_in_pskl ] |- _ => rewrite IH by assumption
    end;
    simpl; lia.
Qed.

(** ⭐ The guess block is EXACTLY the pattern's holes — the accounting fact
    that makes W conservative at Assign-SolveM. *)
Lemma e_guess_mono_block_nundef : forall S0 P S1 Ξ A,
  e_guess_mono S0 P S1 Ξ A -> nundef_aenv Ξ = nholes_pskl P.
Proof.
  intros * H; induction H; simpl;
    repeat rewrite nundef_aenv_app;
    repeat rewrite nholes_pskl_open in *;
    lia.
Qed.

(* ===================================================================== *)
(*  §15  The two run-invariants the Arrow row needs                       *)
(* ===================================================================== *)

(** Defined flexibles never disappear along a run — every row re-attaches
    what it stripped, and Assign-SolveM only adds. *)
Lemma e_assign_unify_consis_ndef_mono :
  (forall S0 Θ Ξ α P S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ' }}e ->
     ndef_aenv Ξ + ndef_aenv Θ <= ndef_aenv Θ') /\
  (forall S0 Θ α β S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊲ α ≈ᵘ β ⊣ Θ' }}e ->
     ndef_aenv Θ <= ndef_aenv Θ') /\
  (forall Δ1 Δ2 S0 Θ P0 P Q S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}e ->
     ndef_aenv Θ <= ndef_aenv Θ').
Proof.
  apply (e_assign_unify_consis_mutind
           (fun S0 Θ Ξ α P S1 Θ' _ =>
              ndef_aenv Ξ + ndef_aenv Θ <= ndef_aenv Θ')
           (fun S0 Θ α β S1 Θ' _ => ndef_aenv Θ <= ndef_aenv Θ')
           (fun Δ1 Δ2 S0 Θ P0 P Q S1 Θ' _ =>
              ndef_aenv Θ <= ndef_aenv Θ'));
    intros; simpl in *;
    repeat rewrite ndef_aenv_app in *; simpl in *;
    (* Flex-Flex-Skip' carries its binding as a disjunction *)
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H
    | H : exists _, _ |- _ => destruct H
    end; subst; simpl in *;
    lia.
Qed.

Corollary e_consis_ndef_mono : forall Δ1 Δ2 S0 Θ P0 P Q S1 Θ',
  {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}e ->
  ndef_aenv Θ <= ndef_aenv Θ'.
Proof.
  intros. eapply (proj2 (proj2 e_assign_unify_consis_ndef_mono)); eassumption.
Qed.

(** ⭐ W-PRESERVATION, in the addition form that CHAINS at the Arrow row:
    what a run leaves behind (its undefs plus its defs) is bounded by what
    it was given plus the holes of its skeleton inputs.  Read off it: a run
    that created a def (ndef up by d) consumed at least d undefs-or-holes —
    so W strictly drops whenever the context grew. *)
Lemma e_assign_unify_consis_wpres :
  (forall S0 Θ Ξ α P S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊲[ Ξ ] α ≔ P ⊣ Θ' }}e ->
     nundef_aenv Θ' + ndef_aenv Θ'
     <= nundef_aenv (Ξ ++ Θ) + ndef_aenv (Ξ ++ Θ) + nholes_pskl P) /\
  (forall S0 Θ α β S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊲ α ≈ᵘ β ⊣ Θ' }}e ->
     nundef_aenv Θ' + ndef_aenv Θ' <= nundef_aenv Θ + ndef_aenv Θ) /\
  (forall Δ1 Δ2 S0 Θ P0 P Q S1 Θ',
     {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}e ->
     nundef_aenv Θ' + ndef_aenv Θ'
     <= nundef_aenv Θ + ndef_aenv Θ + nholes_pskl P0 + nholes_pskl P).
Proof.
  apply (e_assign_unify_consis_mutind
           (fun S0 Θ Ξ α P S1 Θ' _ =>
              nundef_aenv Θ' + ndef_aenv Θ'
              <= nundef_aenv (Ξ ++ Θ) + ndef_aenv (Ξ ++ Θ) + nholes_pskl P)
           (fun S0 Θ α β S1 Θ' _ =>
              nundef_aenv Θ' + ndef_aenv Θ' <= nundef_aenv Θ + ndef_aenv Θ)
           (fun Δ1 Δ2 S0 Θ P0 P Q S1 Θ' _ =>
              nundef_aenv Θ' + ndef_aenv Θ'
              <= nundef_aenv Θ + ndef_aenv Θ
                 + nholes_pskl P0 + nholes_pskl P));
    intros; simpl in *;
    (* Assign-SolveM: the guess block is the pattern's holes, and flex-only *)
    repeat match goal with
    | Hg : e_guess_mono _ _ _ _ _ |- _ =>
        pose proof (e_guess_mono_block_nundef Hg);
        pose proof (all_flex_mono_ndef (e_guess_mono_block_flex Hg));
        clear Hg
    end;
    (* the substitution on a VARIABLE subject has already reduced to the
       bare comparison — resolve it so its hole count computes *)
    repeat match goal with
    | H : context [ nholes_pskl (if ?c then _ else _) ] |- _ => destruct c
    | |- context [ nholes_pskl (if ?c then _ else _) ] => destruct c
    end;
    (* the substituted skeletons keep their hole counts *)
    repeat rewrite nholes_pskl_subst_holefree in *
      by (auto using nholes_ptyp_to_pskl);
    repeat rewrite nholes_ptyp_to_pskl in *;
    repeat rewrite nholes_pskl_open in *;
    repeat rewrite nundef_aenv_app in *;
    repeat rewrite ndef_aenv_app in *;
    simpl in *;
    (* Flex-Flex-Skip' carries its binding as a disjunction *)
    repeat match goal with
    | H : _ \/ _ |- _ => destruct H
    | H : exists _, _ |- _ => destruct H
    end; subst; simpl in *;
    lia.
Qed.

Corollary e_consis_wpres : forall Δ1 Δ2 S0 Θ P0 P Q S1 Θ',
  {{ S0 ↝ S1 ⊨ Θ ⊢[ Δ1 | Δ2 | P0 ] P ∼ Q ⊣ Θ' }}e ->
  nundef_aenv Θ' + ndef_aenv Θ'
  <= nundef_aenv Θ + ndef_aenv Θ + nholes_pskl P0 + nholes_pskl P.
Proof.
  intros. eapply (proj2 (proj2 e_assign_unify_consis_wpres)); eassumption.
Qed.

(* ===================================================================== *)
(*  §16  ⭐⭐⭐ TOTALITY OF THE CONSISTENCY BLOCK                            *)
(*                                                                        *)
(*  The lex measure ( W , ndef Θ , size P0 + size P , |Θ|-walk ), with    *)
(*  W := nholes P0 + nholes P + nundef Θ.  Which component each rule      *)
(*  consumes:                                                             *)
(*                                                                        *)
(*    Arrow p2         W, or size: if the domain's run created a def, W   *)
(*                     strictly dropped (§15's inequality — creating a    *)
(*                     def costs an undef or a hole); if it created none, *)
(*                     ndef ties by monotonicity and SIZE pays            *)
(*    structural rows  size                                               *)
(*    Flex/FlexL/R     size (a variable leaves the skeleton inputs)       *)
(*    Assign / FF-Assign  ndef (the crossed def is dropped below)         *)
(*    walk rows        |Θ| (every row peels an entry)                     *)
(*    Assign-SolveM    the guess, total at an lc pattern (§11)            *)
(* ===================================================================== *)

Lemma e_consis_block_order_total_n :
  forall n1 n2,
  (forall n4 S Θ α β,
     nundef_aenv Θ <= n1 ->
     ndef_aenv Θ <= n2 ->
     length Θ <= n4 ->
     aenv_defs_mono Θ ->
     e_unify_order S Θ α β) /\
  (forall n4 S Θ Ξ α P,
     nholes_pskl P + nundef_aenv (Ξ ++ Θ) <= n1 ->
     ndef_aenv (Ξ ++ Θ) <= n2 ->
     length Θ <= n4 ->
     lc_pskl P -> aenv_defs_mono (Ξ ++ Θ) ->
     e_assign_order S Θ Ξ α P) /\
  (forall n3 Δ1 Δ2 S Θ P0 P,
     nholes_pskl P0 + nholes_pskl P + nundef_aenv Θ <= n1 ->
     ndef_aenv Θ <= n2 ->
     size_pskl P0 + size_pskl P <= n3 ->
     lc_pskl P0 -> lc_pskl P -> aenv_defs_mono Θ ->
     e_consis_order Δ1 Δ2 S Θ P0 P).
Proof.
  intros n1; induction n1 as [n1 IH1] using lt_wf_ind;
    intros n2; induction n2 as [n2 IH2] using lt_wf_ind.
  (* ------------------------------------------------------------------ *)
  (*  The unify walk — peels the context, and consumes a def at          *)
  (*  Flex-Flex-Assign.                                                  *)
  (* ------------------------------------------------------------------ *)
  assert (Huni : forall n4 S Θ α β,
             nundef_aenv Θ <= n1 -> ndef_aenv Θ <= n2 -> length Θ <= n4 ->
             aenv_defs_mono Θ ->
             e_unify_order S Θ α β).
  { intros n4; induction n4 as [n4 IH4] using lt_wf_ind;
      intros * Hw Hnd Hlen Hdm.
    constructor; intros; subst; simpl in *;
      repeat match goal with
      | H : Forall entry_def_mono (_ :: _) |- _ =>
          inversion H; subst; clear H
      end.
    - (* Flex-Flex-Assign: the crossed def is consumed — the consis
         conjunct at ndef − 1, on two hole-free read-backs *)
      match goal with
      | He : entry_def_mono (_, abind_flex_mono_def _) |- _ =>
          unfold entry_def_mono in He; simpl in He
      end.
      unshelve eapply (proj2 (proj2 (IH2 (ndef_aenv Θ0) ltac:(lia)))
                         (size_pskl _ + size_pskl _));
        try apply le_n;
        try assumption;
        try solve [ repeat rewrite nholes_ptyp_to_pskl; simpl; lia ];
        try solve [ apply ptyp_to_pskl_lc;
                    match goal with
                    | |- context [ if ?c then _ else _ ] => destruct c
                    end;
                    auto using mono_ptyp_lc; constructor ].
    - (* Flex-Flex-Skip *)
      apply (IH4 (length Θ0)); try assumption; try lia.
    - (* Flex-Flex-Skip', rigid *)
      apply (IH4 (length Θ0)); try assumption; try lia.
    - (* Flex-Flex-Skip', term (typ) *)
      apply (IH4 (length Θ0)); try assumption; try lia.
    - (* Flex-Flex-Skip', term (skl) *)
      apply (IH4 (length Θ0)); try assumption; try lia. }
  (* ------------------------------------------------------------------ *)
  (*  The assign walk — same shape, plus the guess at the target.        *)
  (* ------------------------------------------------------------------ *)
  assert (Hass : forall n4 S Θ Ξ α P,
             nholes_pskl P + nundef_aenv (Ξ ++ Θ) <= n1 ->
             ndef_aenv (Ξ ++ Θ) <= n2 ->
             length Θ <= n4 ->
             lc_pskl P -> aenv_defs_mono (Ξ ++ Θ) ->
             e_assign_order S Θ Ξ α P).
  { intros n4; induction n4 as [n4 IH4] using lt_wf_ind;
      intros * Hw Hnd Hlen Hlc Hdm.
    constructor; intros; subst; simpl in *;
      repeat rewrite nundef_aenv_app in Hw; simpl in Hw;
      repeat rewrite ndef_aenv_app in Hnd; simpl in Hnd;
      repeat match goal with
      | H : Forall entry_def_mono (_ ++ _) |- _ =>
          apply Forall_app in H; destruct H
      | H : Forall entry_def_mono (_ :: _) |- _ =>
          inversion H; subst; clear H
      end.
    - (* Assign-SolveM — the guess, total at the lc pattern *)
      apply e_guess_mono_order_total; assumption.
    - (* Assign-Assign — the consis conjunct at ndef − 1; mono
         substitution keeps the hole counts *)
      match goal with
      | He : entry_def_mono (_, abind_flex_mono_def _) |- _ =>
          unfold entry_def_mono in He; simpl in He
      end.
      unshelve eapply (proj2 (proj2 (IH2 (ndef_aenv (Ξ ++ Θ0))
                                       ltac:(rewrite ndef_aenv_app; lia)))
                         (size_pskl _ + size_pskl _));
        try apply le_n;
        try assumption;
        (* W: hole counts survive the mono substitution *)
        try solve [ rewrite nholes_pskl_subst_holefree
                      by auto using nholes_ptyp_to_pskl;
                    repeat match goal with
                    | |- context [ nholes_pskl (if ?c then _ else _) ] =>
                        destruct c
                    end;
                    repeat rewrite nholes_ptyp_to_pskl;
                    rewrite nundef_aenv_app; simpl; lia ];
        (* the ndef bound *)
        try solve [ rewrite ndef_aenv_app; apply le_n ];
        (* lc of the substituted subject (already reduced) and pattern *)
        try solve [ match goal with
                    | |- lc_pskl (if ?c then _ else _) => destruct c
                    end;
                    auto using ptyp_to_pskl_lc, mono_ptyp_lc;
                    constructor ];
        try solve [ apply subst_pskl_in_pskl_lc_pskl;
                    auto using ptyp_to_pskl_lc, mono_ptyp_lc ];
        auto using Forall_app_intro.
    - (* Assign-Depend / Assign-Skip *)
      split;
        (apply (IH4 (length Θ0)); [ lia | .. ];
         try assumption;
         repeat rewrite nundef_aenv_app; repeat rewrite ndef_aenv_app;
         simpl; try lia;
         repeat apply Forall_app_intro;
         eauto using Forall_cons, Forall_nil, entry_def_mono_flex).
    - (* Assign-SkipRigid *)
      apply (IH4 (length Θ0)); [ lia | .. ];
        try assumption;
        repeat rewrite nundef_aenv_app; repeat rewrite ndef_aenv_app;
        simpl; try lia;
        auto using Forall_app_intro.
    - (* Assign-SkipTmVar (typ) *)
      apply (IH4 (length Θ0)); [ lia | .. ];
        try assumption;
        repeat rewrite nundef_aenv_app; repeat rewrite ndef_aenv_app;
        simpl; try lia;
        auto using Forall_app_intro.
    - (* Assign-SkipTmVar (skl) *)
      apply (IH4 (length Θ0)); [ lia | .. ];
        try assumption;
        repeat rewrite nundef_aenv_app; repeat rewrite ndef_aenv_app;
        simpl; try lia;
        auto using Forall_app_intro. }
  split; [ exact Huni | split; [ exact Hass | ] ].
  (* ------------------------------------------------------------------ *)
  (*  Consistency proper.                                                *)
  (* ------------------------------------------------------------------ *)
  intros n3; induction n3 as [n3 IH3] using lt_wf_ind;
    intros * Hw Hnd Hsz Hlc0 Hlc Hdm.
  constructor; intros; subst; simpl in Hw, Hsz.
  - (* Arrow — the domain by size; the codomain by the case split the two
       §15 invariants decide *)
    repeat match goal with
    | Hl : lc_pskl (pskl_arrow _ _) |- _ =>
        apply lc_pskl_arrow_inv in Hl; destruct Hl
    end.
    split.
    + unshelve eapply (IH3 (size_pskl P0a + size_pskl P1) ltac:(lia));
        try apply le_n; try assumption; lia.
    + intros * Hc1.
      pose proof (e_consis_wpres Hc1) as Hwp.
      pose proof (e_consis_ndef_mono Hc1) as Hmono.
      pose proof (e_consis_defs_mono Hc1 Hdm) as Hdm1.
      destruct (lt_eq_lt_dec (ndef_aenv Θ) (ndef_aenv Θ1)) as [[Hlt|Heq]|Hgt];
        [ | | lia ].
      * (* the domain created a def — W strictly dropped: restart at IH1 *)
        unshelve eapply (proj2 (proj2 (IH1 (nholes_pskl P0b + nholes_pskl P2
                                            + nundef_aenv Θ1)
                                         ltac:(lia)
                                         (ndef_aenv Θ1)))
                           (size_pskl P0b + size_pskl P2));
          try apply le_n; try assumption.
      * (* no def created — ndef ties, size pays *)
        unshelve eapply (IH3 (size_pskl P0b + size_pskl P2) ltac:(lia));
          try apply le_n; try assumption; lia.
  - (* ForallInh *)
    unshelve eapply (IH3 (size_pskl (open_pskl_wrt_pskl P0'
                                       (pskl_var_f (supply_fresh S)))
                          + size_pskl (open_pskl_wrt_pskl P1
                                         (pskl_var_f (supply_fresh S))))
                       ltac:(repeat rewrite size_pskl_open_pskl_wrt_pskl_var;
                             lia));
      try apply le_n; try assumption;
      try solve [ repeat rewrite nholes_pskl_open; simpl; lia ];
      try solve [ simpl; lia ];
      try solve [ eauto using lc_pskl_all_syn_inv ];
      try solve [ constructor; [ apply entry_def_mono_tvar | assumption ] ].
  - (* ForallSyn *)
    unshelve eapply (IH3 (size_pskl (pskl_tophole P0')
                          + size_pskl (open_pskl_wrt_pskl P1
                                         (pskl_var_f (supply_fresh S))))
                       ltac:(simpl;
                             repeat rewrite size_pskl_open_pskl_wrt_pskl_var;
                             lia));
      try apply le_n; try assumption;
      try solve [ simpl; repeat rewrite nholes_pskl_open; simpl; lia ];
      try solve [ simpl; lia ];
      try solve [ eauto using lc_pskl_all_syn_inv ];
      try solve [ constructor; [ apply entry_def_mono_tvar | assumption ] ].
  - (* UnivGhost *)
    unshelve eapply (IH3 (size_pskl P0' + size_pskl P1) ltac:(simpl in *; lia));
      try apply le_n; try assumption;
      try solve [ simpl in *; lia ];
      eauto using lc_pskl_tophole_inv.
  - (* UnivGhost1 *)
    unshelve eapply (IH3 (size_pskl (open_pskl_wrt_pskl P0'
                                       (pskl_var_f (supply_fresh S)))
                          + size_pskl (pskl_tophole P1))
                       ltac:(simpl;
                             repeat rewrite size_pskl_open_pskl_wrt_pskl_var;
                             lia));
      try apply le_n; try assumption;
      try solve [ simpl; repeat rewrite nholes_pskl_open; simpl; lia ];
      try solve [ simpl; lia ];
      try solve [ eauto using lc_pskl_all_syn_inv ];
      try solve [ constructor; [ apply entry_def_mono_tvar | assumption ] ].
  - (* UnivGhost2 *)
    unshelve eapply (IH3 (size_pskl P0 + size_pskl P1) ltac:(simpl in *; lia));
      try apply le_n; try assumption;
      try solve [ simpl in *; lia ];
      eauto using lc_pskl_tophole_inv.
  - (* UnivGhostR *)
    unshelve eapply (IH3 (size_pskl P0' + size_pskl P) ltac:(simpl in *; lia));
      try apply le_n; try assumption;
      try solve [ simpl in *; lia ];
      eauto using lc_pskl_tophole_inv.
  - (* Flex — the unify walk *)
    apply (Huni (length Θ)); try apply le_n; try assumption; simpl in *; lia.
  - (* FlexL — assign the pattern *)
    apply (Hass (length Θ)); simpl; try apply le_n; try assumption; lia.
  - (* FlexR — assign the subject *)
    apply (Hass (length Θ)); simpl; try apply le_n; try assumption; lia.
Qed.

(** ⭐⭐ THE CONSISTENCY BLOCK TERMINATES — §8b.4's "not routine" campaign,
    closed.  The measure the paper's design principle buys: holes and
    undefined flexibles are the fuel, defined flexibles are consumed by the
    walks, and sizes referee the structural descent. *)
Theorem e_consis_order_total : forall Δ1 Δ2 S Θ P0 P,
  lc_pskl P0 -> lc_pskl P -> aenv_defs_mono Θ ->
  e_consis_order Δ1 Δ2 S Θ P0 P.
Proof.
  intros.
  unshelve eapply (proj2 (proj2 (e_consis_block_order_total_n
                                   (nholes_pskl P0 + nholes_pskl P
                                    + nundef_aenv Θ)
                                   (ndef_aenv Θ)))
                     (size_pskl P0 + size_pskl P));
    try apply le_n; assumption.
Qed.

(* ===================================================================== *)
(*  §17  ⭐⭐⭐ TOTALITY OF THE SUBTYPING WALK                               *)
(*                                                                        *)
(*  The lexicographic argument, assembled.  Which component each rule     *)
(*  consumes:                                                             *)
(*                                                                        *)
(*    Arrow        fnd_mode M   (an FN is crossed; everything resets)     *)
(*    ForallR      nall P0      (the pattern's ∀ is opened at a variable  *)
(*                              and GONE — open-at-var preserves nall)    *)
(*    ForallL      hnall P      (§9's decrease theorem; the context grows *)
(*                              by a flex-only block, so ndef holds)      *)
(*    Flex-Assign  ndef Θ       (a defined flexible is substituted away;  *)
(*                              mono-substitution fixes nall and hnall)   *)
(*    UnivGhostL   size P       (a ⫯ is stripped; hnall is transparent)   *)
(*    the walk     |Θ0|         (every e_sub_flex row peels an entry)     *)
(*    Flex-Solve   —            (TIED: the re-entered subject α̂→β̂ has     *)
(*                              only the Arrow row, so ONE inline step    *)
(*                              reaches fnd_mode M — 8b.4's ⚠️)            *)
(*                                                                        *)
(*  The consistency block's totality enters as the hypothesis [Hco] —     *)
(*  in exactly [e_consis_order_total]'s shape, so the final theorem       *)
(*  below discharges it and carries NO hypothesis.                        *)
(* ===================================================================== *)

Lemma e_sub_order_total_n :
  (forall Δ1 Δ2 S Θ P0 P,
     lc_pskl P0 -> lc_pskl P -> aenv_defs_mono Θ ->
     e_consis_order Δ1 Δ2 S Θ P0 P) ->
  forall n1 n2 n4,
  (forall n3 n5 S0 NM M P0 Θ0 P,
     fnd_mode M <= n1 ->
     nall_pskl P0 <= n2 ->
     ndef_aenv Θ0 <= n4 ->
     hnall_pskl P <= n3 ->
     size_pskl P <= n5 ->
     lc_pskl P -> lc_pskl P0 -> aenv_defs_mono Θ0 ->
     e_sub_order S0 NM M P0 Θ0 P)
  /\
  (forall n6 S0 NM M P0 Θ0 Ξ α,
     fnd_mode (mode_fn M) <= n1 ->
     nall_pskl P0 <= n2 ->
     ndef_aenv (Ξ ++ Θ0) <= n4 ->
     length Θ0 <= n6 ->
     lc_pskl P0 -> aenv_defs_mono (Ξ ++ Θ0) ->
     e_sub_flex_order S0 NM M P0 Θ0 Ξ α).
Proof.
  intros Hco n1; induction n1 as [n1 IH1] using lt_wf_ind;
    intros n2; induction n2 as [n2 IH2] using lt_wf_ind;
    intros n4; induction n4 as [n4 IH4] using lt_wf_ind.
  (* ------------------------------------------------------------------ *)
  (*  Ψ — the flexible walk.  Its exits reach Φ only through IH1 (an     *)
  (*  arrow crossed, via the inline step), IH4 (a def consumed), and its *)
  (*  own rows only peel the context (IH6).                              *)
  (* ------------------------------------------------------------------ *)
  assert (Hpsi : forall n6 S0 NM M P0 Θ0 Ξ α,
             fnd_mode (mode_fn M) <= n1 ->
             nall_pskl P0 <= n2 ->
             ndef_aenv (Ξ ++ Θ0) <= n4 ->
             length Θ0 <= n6 ->
             lc_pskl P0 -> aenv_defs_mono (Ξ ++ Θ0) ->
             e_sub_flex_order S0 NM M P0 Θ0 Ξ α).
  { intros n6; induction n6 as [n6 IH6] using lt_wf_ind;
      intros * Hfnd Hnall Hndef Hlen Hlc0 Hdm.
    constructor; intros; subst;
      (* ⚙ [simpl in *] first: metalib's [x ~ a] is [one (x, a)], a
         DEFINITION, so neither the [Forall] patterns nor [ndef]'s
         reduction see the cons until it is unfolded *)
      simpl in *;
      repeat rewrite ndef_aenv_app in Hndef; simpl in Hndef;
      repeat match goal with
      | H : Forall entry_def_mono (_ ++ _) |- _ =>
          apply Forall_app in H; destruct H
      | H : Forall entry_def_mono (_ :: _) |- _ =>
          inversion H; subst; clear H
      end.
    - (* Flex-Solve: the ONE tied edge — build the re-entered call's order
         by hand; its subject is an arrow, so its only live premise is the
         Arrow row, which strictly drops fnd_mode.  *)
      constructor; intros; subst; try congruence.
      (* the Arrow premise survives *)
      match goal with
      | Heq : mode_fn _ = mode_fn _ |- _ =>
          inversion Heq; subst; clear Heq
      end;
      match goal with
      | Heq : pskl_arrow _ _ = pskl_arrow _ _ |- _ =>
          inversion Heq; subst; clear Heq
      end.
      split.
      { apply Hco.
        - match goal with
          | Hl : lc_pskl (pskl_arrow _ _) |- _ =>
              apply lc_pskl_arrow_inv in Hl; destruct Hl; assumption
          end.
        - constructor.
        - repeat apply Forall_app_intro;
            eauto 10 using Forall_cons, Forall_nil, entry_def_mono_flex,
              entry_def_mono_def, mono_ptyp__arrow, mono_ptyp__var. }
      intros * Hcons.
      (* the mode is read off the GOAL — [subst] may have renamed [M] *)
      match goal with
      | |- e_sub_order _ _ ?Mg _ _ _ =>
          unshelve eapply (proj1 (IH1 (fnd_mode Mg)
                                    ltac:(simpl in Hfnd; lia)
                                    (nall_pskl _) (ndef_aenv _))
                             (hnall_pskl _) (size_pskl _))
      end;
        try apply le_n;
        try solve [ constructor ].
      + (* the codomain of the pattern is locally closed *)
        match goal with
        | Hl : lc_pskl (pskl_arrow _ _) |- _ =>
            apply lc_pskl_arrow_inv in Hl; destruct Hl; assumption
        end.
      + (* the domain run's output keeps the payload discipline *)
        eapply e_consis_defs_mono; [ eassumption | ].
        repeat apply Forall_app_intro;
          eauto 10 using Forall_cons, Forall_nil, entry_def_mono_flex,
            entry_def_mono_def, mono_ptyp__arrow, mono_ptyp__var.
    - (* Flex-Assign: the def is consumed — IH4, with the ∀ counts fixed
         by mono-substitution *)
      match goal with
      | He : entry_def_mono (_, abind_flex_mono_def _) |- _ =>
          unfold entry_def_mono in He; simpl in He
      end.
      unshelve eapply (proj1 (IH4 (ndef_aenv (Ξ ++ Θ0'))
                                ltac:(rewrite ndef_aenv_app in *; lia))
                         (hnall_pskl _) (size_pskl _));
        try apply le_n;
        try assumption;
        (* nall (subst τ β P0) = nall P0 *)
        try solve [ rewrite nall_pskl_subst_nallfree
                      by auto using mono_pskl_nall; assumption ];
        (* both substituted skeletons are locally closed — the subject's
           substitution has already REDUCED (it is a variable), so it shows
           as the bare comparison *)
        try solve [ match goal with
                    | |- lc_pskl (if ?c then _ else _) => destruct c
                    end;
                    auto using ptyp_to_pskl_lc, mono_ptyp_lc;
                    constructor ];
        try solve [ apply subst_pskl_in_pskl_lc_pskl;
                    auto using ptyp_to_pskl_lc, mono_ptyp_lc;
                    constructor ];
        (* the payload discipline, reassembled without the def *)
        auto using Forall_app_intro.
    - (* Flex-Depend / Flex-Skip *)
      split;
        (apply (IH6 (length Θ0')); [ lia | .. ];
         try assumption;
         repeat rewrite ndef_aenv_app; simpl;
         try lia;
         repeat apply Forall_app_intro;
         eauto using Forall_cons, Forall_nil, entry_def_mono_flex).
    - (* Flex-SkipRigid *)
      apply (IH6 (length Θ0')); [ lia | .. ];
        try assumption;
        repeat rewrite ndef_aenv_app; simpl;
        try lia;
        auto using Forall_app_intro.
    - (* Flex-SkipTmVar (typ payload) *)
      apply (IH6 (length Θ0')); [ lia | .. ];
        try assumption;
        repeat rewrite ndef_aenv_app; simpl;
        try lia;
        auto using Forall_app_intro.
    - (* Flex-SkipTmVar (skl payload) *)
      apply (IH6 (length Θ0')); [ lia | .. ];
        try assumption;
        repeat rewrite ndef_aenv_app; simpl;
        try lia;
        auto using Forall_app_intro. }
  split; [ | exact Hpsi ].
  (* ------------------------------------------------------------------ *)
  (*  Φ — the subtyping judgement proper.                                *)
  (* ------------------------------------------------------------------ *)
  intros n3; induction n3 as [n3 IH3] using lt_wf_ind;
    intros n5; induction n5 as [n5 IH5] using lt_wf_ind;
    intros * Hfnd Hnall Hndef Hh Hsz Hlc Hlc0 Hdm.
  constructor; intros; subst.
  - (* Check — the consistency hypothesis *)
    apply Hco; assumption.
  - (* ForallR — the pattern's ∀ is consumed: IH2 *)
    simpl in Hnall.
    unshelve eapply (proj1 (IH2 (nall_pskl
                                   (open_pskl_wrt_pskl B
                                      (pskl_var_f (supply_fresh S0))))
                              ltac:(rewrite nall_pskl_open; lia)
                              (ndef_aenv _))
                       (hnall_pskl _) (size_pskl _));
      try apply le_n;
      try assumption.
    + (* the opened pattern is locally closed *)
      eauto using lc_pskl_all_syn_inv.
    + constructor; [ apply entry_def_mono_tvar | assumption ].
  - (* FlexMono — enter the walk *)
    apply (Hpsi (length Θ0));
      simpl; try assumption; try apply le_n.
  - (* Arrow — an FN is crossed: IH1, everything resets *)
    split.
    { apply Hco;
        try solve [ match goal with
                    | Hl : lc_pskl (pskl_arrow _ _) |- _ =>
                        apply lc_pskl_arrow_inv in Hl; destruct Hl; assumption
                    end ];
        assumption. }
    intros * Hcons.
    repeat match goal with
    | Hl : lc_pskl (pskl_arrow _ _) |- _ =>
        apply lc_pskl_arrow_inv in Hl; destruct Hl
    end.
    match goal with
    | |- e_sub_order _ _ ?Mg _ _ _ =>
        unshelve eapply (proj1 (IH1 (fnd_mode Mg)
                                  ltac:(simpl in Hfnd; lia)
                                  (nall_pskl _) (ndef_aenv _))
                           (hnall_pskl _) (size_pskl _))
    end;
      try apply le_n;
      try assumption.
    eapply e_consis_defs_mono; eassumption.
  - (* ForallL — §9's decrease theorem: IH3 *)
    match goal with
    | Hg : guarded_pskl _ \/ _ = pskl_hole |- _ => idtac
    end.
    split.
    + apply e_extract_order_total;
        eauto using lc_pskl_all_syn_inv.
    + intros * Hxt Hwf.
      (* the instantiation is locally closed — §12's composition *)
      assert (Hlc1 : lc_pskl P1)
        by (eapply e_extract_lc;
            eauto using lc_pskl_all_syn_inv).
      unshelve eapply (IH3 (hnall_pskl (open_pskl_wrt_pskl Q P1))
                         ltac:(pose proof (@e_extract_forall_l_hnall
                                             (add (supply_fresh S0) S0)
                                             Θ0 NM (supply_fresh S0)
                                             M Q P0 S1 Ξ P1 Hxt
                                             ltac:(assumption));
                               lia)
                         (size_pskl _));
        try apply le_n;
        try assumption.
      * (* the block is flex-only, so ndef is untouched *)
        rewrite ndef_aenv_app.
        rewrite (all_flex_mono_ndef (e_extract_block_flex Hxt)).
        lia.
      * (* lc (open Q P1): graft via a fresh name *)
        destruct (atom_fresh (ftvar_in_pskl Q)) as [x Hx].
        rewrite (subst_pskl_in_pskl_intro x) by assumption.
        apply subst_pskl_in_pskl_lc_pskl;
          eauto using lc_pskl_all_syn_inv.
      * apply Forall_app_intro;
          eauto using all_flex_mono_defs_mono, e_extract_block_flex.
  - (* UnivGhostL — a ⫯ is stripped: IH5 *)
    simpl in Hh, Hsz.
    unshelve eapply (IH5 (size_pskl Q) ltac:(lia));
      try apply le_n;
      try assumption.
    eauto using lc_pskl_tophole_inv.
Qed.

(** ⭐⭐⭐ THE THEOREM — the subtyping walk terminates on every input that is
    locally closed and whose context keeps the payload discipline.  NO
    hypothesis left: §16 discharged the consistency block. *)
Theorem e_sub_order_total : forall S0 NM M P0 Θ0 P,
  lc_pskl P -> lc_pskl P0 -> aenv_defs_mono Θ0 ->
  e_sub_order S0 NM M P0 Θ0 P.
Proof.
  intros.
  unshelve eapply (proj1 (e_sub_order_total_n e_consis_order_total
                            (fnd_mode M) (nall_pskl P0) (ndef_aenv Θ0))
                     (hnall_pskl P) (size_pskl P));
    try apply le_n; assumption.
Qed.
