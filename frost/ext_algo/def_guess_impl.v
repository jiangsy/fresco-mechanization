(** ext_algo — [guess^TY] as an EXECUTABLE FUNCTION, by Bove–Capretta.

    M1.7 of docs/HANDOFF-extractable-algo-encoding.md §7.6: the spike that
    proves the whole of TODO (2)'s pipeline on one small judgement before any
    of it is committed to at scale.  Four layers, in order:

      §1  [guess_result]        what the function returns
      §2  [e_guess_mono_order]  the DOMAIN PREDICATE — the call graph, in Prop
      §3  [e_guess_mono_impl]   the function, by STRUCTURAL recursion on it
      §4  [e_guess_mono_order_total] / [e_guess_mono_run] — totality, and the
                                argument-free runner it buys

    ⭐ WHY THIS SHAPE AND NOT [Equations … by wf] WITH A MEASURE.  The hand-off
    originally owed a well-founded measure before any code could exist, because
    [guess^TY] is NOT structurally recursive: the ∀ row recurses on
    [open_pskl_wrt_pskl P (pskl_var_f β)], which is no subterm of
    [pskl_all_syn P].  Bove–Capretta removes that debt.  The function recurses
    structurally on a Prop-valued domain predicate that mirrors its own call
    graph, and TERMINATION becomes a separate theorem (§4) rather than a
    precondition of the definition.  Extraction erases the predicate entirely.

    ⚙ NO Prop→Type ELIMINATION HAPPENS, which is the thing to check before
    believing this is legal.  The branches match on [P] (a [Set]); each
    recursive call's sub-derivation is produced by INVERTING [H] in a Prop
    goal, which the guard checker accepts as a structural subterm.  The one
    place a Prop is eliminated into [Type] is the [pskl_var_b] branch, and it
    goes through [False_rect] — empty elimination, always permitted.

    The pattern is McTT's (`~/Documents/HKU/Research/mctt_ref`,
    `theories/Extraction/{Evaluation,Readback,NbE,Subtyping,TypeCheck}.v`),
    including the [derive(equations=yes,eliminator=no)] attribute: the derived
    equation lemmas and eliminator are what would drag dependent-elimination
    axioms in, and nothing here needs them.

    ⭐⭐ WHAT THIS EXTRACTS TO — the result the spike exists to produce, and the
    standing bar of the hand-off's §8 (clean program, no proof concepts) met
    with nothing left over.  [Recursive Extraction e_guess_mono_run] gives:

<<
      let rec e_guess_mono_impl s0 = function
      | Pskl_unit -> { gr_supply = s0; gr_block = []; gr_type = Ptyp_unit }
      | Pskl_var_b _ -> assert false (* absurd case *)
      | Pskl_var_f a ->
        { gr_supply = s0; gr_block = []; gr_type = (Ptyp_var_f a) }
      | Pskl_arrow (p1, p2) ->
        let r1 = e_guess_mono_impl s0 p1 in
        let r2 = e_guess_mono_impl r1.gr_supply p2 in
        { gr_supply = r2.gr_supply;
          gr_block = (app r1.gr_block r2.gr_block);
          gr_type = (Ptyp_arrow (r1.gr_type, r2.gr_type)) }
      | Pskl_all_syn p1 ->
        let r = e_guess_mono_impl (AtomSetImpl.add (supply_fresh s0) s0)
                  (open_pskl_wrt_pskl p1 (Pskl_var_f (supply_fresh s0))) in
        { gr_supply = r.gr_supply; gr_block = r.gr_block;
          gr_type = (Ptyp_all
            (close_ptyp_wrt_ptyp (supply_fresh s0) r.gr_type)) }
      | Pskl_hole ->
        { gr_supply = (AtomSetImpl.add (supply_fresh s0) s0);
          gr_block = (app (EnvImpl.one ((supply_fresh s0), Abind_flex_mono)) []);
          gr_type = (Ptyp_var_f (supply_fresh s0)) }
      | Pskl_tophole p0 -> e_guess_mono_impl s0 p0

      let e_guess_mono_run = e_guess_mono_impl
>>

    The domain predicate is gone; [lc_pskl] is gone (so [e_guess_mono_run]
    eta-reduces to the implementation); [sig] is gone.  No [Acc], no
    [Fix_sub], no [Obj.magic].  And [Print Assumptions] on
    [e_guess_mono_impl] / [e_guess_mono_run] / [e_guess_mono_run_sound] is
    "Closed under the global context" — [Equations] contributed no axiom.

    ⭐⭐ AND IT VINDICATES M1'S ONE STRUCTURAL CHANGE.  Set the [Pskl_arrow]
    branch beside [guess]'s own arrow case in the reference implementation
    (benchmark/Fresco/lib/type.ml:97-100):

<<
      | TArr (a, b) ->
        let l, a = aux l Any a in
        let l, b = aux l Any b in     (* the accumulator THREADS *)
        l, TArr (a, b)
>>

    [type.ml] threads its accumulator [l] through both halves.  So
    [a_guess_mono__arrow]'s running of both halves at the SAME [Θ] — the thing
    that costs [AT-Abs] its [uniq (αs ++ Θ1)] premise — is a departure from
    the implementation, and [e_guess_mono__arrow] is the faithful reading, not
    the convenient one.  Row for row the rest matches too: [l] is [gr_block],
    [incr counter] is [supply_fresh]+[add], [Bindlib.unbind]/[bind_var] are
    [open_pskl_wrt_pskl]/[close_ptyp_wrt_ptyp], and [UGhost p -> aux l k p] is
    the [Pskl_tophole] row.  ⚙ The one real difference left is accumulator
    SHAPE: [type.ml] conses onto a single [l], we concatenate two blocks.

    ⚠️ TWO EXTRACTION NOTES FOR WHOEVER WRITES THE REAL DRIVER.  (i) Coq warns
    "the extraction is currently set to bypass opacity" and names metalib's
    [atom_fresh] / [nat_list_max] — that is the [supply_fresh] opacity
    recorded in def_supply.v, and it is benign: extraction reads the module
    body and emits ordinary code.  (ii) WITHOUT [ExtrOcamlNatInt], metalib's
    atoms extract as UNARY [nat] ([S (nat_list_max xs)]), which is not a
    performance footnote but a wall.  McTT imports it in
    [theories/Entrypoint.v]; do the same. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.def_shapes.
Require Import src.frost.decl.def_rules.
Require Import src.frost.algo.def_rules.
Require Import src.frost.ext_algo.def_supply.
Require Import src.frost.ext_algo.def_uip.
Require Import src.frost.ext_algo.def_guess.

(* ⚠️ NO [Set Implicit Arguments] IN THIS FILE, unlike every other file in the
   tree.  Here it is actively wrong: [e_guess_mono_impl]'s [S0] and [P] are
   both inferable from its derivation argument [H], so the flag makes them
   IMPLICIT — and the RECURSIVE CALLS inside the [Equations] block then read
   [e_guess_mono_impl S0 P _] as passing [S0] for [H], with an error that
   names neither.  An implementation file also reads better with its arguments
   explicit, since they are the arguments the extracted OCaml takes. *)

(* ===================================================================== *)
(*  §1  The result                                                        *)
(* ===================================================================== *)

(** A record rather than a nested [sigT], so the extracted OCaml returns a
    named triple — the shape [type.ml] returns, and the shape a differential
    test can read.  ⚙ [sigT] would extract to bare nested pairs. *)
Record guess_result : Type := mk_guess_result {
  gr_supply : supply;      (* the supply the run leaves behind *)
  gr_block  : aenv;        (* Ξ — the invented flexibles *)
  gr_type   : ptyp         (* A — the monotype-filled painting *)
}.

Definition guess_spec (S0 : supply) (P : pskl) (r : guess_result) : Prop :=
  e_guess_mono S0 P (gr_supply r) (gr_block r) (gr_type r).

(** ⚠️ WRITE THE RETURN TYPE AS [sig (guess_spec S0 P)], NEVER AS
    [{ r | guess_spec S0 P r }].  The tree's meta-level substitution notations
    ([{ A' ᵗ/ₜ α } A], [{ e' ᵉ/ₑ x } e], [{ A ᵉ/ₜ α } e] — frost/notations.v:215)
    claim the [{ term …] prefix, so Coq's own [sig] notation no longer parses
    and the error names the substitution glyphs, mentioning neither [sig] nor
    the line's actual problem.  Every Bove–Capretta signature in ext_algo/ will
    hit this, since [sig] is the return type the whole pattern is built on. *)
Notation guess_res S0 P := (sig (guess_spec S0 P)).

(* ===================================================================== *)
(*  §2  The domain predicate                                              *)
(*                                                                        *)
(*  Read it as the CALL GRAPH, not as a second copy of the rules: it says  *)
(*  which recursive calls the function makes, and nothing about what they  *)
(*  return.  Two rows are worth a look:                                    *)
(*                                                                        *)
(*  - [ego_arrow]'s second premise is HIGHER-ORDER — it quantifies over    *)
(*    whatever the FIRST call produced.  That is what a threaded supply    *)
(*    forces (the right half starts at the left half's output), and it is  *)
(*    the McTT idiom for exactly this situation (cf. [eeo_natrec],         *)
(*    Evaluation.v:28).  ⚙ The guard checker copes: applying a structural  *)
(*    subterm of [H] to arguments still yields a subterm.                  *)
(*                                                                        *)
(*  - [ego_forall] names [supply_fresh S] rather than quantifying over a   *)
(*    fresh atom.  The domain predicate describes THIS implementation's    *)
(*    calls, and this implementation makes the deterministic choice; the   *)
(*    RELATION (def_guess.v) keeps the freedom, which is what makes the    *)
(*    bridge to frost/algo work.  Committing to the choice here is what    *)
(*    separates "the algorithm" from "an implementation of it".            *)
(* ===================================================================== *)

Inductive e_guess_mono_order : supply -> pskl -> Prop :=
| ego_hole : forall S,
    e_guess_mono_order S pskl_hole
| ego_tophole : forall S P,
    e_guess_mono_order S P ->
    e_guess_mono_order S (pskl_tophole P)
| ego_var : forall S α,
    e_guess_mono_order S (pskl_var_f α)
| ego_unit : forall S,
    e_guess_mono_order S pskl_unit
| ego_arrow : forall S P Q,
    e_guess_mono_order S P ->
    (forall S1 Ξ1 A, e_guess_mono S P S1 Ξ1 A -> e_guess_mono_order S1 Q) ->
    e_guess_mono_order S (pskl_arrow P Q)
| ego_forall : forall S P,
    e_guess_mono_order (add (supply_fresh S) S)
      (open_pskl_wrt_pskl P (pskl_var_f (supply_fresh S))) ->
    e_guess_mono_order S (pskl_all_syn P).

(** The one input shape with no call-graph row: a dangling de Bruijn index is
    not a skeleton any run can be given.  Eliminated into [False] — a Prop —
    so that §3's use of [False_rect] is empty elimination and not a
    Prop→Type escape. *)
Lemma e_guess_mono_order_var_b_absurd : forall S n,
  e_guess_mono_order S (pskl_var_b n) -> False.
Proof. intros * H; inversion H. Qed.

(* ===================================================================== *)
(*  §3  The function                                                      *)
(* ===================================================================== *)

(** The obligation tactic discharges TWO kinds of goal, and the order of the
    steps is what makes one tactic serve both:

    - the [_] standing for a recursive call's ORDER argument — got by
      inverting [H].  ⚙ It is also here that the guard condition is met: the
      inverted sub-derivation is a structural subterm of [H], which is what
      lets [by struct H] go through on a non-structural recursion.
    - the [_] standing for the branch's [guess_spec] proof — got by applying
      an [e_guess_mono] rule to the results of those calls.

    [unfold guess_spec in *] must come AFTER the inversion and BEFORE [eauto]:
    the arrow row's second call needs its order argument from
    [ego_arrow]'s higher-order premise applied to the FIRST call's result,
    and that result is in the context as a [guess_spec], which [eauto] cannot
    see through. *)
#[local] Ltac guess_impl_tac :=
  intros;
  try (match goal with H : e_guess_mono_order _ _ |- _ =>
         inversion H; subst end);
  unfold guess_spec in *; simpl in *;
  eauto using e_guess_mono, supply_fresh_notin.

#[tactic="guess_impl_tac", derive(equations=yes,eliminator=no)]
Equations e_guess_mono_impl (S0 : supply) (P : pskl)
    (H : e_guess_mono_order S0 P) : guess_res S0 P
  by struct H :=
| S0, pskl_hole, H =>
    exist _ (mk_guess_result (add (supply_fresh S0) S0)
               ((supply_fresh S0 ~ abind_flex_mono) ++ nil)
               (ptyp_var_f (supply_fresh S0))) _
| S0, pskl_var_f α, H => exist _ (mk_guess_result S0 nil (ptyp_var_f α)) _
| S0, pskl_unit, H => exist _ (mk_guess_result S0 nil ptyp_unit) _
| S0, pskl_tophole P, H =>
    let (r, Hr) := e_guess_mono_impl S0 P _ in
    exist _ r _
| S0, pskl_arrow P Q, H =>
    let (r1, H1) := e_guess_mono_impl S0 P _ in
    let (r2, H2) := e_guess_mono_impl (gr_supply r1) Q _ in
    exist _ (mk_guess_result (gr_supply r2)
               (gr_block r1 ++ gr_block r2)
               (ptyp_arrow (gr_type r1) (gr_type r2))) _
| S0, pskl_all_syn P, H =>
    let (r, Hr) := e_guess_mono_impl (add (supply_fresh S0) S0)
                     (open_pskl_wrt_pskl P (pskl_var_f (supply_fresh S0))) _ in
    exist _ (mk_guess_result (gr_supply r) (gr_block r)
               (ptyp_all (close_ptyp_wrt_ptyp (supply_fresh S0) (gr_type r)))) _
| S0, pskl_var_b n, H =>
    False_rect _ (e_guess_mono_order_var_b_absurd S0 n H).

(* ===================================================================== *)
(*  §4  Totality, and the runner                                          *)
(*                                                                        *)
(*  ⭐ THIS is where a termination argument would live, and for [guess^TY]  *)
(*  it is one line per row: the subject shrinks, and the ∀ row's           *)
(*  [open … (pskl_var_f _)] is covered by [lc_pskl]'s own cofinite         *)
(*  premise.  The point of the spike is that the FUNCTION above did not    *)
(*  have to wait for it.  For [a_sub] / [a_typing] this lemma is where the *)
(*  real measure will be owed — and only there.                            *)
(* ===================================================================== *)

Lemma e_guess_mono_order_total : forall P,
  lc_pskl P ->
  forall S0, e_guess_mono_order S0 P.
Proof.
  intros P Hlc;
    induction Hlc as [ | α | P1 P2 Hlc1 IH1 Hlc2 IH2 | P1 Hlc IH
                     | | P1 Hlc IH ];
    intros S0.
  - apply ego_unit.
  - apply ego_var.
  - apply ego_arrow; [ apply IH1 | intros; apply IH2 ].
  - apply ego_forall. apply IH.
  - apply ego_hole.
  - apply ego_tophole. apply IH.
Qed.

(** ⭐ THE RUNNER — no derivation argument, no fuel, no measure in its type.
    [lc_pskl P] is a genuine precondition on the input, not a termination
    certificate: it says the caller handed us a skeleton and not a dangling
    index. *)
Definition e_guess_mono_run (S0 : supply) (P : pskl) (H : lc_pskl P)
  : guess_result :=
  proj1_sig (e_guess_mono_impl S0 P (e_guess_mono_order_total P H S0)).

(** Runner soundness: what it returns is a real [guess^TY] run.  Composed with
    [e_guess_mono_sound] (prop_guess.v §3) this reaches [a_guess_mono], i.e.
    the encoding the four flagship theorems are stated over. *)
Lemma e_guess_mono_run_sound : forall S0 P (H : lc_pskl P),
  e_guess_mono S0 P
    (gr_supply (e_guess_mono_run S0 P H))
    (gr_block  (e_guess_mono_run S0 P H))
    (gr_type   (e_guess_mono_run S0 P H)).
Proof.
  intros S0 P H. unfold e_guess_mono_run.
  exact (proj2_sig (e_guess_mono_impl S0 P (e_guess_mono_order_total P H S0))).
Qed.

(** Runner completeness: every run the RELATION admits is the one the runner
    performs, up to the names the relation was free to choose.  ⚙ Stated as
    "the runner does not fail" because [e_guess_mono_run] is total — which is
    the whole point of §4; there is no [None] to rule out. *)
