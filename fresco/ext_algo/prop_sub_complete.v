(** ext_algo — §8c.11 / §8c.13, campaign level 6: the SUBTYPING runner's
    COMPLETENESS.

    §1  a strong-induction principle for [e_sub_call_order]
    §3  equivariance along a CHAIN, for [e_sub] / [e_sub_flex]
    §4  the ROOT INVERSIONS — §8c.11's overlap table, as lemmas
    §5  the [SI-Flex-Solve] REALIGNMENT, and §5b the three small pieces
        the SUB half needs ([swaps_pskl_open], the wf chain iteration,
        [split_at_tvar]'s completeness, [e_extract]'s inversion)
    §6  THE MOTIVE
    §7  THE MAIN INDUCTION — §7a the flex half, §7b the sub half,
        §7c the two joined through §1's principle
    §8  the three headlines

    ⭐ §4 IS THE LEVEL'S GOOD NEWS.  [guarded_pskl] is [unit | var | arrow]
    and NOTHING else, so [∀], [◇] and [⫯] are all UNGUARDED and every cell
    of the runner's dispatch admits EXACTLY ONE rule — including [◇ ⩽ ◇],
    where [SI-Ghost] and [SI-UnivGhostR] would otherwise have returned
    different answers.  Contrast level 5, whose §4 has three genuinely
    disjunctive cells.  The [e_sub_flex] side is overlap-free by
    construction, and at [TI] the only rule is [SI-Infer], hereditarily
    (the audit's one finding, fixed in `35a13b3`).

    ⭐⭐ WHAT THE MOTIVE OWES, AND WHY IT IS LEVEL 5's WITH ONE
    SIMPLIFICATION.  Level 5 relates the derivation's outputs to the
    runner's up to a SWAP CHAIN, and its output relation is a MATCH on the
    call tag because only the consistency tag carries an output skeleton.
    Here BOTH tags do ([e_sub] returns the counterpart, [e_sub_flex] returns
    it too), so the output conjunct is a plain EQUALITY at every tag.

    ⛔⛔ THE HISTORY, because it is the level's whole story.  The motive's
    SUPPLY conjunct, [swaps_atoms ps Sd [=] sb_supply r], was machine-checked
    FALSE three times over, each time because a DISPATCH GUARD was missing
    one layer down and the algorithm therefore answered the same query with
    two different amounts of fresh supply.  [SI-ForallL] runs an extraction,
    so every one of them reached this level:

    | refutation | the guard that retracts it |
    |---|---|
    | `cex/probe_extract_supply_drift.v` | ABSENCE-FIRST (§8c.14) |
    | `cex/probe_extract_flexr_ug2_drift.v` | FlexR-PRIORITY (§8c.16) |
    | `cex/probe_solve_sub_forall_r_drift.v` | SOLVE-DISPATCH (§8c.19) |

    All five guards are landed, and [e_extract_det]
    (`ext_algo/prop_extract_det.v` §9) is the statement they buy — the one
    [SI-ForallL] needs to move a derivation's extraction onto the runner's
    rails.  docs/HANDOFF-extractable-algo-encoding.md §8c.13–§8c.19.

    ✅ AND IT IS CLOSED (2026-08-18).  Three rows are the level's content
    and the rest is dispatch: [SI-Flex-Solve] (§5's TWO-name realignment —
    the second pair's left column is the name the FIRST transposition left
    [bd] at, not [bd]), [SI-ForallR] (pre-swap the opener, then
    [split_at_tvar]'s completeness reads the junk block back off the
    runner's own answer), and [SI-ForallL] (pre-swap the opener, then
    [e_extract_det]).

    ⛔ ONE UPSTREAM PREMISE HAD TO GO — not because it was wrong, but
    because it is UNSATISFIABLE at its only consumer, so a true lemma was
    unusable.  [e_extract_impl_complete] (prop_look_pair.v §4) carried
    [add α (ftv P ∪ ftv P') ⊆ ftvar Θ0], and at [SI-ForallL] the extract's
    [α] IS the rule's fresh opener, so [α ∈ ftvar Θ0] cannot hold.  ⚙
    Dropping it yields a STRICTLY STRONGER statement, so nothing that used
    the old form is disturbed (nothing did — see below).  The
    repair is local to that proof: cut the b-core's RIGID ENRICHMENT at
    [ftvar Θ0] rather than at the input supply, so the whole supply — hence
    [α], [ftv P] and [ftv P'] — is visible in the enriched contexts, and
    peel the two rigid prefixes by RIGIDITY rather than by freshness. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Bool.Sumbool.
Require Import Metalib.Metatheory.
From Equations Require Import Equations.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_coercions.
Require Import src.fresco.prop_tag.
Require Import src.fresco.prop_basic.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.prop_basic.
Require Import src.fresco.algo.prop_swap.
Require Import src.fresco.ext_algo.notations.
Require Import src.fresco.ext_algo.def_supply.
Require Import src.fresco.ext_algo.def_dec.
Require Import src.fresco.ext_algo.prop_dec.
Require Import src.fresco.ext_algo.def_guess.
Require Import src.fresco.ext_algo.prop_guess.
Require Import src.fresco.ext_algo.def_consis.
Require Import src.fresco.ext_algo.prop_consis.
Require Import src.fresco.ext_algo.def_look.
Require Import src.fresco.ext_algo.prop_look.
Require Import src.fresco.ext_algo.def_solve.
Require Import src.fresco.ext_algo.prop_solve.
Require Import src.fresco.ext_algo.def_extract.
Require Import src.fresco.ext_algo.prop_extract.
Require Import src.fresco.ext_algo.def_sub.
Require Import src.fresco.ext_algo.prop_sub.
Require Import src.fresco.ext_algo.def_order.
Require Import src.fresco.ext_algo.prop_termination.
Require Import src.fresco.ext_algo.prop_solve_det.
Require Import src.fresco.ext_algo.def_consis_impl.
Require Import src.fresco.ext_algo.prop_consis_complete.
Require Import src.fresco.ext_algo.def_extract_impl.
Require Import src.fresco.ext_algo.prop_extract_det.
Require Import src.fresco.ext_algo.prop_look_pair.
Require Import src.fresco.ext_algo.def_sub_impl.

Set Implicit Arguments.

Open Scope fresco_a_scope.
Open Scope fresco_e_scope.

(* ===================================================================== *)
(*  §1  Strong induction for [e_sub_call_order]                           *)
(*                                                                        *)
(*  prop_consis_complete.v §1's idiom, verbatim: the runner recurses on    *)
(*  the ORDER, so completeness must too, and the order's own [Induction]   *)
(*  scheme gives an IH only at the immediate sub-orders.  Hand-write the   *)
(*  principle with every RECURSIVE premise DOUBLED — the order premise     *)
(*  itself and its motive companion — so a case script may use either.     *)
(*                                                                        *)
(*  ⚙ Three premises have no companion because they are not recursive      *)
(*  calls of this block: [Check]'s [e_consis_order], [Arrow]'s first       *)
(*  conjunct (also an [e_consis_order]) and [ForallL]'s first conjunct     *)
(*  (an [e_extract_order]).                                               *)
(* ===================================================================== *)

Section e_sub_call_order_sind.

Variable Qc : supply -> a_sub_mode -> mode -> pskl -> aenv -> sub_call -> Prop.

Hypothesis Hsub : forall S0 NM M P0 Θ0 P,
    (* Check — one consistency run *)
    (M = mode_tc -> e_consis_order empty empty S0 Θ0 P0 P) ->
    (* ForallR — peel the pattern's quantifier *)
    (forall B,
       M = mode_tc -> P0 = pskl_all_syn B ->
       e_sub_call_order (add (supply_fresh S0) S0) a_sub_mode_ty mode_tc
         (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))
         ((supply_fresh S0 ~ abind_tvar) ++ Θ0) (sub_call_sub P)) ->
    (forall B,
       M = mode_tc -> P0 = pskl_all_syn B ->
       Qc (add (supply_fresh S0) S0) a_sub_mode_ty mode_tc
         (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))
         ((supply_fresh S0 ~ abind_tvar) ++ Θ0) (sub_call_sub P)) ->
    (* FlexMono — enter the walk *)
    (forall α M',
       P = pskl_var_f α -> M = mode_fn M' ->
       e_sub_call_order S0 NM M' P0 Θ0 (sub_call_flex nil α)) ->
    (forall α M',
       P = pskl_var_f α -> M = mode_fn M' ->
       Qc S0 NM M' P0 Θ0 (sub_call_flex nil α)) ->
    (* Arrow — the domain goes to consistency, the codomain stays *)
    (forall M' P0a P0b P1 P2,
       M = mode_fn M' -> P0 = pskl_arrow P0a P0b -> P = pskl_arrow P1 P2 ->
       e_consis_order empty empty S0 Θ0 P0a P1
       /\ (forall S1 Θ1 Q1,
             {{ S0 ↝ S1 ⊨ Θ0 ⊢[ empty | empty | P0a ] P1 ∼ Q1 ⊣ Θ1 }}e ->
             e_sub_call_order S1 NM M' P0b Θ1 (sub_call_sub P2))) ->
    (forall M' P0a P0b P1 P2,
       M = mode_fn M' -> P0 = pskl_arrow P0a P0b -> P = pskl_arrow P1 P2 ->
       forall S1 Θ1 Q1,
         {{ S0 ↝ S1 ⊨ Θ0 ⊢[ empty | empty | P0a ] P1 ∼ Q1 ⊣ Θ1 }}e ->
         Qc S1 NM M' P0b Θ1 (sub_call_sub P2)) ->
    (* ForallL — extract an instantiation, then recurse on the opened body *)
    (forall Q,
       P = pskl_all_syn Q -> M <> mode_ti ->
       (guarded_pskl P0 \/ P0 = pskl_ghost) ->
       e_extract_order (add (supply_fresh S0) S0) Θ0 NM (supply_fresh S0) M
         (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0))) P0
       /\ (forall S1 Ξ P1,
             {{ (add (supply_fresh S0) S0) ↝ S1 ⊨ Θ0
                ⊢ (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
                ⊳[ NM , (supply_fresh S0) , M ] P0 ⤳ Ξ ↪ P1 }}e ->
             {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a ->
             e_sub_call_order S1 NM M P0 (Ξ ++ Θ0)
               (sub_call_sub (open_pskl_wrt_pskl Q P1)))) ->
    (forall Q,
       P = pskl_all_syn Q -> M <> mode_ti ->
       (guarded_pskl P0 \/ P0 = pskl_ghost) ->
       forall S1 Ξ P1,
         {{ (add (supply_fresh S0) S0) ↝ S1 ⊨ Θ0
            ⊢ (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
            ⊳[ NM , (supply_fresh S0) , M ] P0 ⤳ Ξ ↪ P1 }}e ->
         {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a ->
         Qc S1 NM M P0 (Ξ ++ Θ0)
           (sub_call_sub (open_pskl_wrt_pskl Q P1))) ->
    (* UnivGhostL — strip the subject's ⫯ *)
    (forall Q,
       P = pskl_univ_ghost Q -> M <> mode_ti ->
       e_sub_call_order S0 NM M P0 Θ0 (sub_call_sub Q)) ->
    (forall Q,
       P = pskl_univ_ghost Q -> M <> mode_ti ->
       Qc S0 NM M P0 Θ0 (sub_call_sub Q)) ->
    Qc S0 NM M P0 Θ0 (sub_call_sub P).

Hypothesis Hflex : forall S0 NM M P0 Θ0 Ξ α,
    (* Flex-Solve — the head IS the target, undefined *)
    (forall Θ0',
       Θ0 = (α ~ abind_flex_mono) ++ Θ0' ->
       e_sub_call_order
         (add (supply_fresh (add (supply_fresh S0) S0))
            (add (supply_fresh S0) S0))
         NM (mode_fn M) P0
         (Ξ ++ (α ~ abind_flex_mono_def
                      (ptyp_arrow (ptyp_var_f (supply_fresh S0))
                         (ptyp_var_f (supply_fresh (add (supply_fresh S0) S0)))))
             ++ (supply_fresh (add (supply_fresh S0) S0) ~ abind_flex_mono)
             ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0')
         (sub_call_sub
            (pskl_arrow (pskl_var_f (supply_fresh S0))
               (pskl_var_f (supply_fresh (add (supply_fresh S0) S0)))))) ->
    (forall Θ0',
       Θ0 = (α ~ abind_flex_mono) ++ Θ0' ->
       Qc (add (supply_fresh (add (supply_fresh S0) S0))
             (add (supply_fresh S0) S0))
         NM (mode_fn M) P0
         (Ξ ++ (α ~ abind_flex_mono_def
                      (ptyp_arrow (ptyp_var_f (supply_fresh S0))
                         (ptyp_var_f (supply_fresh (add (supply_fresh S0) S0)))))
             ++ (supply_fresh (add (supply_fresh S0) S0) ~ abind_flex_mono)
             ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0')
         (sub_call_sub
            (pskl_arrow (pskl_var_f (supply_fresh S0))
               (pskl_var_f (supply_fresh (add (supply_fresh S0) S0)))))) ->
    (* Flex-Assign — a defined head is substituted away and dropped *)
    (forall β τ Θ0',
       Θ0 = (β ~ abind_flex_mono_def τ) ++ Θ0' ->
       e_sub_call_order S0 NM (mode_fn M)
         (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
         (Ξ ++ Θ0')
         (sub_call_sub
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)))) ->
    (forall β τ Θ0',
       Θ0 = (β ~ abind_flex_mono_def τ) ++ Θ0' ->
       Qc S0 NM (mode_fn M)
         (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
         (Ξ ++ Θ0')
         (sub_call_sub
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)))) ->
    (* Flex-Depend / Flex-Skip — an undefined non-target head *)
    (forall β Θ0',
       Θ0 = (β ~ abind_flex_mono) ++ Θ0' ->
       e_sub_call_order S0 NM M P0 Θ0'
         (sub_call_flex (Ξ ++ (β ~ abind_flex_mono)) α)
       /\ e_sub_call_order S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (forall β Θ0',
       Θ0 = (β ~ abind_flex_mono) ++ Θ0' ->
       Qc S0 NM M P0 Θ0' (sub_call_flex (Ξ ++ (β ~ abind_flex_mono)) α)
       /\ Qc S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (* Flex-SkipRigid *)
    (forall β Θ0',
       Θ0 = (β ~ abind_tvar) ++ Θ0' ->
       e_sub_call_order S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (forall β Θ0',
       Θ0 = (β ~ abind_tvar) ++ Θ0' ->
       Qc S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (* Flex-SkipTmVar, both payload sorts *)
    (forall x A Θ0',
       Θ0 = (x ~ abind_var_typ A) ++ Θ0' ->
       e_sub_call_order S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (forall x A Θ0',
       Θ0 = (x ~ abind_var_typ A) ++ Θ0' ->
       Qc S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (forall x Q Θ0',
       Θ0 = (x ~ abind_var_skl Q) ++ Θ0' ->
       e_sub_call_order S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (forall x Q Θ0',
       Θ0 = (x ~ abind_var_skl Q) ++ Θ0' ->
       Qc S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    Qc S0 NM M P0 Θ0 (sub_call_flex Ξ α).

Fixpoint e_sub_call_order_sind S0 NM M P0 Θ0 c
    (H : e_sub_call_order S0 NM M P0 Θ0 c) {struct H} : Qc S0 NM M P0 Θ0 c :=
  match H in e_sub_call_order S0' NM' M' P0' Θ0' c'
        return Qc S0' NM' M' P0' Θ0' c' with
  | e_sub_call_order__sub _ _ _ _ _ _ p1 p2 p3 p4 p5 p6 =>
      @Hsub _ _ _ _ _ _
        p1
        p2
        (fun B E1 E2 => e_sub_call_order_sind (p2 B E1 E2))
        p3
        (fun α M' E1 E2 => e_sub_call_order_sind (p3 α M' E1 E2))
        p4
        (fun M' P0a P0b P1 P2 E1 E2 E3 S1 Θ1 Q1 Hrun =>
           match p4 M' P0a P0b P1 P2 E1 E2 E3 with
           | conj _ Hrec => e_sub_call_order_sind (Hrec S1 Θ1 Q1 Hrun)
           end)
        p5
        (fun Q E1 E2 Hg S1 Ξ P1 Hrun Hwf =>
           match p5 Q E1 E2 Hg with
           | conj _ Hrec => e_sub_call_order_sind (Hrec S1 Ξ P1 Hrun Hwf)
           end)
        p6
        (fun Q E1 E2 => e_sub_call_order_sind (p6 Q E1 E2))
  | e_sub_call_order__flex _ _ _ _ _ _ _ q1 q2 q3 q4 q5 q6 =>
      @Hflex _ _ _ _ _ _ _
        q1
        (fun Θ0' E => e_sub_call_order_sind (q1 Θ0' E))
        q2
        (fun β τ Θ0' E => e_sub_call_order_sind (q2 β τ Θ0' E))
        q3
        (fun β Θ0' E =>
           match q3 β Θ0' E with
           | conj Ha Hb =>
               conj (e_sub_call_order_sind Ha) (e_sub_call_order_sind Hb)
           end)
        q4
        (fun β Θ0' E => e_sub_call_order_sind (q4 β Θ0' E))
        q5
        (fun x A Θ0' E => e_sub_call_order_sind (q5 x A Θ0' E))
        q6
        (fun x Q Θ0' E => e_sub_call_order_sind (q6 x Q Θ0' E))
  end.

End e_sub_call_order_sind.

(* ===================================================================== *)
(*  §3  EQUIVARIANCE ALONG A CHAIN                                        *)
(*                                                                        *)
(*  prop_consis_complete.v §3's iteration, for this level's judgements.    *)
(*  What consumes it: [SI-Arrow] and [SI-ForallL] run their second premise *)
(*  at the FIRST premise's output, and by then the derivation's names and  *)
(*  the runner's differ by a whole CHAIN of transpositions, not one.       *)
(* ===================================================================== *)

Lemma e_sub_swaps : forall ps S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  forall S0', S0' [=] swaps_atoms ps S0 ->
  exists S1', S1' [=] swaps_atoms ps S1 /\
    {{ S0' ↝ S1' ⊨ (swaps_aenv ps Θ0) ⊢[ NM | M | (swaps_pskl ps P0) ]
       (swaps_pskl ps P) ⩽ (swaps_pskl ps Q) ⊣ (swaps_aenv ps Θ1) }}e.
Proof.
  induction ps as [ | [a b] ps IH ]; intros * Hd S0' Heq; simpl in *.
  - (* the empty chain moves nothing but the supply *)
    exact (e_sub_supply_respect Hd Heq).
  - assert (Hr : swap_atoms a b S0 [=] swap_atoms a b S0) by reflexivity.
    destruct (e_sub_swap Hd Hr) as [S1a [HS1a Hda]].
    destruct (IH _ _ _ _ _ _ _ _ _ Hda _ Heq) as [S1' [HS1' Hd']].
    exists S1'. split; [ | exact Hd' ].
    rewrite HS1'. apply swaps_atoms_cong. exact HS1a.
Qed.

(** ⚙ [a_suffix] survives a chain, which is what [SI-ForallR]'s
    [split_at_tvar] step below needs of the transported junk block. *)
Lemma a_suffix_swaps : forall ps (Ξ : aenv),
  a_suffix Ξ -> a_suffix (swaps_aenv ps Ξ).
Proof.
  induction ps as [ | [a b] ps IH ]; intros Ξ Hs; simpl; [ exact Hs | ].
  apply IH. apply a_suffix_swap. exact Hs.
Qed.

(* ===================================================================== *)
(*  §4  ROOT INVERSIONS — the case backbone, machine-checked              *)
(*                                                                        *)
(*  §8c.11's overlap table as lemmas: one per clause of the runner's       *)
(*  dispatch, each turning a derivation at the clause's shape into that    *)
(*  rule's premises — or into [False] where the runner rejects.  ⭐ Every  *)
(*  one is a SINGLE rule, no disjunctions: [guarded_pskl] is               *)
(*  [unit | var | arrow] and nothing else, so the ∀ / ◇ / ⫯ overlaps the   *)
(*  rule list suggests are all vacuous, and the [e_sub_flex] side is       *)
(*  keyed to distinct binding shapes.  (Contrast level 5, whose §4 has     *)
(*  three genuinely disjunctive cells.)                                    *)
(* ===================================================================== *)

(** After [inversion], the rows that COULD have matched the shape but demand
    [guarded_pskl] of a ∀ / ⫯ / ◇ leave that demand behind; it is never
    derivable, so one [inversion] each closes them. *)
Local Ltac kill_unguarded :=
  repeat match goal with
         | Hg : guarded_pskl (pskl_all_syn _) |- _ => solve [ inversion Hg ]
         | Hg : guarded_pskl (pskl_univ_ghost _) |- _ => solve [ inversion Hg ]
         | Hg : guarded_pskl pskl_ghost |- _ => solve [ inversion Hg ]
         end.

(** [SI-ForallL]'s own guard, at a counterpart that is neither guarded nor
    a ghost — the shape that kills it beside [SI-ForallR]. *)
Local Ltac kill_forall_l_guard :=
  repeat match goal with
         | Hg : guarded_pskl ?X \/ ?X = pskl_ghost |- _ =>
             solve [ destruct Hg as [Hg | Hg];
                     [ inversion Hg | discriminate ] ]
         end.

(* --- the mode dispatch: at TI only SI-Infer, hereditarily (`35a13b3`) --- *)

Lemma e_sub_inv_ti : forall S0 NM P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | mode_ti | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  P0 = pskl_ghost /\ Q = P /\ S1 = S0 /\ Θ1 = Θ0.
Proof.
  intros * Hd. inversion Hd; subst; try congruence.
  repeat split; reflexivity.
Qed.

(* --- (ty, tc) --- *)

Lemma e_sub_inv_forall_r : forall S0 Θ0 B P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_ty | mode_tc | (pskl_all_syn B) ]
     P ⩽ Q ⊣ Θ1 }}e ->
  Q = pskl_all_syn B /\ pskl_ghost_free (pskl_all_syn B) /\
  exists α Ξ,
    a_suffix Ξ /\ uniq (Ξ ++ Θ0) /\ α `notin` S0 /\
    {{ (add α S0) ↝ S1 ⊨ ((α ~ abind_tvar) ++ Θ0)
       ⊢[ a_sub_mode_ty | mode_tc | (open_pskl_wrt_pskl B (pskl_var_f α)) ]
       P ⩽ (open_pskl_wrt_pskl B (pskl_var_f α))
       ⊣ (Ξ ++ (α ~ abind_tvar) ++ Θ1) }}e.
Proof.
  intros * Hd. inversion Hd; subst; kill_unguarded; kill_forall_l_guard.
  split; [ reflexivity | split; [ assumption | eauto 10 ] ].
Qed.

Lemma e_sub_inv_check : forall S0 Θ0 P0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_ty | mode_tc | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  (forall B, P0 <> pskl_all_syn B) ->
  (forall B, P <> pskl_all_syn B) ->
  Q = P0 /\ pskl_ghost_free P /\ pskl_ghost_free P0 /\
  guarded_pskl P /\ guarded_pskl P0 /\ e_consis_chk S0 Θ0 P P0 S1 Θ1.
Proof.
  intros * Hd Hn0 Hn. inversion Hd; subst;
    try solve [ exfalso; eapply Hn0; reflexivity
              | exfalso; eapply Hn; reflexivity ].
  repeat split; assumption.
Qed.

(* --- the subject is a ∀: [SI-ForallL], at every mode that admits it --- *)

(** ⚙ A plain inversion would need [P0 <> ∀], which is there for exactly ONE
    competing row, [SI-ForallR] — and that row also demands [NM = ty] and
    [M = TC].  The runner reaches [SI-ForallL] from three arms, and only
    the [(ty, TC)] one has already fixed the subject's shape, so state the
    inversion over the DISJUNCTION the three arms discharge differently. *)
Lemma e_sub_inv_forall_l_gen : forall S0 NM M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | M | P0 ] (pskl_all_syn P) ⩽ Q ⊣ Θ1 }}e ->
  M <> mode_ti ->
  (NM = a_sub_mode_sk \/ M <> mode_tc \/ (forall B, P0 <> pskl_all_syn B)) ->
  (guarded_pskl P0 \/ P0 = pskl_ghost) /\
  exists α Sm Ξ P1,
    α `notin` S0 /\
    {{ (add α S0) ↝ Sm ⊨ Θ0 ⊢ (open_pskl_wrt_pskl P (pskl_var_f α))
       ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ P1 }}e /\
    {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a /\
    {{ Sm ↝ S1 ⊨ (Ξ ++ Θ0) ⊢[ NM | M | P0 ]
       (open_pskl_wrt_pskl P P1) ⩽ Q ⊣ Θ1 }}e.
Proof.
  intros * Hd Hti Hor. inversion Hd; subst; kill_unguarded;
    try solve [ congruence
              | destruct Hor as [Ho | [Ho | Ho]];
                solve [ discriminate | congruence
                      | exfalso; eapply Ho; reflexivity ] ].
  split; [ assumption | eauto 10 ].
Qed.

(* --- (sk, M ≠ TI) --- *)

Lemma e_sub_inv_ghost : forall S0 M P0 Θ0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | M | P0 ] pskl_ghost ⩽ Q ⊣ Θ1 }}e ->
  M <> mode_ti ->
  Q = P0 /\ S1 = S0 /\ Θ1 = Θ0.
Proof.
  intros * Hd Hti. inversion Hd; subst; kill_unguarded; try congruence.
  repeat split; reflexivity.
Qed.

Lemma e_sub_inv_univ_ghost_l : forall S0 M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | M | P0 ] (pskl_univ_ghost P) ⩽ Q ⊣ Θ1 }}e ->
  M <> mode_ti ->
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | M | P0 ] P ⩽ Q ⊣ Θ1 }}e.
Proof.
  intros * Hd Hti. inversion Hd; subst; kill_unguarded;
    solve [ congruence | assumption ].
Qed.

(** ⭐ The audit's dangerous-looking cell, and it is not: [UnivGhostR] wants
    a GUARDED subject, so at [◇ ⩽ ◇] only [SI-Ghost] fires and the two
    would-be outputs never meet. *)
Lemma e_sub_inv_univ_ghost_r : forall S0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | mode_tc | pskl_ghost ] P ⩽ Q ⊣ Θ1 }}e ->
  P <> pskl_ghost -> (forall Pb, P <> pskl_univ_ghost Pb) ->
  (forall Pb, P <> pskl_all_syn Pb) ->
  guarded_pskl P /\ Q = pskl_univ_ghost P /\ S1 = S0 /\ Θ1 = Θ0.
Proof.
  intros * Hd Hnh Hnt Hna. inversion Hd; subst;
    try solve [ congruence
              | exfalso; eapply Hnt; reflexivity
              | exfalso; eapply Hna; reflexivity ].
  repeat split; solve [ assumption | reflexivity ].
Qed.

(** The runner's [None] at [(sk, tc)] with a guarded subject and a
    non-ghost counterpart: no rule fires there either. *)
Lemma e_sub_inv_sk_tc_none : forall S0 P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_sk | mode_tc | P0 ] P ⩽ Q ⊣ Θ1 }}e ->
  P <> pskl_ghost -> (forall Pb, P <> pskl_univ_ghost Pb) ->
  (forall Pb, P <> pskl_all_syn Pb) -> P0 <> pskl_ghost -> False.
Proof.
  intros * Hd Hnh Hnt Hna Hn0. inversion Hd; subst;
    solve [ congruence
          | exfalso; eapply Hnt; reflexivity
          | exfalso; eapply Hna; reflexivity ].
Qed.

(* --- (fn) --- *)

Lemma e_sub_inv_arrow : forall S0 NM M P0a P0b Θ0 P1 P2 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | (mode_fn M) | (pskl_arrow P0a P0b) ]
     (pskl_arrow P1 P2) ⩽ Q ⊣ Θ1 }}e ->
  exists Sm Θm Q1 Q2,
    Q = pskl_arrow Q1 Q2 /\
    {{ S0 ↝ Sm ⊨ Θ0 ⊢[ empty | empty | P0a ] P1 ∼ Q1 ⊣ Θm }}e /\
    {{ Sm ↝ S1 ⊨ Θm ⊢[ NM | M | P0b ] P2 ⩽ Q2 ⊣ Θ1 }}e.
Proof.
  intros * Hd. inversion Hd; subst; kill_unguarded. eauto 10.
Qed.

Lemma e_sub_inv_arrow_none : forall S0 NM M P0 Θ0 P1 P2 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | (mode_fn M) | P0 ] (pskl_arrow P1 P2) ⩽ Q ⊣ Θ1 }}e ->
  (forall A B, P0 <> pskl_arrow A B) -> False.
Proof.
  intros * Hd Hn0. inversion Hd; subst;
    solve [ congruence | exfalso; eapply Hn0; reflexivity ].
Qed.

Lemma e_sub_inv_flex_mono : forall S0 NM M P0 Θ0 α Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | (mode_fn M) | P0 ] (pskl_var_f α) ⩽ Q ⊣ Θ1 }}e ->
  e_sub_flex S0 NM M P0 Θ0 nil α Q S1 Θ1.
Proof. intros * Hd. inversion Hd; subst; kill_unguarded. assumption. Qed.

Lemma e_sub_inv_fn_unit_none : forall S0 NM M P0 Θ0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ NM | (mode_fn M) | P0 ] pskl_unit ⩽ Q ⊣ Θ1 }}e -> False.
Proof. intros * Hd. inversion Hd. Qed.

Lemma e_sub_inv_fn_ty_ghost_none : forall S0 M P0 Θ0 Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_ty | (mode_fn M) | P0 ]
     pskl_ghost ⩽ Q ⊣ Θ1 }}e -> False.
Proof. intros * Hd. inversion Hd. Qed.

Lemma e_sub_inv_fn_ty_univ_ghost_none : forall S0 M P0 Θ0 P Q S1 Θ1,
  {{ S0 ↝ S1 ⊨ Θ0 ⊢[ a_sub_mode_ty | (mode_fn M) | P0 ]
     (pskl_univ_ghost P) ⩽ Q ⊣ Θ1 }}e -> False.
Proof. intros * Hd. inversion Hd. Qed.

(* --- the WALK: one inversion per head binding shape --------------------- *)

Lemma e_sub_flex_inv_nil : forall S0 NM M P0 Ξ α Q S1 Θ1,
  e_sub_flex S0 NM M P0 nil Ξ α Q S1 Θ1 -> False.
Proof. intros * Hd. inversion Hd. Qed.

(** The head IS the target: only [SI-Flex-Solve] — every other row of the
    walk demands [α <> β] or a different binding shape. *)
Lemma e_sub_flex_inv_self : forall S0 NM M P0 Θ0 Ξ α Q S1 Θ1,
  e_sub_flex S0 NM M P0 ((α ~ abind_flex_mono) ++ Θ0) Ξ α Q S1 Θ1 ->
  exists a1 b1, a1 `notin` S0 /\ b1 `notin` add a1 S0 /\
    {{ (add b1 (add a1 S0)) ↝ S1 ⊨
       (Ξ ++ (α ~ abind_flex_mono_def
                    (ptyp_arrow (ptyp_var_f a1) (ptyp_var_f b1)))
           ++ (b1 ~ abind_flex_mono) ++ (a1 ~ abind_flex_mono) ++ Θ0)
       ⊢[ NM | (mode_fn M) | P0 ]
       (pskl_arrow (pskl_var_f a1) (pskl_var_f b1)) ⩽ Q ⊣ Θ1 }}e.
Proof.
  intros * Hd. inversion Hd; subst; try congruence. eauto 10.
Qed.

Lemma e_sub_flex_inv_other_flex : forall S0 NM M P0 Θ0 Ξ α β Q S1 Θ1,
  α <> β ->
  e_sub_flex S0 NM M P0 ((β ~ abind_flex_mono) ++ Θ0) Ξ α Q S1 Θ1 ->
  (β `in` ftvar_in_pskl P0 /\
     e_sub_flex S0 NM M P0 Θ0 (Ξ ++ (β ~ abind_flex_mono)) α Q S1 Θ1)
  \/ (β `notin` ftvar_in_pskl P0 /\ exists Θ1',
        Θ1 = (β ~ abind_flex_mono) ++ Θ1' /\
        e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1').
Proof.
  intros * Hne Hd. inversion Hd; subst; try congruence.
  - left; split; assumption.
  - right; split; [ assumption | eauto ].
Qed.

Lemma e_sub_flex_inv_def : forall S0 NM M P0 Θ0 Ξ α β τ Q S1 Θ1,
  e_sub_flex S0 NM M P0 ((β ~ abind_flex_mono_def τ) ++ Θ0) Ξ α Q S1 Θ1 ->
  exists Θ1', Θ1 = (β ~ abind_flex_mono_def τ) ++ Θ1' /\
    {{ S0 ↝ S1 ⊨ (Ξ ++ Θ0)
       ⊢[ NM | (mode_fn M) | (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0) ]
       (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)) ⩽ Q
       ⊣ Θ1' }}e.
Proof. intros * Hd. inversion Hd; subst. eauto. Qed.

Lemma e_sub_flex_inv_tvar : forall S0 NM M P0 Θ0 Ξ α β Q S1 Θ1,
  e_sub_flex S0 NM M P0 ((β ~ abind_tvar) ++ Θ0) Ξ α Q S1 Θ1 ->
  α <> β /\ β `notin` ftvar_in_pskl P0 /\ exists Θ1',
    Θ1 = (β ~ abind_tvar) ++ Θ1' /\ e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1'.
Proof.
  intros * Hd. inversion Hd; subst.
  split; [ assumption | split; [ assumption | eauto ] ].
Qed.

Lemma e_sub_flex_inv_var_typ : forall S0 NM M P0 Θ0 Ξ α x A Q S1 Θ1,
  e_sub_flex S0 NM M P0 ((x ~ abind_var_typ A) ++ Θ0) Ξ α Q S1 Θ1 ->
  exists Θ1', Θ1 = (x ~ abind_var_typ A) ++ Θ1' /\
    e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1'.
Proof. intros * Hd. inversion Hd; subst. eauto. Qed.

Lemma e_sub_flex_inv_var_skl : forall S0 NM M P0 Θ0 Ξ α x Qp Q S1 Θ1,
  e_sub_flex S0 NM M P0 ((x ~ abind_var_skl Qp) ++ Θ0) Ξ α Q S1 Θ1 ->
  exists Θ1', Θ1 = (x ~ abind_var_skl Qp) ++ Θ1' /\
    e_sub_flex S0 NM M P0 Θ0 Ξ α Q S1 Θ1'.
Proof. intros * Hd. inversion Hd; subst. eauto. Qed.


(* ===================================================================== *)
(*  §5  THE [SI-Flex-Solve] REALIGNMENT                                   *)
(*                                                                        *)
(*  §8c.20's one non-routine row, packaged.  [SI-Flex-Solve] invents TWO   *)
(*  names at once, and the derivation's pair [(ad, bd)] is only known to   *)
(*  dodge [S0] and [add ad S0]; the runner's is [supply_fresh]'s.  ONE     *)
(*  chain realigns them, and it is not the naive [(ad,a1)::(bd,b1)]: the   *)
(*  first transposition may already have moved [bd] (namely when           *)
(*  [bd = a1]), so the second pair's LEFT column has to be the moved name  *)
(*  [swap_atom ad a1 bd].  ⚙ With the derivation on the runner's rails the *)
(*  motive premise applies verbatim.                                      *)
(* ===================================================================== *)

Lemma e_sub_flex_solve_realign : forall S0 NM M P0 Θ0' Ξ α Qd Sd Θd ad bd,
  ad `notin` S0 -> bd `notin` add ad S0 ->
  ftvar_in_aenv (Ξ ++ Θ0') ∪ ftvar_in_pskl P0 ∪ singleton α [<=] S0 ->
  {{ (add bd (add ad S0)) ↝ Sd ⊨
     (Ξ ++ (α ~ abind_flex_mono_def
                  (ptyp_arrow (ptyp_var_f ad) (ptyp_var_f bd)))
         ++ (bd ~ abind_flex_mono) ++ (ad ~ abind_flex_mono) ++ Θ0')
     ⊢[ NM | (mode_fn M) | P0 ]
     (pskl_arrow (pskl_var_f ad) (pskl_var_f bd)) ⩽ Qd ⊣ Θd }}e ->
  exists ps0 Sd',
    (forall a b, In (a, b) ps0 -> a `notin` S0 /\ b `notin` S0)
    /\ Sd' [=] swaps_atoms ps0 Sd
    /\ {{ (add (supply_fresh (add (supply_fresh S0) S0))
             (add (supply_fresh S0) S0)) ↝ Sd' ⊨
       (Ξ ++ (α ~ abind_flex_mono_def
                    (ptyp_arrow (ptyp_var_f (supply_fresh S0))
                       (ptyp_var_f (supply_fresh (add (supply_fresh S0) S0)))))
           ++ (supply_fresh (add (supply_fresh S0) S0) ~ abind_flex_mono)
           ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0')
       ⊢[ NM | (mode_fn M) | P0 ]
       (pskl_arrow (pskl_var_f (supply_fresh S0))
          (pskl_var_f (supply_fresh (add (supply_fresh S0) S0))))
       ⩽ (swaps_pskl ps0 Qd) ⊣ (swaps_aenv ps0 Θd) }}e.
Proof.
  intros * Had Hbd Hcov Ds.
  assert (Hswl : forall x y, swap_atom x y x = y).
  { intros x y. unfold swap_atom.
    destruct (x == x) as [_ | Hc]; [ reflexivity | contradiction ]. }
  remember (supply_fresh S0) as a1 eqn:Ea1.
  remember (supply_fresh (add a1 S0)) as b1 eqn:Eb1.
  assert (Ha1 : a1 `notin` S0) by (subst a1; apply supply_fresh_notin).
  assert (Hb1 : b1 `notin` add a1 S0) by (subst b1; apply supply_fresh_notin).
  clear Ea1 Eb1.
  remember (swap_atom ad a1 bd) as c eqn:Ec.
  assert (Hbdad : bd <> ad) by (clear - Hbd; fsetdec).
  assert (Hc : c `notin` add a1 S0).
  { subst c. unfold swap_atom.
    destruct (bd == ad) as [Hc1 | Hne1]; [ contradiction | ].
    destruct (bd == a1) as [Hc2 | Hne2].
    - assert (Hada1 : ad <> a1) by congruence. clear - Had Hada1. fsetdec.
    - clear - Hbd Hne2. fsetdec. }
  assert (Hav : forall a b, In (a, b) ((ad, a1) :: (c, b1) :: nil) ->
                a `notin` S0 /\ b `notin` S0).
  { intros a b [Heq | [Heq | []]]; inversion Heq; subst;
      solve [ split; assumption
            | split; [ clear - Hc; fsetdec | clear - Hb1; fsetdec ] ]. }
  (* the chain's action on the two names the row invents *)
  assert (Hsad : swaps_atom ((ad, a1) :: (c, b1) :: nil) ad = a1).
  { simpl. rewrite Hswl.
    apply swap_atom_other; [ clear - Hc | clear - Hb1 ]; fsetdec. }
  assert (Hsbd : swaps_atom ((ad, a1) :: (c, b1) :: nil) bd = b1).
  { simpl. rewrite <- Ec. rewrite Hswl. reflexivity. }
  (* everything the ROW does not invent is fixed by the chain *)
  assert (Hfixa : forall (x : atom), x `in` S0 ->
            swaps_atom ((ad, a1) :: (c, b1) :: nil) x = x).
  { intros x Hx. apply swaps_atom_notin. intros a b Hin.
    destruct (Hav a b Hin) as [Ha Hb]. split; intros ->; contradiction. }
  assert (HfixΘ : forall (Θ : aenv), ftvar_in_aenv Θ [<=] S0 ->
            swaps_aenv ((ad, a1) :: (c, b1) :: nil) Θ = Θ).
  { intros Θ HΘ. apply swaps_aenv_fresh_id. intros a b Hin.
    destruct (Hav a b Hin) as [Ha Hb]. split; fsetdec. }
  assert (HfixP : forall P, ftvar_in_pskl P [<=] S0 ->
            swaps_pskl ((ad, a1) :: (c, b1) :: nil) P = P).
  { intros P HP. apply swaps_pskl_fresh_id. intros a b Hin.
    destruct (Hav a b Hin) as [Ha Hb]. split; fsetdec. }
  rewrite ftvar_in_aenv_app in Hcov.
  destruct (e_sub_swaps ((ad, a1) :: (c, b1) :: nil) Ds
              (S0' := add b1 (add a1 S0))) as [Sd' [HSd' Ds']].
  { rewrite swaps_atoms_add, swaps_atoms_add, Hsad, Hsbd.
    rewrite (swaps_atoms_notin _ _ Hav). reflexivity. }
  exists ((ad, a1) :: (c, b1) :: nil), Sd'.
  split; [ exact Hav | ]. split; [ exact HSd' | ].
  (* rewrite the transported context and subject onto the runner's rails *)
  repeat rewrite swaps_aenv_app_dist in Ds'.
  rewrite swaps_aenv_one_def, swaps_aenv_one_flex, swaps_aenv_one_flex in Ds'.
  rewrite swaps_ptyp_arrow, swaps_ptyp_var_f, swaps_ptyp_var_f in Ds'.
  rewrite swaps_pskl_arrow, swaps_pskl_var_f, swaps_pskl_var_f in Ds'.
  rewrite Hsad, Hsbd in Ds'.
  rewrite (Hfixa α) in Ds' by (clear - Hcov; fsetdec).
  rewrite (HfixΘ Ξ) in Ds' by (clear - Hcov; fsetdec).
  rewrite (HfixΘ Θ0') in Ds' by (clear - Hcov; fsetdec).
  rewrite (HfixP P0) in Ds' by (clear - Hcov; fsetdec).
  exact Ds'.
Qed.

(* ⚠️ [Set Implicit Arguments] leaves [Ξ] / [Θ0'] EXPLICIT — they occur only
   under [++], which is not a strict position — so the caller would have to
   count underscores.  Pin the whole prefix instead. *)
Arguments e_sub_flex_solve_realign {S0 NM M P0 Θ0' Ξ α Qd Sd Θd ad bd} _ _ _ _.

(* --------------------------------------------------------------------- *)
(*  §5b  Two chain iterations and one decomposition the SUB half needs     *)
(* --------------------------------------------------------------------- *)

Lemma swaps_pskl_open : forall ps P1 P2,
  swaps_pskl ps (open_pskl_wrt_pskl P1 P2)
  = open_pskl_wrt_pskl (swaps_pskl ps P1) (swaps_pskl ps P2).
Proof.
  induction ps as [ | [a b] ps IH ]; intros; simpl; [ reflexivity | ].
  rewrite swap_pskl_open. apply IH.
Qed.

(** [SI-ForallL]'s wf side condition, moved onto the runner's rails.  ⚙ The
    Δ index is [empty] at every call site, and a swap fixes it. *)
Lemma a_wf_pskl_swaps : forall ps (Θ : aenv) P,
  {{ Θ ⨟ empty ⊢ₚₛ P }}a ->
  {{ (swaps_aenv ps Θ) ⨟ empty ⊢ₚₛ (swaps_pskl ps P) }}a.
Proof.
  induction ps as [ | [a b] ps IH ]; intros Θ P H; simpl; [ exact H | ].
  apply IH. eapply a_wf_pskl_swap;
    [ exact H | symmetry; apply swap_atoms_empty ].
Qed.

(** ⭐ [SI-ForallR]'s decomposition step, in prop_dec.v §6's shape: on the
    context the rule produces, [split_at_tvar] SUCCEEDS and returns the
    rule's own two pieces.  ⚠️ Same caveat as [split_at_key_skl_complete]:
    the scan stops at the FIRST marker, so it agrees with the derivation's
    decomposition only because the context is [uniq] — which is what the
    premise's own soundness supplies. *)
Lemma split_at_tvar_complete : forall α Θ Ξ Θ',
  Θ = Ξ ++ (α ~ abind_tvar) ++ Θ' -> uniq Θ ->
  exists r, split_at_tvar α Θ = Some r /\ proj1_sig r = (Ξ, Θ').
Proof.
  intros α Θ Ξ Θ' -> Hu. revert Θ' Hu.
  induction Ξ as [ | [y b] Ξ' IH ]; intros Θ' Hu.
  - simpl. destruct (abind_is_tvar_dec abind_tvar) as [Hb | Hb];
      [ | congruence ].
    destruct (α == α) as [Heq | Hne]; [ | congruence ].
    eexists. split; reflexivity.
  - simpl in Hu |- *. inversion Hu; subst.
    destruct (IH Θ' ltac:(assumption)) as [[t Ht] [Hr Hpr]].
    simpl in Hpr; subst t.
    change (α ~ abind_tvar ++ Θ') with ((α, abind_tvar) :: Θ') in Hr.
    assert (Hαy : α <> y) by (simpl_env in *; fsetdec).
    destruct (abind_is_tvar_dec b) as [Hb | Hb].
    + destruct (α == y) as [Heq | Hne]; [ congruence | ].
      rewrite Hr. eexists. split; reflexivity.
    + rewrite Hr. eexists. split; reflexivity.
Qed.

(* ⚠️ Pin the prefix: [Set Implicit Arguments] leaves the three contexts in
   inconsistent slots, and the caller would have to count underscores. *)
Arguments split_at_tvar_complete {α Θ Ξ Θ'} _ _.

(* ===================================================================== *)
(*  §6  THE MOTIVE                                                        *)
(*                                                                        *)
(*  prop_consis_complete.v §6's shape, with the ONE simplification §8c.13  *)
(*  predicted: both call tags carry an output skeleton, so the output      *)
(*  conjunct is a plain EQUALITY rather than a tag-keyed match.            *)
(* ===================================================================== *)

Definition sub_call_answer {S0 : supply} {NM : a_sub_mode} {M : mode}
    {P0 : pskl} {Θ0 : aenv} {c : sub_call}
    (o : option (sig (sub_call_spec S0 NM M P0 Θ0 c))) : option sub_result :=
  match o with None => None | Some r => Some (proj1_sig r) end.

Definition sub_call_run (S0 : supply) (NM : a_sub_mode) (M : mode)
    (P0 : pskl) (Θ0 : aenv) (c : sub_call)
    (Sd : supply) (Θd : aenv) (Qd : pskl) : Prop :=
  match c with
  | sub_call_sub P    => {{ S0 ↝ Sd ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Qd ⊣ Θd }}e
  | sub_call_flex Ξ α => e_sub_flex S0 NM M P0 Θ0 Ξ α Qd Sd Θd
  end.

Definition sub_call_uniq (Θ0 : aenv) (c : sub_call) : Prop :=
  match c with
  | sub_call_sub _    => uniq Θ0
  | sub_call_flex Ξ _ => uniq (Ξ ++ Θ0)
  end.

Definition sub_call_cover (P0 : pskl) (Θ0 : aenv) (c : sub_call) : atoms :=
  match c with
  | sub_call_sub P    =>
      ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P
  | sub_call_flex Ξ α =>
      ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P0 ∪ singleton α
  end.

Definition sub_call_complete (S0 : supply) (NM : a_sub_mode) (M : mode)
    (P0 : pskl) (Θ0 : aenv) (c : sub_call) : Prop :=
  forall (HP : sub_call_lc c) (HP0 : lc_pskl P0)
         (HD : sub_call_defs_mono Θ0 c)
         (H : e_sub_call_order S0 NM M P0 Θ0 c),
    sub_call_uniq Θ0 c ->
    sub_call_cover P0 Θ0 c [<=] S0 ->
    forall Sd Θd Qd, sub_call_run S0 NM M P0 Θ0 c Sd Θd Qd ->
    exists r ps,
      sub_call_answer (e_sub_call_impl c S0 NM M P0 Θ0 HP HP0 HD H) = Some r
      /\ (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
      /\ swaps_atoms ps Sd [=] sb_supply r
      /\ swaps_aenv ps Θd = sb_ctx r
      /\ swaps_pskl ps Qd = sb_out r.

(* ===================================================================== *)
(*  §7  THE MAIN INDUCTION                                                *)
(*                                                                        *)
(*  ⭐ SPLIT AT §1's TWO HYPOTHESES (§8c.20).  [sub_call_complete_sub]     *)
(*  and [sub_call_complete_flex] are LITERALLY [Hsub] / [Hflex] with       *)
(*  [Qc] replaced by [sub_call_complete]; §7c then feeds them to           *)
(*  [e_sub_call_order_sind] in three lines.  The alternative — one         *)
(*  monolithic induction — puts ~120 lines of premises and both halves'    *)
(*  case trees in a single script.                                        *)
(* ===================================================================== *)

(** prop_consis_complete.v §7's [kill_ccall], with this level's extra
    [NM] / [M] / [P0] arguments: run the motive at the recursive call's
    own inputs, then read the runner's answer off the same call. *)
Local Ltac kill_scall Hmot Hu Hcov Hder r Hr ps Hav HS HT HQ :=
  match goal with
  | |- context [ e_sub_call_impl ?c ?S ?nm ?m ?p0 ?T ?hp ?hp0 ?hd ?h ] =>
      let Hx := fresh "Hx" in
      let Hcl := fresh "Hcl" in
      let rr := fresh "rr" in
      destruct (Hmot hp hp0 hd h Hu Hcov _ _ _ Hder)
        as [r [ps [Hx [Hav [HS [HT HQ]]]]]];
      destruct (e_sub_call_impl c S nm m p0 T hp hp0 hd h)
        as [ [rr Hr] | ] eqn:Hcl;
      try rewrite Hcl in Hx; cbn [sub_call_answer] in Hx;
      [ inversion Hx; subst; clear Hx Hcl; cbv beta iota
      | discriminate ]
  end.

(** The head entry a walk row re-wraps is named in [sub_call_cover], hence
    in [S0], which every chain pair dodges. *)
Local Ltac head_fresh Hav Hcov :=
  apply swaps_aenv_fresh_id; intros a0 b0 Hin;
  let Ha0 := fresh "Ha0" in let Hb0 := fresh "Hb0" in
  destruct (Hav a0 b0 Hin) as [Ha0 Hb0]; split;
  clear - Ha0 Hb0 Hcov; repeat rewrite ftvar_in_aenv_app in Hcov;
  simpl in *; fsetdec.

Local Ltac split4 := split; [ | split; [ | split ] ].

(** ⚠️ The runner's atom tests are CONVOYED, so the GOAL's own scrutinee
    has to be destructed — prop_consis_complete.v §7's warning, verbatim. *)
Local Ltac split_eqdec Hl Hr :=
  lazymatch goal with
  | |- context [ @eq_dec ?T ?E ?x ?y ] =>
      destruct (@eq_dec T E x y) as [ Hl | Hr ]
  end.

(* --------------------------------------------------------------------- *)
(*  §7a  THE FLEX HALF — §1's [Hflex], with [Qc := sub_call_complete]      *)
(*                                                                        *)
(*  Each row: invert the derivation with its §4 lemma, walk the runner's   *)
(*  own tests, recurse through the motive premise, re-wrap the head.  ⭐   *)
(*  The only non-routine one is [SI-Flex-Solve], whose two invented names  *)
(*  are realigned by §5's chain.                                          *)
(* --------------------------------------------------------------------- *)
Lemma sub_call_complete_flex : forall S0 NM M P0 Θ0 Ξ α,
    (* Flex-Solve — the head IS the target, undefined *)
    (forall Θ0',
       Θ0 = (α ~ abind_flex_mono) ++ Θ0' ->
       e_sub_call_order
         (add (supply_fresh (add (supply_fresh S0) S0))
            (add (supply_fresh S0) S0))
         NM (mode_fn M) P0
         (Ξ ++ (α ~ abind_flex_mono_def
                      (ptyp_arrow (ptyp_var_f (supply_fresh S0))
                         (ptyp_var_f (supply_fresh (add (supply_fresh S0) S0)))))
             ++ (supply_fresh (add (supply_fresh S0) S0) ~ abind_flex_mono)
             ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0')
         (sub_call_sub
            (pskl_arrow (pskl_var_f (supply_fresh S0))
               (pskl_var_f (supply_fresh (add (supply_fresh S0) S0)))))) ->
    (forall Θ0',
       Θ0 = (α ~ abind_flex_mono) ++ Θ0' ->
       sub_call_complete (add (supply_fresh (add (supply_fresh S0) S0))
             (add (supply_fresh S0) S0))
         NM (mode_fn M) P0
         (Ξ ++ (α ~ abind_flex_mono_def
                      (ptyp_arrow (ptyp_var_f (supply_fresh S0))
                         (ptyp_var_f (supply_fresh (add (supply_fresh S0) S0)))))
             ++ (supply_fresh (add (supply_fresh S0) S0) ~ abind_flex_mono)
             ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0')
         (sub_call_sub
            (pskl_arrow (pskl_var_f (supply_fresh S0))
               (pskl_var_f (supply_fresh (add (supply_fresh S0) S0)))))) ->
    (* Flex-Assign — a defined head is substituted away and dropped *)
    (forall β τ Θ0',
       Θ0 = (β ~ abind_flex_mono_def τ) ++ Θ0' ->
       e_sub_call_order S0 NM (mode_fn M)
         (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
         (Ξ ++ Θ0')
         (sub_call_sub
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)))) ->
    (forall β τ Θ0',
       Θ0 = (β ~ abind_flex_mono_def τ) ++ Θ0' ->
       sub_call_complete S0 NM (mode_fn M)
         (subst_pskl_in_pskl (ptyp_to_pskl τ) β P0)
         (Ξ ++ Θ0')
         (sub_call_sub
            (subst_pskl_in_pskl (ptyp_to_pskl τ) β (pskl_var_f α)))) ->
    (* Flex-Depend / Flex-Skip — an undefined non-target head *)
    (forall β Θ0',
       Θ0 = (β ~ abind_flex_mono) ++ Θ0' ->
       e_sub_call_order S0 NM M P0 Θ0'
         (sub_call_flex (Ξ ++ (β ~ abind_flex_mono)) α)
       /\ e_sub_call_order S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (forall β Θ0',
       Θ0 = (β ~ abind_flex_mono) ++ Θ0' ->
       sub_call_complete S0 NM M P0 Θ0' (sub_call_flex (Ξ ++ (β ~ abind_flex_mono)) α)
       /\ sub_call_complete S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (* Flex-SkipRigid *)
    (forall β Θ0',
       Θ0 = (β ~ abind_tvar) ++ Θ0' ->
       e_sub_call_order S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (forall β Θ0',
       Θ0 = (β ~ abind_tvar) ++ Θ0' ->
       sub_call_complete S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (* Flex-SkipTmVar, both payload sorts *)
    (forall x A Θ0',
       Θ0 = (x ~ abind_var_typ A) ++ Θ0' ->
       e_sub_call_order S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (forall x A Θ0',
       Θ0 = (x ~ abind_var_typ A) ++ Θ0' ->
       sub_call_complete S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (forall x Q Θ0',
       Θ0 = (x ~ abind_var_skl Q) ++ Θ0' ->
       e_sub_call_order S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    (forall x Q Θ0',
       Θ0 = (x ~ abind_var_skl Q) ++ Θ0' ->
       sub_call_complete S0 NM M P0 Θ0' (sub_call_flex Ξ α)) ->
    sub_call_complete S0 NM M P0 Θ0 (sub_call_flex Ξ α).
Proof.
  intros S0 NM M P0 Θ0 Ξ α hsl Hsl hag Hag hdp Hdp hrg Hrg htv Htv hts Hts.
  unfold sub_call_complete.
  intros HP HP0 HD Hord Hu Hcov Sd Θd Qd Hd.
  cbn [sub_call_uniq sub_call_cover sub_call_run] in *.
  destruct Θ0 as [ | [γ b] Θ0' ]; [ destruct (e_sub_flex_inv_nil Hd) | ].
  destruct b as [ | A | Qp | | τ ].
  - (* rigid head — SI-Flex-SkipRigid *)
    rewrite e_sub_call_impl_equation_3. cbv beta iota.
    destruct (e_sub_flex_inv_tvar Hd) as [Hne [Hnf [Θd' [-> Ds]]]].
    split_eqdec Heq Hne2; [ congruence | ]. cbv beta iota.
    destruct (sumbool_of_bool (mem γ (ftvar_in_pskl P0))) as [Hm | Hm];
      [ exfalso; apply mem_true_in in Hm; contradiction | ].
    cbv beta iota.
    assert (Hu0 : uniq (Ξ ++ Θ0')) by (clear - Hu; solve_uniq).
    assert (Hcov0 : ftvar_in_aenv (Ξ ++ Θ0') ∪ ftvar_in_pskl P0
                    ∪ singleton α [<=] S0)
      by (clear - Hcov; repeat rewrite ftvar_in_aenv_app in *;
          simpl in *; fsetdec).
    kill_scall (Hrg γ Θ0' eq_refl) Hu0 Hcov0 Ds r Hr ps Hav HS HT HQ.
    exists (mk_sub_result (sb_supply r) ((γ ~ abind_tvar) ++ sb_ctx r)
              (sb_out r)), ps.
    split; [ reflexivity | ].
    split4; [ exact Hav | cbn [sb_supply proj1_sig]; exact HS
            | | cbn [sb_out proj1_sig]; exact HQ ].
    cbn [sb_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
    head_fresh Hav Hcov.
  - (* term variable, TYPE payload — SI-Flex-SkipTmVar *)
    rewrite e_sub_call_impl_equation_4. cbv beta iota.
    destruct (e_sub_flex_inv_var_typ Hd) as [Θd' [-> Ds]].
    assert (Hu0 : uniq (Ξ ++ Θ0')) by (clear - Hu; solve_uniq).
    assert (Hcov0 : ftvar_in_aenv (Ξ ++ Θ0') ∪ ftvar_in_pskl P0
                    ∪ singleton α [<=] S0)
      by (clear - Hcov; repeat rewrite ftvar_in_aenv_app in *;
          simpl in *; fsetdec).
    kill_scall (Htv γ A Θ0' eq_refl) Hu0 Hcov0 Ds r Hr ps Hav HS HT HQ.
    exists (mk_sub_result (sb_supply r) ((γ ~ abind_var_typ A) ++ sb_ctx r)
              (sb_out r)), ps.
    split; [ reflexivity | ].
    split4; [ exact Hav | cbn [sb_supply proj1_sig]; exact HS
            | | cbn [sb_out proj1_sig]; exact HQ ].
    cbn [sb_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
    head_fresh Hav Hcov.
  - (* term variable, SKELETON payload *)
    rewrite e_sub_call_impl_equation_5. cbv beta iota.
    destruct (e_sub_flex_inv_var_skl Hd) as [Θd' [-> Ds]].
    assert (Hu0 : uniq (Ξ ++ Θ0')) by (clear - Hu; solve_uniq).
    assert (Hcov0 : ftvar_in_aenv (Ξ ++ Θ0') ∪ ftvar_in_pskl P0
                    ∪ singleton α [<=] S0)
      by (clear - Hcov; repeat rewrite ftvar_in_aenv_app in *;
          simpl in *; fsetdec).
    kill_scall (Hts γ Qp Θ0' eq_refl) Hu0 Hcov0 Ds r Hr ps Hav HS HT HQ.
    exists (mk_sub_result (sb_supply r) ((γ ~ abind_var_skl Qp) ++ sb_ctx r)
              (sb_out r)), ps.
    split; [ reflexivity | ].
    split4; [ exact Hav | cbn [sb_supply proj1_sig]; exact HS
            | | cbn [sb_out proj1_sig]; exact HQ ].
    cbn [sb_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
    head_fresh Hav Hcov.
  - (* undefined flexible head *)
    rewrite e_sub_call_impl_equation_6. cbv beta iota.
    split_eqdec Heq Hne.
    + (* ⭐ SI-Flex-Solve — the head IS the target *)
      subst γ. cbv beta iota.
      destruct (e_sub_flex_inv_self Hd) as [ad [bd [Had [Hbd Ds]]]].
      assert (Hcov1 : ftvar_in_aenv (Ξ ++ Θ0') ∪ ftvar_in_pskl P0
                      ∪ singleton α [<=] S0)
        by (clear - Hcov; repeat rewrite ftvar_in_aenv_app in *;
            simpl in *; fsetdec).
      destruct (e_sub_flex_solve_realign Had Hbd Hcov1 Ds)
        as [ps0 [Sd0 [Hav0 [HS0 Ds0]]]].
      pose proof (supply_fresh_notin S0) as Ha1.
      pose proof (supply_fresh_notin (add (supply_fresh S0) S0)) as Hb1.
      pose proof (dom_subset_ftvar_in_aenv Ξ) as HdΞ.
      pose proof (dom_subset_ftvar_in_aenv Θ0') as HdΘ.
      assert (HΞS : ftvar_in_aenv Ξ [<=] S0)
        by (clear - Hcov1; rewrite ftvar_in_aenv_app in Hcov1; fsetdec).
      assert (HΘS : ftvar_in_aenv Θ0' [<=] S0)
        by (clear - Hcov1; rewrite ftvar_in_aenv_app in Hcov1; fsetdec).
      assert (HαS : α `in` S0) by (clear - Hcov1; fsetdec).
      assert (Hu1 : uniq (Ξ ++ Θ0')) by (clear - Hu; solve_uniq).
      assert (HαΞ : α `notin` dom Ξ)
        by (clear - Hu; destruct_uniq; unfold disjoint in *;
            simpl in *; fsetdec).
      assert (HαΘ : α `notin` dom Θ0')
        by (clear - Hu; destruct_uniq; simpl in *; fsetdec).
      (* the two invented names dodge the whole context, and each other *)
      assert (Ha1Ξ : supply_fresh S0 `notin` dom Ξ)
        by (clear - Ha1 HdΞ HΞS; fsetdec).
      assert (Ha1Θ : supply_fresh S0 `notin` dom Θ0')
        by (clear - Ha1 HdΘ HΘS; fsetdec).
      assert (Hb1Ξ : supply_fresh (add (supply_fresh S0) S0)
                     `notin` dom Ξ)
        by (clear - Hb1 HdΞ HΞS; fsetdec).
      assert (Hb1Θ : supply_fresh (add (supply_fresh S0) S0)
                     `notin` dom Θ0')
        by (clear - Hb1 HdΘ HΘS; fsetdec).
      assert (Hu2 : uniq (Ξ ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0'))
        by (apply uniq_insert_mid; assumption).
      assert (Hu3 : uniq (Ξ ++ (supply_fresh (add (supply_fresh S0) S0)
                                  ~ abind_flex_mono)
                             ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0')).
      { apply uniq_insert_mid; [ exact Hu2 | exact Hb1Ξ | ].
        clear - Hb1 Hb1Θ. simpl. fsetdec. }
      assert (Hu0 : uniq (Ξ ++ (α ~ abind_flex_mono_def
                       (ptyp_arrow (ptyp_var_f (supply_fresh S0))
                          (ptyp_var_f (supply_fresh (add (supply_fresh S0) S0)))))
                     ++ (supply_fresh (add (supply_fresh S0) S0)
                           ~ abind_flex_mono)
                     ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0')).
      { apply uniq_insert_mid; [ exact Hu3 | exact HαΞ | ].
        clear - HαΘ HαS Ha1 Hb1. simpl. fsetdec. }
      assert (Hcov0 : ftvar_in_aenv (Ξ ++ (α ~ abind_flex_mono_def
                       (ptyp_arrow (ptyp_var_f (supply_fresh S0))
                          (ptyp_var_f (supply_fresh (add (supply_fresh S0) S0)))))
                     ++ (supply_fresh (add (supply_fresh S0) S0)
                           ~ abind_flex_mono)
                     ++ (supply_fresh S0 ~ abind_flex_mono) ++ Θ0')
                    ∪ ftvar_in_pskl P0
                    ∪ ftvar_in_pskl (pskl_arrow
                         (pskl_var_f (supply_fresh S0))
                         (pskl_var_f (supply_fresh (add (supply_fresh S0) S0))))
                    [<=] add (supply_fresh (add (supply_fresh S0) S0))
                           (add (supply_fresh S0) S0))
        by (clear - Hcov1; repeat rewrite ftvar_in_aenv_app in *;
            simpl in *; fsetdec).
      kill_scall (Hsl Θ0' eq_refl) Hu0 Hcov0 Ds0 r Hr ps Hav HS HT HQ.
      exists r, (ps0 ++ ps).
      split; [ reflexivity | ].
      split4.
      * intros a0 b0 Hin. apply in_app_or in Hin.
        destruct Hin as [Hin | Hin]; [ exact (Hav0 _ _ Hin) | ].
        destruct (Hav _ _ Hin) as [Ha0 Hb0]. split; fsetdec.
      * rewrite swaps_atoms_app. rewrite <- HS.
        apply swaps_atoms_cong. symmetry. exact HS0.
      * rewrite swaps_aenv_app. exact HT.
      * rewrite swaps_pskl_app. exact HQ.
    + cbv beta iota.
      destruct (e_sub_flex_inv_other_flex (not_eq_sym Hne) Hd)
        as [[Hin Dd] | [Hni [Θd' [-> Ds]]]].
      * (* SI-Flex-Depend — the head occurs in the subject *)
        destruct (sumbool_of_bool (mem γ (ftvar_in_pskl P0))) as [Hm | Hm];
          [ | exfalso; apply mem_false_notin in Hm; contradiction ].
        cbv beta iota.
        assert (Hu0 : uniq ((Ξ ++ (γ ~ abind_flex_mono)) ++ Θ0'))
          by (clear - Hu; solve_uniq).
        assert (Hcov0 : ftvar_in_aenv ((Ξ ++ (γ ~ abind_flex_mono)) ++ Θ0')
                        ∪ ftvar_in_pskl P0 ∪ singleton α [<=] S0)
          by (clear - Hcov; repeat rewrite ftvar_in_aenv_app in *;
              simpl in *; fsetdec).
        kill_scall (proj1 (Hdp γ Θ0' eq_refl)) Hu0 Hcov0 Dd
          r Hr ps Hav HS HT HQ.
        exists r, ps. split; [ reflexivity | ].
        split4; [ exact Hav | exact HS | exact HT | exact HQ ].
      * (* SI-Flex-Skip — the head is re-wrapped *)
        destruct (sumbool_of_bool (mem γ (ftvar_in_pskl P0))) as [Hm | Hm];
          [ exfalso; apply mem_true_in in Hm; contradiction | ].
        cbv beta iota.
        assert (Hu0 : uniq (Ξ ++ Θ0')) by (clear - Hu; solve_uniq).
        assert (Hcov0 : ftvar_in_aenv (Ξ ++ Θ0') ∪ ftvar_in_pskl P0
                        ∪ singleton α [<=] S0)
          by (clear - Hcov; repeat rewrite ftvar_in_aenv_app in *;
              simpl in *; fsetdec).
        kill_scall (proj2 (Hdp γ Θ0' eq_refl)) Hu0 Hcov0 Ds
          r Hr ps Hav HS HT HQ.
        exists (mk_sub_result (sb_supply r)
                  ((γ ~ abind_flex_mono) ++ sb_ctx r) (sb_out r)), ps.
        split; [ reflexivity | ].
        split4; [ exact Hav | cbn [sb_supply proj1_sig]; exact HS
                | | cbn [sb_out proj1_sig]; exact HQ ].
        cbn [sb_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
        head_fresh Hav Hcov.
  - (* defined flexible head — SI-Flex-Assign *)
    rewrite e_sub_call_impl_equation_7. cbv beta iota.
    destruct (e_sub_flex_inv_def Hd) as [Θd' [-> Dc]].
    assert (Hu0 : uniq (Ξ ++ Θ0')) by (clear - Hu; solve_uniq).
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P0
                  (ptyp_to_pskl τ) γ) as Hsu1.
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper (pskl_var_f α)
                  (ptyp_to_pskl τ) γ) as Hsu2.
    pose proof (ftvar_ptyp_to_pskl τ) as Hftτ.
    assert (HΞΘ : ftvar_in_aenv (Ξ ++ Θ0') [<=] S0)
      by (clear - Hcov; repeat rewrite ftvar_in_aenv_app in *;
          simpl in *; fsetdec).
    assert (HαS : α `in` S0) by (clear - Hcov; fsetdec).
    assert (Hτ : ftvar_in_pskl (ptyp_to_pskl τ) [<=] S0)
      by (rewrite Hftτ; clear - Hcov;
          repeat rewrite ftvar_in_aenv_app in *; simpl in *; fsetdec).
    assert (HP0S : ftvar_in_pskl P0 [<=] S0) by (clear - Hcov; fsetdec).
    assert (Hb1 : ftvar_in_pskl
              (subst_pskl_in_pskl (ptyp_to_pskl τ) γ P0) [<=] S0).
    { clear - Hsu1 Hτ HP0S.
      assert (Hrm : remove γ (ftvar_in_pskl P0) [<=] ftvar_in_pskl P0)
        by (clear; fsetdec).
      fsetdec. }
    assert (Hb2 : ftvar_in_pskl
              (subst_pskl_in_pskl (ptyp_to_pskl τ) γ (pskl_var_f α))
              [<=] S0).
    { clear - Hsu2 Hτ HαS. simpl in Hsu2.
      assert (Hrm : remove γ (singleton α) [<=] singleton α)
        by (clear; fsetdec).
      fsetdec. }
    assert (Hcov0 : ftvar_in_aenv (Ξ ++ Θ0')
                    ∪ ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl τ) γ P0)
                    ∪ ftvar_in_pskl (subst_pskl_in_pskl (ptyp_to_pskl τ) γ
                          (pskl_var_f α)) [<=] S0)
      by (clear - HΞΘ Hb1 Hb2; fsetdec).
    kill_scall (Hag γ τ Θ0' eq_refl) Hu0 Hcov0 Dc r Hr ps Hav HS HT HQ.
    exists (mk_sub_result (sb_supply r)
              ((γ ~ abind_flex_mono_def τ) ++ sb_ctx r) (sb_out r)), ps.
    split; [ reflexivity | ].
    split4; [ exact Hav | cbn [sb_supply proj1_sig]; exact HS
            | | cbn [sb_out proj1_sig]; exact HQ ].
    cbn [sb_ctx proj1_sig]. rewrite swaps_aenv_app_dist, HT. f_equal.
    head_fresh Hav Hcov.
Qed.

(** The CONSISTENCY runner's completeness at a sub-runner call site —
    prop_consis_complete.v §7's [kill_ccall] through the [e_consis_impl]
    wrapper, exactly as its §8 corollaries unfold it. *)
Local Ltac kill_consis Hu Hcov Hder r Hr ps Hav HS HT HQ :=
  match goal with
  | |- context [ e_consis_impl ?d1 ?d2 ?S ?T ?p0 ?p ?h0 ?h1 ?hd ?h ] =>
      let Hx := fresh "Hx" in let Hcl := fresh "Hcl" in
      let rr := fresh "rr" in let Ho := fresh "Ho" in
      set (Ho := e_consis_order_to_call d1 d2 S T p0 p h);
      destruct (e_consis_call_impl_complete Ho (conj h0 h1) hd Ho Hu Hcov
                  _ _ _ Hder)
        as [r [ps [Hx [Hav [HS [HT HQ]]]]]];
      unfold e_consis_impl; fold Ho;
      destruct (e_consis_call_impl (consis_call_consis d1 d2 p0 p) S T
                  (conj h0 h1) hd Ho) as [ [rr Hr] | ] eqn:Hcl;
      try rewrite Hcl in Hx; cbn [consis_call_answer] in Hx;
      [ inversion Hx; subst; clear Hx Hcl; cbv beta iota;
        cbn [consis_call_out_rel] in HQ
      | discriminate ]
  end.

(** Every boolean the SUB runner tests, discharged from the derivation's own
    premises — the [_ck_complete] side of def_dec.v, one alternative per
    test.  ⚠️ [ForallL]'s guard is the [◇]-or-guarded DISJUNCTION the rule
    carries, so it is destructed rather than [assumption]ed. *)
Local Ltac ck_leaf :=
  solve [ apply ghost_free_ck_complete; assumption
        | apply guarded_shape_ck_complete; assumption
        | apply uniq_ck_complete; assumption
        | apply suffix_ck_complete; assumption
        | apply pskl_eqb_complete; assumption
        | apply wf_pskl_ck_complete_at_size; assumption
        | apply orb_true_intro;
          match goal with
          | H : guarded_pskl _ \/ _ = pskl_ghost |- _ =>
              destruct H as [H | H];
              [ left; apply guarded_shape_ck_complete; exact H
              | right; apply ghost_ck_complete; exact H ]
          end ].

(** ⚠️ The LEAF is tried FIRST: [apply andb_true_intro] unifies up to delta,
    so on [ghost_free_ck (P → Q)] it would happily UNFOLD the fixpoint and
    split a goal the [_ck_complete] lemma answers whole. *)
Local Ltac ck_true := repeat (ck_leaf || (apply andb_true_intro; split)).

(** A runner test the derivation's own premises satisfy: prove the boolean
    TRUE first, then the rejecting branch is [congruence]. *)
Local Ltac bool_true :=
  match goal with
  | |- context [ sumbool_of_bool ?b ] =>
      let Hbt := fresh "Hbt" in let Hb := fresh "Hb" in
      assert (Hbt : b = true) by ck_true;
      destruct (sumbool_of_bool b) as [Hb | Hb];
      [ cbv beta iota | congruence ]
  end.

(** An output the runner hands back UNCHANGED from its inputs — the chain
    fixes it because its free names are all in [S0]. *)
Local Ltac out_fixed Hav Hcov :=
  apply swaps_pskl_fresh_id; intros a0 b0 Hin;
  let Ha0 := fresh "Ha0" in let Hb0 := fresh "Hb0" in
  destruct (Hav a0 b0 Hin) as [Ha0 Hb0]; split;
  clear - Ha0 Hb0 Hcov; simpl in *; fsetdec.

(** A row that spends nothing and answers from its inputs: the EMPTY chain. *)
Local Ltac answer_id :=
  eexists; exists (@nil (atom * atom));
  split; [ reflexivity | ];
  split4; [ intros ? ? []
          | cbn [swaps_atoms sb_supply]; reflexivity
          | cbn [swaps_aenv sb_ctx]; reflexivity
          | cbn [swaps_pskl sb_out]; reflexivity ].

(** A [pskl_var_b] column is unreachable: its [lc_pskl] hypothesis is. *)
Local Ltac kill_var_b :=
  exfalso;
  match goal with H : lc_pskl (pskl_var_b _) |- _ => inversion H end.

(** [SI-Check] — the whole [(ty, TC)] arm below a non-∀ counterpart and a
    non-∀ subject.  One consistency run, and the answer's skeleton is the
    INPUT pattern, which the chain fixes. *)
Local Ltac do_check Hd Hu Hcov :=
  let Hgf1 := fresh "Hgf1" in
  let Hgf0 := fresh "Hgf0" in let Hgd1 := fresh "Hgd1" in
  let Hgd0 := fresh "Hgd0" in let Qc0 := fresh "Qc0" in
  let Dc := fresh "Dc" in let Hcov0 := fresh "Hcov0" in
  let r := fresh "r" in let Hr := fresh "Hr" in let ps := fresh "ps" in
  let Hav := fresh "Hav" in let HS := fresh "HS" in
  let HT := fresh "HT" in let HQ := fresh "HQ" in
  destruct (e_sub_inv_check Hd ltac:(intros; discriminate)
              ltac:(intros; discriminate))
    as [-> [Hgf1 [Hgf0 [Hgd1 [Hgd0 [Qc0 Dc]]]]]];
  bool_true;
  match goal with
  | |- context [ e_consis_impl ?d1 ?d2 ?S ?T ?p0 ?p ?h0 ?h1 ?hd ?h ] =>
      assert (Hcov0 : consis_call_cover T (consis_call_consis d1 d2 p0 p)
                      [<=] S)
        by (cbn [consis_call_cover]; clear - Hcov; simpl in *; fsetdec)
  end;
  kill_consis Hu Hcov0 Dc r Hr ps Hav HS HT HQ;
  eexists; exists ps;
  split; [ reflexivity | ];
  split4; [ exact Hav | cbn [sb_supply]; exact HS
          | cbn [sb_ctx]; exact HT
          | cbn [sb_out]; out_fixed Hav Hcov ].

(** [SI-UnivGhostL] — the ⫯-stripping rows, at both [TC] and [FN]: the
    runner passes the recursive answer through verbatim. *)
Local Ltac do_univ_ghost_l Hd Hu Hcov Hmot :=
  let Ds := fresh "Ds" in let Hcov0 := fresh "Hcov0" in
  let r := fresh "r" in let Hr := fresh "Hr" in let ps := fresh "ps" in
  let Hav := fresh "Hav" in let HS := fresh "HS" in
  let HT := fresh "HT" in let HQ := fresh "HQ" in
  pose proof (e_sub_inv_univ_ghost_l Hd ltac:(discriminate)) as Ds;
  match goal with
  | |- context [ e_sub_call_impl ?c ?S ?nm ?m ?p0 ?T ?hp ?hp0 ?hd ?h ] =>
      assert (Hcov0 : sub_call_cover p0 T c [<=] S)
        by (cbn [sub_call_cover] in *; clear - Hcov; simpl in *; fsetdec)
  end;
  kill_scall Hmot Hu Hcov0 Ds r Hr ps Hav HS HT HQ;
  exists r, ps; split; [ reflexivity | ];
  split4; [ exact Hav | exact HS | exact HT | exact HQ ].

(** [SI-Ghost] — a [◇] subject at [sk] answers with the pattern, spending
    nothing. *)
Local Ltac do_ghost Hd :=
  destruct (e_sub_inv_ghost Hd ltac:(discriminate)) as [-> [-> ->]];
  answer_id.

(** ⭐⭐ [SI-ForallL] — the row all five dispatch guards were landed for.
    The runner draws [supply_fresh S0] where the derivation drew its own
    opener, runs [e_extract_impl] and then recurses at the extraction's
    OUTPUT, so the derivation's extraction has to be moved onto the
    runner's rails: one pre-swap for the opener, then [e_extract_det]
    (prop_extract_det.v §9) for everything the extraction itself invented. *)
Local Ltac do_forall_l Hd Hu Hcov pmot s0 t0 p0 q :=
  let Hg := fresh "Hg" in let ad := fresh "ad" in
  let Sm := fresh "Sm" in let Xd := fresh "Xd" in
  let P1d := fresh "P1d" in let Had := fresh "Had" in
  let Dx := fresh "Dx" in let Hwfd := fresh "Hwfd" in
  let Dsub := fresh "Dsub" in let Ha1 := fresh "Ha1" in
  let Hav0 := fresh "Hav0" in let Hsad := fresh "Hsad" in
  let HfixT := fresh "HfixT" in let HfixQ := fresh "HfixQ" in
  let Smx := fresh "Smx" in let HSmx := fresh "HSmx" in
  let Dx1 := fresh "Dx1" in let Dx2 := fresh "Dx2" in
  let Hcx := fresh "Hcx" in let Hop := fresh "Hop" in
  destruct (e_sub_inv_forall_l_gen Hd ltac:(discriminate)
              ltac:(solve [ left; reflexivity
                          | right; left; discriminate
                          | right; right; intros ? Habs;
                            discriminate Habs ]))
    as [Hg [ad [Sm [Xd [P1d [Had [Dx [Hwfd Dsub]]]]]]]];
  bool_true;
  pose proof (supply_fresh_notin s0) as Ha1;
  assert (Hav0 : forall a b, In (a, b) ((ad, supply_fresh s0) :: nil) ->
                 a `notin` s0 /\ b `notin` s0)
    by (intros a b [Heq | []]; inversion Heq; subst; split; assumption);
  assert (Hsad : swaps_atom ((ad, supply_fresh s0) :: nil) ad
                 = supply_fresh s0)
    by (simpl; unfold swap_atom;
        destruct (ad == ad); [ reflexivity | congruence ]);
  assert (HfixT : forall (X : aenv), ftvar_in_aenv X [<=] s0 ->
            swaps_aenv ((ad, supply_fresh s0) :: nil) X = X)
    by (intros X HX; apply swaps_aenv_fresh_id; intros a b Hin;
        let Hza := fresh in let Hzb := fresh in
        destruct (Hav0 a b Hin) as [Hza Hzb]; split; fsetdec);
  assert (HfixQ : forall X, ftvar_in_pskl X [<=] s0 ->
            swaps_pskl ((ad, supply_fresh s0) :: nil) X = X)
    by (intros X HX; apply swaps_pskl_fresh_id; intros a b Hin;
        let Hza := fresh in let Hzb := fresh in
        destruct (Hav0 a b Hin) as [Hza Hzb]; split; fsetdec);
  (* PRE-SWAP the extraction onto the runner's opener *)
  destruct (e_extract_swaps ((ad, supply_fresh s0) :: nil) Dx
              (S0' := add (supply_fresh s0) s0)) as [Smx [HSmx Dx1]];
  [ simpl; rewrite swap_atoms_add;
    rewrite (swap_atoms_notin ad (supply_fresh s0) s0)
      by (clear - Had Ha1; fsetdec);
    unfold swap_atom; destruct (ad == ad); [ reflexivity | congruence ]
  | ];
  rewrite (HfixT t0) in Dx1 by (clear - Hcov; simpl in *; fsetdec);
  rewrite swaps_pskl_open, swaps_pskl_var_f, Hsad in Dx1;
  rewrite (HfixQ q) in Dx1 by (clear - Hcov; simpl in *; fsetdec);
  rewrite (HfixQ p0) in Dx1 by (clear - Hcov; simpl in *; fsetdec);
  pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper q
                (pskl_var_f (supply_fresh s0))) as Hop;
  simpl in Hop;
  assert (Hcx : add (supply_fresh s0)
            (ftvar_in_aenv t0
             ∪ ftvar_in_pskl (open_pskl_wrt_pskl q
                  (pskl_var_f (supply_fresh s0)))
             ∪ ftvar_in_pskl p0) [<=] add (supply_fresh s0) s0)
    by (clear - Hcov Hop; simpl in *; fsetdec);
  (* the RUNNER's extraction answers — level 4's headline *)
  destruct (e_extract_inv Dx1) as [Sa1 [Sa2 [Xl [Xs [Xg [Cl [Qs
              [Hxeq [Hlk [Hfd Hgs]]]]]]]]]];
  let rx := fresh "rx" in let Hrx := fresh "Hrx" in
  let Hne := fresh "Hne" in let Hxc := fresh "Hxc" in
  match goal with
  | |- context [ e_extract_impl ?S ?T ?nm ?al ?mm ?pp ?pp' ?h1 ?h2 ?h3 ] =>
      assert (Hne : e_extract_impl S T nm al mm pp pp' h1 h2 h3 <> None)
        by (exact (e_extract_impl_complete h1 h2 h3 Hlk Hfd Hcx Hcx));
      destruct (e_extract_impl S T nm al mm pp pp' h1 h2 h3)
        as [ [rx Hrx] | ] eqn:Hxc;
      [ cbv beta iota | exact (False_ind _ (Hne eq_refl)) ]
  end;
  unfold extract_spec in Hrx;
  (* ⭐ THE DETERMINISM STEP *)
  let ps1 := fresh "ps1" in let Hav1 := fresh "Hav1" in
  let HS1 := fresh "HS1" in let HX1 := fresh "HX1" in
  let HY1 := fresh "HY1" in
  destruct (e_extract_det Dx1 Hrx Hcx) as [ps1 [Hav1 [HS1 [HX1 HY1]]]];
  (* the wf side condition, transported *)
  let Hwf0 := fresh "Hwf0" in let Hwf1 := fresh "Hwf1" in
  pose proof (a_wf_pskl_swaps ((ad, supply_fresh s0) :: nil) Hwfd) as Hwf0;
  rewrite swaps_aenv_app_dist in Hwf0;
  rewrite (HfixT t0) in Hwf0 by (clear - Hcov; simpl in *; fsetdec);
  pose proof (a_wf_pskl_swaps ps1 Hwf0) as Hwf1;
  rewrite swaps_aenv_app_dist, HX1, HY1 in Hwf1;
  rewrite (swaps_aenv_fresh_id ps1 t0) in Hwf1
    by (intros a b Hin;
        let Hza := fresh in let Hzb := fresh in
        destruct (Hav1 a b Hin) as [Hza Hzb];
        split; clear - Hza Hzb Hcov; simpl in *; fsetdec);
  bool_true;
  (* move the RECURSIVE premise onto the runner's rails, both chains *)
  let Sd1 := fresh "Sd1" in let HSd1 := fresh "HSd1" in
  let Ds1 := fresh "Ds1" in
  destruct (e_sub_swaps ((ad, supply_fresh s0) :: nil) Dsub (S0' := Smx))
    as [Sd1 [HSd1 Ds1]]; [ exact HSmx | ];
  let Sd2 := fresh "Sd2" in let HSd2 := fresh "HSd2" in
  let Ds2 := fresh "Ds2" in
  destruct (e_sub_swaps ps1 Ds1 (S0' := ex_supply rx)) as [Sd2 [HSd2 Ds2]];
  [ symmetry; exact HS1 | ];
  rewrite ! swaps_aenv_app_dist, HX1 in Ds2;
  rewrite (HfixT t0) in Ds2 by (clear - Hcov; simpl in *; fsetdec);
  rewrite (swaps_aenv_fresh_id ps1 t0) in Ds2
    by (intros a b Hin;
        let Hza := fresh in let Hzb := fresh in
        destruct (Hav1 a b Hin) as [Hza Hzb];
        split; clear - Hza Hzb Hcov; simpl in *; fsetdec);
  rewrite ! swaps_pskl_open, HY1 in Ds2;
  rewrite (HfixQ q) in Ds2 by (clear - Hcov; simpl in *; fsetdec);
  rewrite (swaps_pskl_fresh_id ps1 q) in Ds2
    by (intros a b Hin;
        let Hza := fresh in let Hzb := fresh in
        destruct (Hav1 a b Hin) as [Hza Hzb];
        split; clear - Hza Hzb Hcov; simpl in *; fsetdec);
  rewrite (HfixQ p0) in Ds2 by (clear - Hcov; simpl in *; fsetdec);
  rewrite (swaps_pskl_fresh_id ps1 p0) in Ds2
    by (intros a b Hin;
        let Hza := fresh in let Hzb := fresh in
        destruct (Hav1 a b Hin) as [Hza Hzb];
        split; clear - Hza Hzb Hcov; simpl in *; fsetdec);
  (* the recursive call's own side conditions, from the extraction's block *)
  let Hblk := fresh "Hblk" in let Hgrx := fresh "Hgrx" in
  let Houtx := fresh "Houtx" in let Hd0 := fresh "Hd0" in
  pose proof (e_extract_block Hrx) as [Hblk [Hblkf [Hblku Hblkft]]];
  pose proof (e_extract_supply_grows Hrx) as Hgrx;
  pose proof (e_extract_out_ftvar Hrx) as Houtx;
  pose proof (dom_subset_ftvar_in_aenv t0) as Hd0;
  let Hu1 := fresh "Hu1" in let Hcov1 := fresh "Hcov1" in
  assert (Hu1 : uniq (ex_block rx ++ t0));
  [ apply uniq_app_4;
    [ exact Hblku | exact Hu
    | unfold disjoint; clear - Hblkf Hd0 Hcov Ha1; simpl in *; fsetdec ]
  | ];
  assert (Hcov1 : ftvar_in_aenv (ex_block rx ++ t0) ∪ ftvar_in_pskl p0
            ∪ ftvar_in_pskl (open_pskl_wrt_pskl q (ex_out rx))
            [<=] ex_supply rx);
  [ rewrite ftvar_in_aenv_app;
    (let Hoq := fresh in
     pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper q (ex_out rx)) as Hoq;
     clear - Hblk Hblkft Hgrx Houtx Hoq Hop Hcov;
     simpl in *; fsetdec)
  | ];
  let r := fresh "r" in let Hr := fresh "Hr" in let ps := fresh "ps" in
  let Hav := fresh "Hav" in let HS := fresh "HS" in
  let HT := fresh "HT" in let HQ := fresh "HQ" in
  kill_scall (pmot Hg _ _ _ Hrx Hwf1) Hu1 Hcov1 Ds2 r Hr ps Hav HS HT HQ;
  exists r, (((ad, supply_fresh s0) :: nil) ++ ps1 ++ ps);
  split; [ reflexivity | ];
  split4;
  [ intros a0 b0 Hin; rewrite ! in_app_iff in Hin;
    destruct Hin as [Hin | [Hin | Hin]];
    [ exact (Hav0 a0 b0 Hin)
    | let Hza := fresh in let Hzb := fresh in
      destruct (Hav1 a0 b0 Hin) as [Hza Hzb]; split; clear - Hza Hzb; fsetdec
    | let Hza := fresh in let Hzb := fresh in
      destruct (Hav a0 b0 Hin) as [Hza Hzb];
      split; clear - Hza Hzb Hgrx Ha1; fsetdec ]
  | rewrite ! swaps_atoms_app; rewrite <- HS;
    apply swaps_atoms_cong; rewrite HSd2;
    apply swaps_atoms_cong; symmetry; exact HSd1
  | rewrite ! swaps_aenv_app; exact HT
  | rewrite ! swaps_pskl_app; exact HQ ].

(** The [(ty, TC)] arm's SUBJECT dispatch, below a non-∀ counterpart.
    ⚠️ The [SI-ForallL] branch reads its own [Q] OFF THE GOAL: an [Ltac]
    body resolves a bare identifier at DEFINITION time, so a name the
    tactic's own [destruct] pattern introduces cannot be written down. *)
Local Ltac do_ty_tc_p Hd Hu Hcov hfl p :=
  destruct p as [ | n | γ | Pa Pb | Q | | Pb ]; cbv beta iota;
  [ do_check Hd Hu Hcov
  | kill_var_b
  | do_check Hd Hu Hcov
  | do_check Hd Hu Hcov
  | lazymatch goal with
    | |- context [ e_extract_impl (add (supply_fresh ?ss) ?ss) ?tt _ _ _
                     (open_pskl_wrt_pskl ?qq (pskl_var_f _)) ?pp _ _ _ ] =>
        do_forall_l Hd Hu Hcov
          (hfl qq eq_refl ltac:(discriminate)) ss tt pp qq
    end
  | do_check Hd Hu Hcov
  | do_check Hd Hu Hcov ].

(** The [(sk, TC)] arm below a subject that is neither [∀] nor [◇] nor [⫯]:
    the runner keys on the PATTERN, and only a [◇] pattern has a rule
    ([SI-UnivGhostR]).  §4's [e_sub_inv_sk_tc_none] kills the other six. *)
Local Ltac do_sk_tc_p0 Hd p0 :=
  destruct p0 as [ | n0 | γ0 | P0a P0b | B | | P0b ]; cbv beta iota;
  [ | | | |
  | destruct (e_sub_inv_univ_ghost_r Hd ltac:(discriminate)
               ltac:(intros ? Habs; discriminate Habs)
               ltac:(intros ? Habs; discriminate Habs))
      as [Hgd [-> [-> ->]]];
    bool_true; answer_id
  | ];
  try solve [ exfalso; eapply e_sub_inv_sk_tc_none;
              [ exact Hd | discriminate
              | intros ? Habs; discriminate Habs
              | intros ? Habs; discriminate Habs | discriminate ] ].

(* --------------------------------------------------------------------- *)
(*  §7b  THE SUB HALF — §1's [Hsub], with [Qc := sub_call_complete]        *)
(*                                                                        *)
(*  The case tree is the runner's dispatch, clause for clause (§8c.13's    *)
(*  table): mode first, then [NM], then the shape column the arm keys on.  *)
(*  ⭐ Its one genuinely new row is [SI-ForallL] — the row all five        *)
(*  dispatch guards were landed for: it runs [e_extract_impl] and then     *)
(*  recurses at the extraction's output, so the derivation's extraction    *)
(*  has to be moved onto the runner's rails, which is [e_extract_det].     *)
(* --------------------------------------------------------------------- *)
Lemma sub_call_complete_sub : forall S0 NM M P0 Θ0 P,
    (* Check — one consistency run *)
    (M = mode_tc -> e_consis_order empty empty S0 Θ0 P0 P) ->
    (* ForallR — peel the pattern's quantifier *)
    (forall B,
       M = mode_tc -> P0 = pskl_all_syn B ->
       e_sub_call_order (add (supply_fresh S0) S0) a_sub_mode_ty mode_tc
         (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))
         ((supply_fresh S0 ~ abind_tvar) ++ Θ0) (sub_call_sub P)) ->
    (forall B,
       M = mode_tc -> P0 = pskl_all_syn B ->
       sub_call_complete (add (supply_fresh S0) S0) a_sub_mode_ty mode_tc
         (open_pskl_wrt_pskl B (pskl_var_f (supply_fresh S0)))
         ((supply_fresh S0 ~ abind_tvar) ++ Θ0) (sub_call_sub P)) ->
    (* FlexMono — enter the walk *)
    (forall α M',
       P = pskl_var_f α -> M = mode_fn M' ->
       e_sub_call_order S0 NM M' P0 Θ0 (sub_call_flex nil α)) ->
    (forall α M',
       P = pskl_var_f α -> M = mode_fn M' ->
       sub_call_complete S0 NM M' P0 Θ0 (sub_call_flex nil α)) ->
    (* Arrow — the domain goes to consistency, the codomain stays *)
    (forall M' P0a P0b P1 P2,
       M = mode_fn M' -> P0 = pskl_arrow P0a P0b -> P = pskl_arrow P1 P2 ->
       e_consis_order empty empty S0 Θ0 P0a P1
       /\ (forall S1 Θ1 Q1,
             {{ S0 ↝ S1 ⊨ Θ0 ⊢[ empty | empty | P0a ] P1 ∼ Q1 ⊣ Θ1 }}e ->
             e_sub_call_order S1 NM M' P0b Θ1 (sub_call_sub P2))) ->
    (forall M' P0a P0b P1 P2,
       M = mode_fn M' -> P0 = pskl_arrow P0a P0b -> P = pskl_arrow P1 P2 ->
       forall S1 Θ1 Q1,
         {{ S0 ↝ S1 ⊨ Θ0 ⊢[ empty | empty | P0a ] P1 ∼ Q1 ⊣ Θ1 }}e ->
         sub_call_complete S1 NM M' P0b Θ1 (sub_call_sub P2)) ->
    (* ForallL — extract an instantiation, then recurse on the opened body *)
    (forall Q,
       P = pskl_all_syn Q -> M <> mode_ti ->
       (guarded_pskl P0 \/ P0 = pskl_ghost) ->
       e_extract_order (add (supply_fresh S0) S0) Θ0 NM (supply_fresh S0) M
         (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0))) P0
       /\ (forall S1 Ξ P1,
             {{ (add (supply_fresh S0) S0) ↝ S1 ⊨ Θ0
                ⊢ (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
                ⊳[ NM , (supply_fresh S0) , M ] P0 ⤳ Ξ ↪ P1 }}e ->
             {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a ->
             e_sub_call_order S1 NM M P0 (Ξ ++ Θ0)
               (sub_call_sub (open_pskl_wrt_pskl Q P1)))) ->
    (forall Q,
       P = pskl_all_syn Q -> M <> mode_ti ->
       (guarded_pskl P0 \/ P0 = pskl_ghost) ->
       forall S1 Ξ P1,
         {{ (add (supply_fresh S0) S0) ↝ S1 ⊨ Θ0
            ⊢ (open_pskl_wrt_pskl Q (pskl_var_f (supply_fresh S0)))
            ⊳[ NM , (supply_fresh S0) , M ] P0 ⤳ Ξ ↪ P1 }}e ->
         {{ (Ξ ++ Θ0) ⨟ empty ⊢ₚₛ P1 }}a ->
         sub_call_complete S1 NM M P0 (Ξ ++ Θ0)
           (sub_call_sub (open_pskl_wrt_pskl Q P1))) ->
    (* UnivGhostL — strip the subject's ⫯ *)
    (forall Q,
       P = pskl_univ_ghost Q -> M <> mode_ti ->
       e_sub_call_order S0 NM M P0 Θ0 (sub_call_sub Q)) ->
    (forall Q,
       P = pskl_univ_ghost Q -> M <> mode_ti ->
       sub_call_complete S0 NM M P0 Θ0 (sub_call_sub Q)) ->
    sub_call_complete S0 NM M P0 Θ0 (sub_call_sub P).
Proof.
  intros S0 NM M P0 Θ0 P hck hfr Hfr hfm Hfm har Har hfl Hfl hug Hug.
  unfold sub_call_complete.
  intros HP HP0 HD Hord Hu Hcov Sd Θd Qd Hd.
  cbn [sub_call_lc sub_call_uniq sub_call_cover sub_call_run] in *.
  rewrite e_sub_call_impl_equation_1.
  destruct M as [ | | M' ]; cbv beta iota.
  - (* ============ mode TI — SI-Infer, and nothing else ============ *)
    destruct (e_sub_inv_ti Hd) as [-> [-> [-> ->]]]. cbv beta iota. answer_id.
  - (* ================= mode TC ================= *)
    destruct NM; cbv beta iota.
    + (* --- NM = ty : SI-ForallR outranks the subject dispatch --- *)
      destruct P0 as [ | n0 | γ0 | P0a P0b | B | | P0b ]; cbv beta iota.
      * do_ty_tc_p Hd Hu Hcov Hfl P.
      * inversion HP0.
      * do_ty_tc_p Hd Hu Hcov Hfl P.
      * do_ty_tc_p Hd Hu Hcov Hfl P.
      * (* ⭐ SI-ForallR — peel the pattern's ∀, then SPLIT the junk block *)
        destruct (e_sub_inv_forall_r Hd)
          as [-> [Hgf [ad [Xd [Hsuf [HuX [Had Dr]]]]]]].
        bool_true.
        pose proof (supply_fresh_notin S0) as Ha1.
        pose proof (dom_subset_ftvar_in_aenv Θ0) as Hd0.
        (* PRE-SWAP the derivation's opener onto [supply_fresh S0] *)
        assert (Hav0 : forall a b, In (a, b) ((ad, supply_fresh S0) :: nil) ->
                       a `notin` S0 /\ b `notin` S0)
          by (intros a b [Heq | []]; inversion Heq; subst;
              split; assumption).
        assert (Hsad : swaps_atom ((ad, supply_fresh S0) :: nil) ad
                       = supply_fresh S0)
          by (simpl; unfold swap_atom;
              destruct (ad == ad); [ reflexivity | congruence ]).
        assert (HfixΘ : forall (X : aenv), ftvar_in_aenv X [<=] S0 ->
                  swaps_aenv ((ad, supply_fresh S0) :: nil) X = X)
          by (intros X HX; apply swaps_aenv_fresh_id; intros a b Hin;
              destruct (Hav0 a b Hin) as [Hxa Hxb]; split; fsetdec).
        assert (HfixP : forall X, ftvar_in_pskl X [<=] S0 ->
                  swaps_pskl ((ad, supply_fresh S0) :: nil) X = X)
          by (intros X HX; apply swaps_pskl_fresh_id; intros a b Hin;
              destruct (Hav0 a b Hin) as [Hxa Hxb]; split; fsetdec).
        destruct (e_sub_swaps ((ad, supply_fresh S0) :: nil) Dr
                    (S0' := add (supply_fresh S0) S0)) as [Sd1 [HSd1 Dr1]].
        { simpl. rewrite swap_atoms_add.
          rewrite (swap_atoms_notin ad (supply_fresh S0) S0)
            by (clear - Had Ha1; fsetdec).
          unfold swap_atom. destruct (ad == ad); [ reflexivity | congruence ]. }
        rewrite swaps_aenv_cons_tvar, Hsad in Dr1.
        rewrite (HfixΘ Θ0) in Dr1
          by (clear - Hcov; simpl in *; fsetdec).
        rewrite swaps_pskl_open, swaps_pskl_var_f, Hsad in Dr1.
        rewrite (HfixP B) in Dr1 by (clear - Hcov; simpl in *; fsetdec).
        rewrite (HfixP P) in Dr1 by (clear - Hcov; simpl in *; fsetdec).
        rewrite swaps_aenv_app_dist, swaps_aenv_cons_tvar, Hsad in Dr1.
        (* the premise's own side conditions, at the runner's opener *)
        assert (Ha1d : supply_fresh S0 `notin` dom Θ0)
          by (clear - Ha1 Hd0 Hcov; simpl in *; fsetdec).
        assert (Hu1 : uniq ((supply_fresh S0 ~ abind_tvar) ++ Θ0))
          by (clear - Hu Ha1d; solve_uniq).
        assert (Hcov1 : ftvar_in_aenv ((supply_fresh S0 ~ abind_tvar) ++ Θ0)
                        ∪ ftvar_in_pskl (open_pskl_wrt_pskl B
                             (pskl_var_f (supply_fresh S0)))
                        ∪ ftvar_in_pskl P [<=] add (supply_fresh S0) S0).
        { pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B
                        (pskl_var_f (supply_fresh S0))) as Hop.
          simpl in Hop. clear - Hop Hcov. simpl in *. fsetdec. }
        kill_scall (Hfr B eq_refl eq_refl) Hu1 Hcov1 Dr1 r Hr ps Hav HS HT HQ.
        (* the recursive answer's own outputs *)
        cbn [sub_call_spec sub_spec] in Hr.
        pose proof ((proj1 e_sub_sub_flex_sound) _ _ _ _ _ _ _ _ _ Hr Hu1 Hcov1)
          as [Hra [Huc [Hcvc Hqc]]].
        (* the counterpart the runner tests for *)
        assert (Hout : sb_out r = open_pskl_wrt_pskl B
                         (pskl_var_f (supply_fresh S0))).
        { rewrite <- HQ. apply swaps_pskl_fresh_id.
          intros a0 b0 Hin. destruct (Hav a0 b0 Hin) as [Hya Hyb].
          pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B
                        (pskl_var_f (supply_fresh S0))) as Hop.
          simpl in Hop. split; clear - Hya Hyb Hop Hcov; simpl in *; fsetdec. }
        bool_true.
        (* the output context, decomposed at the runner's own marker *)
        assert (Hctx : sb_ctx r
                  = swaps_aenv ps (swaps_aenv ((ad, supply_fresh S0) :: nil) Xd)
                    ++ (supply_fresh S0 ~ abind_tvar)
                    ++ swaps_aenv ps (swaps_aenv ((ad, supply_fresh S0) :: nil) Θd)).
        { rewrite <- HT. rewrite swaps_aenv_app_dist, swaps_aenv_cons_tvar.
          repeat f_equal.
          apply swaps_atom_notin. intros a0 b0 Hin.
          destruct (Hav a0 b0 Hin) as [Hya Hyb].
          split; intro Heq0; subst; clear - Hya Hyb; fsetdec. }
        assert (Hsufr : a_suffix
                  (swaps_aenv ps (swaps_aenv ((ad, supply_fresh S0) :: nil) Xd)))
          by (apply a_suffix_swaps; apply a_suffix_swaps; exact Hsuf).
        assert (HΘfix : swaps_aenv ps
                  (swaps_aenv ((ad, supply_fresh S0) :: nil) Θ0) = Θ0).
        { rewrite (HfixΘ Θ0) by (clear - Hcov; simpl in *; fsetdec).
          apply swaps_aenv_fresh_id. intros a0 b0 Hin.
          destruct (Hav a0 b0 Hin) as [Hya Hyb].
          split; clear - Hya Hyb Hcov; simpl in *; fsetdec. }
        assert (HuXr : uniq
                  (swaps_aenv ps (swaps_aenv ((ad, supply_fresh S0) :: nil) Xd)
                   ++ Θ0)).
        { rewrite <- HΘfix. rewrite <- ! swaps_aenv_app_dist.
          apply swaps_aenv_uniq. apply swaps_aenv_uniq. exact HuX. }
        destruct (split_at_tvar_complete Hctx Huc)
          as [[pp Hpp] [Hsp Hpr]].
        simpl in Hpr; subst pp.
        rewrite Hsp. cbv beta iota. cbn [fst snd].
        bool_true.
        exists (mk_sub_result (sb_supply r)
                  (swaps_aenv ps (swaps_aenv ((ad, supply_fresh S0) :: nil) Θd))
                  (pskl_all_syn B)), (((ad, supply_fresh S0) :: nil) ++ ps).
        split; [ reflexivity | ].
        split4.
        -- intros a0 b0 Hin. apply in_app_or in Hin.
           destruct Hin as [Hin | Hin]; [ exact (Hav0 a0 b0 Hin) | ].
           destruct (Hav a0 b0 Hin) as [Hya Hyb].
           split; clear - Hya Hyb; fsetdec.
        -- cbn [sb_supply]. rewrite swaps_atoms_app. rewrite <- HS.
           apply swaps_atoms_cong. symmetry. exact HSd1.
        -- cbn [sb_ctx]. rewrite swaps_aenv_app. reflexivity.
        -- cbn [sb_out]. rewrite swaps_pskl_app, ! swaps_pskl_all_syn.
           rewrite (HfixP B) by (clear - Hcov; simpl in *; fsetdec).
           f_equal. apply swaps_pskl_fresh_id. intros a0 b0 Hin.
           destruct (Hav a0 b0 Hin) as [Hya Hyb].
           split; clear - Hya Hyb Hcov; simpl in *; fsetdec.
      * do_ty_tc_p Hd Hu Hcov Hfl P.
      * do_ty_tc_p Hd Hu Hcov Hfl P.
    + (* --- NM = sk : the runner keys on the SUBJECT --- *)
      destruct P as [ | n | γ | Pa Pb | Q | | Pb ]; cbv beta iota.
      * do_sk_tc_p0 Hd P0.
      * kill_var_b.
      * do_sk_tc_p0 Hd P0.
      * do_sk_tc_p0 Hd P0.
      * (* SI-ForallL *)
        do_forall_l Hd Hu Hcov
          (Hfl Q eq_refl ltac:(discriminate)) S0 Θ0 P0 Q.
      * (* SI-Ghost *) do_ghost Hd.
      * (* SI-UnivGhostL *)
        do_univ_ghost_l Hd Hu Hcov (Hug Pb eq_refl ltac:(discriminate)).
  - (* ================= mode FN ================= *)
    destruct P as [ | n | γ | Pa Pb | Q | | Pb ]; cbv beta iota.
    * (* 1 : no rule fires *) destruct (e_sub_inv_fn_unit_none Hd).
    * kill_var_b.
    * (* SI-FlexMono — enter the walk with an EMPTY accumulator *)
      pose proof (e_sub_inv_flex_mono Hd) as Df.
      assert (Hcov0 : ftvar_in_aenv (nil ++ Θ0) ∪ ftvar_in_pskl P0
                      ∪ singleton γ [<=] S0)
        by (clear - Hcov; simpl in *; fsetdec).
      assert (Hu0 : uniq (nil ++ Θ0)) by (clear - Hu; simpl; assumption).
      kill_scall (Hfm γ M' eq_refl eq_refl) Hu0 Hcov0 Df
        r Hr ps Hav HS HT HQ.
      exists r, ps. split; [ reflexivity | ].
      split4; [ exact Hav | exact HS | exact HT | exact HQ ].
    * (* SI-Arrow, at an arrow pattern; every other pattern rejects *)
      destruct P0 as [ | n0 | γ0 | P0a P0b | B | | P0b ]; cbv beta iota;
        [ | | | | | | ];
        try solve [ destruct (e_sub_inv_arrow_none Hd
                      ltac:(intros ? ? Habs; discriminate Habs)) ].
      destruct (e_sub_inv_arrow Hd) as [Sm [Θm [Qd1 [Qd2 [-> [D1 D2]]]]]].
      assert (Hcov1 : consis_call_cover Θ0
                (consis_call_consis empty empty P0a Pa) [<=] S0)
        by (cbn [consis_call_cover]; clear - Hcov; simpl in *; fsetdec).
      kill_consis Hu Hcov1 D1 r1 Hr1 ps1 Hav1 HS1 HT1 HQ1.
      cbn [consis_call_spec consis_spec] in Hr1.
      (* what the FIRST premise's own soundness puts in scope for the second *)
      pose proof ((proj2 (proj2 e_assign_unify_consis_sound))
                    _ _ _ _ _ _ _ _ _ Hr1 Hu
                    ltac:(clear - Hcov; simpl in *; fsetdec))
        as [Da1 [Hu1' Hcov1']].
      pose proof (e_consis_supply_grows Hr1) as Hgr1.
      pose proof ((proj2 (proj2 e_assign_unify_consis_out_ftvar))
                    _ _ _ _ _ _ _ _ _ Hr1 Hu
                    ltac:(clear - Hcov; simpl in *; fsetdec)) as Hout1.
      (* move the SECOND premise onto the runner's rails *)
      destruct (e_sub_swaps ps1 D2 (S0' := cs_supply r1)) as [S2t [HS2t D2t]];
        [ symmetry; exact HS1 | ].
      rewrite HT1 in D2t.
      rewrite (swaps_pskl_fresh_id ps1 P0b) in D2t
        by (intros a0 b0 Hin; destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0];
            split; clear - Ha0 Hb0 Hcov; simpl in *; fsetdec).
      rewrite (swaps_pskl_fresh_id ps1 Pb) in D2t
        by (intros a0 b0 Hin; destruct (Hav1 a0 b0 Hin) as [Ha0 Hb0];
            split; clear - Ha0 Hb0 Hcov; simpl in *; fsetdec).
      assert (Hcov2 : ftvar_in_aenv (cs_ctx r1) ∪ ftvar_in_pskl P0b
                      ∪ ftvar_in_pskl Pb [<=] cs_supply r1)
        by (clear - Hcov Hcov1' Hgr1; simpl in *; fsetdec).
      kill_scall (Har M' P0a P0b Pa Pb eq_refl eq_refl eq_refl _ _ _ Hr1)
        Hu1' Hcov2 D2t r2 Hr2 ps2 Hav2 HS2 HT2 HQ2.
      exists (mk_sub_result (sb_supply r2) (sb_ctx r2)
                (pskl_arrow (cs_out r1) (sb_out r2))), (ps1 ++ ps2).
      split; [ reflexivity | ].
      split4.
      -- intros a0 b0 Hin. apply in_app_or in Hin.
         destruct Hin as [Hin | Hin]; [ exact (Hav1 a0 b0 Hin) | ].
         destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0].
         split; clear - Ha0 Hb0 Hgr1; fsetdec.
      -- cbn [sb_supply]. rewrite swaps_atoms_app. rewrite <- HS2.
         apply swaps_atoms_cong. symmetry. exact HS2t.
      -- cbn [sb_ctx]. rewrite swaps_aenv_app. exact HT2.
      -- cbn [sb_out]. rewrite swaps_pskl_app, ! swaps_pskl_arrow.
         rewrite HQ1 in *. f_equal; [ | exact HQ2 ].
         apply swaps_pskl_fresh_id. intros a0 b0 Hin.
         destruct (Hav2 a0 b0 Hin) as [Ha0 Hb0].
         split; clear - Ha0 Hb0 Hout1; fsetdec.

    * (* SI-ForallL *)
      do_forall_l Hd Hu Hcov
        (Hfl Q eq_refl ltac:(discriminate)) S0 Θ0 P0 Q.
    * (* SI-Ghost, at sk only *)
      destruct NM; cbv beta iota;
        [ destruct (e_sub_inv_fn_ty_ghost_none Hd) | do_ghost Hd ].
    * (* SI-UnivGhostL, at sk only *)
      destruct NM; cbv beta iota;
        [ destruct (e_sub_inv_fn_ty_univ_ghost_none Hd)
        | do_univ_ghost_l Hd Hu Hcov (Hug Pb eq_refl ltac:(discriminate)) ].
Qed.

(* --------------------------------------------------------------------- *)
(*  §7c  The two halves, joined                                           *)
(* --------------------------------------------------------------------- *)

Lemma e_sub_call_impl_complete : forall S0 NM M P0 Θ0 c
    (H0 : e_sub_call_order S0 NM M P0 Θ0 c),
    sub_call_complete S0 NM M P0 Θ0 c.
Proof.
  intros. apply (e_sub_call_order_sind sub_call_complete);
    [ exact sub_call_complete_sub | exact sub_call_complete_flex
    | exact H0 ].
Qed.

(* ===================================================================== *)
(*  §8  THE THREE HEADLINES                                               *)
(*                                                                        *)
(*  prop_consis_complete.v §8's shape, for the SUBTYPING runner — and      *)
(*  UNRESTRICTED: level 5's ghost-free rung was lifted (§8c.17), so         *)
(*  nothing here excludes a ghost-carrying skeleton.  The side conditions  *)
(*  are prop_sub.v §4's, verbatim: the context is [uniq] and the supply    *)
(*  covers it, the pattern and the subject.                               *)
(* ===================================================================== *)

Corollary e_sub_impl_complete : forall S0 NM M P0 Θ0 P
    (HP : lc_pskl P) (HP0 : lc_pskl P0) (HD : aenv_defs_mono Θ0)
    (H : e_sub_order S0 NM M P0 Θ0 P) Sd Θd Qd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Qd ⊣ Θd }}e ->
  uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P [<=] S0 ->
  exists r ps,
    e_sub_impl S0 NM M P0 Θ0 P HP HP0 HD H = Some r
    /\ (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
    /\ swaps_atoms ps Sd [=] sb_supply (proj1_sig r)
    /\ swaps_aenv ps Θd = sb_ctx (proj1_sig r)
    /\ swaps_pskl ps Qd = sb_out (proj1_sig r).
Proof.
  intros * Hd Hu Hcov.
  set (Ho := e_sub_order_to_call _ _ _ _ _ _ H).
  destruct (e_sub_call_impl_complete Ho HP HP0 HD Ho Hu Hcov Sd Θd Qd Hd)
    as [r0 [ps [Heq [Hav [HS [HT HQ]]]]]].
  unfold e_sub_impl. fold Ho.
  destruct (e_sub_call_impl (sub_call_sub P) S0 NM M P0 Θ0 HP HP0 HD Ho)
    as [ [rr Hrr] | ] eqn:Hcl;
    try rewrite Hcl in Heq; cbn [sub_call_answer proj1_sig] in Heq;
    [ inversion Heq; subst | discriminate ].
  eexists; exists ps.
  split; [ reflexivity | ].
  split; [ exact Hav | ]. split; [ exact HS | ].
  split; [ exact HT | exact HQ ].
Qed.

Corollary e_sub_flex_impl_complete : forall S0 NM M P0 Θ0 Ξ α
    (HP0 : lc_pskl P0) (HD : aenv_defs_mono (Ξ ++ Θ0))
    (H : e_sub_flex_order S0 NM M P0 Θ0 Ξ α) Sd Θd Qd,
  e_sub_flex S0 NM M P0 Θ0 Ξ α Qd Sd Θd ->
  uniq (Ξ ++ Θ0) ->
  ftvar_in_aenv (Ξ ++ Θ0) ∪ ftvar_in_pskl P0 ∪ singleton α [<=] S0 ->
  exists r ps,
    e_sub_flex_impl S0 NM M P0 Θ0 Ξ α HP0 HD H = Some r
    /\ (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
    /\ swaps_atoms ps Sd [=] sb_supply (proj1_sig r)
    /\ swaps_aenv ps Θd = sb_ctx (proj1_sig r)
    /\ swaps_pskl ps Qd = sb_out (proj1_sig r).
Proof.
  intros * Hd Hu Hcov.
  set (Ho := e_sub_flex_order_to_call _ _ _ _ _ _ _ H).
  destruct (e_sub_call_impl_complete Ho I HP0 HD Ho Hu Hcov Sd Θd Qd Hd)
    as [r0 [ps [Heq [Hav [HS [HT HQ]]]]]].
  unfold e_sub_flex_impl. fold Ho.
  destruct (e_sub_call_impl (sub_call_flex Ξ α) S0 NM M P0 Θ0 I HP0 HD Ho)
    as [ [rr Hrr] | ] eqn:Hcl;
    try rewrite Hcl in Heq; cbn [sub_call_answer proj1_sig] in Heq;
    [ inversion Heq; subst | discriminate ].
  eexists; exists ps.
  split; [ reflexivity | ].
  split; [ exact Hav | ]. split; [ exact HS | ].
  split; [ exact HT | exact HQ ].
Qed.

(** ⭐ The subtyping headline, over the argument-free runner of
    def_sub_impl.v §4 — the twin of [e_sub_run_sound]. *)
Theorem e_sub_run_complete : forall S0 NM M P0 Θ0 P
    (HP : lc_pskl P) (HP0 : lc_pskl P0) (HD : aenv_defs_mono Θ0) Sd Θd Qd,
  {{ S0 ↝ Sd ⊨ Θ0 ⊢[ NM | M | P0 ] P ⩽ Qd ⊣ Θd }}e ->
  uniq Θ0 ->
  ftvar_in_aenv Θ0 ∪ ftvar_in_pskl P0 ∪ ftvar_in_pskl P [<=] S0 ->
  exists r ps,
    e_sub_run S0 NM M P0 Θ0 P HP HP0 HD = Some r
    /\ (forall a b, In (a, b) ps -> a `notin` S0 /\ b `notin` S0)
    /\ swaps_atoms ps Sd [=] sb_supply r
    /\ swaps_aenv ps Θd = sb_ctx r
    /\ swaps_pskl ps Qd = sb_out r.
Proof.
  intros * Hd Hu Hcov. unfold e_sub_run.
  destruct (e_sub_impl_complete HP HP0 HD
              (@e_sub_order_total S0 NM M P0 Θ0 P HP HP0 HD)
              Hd Hu Hcov) as [r [ps [Heq [Hav [HS [HT HQ]]]]]].
  rewrite Heq.
  exists (proj1_sig r), ps.
  split; [ reflexivity | ].
  split; [ exact Hav | ]. split; [ exact HS | ].
  split; [ exact HT | exact HQ ].
Qed.
