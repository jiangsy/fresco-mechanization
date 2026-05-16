(** * Frost mechanization — paper-to-Coq theorem index.

    This file collects all major paper-claimed theorems and lemmas of
    the Frost system, mapping each one to its Coq counterpart in the
    mechanization. For each lemma we record:

    - the paper reference (Lemma / Theorem label, section, line);
    - the Coq lemma name and its containing file;
    - the closure status ([Qed] vs [Admitted]).

    The index is structured to mirror the paper's structure:
    declarative properties (Section 3 / [declarative.tex]), then the
    syntax-directed appendix ([syntax-directed.tex]), then the proof
    appendix ([proofs.tex]).

    To re-verify the index against the codebase, run:
        cd mechanization && make coq
        grep -cE "^\\s*Admitted\\." frost/decl/*.v frost/algo/*.v

    For faster development iteration on large files like
    [frost/decl/prop_typing.v] (~5 minutes single-threaded), use:
        cd mechanization && make quick        (* vos: skips opaque-proof
                                                 checking, ~3-4x faster *)
        cd mechanization && make NJOBS=8 coq  (* parallel kernel check *)

    [make coq] runs full kernel acceptance and is the bar for committing.
    [make quick] is a development convenience — run [make coq] before
    pushing.
*)

Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_subtyping.
Require Import src.frost.decl.prop_typing.
Require Import src.frost.decl.prop_skeleton.

(* ========================================================================== *)
(*  SECTION 3 — DECLARATIVE PROPERTIES (paper [declarative.tex])              *)
(* ========================================================================== *)

(** ** Lemma 3.1 — General subsumption.
    Paper [declarative.tex:574]. Mechanised as
    [d_typing_general_subsumption_via_gen], a one-line corollary of D12
    (Lemma B.5, [d_typing_general_subsumption_gen]). Status: [Qed]
    proof body. Transitive axiom count via [Print Assumptions] at the
    end of this file. *)
Check d_typing_general_subsumption_via_gen.

(** ** Lemma 3.2 — Soundness of subtyping.
    Paper [declarative.tex:1095]. Mechanised as [d_sub_sound]. Status:
    stated under [is_typ A] precondition; [Qed]. *)
Check d_sub_sound.

(** ** Lemma 3.3 — No guessing of polytypes.
    Paper [declarative.tex:1102] (paper itself flags as "sketchy").
    Strict-equality form is PROVABLY FALSE — concrete counter-example
    documented inline in [prop_subtyping.v]. Status: [Admitted] as a
    paper-claim placeholder (to be tweaked to a weaker form in a
    future paper-revision pass). *)
Check d_sub_no_guess_uniqueness.

(** ** Lemma 3.4 — Refinement preserves well-formedness.
    Paper [declarative.tex:1380]. Status: [Qed]. *)
Check d_refine_preserves_wf.

(** ** Lemma 3.7 — Preservation of Skeleton Well-formedness.
    Paper [declarative.tex:1970]. Mechanised as the d_pat half of the
    mutual [d_typing_pat_preserves_wf]. Status: [Qed].

    See also [d_pat_preserves_skel_wf] (specialised wrapper in
    prop_skeleton.v) for the named paper-facing form. *)
Check d_typing_pat_preserves_wf.
Check d_pat_preserves_skel_wf.

(** ** Lemma 3.8 — Validity of skeleton inference.
    Paper [declarative.tex:1981]. Status: [Admitted] (depends on
    Phase 3 refinement reflexivity + d_pat_consis ghost-case
    narrowing). *)
Check d_pat_validity.

(** ** Lemma 3.9 — Safety of skeleton inference.
    Paper [declarative.tex:1986]. Status: [Admitted] (depends on
    principal-skeleton construction — a join operation on skeletons
    under refinement). *)
Check d_pat_safety.

(* ========================================================================== *)
(*  APPENDIX B — SYNTAX-DIRECTED LEMMAS (paper [syntax-directed.tex])         *)
(* ========================================================================== *)

(** ** Lemma B.2 — Consistency Transitivity.
    Paper [syntax-directed.tex:146]. Status: [Qed] (post the
    [d_consis__forall_inh] structural fix matching paper's
    [typconsis] [ForallInh] rule; 3 new live cofinite-rename cases
    closed in this pass). *)
Check d_consis_compose.

(** ** Lemma B.3 — Consistency-Subtyping Transitivity.
    
    TODO: this lemma should be renamed, d_consis_extends_d_sub is a 
    misleading name.  
    
    Paper [syntax-directed.tex:161]. Paper statement (verbatim):
        If d_consis_gen Δ1 Γ T T'
        and d_sub_gen M Δ2 Γ T' A,
        then d_sub_gen M (Δ1 ∪ Δ2) Γ T A.

    IMPORTANT: the paper uses the GENERALISED relations (d_consis_gen +
    d_sub_gen, syntax-directed.tex §"Generalised subtyping/consistency").
    Our mechanization does NOT currently have a lemma matching this
    exact statement.

    What we have instead:
    - [d_consis_extends_d_sub] in [prop_subtyping.v]: same SHAPE but
      uses the NON-generalised relations (d_consis + d_sub). It is
      auxiliary scaffolding consumed by D12 via [d_sub_gen_trans]; it
      is NOT a direct mechanization of paper B.3. Status: proof body
      has 1 admit (d_sub__check sub-case post-refactor).
    - [d_consis_extends_d_sub_gen_nil] in [prop_typing.v]: closer to
      B.3 in spirit (uses d_sub_gen on the second relation) but
      specialized to Δ = nil and still uses d_consis (not d_consis_gen)
      on the first. Status: [Qed].

    A faithful mechanization of B.3 is a TODO. Soundness of the current
    [d_consis_extends_d_sub] in the DECLARATIVE rule set has not been
    independently audited; the proof skeleton was ported from algorithmic
    intuition. The remaining admit is the locus where post-refactor
    soundness must be re-validated. *)
Check d_consis_extends_d_sub.

(** ** Lemma B.4 — Subtyping Transitivity.
    Paper [syntax-directed.tex:249]. Mechanised as [d_sub_gen_trans]
    over the generalised subtyping relation. Status: [Qed]. *)
Check d_sub_gen_trans.

(** ** Lemma B.5 — Generalised General Subsumption (D12).
    Paper [syntax-directed.tex:343]. Mechanised as
    [d_typing_general_subsumption_gen]. Status: proof body is [Qed]
    (all 4 __abs / __abs_anno × m_orig admits closed; __app case closed
    via [d_consis_gen_refl_is_typ]). Remaining axioms are TRANSITIVE
    dependencies through helpers — see [Print Assumptions] at file end. *)
Check d_typing_general_subsumption_gen.

(* ========================================================================== *)
(*  APPENDIX D — PROOF APPENDIX (paper [proofs.tex])                          *)
(* ========================================================================== *)

(** ** Lemma D.1 — Stability.
    Paper [proofs.tex:15]. Mechanised as several stability lemmas:
    [d_typing_swap_mono] (S1, argument-permutation),
    [d_typing_app_restructure] (S2, application-restructuring),
    [d_typing_order_irrel_adj] (order-irrelevance, 2-arg adjacent).
    Status: all [Admitted] (research-grade — require d_pat inversion
    machinery, namely a d_pat-from-d_typing lemma). *)
Check d_typing_swap_mono.
Check d_typing_app_restructure.
Check d_typing_order_irrel_adj.

(** ** Lemma D.2 / 3.6 — Structural rules.
    Paper [proofs.tex:20] / Lemma 3.6 in main text. Mechanised as
    several weakening lemmas:
    - [d_typing_pat_weakening] ([Qed], in prop_typing.v).
    - [d_typing_pat_subst_typ_mut] ([Admitted], 18-case mechanical
      substitution proof). *)
Check d_typing_pat_weakening.
Check d_typing_pat_subst_typ_mut.

(** ** Lemma D.4 — Splitting refines.
    Paper [proofs.tex:33]. Mechanised as a family of split lemmas:
    [d_refine_arrow_split], [d_refine_all_plain_split],
    [d_refine_hole_split], [d_refine_tophole_split] plus their
    syn-painted variants. Status: all [Qed]. *)
Check d_refine_arrow_split.
Check d_refine_all_plain_split.
Check d_refine_hole_split.
Check d_refine_tophole_split.

(** NOTE: Earlier drafts of this index conflated "D.5 — Consistency
    extends subtyping" with B.3 above. Paper Lemma D.5 (in [proofs.tex])
    is an ALGORITHMIC property, not a declarative one — there is no
    declarative paper-claim for "consis extends subtyping". Removed
    the duplicate reference here; [d_consis_extends_d_sub] in our
    mechanization is auxiliary scaffolding for D12 (see CAVEAT under
    Lemma B.3 above), not the D.5 of [proofs.tex]. *)

(* ========================================================================== *)
(*  E1 — EXPRESSIVENESS BENCHMARK (paper §3.D design)                         *)
(* ========================================================================== *)

(** Church-encoded existentials — three concrete typing theorems
    (introduction, elimination, round-trip) demonstrating
    impredicative encoding. Status: all [Admitted] (research-grade —
    gated on [d_typing_pat_subst_typ_mut]). *)
Check E1_intro.
Check E1_elim.
Check E1_roundtrip.

(* ========================================================================== *)
(*  SUPPORTING META-THEORY (mechanization-internal but paper-faithful)        *)
(* ========================================================================== *)

(** ** Subtype reflexivity on mono types.
    Used in __refl_mono of D12. Status: [Qed]. *)
Check d_sub_refl_mono.
Check d_sub_refl_mono_mode.

(** ** Mode-lift on mono types.
    [d_typing mode_ti] lifts to any compatible mode at the same mono
    type. Status: [Admitted] at __app (function arg-type mono not
    derivable from d_typing__app's premises — research-grade gap
    shared with D12's __app). *)
Check d_typing_lift_mono.

(** ** Completeness of d_sub w.r.t. monotype-only shallow sub.
    Status: [Admitted] (refl on polytypes / typ_all_col → typ_all_etag
    translation gap — paper-flagged design issue). *)
Check d_sub_complete_mono.

(** ** Generalised consistency: structural reflexivity on is_inh_typ.
    [d_consis_gen_refl] — the mechanised form of the implicit paper
    fact "typconsis is reflexive on inh{∀}-types" used in the __app
    step of Lemma B.5. Status: [Qed]. *)
Check d_consis_gen_refl.

(** ** Generalised → original bridges.
    [d_consis_gen_to_d_consis] and [d_sub_gen_to_d_sub] — the bridge
    lemmas that bring the generalised relations back down to the
    original ones. Both [Qed] post the [d_consis__forall_inh]
    structural fix. *)
Check d_consis_gen_to_d_consis.
Check d_sub_gen_to_d_sub.

(** ** Generalised typing → original typing collapse.
    [d_typing_gen_collapse] — the structural collapse driving D1's
    corollary. Status: [Qed]. *)
Check d_typing_gen_collapse.

(** ** Narrowing under consistency equivalence.
    [d_typing_narrow_consis] — restricted (non-circular) narrowing
    used by D12's __abs / __abs_anno + __arg cases. Status: [Admitted]
    (re-encoding gap on __var case; the body 18-case mutual closes
    post-rewrite). *)
Check d_typing_narrow_consis.
Check d_typing_gen_narrow_consis.

(* ========================================================================== *)
(*  REMOVED LEMMAS (paper-misaligned or provably false in current rules)      *)
(* ========================================================================== *)

(** The following were removed from the codebase as PROVABLY FALSE
    under the current rule set; closure requires rule-definition
    changes flagged in inline comments.

    - [d_typing_check_is_inh] / [d_typing_gen_check_is_inh] (paper-level
      colour invariant "mode_tc has is_inh_typ output"):
      [d_typing__freeze] inherits the inner mode_ti type without
      repainting — concrete counter-example: [exp_anno e0
      (inh_color (ctyp_all (ctyp_var_b 0)))] produces a [typ_all_col
      colour_syn] output, which after __freeze becomes the mode_tc
      output but is NOT [is_inh_typ]. Paper-faithful fix requires
      restating [__freeze] / [__abs] / [__abs_anno] / [__app] to thread
      [is_inh_typ] on the result-side type.

    - [d_consis_lhs_is_syn_typ]: provably false post the new
      [d_consis__forall_inh] rule. Counter-example: [A = typ_all_col
      colour_inh (typ_var_b 0)] is [is_inh_typ] and [d_consis nil Γ A A]
      is derivable (via __forall_inh with trivial cofinite premise),
      but [is_syn_typ A] FAILS at the head. *)

(* ========================================================================== *)
(*  PRINT ASSUMPTIONS — D1 / D12 transitive axiom list                        *)
(* ========================================================================== *)

(** Re-verify the transitive axiom dependencies of the two flagship
    declarative theorems. Run `make coq` then `coqc -R . src README.v`
    (or step through this file in vsrocq) to see the live output.

    Current state (2026-05-17): 2 transitive axioms, both isolated to
    the helper layer:
    - [d_typing_gen_lift_mono] — mode-lift on mono types. Admitted at
      __app (function arg-type [P'] may be polytype; closure requires
      D12, creating a cycle that needs mutual induction or inlining
      ~400 lines of SPLIT helpers into D12 to break).
    - [prop_subtyping.d_consis_extends_d_sub] — admitted at __check
      sub-case (post-refactor: the [d_consis__forall_syn] rule allows
      non-mono LHS, breaking the [T mono → A = T] chain). See CAVEAT
      under Lemma B.3 in this file. *)

Print Assumptions d_typing_general_subsumption_via_gen.
Print Assumptions d_typing_general_subsumption_gen.
