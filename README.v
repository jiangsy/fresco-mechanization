(** Frost re-mechanization — the compilable paper-to-Coq theorem index.

    THIS FILE IS A HEADLINE INDEX, NOT A CATALOGUE.  It lists the results a
    reader of the paper would come looking for: the flagship theorems, and the
    P5/P6 chain thm:complete-subtyping is assembled from.  Everything the
    mechanization found BEYOND the paper — the facts it asserts inline and
    never states, the external wf conditions, the refuted statements — is
    recorded in docs/PAPER-GAPS.md and docs/WF-SIDE-CONDITIONS.md, not here.

    ⚠️ A lemma having a paper label is NOT a reason to appear here.  The tree
    has hundreds of supporting results — generalized forms (`*_gen`), fuel/μ
    bundles, renaming kits, scoping invariants — and they belong in their own
    files.  The exhaustive per-lemma map is [PROGRESS.md] Part 1; this file
    stays short enough to read in one sitting.

    EVERY ENTRY HAS THE SAME THREE PARTS:
      (1) the paper's Lemma/Theorem name and label;
      (2) [Check name : <type>] — the statement ASCRIBED, in the paper's own
          notation, so the paper form is MACHINE-CHECKED rather than a prose
          comment.  A bare [Check name.] is used where the full type is
          bookkeeping (ρ / Ψ / Θw indices) that would obscure more than it
          shows — the statement is then in the cited file;
      (3) [Print Assumptions name] IMMEDIATELY AFTER, so a claim and its axiom
          status sit together.

    The build tail prints one assumption report per entry and EVERY one must
    read "Closed under the global context".

    ⚙ "External wf" premises are the ones the paper states in PROSE, outside
    its rules ("as usual, all inputs are well-formed").  A Coq [Inductive] has
    no such notion, so each becomes an explicit hypothesis; the registry is
    docs/WF-SIDE-CONDITIONS.md.  Departures from the paper's own statements
    are in docs/PAPER-GAPS.md and flagged ⚠️ at the entry.

    NOTATION
      Γ / Θ  declarative / algorithmic context      Ξ  suffix (fresh block)
      Δ, Ψ   tag context, tag scope                 κ, ζ  metasubstitutions
      A B C  ptyp, btyp, utyp                       P Q R  pskl, bskl, uskl
      κ ∷ Θ₀ ⊑ Θ  information increase              Θ₀ ⊴ Θ₁  its relational form
      ∼ consistency   ⩽ subtyping   ⦂ a term's type / skeleton (at any mode)
      ⊳ refinement    ⊑ᵖ partial precision   ≡ᵗ/≡ˢ/≡ᵘ equivalence
      ⊑ (bare) is information increase, above   ⪯ᶜᵗˣ ctx precision

    TURNSTILE DECORATIONS — two axes, two devices (legend: frost/notations.v).
      SUPERSCRIPT = the SYSTEM, and nothing else — never two marks at once.
        [⊢] declarative, [⊢ᵃᵈ] declarative-over-Θ ([ad_*]), [⊢ᵃ] algorithmic
        ([a_*]), [⊢ᵗ] ε-tagged decorated, [⊢ˢ] syntax-directed (declarative
        only — the ad system has no other typing judgement, so [ad_sd_typing]
        is plain [⊢ᵃᵈ]).
      SUBSCRIPT = the SORT.  bare = types, [⊢ₛ] = skeletons — used exactly
        where the system has one relation PER sort ([⊢ₛ[M] e ⦂ P] skeleton
        inference vs [⊢[M] e ⦂ A] typing).  Where one relation covers both,
        the sort is the bracket index instead ([⊢ᵃ[ N | m | P0 ]]).
      [ … ] carries the indices, [⊣ Θ'] the output context.  ⚠️ [⦂] is used at
      every mode: [⇨] would claim synthesis, which only holds at [M = TI].  *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.decorated_algo.def_decorated.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.          (* the algorithmic judgement notations *)
Require Import src.frost.algo.def_meta.            (* κ ∷ Θ ⊑ Θ', Θ ⊴ Θ' *)
Require Import src.frost.decorated_algo.def_decl_algo.
Require Import src.frost.decorated_algo.def_decl_algo_sub.
Require Import src.frost.decorated_algo.def_decl_algo_typing.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_syntax_directed.
Require Import src.frost.decl.prop_general_subsumption.
Require Import src.frost.algo.consis.prop_soundness_consis.
Require Import src.frost.algo.consis.prop_completeness_consis.
Require Import src.frost.decorated_algo.prop_decorate_key.
Require Import src.frost.algo.sub.prop_completeness_sub_precise.
Require Import src.frost.algo.sub.look.prop_eq_var.
Require Import src.frost.algo.sub.look.prop_eq_cstr.
Require Import src.frost.algo.sub.look.prop_sub_var.
Require Import src.frost.algo.sub.look.prop_sub_cstr.
Require Import src.frost.algo.sub.look.prop_extract.
Require Import src.frost.algo.sub.prop_completeness_sub.
Require Import src.frost.algo.pat.prop_soundness_pat.
Require Import src.frost.algo.typing.prop_soundness_typing.
Require Import src.frost.algo.prop_precise.      (* the ⊢ₚᵣᵃᵈ _ ⊑ _ notation *)
Require Import src.frost.algo.prop_precise_sub.
Require Import src.frost.algo.pat.prop_completeness_pat.
Require Import src.frost.algo.typing.prop_typing.


(* ##################################################################### *)
(*  I.  THE DECLARATIVE SYSTEM — full-decl-proofs.tex                     *)
(* ##################################################################### *)

(* Lemma [Soundness of the syntax-directed rules]  lemma:typing-syn-soundness *)
Check d_sd_typing_sound :
  forall M Γ e B, Γ ⊢ˢ[ M ] e ⦂ B -> Γ ⊢[ M ] e ⦂ B.
Print Assumptions d_sd_typing_sound.

(* Lemma [Completeness of the syntax-directed rules]  lemma:typing-syn-completeness *)
Check d_sd_typing_complete :
  forall M Γ e B, Γ ⊢[ M ] e ⦂ B -> d_wf_denv Γ -> Γ ⊢ˢ[ M ] e ⦂ B.
Print Assumptions d_sd_typing_complete.

(* Theorem [General subsumption] — proved on the SYNTAX-DIRECTED system (the
   "Removed base terms" rework moved it there); the [d_typing] form is a
   corollary. *)
Check d_sd_typing_general_subsumption :
  forall Γ e A B m,
  d_wf_denv Γ ->
  Γ ⊢ˢ[ mode_ti ] e ⦂ (ptyp_to_btyp_syn A) ->
  empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⩽ B ->
  Γ ⊢ˢ[ m ] e ⦂ B.
Print Assumptions d_sd_typing_general_subsumption.

Check d_typing_general_subsumption :
  forall Γ e A B m,
  Γ ⊢[ mode_ti ] e ⦂ (ptyp_to_btyp_syn A) ->
  empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⩽ B ->
  Γ ⊢[ m ] e ⦂ B.
Print Assumptions d_typing_general_subsumption.


(* ##################################################################### *)
(*  II.  CONSISTENCY — consistency-proofs.tex (appendix B)                *)
(* ##################################################################### *)

(* ⭐ Theorem [Soundness of consistency]  thm:sound-consistency
   A run is an information increase whose output is a declarative consistency
   at a colouring of the result, refining the inherited painting of the input.
   ⚙ Derived from the DECORATED induction.  The paper's two-slot [∼] is the
   output-suppressed abbreviation, so assign / unify / consis form ONE SCC and
   their soundness is a single 3-way mutual induction — exactly as the paper
   organises its own proof. *)
Check a_consis_sound :
  forall Θ0 P0 P P' Θ1,
  Θ0 ⊢ᵃ[ P0 ] P ∼ P' ⊣ Θ1 ->
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  Θ0 ⊴ Θ1 /\
  (exists Qt, bskl_to_pskl Qt = P' /\
     empty ⨟ Θ1 ⊢ᵃᵈ (pskl_to_uskl P) ∼ Qt /\
     Θ1 ⨟ empty ⊢ᵣᵃᵈ (pskl_to_bskl_inh P0) ⊳ Qt) /\
  Θ1 ⨟ empty ⊢ᵣₚᵃᵈ P ⊳ P'.
Print Assumptions a_consis_sound.

(* ⭐ Theorem [Completeness and optimality of consistency]
   thm:complete-consistency.  Whenever a solution κ of the question (Θ₀; P₀)
   makes the declarative judgement hold, the algorithm SUCCEEDS, and its answer
   FACTORS through the solution — ∃ζ. ζ ∷ Θ₁ ⊑ Θ ∧ ζ ∘ κ₁ ≡ κ ∧ ζP₁ ⊑ ⌊Qb⌋.
   That factoring IS the optimality.
   ⚠️ The paper's 2-condition statement is FALSE as literally given; what is
   proved is the AUGMENTED one.  docs/PAPER-GAPS.md. *)
Check a_consis_complete.
Print Assumptions a_consis_complete.


(* ##################################################################### *)
(*  III.  SUBTYPING — subtyping-proofs.tex                                *)
(* ##################################################################### *)

(* ⭐ Theorem [Soundness of subtyping]  thm:sound-subtyping *)
Check a_sub_sound :
  forall NM M P0 Θ0 P P' Θ1,
  Θ0 ⊢ᵃ[ NM | M | P0 ] P ⩽ P' ⊣ Θ1 ->
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
  Θ0 ⊴ Θ1 /\ a_wf_aenv Θ1 /\
  exists Qt,
    bskl_to_pskl Qt = P' /\
    (empty ⨟ Θ1 ⊢ᵃᵈ[ NM | M ] (pskl_to_uskl P) ⩽ Qt) /\
    Θ1 ⨟ empty ⊢ᵣᵃᵈ (pskl_to_bskl_inh P0) ⊳ Qt.
Print Assumptions a_sub_sound.

(* ⭐⭐⭐ Theorem [Completeness and optimality of subtyping]
   thm:complete-subtyping (algorithmic.tex:1446) — UNCONDITIONAL: no residual
   hypothesis.
   Premises beyond the paper's are the EXTERNAL wf side conditions
   (docs/WF-SIDE-CONDITIONS.md): wf of the counterpart, and the subject's
   ghost-freeness at the TY sort. *)
Check a_sub_complete.
Print Assumptions a_sub_complete.

(* --- the chain thm:complete-subtyping is assembled from ----------------
     P5        stability of subtyping under more precise substitution  :1664
     P6-Cv/Cs  completeness of CONSISTENCY constraint collection + solving
                                       (consistency-proofs :1180 / :920)
     P6-Sv/Ss  the SUBTYPING analogues                      :1696 / :2202
     P6-L      look completeness                                     :2730
   ⚠️ P6-Ss's Sub-ForallR needs a MODE-GUARDED ftv-𝒞 disjunction: the sub-side
   analogue of [ad_pat_consis_target_ftv] is FALSE
   (cex/cex_p6ss_sub_target_ftv.v).  ⚠️ P6-Cs carries one paper-EXTERNAL wf
   side condition whose NECESSITY is machine-checked
   (cex/cex_p6cs_subject_wf.v).  Both in docs/PAPER-GAPS.md.
   ⚙ Bare [Check]s deliberately: these statements carry the ρ / Ψ / Θw
   bookkeeping that makes the induction go through, and printing it here would
   bury the chain.  The statements are in the files named above. *)
Check ad_pat_sub_precise_upre.
Print Assumptions ad_pat_sub_precise_upre.
Check a_solve_eq_complete_var.
Print Assumptions a_solve_eq_complete_var.
Check a_lookeq_solve_complete.
Print Assumptions a_lookeq_solve_complete.
Check a_solve_sub_complete_var.
Print Assumptions a_solve_sub_complete_var.
Check a_looksub_solve_complete.
Print Assumptions a_looksub_solve_complete.
Check a_extract_complete.
Print Assumptions a_extract_complete.


(* ##################################################################### *)
(*  IV.  SKELETON + TYPE INFERENCE — proofs.tex (section D)               *)
(*       ⭐⭐⭐ THE FOUR FLAGSHIP THEOREMS                                  *)
(* ##################################################################### *)

(* ⭐⭐⭐ Theorem [Soundness of skeleton inference]  thm:sound-skeleton-inference
   An [a_pat] run is an information increase whose output context carries the
   DECLARATIVE skeleton inference at a colouring of the output, refining the
   inherited painting of the input skeleton.
   External side condition: wf of the term ([a_wf_exp] — the problem
   definition's "M is well-formed in Θ₀"). *)
Check a_pat_sound :
  forall m Θ0 P0 e P Θ1,
  Θ0 ⊢ₛᵃ[ m ; P0 ] e ⦂ P ⊣ Θ1 ->
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_sk_mode_compat m P0 ->
  a_wf_exp Θ0 e ->
  Θ0 ⊴ Θ1 /\ a_wf_aenv Θ1 /\
  exists Qt, bskl_to_pskl Qt = P /\
    (Θ1 ⊢ₛᵃᵈ[ m ] e ⦂ Qt) /\
    (Θ1 ⨟ empty ⊢ᵣᵃᵈ (pskl_to_bskl_inh P0) ⊳ Qt).
Print Assumptions a_pat_sound.

(* ⭐⭐⭐ Theorem [Soundness of type inference]  thm:sound-type-inference
   The same statement one layer up, with [a_ty_mode_compat] for
   [a_sk_mode_compat].  ⚙ The conclusion additionally carries [a_wf_ptyp Θ1 A]
   — the output type is scoped in the output context, which AT-App consumes.
   ⚠️ FOUR rule-level side conditions the paper leaves to prose are stated ON
   the rules (docs/PAPER-GAPS.md): the two Barendregt conditions the four
   suffix-DISCARDING check rows need for lemma:suffix-erasure, the [uniq]
   filter AT-Abs needs on guess^TY's block, and the correction of
   AT-AbsAnnoCheck's result domain. *)
Check a_typing_sound :
  forall m Θ0 P0 e A Θ1,
  Θ0 ⊢ᵃ[ m ; P0 ] e ⦂ A ⊣ Θ1 ->
  a_wf_aenv Θ0 ->
  Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
  a_ty_mode_compat m P0 ->
  a_wf_exp Θ0 e ->
  Θ0 ⊴ Θ1 /\ a_wf_aenv Θ1 /\ a_wf_ptyp Θ1 A /\
  exists Bt, btyp_to_ptyp Bt = A /\
    (Θ1 ⊢ᵃᵈ[ m ] e ⦂ Bt) /\
    (Θ1 ⨟ empty ⊢ᵣᵃᵈ (pskl_to_bskl_inh P0) ⊳ (btyp_to_bskl Bt)).
Print Assumptions a_typing_sound.

(* ⭐⭐⭐ Theorem [Completeness + optimality of skeleton inference]
   thm:complete-skeleton-inference.  Whenever the DECLARATIVE system infers Q
   at a solution κ of the question (Θ₀; M; P₀), the ALGORITHM succeeds and its
   answer FACTORS through the solution — the same factored optimality as
   thm:complete-subtyping:
     ∀κ₁ identity out of Θ₀. ∃ζ.  ζ ∷ Θ₁ ⊑ Θ  ∧  ζ ∘ κ₁ ≡ κ  ∧  ζP₁ ⊑ ⌊Q⌋
   ⚙ TERM-SIZE induction only: the mech FUSED the paper's P-Sub into the three
   base rows, so every recursive premise is at a strict subterm.
   What the four theorems carry BEYOND the paper's own premises is
   registered in docs/WF-SIDE-CONDITIONS.md. *)
Check a_pat_complete :
  forall e M Θ0 P0 κ Θ Q,
    a_wf_aenv Θ0 -> a_wf_aenv Θ ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
    a_sk_mode_compat M P0 ->
    κ ∷ Θ0 ⊑ Θ ->
    (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0) ->
    lc_exp e ->
    Θ ⊢ₛᵃᵈ[ M ] e ⦂ Q ->
    Θ ⨟ empty ⊢ᵣᵃᵈ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q ->
    exists P1 Θ1,
      Θ0 ⊢ₛᵃ[ M ; P0 ] e ⦂ P1 ⊣ Θ1 /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
           Θ ⨟ empty ⊢ₚᵣᵃᵈ (msubst_pskl ζ P1) ⊑ (bskl_to_pskl Q)).
Print Assumptions a_pat_complete.

(* ⭐⭐⭐ Theorem [Completeness + optimality of type inference]
   thm:complete-type-inference — the typing analogue, with the run's result
   Θ-EQUIVALENT to the declarative type (precision on TYPES is equivalence).
   ⚙ LEXICOGRAPHIC (size_exp e, size_btyp B) induction: ten of the twelve rows
   recurse at a strictly smaller subject; only the two ∀-peeling AbsCheck rows
   recurse at the SAME subject, and they drop one ∀ off the declarative result. *)
Check a_typing_complete :
  forall e M Θ0 P0 κ Θ B,
    a_wf_aenv Θ0 -> a_wf_aenv Θ ->
    Θ0 ⨟ empty ⊢ₚₛᵃ P0 ->
    a_ty_mode_compat M P0 ->
    κ ∷ Θ0 ⊑ Θ ->
    (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0) ->
    lc_exp e ->
    Θ ⊢ᵃᵈ[ M ] e ⦂ B ->
    Θ ⨟ empty ⊢ᵣᵃᵈ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) ->
    exists A1 Θ1,
      Θ0 ⊢ᵃ[ M ; P0 ] e ⦂ A1 ⊣ Θ1 /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
           Θ ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B)).
Print Assumptions a_typing_complete.

(* --- the two section-D lemmas the paper states in its own right -------- *)

(* Lemma [Precision extends skeleton subtyping]  lemma:precision-sub *)
Check ad_precise_extends_pat_sub_v.
Print Assumptions ad_precise_extends_pat_sub_v.

(* Lemma [Context precision preserves skeleton inference]
   lemma:context-precision-skeleton, over the paper's ⪯ᶜᵗˣ *)
Check ad_ctx_precise_pat :
  forall M Θ e Q,
  Θ ⊢ₛᵃᵈ[ M ] e ⦂ Q ->
  forall Θ', Θ' ⪯ᶜᵗˣ Θ -> a_wf_aenv Θ -> a_wf_aenv Θ' -> Θ' ⊢ₛᵃᵈ[ M ] e ⦂ Q.
Print Assumptions ad_ctx_precise_pat.
