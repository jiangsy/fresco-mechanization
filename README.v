(** Frost re-mechanization — the compilable paper-to-Coq theorem index.

    THIS FILE IS A HEADLINE INDEX, NOT A CATALOGUE.  It lists the results a
    reader of the paper would come looking for: the flagship theorems, the
    P5/P6 chain thm:complete-subtyping is assembled from, and (§V) the
    expressiveness results backing the paper's PROSE claims.  Everything the
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

    JUDGEMENT DELIMITERS — the SYSTEM is the brace pair, and each pair is its
    own notation scope (legend: frost/notations.v).
      [{{ … }}d]  declarative ([d_*], over Γ)
      [{{ … }}ad] declarative over algorithmic contexts ([ad_*], over Θ)
      [{{ … }}a]  algorithmic ([a_*], with [⊣ Θ'])
      [{{ … }}da]  ε-tagged decorated ([a_consistag] / [a_subtag])
    That frees the turnstile for the judgement's own two axes:
      SUPERSCRIPT = WHICH COPY (in practice, the SORT).  bare = types,
        [⊢ˢ] = skeletons, [⊢ᵉ] = expressions ([a_wf_exp]), [⊢ˢᵈ] =
        syntax-directed — so [{{ Γ ⊢ˢ[M] e ⦂ P }}d] is skeleton inference and
        [{{ Γ ⊢[M] e ⦂ A }}d] is typing.  Where one relation covers both sorts
        the sort is the bracket index instead ([⊢[ N | m | P0 ]]).
      SUBSCRIPT = WHICH RELATION, when a system has several at one sort:
        [⊢ᵣ]/[⊢ᵣₚ] refinement, [⊢ₚᵣ] precision, [⊢ₛ]/[⊢ₑ] the solve layer,
        and [⊢ₚ]/[⊢ᵦ]/[⊢ᵤ]/[⊢ₚₛ]/[⊢ᵤₛ] for well-formedness.
    A judgement about a CONTEXT ALONE puts the turnstile first: [{{ ⊢ Θ }}a]
    is [a_wf_aenv] (the paper's [Θ ⊢ ctx]).
    One relation's copies across systems now differ by the DELIMITER alone:
    [{{ Γ ⨟ Δ ⊢ᵣ Q ⊳ P }}d] vs [{{ Θ ⨟ Δ ⊢ᵣ Q ⊳ P }}ad].
      [ … ] carries the indices, [⊣ Θ'] the output context.  ⚠️ [⦂] is used at
      every mode: [⇨] would claim synthesis, which only holds at [M = TI].  *)

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.deco_algo.def_decorated.
Require Import src.frost.def_extra.
Require Import src.frost.coercions.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.notations.
Require Import src.frost.algo.def_extra.          (* the algorithmic judgement notations *)
Require Import src.frost.algo.def_meta.            (* κ ∷ Θ ⊑ Θ', Θ ⊴ Θ' *)
Require Import src.frost.algo_decl.def_consis_refine.
Require Import src.frost.algo_decl.def_subtyping.
Require Import src.frost.algo_decl.def_typing.
Require Import src.frost.decl.prop_wellformed.
Require Import src.frost.decl.prop_syntax_directed.
Require Import src.frost.decl.prop_general_subsumption.
Require Import src.frost.decl.prop_stability.       (* order irrelevance *)
Require Import src.frost.decl.prop_shallow.         (* the two expressiveness results *)
Require Import src.frost.algo.consis.prop_soundness_consis.
Require Import src.frost.algo.consis.prop_completeness_consis.
Require Import src.frost.deco_algo.prop_soundness_sub.
Require Import src.frost.algo.sub.prop_completeness_sub_precise.
Require Import src.frost.algo.sub.look.prop_eq_var.
Require Import src.frost.algo.sub.look.prop_eq_cstr.
Require Import src.frost.algo.sub.look.prop_sub_var.
Require Import src.frost.algo.sub.look.prop_sub_cstr.
Require Import src.frost.algo.sub.look.prop_extract.
Require Import src.frost.algo.sub.prop_completeness_sub.
Require Import src.frost.algo.pat.prop_soundness_pat.
Require Import src.frost.algo.typing.prop_soundness_typing.
Require Import src.frost.algo.prop_precise.      (* the {{ _ ⨟ _ ⊢ₚᵣ _ ⊑ _ }}ad notation *)
Require Import src.frost.algo.prop_precise_sub.
Require Import src.frost.algo.pat.prop_completeness_pat.
Require Import src.frost.algo.typing.prop_completeness_typing.
Require Import src.frost.algo.typing.prop_closed.


(* ##################################################################### *)
(*  I.  THE DECLARATIVE SYSTEM — full-decl-proofs.tex                     *)
(* ##################################################################### *)

(* Lemma [Soundness of the syntax-directed rules]  lemma:typing-syn-soundness *)
Check d_sd_typing_sound :
  forall M Γ e B, {{ Γ ⊢ˢᵈ[ M ] e ⦂ B }}d -> {{ Γ ⊢[ M ] e ⦂ B }}d.
Print Assumptions d_sd_typing_sound.

(* Lemma [Completeness of the syntax-directed rules]  lemma:typing-syn-completeness *)
Check d_sd_typing_complete :
  forall M Γ e B, {{ Γ ⊢[ M ] e ⦂ B }}d -> d_wf_denv Γ -> {{ Γ ⊢ˢᵈ[ M ] e ⦂ B }}d.
Print Assumptions d_sd_typing_complete.

(* Theorem [General subsumption] — proved on the SYNTAX-DIRECTED system (the
   "Removed base terms" rework moved it there); the [d_typing] form is a
   corollary. *)
Check d_sd_typing_general_subsumption :
  forall Γ e A B m,
  d_wf_denv Γ ->
  {{ Γ ⊢ˢᵈ[ mode_ti ] e ⦂ (ptyp_to_btyp_syn A) }}d ->
  {{ empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⩽ B }}d ->
  {{ Γ ⊢ˢᵈ[ m ] e ⦂ B }}d.
Print Assumptions d_sd_typing_general_subsumption.

Check d_typing_general_subsumption :
  forall Γ e A B m,
  {{ Γ ⊢[ mode_ti ] e ⦂ (ptyp_to_btyp_syn A) }}d ->
  {{ empty ⨟ Γ ⊢[ m ] (ptyp_to_utyp_syn A) ⩽ B }}d ->
  {{ Γ ⊢[ m ] e ⦂ B }}d.
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
  {{ Θ0 ⊢[ P0 ] P ∼ P' ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  Θ0 ⊴ Θ1 /\
  (exists Qt, bskl_to_pskl Qt = P' /\
     {{ empty ⨟ Θ1 ⊢ˢ (pskl_to_uskl P) ∼ Qt }}ad /\
     {{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ Qt }}ad) /\
  {{ Θ1 ⨟ empty ⊢ᵣₚ P ⊳ P' }}ad.
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
  {{ Θ0 ⊢[ NM | M | P0 ] P ⩽ P' ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P }}a ->
  (NM = a_sub_mode_sk -> a_sk_mode_compat M P0) ->
  (NM = a_sub_mode_ty -> a_ty_mode_compat M P0) ->
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\
  exists Qt,
    bskl_to_pskl Qt = P' /\
    ({{ empty ⨟ Θ1 ⊢ˢ[ NM | M ] (pskl_to_uskl P) ⩽ Qt }}ad) /\
    {{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ Qt }}ad.
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
Check ad_pat_sub_precise_upre_fuel.
Print Assumptions ad_pat_sub_precise_upre_fuel.
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
  {{ Θ0 ⊢ˢ[ m ; P0 ] e ⦂ P ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_sk_mode_compat m P0 ->
  {{ Θ0 ⊢ᵉ e }}a ->
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\
  exists Qt, bskl_to_pskl Qt = P /\
    ({{ Θ1 ⊢ˢ[ m ] e ⦂ Qt }}ad) /\
    ({{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ Qt }}ad).
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
  {{ Θ0 ⊢[ m ; P0 ] e ⦂ A ⊣ Θ1 }}a ->
  {{ ⊢ Θ0 }}a ->
  {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
  a_ty_mode_compat m P0 ->
  {{ Θ0 ⊢ᵉ e }}a ->
  Θ0 ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ a_wf_ptyp Θ1 A /\
  exists Bt, btyp_to_ptyp Bt = A /\
    ({{ Θ1 ⊢ˢᵈ[ m ] e ⦂ Bt }}ad) /\
    ({{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P0) ⊳ (btyp_to_bskl Bt) }}ad).
Print Assumptions a_typing_sound.

(* ⭐ …AT A CLOSED PROGRAM, which is the form a reader wants — one statement
   per user-facing mode, and the DECLARATIVE side is now the paper's own
   §declarative system [{{ … }}d] over a declarative context, not [{{ … }}ad] over
   [nil : aenv].  At the EMPTY context three premises of the theorem above go:
   [{{ ⊢ · }}a] is a constructor, [{{ · ⨟ ∅ ⊢ₚₛ P0 }}a] is [a_wf_pskl__hole] resp.
   the annotation's own wf, and [a_ty_mode_compat] is read off the mode; and
   the answer's colouring is forced by the mode, so the existential [Bt]
   collapses to [syn{A}] resp. [inh{A}].
   ⚠️ [{{ · ⊢ᵉ e }}a] stays: it is the INPUT condition on the problem (the
   paper's "M is well-formed in Θ₀"), and the algorithmic run does not imply
   it — see the header note in typing/prop_closed.v.
   ⭐ [ζ] CLOSES the run's output context, which normally still holds
   flexibles ([fun x -> x] returns [α̂ → α̂] with [Θ1 = α̂]); it is built, not
   assumed, so the statement is not vacuous (algo_decl/prop_conserv.v §11).
   The [{{ … }}ad] → [{{ … }}d] translation is the prose-completion of the paper's
   [app:decl-in-algo-context] "it is easy to extend them to algorithmic
   contexts Θ" — algo_decl/prop_conserv.v, docs/PAPER-GAPS.md. *)
Check a_typing_sound_infer :
  forall e A Θ1,
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⊢[ mode_ti ; pskl_hole ] e ⦂ A ⊣ Θ1 }}a ->
  nil ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ a_wf_ptyp Θ1 A /\
  ({{ Θ1 ⨟ empty ⊢ᵣ bskl_hole ⊳ (btyp_to_bskl (ptyp_to_btyp_syn A)) }}ad) /\
  exists ζ, ζ ∷ Θ1 ⊑ nil /\
    ({{ nil ⊢ˢᵈ[ mode_ti ] e ⦂ (ptyp_to_btyp_syn (msubst_ptyp ζ A)) }}d) /\
    ({{ nil ⊢[ mode_ti ] e ⦂ (ptyp_to_btyp_syn (msubst_ptyp ζ A)) }}d).
Print Assumptions a_typing_sound_infer.

Check a_typing_sound_check :
  forall e A0 A Θ1,
  {{ nil ⊢ᵉ e }}a ->
  a_wf_ptyp nil A0 ->
  {{ nil ⊢[ mode_tc ; (ptyp_to_pskl A0) ] e ⦂ A ⊣ Θ1 }}a ->
  nil ⊴ Θ1 /\ {{ ⊢ Θ1 }}a /\ a_wf_ptyp Θ1 A /\
  ({{ Θ1 ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (ptyp_to_pskl A0))
     ⊳ (btyp_to_bskl (ptyp_to_btyp_inh A)) }}ad) /\
  exists ζ, ζ ∷ Θ1 ⊑ nil /\
    ({{ nil ⊢ˢᵈ[ mode_tc ] e ⦂ (ptyp_to_btyp_inh (msubst_ptyp ζ A)) }}d) /\
    ({{ nil ⊢[ mode_tc ] e ⦂ (ptyp_to_btyp_inh (msubst_ptyp ζ A)) }}d).
Print Assumptions a_typing_sound_check.

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
    {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    a_sk_mode_compat M P0 ->
    κ ∷ Θ0 ⊑ Θ ->
    (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0) ->
    lc_exp e ->
    {{ Θ ⊢ˢ[ M ] e ⦂ Q }}ad ->
    {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ Q }}ad ->
    exists P1 Θ1,
      {{ Θ0 ⊢ˢ[ M ; P0 ] e ⦂ P1 ⊣ Θ1 }}a /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
           {{ Θ ⨟ empty ⊢ₚᵣ (msubst_pskl ζ P1) ⊑ (bskl_to_pskl Q) }}ad).
Print Assumptions a_pat_complete.

(* ⭐⭐⭐ Theorem [Completeness + optimality of type inference]
   thm:complete-type-inference — the typing analogue, with the run's result
   Θ-EQUIVALENT to the declarative type (precision on TYPES is equivalence).
   ⚙ LEXICOGRAPHIC (size_exp e, size_btyp B) induction: ten of the twelve rows
   recurse at a strictly smaller subject; only the two ∀-peeling AbsCheck rows
   recurse at the SAME subject, and they drop one ∀ off the declarative result. *)
Check a_typing_complete :
  forall e M Θ0 P0 κ Θ B,
    {{ ⊢ Θ0 }}a -> {{ ⊢ Θ }}a ->
    {{ Θ0 ⨟ empty ⊢ₚₛ P0 }}a ->
    a_ty_mode_compat M P0 ->
    κ ∷ Θ0 ⊑ Θ ->
    (forall α, α `in` ftvar_in_exp e -> binds α abind_tvar Θ0) ->
    lc_exp e ->
    {{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad ->
    {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh (msubst_pskl κ P0)) ⊳ (btyp_to_bskl B) }}ad ->
    exists A1 Θ1,
      {{ Θ0 ⊢[ M ; P0 ] e ⦂ A1 ⊣ Θ1 }}a /\
      (forall κ1, is_id_msubst κ1 -> κ1 ∷ Θ0 ⊑ Θ1 ->
         exists ζ,
           ζ ∷ Θ1 ⊑ Θ /\
           a_inc_equiv Θ0 κ (msubst_compose ζ κ1) Θ /\
           {{ Θ ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a).
Print Assumptions a_typing_complete.

(* ⭐ …AT A CLOSED PROGRAM.  Same three premises go as in the soundness
   corollaries, plus two more: [κ ∷ · ⊑ ·] holds at [κ = ·] ([a_inc__empty]),
   so no metasubstitution is quantified at all, and the optimality is applied
   at the identity increase SOUNDNESS hands back — leaving the readable form,
   "the answer, closed off by a witness ζ, IS the declarative type".  So the
   run is not merely SOME derivation of [e]: it is the most general one.
   ⭐ And NO condition on the term: since [ad_sd_typing__anno] carries
   [a_wf_ptyp Θ A] like its four type-carrying siblings, a derivation
   EXHIBITS its own subject as well formed ([ad_sd_typing_wf_exp]), so at the
   empty context "[e] is closed" is a theorem.  ⭐ At INFERENCE the refinement
   premise goes too: at [□] it says only that the declarative result is a
   synthesised painting of a well-formed type, and both halves are read off
   the derivation.  So the derivation is the ONLY premise. *)
Check a_typing_complete_infer :
  forall e (B : btyp),
  {{ nil ⊢ˢᵈ[ mode_ti ] e ⦂ B }}ad ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_ti ; pskl_hole ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Print Assumptions a_typing_complete_infer.

(* At CHECKING the checked type is the DECLARATIVE RESULT itself: at [TC] the
   colouring is forced, so the general statement's refinement premise at an
   arbitrary annotation [A0] is reflexivity at [⌊B⌋] and [A0] goes with it.
   Nothing is lost at the empty context — refinement of a ghost-free painting
   takes only the structural rows there (the flexible rows need a definition
   in the context, and [·] has none), so [inh{A0} ⊳ ⌊B⌋] forces [A0 = ⌊B⌋]. *)
Check a_typing_complete_check :
  forall e (B : btyp),
  {{ nil ⊢ˢᵈ[ mode_tc ] e ⦂ B }}ad ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_tc ; (ptyp_to_pskl (btyp_to_ptyp B)) ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Print Assumptions a_typing_complete_check.

(* ⭐⭐ …AND OVER THE PAPER'S OWN §DECLARATIVE SYSTEM.  The two entries above
   read [{{ … }}ad], the decl-in-algo judgement a reader of the paper's
   declarative figure has never met; these read [{{ … }}d], so soundness and
   completeness finally meet on the SAME judgement (the soundness corollaries
   have read [⊢ˢ] / [⊢] since 2026-08-10).

   ⭐ What closed them: the mechanisation stopped deferring the paper's
   presupposition that skeleton consistency implies refinement
   (declarative.tex:2074) and the counterpart's well-formedness for skeleton
   inference (:1595).  Carried on the rules, they make [d_pat] and [ad_pat]
   agree row for row, so [d_sd_typing_to_ad] needs no hypothesis.  Before that
   the bridge carried one that was provably FALSE, hence vacuous —
   docs/ghost-capture.tex, cex/cex_d_pat_bridges_false.v.

   ⚠️ [{{ nil ⊢ᵉ e }}a] is a real premise here and NOT bookkeeping: it is the
   same one the soundness corollaries take, and on the declarative side it is
   not derivable, because [d_sd_typing__anno] states no well-formedness for
   its annotation (the sd-Anno gap, docs/PAPER-GAPS.md). *)
Check a_typing_complete_sd_infer :
  forall e (B : btyp),
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⊢ˢᵈ[ mode_ti ] e ⦂ B }}d ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_ti ; pskl_hole ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Print Assumptions a_typing_complete_sd_infer.

Check a_typing_complete_sd_check :
  forall e (B : btyp),
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⊢ˢᵈ[ mode_tc ] e ⦂ B }}d ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_tc ; (ptyp_to_pskl (btyp_to_ptyp B)) ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Print Assumptions a_typing_complete_sd_check.

(* …and over the ORIGINAL declarative judgement, through the syntax-directed
   system's completeness for it ([d_sd_typing_complete]). *)
Check a_typing_complete_decl_infer :
  forall e (B : btyp),
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⊢[ mode_ti ] e ⦂ B }}d ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_ti ; pskl_hole ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Print Assumptions a_typing_complete_decl_infer.

Check a_typing_complete_decl_check :
  forall e (B : btyp),
  {{ nil ⊢ᵉ e }}a ->
  {{ nil ⊢[ mode_tc ] e ⦂ B }}d ->
  exists A1 Θ1,
    {{ nil ⊢[ mode_tc ; (ptyp_to_pskl (btyp_to_ptyp B)) ] e ⦂ A1 ⊣ Θ1 }}a /\
    exists ζ, ζ ∷ Θ1 ⊑ nil /\ {{ nil ⊢ (msubst_ptyp ζ A1) ≡ᵗ (btyp_to_ptyp B) }}a.
Print Assumptions a_typing_complete_decl_check.

(* --- the two section-D lemmas the paper states in its own right -------- *)

(* Lemma [Precision extends skeleton subtyping]  lemma:precision-sub *)
Check ad_precise_extends_pat_sub.
Print Assumptions ad_precise_extends_pat_sub.

(* Lemma [Context precision preserves skeleton inference]
   lemma:context-precision-skeleton, over the paper's ⪯ᶜᵗˣ *)
Check ad_ctx_precise_pat :
  forall M Θ e Q,
  {{ Θ ⊢ˢ[ M ] e ⦂ Q }}ad ->
  forall Θ', {{ Θ' ⪯ᶜᵗˣ Θ }}ad -> {{ ⊢ Θ }}a -> {{ ⊢ Θ' }}a -> {{ Θ' ⊢ˢ[ M ] e ⦂ Q }}ad.
Print Assumptions ad_ctx_precise_pat.


(* ##################################################################### *)
(*  V.  WHAT THE DECLARATIVE SYSTEM CAN EXPRESS                           *)
(*      ⚙ These three back claims the paper makes in PROSE rather than as *)
(*      numbered theorems, so each entry cites the PASSAGE.  They are the *)
(*      terminal results of decl/prop_stability.v and decl/prop_shallow.v *)
(*      — nothing in the tree consumes them, which is exactly why they    *)
(*      belong here: without an entry their assumption reports are never  *)
(*      printed.                                                          *)
(* ##################################################################### *)

(* ⭐ ORDER IRRELEVANCE — "Fresco is not sensitive to argument order"
   (overview.tex:859, the paragraph of that name).  Permuting a function-typed
   variable's arguments, and its argument types with them, does not affect
   typability: one [Permutation] moves the [(type, term)] pairs together, the
   head carries an arbitrary n-quantifier prefix and an arbitrary codomain, and
   the result [B'] at mode [m] is arbitrary.  [Permutation] is symmetric, so
   this gives the "iff" for free.
   ⚙ [d_wf_denv Γ] is REQUIRED, not cosmetic: inverting the head's [ti]
   derivation yields [B1 = ⌈A₀⌉ˢ] for SOME binding of [x], and [uniq Γ] is what
   identifies that [A₀] with the lemma's own (decl/prop_stability.v). *)
Check d_typing_order_irrel :
  forall Γ m n x y args args' A B',
  d_wf_denv Γ ->
  Permutation args args' ->
  binds x (dbind_typ (ptyp_forall_prefix n (curry_ptyp args A))) Γ ->
  binds y (dbind_typ (ptyp_forall_prefix n (curry_ptyp args' A))) Γ ->
  {{ Γ ⊢[ m ] (curry_exp (exp_var_f x) args) ⦂ B' }}d ->
  {{ Γ ⊢[ m ] (curry_exp (exp_var_f y) args') ⦂ B' }}d.
Print Assumptions d_typing_order_irrel.

(* SHALLOW SUBTYPING IS SUBSUMED — the LOWER bound on [⩽]'s expressive power.
   [{{ Γ ⊢ A ≤ B }}d] ([d_shallow_sub], decl/def_extra.v:375) is the standard
   shallow polymorphic subtyping relation with MONOTYPE instantiation that
   declarative.tex:1191 defines; the claim that check-mode [⩽] subsumes it is
   at :1179.  ⚠️ Both passages currently sit inside an [\iffalse] block, so
   this entry is a mechanized claim looking for a home in the paper, not a
   transcription of a live one. *)
Check d_shallow_sub_complete :
  forall Γ A A',
  {{ Γ ⊢ A ≤ A' }}d ->
  {{ empty ⨟ Γ ⊢[ mode_tc ] (ptyp_to_utyp_syn A) ⩽ (ptyp_to_btyp_inh A') }}d.
Print Assumptions d_shallow_sub_complete.

(* ONLY POLYTYPES NEED ANNOTATION — a MONOTYPE annotation on a lambda binder
   is always redundant: the monotype is guessed or inherited instead
   (introduction.tex:171, also [\iffalse]'d).  The domain is forced rather
   than assumed — any [btyp] erasing to a monotype [A] IS [inh{A}] at every
   mode ([mono_btyp_to_ptyp_inv]).
   ⚠️ ASCRIPTIONS [(e : A)] are NOT erasable even at a monotype: the
   annotation's role there is MODE, not polymorphism — [freeze e] has no
   inference-mode typing at all ([freeze_no_infer], decl/prop_annotation.v),
   so an ascription can be the only way to give a term a [ti] typing. *)
Check mono_lambda_anno_redundant :
  forall m Γ A e B2,
  mono_ptyp A ->
  {{ Γ ⊢[ m ] (exp_abs_anno A e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B2) }}d ->
  {{ Γ ⊢[ m ] (exp_abs e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B2) }}d.
Print Assumptions mono_lambda_anno_redundant.
