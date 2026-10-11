(** Declarative SKELETON INFERENCE and SYNTAX-DIRECTED TYPING in algorithmic
    contexts (paper app:decl-in-algo-context, fig:declarative-in-algo-context).

    The last missing piece of the [decl-in-algo-context] layer: [def_consis_refine.v]
    ported consistency / refinement / well-formedness, [def_subtyping.v]
    ported subtyping, and this file ports the two judgements section D's
    soundness and completeness theorems are stated against —
    [d_pat] (skeleton inference) and [d_sd_typing] (syntax-directed typing).

    ⭐ WHICH TYPING JUDGEMENT.  The paper's appendix ports the SYNTAX-DIRECTED
    system, not [d_typing]: "For syntax-directed typing, we only need to extend
    freezing and annotated lambda rules with explicit type equivalence
    premises" (full-algo-spec.tex:117).  The two are equivalent declaratively
    ([d_sd_typing_sound] / [d_sd_typing_complete], decl/prop_syntax_directed.v),
    and it is the syntax-directed one the algorithm mirrors rule for rule.

    ⭐ WHAT CHANGES, AND WHAT DOES NOT.  Per the appendix, "for most rules we
    simply replace declarative contexts Γ with algorithmic contexts Θ", and new
    rules are needed only where a FLEXIBLE variable can appear.  Neither
    judgement here looks a type variable up directly — every type-level lookup
    happens inside the embedded subtyping / consistency / refinement premises,
    which already carry their flexible rows ([ad_pat_sub__flex_mono],
    [ad_pat_consis__flex_l] / [__flex_r], [ad_refine_syn__flex_l] / [__flex_r]).
    So NO new rule is added here.  What IS added, verbatim from the appendix's
    figure, are the THREE explicit type-equivalence premises: α-equivalence is
    implicit in the declarative system but must be stated once flexibles exist,
    and the three rules that silently reuse an annotation are

      [sdtylab{Freeze}]        [{{ Θ ⊢ B ≡ᵗ A }}a]   (the synthesised premise's type
                                               vs the inherited conclusion's)
      [sdtylab{AbsAnnoCheck}]  [{{ Θ ⊢ A ≡ᵗ A' }}a]  (the binding's annotation vs the
                                               conclusion's domain)
      [sdtylab{AbsAnno}]       [{{ Θ ⊢ A ≡ᵗ A' }}a]  (same, in the non-check modes)

    ⭐ LEAF-VALID EMBEDDING.
    The three BASE rows of each judgement embed the join with its LEAF DATUM.
    thm:complete-subtyping can only CONSUME a leaf-valid join, and the capture
    configuration (subject [∀X.◇], counterpart [∀ˢX.X]) shows the datum is NOT
    recoverable from a join that lacks it and IS reachable here:
    cex/cex_ad_pat_join_not_leaf_valid.v.  This is the paper's own AUGMENTED
    consistency-solution notion propagating one layer up.

    [ad_pat_sub] carries that datum itself, so the rows embed the PAPER'S
    OWN relation, with no proof measure in the specification.

    ⚙ SORTS.  [ad_pat_sub] is the paper's ALL-IN-ONE subtyping box
    [typsub[N][M][Ψ]] — one judgement over [uskl]/[bskl] carrying the paper's
    N ∈ {TY, SK} as an index (def_subtyping.v).  So the declarative
    [d_pat_sub] premises of [d_pat] become [ad_pat_sub] at [a_sub_mode_sk] with
    their sorts unchanged, and the [d_sub] premises of [d_sd_typing] become
    [ad_pat_sub] at [a_sub_mode_ty] with their TYPE sorts painted into the
    skeleton sorts ([ptyp_to_uskl_syn] on the subject, [btyp_to_bskl] on the
    target) — the same embedding the subtyping flagships already use at TY.

    Naming follows the layer: [ad_*] = the [d_*] judgement over an [aenv],
    written with the [}}ad] delimiter. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.basic.def_meta.
Require Import src.fresco.algo_decl.def_consis_refine.
Require Import src.fresco.algo_decl.def_subtyping.

Set Implicit Arguments.

(* the judgement notations below live in this scope; `Open Scope` is not
   transitive through `Require Import`, so the DECLARING file must open it *)
Open Scope fresco_ad_scope.

Reserved Notation "{{ Θ ⊢ˢ[ M ] e ⦂ Q }}ad"
  (at level 0, M at level 0, e at level 74, Q at level 74,
   format "'{{'  Θ  ⊢ˢ[  M  ]  e  ⦂  Q  '}}ad'").
Reserved Notation "{{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad"
  (at level 0, M at level 0, e at level 74, B at level 74,
   format "'{{'  Θ  ⊢ˢᵈ[  M  ]  e  ⦂  B  '}}ad'").

(* ===================================================================== *)
(*  Skeleton inference over Θ  (decl [{{ Γ ⊢ˢ[M] e ⦂ Q }}d], fig:decl-skeleton- *)
(*  inference).  Self-contained: its App rule INFERS the function's       *)
(*  skeleton, so there is no mutual block with typing.                    *)
(* ===================================================================== *)

Inductive ad_pat : mode -> aenv -> exp -> bskl -> Prop :=
| ad_pat__unit : forall Θ m Q,                                   (* P-Unit *)
    (* ⭐ [paper-gap] THE COUNTERPART'S DISCIPLINED WF, on all three base
       rows (2026-08-07, hand-off §5).  The embedded subtyping's external
       side condition is well-formedness of BOTH sides (declarative.tex:1427;
       WF-SIDE-CONDITIONS.md), and [Q] is otherwise unconstrained here —
       [ad_pat_sub_target_scope_ty] gives only scope, and the wf cannot propagate
       top-down (it dies at [ad_pat__app]'s existential premise skeleton, and
       the refinement rules alone do not preserve wf:
       [ad_refine_syn_output_not_wf], cex/cex_refine_not_transitive.v).
       lemma:context-precision's Var case and thm:complete-skeleton-
       inference's Sub case both consume exactly this premise; soundness
       supplies it from the run by [a_sub_output_wf] (algo/basic/prop_wf_preservation.v
       — the algorithm's outputs ARE well-formed). *)
    {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
    ad_pat_sub a_sub_mode_sk m empty Θ uskl_unit Q ->
    {{ Θ ⊢ˢ[ m ] exp_unit ⦂ Q }}ad
| ad_pat__var : forall Θ m x (P : pskl) b Q,                      (* P-Var *)
    (* the paper's single [x : P] entry, in either of its two [abind] forms *)
    binds x b Θ ->
    abind_to_pskl b = Some P ->
    {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
    ad_pat_sub a_sub_mode_sk m empty Θ
      (bskl_to_uskl (pskl_to_bskl_syn P)) Q ->
    {{ Θ ⊢ˢ[ m ] (exp_var_f x) ⦂ Q }}ad
| ad_pat__anno : forall Θ m e (A : ptyp) Q,                      (* P-Anno *)
    (* no wf premise on [A], as in the paper and [d_pat__anno] *)
    {{ Θ ⨟ empty ⊢ₚₛ (bskl_to_pskl Q) }}a ->
    ad_pat_sub a_sub_mode_sk m empty Θ
      (bskl_to_uskl (pskl_to_bskl_syn (ptyp_to_pskl A))) Q ->
    {{ Θ ⊢ˢ[ m ] (exp_anno e A) ⦂ Q }}ad
| ad_pat__freeze : forall Θ e P,                               (* P-Freeze *)
    {{ Θ ⊢ˢ[ mode_ti ] e ⦂ (pskl_to_bskl_syn P) }}ad ->
    {{ Θ ⊢ˢ[ mode_tc ] (exp_freeze e) ⦂ (pskl_to_bskl_syn P) }}ad
| ad_pat__abs : forall L Θ m e P Q,                               (* P-Abs *)
    m <> mode_tc ->
    {{ Θ ⨟ empty ⊢ₚₛ P }}a ->
    mod_comp_sk (bskl_arrow (pskl_to_bskl_inh P) Q) m ->
    (forall x, x `notin` L ->
       {{ ((x ~ abind_var_skl P) ++ Θ) ⊢ˢ[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q }}ad) ->
    {{ Θ ⊢ˢ[ m ] (exp_abs e) ⦂ (bskl_arrow (pskl_to_bskl_inh P) Q) }}ad
| ad_pat__abs_anno : forall L Θ m e (A : ptyp) (B : btyp) Q,  (* P-AbsAnno *)
    m <> mode_tc ->
    a_wf_ptyp Θ A ->
    btyp_to_ptyp B = A ->
    mod_comp_sk (bskl_arrow (btyp_to_bskl B) Q) m ->
    (forall x, x `notin` L ->
       {{ ((x ~ abind_var_typ A) ++ Θ) ⊢ˢ[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ Q }}ad) ->
    {{ Θ ⊢ˢ[ m ] (exp_abs_anno A e) ⦂ (bskl_arrow (btyp_to_bskl B) Q) }}ad
| ad_pat__app : forall Θ m e1 e2 P (Q1 Q2 : bskl),                (* P-App *)
    {{ Θ ⊢ˢ[ mode_tc ] e2 ⦂ (pskl_to_bskl_syn P) }}ad ->
    {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P) ⊳ Q1 }}ad ->
    {{ Θ ⊢ˢ[ mode_fn m ] e1 ⦂ (bskl_arrow Q1 Q2) }}ad ->
    {{ Θ ⊢ˢ[ m ] (exp_app e1 e2) ⦂ Q2 }}ad
| ad_pat__abs_check : forall L Θ e P,                        (* P-AbsCheck *)
    (forall x, x `notin` L ->
       {{ ((x ~ abind_var_skl pskl_ghost) ++ Θ) ⊢ˢ[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ (pskl_to_bskl_syn P) }}ad) ->
    {{ Θ ⊢ˢ[ mode_tc ] (exp_abs e)
      ⦂ (bskl_univ_ghost (bskl_arrow bskl_ghost (pskl_to_bskl_syn P))) }}ad
| ad_pat__abs_anno_check : forall L Θ e A P,             (* P-AbsAnnoCheck *)
    a_wf_ptyp Θ A ->
    (forall x, x `notin` L ->
       {{ ((x ~ abind_var_typ A) ++ Θ) ⊢ˢ[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ (pskl_to_bskl_syn P) }}ad) ->
    {{ Θ ⊢ˢ[ mode_tc ] (exp_abs_anno A e)
      ⦂ (bskl_univ_ghost (bskl_arrow (btyp_to_bskl (ptyp_to_btyp_syn A))
                                  (pskl_to_bskl_syn P))) }}ad
where "{{ Θ ⊢ˢ[ M ] e ⦂ Q }}ad" := (ad_pat M Θ e Q) : fresco_ad_scope.

(* ===================================================================== *)
(*  Syntax-directed typing over Θ  (decl [{{ Γ ⊢ˢᵈ[M] e ⦂ B }}d], + the paper's *)
(*  three explicit type-equivalence premises).                            *)
(* ===================================================================== *)

Inductive ad_sd_typing : mode -> aenv -> exp -> btyp -> Prop :=
| ad_sd_typing__unit : forall Θ m B,                            (* sd-Unit *)
    ad_pat_sub a_sub_mode_ty m empty Θ
      (ptyp_to_uskl_syn ptyp_unit) (btyp_to_bskl B) ->
    {{ Θ ⊢ˢᵈ[ m ] exp_unit ⦂ B }}ad
| ad_sd_typing__var : forall Θ m x A B,                          (* sd-Var *)
    binds x (abind_var_typ A) Θ ->
    ad_pat_sub a_sub_mode_ty m empty Θ
      (ptyp_to_uskl_syn A) (btyp_to_bskl B) ->
    {{ Θ ⊢ˢᵈ[ m ] (exp_var_f x) ⦂ B }}ad
| ad_sd_typing__anno : forall Θ m e A B,                        (* sd-Anno *)
    (* ⭐ [paper-gap] THE ANNOTATION IS WELL-FORMED IN Θ.  Its four
       type-carrying siblings ([__abs_check_base], [__abs_anno_check_base],
       [__abs], [__abs_anno]) all state this; sd-Anno was the one rule that
       did not, and without it a derivation says NOTHING about the scope of
       the types the term mentions — [ad_pat_sub_target_scope_ty] constrains only
       the join's TARGET.  With it, [ad_sd_typing_wf_exp] holds: a derivation
       exhibits its own subject as a well-formed term, which is what the
       paper's ambient "all inputs are well-formed" means.
       docs/PAPER-GAPS.md. *)
    a_wf_ptyp Θ A ->
    {{ Θ ⊢ˢᵈ[ mode_tc ] e ⦂ (ptyp_to_btyp_inh A) }}ad ->
    ad_pat_sub a_sub_mode_ty m empty Θ
      (ptyp_to_uskl_syn A) (btyp_to_bskl B) ->
    {{ Θ ⊢ˢᵈ[ m ] (exp_anno e A) ⦂ B }}ad
| ad_sd_typing__freeze : forall Θ e A B,                      (* sd-Freeze *)
    (* ⭐ the appendix's first added premise: the synthesised premise's type
       and the inherited conclusion's need only be EQUIVALENT under Θ, not
       syntactically equal — a flexible in either may stand for the other. *)
    {{ Θ ⊢ˢᵈ[ mode_ti ] e ⦂ (ptyp_to_btyp_syn B) }}ad ->
    {{ Θ ⊢ B ≡ᵗ A }}a ->
    {{ Θ ⊢ˢᵈ[ mode_tc ] (exp_freeze e) ⦂ (ptyp_to_btyp_inh A) }}ad
| ad_sd_typing__abs_check_step : forall L Θ e B,        (* sd-AbsCheck (∀) *)
    (* no [is_ityp] premise, as in the paper and [d_sd_typing]: the body is
       TC-mode, so its type is always inherited *)
    (forall α, α `notin` L ->
       {{ ((α ~ abind_tvar) ++ Θ) ⊢ˢᵈ[ mode_tc ] (exp_abs e)
         ⦂ (open_btyp_wrt_btyp B (btyp_var_f α)) }}ad) ->
    {{ Θ ⊢ˢᵈ[ mode_tc ] (exp_abs e) ⦂ (btyp_all_inh B) }}ad
| ad_sd_typing__abs_check_base : forall L Θ e A B,      (* sd-AbsCheck (→) *)
    a_wf_ptyp Θ A ->
    is_ityp B ->
    (forall x, x `notin` L ->
       {{ ((x ~ abind_var_typ A) ++ Θ) ⊢ˢᵈ[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B }}ad) ->
    {{ Θ ⊢ˢᵈ[ mode_tc ] (exp_abs e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B) }}ad
| ad_sd_typing__abs_anno_check_step : forall L Θ A e B,
                                                    (* sd-AbsAnnoCheck (∀) *)
    (forall α, α `notin` L ->
       {{ ((α ~ abind_tvar) ++ Θ) ⊢ˢᵈ[ mode_tc ] (exp_abs_anno A e)
         ⦂ (open_btyp_wrt_btyp B (btyp_var_f α)) }}ad) ->
    {{ Θ ⊢ˢᵈ[ mode_tc ] (exp_abs_anno A e) ⦂ (btyp_all_inh B) }}ad
| ad_sd_typing__abs_anno_check_base : forall L Θ e A A' B,
    (* ⭐ the appendix's second added premise.  The BINDING keeps the written
       annotation [A]; the conclusion's domain is any Θ-equivalent [A'].
       (The paper writes it under [Θ,ᾱ] because its rule peels the ∀s in one
       step; here [_step] has already extended the context.) *)
    a_wf_ptyp Θ A ->                                (* sd-AbsAnnoCheck (→) *)
    {{ Θ ⊢ A ≡ᵗ A' }}a ->
    is_ityp B ->
    (forall x, x `notin` L ->
       {{ ((x ~ abind_var_typ A) ++ Θ) ⊢ˢᵈ[ mode_tc ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B }}ad) ->
    {{ Θ ⊢ˢᵈ[ mode_tc ] (exp_abs_anno A e)
      ⦂ (btyp_arrow (ptyp_to_btyp_inh A') B) }}ad
| ad_sd_typing__abs : forall L Θ m e A B,                        (* sd-Abs *)
    m <> mode_tc ->
    a_wf_ptyp Θ A ->
    mod_comp_ty (btyp_arrow (ptyp_to_btyp_inh A) B) m ->
    (forall x, x `notin` L ->
       {{ ((x ~ abind_var_typ A) ++ Θ) ⊢ˢᵈ[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B }}ad) ->
    {{ Θ ⊢ˢᵈ[ m ] (exp_abs e) ⦂ (btyp_arrow (ptyp_to_btyp_inh A) B) }}ad
| ad_sd_typing__abs_anno : forall L Θ m e A A' B1 B2,        (* sd-AbsAnno *)
    (* ⭐ the appendix's third added premise, same reading as AbsAnnoCheck's:
       the arrow's domain [B1] erases to a Θ-EQUIVALENT [A'], not to the
       written annotation [A] itself. *)
    m <> mode_tc ->
    a_wf_ptyp Θ A ->
    {{ Θ ⊢ A ≡ᵗ A' }}a ->
    btyp_to_ptyp B1 = A' ->
    mod_comp_ty (btyp_arrow B1 B2) m ->
    (forall x, x `notin` L ->
       {{ ((x ~ abind_var_typ A) ++ Θ) ⊢ˢᵈ[ decr_mode m ]
         (open_exp_wrt_exp e (exp_var_f x)) ⦂ B2 }}ad) ->
    {{ Θ ⊢ˢᵈ[ m ] (exp_abs_anno A e) ⦂ (btyp_arrow B1 B2) }}ad
| ad_sd_typing__app : forall Θ m e1 e2 P A2 B1 B2,               (* sd-App *)
    {{ Θ ⊢ˢ[ mode_tc ] e2 ⦂ (pskl_to_bskl_syn P) }}ad ->
    {{ Θ ⨟ empty ⊢ᵣ (pskl_to_bskl_inh P) ⊳ (btyp_to_bskl B1) }}ad ->
    {{ Θ ⊢ˢᵈ[ (mode_fn m) ] e1 ⦂ (btyp_arrow B1 B2) }}ad ->
    (* ⭐ [paper-gap] THE APPENDIX'S FOURTH TYPE-EQUIVALENCE PREMISE.  The
       appendix (full-algo-spec.tex, fig:declarative-in-algo-context) says
       "for syntax-directed typing, we only need to extend freezing and
       annotated lambda rules with explicit type equivalence premises" —
       but its own proof of thm:sound-type-inference needs one HERE too:
       the AT-App case checks the argument at [inh{A'}] and this rule wants
       it at [inh{A}], and the step "Thus by ⑧ and ⑬, we have
       [Θ3 ⊢ N ⦂ inh{A}]" is exactly the missing bridge.  The reason is the
       appendix's own reason for the other three: in an ALGORITHMIC context
       a flexible may stand for either type, so the function's domain and
       the argument's checked type need only be EQUIVALENT, not equal.
       docs/PAPER-GAPS.md. *)
    {{ Θ ⊢ (btyp_to_ptyp B1) ≡ᵗ A2 }}a ->
    {{ Θ ⊢ˢᵈ[ mode_tc ] e2 ⦂ (ptyp_to_btyp_inh A2) }}ad ->
    {{ Θ ⊢ˢᵈ[ m ] (exp_app e1 e2) ⦂ B2 }}ad
where "{{ Θ ⊢ˢᵈ[ M ] e ⦂ B }}ad" := (ad_sd_typing M Θ e B) : fresco_ad_scope.
