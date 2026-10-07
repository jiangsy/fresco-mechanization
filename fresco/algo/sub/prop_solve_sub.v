(** BASICS for the constraint-SOLVING layer ([a_solve_sub] / [a_solve_eq]),
    docs/DESIGN-subtyping.md §3.3(2).  These are the undecorated shadows of
    the decorated tag-solving ([a_solvetag_sub]/[a_solvetag_eq]); the
    subtyping-decoration lemmas invert [a_sub]'s Extract = look ∘ solve ∘ guess
    into a [solve]/[solvetag] pair, so [solve]'s outputs must be well-behaved.

    First: solving preserves local closure — a locally-closed problem has a
    locally-closed solution. *)

Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Metalib.Metatheory.

Require Import src.fresco.notations.
Require Import src.fresco.coercions.
Require Import src.fresco.def_shapes.
Require Import src.fresco.prop_ln.
Require Import src.fresco.prop_basic.
Require Import src.fresco.decl.def_rules.
Require Import src.fresco.algo.def_rules.
Require Import src.fresco.algo.def_meta.
(* SE-FlexR calls [guess^TY] (2026-08-04), so the solve basics now rest on
   the guess kit — [a_guess_mono_decls] / [_generated_fresh] / [_ftv].  No
   cycle: prop_flex's closure is def_extra, def_meta, def_decorated,
   prop_inc, prop_stability, prop_decorate, none of which sees this file. *)
Require Import src.fresco.algo.prop_basic.
(* the swap kit: equivariance is the renaming primitive the solve's binder
   rows now need (their witness sits IN the premise's context) *)
Require Import src.fresco.algo.prop_swap.

Set Implicit Arguments.

Scheme a_solve_sub_mutind := Induction for a_solve_sub Sort Prop
  with a_solve_eq_mutind  := Induction for a_solve_eq  Sort Prop.
Combined Scheme a_solve_sub_eq_mutind
  from a_solve_sub_mutind, a_solve_eq_mutind.

(* ===================================================================== *)
(*  THE GUESS SIDE OF SE-FlexR.  Three facts about [guess^TY]'s OUTPUT     *)
(*  TYPE, read back into [pskl] — the shape SE-FlexR now returns.          *)
(* ===================================================================== *)

(** [guess^TY] of an (openable) skeleton is locally closed.  Local closure
    of the SOURCE is not a hypothesis: [a_guess_mono] has no row for a bound
    variable, so a derivation exists only for a locally-closed subject. *)
Lemma a_guess_mono_lc : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A -> lc_ptyp A.
Proof.
  intros Θ P Ξ A H; induction H;
    try solve [ assumption | constructor; auto ].
  (* ∀ : the rule's OWN witness serves — close/open round trip *)
  match goal with
  | |- lc_ptyp (ptyp_all (close_ptyp_wrt_ptyp ?b _)) =>
      apply (lc_ptyp_all_exists b);
      rewrite open_ptyp_wrt_ptyp_close_ptyp_wrt_ptyp; assumption
  end.
Qed.

Corollary a_guess_mono_lc_pskl : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A -> lc_pskl (ptyp_to_pskl A).
Proof. intros. apply ptyp_to_pskl_lc. eauto using a_guess_mono_lc. Qed.

(** A GUARDED subject guesses to a guarded result: [guess^TY] is structural
    on the three guarded shapes (unit / var / arrow) and only ghosts move. *)
Lemma a_guess_mono_guarded : forall Θ P Ξ A,
  a_guess_mono Θ P Ξ A -> guarded_pskl P -> guarded_pskl (ptyp_to_pskl A).
Proof.
  intros Θ P Ξ A H Hg; inversion Hg; subst; inversion H; subst; cbn.
  - apply guarded_pskl__unit.
  - apply guarded_pskl__var.
  - apply guarded_pskl__arrow;
      (apply ptyp_to_pskl_lc; eapply a_guess_mono_lc; eassumption).
Qed.

(** A guarded skeleton is locally closed. *)
Lemma guarded_pskl_lc : forall P, guarded_pskl P -> lc_pskl P.
Proof. intros P H; inversion H; subst; constructor; assumption. Qed.

Lemma lc_pskl_arrow_inv : forall P1 P2,
  lc_pskl (pskl_arrow P1 P2) -> lc_pskl P1 /\ lc_pskl P2.
Proof. intros P1 P2 H; inversion H; auto. Qed.

Lemma lc_pskl_tophole_inv : forall P,
  lc_pskl (pskl_tophole P) -> lc_pskl P.
Proof. intros P H; inversion H; auto. Qed.

Lemma lc_pskl_all_syn_inv : forall P,
  lc_pskl (pskl_all_syn P) ->
  forall α, lc_pskl (open_pskl_wrt_pskl P (pskl_var_f α)).
Proof. intros P H; inversion H; auto. Qed.

(** Solving preserves local closure. *)
Lemma a_solve_sub_eq_lc :
  (forall Θ m P P0 Ξ P', {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a ->
     lc_pskl P -> lc_pskl P0 -> lc_pskl P') /\
  (forall Θ P P0 Ξ P', {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
     lc_pskl P -> lc_pskl P0 -> lc_pskl P').
Proof.
  apply a_solve_sub_eq_mutind; intros;
    (* SE-FlexR's output is now [guess^TY]'s, not the flexible *)
    try solve [ eapply a_guess_mono_lc_pskl; eassumption ];
    (* peel structured, non-binder inputs *)
    repeat match goal with
    | H : lc_pskl (pskl_arrow _ _) |- _ =>
        apply lc_pskl_arrow_inv in H; destruct H
    | H : lc_pskl (pskl_tophole _) |- _ => apply lc_pskl_tophole_inv in H
    | H : guarded_pskl _           |- _ => apply guarded_pskl_lc in H
    end;
    (* discharge every case with a non-binder output *)
    try solve
      [ assumption
      | eauto
      | constructor; eauto
      | apply lc_pskl_tophole; eauto
      | apply lc_pskl_tophole; constructor; eauto ].
  (* remaining: binder cases — exists-fresh + close: the rule's OWN β
     serves; the close/open round trip exposes the premise's output. *)
  - (* SS-ForallL : ∀P ≼ Q ⤳ ∀(close β P') *)
    match goal with
    | HP : lc_pskl (pskl_all_syn _) |- lc_pskl (pskl_all_syn (close_pskl_wrt_pskl ?b _)) =>
        apply (lc_pskl_all_syn_exists b);
        rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl;
        match goal with
        | IH : lc_pskl _ -> lc_pskl _ -> lc_pskl _ |- _ =>
            apply IH; [ apply (lc_pskl_all_syn_inv HP) | assumption ]
        end
    end.
  - (* SS-ForallR : A ≼ ∀B ⤳ P' (output passes through; β may escape) *)
    match goal with
    | HQ : lc_pskl (pskl_all_syn _),
      IH : lc_pskl _ -> lc_pskl _ -> lc_pskl _ |- _ =>
        apply IH; [ assumption | apply (lc_pskl_all_syn_inv HQ) ]
    end.
  - (* SE-Forall : ∀P ∼ ∀Q ⤳ ∀(close β P') *)
    match goal with
    | HP : lc_pskl (pskl_all_syn ?p), HQ : lc_pskl (pskl_all_syn ?q)
      |- lc_pskl (pskl_all_syn (close_pskl_wrt_pskl ?b _)) =>
        apply (lc_pskl_all_syn_exists b);
        rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl;
        match goal with
        | IH : lc_pskl _ -> lc_pskl _ -> lc_pskl _ |- _ =>
            apply IH; [ apply (lc_pskl_all_syn_inv HP)
                      | apply (lc_pskl_all_syn_inv HQ) ]
        end
    end.
  - (* SE-GhostForall : ⫯P ∼ ∀Q ⤳ ∀(close β P') *)
    match goal with
    | HQ : lc_pskl (pskl_all_syn _)
      |- lc_pskl (pskl_all_syn (close_pskl_wrt_pskl ?b _)) =>
        apply (lc_pskl_all_syn_exists b);
        rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl;
        match goal with
        | IH : lc_pskl _ -> lc_pskl _ -> lc_pskl _ |- _ =>
            apply IH; [ apply lc_pskl_tophole; assumption
                      | apply (lc_pskl_all_syn_inv HQ) ]
        end
    end.
  - (* SE-ForallGhost : ∀P ∼ ⫯Q ⤳ ∀(close β P') *)
    match goal with
    | HP : lc_pskl (pskl_all_syn _)
      |- lc_pskl (pskl_all_syn (close_pskl_wrt_pskl ?b _)) =>
        apply (lc_pskl_all_syn_exists b);
        rewrite open_pskl_wrt_pskl_close_pskl_wrt_pskl;
        match goal with
        | IH : lc_pskl _ -> lc_pskl _ -> lc_pskl _ |- _ =>
            apply IH; [ apply (lc_pskl_all_syn_inv HP)
                      | apply lc_pskl_tophole; assumption ]
        end
    end.
Qed.

Lemma a_solve_sub_lc : forall Θ m P P0 Ξ P',
  {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a -> lc_pskl P -> lc_pskl P0 -> lc_pskl P'.
Proof. intros; eapply (proj1 a_solve_sub_eq_lc); eauto. Qed.

Lemma a_solve_eq_lc : forall Θ P P0 Ξ P',
  {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a -> lc_pskl P -> lc_pskl P0 -> lc_pskl P'.
Proof. intros; eapply (proj2 a_solve_sub_eq_lc); eauto. Qed.

(** Solving a GUARDED subject yields a guarded solution: a guarded LHS only
    matches rules whose output is again guarded (no ghost/tophole/∀ can be
    introduced on the left).  Needed for the tophole cases of output
    well-formedness. *)
Lemma a_solve_sub_eq_guarded :
  (forall Θ m P P0 Ξ P', {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a ->
     lc_pskl P -> lc_pskl P0 -> guarded_pskl P -> guarded_pskl P') /\
  (forall Θ P P0 Ξ P', {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
     lc_pskl P -> lc_pskl P0 -> guarded_pskl P -> guarded_pskl P').
Proof.
  apply a_solve_sub_eq_mutind; intros;
    (* SE-FlexR: guess^TY is structural on the guarded shapes *)
    try solve [ eapply a_guess_mono_guarded; eassumption ];
    (* a non-guarded subject makes the case vacuous *)
    try solve [ match goal with H : guarded_pskl _ |- _ => inversion H end ];
    (* peel lc of the arrow / tophole subject/rhs *)
    repeat match goal with
    | H : lc_pskl (pskl_arrow _ _) |- _ => apply lc_pskl_arrow_inv in H; destruct H
    | H : lc_pskl (pskl_tophole _) |- _ => apply lc_pskl_tophole_inv in H
    end;
    try solve
      [ assumption
      | eauto
      | constructor; eauto using a_solve_sub_lc, a_solve_eq_lc ].
  - (* SS-ForallR : guarded LHS [A] carried through the ∀-RHS opening *)
    match goal with
    | HQ : lc_pskl (pskl_all_syn _),
      IH : lc_pskl _ -> lc_pskl _ -> guarded_pskl _ -> guarded_pskl _ |- _ =>
        apply IH;
          [ assumption | apply (lc_pskl_all_syn_inv HQ) | assumption ]
    end.
Qed.

(* ===================================================================== *)
(*  ⭐ THE GENERATED BLOCK [Ξ] — the scoping invariants (2026-08-04).       *)
(*                                                                        *)
(*  SE-FlexR is the only row that invents names, and it invents them with  *)
(*  [guess^TY], whose avoid-input is the context it runs at.  Three facts  *)
(*  follow, and between them they are what makes moving [Ξ] around safe:   *)
(*                                                                        *)
(*  (K1) [a_decls Ξ] — the block is undefined flexibles only.  So its      *)
(*       entries carry NO payload, hence (K3) it mentions nothing but its  *)
(*       own names: a block can never be ill-scoped, only mis-NAMED.       *)
(*  (K2) every generated name dodges [ftvar_in_aenv Θ].  This is the       *)
(*       load-bearing one.  It gives at once:                              *)
(*         · NO CAPTURE at the four closing binder rows — their premise    *)
(*           runs at [(β ~ tvar) ++ Θ], whose [ftvar_in_aenv] contains β,  *)
(*           so [β ∉ dom Ξ] and [close_β] cannot bind a generated name;    *)
(*         · SIBLING DISJOINTNESS in the threading rows — the second half  *)
(*           runs at [Ξ1 ++ Θ], so [dom Ξ2 ∩ dom Ξ1 = ∅];                  *)
(*         · disjointness from Θ0 and from the collection's own block in   *)
(*           [a_extract], where the solve runs at [Ξl ++ Θ0].              *)
(*  (K3) [ftvar_in_aenv Ξ ⊆ dom Ξ].                                        *)
(*                                                                        *)
(*  ⚠️ What does NOT follow is [uniq Ξ], and the obstruction is INHERITED,  *)
(*  not new: [a_guess_mono__arrow] runs both halves at the same [Θ], so    *)
(*  guess^TY's own block can self-collide — exactly as [a_looksub__arrow]  *)
(*  can.  Colliding blocks are filtered downstream by [a_sub__forall_l]'s  *)
(*  [uniq (Ξ ++ Θ0)] premise, which is where the tree has always put this  *)
(*  obligation.  Threading the SOLVE's arrow rows still buys the           *)
(*  disjointness of the two sub-blocks, which the completeness            *)
(*  construction needs to build one κ-extension over [Ξ2 ++ Ξ1].          *)
(* ===================================================================== *)

(** (K1) *)
Lemma a_solve_sub_eq_decls :
  (forall Θ m P P0 Ξ P', {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a -> a_decls Ξ) /\
  (forall Θ P P0 Ξ P',   {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a     -> a_decls Ξ).
Proof.
  apply a_solve_sub_eq_mutind; intros;
    try solve
      [ constructor
      | assumption
      | apply a_decls_app; assumption
      | eapply a_guess_mono_decls; eassumption ].
Qed.

Lemma a_solve_sub_decls : forall Θ m P P0 Ξ P',
  {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a -> a_decls Ξ.
Proof. intros; eapply (proj1 a_solve_sub_eq_decls); eauto. Qed.

Lemma a_solve_eq_decls : forall Θ P P0 Ξ P',
  {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a -> a_decls Ξ.
Proof. intros; eapply (proj2 a_solve_sub_eq_decls); eauto. Qed.

(** (K2) — the master scoping invariant.  Stated in SET form: the
    per-case reasoning is then pure set algebra and never has to match on
    the shape of an induction hypothesis. *)
Lemma a_solve_sub_eq_generated_fresh_set :
  (forall Θ m P P0 Ξ P', {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a ->
     dom Ξ ∩ ftvar_in_aenv Θ [=] empty) /\
  (forall Θ P P0 Ξ P', {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
     dom Ξ ∩ ftvar_in_aenv Θ [=] empty).
Proof.
  apply a_solve_sub_eq_mutind; intros;
    (* the nil rows *)
    try solve [ simpl; clear; fsetdec ];
    (* the pass-through rows *)
    try solve [ assumption ];
    (* SE-FlexR — guess^TY's own avoid-input, in set form *)
    try solve
      [ apply inter_empty_pointwise; intros α0 Hα0;
        eapply a_guess_mono_generated_fresh; eassumption ];
    (* the four CLOSING binder rows + SS-ForallR: the premise ran at
       [(β ~ tvar) ++ Θ], so its block dodges β as well as Θ *)
    try solve
      [ match goal with
        | IH : dom ?X ∩ ftvar_in_aenv (_ ++ ?Th) [=] empty
          |- dom ?X ∩ ftvar_in_aenv ?Th [=] empty =>
            simpl in IH; clear - IH; fsetdec
        end ].
  (* the THREADING rows (SS-Arrow / SS-GhostLF / SE-Arrow): the second
     block dodges [ftvar_in_aenv (Ξ1 ++ Θ)], which CONTAINS [dom Ξ1] *)
  all: match goal with
       | IH1 : dom ?X1 ∩ ftvar_in_aenv ?Th [=] empty,
         IH2 : dom ?X2 ∩ ftvar_in_aenv (?X1 ++ ?Th) [=] empty
         |- dom (?X2 ++ ?X1) ∩ ftvar_in_aenv ?Th [=] empty =>
           rewrite dom_app; rewrite ftvar_in_aenv_app in IH2;
           clear - IH1 IH2; fsetdec
       end.
Qed.

Lemma a_solve_sub_generated_fresh : forall Θ m P P0 Ξ P',
  {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a ->
  forall α, α `in` dom Ξ -> α `notin` ftvar_in_aenv Θ.
Proof.
  intros * H α Hin.
  pose proof ((proj1 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ _ H) as Hs.
  clear - Hs Hin; fsetdec.
Qed.

Lemma a_solve_eq_generated_fresh : forall Θ P P0 Ξ P',
  {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
  forall α, α `in` dom Ξ -> α `notin` ftvar_in_aenv Θ.
Proof.
  intros * H α Hin.
  pose proof ((proj2 a_solve_sub_eq_generated_fresh_set) _ _ _ _ _ H) as Hs.
  clear - Hs Hin; fsetdec.
Qed.

Corollary a_solve_eq_generated_notin_dom : forall Θ P P0 Ξ P' α,
  {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a -> α `in` dom Ξ -> α `notin` dom Θ.
Proof.
  intros * H Hin.
  pose proof (a_solve_eq_generated_fresh H Hin) as Hfr.
  pose proof (dom_subset_ftvar_in_aenv Θ) as Hd. clear - Hfr Hd. fsetdec.
Qed.

Corollary a_solve_sub_generated_apart_binder : forall β Θ m P P0 Ξ P',
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a -> β `notin` dom Ξ.
Proof.
  intros * H Hin.
  pose proof (a_solve_sub_generated_fresh H Hin) as Hfr.
  simpl in Hfr. clear - Hfr. fsetdec.
Qed.

Corollary a_solve_eq_generated_apart_binder : forall β Θ P P0 Ξ P',
  {{ ((β ~ abind_tvar) ++ Θ) ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a -> β `notin` dom Ξ.
Proof.
  intros * H Hin.
  pose proof (a_solve_eq_generated_fresh H Hin) as Hfr.
  simpl in Hfr. clear - Hfr. fsetdec.
Qed.

(** (K3) — the block mentions exactly its own domain. *)
Lemma a_solve_sub_eq_generated_ftvar :
  (forall Θ m P P0 Ξ P', {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a ->
     ftvar_in_aenv Ξ [<=] dom Ξ) /\
  (forall Θ P P0 Ξ P', {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
     ftvar_in_aenv Ξ [<=] dom Ξ).
Proof.
  apply a_solve_sub_eq_mutind; intros;
    try solve
      [ simpl; clear; fsetdec
      | assumption
      | eapply a_guess_mono_generated_ftvar; eassumption
      | rewrite ftvar_in_aenv_app, dom_app;
        match goal with
        | IH1 : ftvar_in_aenv ?X1 [<=] dom ?X1,
          IH2 : ftvar_in_aenv ?X2 [<=] dom ?X2 |- _ =>
            clear - IH1 IH2; fsetdec
        end ].
Qed.

(** Free variables of the solution.  The EQ half is exact — every eq-∀
    rule CLOSES its output, so eq-solving introduces no new names.  The
    SUB half is DISJUNCTIVE: [SS-ForallR] deliberately lets its binder
    escape into the result (see the constructor comment), so an output
    variable is an input variable OR a name fresh for the context.
    Consumers pin the names they care about inside [dom Θ] (the looked-for
    variable, collected flexibles, binders), where the two readings
    coincide. *)
Lemma a_solve_sub_eq_ftv :
  (forall Θ m P P0 Ξ P', {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a ->
     forall α, α `in` ftvar_in_pskl P' ->
       α `in` (ftvar_in_pskl P `union` ftvar_in_pskl P0) \/
       α `notin` dom Θ) /\
  (forall Θ P P0 Ξ P', {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
     ftvar_in_pskl P' [<=]
       ftvar_in_pskl P `union` ftvar_in_pskl P0 `union` dom Ξ).
Proof.
  apply a_solve_sub_eq_mutind; intros;
    (* ⭐ SE-FlexR is the ONE row that introduces names: [guess^TY] bounds
       its result by the SOURCE plus the block it generated, and a generated
       name dodges [ftvar_in_aenv Θ] — so on the SUB side it lands in the
       RIGHT disjunct and that half's statement is unchanged, while the EQ
       side's formerly-exact bound gains [dom Ξ]. *)
    try solve
      [ (* eq half, SE-FlexR *)
        match goal with
        | Hg : a_guess_mono ?Th ?p ?X ?a
          |- ftvar_in_pskl (ptyp_to_pskl ?a) [<=] _ =>
            pose proof (a_guess_mono_ftv Hg) as Hgf;
            pose proof (ftvar_ptyp_to_pskl a) as Hco;
            clear - Hgf Hco; fsetdec
        end
      | (* sub half has no FlexR row; this arm is inert there *)
        idtac ];
    try solve
      [ (* eq-half exact goals + structure-free ones *)
        cbn [ftvar_in_pskl] in *; fsetdec
      | (* sub-half goals whose LEFT disjunct is direct *)
        cbn [ftvar_in_pskl] in *; left; fsetdec
      | (* eq-half CLOSE cases: the closed payload drops the binder *)
        match goal with
        | IH : ftvar_in_pskl ?p' [<=] _
          |- ftvar_in_pskl (pskl_all_syn (close_pskl_wrt_pskl ?b ?p')) [<=] _ =>
            pose proof (ftvar_in_pskl_close_pskl_wrt_pskl p' b) as Hcl;
            pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f b));
            pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper Q (pskl_var_f b));
            cbn [ftvar_in_pskl] in *; fsetdec
        end ].
  - (* SS-ForallL : disjunct through the close *)
    match goal with
    | IH : forall α, α `in` ftvar_in_pskl ?p' -> _ ,
      Hm : ?a `in` ftvar_in_pskl (pskl_all_syn (close_pskl_wrt_pskl ?b ?p'))
      |- _ =>
        pose proof (ftvar_in_pskl_close_pskl_wrt_pskl p' b) as Hcl;
        cbn [ftvar_in_pskl] in Hm;
        assert (Hin : a `in` ftvar_in_pskl p') by (clear - Hm Hcl; fsetdec);
        assert (Hne : a `notin` singleton b) by (clear - Hm Hcl; fsetdec);
        destruct (IH a Hin) as [Hl | Hr];
          [ pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f b))
              as Hup; cbn [ftvar_in_pskl] in *; left; clear - Hl Hup Hne; fsetdec
          | right; simpl in Hr; clear - Hr; fsetdec ]
    end.
  - (* SS-UnivGhostL *)
    match goal with
    | IH : forall α, α `in` ftvar_in_pskl ?p' -> _ ,
      Hm : ?a `in` ftvar_in_pskl (pskl_tophole ?p') |- _ =>
        cbn [ftvar_in_pskl] in Hm;
        destruct (IH a Hm) as [Hl | Hr];
          [ left; cbn [ftvar_in_pskl] in *; clear - Hl; fsetdec
          | right; simpl in Hr; clear - Hr; fsetdec ]
    end.
  - (* SS-Check — NEW CASE (2026-08-04).  The eq IH's bound was EXACT and
       is now [∪ dom Ξ], so [left] no longer follows on the nose: a
       generated name goes to the RIGHT disjunct, because it dodges
       [ftvar_in_aenv Θ] and a fortiori [dom Θ]. *)
    match goal with
    | Hs : {{ _ ⊢ₑ _ ∼ _ ⤳ ?X ⨾ ?p' }}a ,
      He : ftvar_in_pskl ?p' [<=] _ ,
      Hm : ?a `in` ftvar_in_pskl ?p' |- _ =>
        destruct (AtomSetProperties.In_dec a (dom X)) as [Hd | Hd];
          [ right; eapply a_solve_eq_generated_notin_dom; eassumption
          | left; cbn [ftvar_in_pskl] in *; clear - Hm He Hd; fsetdec ]
    end.
  - (* SS-ForallR : the leak — the output variable is an input variable,
       the escaped binder (fresh for [ftvar_in_aenv Θ] ⊇ [dom Θ] by the
       rule's own condition), or already fresh *)
    match goal with
    | Hfr : ?b `notin` _ ,
      IH : forall α, α `in` ftvar_in_pskl ?p' -> _ ,
      Hm : ?a `in` ftvar_in_pskl ?p' |- _ =>
        pose proof (dom_subset_ftvar_in_aenv Θ) as Hdf;
        destruct (IH a Hm) as [Hl | Hr];
          [ pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f b))
              as Hup; cbn [ftvar_in_pskl] in *;
            destruct (a == b) as [-> | Hne];
              [ right; clear - Hfr Hdf; fsetdec
              | left;
                assert (Hne' : a `notin` singleton b)
                  by (apply notin_singleton_2; auto);
                clear - Hl Hup Hne'; fsetdec ]
          | right; simpl in Hr; clear - Hr; fsetdec ]
    end.
  - (* SS-Arrow : the domain's eq bound now admits [dom Ξ1] (→ right
       disjunct), and the codomain's right disjunct is at the THREADED
       context [Ξ1 ++ Θ], which only makes it stronger *)
    match goal with
    | Hs : {{ _ ⊢ₑ _ ∼ _ ⤳ ?X1 ⨾ ?e' }}a ,
      He : ftvar_in_pskl ?e' [<=] _ ,
      IH : forall α, α `in` ftvar_in_pskl ?p2' -> _ ,
      Hm : ?a `in` ftvar_in_pskl (pskl_arrow ?e' ?p2') |- _ =>
        cbn [ftvar_in_pskl] in Hm;
        apply union_1 in Hm; destruct Hm as [Hm | Hm];
          [ destruct (AtomSetProperties.In_dec a (dom X1)) as [Hd | Hd];
              [ right; eapply a_solve_eq_generated_notin_dom; eassumption
              | left; cbn [ftvar_in_pskl] in *; clear - Hm He Hd; fsetdec ]
          | destruct (IH a Hm) as [Hl | Hr];
              [ left; cbn [ftvar_in_pskl] in *; clear - Hl; fsetdec
              | right; rewrite dom_app in Hr; clear - Hr; fsetdec ] ]
    end.
  - (* SS-GhostLF : both branches at ◇, same treatment as SS-Arrow *)
    match goal with
    | Hs : {{ _ ⊢ₑ _ ∼ _ ⤳ ?X1 ⨾ ?e' }}a ,
      He : ftvar_in_pskl ?e' [<=] _ ,
      IH : forall α, α `in` ftvar_in_pskl ?p2' -> _ ,
      Hm : ?a `in` ftvar_in_pskl (pskl_tophole (pskl_arrow ?e' ?p2')) |- _ =>
        cbn [ftvar_in_pskl] in Hm;
        apply union_1 in Hm; destruct Hm as [Hm | Hm];
          [ destruct (AtomSetProperties.In_dec a (dom X1)) as [Hd | Hd];
              [ right; eapply a_solve_eq_generated_notin_dom; eassumption
              | left; cbn [ftvar_in_pskl] in *; clear - Hm He Hd; fsetdec ]
          | destruct (IH a Hm) as [Hl | Hr];
              [ left; cbn [ftvar_in_pskl] in *; clear - Hl; fsetdec
              | right; rewrite dom_app in Hr; clear - Hr; fsetdec ] ]
    end.
  - (* SE-Arrow — NEW CASE: the block splits, [dom (Ξ2 ++ Ξ1)] *)
    rewrite dom_app.
    match goal with
    | IH1 : ftvar_in_pskl ?p1' [<=] _ , IH2 : ftvar_in_pskl ?p2' [<=] _
      |- ftvar_in_pskl (pskl_arrow ?p1' ?p2') [<=] _ =>
        cbn [ftvar_in_pskl]; clear - IH1 IH2; fsetdec
    end.
Qed.

Lemma a_solve_sub_ftv : forall Θ m P P0 Ξ P',
  {{ Θ ⊢ₛ P ≼[ m ] P0 ⤳ Ξ ⨾ P' }}a ->
  forall α, α `in` ftvar_in_pskl P' ->
    α `in` (ftvar_in_pskl P `union` ftvar_in_pskl P0) \/ α `notin` dom Θ.
Proof. intros; eapply (proj1 a_solve_sub_eq_ftv); eauto. Qed.

Lemma a_solve_eq_ftv : forall Θ P P0 Ξ P',
  {{ Θ ⊢ₑ P ∼ P0 ⤳ Ξ ⨾ P' }}a ->
  ftvar_in_pskl P' [<=]
    ftvar_in_pskl P `union` ftvar_in_pskl P0 `union` dom Ξ.
Proof. intros; eapply (proj2 a_solve_sub_eq_ftv); eauto. Qed.

(* ===================================================================== *)
(*  ⭐ RENAMING THROUGH THE SOLVE — now DERIVED FROM EQUIVARIANCE          *)
(*  (rewritten 2026-08-04; was a 540-line size induction).                 *)
(*                                                                        *)
(*  ⚠️ WHY THE OLD PROOF CANNOT SURVIVE THE REPAIR.  Its binder cases      *)
(*  moved a colliding witness [b] out of the way by renaming the PREMISE   *)
(*  [b ⤳ δ] and then renaming again — and a rename's side condition is     *)
(*  "the source dodges the context".  The solve's binder rows now run      *)
(*  their premise at [(b ~ tvar) ++ Θ] (so that a guess below the binder   *)
(*  cannot generate [b] and be captured by the [close]), and there [b] IS  *)
(*  in the context.  The witness-move is therefore not a rename at all.    *)
(*                                                                        *)
(*  It is a SWAP, and a swap has no freshness side condition: it renames   *)
(*  the context along with everything else ([a_solve_sub_eq_swap],         *)
(*  prop_swap.v).  With [swap_pskl_as_subst] the whole family collapses to *)
(*  three rewrites.  This is the swap kit's stated purpose — equivariance  *)
(*  as THE renaming primitive — reaching the solve layer.                  *)
(*                                                                        *)
(*  The hypotheses are correspondingly the swap's: BOTH atoms dodge        *)
(*  [ftvar_in_aenv Θ] (not merely [dom Θ] — a flexible's payload may       *)
(*  mention them) and both dodge the generated block [Ξ], which stays      *)
(*  FIXED.  [β0 ∉ dom Ξ] is free from [β0 ∉ ftv P'] via                    *)
(*  [a_solve_*_generated_occurs] below; [α0 ∉ dom Ξ] is genuinely needed —  *)
(*  renaming a generated name in [P'] while keeping [Ξ] would desynchronize *)
(*  the two.                                                              *)
(* ===================================================================== *)

Lemma subst_pskl_var_same : forall P α,
  subst_pskl_in_pskl (pskl_var_f α) α P = P.
Proof.
  induction P; intros α0; simpl; f_equal; auto.
  destruct (α == α0); subst; reflexivity.
Qed.

(** [guess^TY] consults its context ONLY through the avoid-conditions
    [∉ ftvar_in_aenv Θ], so it transports to any context that MENTIONS LESS.
    Needed by the solve's context-change lemma now that SE-FlexR calls it. *)
Lemma a_guess_mono_ctx_shrink : forall Θ P Ξ A Θ',
  a_guess_mono Θ P Ξ A ->
  ftvar_in_aenv Θ' [<=] ftvar_in_aenv Θ ->
  a_guess_mono Θ' P Ξ A.
Proof.
  intros Θ P Ξ A Θ' H; revert Θ'; induction H; intros Θ' Hsub.
  - apply a_guess_mono__hole. clear - H Hsub; fsetdec.
  - apply a_guess_mono__tophole; auto.
  - apply a_guess_mono__var.
  - apply a_guess_mono__unit.
  - apply a_guess_mono__arrow; auto.
  - apply a_guess_mono__forall with (β := β);
      [ clear - H Hsub; fsetdec
      | apply IHa_guess_mono; simpl; clear - Hsub; fsetdec ].
Qed.

(** ⭐ THE WITNESS-MOVE, PACKAGED.  A solve premise recorded at the rule's
    OWN binder [b] is transported to any [α0] fresh for the two input
    skeletons and the output.

    ⚠️ This is the operation the freshness-campaign proofs used to perform
    with a double RENAME, and which the repair broke: [b] now sits IN the
    premise's context, so "the source dodges the context" cannot hold.  A
    SWAP has no such condition — it carries the context along — and that is
    harmless here because every consumer quantifies the context universally
    and never mentions it in its conclusion.  The moved premise therefore
    runs at [(α0 ~ tvar) ++ swap_aenv b α0 Θ], and nobody has to care. *)
Lemma a_solve_eq_move_binder : forall Θ b P Q Ξ P' α0,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f b))
    ∼ (open_pskl_wrt_pskl Q (pskl_var_f b)) ⤳ Ξ ⨾ P' }}a ->
  b `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q ->
  α0 `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q
      `union` ftvar_in_pskl P' ->
  {{ ((α0 ~ abind_tvar) ++ swap_aenv b α0 Θ)
    ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f α0))
     ∼ (open_pskl_wrt_pskl Q (pskl_var_f α0))
     ⤳ (swap_aenv b α0 Ξ) ⨾ (subst_pskl_in_pskl (pskl_var_f α0) b P') }}a.
Proof.
  intros Θ b P Q Ξ P' α0 Hp Hb Hα0.
  pose proof ((proj2 (a_solve_sub_eq_swap b α0)) _ _ _ _ _ Hp) as Hr.
  rewrite swap_aenv_app, swap_aenv_one_tvar in Hr.
  rewrite ! swap_pskl_open_var, swap_atom_l in Hr.
  rewrite (swap_pskl_fresh_id b α0 P) in Hr
    by (clear - Hb Hα0; fsetdec).
  rewrite (swap_pskl_fresh_id b α0 Q) in Hr
    by (clear - Hb Hα0; fsetdec).
  rewrite (swap_pskl_as_subst b α0 P') in Hr
    by (clear - Hα0; fsetdec).
  exact Hr.
Qed.

(** The same for a subject that is NOT opened (the ∀◇ rows: [∀◇P] passes
    through the premise unchanged). *)
(** The SUB-side witness-moves: SS-ForallL opens the SUBJECT (the target
    rides along b-free), SS-ForallR opens the TARGET. *)
Lemma a_solve_sub_move_binder_l : forall Θ b m P Q Ξ P' α0,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ₛ (open_pskl_wrt_pskl P (pskl_var_f b))
    ≼[ m ] Q ⤳ Ξ ⨾ P' }}a ->
  b `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q ->
  α0 `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q
      `union` ftvar_in_pskl P' ->
  {{ ((α0 ~ abind_tvar) ++ swap_aenv b α0 Θ)
    ⊢ₛ (open_pskl_wrt_pskl P (pskl_var_f α0)) ≼[ m ] Q
     ⤳ (swap_aenv b α0 Ξ) ⨾ (subst_pskl_in_pskl (pskl_var_f α0) b P') }}a.
Proof.
  intros Θ b m P Q Ξ P' α0 Hp Hb Hα0.
  pose proof ((proj1 (a_solve_sub_eq_swap b α0)) _ _ _ _ _ _ Hp) as Hr.
  rewrite swap_aenv_app, swap_aenv_one_tvar in Hr.
  rewrite swap_pskl_open_var, swap_atom_l in Hr.
  rewrite (swap_pskl_fresh_id b α0 P) in Hr by (clear - Hb Hα0; fsetdec).
  rewrite (swap_pskl_fresh_id b α0 Q) in Hr by (clear - Hb Hα0; fsetdec).
  rewrite (swap_pskl_as_subst b α0 P') in Hr by (clear - Hα0; fsetdec).
  exact Hr.
Qed.

Lemma a_solve_sub_move_binder_r : forall Θ b A B Ξ P' α0,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ₛ A ≼[ mode_tc ]
    (open_pskl_wrt_pskl B (pskl_var_f b)) ⤳ Ξ ⨾ P' }}a ->
  b `notin` ftvar_in_pskl A `union` ftvar_in_pskl B ->
  α0 `notin` ftvar_in_pskl A `union` ftvar_in_pskl B
      `union` ftvar_in_pskl P' ->
  {{ ((α0 ~ abind_tvar) ++ swap_aenv b α0 Θ)
    ⊢ₛ A ≼[ mode_tc ] (open_pskl_wrt_pskl B (pskl_var_f α0))
     ⤳ (swap_aenv b α0 Ξ) ⨾ (subst_pskl_in_pskl (pskl_var_f α0) b P') }}a.
Proof.
  intros Θ b A B Ξ P' α0 Hp Hb Hα0.
  pose proof ((proj1 (a_solve_sub_eq_swap b α0)) _ _ _ _ _ _ Hp) as Hr.
  rewrite swap_aenv_app, swap_aenv_one_tvar in Hr.
  rewrite swap_pskl_open_var, swap_atom_l in Hr.
  rewrite (swap_pskl_fresh_id b α0 A) in Hr by (clear - Hb Hα0; fsetdec).
  rewrite (swap_pskl_fresh_id b α0 B) in Hr by (clear - Hb Hα0; fsetdec).
  rewrite (swap_pskl_as_subst b α0 P') in Hr by (clear - Hα0; fsetdec).
  exact Hr.
Qed.

Lemma a_solve_eq_move_binder_tophole_l : forall Θ b P Q Ξ P' α0,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ₑ (pskl_tophole P)
    ∼ (open_pskl_wrt_pskl Q (pskl_var_f b)) ⤳ Ξ ⨾ P' }}a ->
  b `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q ->
  α0 `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q
      `union` ftvar_in_pskl P' ->
  {{ ((α0 ~ abind_tvar) ++ swap_aenv b α0 Θ)
    ⊢ₑ (pskl_tophole P) ∼ (open_pskl_wrt_pskl Q (pskl_var_f α0))
     ⤳ (swap_aenv b α0 Ξ) ⨾ (subst_pskl_in_pskl (pskl_var_f α0) b P') }}a.
Proof.
  intros Θ b P Q Ξ P' α0 Hp Hb Hα0.
  pose proof ((proj2 (a_solve_sub_eq_swap b α0)) _ _ _ _ _ Hp) as Hr.
  rewrite swap_aenv_app, swap_aenv_one_tvar in Hr.
  cbn [swap_pskl] in Hr.
  rewrite swap_pskl_open_var, swap_atom_l in Hr.
  rewrite (swap_pskl_fresh_id b α0 P) in Hr
    by (clear - Hb Hα0; fsetdec).
  rewrite (swap_pskl_fresh_id b α0 Q) in Hr
    by (clear - Hb Hα0; fsetdec).
  rewrite (swap_pskl_as_subst b α0 P') in Hr
    by (clear - Hα0; fsetdec).
  exact Hr.
Qed.

Lemma a_solve_eq_move_binder_tophole_r : forall Θ b P Q Ξ P' α0,
  {{ ((b ~ abind_tvar) ++ Θ) ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f b))
    ∼ (pskl_tophole Q) ⤳ Ξ ⨾ P' }}a ->
  b `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q ->
  α0 `notin` ftvar_in_pskl P `union` ftvar_in_pskl Q
      `union` ftvar_in_pskl P' ->
  {{ ((α0 ~ abind_tvar) ++ swap_aenv b α0 Θ)
    ⊢ₑ (open_pskl_wrt_pskl P (pskl_var_f α0)) ∼ (pskl_tophole Q)
     ⤳ (swap_aenv b α0 Ξ) ⨾ (subst_pskl_in_pskl (pskl_var_f α0) b P') }}a.
Proof.
  intros Θ b P Q Ξ P' α0 Hp Hb Hα0.
  pose proof ((proj2 (a_solve_sub_eq_swap b α0)) _ _ _ _ _ Hp) as Hr.
  rewrite swap_aenv_app, swap_aenv_one_tvar in Hr.
  cbn [swap_pskl] in Hr.
  rewrite swap_pskl_open_var, swap_atom_l in Hr.
  rewrite (swap_pskl_fresh_id b α0 P) in Hr
    by (clear - Hb Hα0; fsetdec).
  rewrite (swap_pskl_fresh_id b α0 Q) in Hr
    by (clear - Hb Hα0; fsetdec).
  rewrite (swap_pskl_as_subst b α0 P') in Hr
    by (clear - Hα0; fsetdec).
  exact Hr.
Qed.

(* ===================================================================== *)
(*  ⭐ THE Ξ KIT AT THE CONSTRAINT-LIST LEVEL (2026-08-04).                *)
(*  [a_solve_cstr] folds the eq-solve over a list and CONCATENATES the     *)
(*  blocks, so both invariants of §4(c) lift by a two-line induction.      *)
(*  P6-Cs needs them to rebuild [{{ ⊢ (Ξs ++ Ξc ++ Θ0) }}a] and to feed   *)
(*  [a_inc_flex_prefix_build] a second time.                              *)
(* ===================================================================== *)

(** (K1) at the list level: the block is undefined flexibles only. *)
Lemma a_solve_cstr_decls : forall Θ 𝒞 P Ξ P',
  {{ Θ ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ P' }}a -> a_decls Ξ.
Proof.
  intros Θ 𝒞 P Ξ P' H; induction H.
  - constructor.
  - eapply a_solve_sub_decls; eassumption.
  - apply a_decls_app; [ exact IHa_solve_cstr | ].
    eapply a_solve_eq_decls; eassumption.
Qed.

(** (K2) at the list level.  The tail runs at [Ξ1 ++ Θ], whose [ftvar_in_aenv]
    CONTAINS [Θ]'s, so the tail's block dodges [Θ] a fortiori — that is the
    whole content, and it is why the rules thread rather than run both halves
    at [Θ]. *)
Lemma a_solve_cstr_generated_fresh : forall Θ 𝒞 P Ξ P',
  {{ Θ ⊩ 𝒞 ⨾ P ⤳ Ξ ⨾ P' }}a ->
  forall α, α `in` dom Ξ -> α `notin` ftvar_in_aenv Θ.
Proof.
  intros Θ 𝒞 P Ξ P' H; induction H; intros α Hin.
  - simpl in Hin; exfalso; clear - Hin; fsetdec.
  - eapply a_solve_sub_generated_fresh; eassumption.
  - rewrite dom_app in Hin.
    destruct (AtomSetProperties.In_dec α (dom Ξ2)) as [Hin2 | Hnin2].
    + pose proof (IHa_solve_cstr α Hin2) as Hfr.
      rewrite ftvar_in_aenv_app in Hfr. clear - Hfr; fsetdec.
    + assert (Hin1 : α `in` dom Ξ1) by (clear - Hin Hnin2; fsetdec).
      eapply a_solve_eq_generated_fresh; eassumption.
Qed.

(** ⭐⭐ A GHOST TARGET SOLVES TO THE IDENTITY — block empty, accumulator
    untouched, whatever the subject.

    ⚙ NOTE THAT NO DISPATCH GUARD IS OWED HERE, unlike the COLLECTION.  The
    runner does answer a ghost target by SS-Vacuous first
    (ext_algo/def_solve_impl.v:341), so SS-ForallL and SS-UnivGhostL DO
    overlap it — but they AGREE with it: SS-ForallL re-CLOSES its opener
    ([close β (open P β) = P]) and SS-UnivGhostL rebuilds its [⫯], so every
    surviving row returns the accumulator.  The collection has no such
    property, which is exactly why the guard is needed there and not here.

    ⚙ MOVED here 2026-08-18 from ext_algo/prop_look_equiv.v: P6's ForallL row
    (sub/look/prop_sub_cstr.v) consumes it, and that file is UPSTREAM of
    ext_algo — one fact, one name, one file, in the layer its consumers see. *)
Lemma a_solve_sub_hole_target_inv : forall Θ m P Ξ P',
  {{ Θ ⊢ₛ P ≼[ m ] pskl_hole ⤳ Ξ ⨾ P' }}a ->
  Ξ = nil /\ P' = P.
Proof.
  intros Θ m P Ξ P' Hd.
  remember pskl_hole as T eqn:HT.
  induction Hd; inversion HT; subst.
  - (* SS-Var *) auto.
  - (* SS-ForallL: the yield re-closes to the subject *)
    destruct IHHd as [-> ->]; [ reflexivity | ].
    split; [ reflexivity | ].
    rewrite close_pskl_wrt_pskl_open_pskl_wrt_pskl;
      [ reflexivity
      | match goal with
        | Hfr : ?b `notin` ftvar_in_aenv _ `union` _ `union` _ |- _ =>
            clear - Hfr; fsetdec
        end ].
  - (* SS-UnivGhostL *)
    destruct IHHd as [-> ->]; [ reflexivity | ]. auto.
  - (* SS-Vacuous *) auto.
  - (* SS-Check: guarded ◇ has no constructor *)
    match goal with
    | Hg : guarded_pskl pskl_hole |- _ => inversion Hg
    end.
  - (* SS-GhostL at B = ◇: ghost-free ◇ has no constructor *)
    match goal with
    | Hg : pskl_ghost_free pskl_hole |- _ => inversion Hg
    end.
Qed.

