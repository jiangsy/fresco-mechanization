(** BASICS for the constraint-collection layer
    ([a_looksub]/[a_lookeq]/[a_extract]) — docs/DESIGN-subtyping.md P2.

    The declaration-shape facts every re-attachment of a look output [Ξ] to
    a context needs: look only ever generates FLEXIBLE declarations (the
    single generative rule is LE-FlexR), and [a_extract] appends [guess]'s
    declarations ([a_guess_mono_decls]). *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.coercions.
Require Import src.frost.predicates.
Require Import src.frost.ltac_utils.
Require Import src.frost.prop_ln.
Require Import src.frost.prop_basic.
Require Import src.frost.decl.def_extra.
Require Import src.frost.decl.prop_basic.
Require Import src.frost.algo.def_extra.
Require Import src.frost.algo.def_meta.
Require Import src.frost.algo.prop_inc.
Require Import src.frost.algo.prop_flex.
Require Import src.frost.algo.prop_solve_sub.
Require Import src.frost.algo.prop_consis_sound.

Set Implicit Arguments.

Scheme a_looksub_mutind := Induction for a_looksub Sort Prop
  with a_lookeq_mutind := Induction for a_lookeq Sort Prop.

Combined Scheme a_looksub_lookeq_mutind
  from a_looksub_mutind, a_lookeq_mutind.

(* ===================================================================== *)
(*  §1  Look outputs are declaration-only contexts                        *)
(* ===================================================================== *)

Lemma a_looksub_lookeq_decls :
  (forall Θ α m P P' Ξ 𝒞, Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 -> a_decls Ξ) /\
  (forall Θ α P P' Ξ 𝒞, Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 -> a_decls Ξ).
Proof.
  apply (a_looksub_lookeq_mutind
           (fun Θ α m P P' Ξ 𝒞 _ => a_decls Ξ)
           (fun Θ α P P' Ξ 𝒞 _ => a_decls Ξ));
    intros; try solve [ assumption ]; try solve [ apply a_decls__nil ];
    try solve [ apply a_decls_app; assumption ];
    try solve [ destruct (atom_fresh L) as [β0 Hβ0]; eauto ].
  (* LE-FlexR : the single generative rule *)
  econstructor; apply a_decls__nil.
Qed.

Lemma a_looksub_decls : forall Θ α m P P' Ξ 𝒞,
  Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 -> a_decls Ξ.
Proof. intros; eapply (proj1 a_looksub_lookeq_decls); eauto. Qed.

Lemma a_lookeq_decls : forall Θ α P P' Ξ 𝒞,
  Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 -> a_decls Ξ.
Proof. intros; eapply (proj2 a_looksub_lookeq_decls); eauto. Qed.

(** [guess] generates only declarations ([SK]: none; [TY]: the fresh mono
    flexibles of [a_guess_mono]). *)
Lemma a_guess_decls : forall Θ NM P Ξ P',
  a_guess Θ NM P Ξ P' -> a_decls Ξ.
Proof.
  intros Θ NM P Ξ P' H; destruct H;
    [ apply a_decls__nil | eapply a_guess_mono_decls; eauto ].
Qed.

(** The collected block holds only bare flexibles (LE-FlexR is the single
    generative rule), so it mentions exactly its own domain — the look
    counterpart of [a_guess_mono_generated_ftvar].  This is what lets the
    consumers of the TARGET-only rename below phrase their premise as the
    [dom Ξ] freshness they already have. *)
Lemma a_looksub_lookeq_generated_ftvar :
  (forall Θ α m P P' Ξ 𝒞, Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 -> ftvar_in_aenv Ξ [<=] dom Ξ) /\
  (forall Θ α P P' Ξ 𝒞, Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 -> ftvar_in_aenv Ξ [<=] dom Ξ).
Proof.
  apply (a_looksub_lookeq_mutind
           (fun Θ α m P P' Ξ 𝒞 _ => ftvar_in_aenv Ξ [<=] dom Ξ)
           (fun Θ α P P' Ξ 𝒞 _ => ftvar_in_aenv Ξ [<=] dom Ξ));
    intros; simpl; try solve [ fsetdec ];
    try solve [ destruct (atom_fresh L) as [β0 Hβ0]; eauto ];
    rewrite ftvar_in_aenv_app, dom_app; fsetdec.
Qed.

Lemma a_looksub_generated_ftvar : forall Θ α m P P' Ξ 𝒞,
  Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof. intros; eapply (proj1 a_looksub_lookeq_generated_ftvar); eauto. Qed.

Lemma a_lookeq_generated_ftvar : forall Θ α P P' Ξ 𝒞,
  Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 -> ftvar_in_aenv Ξ [<=] dom Ξ.
Proof. intros; eapply (proj2 a_looksub_lookeq_generated_ftvar); eauto. Qed.

Lemma a_extract_decls : forall Θ0 NM α m P P' Ξ P0,
  Θ0 ⊢ P ⊳[ NM , α , m ] P' ⤳ Ξ ↪ P0 -> a_decls Ξ.
Proof.
  intros Θ0 NM α m P P' Ξ P0 H; destruct H.
  apply a_decls_app;
    [ eapply a_looksub_decls; eauto | eapply a_guess_decls; eauto ].
Qed.

(* ===================================================================== *)
(*  §2  Free variables of the collected constraints                       *)
(*                                                                        *)
(*  Every variable in a collected constraint comes from the RHS being     *)
(*  compared against, or is one of the freshly-generated flexibles in Ξ   *)
(*  (LE-FlexR).  Needed for freshness bookkeeping when re-attaching Ξ.     *)
(* ===================================================================== *)

Definition ftvar_in_cstr (c : a_cstr) : atoms :=
  match c with
  | a_cstr_sub _ P => ftvar_in_pskl P
  | a_cstr_eq P     => ftvar_in_pskl P
  end.

Fixpoint ftvar_in_cstrs (C : a_cstrs) : atoms :=
  match C with
  | nil     => empty
  | c :: C' => ftvar_in_cstr c `union` ftvar_in_cstrs C'
  end.

Lemma ftvar_in_cstrs_app : forall C1 C2,
  ftvar_in_cstrs (C1 ++ C2) [=] ftvar_in_cstrs C1 `union` ftvar_in_cstrs C2.
Proof. induction C1; intros; simpl; [ fsetdec | rewrite IHC1; fsetdec ]. Qed.

(** Renaming a variable throughout a collected constraint list.  Needed by
    the TARGET-only rename below: the collected [𝒞] is an OUTPUT, so a
    canonical renaming lemma must rename it rather than demand the source
    be absent from it (DESIGN.md §4.3, canon rule 3). *)
Definition subst_cstr (γ β : atom) (c : a_cstr) : a_cstr :=
  match c with
  | a_cstr_sub m P => a_cstr_sub m (subst_pskl_in_pskl (pskl_var_f γ) β P)
  | a_cstr_eq P    => a_cstr_eq (subst_pskl_in_pskl (pskl_var_f γ) β P)
  end.

Fixpoint subst_cstrs (γ β : atom) (C : a_cstrs) : a_cstrs :=
  match C with
  | nil     => nil
  | c :: C' => subst_cstr γ β c :: subst_cstrs γ β C'
  end.

Lemma subst_cstrs_app : forall γ β C1 C2,
  subst_cstrs γ β (C1 ++ C2) = subst_cstrs γ β C1 ++ subst_cstrs γ β C2.
Proof. induction C1; intros; simpl; [ reflexivity | rewrite IHC1; reflexivity ]. Qed.

Lemma subst_cstrs_fresh_eq : forall γ β C,
  β `notin` ftvar_in_cstrs C -> subst_cstrs γ β C = C.
Proof.
  induction C as [ | c C' IH ]; intros Hβ; simpl in *; [ reflexivity | ].
  rewrite IH by (clear - Hβ; fsetdec).
  destruct c; simpl; rewrite subst_pskl_in_pskl_fresh_eq
    by (clear - Hβ; simpl in Hβ; fsetdec); reflexivity.
Qed.

Lemma ftvar_in_cstrs_subst_upper : forall γ β C,
  ftvar_in_cstrs (subst_cstrs γ β C)
    [<=] singleton γ `union` remove β (ftvar_in_cstrs C).
Proof.
  induction C as [ | c C' IH ]; simpl; [ fsetdec | ].
  destruct c; simpl;
    match goal with |- context[ftvar_in_pskl (subst_pskl_in_pskl _ _ ?P)] =>
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P (pskl_var_f γ) β) as Hup
    end; simpl in Hup; clear - IH Hup; fsetdec.
Qed.

(* DISJUNCTIVE since the freshness campaign's cluster 3, and necessarily so:
   the five ∀ rules LEAK their binder, so a collected constraint really can
   name a variable the conclusion's target no longer shows —

     Θ ⊢ ∀b. α  ∼[α]  ∀b. b  ⤳ ·  ⨾  [ b0 ≐ ]        (LE-ForallInh, LE-Var)

   has [ftvar_in_cstrs 𝒞 = {b0}] while [ftv (∀b.b) ∪ dom · = ∅].  The exact
   bound is therefore FALSE and the repair is the same one cluster 2 made
   for [a_solve_sub_eq_ftv] / [a_solve_cstr_ftv]: an escaping variable is
   one the RUN INVENTED, and the avoid-input [Θ] is what lets us say so.
   (This lemma is exactly why look needed a context: without [Θ] the second
   disjunct cannot even be STATED, and [a_extract_output_fresh] below — the
   paper's lemma:look-output-fresh, subtyping-proofs:522 — loses its proof.) *)
Lemma a_looksub_lookeq_ftv :
  (forall Θ α m P P' Ξ 𝒞, Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall α0, α0 `in` ftvar_in_cstrs 𝒞 ->
       α0 `in` (ftvar_in_pskl P' `union` dom Ξ) \/
       α0 `notin` ftvar_in_aenv Θ) /\
  (forall Θ α P P' Ξ 𝒞, Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall α0, α0 `in` ftvar_in_cstrs 𝒞 ->
       α0 `in` (ftvar_in_pskl P' `union` dom Ξ) \/
       α0 `notin` ftvar_in_aenv Θ).
Proof.
  apply (a_looksub_lookeq_mutind
           (fun Θ α m P P' Ξ 𝒞 _ =>
              forall α0, α0 `in` ftvar_in_cstrs 𝒞 ->
                α0 `in` (ftvar_in_pskl P' `union` dom Ξ) \/
                α0 `notin` ftvar_in_aenv Θ)
           (fun Θ α P P' Ξ 𝒞 _ =>
              forall α0, α0 `in` ftvar_in_cstrs 𝒞 ->
                α0 `in` (ftvar_in_pskl P' `union` dom Ξ) \/
                α0 `notin` ftvar_in_aenv Θ));
    intros; simpl in *;
    (* the non-binder rows: constraints come from the target or from Ξ *)
    try solve [ left; match goal with Hin : _ `in` _ |- _ =>
                  clear - Hin; fsetdec end ].
  (* Twelve rows survive: five that repeat their premise verbatim, the two
     arrows, and the five BINDER rows — three of which open the TARGET, and
     those are exactly where a leaked binder can show up in 𝒞. *)
  all: try solve [ exact (H α0 H0) ].
  all: try solve [ (* the arrows: split the constraint list *)
         rewrite ftvar_in_cstrs_app in H1; rewrite dom_app;
         destruct (AtomSetProperties.In_dec α0 (ftvar_in_cstrs C1))
           as [Hin | Hin];
         [ destruct (H α0 Hin) as [Hd | Hd]
         | destruct (H0 α0 ltac:(clear - H1 Hin; fsetdec)) as [Hd | Hd] ];
         solve [ left; clear - Hd; fsetdec | right; exact Hd ] ].
  (* The five BINDER rows.  [n] is the rule's own side condition, and the
     right disjunct is inherited because the premise's context only GREW. *)
  all: destruct (H α0 H0) as [Hl | Hr].
  all: try solve [ right; clear - Hr; fsetdec ].
  all: try solve [ left; exact Hl ].   (* LS-ForallL / LE-ForallSyn: target untouched *)
  (* what remains: the three rows that OPEN THE TARGET, where the escapee may
     BE the binder — and there the rule's own freshness is the witness *)
  all: match goal with
       | Hl : _ `in` union (ftvar_in_pskl (open_pskl_wrt_pskl ?B _)) _ |- _ =>
           pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper B (pskl_var_f β))
             as Hup
       end; simpl in Hup;
       destruct (α0 == β) as [-> | Hne];
         [ right; clear - n; fsetdec | left; clear - Hl Hup Hne; fsetdec ].
Qed.

Lemma a_looksub_ftv : forall Θ α m P P' Ξ 𝒞,
  Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
  forall α0, α0 `in` ftvar_in_cstrs 𝒞 ->
    α0 `in` (ftvar_in_pskl P' `union` dom Ξ) \/ α0 `notin` ftvar_in_aenv Θ.
Proof. intros * H; eapply (proj1 a_looksub_lookeq_ftv); eauto. Qed.

(* ===================================================================== *)
(*  §3  Look freshness (lemma:look-output-fresh, subtyping-proofs:522)    *)
(*                                                                        *)
(*  The extract output's free variables come from the input skeleton      *)
(*  [P0] and the collected/guessed flexibles [Ξ] only — in particular     *)
(*  the looked-for variable α (or any variable fresh for [P0] and [Ξ])    *)
(*  does not survive into the instantiation candidate.                    *)
(* ===================================================================== *)

(* DISJUNCTIVE since the freshness campaign: [SS-ForallR] deliberately
   leaks its binder into the result (see the constructor comment), so an
   output variable is an input variable OR fresh for the solve context.
   The EXACT bound survives for eq-only constraint lists
   ([a_solve_cstr_ftv_eq]) — consistency's collections are all-eq, so the
   P6-Cs paths keep the strong form. *)
Lemma a_solve_cstr_ftv : forall Θ 𝒞 P P',
  Θ ⊩ 𝒞 ⨾ P ⤳ P' ->
  forall α, α `in` ftvar_in_pskl P' ->
    α `in` (ftvar_in_pskl P `union` ftvar_in_cstrs 𝒞) \/ α `notin` dom Θ.
Proof.
  intros Θ 𝒞 P P' H; induction H; simpl; intros α0 Hα0.
  - left; fsetdec.
  - destruct (a_solve_sub_ftv H Hα0) as [Hl | Hr];
      [ left; clear - Hl; fsetdec | right; exact Hr ].
  - pose proof ((proj2 a_solve_sub_eq_ftv) _ _ _ _ H) as He.
    destruct (IHa_solve_cstr α0 Hα0) as [Hl | Hr];
      [ left; clear - Hl He; fsetdec | right; exact Hr ].
Qed.

Lemma a_solve_cstr_ftv_eq : forall Θ 𝒞 P P',
  Θ ⊩ 𝒞 ⨾ P ⤳ P' ->
  Forall (fun c => exists Q, c = a_cstr_eq Q) 𝒞 ->
  ftvar_in_pskl P' [<=] ftvar_in_pskl P `union` ftvar_in_cstrs 𝒞.
Proof.
  intros Θ 𝒞 P P' H; induction H; simpl; intros Hall.
  - fsetdec.
  - (* a sub constraint contradicts the all-eq hypothesis *)
    exfalso. inversion Hall as [ | c cs Hc _ ]; subst.
    destruct Hc as [Q0 Hc]. discriminate Hc.
  - inversion Hall as [ | c cs Hc Htl ]; subst.
    pose proof ((proj2 a_solve_sub_eq_ftv) _ _ _ _ H) as He.
    specialize (IHa_solve_cstr Htl).
    clear - He IHa_solve_cstr. fsetdec.
Qed.

Lemma ptyp_to_pskl_ftv : forall A,
  ftvar_in_pskl (ptyp_to_pskl A) [<=] ftvar_in_ptyp A.
Proof. induction A; simpl; fsetdec. Qed.

(* The paper's lemma pins its variable only against [P0] and [Ξ]
   (subtyping-proofs:522); the mech additionally pins it inside [dom Θ0] —
   the Barendregt rendering that separates it from the LEAKED binders of
   [SS-ForallR] and of look's five ∀ rules, which avoid the whole ambient
   context by their side conditions.  Every name the consumers care about
   (the looked-for variable, context binders) lives in [dom Θ0].
   Since cluster 3 this discharges TWO "…or the run invented it" arms —
   the solve's ([a_solve_cstr_ftv]) and the look's ([a_looksub_ftv]) — and
   both die the same way: [α1 ∈ dom Θ0 ⊆ ftvar_in_aenv Θ0]. *)
Lemma a_extract_output_fresh : forall Θ0 NM α M P P0 Ξ P1 α1,
  Θ0 ⊢ P ⊳[ NM , α , M ] P0 ⤳ Ξ ↪ P1 ->
  α1 `in` dom Θ0 ->
  α1 `notin` ftvar_in_pskl P0 ->
  α1 `notin` dom Ξ ->
  α1 `notin` ftvar_in_pskl P1.
Proof.
  intros * Hex Hdom Hγ0 Hα1Ξ. inversion Hex; subst.
  simpl_env in Hα1Ξ.
  match goal with
  | Hlk : _ ⊢ _ ≼[ _ , _ ] _ ⤳ _ ⨾ _ , Hsc : _ ⊩ _ ⨾ _ ⤳ _ |- _ =>
      pose proof (a_looksub_ftv Hlk) as Hb1;
      pose proof (a_solve_cstr_ftv Hsc) as Hb2
  end.
  pose proof (dom_subset_ftvar_in_aenv Θ0) as Hdf.
  (* the shared refutation: a variable of the SOLVE's output is either an
     input variable (⇒ in 𝒞, and then the LOOK's bound applies) or a name
     one of the two runs invented (⇒ outside the ambient context) *)
  match goal with
  | Hsc : _ ⊩ ?Cx ⨾ _ ⤳ ?Qx |- _ =>
      assert (Hcore : α1 `notin` ftvar_in_pskl Qx);
      [ intro Hin; destruct (Hb2 α1 Hin) as [Hl | Hr];
        [ | apply Hr; rewrite dom_app; clear - Hdom; fsetdec ];
        assert (Hc : α1 `in` ftvar_in_cstrs Cx)
          by (clear - Hl; simpl in Hl; fsetdec);
        destruct (Hb1 α1 Hc) as [Hl2 | Hr2];
        [ clear - Hl2 Hγ0 Hα1Ξ; fsetdec | clear - Hr2 Hdom Hdf; fsetdec ]
      | ]
  end.
  match goal with
  | Hg : a_guess _ _ _ _ _ |- _ => inversion Hg; subst
  end.
  - (* SK : output = solve output *) exact Hcore.
  - (* TY : output = guessed monotype *)
    match goal with
    | Hgm : a_guess_mono _ _ _ _ |- _ =>
        pose proof (a_guess_mono_ftv Hgm) as Hb3
    end.
    intro Hin.
    match goal with
    | Hgm : a_guess_mono _ ?q _ _ |- False =>
        assert (HinQ : α1 `in` ftvar_in_pskl q)
          by (pose proof (ptyp_to_pskl_ftv A) as Hb4';
              clear - Hb3 Hb4' Hin Hα1Ξ; fsetdec)
    end.
    exact (Hcore HinQ).
Qed.

(* ===================================================================== *)
(*  §4  Stability of constraint collection under substitution             *)
(*  (lemma:constraint-collection-stable-substitution, tex:504-520,        *)
(*  forward direction).  Substituting an α-free [Q] for β ≠ α preserves   *)
(*  the collected constraints; when the substitution destroys a           *)
(*  guardedness side condition the source has become α-free, so the       *)
(*  derivation switches to the Absent rule (the paper's remark).          *)
(* ===================================================================== *)

(** An α-free source collects nothing. *)
Lemma a_looksub_lookeq_absent_nil :
  (forall Θ α m P P' Ξ 𝒞, Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
     α `notin` ftvar_in_pskl P -> Ξ = nil /\ 𝒞 = nil) /\
  (forall Θ α P P' Ξ 𝒞, Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
     α `notin` ftvar_in_pskl P -> Ξ = nil /\ 𝒞 = nil).
Proof.
  apply (a_looksub_lookeq_mutind
           (fun Θ α m P P' Ξ 𝒞 _ =>
              α `notin` ftvar_in_pskl P -> Ξ = nil /\ 𝒞 = nil)
           (fun Θ α P P' Ξ 𝒞 _ =>
              α `notin` ftvar_in_pskl P -> Ξ = nil /\ 𝒞 = nil));
    intros; simpl in *;
    try solve [ auto ];
    try solve [ exfalso; fsetdec ];
    try match goal with
        | IH1 : _ -> ?Ξ1 = nil /\ ?C1 = nil,
          IH2 : _ -> ?Ξ2 = nil /\ ?C2 = nil
          |- ?Ξ1 ++ ?Ξ2 = nil /\ ?C1 ++ ?C2 = nil =>
            destruct IH1 as [-> ->]; [ fsetdec | ];
            destruct IH2 as [-> ->]; [ fsetdec | ];
            auto
        end;
    (* The BINDER rows.  A source-opening rule re-derives the α-freshness of
       the opened body from its OWN side condition (which pins β ≠ α); a
       target-opening rule leaves the source alone. *)
    try match goal with
        | IH : _ `notin` ftvar_in_pskl (open_pskl_wrt_pskl ?Pb _) -> _ ,
          Hn : _ `notin` ftvar_in_pskl _ ,
          Hsc : _ `notin` add _ _ |- _ =>
            apply IH;
            pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper
                          Pb (pskl_var_f β)) as Hup;
            simpl in Hup; clear - Hup Hn Hsc; fsetdec
        end;
    try match goal with
        | IH : _ -> _ = nil /\ _ = nil |- _ => apply IH; assumption
        end.
Qed.

Lemma guarded_pskl_subst : forall P P' β,
  guarded_pskl P ->
  lc_pskl P' ->
  P <> pskl_var_f β ->
  guarded_pskl (subst_pskl_in_pskl P' β P).
Proof.
  intros P P' β Hg Hlc Hne; inversion Hg; subst; simpl.
  - constructor.
  - destruct_if; [ exfalso; congruence | constructor ].
  - constructor; apply subst_pskl_in_pskl_lc_pskl; auto.
Qed.

(** The SCOPE premise [ftv P0 ⊆ α ∪ ftvar_in_aenv Θ] is the paper's Barendregt
    convention spelled out, and it is LOAD-BEARING since cluster 3: with a
    LEAKING exists-fresh binder the unconditional form is FALSE
    (cex/cex_look_subst_stable_leak.v, Qed) — a [P0] carrying the
    derivation's own binder cannot be re-derived, because every binder the
    rule may pick avoids [ftv (subst P0 β P)].  The premise is exactly what
    the ∀ rules' own side condition bites on ("the substituted skeleton
    introduces no name the judgment does not already mention"), so
    [β0 ∉ ftv P0] is DERIVED.  It names the CONTEXT (not the input
    skeletons) because only the context is MONOTONE under descent: an arrow
    row shrinks the skeletons, a binder row grows the context, and
    [ftvar_in_aenv Θ] therefore threads through both. *)

Lemma a_looksub_lookeq_subst_stable :
  (forall Θ α m P P' Ξ 𝒞, Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall β P0, β <> α -> α `notin` ftvar_in_pskl P0 -> lc_pskl P0 ->
     ftvar_in_pskl P0 [<=] add α (ftvar_in_aenv Θ) ->
     Θ ⊢ (subst_pskl_in_pskl P0 β P) ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞) /\
  (forall Θ α P P' Ξ 𝒞, Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall β P0, β <> α -> α `notin` ftvar_in_pskl P0 -> lc_pskl P0 ->
     ftvar_in_pskl P0 [<=] add α (ftvar_in_aenv Θ) ->
     Θ ⊢ (subst_pskl_in_pskl P0 β P) ∼[ α ] P' ⤳ Ξ ⨾ 𝒞).
Proof.
  apply (a_looksub_lookeq_mutind
           (fun Θ α m P P' Ξ 𝒞 _ =>
              forall β P0, β <> α -> α `notin` ftvar_in_pskl P0 -> lc_pskl P0 ->
              ftvar_in_pskl P0 [<=] add α (ftvar_in_aenv Θ) ->
              Θ ⊢ (subst_pskl_in_pskl P0 β P) ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞)
           (fun Θ α P P' Ξ 𝒞 _ =>
              forall β P0, β <> α -> α `notin` ftvar_in_pskl P0 -> lc_pskl P0 ->
              ftvar_in_pskl P0 [<=] add α (ftvar_in_aenv Θ) ->
              Θ ⊢ (subst_pskl_in_pskl P0 β P) ∼[ α ] P' ⤳ Ξ ⨾ 𝒞));
    intros; simpl.
  - (* LS-Var *)
    destruct_if; [ exfalso; congruence | apply a_looksub__var ].
  - (* LS-Absent *)
    apply a_looksub__absent.
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P P0 β).
    fsetdec.
  - (* LS-Vacuous *)
    apply a_looksub__vacuous.
  - (* LS-Check : switch to Absent when the source was the substituted var *)
    match goal with Hg : guarded_pskl A |- _ => inversion Hg; subst end;
      simpl.
    + (* unit *)
      apply a_looksub__check;
        [ intro Hc; discriminate Hc | constructor | assumption | auto ].
    + (* var α *)
      destruct_if as [-> | HneX].
      * (* α = β : the source became α-free — switch to Absent *)
        match goal with
        | Hl : _ ⊢ _ ∼[ _ ] _ ⤳ _ ⨾ _ |- _ =>
            destruct ((proj2 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ Hl)
              as [-> ->]; [ simpl; fsetdec | ]
        end.
        apply a_looksub__absent. assumption.
      * apply a_looksub__check;
          [ assumption | constructor | assumption | auto ].
    + (* arrow *)
      apply a_looksub__check;
        [ intro Hc; discriminate Hc
        | constructor; apply subst_pskl_in_pskl_lc_pskl; auto
        | assumption
        | match goal with
          | IH : forall (b : atom) (q : pskl), _ |- _ =>
              let HI := fresh "HI" in
              pose proof (IH _ _ ltac:(eassumption) ltac:(eassumption)
                            ltac:(eassumption) ltac:(eassumption)) as HI;
              simpl in HI; exact HI
          end ].
  - (* LS-ForallR : only the SOURCE changes, and the scope premise keeps
       [P0] inside what the binder already avoids — so the SAME binder
       serves, no re-freshening (and hence no output renaming). *)
    apply a_looksub__forall_r with (β := β);
      [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper A P0 β0) as Hup;
        match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
          clear - Hup Hsc n; fsetdec end | ].
    apply H; auto. match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
      clear - Hsc; cbn; fsetdec end.
  - (* LS-Arrow *)
    apply a_looksub__arrow; auto.
  - (* LS-ForallL : the source opens.  If the substituted variable IS the
       binder the substitution is vacuous (the binder avoids [ftv P]);
       otherwise it commutes with the opening. *)
    destruct (β0 == β) as [-> | Hne].
    + rewrite subst_pskl_in_pskl_fresh_eq by (clear - n; cbn; fsetdec).
      apply a_looksub__forall_l with (β := β); assumption.
    + apply a_looksub__forall_l with (β := β);
        [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P P0 β0) as Hup;
          match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
          clear - Hup Hsc n; fsetdec end | ].
      rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
        [ | auto | assumption ].
      apply H; auto. match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
      clear - Hsc; cbn; fsetdec end.
  - (* LS-UnivGhostL *)
    apply a_looksub__univ_ghost_l. auto.
  - (* LE-Var *)
    destruct_if; [ exfalso; congruence | apply a_lookeq__var ].
  - (* LE-Absent *)
    apply a_lookeq__absent.
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P P0 β).
    fsetdec.
  - (* LE-Vacuous *)
    apply a_lookeq__vacuous.
  - (* LE-FlexR *)
    apply a_lookeq__flex_r.
    + (* the generated flexible still avoids the SUBSTITUTED source *)
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P P0 β0) as Hup.
      match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
          clear - Hup Hsc n; fsetdec end.
    + intro Hc. destruct P; simpl in Hc; try discriminate Hc.
      revert Hc.
      destruct_if as [-> | HneX]; intro Hc.
      * (* α = β : then α ∈ ftv (var β) forces α = β, contradiction *)
        simpl in *. fsetdec.
      * inversion Hc; subst. congruence.
    + match goal with
      | |- _ `in` ftvar_in_pskl (subst_pskl_in_pskl ?Qx ?bx ?Px) =>
          pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower Px Qx bx)
      end.
      fsetdec.
  - (* LE-Arrow *)
    apply a_lookeq__arrow; auto.
  - (* LE-ForallInh : the source opens (as LS-ForallL) *)
    destruct (β0 == β) as [-> | Hne].
    + rewrite subst_pskl_in_pskl_fresh_eq by (clear - n; cbn; fsetdec).
      apply a_lookeq__forall_inh with (β := β); assumption.
    + apply a_lookeq__forall_inh with (β := β);
        [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P P0 β0) as Hup;
          match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
          clear - Hup Hsc n; fsetdec end | ].
      rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
        [ | auto | assumption ].
      apply H; auto. match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
      clear - Hsc; cbn; fsetdec end.
  - (* LE-ForallSyn : the source opens *)
    destruct (β0 == β) as [-> | Hne].
    + rewrite subst_pskl_in_pskl_fresh_eq by (clear - n; cbn; fsetdec).
      apply a_lookeq__forall_syn with (β := β); assumption.
    + apply a_lookeq__forall_syn with (β := β);
        [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P P0 β0) as Hup;
          match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
          clear - Hup Hsc n; fsetdec end | ].
      rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
        [ | auto | assumption ].
      apply H; auto. match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
      clear - Hsc; cbn; fsetdec end.
  - (* LE-UnivGhost *)
    apply a_lookeq__univ_ghost. auto.
  - (* LE-UnivGhost1 : the TARGET opens; the source ∀◇ is substituted *)
    apply a_lookeq__univ_ghost1 with (β := β);
      [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P P0 β0) as Hup;
        match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
          clear - Hup Hsc n; fsetdec end | ].
    match goal with
    | IH : forall (b : atom) (q : pskl), _ |- _ =>
        let HI := fresh "HI" in
        pose proof (IH _ _ ltac:(eassumption) ltac:(eassumption)
                      ltac:(eassumption) ltac:(match goal with Hsc : ftvar_in_pskl P0 [<=] _ |- _ =>
      clear - Hsc; cbn; fsetdec end)) as HI;
        simpl in HI; exact HI
    end.
  - (* LE-UnivGhost2 *)
    apply a_lookeq__univ_ghost2; auto.
  - (* LE-UnivGhostR : switch to Absent when the source was β *)
    match goal with Hg : guarded_pskl P |- _ => inversion Hg; subst end;
      simpl.
    + (* unit *)
      apply a_lookeq__univ_ghost_r;
        [ intro Hc; discriminate Hc | constructor | auto ].
    + (* var α *)
      destruct_if as [-> | HneX].
      * (* α = β : the source became α-free — switch to Absent *)
        match goal with
        | Hl : _ ⊢ _ ∼[ _ ] _ ⤳ _ ⨾ _ |- _ =>
            destruct ((proj2 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ Hl)
              as [-> ->]; [ simpl; fsetdec | ]
        end.
        apply a_lookeq__absent. assumption.
      * apply a_lookeq__univ_ghost_r;
          [ assumption | constructor | auto ].
    + (* arrow *)
      apply a_lookeq__univ_ghost_r;
        [ intro Hc; discriminate Hc
        | constructor; apply subst_pskl_in_pskl_lc_pskl; auto
        | match goal with
          | IH : forall (b : atom) (q : pskl), _ |- _ =>
              let HI := fresh "HI" in
              pose proof (IH _ _ ltac:(eassumption) ltac:(eassumption)
                            ltac:(eassumption) ltac:(eassumption)) as HI;
              simpl in HI; exact HI
          end ].
Qed.

Lemma a_looksub_subst_stable : forall Θ α m P P' Ξ 𝒞 β P0,
  Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
  β <> α -> α `notin` ftvar_in_pskl P0 -> lc_pskl P0 ->
  ftvar_in_pskl P0 [<=] add α (ftvar_in_aenv Θ) ->
  Θ ⊢ (subst_pskl_in_pskl P0 β P) ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞.
Proof. intros; eapply (proj1 a_looksub_lookeq_subst_stable); eauto. Qed.

(* ===================================================================== *)
(*  §4b  The REVERSE direction of                                         *)
(*  lemma:constraint-collection-stable-substitution                       *)
(*                                                                        *)
(*  The subtyping-completeness ForallL case (P6-Ss) needs the converse of  *)
(*  §4: a run collected on a subject in which an α-free guess has already  *)
(*  been substituted for a rigid β ≠ α can be UNDONE, recovering the very  *)
(*  same Ξ ⨾ 𝒞 at the un-substituted subject.  Only two shapes of the      *)
(*  un-substituted subject matter: it IS the binder ([pskl_var_f βg]),     *)
(*  where the run happened entirely inside the α-free guess, so §4's       *)
(*  [a_looksub_lookeq_absent_nil] empties it and LS-Absent rebuilds; or it *)
(*  is anything else, where the substitution is STRUCTURAL and the rule    *)
(*  that fired is pinned by the subject's own top constructor.            *)
(*  (subtyping-proofs.tex:2632 uses exactly this direction.)               *)
(* ===================================================================== *)

(** A subject that IS the substituted binder collects nothing: the guess is
    α-free, so [a_looksub_lookeq_absent_nil] empties the run and LS-Absent
    rebuilds it at the bare variable (βg ≠ α). *)
Lemma a_looksub_subst_var : forall Θ α m βg P' Ξ 𝒞 Pg,
  Θ ⊢ Pg ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
  α `notin` ftvar_in_pskl Pg -> βg <> α ->
  Θ ⊢ (pskl_var_f βg) ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞.
Proof.
  intros Θ α m βg P' Ξ 𝒞 Pg H Hα Hβ.
  destruct ((proj1 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ _ H Hα) as [-> ->].
  apply a_looksub__absent. simpl. clear - Hβ. fsetdec.
Qed.

Lemma a_lookeq_subst_var : forall Θ α βg P' Ξ 𝒞 Pg,
  Θ ⊢ Pg ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
  α `notin` ftvar_in_pskl Pg -> βg <> α ->
  Θ ⊢ (pskl_var_f βg) ∼[ α ] P' ⤳ Ξ ⨾ 𝒞.
Proof.
  intros Θ α βg P' Ξ 𝒞 Pg H Hα Hβ.
  destruct ((proj2 a_looksub_lookeq_absent_nil) _ _ _ _ _ _ H Hα) as [-> ->].
  apply a_lookeq__absent. simpl. clear - Hβ. fsetdec.
Qed.

(** The REVERSE direction of
    [lemma:constraint-collection-stable-substitution]. *)
Lemma a_looksub_lookeq_subst_stable_rev :
  (forall Θ α m Ps P' Ξ 𝒞, Θ ⊢ Ps ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall Pu βg Pg, Ps = subst_pskl_in_pskl Pg βg Pu ->
     βg <> α -> βg `in` ftvar_in_aenv Θ ->
     α `notin` ftvar_in_pskl Pg -> lc_pskl Pg -> lc_pskl Pu ->
     Θ ⊢ Pu ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞) /\
  (forall Θ α Ps P' Ξ 𝒞, Θ ⊢ Ps ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall Pu βg Pg, Ps = subst_pskl_in_pskl Pg βg Pu ->
     βg <> α -> βg `in` ftvar_in_aenv Θ ->
     α `notin` ftvar_in_pskl Pg -> lc_pskl Pg -> lc_pskl Pu ->
     Θ ⊢ Pu ∼[ α ] P' ⤳ Ξ ⨾ 𝒞).
Proof.
  apply (a_looksub_lookeq_mutind
           (fun Θ α m Ps P' Ξ 𝒞 _ =>
              forall Pu βg Pg, Ps = subst_pskl_in_pskl Pg βg Pu ->
              βg <> α -> βg `in` ftvar_in_aenv Θ ->
              α `notin` ftvar_in_pskl Pg -> lc_pskl Pg -> lc_pskl Pu ->
              Θ ⊢ Pu ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞)
           (fun Θ α Ps P' Ξ 𝒞 _ =>
              forall Pu βg Pg, Ps = subst_pskl_in_pskl Pg βg Pu ->
              βg <> α -> βg `in` ftvar_in_aenv Θ ->
              α `notin` ftvar_in_pskl Pg -> lc_pskl Pg -> lc_pskl Pu ->
              Θ ⊢ Pu ∼[ α ] P' ⤳ Ξ ⨾ 𝒞)).
  - (* LS-Var *)
    intros Θ α m P Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    destruct (β' == βg) as [-> | Hne'].
    + subst Pg. exfalso. cbn in Hα. clear - Hα. fsetdec.
    + injection Heq as Heq'. subst β'. apply a_looksub__var.
  - (* LS-Absent *)
    intros Θ α m P P' Hnin Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    subst P. apply a_looksub__absent.
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower Pu Pg βg) as Hlow.
    clear - Hnin Hlow Hβ. fsetdec.
  - (* LS-Vacuous *)
    intros; apply a_looksub__vacuous.
  - (* LS-Check *)
    intros Θ α A B Ξ C Hne Hg Hg0 Hlk IH Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq; subst A.
    + apply a_looksub__check; assumption.
    + inversion Hg.
    + destruct (β' == βg) as [-> | Hne'].
      * eapply a_looksub_subst_var;
          [ apply a_looksub__check; eassumption | assumption | assumption ].
      * apply a_looksub__check; assumption.
    + inversion HlcPu as [ | | ? ? HlcPa HlcPb | | | ]; subst.
      apply a_looksub__check;
        [ discriminate
        | apply guarded_pskl__arrow; assumption
        | assumption
        | apply (IH (pskl_arrow Pa Pb) βg Pg);
            [ reflexivity | assumption | assumption | assumption | assumption
            | assumption ] ].
    + inversion Hg.
    + inversion Hg.
    + inversion Hg.
  - (* LS-ForallR *)
    intros Θ α A B Ξ C β Hsc Hpre IH Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    (* target-opening: the source is only UN-substituted, and the binder
       still avoids it because [βg] itself is a context name *)
    subst A.
    assert (Hne1 : βg <> β) by (clear - Hsc Hβin; fsetdec).
    apply a_looksub__forall_r with (β := β);
      [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower Pu Pg βg) as Hlow;
        clear - Hsc Hlow Hne1; fsetdec | ].
    apply (IH Pu βg Pg);
      solve [ assumption | reflexivity | clear - Hβin; cbn; fsetdec ].
  - (* LS-Arrow *)
    intros Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hlk1 IH1 Hlk2 IH2
           Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    + destruct (β' == βg) as [-> | Hne']; [ | discriminate Heq ].
      subst Pg.
      eapply a_looksub_subst_var;
        [ apply a_looksub__arrow; eassumption | assumption | assumption ].
    + inversion HlcPu as [ | | ? ? HlcPa HlcPb | | | ]; subst.
      injection Heq as Heq1 Heq2. subst P1. subst P2.
      apply a_looksub__arrow.
      * apply (IH1 Pa βg Pg); solve [ assumption | reflexivity ].
      * apply (IH2 Pb βg Pg); solve [ assumption | reflexivity ].
  - (* LS-ForallL *)
    intros Θ α m P P' Ξ C β Hsc Hpre IH Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    + destruct (β' == βg) as [-> | Hne']; [ | discriminate Heq ].
      subst Pg.
      eapply a_looksub_subst_var;
        [ apply a_looksub__forall_l with (β := β); [ exact Hsc | exact Hpre ]
        | assumption | assumption ].
    + inversion HlcPu as [ | | | ? Hopen | | ]; subst.
      injection Heq as Heq0. subst P.
      assert (Hne1 : βg <> β) by (clear - Hsc Hβin; fsetdec).
      apply a_looksub__forall_l with (β := β);
        [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower Pb Pg βg) as Hlow;
          clear - Hsc Hlow Hne1; fsetdec | ].
      apply (IH (open_pskl_wrt_pskl Pb (pskl_var_f β)) βg Pg);
        [ apply subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
            [ exact Hne1 | assumption ]
        | assumption | clear - Hβin; cbn; fsetdec
        | assumption | assumption | apply Hopen ].
  - (* LS-UnivGhostL *)
    intros Θ α m P P' Ξ C Hpre IH Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    + destruct (β' == βg) as [-> | Hne']; [ | discriminate Heq ].
      subst Pg.
      eapply a_looksub_subst_var;
        [ apply a_looksub__univ_ghost_l; exact Hpre
        | assumption | assumption ].
    + inversion HlcPu as [ | | | | | ? HlcPb ]; subst.
      injection Heq as Heq0. subst P.
      apply a_looksub__univ_ghost_l.
      apply (IH Pb βg Pg); solve [ assumption | reflexivity ].
  - (* LE-Var *)
    intros Θ α P Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    destruct (β' == βg) as [-> | Hne'].
    + subst Pg. exfalso. cbn in Hα. clear - Hα. fsetdec.
    + injection Heq as Heq'. subst β'. apply a_lookeq__var.
  - (* LE-Absent *)
    intros Θ α P P' Hnin Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    subst P. apply a_lookeq__absent.
    pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower Pu Pg βg) as Hlow.
    clear - Hnin Hlow Hβ. fsetdec.
  - (* LE-Vacuous *)
    intros; apply a_lookeq__vacuous.
  - (* LE-FlexR *)
    intros Θ α P β α1 Hfr Hne Hin Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    subst P. apply a_lookeq__flex_r.
    + (* the generated flexible avoids the UN-substituted source too: it
         avoids [ftvar_in_aenv Θ], where [βg] lives *)
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower Pu Pg βg) as Hlow.
      assert (Hα1βg : α1 <> βg) by (clear - Hfr Hβin; fsetdec).
      clear - Hfr Hlow Hα1βg; fsetdec.
    + intro Hc. subst Pu. cbn in Hne.
      (* destruct the scrutinee IN Hne, so its [if] actually reduces *)
      match type of Hne with context[if ?e then _ else _] => destruct e end;
        [ congruence | apply Hne; reflexivity ].
    + pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper Pu Pg βg) as Hup.
      clear - Hin Hα Hup. fsetdec.
  - (* LE-Arrow *)
    intros Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hlk1 IH1 Hlk2 IH2
           Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    + destruct (β' == βg) as [-> | Hne']; [ | discriminate Heq ].
      subst Pg.
      eapply a_lookeq_subst_var;
        [ apply a_lookeq__arrow; eassumption | assumption | assumption ].
    + inversion HlcPu as [ | | ? ? HlcPa HlcPb | | | ]; subst.
      injection Heq as Heq1 Heq2. subst P1. subst P2.
      apply a_lookeq__arrow.
      * apply (IH1 Pa βg Pg); solve [ assumption | reflexivity ].
      * apply (IH2 Pb βg Pg); solve [ assumption | reflexivity ].
  - (* LE-ForallInh *)
    intros Θ α P P' Ξ C β Hsc Hpre IH Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    + destruct (β' == βg) as [-> | Hne']; [ | discriminate Heq ].
      subst Pg.
      eapply a_lookeq_subst_var;
        [ apply a_lookeq__forall_inh with (β := β); [ exact Hsc | exact Hpre ]
        | assumption | assumption ].
    + inversion HlcPu as [ | | | ? Hopen | | ]; subst.
      injection Heq as Heq0. subst P.
      assert (Hne1 : βg <> β) by (clear - Hsc Hβin; fsetdec).
      apply a_lookeq__forall_inh with (β := β);
        [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower Pb Pg βg) as Hlow;
          clear - Hsc Hlow Hne1; fsetdec | ].
      apply (IH (open_pskl_wrt_pskl Pb (pskl_var_f β)) βg Pg);
        [ apply subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
            [ exact Hne1 | assumption ]
        | assumption | clear - Hβin; cbn; fsetdec
        | assumption | assumption | apply Hopen ].
  - (* LE-ForallSyn *)
    intros Θ α P P' Ξ C β Hsc Hpre IH Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    + destruct (β' == βg) as [-> | Hne']; [ | discriminate Heq ].
      subst Pg.
      eapply a_lookeq_subst_var;
        [ apply a_lookeq__forall_syn with (β := β); [ exact Hsc | exact Hpre ]
        | assumption | assumption ].
    + inversion HlcPu as [ | | | ? Hopen | | ]; subst.
      injection Heq as Heq0. subst P.
      assert (Hne1 : βg <> β) by (clear - Hsc Hβin; fsetdec).
      apply a_lookeq__forall_syn with (β := β);
        [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower Pb Pg βg) as Hlow;
          clear - Hsc Hlow Hne1; fsetdec | ].
      apply (IH (open_pskl_wrt_pskl Pb (pskl_var_f β)) βg Pg);
        [ apply subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
            [ exact Hne1 | assumption ]
        | assumption | clear - Hβin; cbn; fsetdec
        | assumption | assumption | apply Hopen ].
  - (* LE-UnivGhost *)
    intros Θ α P P' Ξ C Hpre IH Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    + destruct (β' == βg) as [-> | Hne']; [ | discriminate Heq ].
      subst Pg.
      eapply a_lookeq_subst_var;
        [ apply a_lookeq__univ_ghost; exact Hpre | assumption | assumption ].
    + inversion HlcPu as [ | | | | | ? HlcPb ]; subst.
      injection Heq as Heq0. subst P.
      apply a_lookeq__univ_ghost.
      apply (IH Pb βg Pg); solve [ assumption | reflexivity ].
  - (* LE-UnivGhost1 *)
    intros Θ α P P' Ξ C β Hsc Hpre IH Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    + destruct (β' == βg) as [-> | Hne']; [ | discriminate Heq ].
      subst Pg.
      eapply a_lookeq_subst_var;
        [ apply a_lookeq__univ_ghost1 with (β := β); [ exact Hsc | exact Hpre ]
        | assumption | assumption ].
    + injection Heq as Heq0. subst P.
      assert (Hne1 : βg <> β) by (clear - Hsc Hβin; fsetdec).
      apply a_lookeq__univ_ghost1 with (β := β);
        [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower Pb Pg βg) as Hlow;
          cbn in Hsc |- *; clear - Hsc Hlow Hne1; fsetdec | ].
      apply (IH (pskl_tophole Pb) βg Pg);
        [ reflexivity | assumption | clear - Hβin; cbn; fsetdec
        | assumption | assumption | assumption ].
  - (* LE-UnivGhost2 *)
    intros Θ α P P' Ξ C Hg Hpre IH Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq;
      try discriminate Heq.
    + destruct (β' == βg) as [-> | Hne']; [ | discriminate Heq ].
      subst Pg.
      eapply a_lookeq_subst_var;
        [ apply a_lookeq__univ_ghost2; eassumption
        | assumption | assumption ].
    + inversion HlcPu as [ | | | | | ? HlcPb ]; subst.
      injection Heq as Heq0. subst P.
      apply a_lookeq__univ_ghost2; [ assumption | ].
      apply (IH Pb βg Pg); solve [ assumption | reflexivity ].
  - (* LE-UnivGhostR *)
    intros Θ α P P' Ξ C Hne Hg Hpre IH Pu βg Pg Heq Hβ Hβin Hα HlcPg HlcPu.
    destruct Pu as [ | n | β' | Pa Pb | Pb | | Pb ]; cbn in Heq; subst P.
    + apply a_lookeq__univ_ghost_r; assumption.
    + inversion Hg.
    + destruct (β' == βg) as [-> | Hne'].
      * eapply a_lookeq_subst_var;
          [ apply a_lookeq__univ_ghost_r; eassumption
          | assumption | assumption ].
      * apply a_lookeq__univ_ghost_r; assumption.
    + inversion HlcPu as [ | | ? ? HlcPa HlcPb | | | ]; subst.
      apply a_lookeq__univ_ghost_r;
        [ discriminate
        | apply guarded_pskl__arrow; assumption
        | apply (IH (pskl_arrow Pa Pb) βg Pg);
            [ reflexivity | assumption | assumption | assumption | assumption
            | assumption ] ].
    + inversion Hg.
    + inversion Hg.
    + inversion Hg.
Qed.

Lemma a_looksub_subst_stable_rev : forall Θ α m P' Ξ 𝒞 Pu βg Pg,
  Θ ⊢ (subst_pskl_in_pskl Pg βg Pu) ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
  βg <> α -> βg `in` ftvar_in_aenv Θ ->
  α `notin` ftvar_in_pskl Pg -> lc_pskl Pg -> lc_pskl Pu ->
  Θ ⊢ Pu ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞.
Proof.
  intros; eapply (proj1 a_looksub_lookeq_subst_stable_rev);
    try eassumption; reflexivity.
Qed.

(* ===================================================================== *)
(*  §5  Renaming the looked-for variable                                  *)
(*                                                                        *)
(*  Collected constraints mention only input residuals, never the looked  *)
(*  variable itself, so the look run is stable under renaming it — the    *)
(*  Barendregt device that keeps the KEY decoration's substitution        *)
(*  variable clear of guessed flexible names.                             *)
(* ===================================================================== *)

Lemma ftv_subst_var_in : forall P α α',
  α `in` ftvar_in_pskl P ->
  α' `in` ftvar_in_pskl (subst_pskl_in_pskl (pskl_var_f α') α P).
Proof.
  induction P as [ | | α1 | | | | ]; intros α α' Hin; simpl in *;
    try solve [ exfalso; fsetdec ].
  - destruct_if as [-> | Hne]; simpl; [ fsetdec | exfalso; fsetdec ].
  - destruct (AtomSetProperties.In_dec α (ftvar_in_pskl P1)) as [Hi | Hni];
      [ pose proof (IHP1 _ α' Hi) | ];
      destruct (AtomSetProperties.In_dec α (ftvar_in_pskl P2)) as [Hi2 | Hni2];
      try pose proof (IHP2 _ α' Hi2); try fsetdec.
  - eauto.
  - eauto.
Qed.

Lemma a_looksub_lookeq_rename_var :
  (forall Θ α m P P' Ξ 𝒞, Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall α', α' `notin` ftvar_in_pskl P ->
     Θ ⊢ (subst_pskl_in_pskl (pskl_var_f α') α P) ≼[ α' , m ] P' ⤳ Ξ ⨾ 𝒞) /\
  (forall Θ α P P' Ξ 𝒞, Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall α', α' `notin` ftvar_in_pskl P ->
     Θ ⊢ (subst_pskl_in_pskl (pskl_var_f α') α P) ∼[ α' ] P' ⤳ Ξ ⨾ 𝒞).
Proof.
  apply (a_looksub_lookeq_mutind
           (fun Θ α m P P' Ξ 𝒞 _ =>
              forall α', α' `notin` ftvar_in_pskl P ->
              Θ ⊢ (subst_pskl_in_pskl (pskl_var_f α') α P) ≼[ α' , m ] P' ⤳ Ξ ⨾ 𝒞)
           (fun Θ α P P' Ξ 𝒞 _ =>
              forall α', α' `notin` ftvar_in_pskl P ->
              Θ ⊢ (subst_pskl_in_pskl (pskl_var_f α') α P) ∼[ α' ] P' ⤳ Ξ ⨾ 𝒞));
    intros; simpl.
  - (* LS-Var *)
    destruct_if as [_ | Hne];
        [ | exfalso; congruence ].
    apply a_looksub__var.
  - (* LS-Absent *)
    rewrite subst_pskl_in_pskl_fresh_eq; [ | assumption ].
    apply a_looksub__absent. assumption.
  - (* LS-Vacuous *)
    apply a_looksub__vacuous.
  - (* LS-Check *)
    apply a_looksub__check.
    + intro Hc. destruct A; simpl in Hc; try discriminate Hc.
      revert Hc.
      destruct_if as [-> | HneX]; intro Hc; [ congruence | ].
      inversion Hc; subst. simpl in *. fsetdec.
    + apply guarded_pskl_subst_var; assumption.
    + assumption.
    + auto.
  - (* LS-ForallR : only the SOURCE changes, and the scope premise keeps
       [P0] inside what the binder already avoids — so the SAME binder
       serves, no re-freshening (and hence no output renaming). *)
    apply a_looksub__forall_r with (β := β);
      [ pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper A P0 β0) as Hup;
        clear - Hup H2 n; fsetdec | ].
    apply H; auto. clear - H2; cbn; fsetdec.
  - (* LS-Arrow *)
    apply a_looksub__arrow;
      [ match goal with IH : forall a, a `notin` _ -> _ |- _ => idtac end | ];
      simpl in *;
      [ match goal with
        | IH : context [ _ ⊢ _ ∼[ _ ] _ ⤳ _ ⨾ _ ] |- _ => apply IH; fsetdec
        end
      | match goal with
        | IH : context [ _ ⊢ _ ≼[ _ , _ ] _ ⤳ _ ⨾ _ ] |- _ => apply IH; fsetdec
        end ].
  - (* LS-ForallL *)
    apply a_looksub__forall_l
      with (L := L `union` singleton α `union` singleton α').
    intros α1 Hα1.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hα1; fsetdec | constructor ].
    match goal with
    | IH : forall β, β `notin` _ -> _ |- _ =>
        apply IH; [ clear - Hα1; fsetdec | ]
    end.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α1)).
    simpl in *. fsetdec.
  - (* LS-UnivGhostL *)
    apply a_looksub__univ_ghost_l. auto.
  - (* LE-Var *)
    destruct_if as [_ | Hne];
        [ | exfalso; congruence ].
    apply a_lookeq__var.
  - (* LE-Absent *)
    rewrite subst_pskl_in_pskl_fresh_eq; [ | assumption ].
    apply a_lookeq__absent. assumption.
  - (* LE-Vacuous *)
    apply a_lookeq__vacuous.
  - (* LE-FlexR *)
    apply a_lookeq__flex_r.
    + (* the generated flexible still avoids the SUBSTITUTED source *)
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper P P0 β0) as Hup.
      clear - Hup H2 n; fsetdec.
    + intro Hc. destruct P; simpl in Hc; try discriminate Hc.
      match goal with
      | Hin : α `in` ftvar_in_pskl (pskl_var_f ?α0) |- _ =>
          simpl in Hin;
          assert (Hα0α : α0 = α) by (clear - Hin; fsetdec);
          subst; congruence
      end.
    + apply ftv_subst_var_in. assumption.
  - (* LE-Arrow *)
    apply a_lookeq__arrow; simpl in *;
      match goal with
      | IH1 : context [ subst_pskl_in_pskl _ _ _ ⊢ ?Pa ∼[ _ ] ?Qa ⤳ _ ⨾ _ ] ,
        IH2 : context [ subst_pskl_in_pskl _ _ _ ⊢ ?Pb ∼[ _ ] ?Qb ⤳ _ ⨾ _ ] |- _ =>
          idtac
      end;
      [ match goal with
        | IH : forall a, a `notin` ftvar_in_pskl ?Px -> _ |-
            _ ⊢ (subst_pskl_in_pskl _ _ ?Px) ∼[ _ ] _ ⤳ _ ⨾ _ =>
            apply IH; fsetdec
        end
      | match goal with
        | IH : forall a, a `notin` ftvar_in_pskl ?Px -> _ |-
            _ ⊢ (subst_pskl_in_pskl _ _ ?Px) ∼[ _ ] _ ⤳ _ ⨾ _ =>
            apply IH; fsetdec
        end ].
  - (* LE-ForallInh *)
    apply a_lookeq__forall_inh
      with (L := L `union` singleton α `union` singleton α').
    intros α1 Hα1.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hα1; fsetdec | constructor ].
    match goal with
    | IH : forall β, β `notin` _ -> _ |- _ =>
        apply IH; [ clear - Hα1; fsetdec | ]
    end.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α1)).
    simpl in *. fsetdec.
  - (* LE-ForallSyn *)
    apply a_lookeq__forall_syn
      with (L := L `union` singleton α `union` singleton α').
    intros α1 Hα1.
    rewrite subst_pskl_in_pskl_open_pskl_wrt_pskl_var;
      [ | clear - Hα1; fsetdec | constructor ].
    match goal with
    | IH : forall β, β `notin` _ -> _ |- _ =>
        apply IH; [ clear - Hα1; fsetdec | ]
    end.
    pose proof (ftvar_in_pskl_open_pskl_wrt_pskl_upper P (pskl_var_f α1)).
    simpl in *. fsetdec.
  - (* LE-UnivGhost *)
    apply a_lookeq__univ_ghost. simpl in *. auto.
  - (* LE-UnivGhost1 *)
    apply a_lookeq__univ_ghost1 with (L := L). intros α1 Hα1.
    match goal with
    | IH : forall β, β `notin` _ -> forall a, _ |- _ =>
        specialize (IH α1 Hα1 α' ltac:(assumption)); simpl in IH; exact IH
    end.
  - (* LE-UnivGhost2 *)
    apply a_lookeq__univ_ghost2; [ assumption | ]. simpl in *. auto.
  - (* LE-UnivGhostR *)
    apply a_lookeq__univ_ghost_r.
    + intro Hc. destruct P; simpl in Hc; try discriminate Hc.
      revert Hc.
      destruct_if as [-> | HneX]; intro Hc; [ congruence | ].
      inversion Hc; subst. simpl in *. fsetdec.
    + apply guarded_pskl_subst_var; assumption.
    + auto.
Qed.

Lemma a_looksub_rename_var : forall Θ α m P P' Ξ 𝒞 α',
  Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
  α' `notin` ftvar_in_pskl P ->
  Θ ⊢ (subst_pskl_in_pskl (pskl_var_f α') α P) ≼[ α' , m ] P' ⤳ Ξ ⨾ 𝒞.
Proof. intros; eapply (proj1 a_looksub_lookeq_rename_var); eauto. Qed.

(* ===================================================================== *)
(*  §8  Rigid renames of a look run (moved from prop_look_complete_cstr,  *)
(*  2026-07-31 — the exists-fresh ForallR consumers need them below the   *)
(*  decoration layer)                                                     *)
(* ===================================================================== *)

Lemma ftv_subst_var_keep : forall P β α1 α,
  α `in` ftvar_in_pskl P -> β <> α ->
  α `in` ftvar_in_pskl (subst_pskl_in_pskl (pskl_var_f α1) β P).
Proof.
  intros P β α1 α Hin Hne.
  pose proof (ftvar_in_pskl_subst_pskl_in_pskl_lower P (pskl_var_f α1) β) as Hlo.
  clear - Hlo Hin Hne; fsetdec.
Qed.

Lemma subst_var_pskl_neq_var : forall P β α1 α,
  P <> pskl_var_f α -> α1 <> α -> β <> α ->
  subst_pskl_in_pskl (pskl_var_f α1) β P <> pskl_var_f α.
Proof.
  intros P β α1 α Hne Hα1 Hβ Hc.
  destruct P; simpl in Hc; try discriminate Hc.
  destruct (α0 == β) as [-> | Hne2];
    [ inversion Hc; congruence | inversion Hc; subst; congruence ].
Qed.

(* (viii) SIMULTANEOUS renaming of a rigid variable on BOTH sides —
   the canonical TARGET-only form (DESIGN.md §4.3, canon rule 3): it renames
   the CONTEXT, the GENERATED block [Ξ] and the collected constraints [𝒞]
   too, and it inducts on the SUBJECT'S SIZE.

   Two campaign shapes meet here.  (1) SIZE INDUCTION, because a binder row
   may have to MOVE its binder, and a re-freshened premise is no
   sub-derivation.  (2) An OUTPUT-freshness premise on the TARGET
   ([α1 ∉ dom Ξ ∪ ftv 𝒞]) — LOAD-BEARING, and this is exactly where the LEAK
   shows: a rule's binder that ESCAPED into Ξ or 𝒞 can no longer be moved
   (moving it would change the outputs), so the target must simply differ
   from it; a binder that did NOT escape can be moved, and then the outputs
   stay fixed.  The proof does that case split at every binder row.  Without
   the premise the claim is FALSE — take the run of
   cex/cex_look_subst_stable_leak.v and rename to its own leaked binder. *)
(** Identities the rename degenerates to, and the one-step context facts the
    binder rows need. *)
Lemma subst_cstrs_same : forall β 𝒞, subst_cstrs β β 𝒞 = 𝒞.
Proof.
  induction 𝒞 as [ | c 𝒞' IH ]; cbn; [ reflexivity | ].
  rewrite IH; destruct c; cbn; rewrite subst_pskl_var_same; reflexivity.
Qed.

Lemma rename_aenv_same : forall β Θ, rename_aenv β β Θ = Θ.
Proof.
  induction Θ as [ | [x bd] Θ' IH ]; cbn; [ reflexivity | ].
  rewrite IH. destruct (x == β) as [-> | _];
    destruct bd; cbn; try rewrite subst_ptyp_var_same;
    try rewrite subst_pskl_var_same; reflexivity.
Qed.

(* ⛔ WIP (cluster 3, stopped here 2026-08-01).  [a_looksub_lookeq_rename_tvar]
   below is stated in its FINAL, correct form but its binder rows are not
   written yet; the file therefore does not compile past this point.  The
   three cases each binder row must take are FORCED, and all three are
   worked out — see PROGRESS.md's 2026-08-01 cluster-3 entry:

     β = b   the rename's SOURCE is the rule's own binder.  [Hfr0] then makes
             the substitution the identity on Θ, P and P', and the rule
             re-fires at the TARGET α1 (fresh for them by the target premise);
             the premise comes from the IH renaming b ⤳ α1, whose context is
             [rename α1 b ((b~tvar)++Θ) = (α1~tvar)++Θ].

     α1 = b  the rename's TARGET is the binder, so the binder must MOVE.  This
             is where the target's OUTPUT-freshness premise pays: α1 ∉ dom Ξ ∪
             ftv 𝒞 and α1 = b together say the binder did NOT leak, so moving
             it to a fresh δ leaves Ξ and 𝒞 fixed ([rename_aenv_fresh_eq],
             [subst_cstrs_fresh_eq] via [a_looksub_lookeq_generated_ftvar]).
             Two IH applications: b ⤳ δ, then β ⤳ α1.

     else    the binder stays put; one IH application, and the side condition
             is re-established from [Hfr0] plus the ftv-upper bounds and b ≠ α1.

   The pattern is [a_solve_sub_eq_rename_size]'s (prop_solve_sub.v) — that
   proof's SS-ForallL row is the line-by-line model, including the
   [subst_pskl_in_pskl_intro] / [rename_aenv_cons_tvar_neq] rewrites. *)
Lemma a_looksub_lookeq_rename_tvar_size : forall n,
  (forall Θ α m P P' Ξ 𝒞,
     2 * (size_pskl P + size_pskl P') + 1 <= n ->
     Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall β α1, β <> α -> α1 <> α ->
     α1 `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union`
                ftvar_in_pskl P' `union` dom Ξ `union` ftvar_in_cstrs 𝒞 ->
     (rename_aenv α1 β Θ) ⊢ (subst_pskl_in_pskl (pskl_var_f α1) β P) ≼[ α , m ]
       (subst_pskl_in_pskl (pskl_var_f α1) β P')
       ⤳ (rename_aenv α1 β Ξ) ⨾ (subst_cstrs α1 β 𝒞)) /\
  (forall Θ α P P' Ξ 𝒞,
     2 * (size_pskl P + size_pskl P') <= n ->
     Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
     forall β α1, β <> α -> α1 <> α ->
     α1 `notin` ftvar_in_aenv Θ `union` ftvar_in_pskl P `union`
                ftvar_in_pskl P' `union` dom Ξ `union` ftvar_in_cstrs 𝒞 ->
     (rename_aenv α1 β Θ) ⊢ (subst_pskl_in_pskl (pskl_var_f α1) β P) ∼[ α ]
       (subst_pskl_in_pskl (pskl_var_f α1) β P')
       ⤳ (rename_aenv α1 β Ξ) ⨾ (subst_cstrs α1 β 𝒞)).
Proof.
  induction n as [ | n IHn ].
  { split; intros Θ α; try (intros m); intros P P' Ξ 𝒞 Hn Hd;
      exfalso; pose proof (size_pskl_min P); pose proof (size_pskl_min P'); lia. }
  destruct IHn as [IHs IHe].
  split.
  (* ==================== the [a_looksub] half ==================== *)
  { intros Θ α m P P' Ξ 𝒞 Hn Hd β α1 Hβα Hα1α Hfr.
    destruct Hd as
      [ Θ α m Q                                   (* LS-Var *)
      | Θ α m Q Q' Hnf                            (* LS-Absent *)
      | Θ α m Q                                   (* LS-Vacuous *)
      | Θ α A B Ξ0 C0 Hne Hg Hg0 Hp               (* LS-Check *)
      | Θ α A B Ξ0 C0 b Hfr0 Hp                   (* LS-ForallR *)
      | Θ α m P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hp1 Hp2   (* LS-Arrow *)
      | Θ α m Q Q' Ξ0 C0 b Hfr0 Hp                (* LS-ForallL *)
      | Θ α m Q Q' Ξ0 C0 Hp ];                    (* LS-UnivGhostL *)
      cbn in Hn, Hfr |- *.
    - (* LS-Var *)
      destruct_if; [ exfalso; congruence | apply a_looksub__var ].
    - (* LS-Absent *)
      apply a_looksub__absent.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper Q (pskl_var_f α1) β)
        as Hup; cbn in Hup; clear - Hup Hnf Hα1α; fsetdec.
    - (* LS-Vacuous *) apply a_looksub__vacuous.
    - (* LS-Check *)
      apply a_looksub__check;
        [ apply subst_var_pskl_neq_var; auto
        | apply guarded_pskl_subst_var; assumption
        | apply guarded_pskl_subst_var; assumption
        | apply IHe with (Θ := Θ); solve [ lia | assumption ] ].
    - (* LS-ForallR — the TARGET opens; the binder LEAKS *)
      look_rename_binder_r IHs a_looksub__forall_r A B b Hfr0 Hp.
    - (* LS-Arrow *)
      rewrite rename_aenv_app, subst_cstrs_app.
      rewrite ftvar_in_cstrs_app, dom_app in Hfr.
      apply a_looksub__arrow;
        [ apply IHe with (Θ := Θ); solve [ lia | assumption
                                         | clear - Hfr; fsetdec ]
        | apply IHs with (Θ := Θ); solve [ lia | assumption
                                         | clear - Hfr; fsetdec ] ].
    - (* LS-ForallL — the SOURCE opens; the binder LEAKS *)
      look_rename_binder_l IHs a_looksub__forall_l Q Q' b Hfr0 Hp.
    - (* LS-UnivGhostL *)
      apply a_looksub__univ_ghost_l;
        apply IHs with (Θ := Θ); solve [ lia | assumption ]. }
  (* ==================== the [a_lookeq] half ==================== *)
  { intros Θ α P P' Ξ 𝒞 Hn Hd β α1 Hβα Hα1α Hfr.
    destruct Hd as
      [ Θ α Q                                     (* LE-Var *)
      | Θ α Q Q' Hnf                              (* LE-Absent *)
      | Θ α Q                                     (* LE-Vacuous *)
      | Θ α Q b γ Hfr0 Hne Hin                    (* LE-FlexR *)
      | Θ α P1 P2 P1' P2' Ξ1 Ξ2 C1 C2 Hp1 Hp2     (* LE-Arrow *)
      | Θ α Q Q' Ξ0 C0 b Hfr0 Hp                  (* LE-ForallInh *)
      | Θ α Q Q' Ξ0 C0 b Hfr0 Hp                  (* LE-ForallSyn *)
      | Θ α Q Q' Ξ0 C0 Hp                         (* LE-UnivGhost *)
      | Θ α Q Q' Ξ0 C0 b Hfr0 Hp                  (* LE-UnivGhost1 *)
      | Θ α Q Q' Ξ0 C0 Hg Hp                      (* LE-UnivGhost2 *)
      | Θ α Q Q' Ξ0 C0 Hne Hg Hp ];               (* LE-UnivGhostR *)
      cbn in Hn, Hfr |- *.
    - (* LE-Var *)
      destruct_if; [ exfalso; congruence | apply a_lookeq__var ].
    - (* LE-Absent *)
      apply a_lookeq__absent.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper Q (pskl_var_f α1) β)
        as Hup; cbn in Hup; clear - Hup Hnf Hα1α; fsetdec.
    - (* LE-Vacuous *) apply a_lookeq__vacuous.
    - (* LE-FlexR : the GENERATED name is renamed with everything else *)
      cbn in Hfr0 |- *.
      pose proof (ftvar_in_aenv_rename_aenv Θ α1 β) as Hren.
      pose proof (ftvar_in_pskl_subst_pskl_in_pskl_upper Q (pskl_var_f α1) β)
        as Hup; cbn in Hup.
      destruct (γ == β) as [-> | Hγβ]; cbn;
        (apply a_lookeq__flex_r;
         [ (* the generated name still avoids everything it must *)
           try solve [ clear - Hfr Hren Hup Hα1α; fsetdec
                     | clear - Hfr0 Hren Hup; fsetdec ]
         | apply subst_var_pskl_neq_var; auto
         | apply ftv_subst_var_keep; auto ]).
    - (* LE-Arrow *)
      rewrite rename_aenv_app, subst_cstrs_app.
      rewrite ftvar_in_cstrs_app, dom_app in Hfr.
      apply a_lookeq__arrow;
        [ apply IHe with (Θ := Θ); solve [ lia | assumption
                                         | clear - Hfr; fsetdec ]
        | apply IHe with (Θ := Θ); solve [ lia | assumption
                                         | clear - Hfr; fsetdec ] ].
    - (* LE-ForallInh — BOTH sides open; the binder LEAKS *)
      look_rename_binder_lr IHe a_lookeq__forall_inh Q Q' b Hfr0 Hp.
    - (* LE-ForallSyn — the SOURCE opens *)
      look_rename_binder_l IHe a_lookeq__forall_syn Q Q' b Hfr0 Hp.
    - (* LE-UnivGhost *)
      apply a_lookeq__univ_ghost;
        apply IHe with (Θ := Θ); solve [ lia | assumption ].
    - (* LE-UnivGhost1 — the TARGET opens *)
      look_rename_binder_r IHe a_lookeq__univ_ghost1 Q Q' b Hfr0 Hp.
    - (* LE-UnivGhost2 *)
      apply a_lookeq__univ_ghost2;
        [ apply guarded_pskl_subst_var; assumption
        | apply IHe with (Θ := Θ); solve [ lia | assumption ] ].
    - (* LE-UnivGhostR *)
      apply a_lookeq__univ_ghost_r;
        [ apply subst_var_pskl_neq_var; auto
        | apply guarded_pskl_subst_var; assumption
        | apply IHe with (Θ := Θ); solve [ lia | assumption ] ]. }
Qed.

Corollary a_looksub_rename_tvar_keep : forall Θ α m P P' Ξ 𝒞 β α1,
  Θ ⊢ P ≼[ α , m ] P' ⤳ Ξ ⨾ 𝒞 ->
  β <> α -> α1 <> α ->
  β `notin` dom Ξ -> β `notin` ftvar_in_cstrs 𝒞 ->
  Θ ⊢ (subst_pskl_in_pskl (pskl_var_f α1) β P) ≼[ α , m ]
    (subst_pskl_in_pskl (pskl_var_f α1) β P') ⤳ Ξ ⨾ 𝒞.
Proof.
  intros * Hlk Hβ Hα1 HβΞ Hβ𝒞.
  pose proof (a_looksub_generated_ftvar Hlk) as Hftv.
  pose proof ((proj1 a_looksub_lookeq_rename_tvar) _ _ _ _ _ _ _ Hlk _ α1 Hβ Hα1) as Hr.
  rewrite (@rename_aenv_fresh_eq Ξ α1 β) in Hr by (clear - Hftv HβΞ; fsetdec).
  rewrite (@subst_cstrs_fresh_eq α1 β 𝒞) in Hr by exact Hβ𝒞.
  exact Hr.
Qed.

Corollary a_lookeq_rename_tvar_keep : forall Θ α P P' Ξ 𝒞 β α1,
  Θ ⊢ P ∼[ α ] P' ⤳ Ξ ⨾ 𝒞 ->
  β <> α -> α1 <> α ->
  β `notin` dom Ξ -> β `notin` ftvar_in_cstrs 𝒞 ->
  Θ ⊢ (subst_pskl_in_pskl (pskl_var_f α1) β P) ∼[ α ]
    (subst_pskl_in_pskl (pskl_var_f α1) β P') ⤳ Ξ ⨾ 𝒞.
Proof.
  intros * Hlk Hβ Hα1 HβΞ Hβ𝒞.
  pose proof (a_lookeq_generated_ftvar Hlk) as Hftv.
  pose proof ((proj2 a_looksub_lookeq_rename_tvar) _ _ _ _ _ _ Hlk _ α1 Hβ Hα1) as Hr.
  rewrite (@rename_aenv_fresh_eq Ξ α1 β) in Hr by (clear - Hftv HβΞ; fsetdec).
  rewrite (@subst_cstrs_fresh_eq α1 β 𝒞) in Hr by exact Hβ𝒞.
  exact Hr.
Qed.
