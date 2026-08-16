(** PROBE (2026-08-16): [a_sub] REJECTS the buried-∀-pattern configuration —
    every derivation, every collection order — settling §8c.8's open question
    on the mech side (docs/HANDOFF-extractable-algo-encoding.md §8c.8/§8c.9).

    THE CONFIGURATION.  The reference implementation rejects

        val f : forall a . forall d . []( unit -> (forall e . a) )
        val h : []( (forall b . b) -> unit )
        val u : unit          let test = h (f u)

    at SI-ForallL's own wf premise (type.ml:961), after the look leaked the
    pattern's ∀-binder into the solved instantiation.  In the mech's fragment
    (no [TMod]; the impl's [] is an effect-modality its collection treats as
    transparent, type.ml:690-693), the corresponding [a_sub] node is
    AT-App's function premise inside the argument's SECOND (typing) pass:

        subject  ⌈∀a.∀d.(1 → ∀e.a)⌉   ([probe_root])
        pattern  ⫯1 → ⌈∀b.b⌉          ([probe_pat] — AT-App premise 3 paints
                                        the inferred domain RIGIDLY)
        at [ TY | FN TC ].

    WHAT IS PROVED ([probe_buried_forall_sub_reject]): this node has NO
    [a_sub] derivation, over ANY context.  The mechanism, machine-checked
    branch by branch: ForallL is the only applicable row; its extract's
    collection has exactly the ForallR-first/ForallL-first choice of
    cex/cex_looksub_not_det.v ([ ≼TC β ] leaked vs [ ≼TC ∀b.b ] closed), and
    BOTH fold to the same shape — a ghost-guarded LEAKED opener [⫯β] — because
    at [◇ ≼TC ∀B] only SS-ForallR applies (∀ is not guarded, so SS-GhostL and
    SS-Check are out), and SS-ForallR does not close (leak BY DESIGN,
    algo/def_rules.v:614-640).  [guess^TY] then returns the bare [β], and
    ForallL's disciplined-wf premise [{{ Θ0 ⨟ empty ⊢ₚₛ P1 }}a] has no rule
    for an unbound variable.

    So the collection ORDER is not where anything is lost (the two orders'
    folds agree up to the fresh opener — the §8c.8/(b) invariant, exhibited
    here on the live configuration), and the runner's ForallR-first commit is
    complete AT THIS NODE: there is no [a_sub] derivation to miss.

    ⚙ CONSEQUENCE FOR [a_sub_complete] (checked against its statement, not
    re-proved): its conclusion would CONSTRUCT this derivation, so its
    declarative premise must fail — for every κ-increase Θ and every [Q]
    refining the pattern, [{{ empty ⨟ Θ ⊢ˢ[ TY | FN TC ] R' ⩽ Q }}ad] is
    underivable.  The blocking mechanism (read off the rules, not
    machine-checked): [a_tags_sort] forces every quantifier of a ForallL
    instantiation to be TAGGED, the consistency leaves demand [Ψ [=] empty],
    and the only Ψ-consuming row is [ad_pat_consis__forall_inh_tagged] —
    a tagged ∀ must meet an inh-∀ of the target inside a consistency premise.
    Here the target's only inh-∀ sits at a TC position, where ForallR peels
    it into a rigid binder before any consistency fires (and Check refuses
    unguarded subjects), so the impredicative instantiation [a ≔ ∀b.b] can
    never discharge its tag.  The declarative system rejects the program too:
    impl, algorithm and spec all agree, and the pre-instantiated variant
    (val f3 : forall d . []( unit -> forall e . forall b . b )) is accepted
    precisely because a DECLARED ∀ is untagged. *)

Require Import Coq.Lists.List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.def_shapes.
Require Import src.frost.algo.def_rules.
Require Import src.frost.algo.prop_basic.

Open Scope frost_a_scope.

(** ⌈∀a.∀d.(1 → ∀e.a)⌉ — the subject, closed. *)
Definition probe_root : pskl :=
  pskl_all_syn (pskl_all_syn (pskl_arrow pskl_unit (pskl_all_syn (pskl_var_b 2)))).

(** The subject after ForallL opens [a] at the flexible [α]:
    ∀_.(1 → ∀_.α), both remaining binders vacuous. *)
Definition probe_subj (α : atom) : pskl :=
  pskl_all_syn (pskl_arrow pskl_unit (pskl_all_syn (pskl_var_f α))).

(** ⌈∀b.b⌉ — the pattern's codomain: AT-App premise 3's rigid painting of
    the inferred domain of [h]. *)
Definition probe_tgt : pskl := pskl_all_syn (pskl_var_b 0).

(** ⫯1 → ⌈∀b.b⌉ — the pattern at [f]: the argument [u]'s skeleton, then the
    rigid codomain. *)
Definition probe_pat : pskl :=
  pskl_arrow (pskl_tophole pskl_unit) probe_tgt.

(* ===================================================================== *)
(*  §1  The COLLECTION, inverted layer by layer.                          *)
(* ===================================================================== *)

(** The arrow's eq half collects nothing: [1 ∼[α] ⫯1] has no occurrence of
    α on either side. *)
Lemma probe_lookeq_unit : forall Θ α Ξ C,
  {{ Θ ⊢ pskl_unit ∼[ α ] (pskl_tophole pskl_unit) ⤳ Ξ ⨾ C }}a ->
  Ξ = nil /\ C = nil.
Proof.
  intros * H.
  inversion H; subst; auto.
  (* LE-UnivGhostR recursed at [1 ∼ 1]: only LE-Absent fits *)
  match goal with
  | Hr : a_lookeq _ _ pskl_unit pskl_unit _ _ |- _ =>
      inversion Hr; subst; auto
  end.
Qed.

(** [α ≼TC β'] emits the current target verbatim (LS-Var; LS-Check is
    excluded by its own [A ≠ α], LS-Absent by occurrence). *)
Lemma probe_looksub_var_var : forall Θ α β' Ξ C,
  {{ Θ ⊢ (pskl_var_f α) ≼[ α , mode_tc ] (pskl_var_f β') ⤳ Ξ ⨾ C }}a ->
  Ξ = nil /\ C = a_cstr_sub mode_tc (pskl_var_f β') :: nil.
Proof.
  intros * H.
  inversion H; subst; auto.
  - (* LS-Absent: α ∉ ftv α *)
    exfalso. simpl in *. fsetdec.
  - (* LS-Check: A ≠ α with A = α *)
    congruence.
Qed.

(** [α ≼TC ∀b.b]: LS-Var reads the WHOLE ∀ target (closed), or LS-ForallR
    peels it first and LS-Var then reads the LEAKED opener. *)
Lemma probe_looksub_var_tgt : forall Θ α Ξ C,
  {{ Θ ⊢ (pskl_var_f α) ≼[ α , mode_tc ] probe_tgt ⤳ Ξ ⨾ C }}a ->
  Ξ = nil /\
  (C = a_cstr_sub mode_tc probe_tgt :: nil \/
   exists β, C = a_cstr_sub mode_tc (pskl_var_f β) :: nil /\
             β `notin` ftvar_in_aenv Θ).
Proof.
  intros * H.
  unfold probe_tgt in *.
  inversion H; subst.
  - (* LS-Var *)
    split; [ reflexivity | left; reflexivity ].
  - (* LS-Absent *)
    exfalso. simpl in *. fsetdec.
  - (* LS-Check: A = α excluded *)
    congruence.
  - (* LS-ForallR: opener β leaks into the emitted constraint *)
    match goal with
    | Hf : ?b `notin` add α _ ,
      Hr : a_looksub ((?b ~ abind_tvar) ++ _) _ _ (pskl_var_f _) _ _ _ |- _ =>
        unfold open_pskl_wrt_pskl in Hr; simpl in Hr;
        apply probe_looksub_var_var in Hr as [HΞ HC]; subst;
        split; [ reflexivity | right; exists b ];
        split; [ reflexivity | clear - Hf; fsetdec ]
    end.
Qed.

(** [∀_.α ≼TC β']: the ∀-stack peels (LS-ForallL) and LS-Var reads β'. *)
Lemma probe_looksub_stack_var : forall Θ α β' Ξ C,
  {{ Θ ⊢ (pskl_all_syn (pskl_var_f α)) ≼[ α , mode_tc ] (pskl_var_f β')
      ⤳ Ξ ⨾ C }}a ->
  Ξ = nil /\ C = a_cstr_sub mode_tc (pskl_var_f β') :: nil.
Proof.
  intros * H.
  inversion H; subst.
  - (* LS-Absent *)
    exfalso. simpl in *. fsetdec.
  - (* LS-Check: guarded ∀ has no constructor *)
    match goal with
    | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
    end.
  - (* LS-ForallL *)
    match goal with
    | Hr : a_looksub ((_ ~ abind_tvar) ++ _) _ _ _ _ _ _ |- _ =>
        unfold open_pskl_wrt_pskl in Hr; simpl in Hr;
        apply probe_looksub_var_var in Hr as [HΞ HC]; subst; auto
    end.
Qed.

(** The crossing (cex_looksub_not_det.v's configuration, live inside this
    node): [∀_.α ≼TC ∀b.b] collects the closed [ ≼TC ∀b.b ] (ForallL first)
    or a leaked [ ≼TC β ] (any route through LS-ForallR). *)
Lemma probe_looksub_stack_tgt : forall Θ α Ξ C,
  {{ Θ ⊢ (pskl_all_syn (pskl_var_f α)) ≼[ α , mode_tc ] probe_tgt ⤳ Ξ ⨾ C }}a ->
  Ξ = nil /\
  (C = a_cstr_sub mode_tc probe_tgt :: nil \/
   exists β, C = a_cstr_sub mode_tc (pskl_var_f β) :: nil /\
             β `notin` ftvar_in_aenv Θ).
Proof.
  intros * H.
  unfold probe_tgt in *.
  inversion H; subst.
  - (* LS-Absent *)
    exfalso. simpl in *. fsetdec.
  - (* LS-Check: guarded ∀ has no constructor *)
    match goal with
    | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
    end.
  - (* LS-ForallR first: recursion at [∀_.α ≼TC β] *)
    match goal with
    | Hf : ?b `notin` add α _ ,
      Hr : a_looksub ((?b ~ abind_tvar) ++ _) _ _ (pskl_all_syn _) _ _ _ |- _ =>
        unfold open_pskl_wrt_pskl in Hr; simpl in Hr;
        apply probe_looksub_stack_var in Hr as [HΞ HC]; subst;
        split; [ reflexivity | right; exists b ];
        split; [ reflexivity | clear - Hf; fsetdec ]
    end.
  - (* LS-ForallL first: recursion at [α ≼TC ∀b.b] over the extended ctx —
       the subject arrives as an UNREDUCED open, so the pattern stays loose *)
    match goal with
    | Hr : a_looksub ((_ ~ abind_tvar) ++ _) _ _ _ _ _ _ |- _ =>
        unfold open_pskl_wrt_pskl in Hr; simpl in Hr;
        apply probe_looksub_var_tgt in Hr as [HΞ [HC | (β1 & HC & Hβ1)]]; subst
    end.
    + split; [ reflexivity | left; reflexivity ].
    + split; [ reflexivity | right; exists β1 ].
      split; [ reflexivity | simpl in Hβ1; clear - Hβ1; fsetdec ].
Qed.

(** The arrow row: eq half is empty, sub half is the crossing. *)
Lemma probe_looksub_arrow : forall Θ α Ξ C,
  {{ Θ ⊢ (pskl_arrow pskl_unit (pskl_all_syn (pskl_var_f α)))
      ≼[ α , mode_fn mode_tc ] probe_pat ⤳ Ξ ⨾ C }}a ->
  Ξ = nil /\
  (C = a_cstr_sub mode_tc probe_tgt :: nil \/
   exists β, C = a_cstr_sub mode_tc (pskl_var_f β) :: nil /\
             β `notin` ftvar_in_aenv Θ).
Proof.
  intros * H.
  unfold probe_pat in *.
  inversion H; subst.
  - (* LS-Absent *)
    exfalso. simpl in *. fsetdec.
  - (* LS-Arrow *)
    match goal with
    | He : a_lookeq _ _ pskl_unit _ _ _ ,
      Hs : a_looksub _ _ mode_tc _ _ _ _ |- _ =>
        apply probe_lookeq_unit in He as [HΞ1 HC1];
        apply probe_looksub_stack_tgt in Hs as [HΞ2 HC2]; subst
    end.
    simpl. auto.
Qed.

(** The top of the look: ForallL peels the vacuous ∀d and the arrow row
    takes over. *)
Lemma probe_look_top : forall Θ α Ξ C,
  {{ Θ ⊢ (probe_subj α) ≼[ α , mode_fn mode_tc ] probe_pat ⤳ Ξ ⨾ C }}a ->
  Ξ = nil /\
  (C = a_cstr_sub mode_tc probe_tgt :: nil \/
   exists β, C = a_cstr_sub mode_tc (pskl_var_f β) :: nil /\
             β `notin` ftvar_in_aenv Θ).
Proof.
  intros * H.
  unfold probe_subj in *.
  inversion H; subst.
  - (* LS-Absent *)
    exfalso. simpl in *. fsetdec.
  - (* LS-ForallL (the vacuous ∀d) *)
    match goal with
    | Hr : a_looksub ((_ ~ abind_tvar) ++ _) _ _ _ _ _ _ |- _ =>
        unfold open_pskl_wrt_pskl in Hr; simpl in Hr;
        apply probe_looksub_arrow in Hr as [HΞ [HC | (β1 & HC & Hβ1)]]; subst
    end.
    + auto.
    + split; [ reflexivity | right; exists β1 ].
      split; [ reflexivity | simpl in Hβ1; clear - Hβ1; fsetdec ].
Qed.

(* ===================================================================== *)
(*  §2  The FOLD: both collections solve to the SAME shape — a            *)
(*  ghost-guarded LEAKED opener.  (The §8c.8/(b) invariant, live.)        *)
(* ===================================================================== *)

(** [◇ ≼TC β]: only SS-GhostL fits, and it guards the variable. *)
Lemma probe_solve_hole_var : forall Θ β Ξ P',
  {{ Θ ⊢ₛ pskl_hole ≼[ mode_tc ] (pskl_var_f β) ⤳ Ξ ⨾ P' }}a ->
  Ξ = nil /\ P' = pskl_tophole (pskl_var_f β).
Proof.
  intros * H.
  inversion H; subst; auto.
  (* SS-Check: guarded ◇ has no constructor *)
  match goal with
  | Hg : guarded_pskl pskl_hole |- _ => inversion Hg
  end.
Qed.

(** [◇ ≼TC ∀b.b]: only SS-ForallR fits (∀ is not guarded, so SS-GhostL and
    SS-Check are out), it opens the target at a fresh β and does NOT close —
    the yield mentions the leaked β. *)
Lemma probe_solve_hole_tgt : forall Θ Ξ P',
  {{ Θ ⊢ₛ pskl_hole ≼[ mode_tc ] probe_tgt ⤳ Ξ ⨾ P' }}a ->
  Ξ = nil /\
  exists β, P' = pskl_tophole (pskl_var_f β) /\ β `notin` ftvar_in_aenv Θ.
Proof.
  intros * H.
  unfold probe_tgt in *.
  inversion H; subst.
  - (* SS-Check: guarded ◇ *)
    match goal with
    | Hg : guarded_pskl pskl_hole |- _ => inversion Hg
    end.
  - (* SS-ForallR *)
    match goal with
    | Hf : ?b `notin` _ ,
      Hr : a_solve_sub ((?b ~ abind_tvar) ++ _) _ _ _ _ _ |- _ =>
        unfold open_pskl_wrt_pskl in Hr; simpl in Hr;
        apply probe_solve_hole_var in Hr as [HΞ HP]; subst;
        split; [ reflexivity | exists b ];
        split; [ reflexivity | clear - Hf; fsetdec ]
    end.
  - (* SS-GhostL: guarded ∀ *)
    match goal with
    | Hg : guarded_pskl (pskl_all_syn _) |- _ => inversion Hg
    end.
Qed.

(** A singleton sub-constraint folds by exactly its solve step. *)
Lemma probe_fold_sub : forall Θ T Ξs Q,
  {{ Θ ⊩ (a_cstr_sub mode_tc T :: nil) ⨾ pskl_hole ⤳ Ξs ⨾ Q }}a ->
  {{ Θ ⊢ₛ pskl_hole ≼[ mode_tc ] T ⤳ Ξs ⨾ Q }}a.
Proof.
  intros * H.
  inversion H; subst; auto.
Qed.

(** [guess^TY] strips the guard and returns the bare leaked variable. *)
Lemma probe_guess_tophole_var : forall Θ β Ξ Q,
  a_guess Θ a_sub_mode_ty (pskl_tophole (pskl_var_f β)) Ξ Q ->
  Ξ = nil /\ Q = pskl_var_f β.
Proof.
  intros * H.
  inversion H; subst.
  match goal with
  | Hm : a_guess_mono _ (pskl_tophole _) _ _ |- _ =>
      inversion Hm; subst
  end.
  match goal with
  | Hm : a_guess_mono _ (pskl_var_f _) _ _ |- _ =>
      inversion Hm; subst
  end.
  simpl. auto.
Qed.

(* ===================================================================== *)
(*  §3  The EXTRACT: every derivation instantiates with a leaked opener.  *)
(* ===================================================================== *)

Lemma probe_extract_leaks : forall Θ0 α Ξ P1,
  {{ Θ0 ⊢ (probe_subj α) ⊳[ a_sub_mode_ty , α , mode_fn mode_tc ] probe_pat
      ⤳ Ξ ↪ P1 }}a ->
  Ξ = nil /\
  exists β, P1 = pskl_var_f β /\ β `notin` ftvar_in_aenv Θ0.
Proof.
  intros * H.
  inversion H; subst.
  (* rename-first: the match only names the inverted premises (§8c.6 §2c) *)
  match goal with
  | H0 : a_looksub _ _ _ _ _ _ _ |- _ => rename H0 into Hlook
  end.
  match goal with
  | H0 : a_solve_cstr _ _ _ _ _ |- _ => rename H0 into Hfold
  end.
  match goal with
  | H0 : a_guess _ _ _ _ _ |- _ => rename H0 into Hguess
  end.
  apply probe_look_top in Hlook as [HΞ [HC | (β & HC & Hβ)]]; subst;
    simpl in Hfold; apply probe_fold_sub in Hfold.
  - (* closed collection [ ≼TC ∀b.b ]: the SOLVE leaks *)
    apply probe_solve_hole_tgt in Hfold as [HΞs (β & HQ & Hβ)]; subst.
    simpl in Hguess.
    apply probe_guess_tophole_var in Hguess as [HΞ' HQ']; subst.
    split; [ reflexivity | exists β ].
    split; [ reflexivity | exact Hβ ].
  - (* leaked collection [ ≼TC β ]: the solve guards the same β *)
    apply probe_solve_hole_var in Hfold as [HΞs HQ]; subst.
    simpl in Hguess.
    apply probe_guess_tophole_var in Hguess as [HΞ' HQ']; subst.
    split; [ reflexivity | exists β ].
    split; [ reflexivity | exact Hβ ].
Qed.

(* ===================================================================== *)
(*  §4  THE PROBE: no [a_sub] derivation exists at this node.             *)
(* ===================================================================== *)

Theorem probe_buried_forall_sub_reject : forall Θ0 Q Θ1,
  ~ a_sub a_sub_mode_ty (mode_fn mode_tc) probe_pat Θ0 probe_root Q Θ1.
Proof.
  intros Θ0 Q Θ1 H.
  unfold probe_root in H.
  inversion H; subst.
  (* only SI-ForallL survives the shape/mode dispatch *)
  match goal with
  | Hext : a_extract _ _ _ _ _ _ _ _ |- _ =>
      unfold open_pskl_wrt_pskl in Hext; simpl in Hext;
      apply probe_extract_leaks in Hext as [HΞ (β & HP1 & Hβ)]; subst
  end.
  (* the disciplined-wf premise has no rule for the unbound β *)
  match goal with
  | Hwf : a_wf_pskl _ _ (pskl_var_f _) |- _ =>
      simpl in Hwf; inversion Hwf; subst;
      match goal with
      | Hd : _ \/ a_binds_tvar _ _ |- _ =>
          destruct Hd as [Hin | Hb];
          [ clear - Hin; fsetdec
          | pose proof (dom_subset_ftvar_in_aenv Θ0) as Hsub;
            assert (β `in` dom Θ0) as Hdom
              by (destruct Hb as [Hb | [Hb | [τ Hb]]]; eauto using binds_In);
            clear - Hsub Hdom Hβ; fsetdec ]
      end
  end.
Qed.
