(** Frost — declarative-system rule definitions. *)

Require Import List.
Require Import Metalib.Metatheory.

Require Import src.frost.notations.
Require Import src.frost.ltac_utils.

(** ** Plain types under a context. *)
Inductive d_wf_typ : list (atom * dbind) -> typ -> Prop :=
| d_wf_typ__unit : forall dE,
    d_wf_typ dE typ_unit
| d_wf_typ__var : forall dE X,
    binds X dbind_tvar dE ->
    d_wf_typ dE (typ_var_f X)
| d_wf_typ__arrow : forall dE A B,
    d_wf_typ dE A ->
    d_wf_typ dE B ->
    d_wf_typ dE (typ_arrow A B)
| d_wf_typ__all : forall L dE c A,
    (forall X, X `notin` L ->
       d_wf_typ ((X ~ dbind_tvar) ++ dE) (open_typ_wrt_typ A (typ_var_f X))) ->
    d_wf_typ dE (typ_all_col c A).

(** ** Well-formed skeletons. Ψ tracks type variables bound previously in
    this skeleton; cleared at □ and at *.P. We forbid TOPHOLE.HOLE and
    nested TOPHOLE / quantifiers (paper line 1190+). *)
Inductive d_wf_skel :
  list atom -> list (atom * dbind) -> typ -> Prop :=
| d_wf_skel__unit : forall dP dE,
    d_wf_skel dP dE typ_unit
| d_wf_skel__var : forall dP dE X,
    List.In X dP \/ binds X dbind_tvar dE ->
    d_wf_skel dP dE (typ_var_f X)
| d_wf_skel__arrow : forall dP dE P Q,
    d_wf_skel dP dE P ->
    d_wf_skel dP dE Q ->
    d_wf_skel dP dE (typ_arrow P Q)
| d_wf_skel__all : forall L dP dE c P,
    (forall X, X `notin` L ->
       d_wf_skel (X :: dP) dE (open_typ_wrt_typ P (typ_var_f X))) ->
    d_wf_skel dP dE (typ_all_col c P)
| d_wf_skel__hole : forall dP dE,
    d_wf_skel dP dE typ_hole
| d_wf_skel__tophole : forall dP dE P,
    guarded_skel P ->
    d_wf_skel nil dE P ->
    d_wf_skel dP dE (typ_tophole P).

(** ** Well-formedness of tagged types. Each ε must appear exactly once
    (linearity by disjoint append). *)
Inductive d_wf_ttyp :
  list atom -> list (atom * dbind) -> typ -> Prop :=
| d_wf_ttyp__unit : forall dE,
    d_wf_ttyp nil dE typ_unit
| d_wf_ttyp__var : forall dE X,
    binds X dbind_tvar dE ->
    d_wf_ttyp nil dE (typ_var_f X)
| d_wf_ttyp__arrow : forall dD1 dD2 dE A B,
    d_wf_ttyp dD1 dE A ->
    d_wf_ttyp dD2 dE B ->
    list_disjoint dD1 dD2 ->
    d_wf_ttyp (dD1 ++ dD2) dE (typ_arrow A B)
| d_wf_ttyp__all : forall L dD dE ee A,
    (forall X, X `notin` L ->
       d_wf_ttyp dD ((X ~ dbind_tvar) ++ dE) (open_typ_wrt_typ A (typ_var_f X))) ->
    ~ List.In ee dD ->
    d_wf_ttyp (ee :: dD) dE (typ_all_eps ee A).

(** ** Well-formedness of unresolved types. The "potential tag δ" (empty or ε)
    is encoded by two ∀ constructors; Δ tracks only the ε-tagged ones. *)
Inductive d_wf_utyp :
  list atom -> list (atom * dbind) -> typ -> Prop :=
| d_wf_utyp__unit : forall dE,
    d_wf_utyp nil dE typ_unit
| d_wf_utyp__var : forall dE X,
    binds X dbind_tvar dE ->
    d_wf_utyp nil dE (typ_var_f X)
| d_wf_utyp__arrow : forall dD1 dD2 dE A B,
    d_wf_utyp dD1 dE A ->
    d_wf_utyp dD2 dE B ->
    list_disjoint dD1 dD2 ->
    d_wf_utyp (dD1 ++ dD2) dE (typ_arrow A B)
| d_wf_utyp__tall : forall L dD dE ee A,
    (forall X, X `notin` L ->
       d_wf_utyp dD ((X ~ dbind_tvar) ++ dE) (open_typ_wrt_typ A (typ_var_f X))) ->
    ~ List.In ee dD ->
    d_wf_utyp (ee :: dD) dE (typ_all_eps ee A)
| d_wf_utyp__pall : forall L dD dE A,
    (forall X, X `notin` L ->
       d_wf_utyp dD ((X ~ dbind_tvar) ++ dE) (open_typ_wrt_typ A (typ_var_f X))) ->
    d_wf_utyp dD dE (typ_all_plain A).

(** ** Tagged skeletons: tagged types + holes/topholes. *)
Inductive d_wf_tskel :
  list atom -> list (atom * dbind) -> typ -> Prop :=
| d_wf_tskel__unit : forall dE,
    d_wf_tskel nil dE typ_unit
| d_wf_tskel__var : forall dE X,
    binds X dbind_tvar dE ->
    d_wf_tskel nil dE (typ_var_f X)
| d_wf_tskel__arrow : forall dD1 dD2 dE psi1 psi2,
    d_wf_tskel dD1 dE psi1 ->
    d_wf_tskel dD2 dE psi2 ->
    list_disjoint dD1 dD2 ->
    d_wf_tskel (dD1 ++ dD2) dE (typ_arrow psi1 psi2)
| d_wf_tskel__all : forall L dD dE ee psi,
    (forall X, X `notin` L ->
       d_wf_tskel dD ((X ~ dbind_tvar) ++ dE)
         (open_typ_wrt_typ psi (typ_var_f X))) ->
    ~ List.In ee dD ->
    d_wf_tskel (ee :: dD) dE (typ_all_eps ee psi)
| d_wf_tskel__hole : forall dE,
    d_wf_tskel nil dE typ_hole
| d_wf_tskel__tophole : forall dD dE psi,
    d_wf_tskel dD dE psi ->
    d_wf_tskel dD dE (typ_tophole psi).

(** ** Unresolved skeletons: unresolved types + holes/topholes. *)
Inductive d_wf_uskel :
  list atom -> list (atom * dbind) -> typ -> Prop :=
| d_wf_uskel__unit : forall dE,
    d_wf_uskel nil dE typ_unit
| d_wf_uskel__var : forall dE X,
    binds X dbind_tvar dE ->
    d_wf_uskel nil dE (typ_var_f X)
| d_wf_uskel__arrow : forall dD1 dD2 dE SS1 SS2,
    d_wf_uskel dD1 dE SS1 ->
    d_wf_uskel dD2 dE SS2 ->
    list_disjoint dD1 dD2 ->
    d_wf_uskel (dD1 ++ dD2) dE (typ_arrow SS1 SS2)
| d_wf_uskel__tall : forall L dD dE ee SS,
    (forall X, X `notin` L ->
       d_wf_uskel dD ((X ~ dbind_tvar) ++ dE)
         (open_typ_wrt_typ SS (typ_var_f X))) ->
    ~ List.In ee dD ->
    d_wf_uskel (ee :: dD) dE (typ_all_eps ee SS)
| d_wf_uskel__pall : forall L dD dE SS,
    (forall X, X `notin` L ->
       d_wf_uskel dD ((X ~ dbind_tvar) ++ dE)
         (open_typ_wrt_typ SS (typ_var_f X))) ->
    d_wf_uskel dD dE (typ_all_plain SS)
| d_wf_uskel__hole : forall dE,
    d_wf_uskel nil dE typ_hole
| d_wf_uskel__tophole : forall dD dE SS,
    d_wf_uskel dD dE SS ->
    d_wf_uskel dD dE (typ_tophole SS).

(** ** Type consistency Δ | Γ ⊢ T ~ A.
    T is is_utyp; A is is_typ; tags in T marked by Δ are "solved" by this
    judgement. *)
Inductive d_consis :
  list atom -> list (atom * dbind) -> typ -> typ -> Prop :=
| d_consis__unit : forall dE,
    d_consis nil dE typ_unit typ_unit
| d_consis__var : forall dE X,
    d_consis nil dE (typ_var_f X) (typ_var_f X)
(* ForallInh: tagged on left, ε added to Δ. *)
| d_consis__forall_inh_tagged : forall L dD dE ee T A,
    (forall X, X `notin` L ->
       d_consis dD ((X ~ dbind_tvar) ++ dE)
         (open_typ_wrt_typ T (typ_var_f X))
         (open_typ_wrt_typ A (typ_var_f X))) ->
    d_consis (ee :: dD) dE (typ_all_eps ee T) (typ_all_col colour_inh A)
(* ForallInh: untagged on left. *)
| d_consis__forall_inh_untagged : forall L dD dE T A,
    (forall X, X `notin` L ->
       d_consis dD ((X ~ dbind_tvar) ++ dE)
         (open_typ_wrt_typ T (typ_var_f X))
         (open_typ_wrt_typ A (typ_var_f X))) ->
    d_consis dD dE (typ_all_plain T) (typ_all_col colour_inh A)
(* ForallSyn: tag NOT solved when RHS is synthesised. *)
| d_consis__forall_syn_tagged : forall L dD dE ee T A,
    (forall X, X `notin` L ->
       d_consis dD ((X ~ dbind_tvar) ++ dE)
         (open_typ_wrt_typ T (typ_var_f X))
         (open_typ_wrt_typ A (typ_var_f X))) ->
    d_consis dD dE (typ_all_eps ee T) (typ_all_col colour_syn A)
| d_consis__forall_syn_untagged : forall L dD dE T A,
    (forall X, X `notin` L ->
       d_consis dD ((X ~ dbind_tvar) ++ dE)
         (open_typ_wrt_typ T (typ_var_f X))
         (open_typ_wrt_typ A (typ_var_f X))) ->
    d_consis dD dE (typ_all_plain T) (typ_all_col colour_syn A)
| d_consis__arrow : forall dD1 dD2 dE T1 T2 A1 A2,
    d_consis dD1 dE T1 A1 ->
    d_consis dD2 dE T2 A2 ->
    list_disjoint dD1 dD2 ->
    d_consis (dD1 ++ dD2) dE (typ_arrow T1 T2) (typ_arrow A1 A2).

(** ** Type subtyping Γ ⊢_M^Δ T ≤ A. *)
Inductive d_sub :
  mode -> list atom -> list (atom * dbind) -> typ -> typ -> Prop :=
| d_sub__infer : forall dE T A,
    is_syn_typ A ->
    d_consis nil dE T A ->
    d_sub mode_ti nil dE T A
| d_sub__check : forall dD dE T A,
    (* T must be guarded — encoded as: not a top-level ∀ of any flavour.
       The forall_l_* rules consume the tagged/plain ∀ cases on the left. *)
    (forall ee T', T <> typ_all_eps ee T') ->
    (forall T', T <> typ_all_plain T') ->
    is_inh_typ A ->
    d_consis dD dE T A ->
    d_sub mode_tc dD dE T A
| d_sub__forall_r : forall L dD dE T A,
    (forall X, X `notin` L ->
       d_sub mode_tc dD ((X ~ dbind_tvar) ++ dE) T (open_typ_wrt_typ A (typ_var_f X))) ->
    d_sub mode_tc dD dE T (typ_all_col colour_inh A)
| d_sub__arg : forall dD1 dD2 dE m T1 T2 A1 A2,
    d_consis dD1 dE T1 A1 ->
    d_sub m dD2 dE T2 A2 ->
    list_disjoint dD1 dD2 ->
    d_sub (mode_fn m) (dD1 ++ dD2) dE (typ_arrow T1 T2) (typ_arrow A1 A2)
| d_sub__forall_l_tagged : forall dD dD' dE m ee T ph A,
    m <> mode_ti ->
    list_disjoint dD' dD ->
    d_wf_ttyp dD' dE ph ->
    d_sub m (dD ++ dD') dE (open_typ_wrt_typ T ph) A ->
    d_sub m dD dE (typ_all_eps ee T) A
| d_sub__forall_l_untagged : forall dD dD' dE m T ph A,
    m <> mode_ti ->
    list_disjoint dD' dD ->
    d_wf_ttyp dD' dE ph ->
    d_sub m (dD ++ dD') dE (open_typ_wrt_typ T ph) A ->
    d_sub m dD dE (typ_all_plain T) A.

(** ** Shallow polymorphic subtyping (paper line 1062). The Phase 2 target:
    we will prove d_sub TC ε Γ A B → d_shallow_sub Γ A B. *)
Inductive d_shallow_sub :
  list (atom * dbind) -> typ -> typ -> Prop :=
| d_shallow_sub__refl : forall dE A,
    d_shallow_sub dE A A
| d_shallow_sub__forall_r : forall L dE A B c,
    (forall X, X `notin` L ->
       d_shallow_sub ((X ~ dbind_tvar) ++ dE) A
         (open_typ_wrt_typ B (typ_var_f X))) ->
    d_shallow_sub dE A (typ_all_col c B)
| d_shallow_sub__forall_l : forall dE A A' B c,
    d_wf_typ dE A' ->
    d_shallow_sub dE (open_typ_wrt_typ A A') B ->
    d_shallow_sub dE (typ_all_col c A) B.

(** ** Base terms O ::= unit | x | M:A — used in the Sub rule. *)
Inductive is_base_term : exp -> Prop :=
| is_base_term__unit : is_base_term exp_unit
| is_base_term__var  : forall x, is_base_term (exp_var_f x)
| is_base_term__anno : forall e A, is_base_term (exp_anno e A).

(** A typ with no ∀ at any depth (any flavour). Used in d_pat_consis ghost. *)
Inductive no_forall_typ : typ -> Prop :=
| no_forall_typ__unit  : no_forall_typ typ_unit
| no_forall_typ__var   : forall X, no_forall_typ (typ_var_f X)
| no_forall_typ__arrow : forall A B,
    no_forall_typ A -> no_forall_typ B ->
    no_forall_typ (typ_arrow A B)
| no_forall_typ__hole  : no_forall_typ typ_hole
| no_forall_typ__tophole : forall A,
    no_forall_typ A -> no_forall_typ (typ_tophole A).

(** ** Declarative typing Γ ⊢_M e : A.

    Mutual with [d_pat] (pattern-matching judgement), [d_refine_syn],
    [d_refine], [d_pat_consis], and [d_pat_sub]. Only [d_typing] and
    [d_pat] strictly require mutuality (App rule); the rest are bundled
    here for uniformity. *)
Inductive d_typing :
  mode -> list (atom * dbind) -> exp -> typ -> Prop :=
| d_typing__unit : forall dE,
    mode_typ_compat mode_ti typ_unit ->
    d_typing mode_ti dE exp_unit typ_unit
| d_typing__var : forall dE x A,
    binds x (dbind_typ A) dE ->
    d_typing mode_ti dE (exp_var_f x) A
| d_typing__anno : forall dE e A,
    is_inh_typ A ->
    d_typing mode_tc dE e A ->
    d_typing mode_ti dE (exp_anno e A) A
| d_typing__sub : forall dE m e A B,
    is_base_term e ->
    d_typing mode_ti dE e A ->
    d_sub m nil dE A B ->
    d_typing m dE e B
| d_typing__freeze : forall dE e A,
    d_typing mode_ti dE e A ->
    d_typing mode_tc dE (exp_freeze e) A
| d_typing__forall : forall L dE e A,
    is_value e ->
    (forall X, X `notin` L ->
       d_typing mode_tc ((X ~ dbind_tvar) ++ dE) e
         (open_typ_wrt_typ A (typ_var_f X))) ->
    d_typing mode_tc dE e (typ_all_col colour_inh A)
| d_typing__abs : forall L dE m e A B,
    is_inh_typ A ->
    (forall x, x `notin` L ->
       d_typing (decr_mode m) ((x ~ dbind_typ A) ++ dE)
         (open_exp_wrt_exp e (exp_var_f x)) B) ->
    d_typing m dE (exp_abs e) (typ_arrow A B)
| d_typing__abs_anno : forall L dE m e A B,
    (forall x, x `notin` L ->
       d_typing (decr_mode m) ((x ~ dbind_typ A) ++ dE)
         (open_exp_wrt_exp e (exp_var_f x)) B) ->
    d_typing m dE (exp_abs_anno A e) (typ_arrow A B)
| d_typing__app : forall dE m e1 e2 P P' A B,
    d_pat mode_ti dE e2 P ->
    d_refine_syn nil dE P P' ->
    d_typing (mode_fn m) dE e1 (typ_arrow A B) ->
    d_typing mode_tc dE e2 A ->
    d_typing m dE (exp_app e1 e2) B

with d_pat :
  mode -> list (atom * dbind) -> exp -> typ -> Prop :=
| d_pat__unit : forall dE,
    d_pat mode_ti dE exp_unit typ_unit
| d_pat__var : forall dE x P,
    binds x (dbind_skel P) dE ->
    d_pat mode_ti dE (exp_var_f x) P
| d_pat__anno : forall dE m e A,
    d_pat m dE (exp_anno e A) A
| d_pat__sub : forall dE m e P Q,
    is_base_term e ->
    d_pat mode_ti dE e P ->
    d_pat_sub m nil dE P Q ->
    d_pat m dE e Q
| d_pat__freeze : forall dE e P,
    d_pat mode_ti dE e P ->
    d_pat mode_tc dE (exp_freeze e) P
| d_pat__abs : forall L dE m e P Q,
    m <> mode_tc ->
    is_inh_skel P ->
    (forall x, x `notin` L ->
       d_pat (decr_mode m) ((x ~ dbind_skel P) ++ dE)
         (open_exp_wrt_exp e (exp_var_f x)) Q) ->
    d_pat m dE (exp_abs e) (typ_arrow P Q)
| d_pat__abs_check : forall L dE e Q,
    (forall x, x `notin` L ->
       d_pat mode_ti ((x ~ dbind_skel typ_hole) ++ dE)
         (open_exp_wrt_exp e (exp_var_f x)) Q) ->
    d_pat mode_tc dE (exp_abs e) (typ_arrow (typ_tophole typ_hole) Q)
| d_pat__abs_anno : forall L dE m e A Q,
    m <> mode_tc ->
    (forall x, x `notin` L ->
       d_pat (decr_mode m) ((x ~ dbind_typ A) ++ dE)
         (open_exp_wrt_exp e (exp_var_f x)) Q) ->
    d_pat m dE (exp_abs_anno A e) (typ_arrow A Q)
| d_pat__abs_anno_check : forall L dE e A Q,
    (forall x, x `notin` L ->
       d_pat mode_ti ((x ~ dbind_typ A) ++ dE)
         (open_exp_wrt_exp e (exp_var_f x)) Q) ->
    d_pat mode_tc dE (exp_abs_anno A e) (typ_arrow (typ_tophole A) Q)
| d_pat__app : forall dE m e1 e2 P P' Q,
    d_pat mode_ti dE e2 P ->
    d_refine_syn nil dE P P' ->
    d_typing (mode_fn m) dE e1 (typ_arrow P' Q) ->
    d_pat m dE (exp_app e1 e2) Q

with d_refine_syn :
  list atom -> list (atom * dbind) -> typ -> typ -> Prop :=
| d_refine_syn__unit : forall dP dE,
    d_refine_syn dP dE typ_unit typ_unit
| d_refine_syn__var : forall dP dE X,
    List.In X dP \/ binds X dbind_tvar dE ->
    d_refine_syn dP dE (typ_var_f X) (typ_var_f X)
| d_refine_syn__arrow : forall dP dE P1 P2 Q1 Q2,
    d_refine_syn dP dE P1 Q1 ->
    d_refine_syn dP dE P2 Q2 ->
    d_refine_syn dP dE (typ_arrow P1 P2) (typ_arrow Q1 Q2)
| d_refine_syn__all_inh : forall L dP dE P Q,
    (forall X, X `notin` L ->
       d_refine_syn (X :: dP) dE
         (open_typ_wrt_typ P (typ_var_f X))
         (open_typ_wrt_typ Q (typ_var_f X))) ->
    d_refine_syn dP dE (typ_all_col colour_inh P) (typ_all_col colour_inh Q)
| d_refine_syn__hole : forall dP dE Q,
    is_syn_skel Q ->
    d_wf_skel dP dE Q ->
    d_refine_syn dP dE typ_hole Q
| d_refine_syn__tophole_no_top : forall L dP dE P Q,
    (forall X, X `notin` L ->
       d_refine_syn (X :: dP) dE P (open_typ_wrt_typ Q (typ_var_f X))) ->
    d_refine_syn dP dE (typ_tophole P) (typ_all_col colour_syn Q)
| d_refine_syn__tophole_with_top : forall L dP dE P Q,
    guarded_skel Q ->
    d_wf_skel nil dE P ->
    (forall X, X `notin` L ->
       d_refine_syn nil dE P (open_typ_wrt_typ Q (typ_var_f X))) ->
    d_refine_syn dP dE (typ_tophole P)
      (typ_all_col colour_syn (typ_tophole Q))

with d_refine :
  list atom -> list (atom * dbind) -> typ -> typ -> Prop :=
| d_refine__unit : forall dP dE,
    d_refine dP dE typ_unit typ_unit
| d_refine__var : forall dP dE X,
    List.In X dP \/ binds X dbind_tvar dE ->
    d_refine dP dE (typ_var_f X) (typ_var_f X)
| d_refine__arrow : forall dP dE P1 P2 Q1 Q2,
    d_refine dP dE P1 Q1 ->
    d_refine dP dE P2 Q2 ->
    d_refine dP dE (typ_arrow P1 P2) (typ_arrow Q1 Q2)
| d_refine__all : forall L dP dE c P Q,
    (forall X, X `notin` L ->
       d_refine (X :: dP) dE
         (open_typ_wrt_typ P (typ_var_f X))
         (open_typ_wrt_typ Q (typ_var_f X))) ->
    d_refine dP dE (typ_all_col c P) (typ_all_col c Q)
| d_refine__hole : forall dP dE Q,
    d_wf_skel nil dE Q ->
    d_refine dP dE typ_hole Q
| d_refine__tophole_no_top : forall L dP dE P Q,
    (forall X, X `notin` L ->
       d_refine (X :: dP) dE P (open_typ_wrt_typ Q (typ_var_f X))) ->
    d_refine dP dE (typ_tophole P) (typ_all_col colour_inh Q)
| d_refine__tophole_with_top : forall L dP dE P Q,
    guarded_skel Q ->
    d_wf_skel nil dE P ->
    (forall X, X `notin` L ->
       d_refine nil dE P (open_typ_wrt_typ Q (typ_var_f X))) ->
    d_refine dP dE (typ_tophole P)
      (typ_all_col colour_inh (typ_tophole Q))

with d_pat_consis :
  list atom -> list (atom * dbind) -> typ -> typ -> Prop :=
| d_pat_consis__unit : forall dE,
    d_pat_consis nil dE typ_unit typ_unit
| d_pat_consis__var : forall dE X,
    d_pat_consis nil dE (typ_var_f X) (typ_var_f X)
| d_pat_consis__forall_inh_tagged : forall L dD dE ee SS P,
    (forall X, X `notin` L ->
       d_pat_consis dD ((X ~ dbind_tvar) ++ dE)
         (open_typ_wrt_typ SS (typ_var_f X))
         (open_typ_wrt_typ P (typ_var_f X))) ->
    d_pat_consis (ee :: dD) dE (typ_all_eps ee SS) (typ_all_col colour_inh P)
| d_pat_consis__forall_inh_untagged : forall L dD dE SS P,
    (forall X, X `notin` L ->
       d_pat_consis dD ((X ~ dbind_tvar) ++ dE)
         (open_typ_wrt_typ SS (typ_var_f X))
         (open_typ_wrt_typ P (typ_var_f X))) ->
    d_pat_consis dD dE (typ_all_plain SS) (typ_all_col colour_inh P)
| d_pat_consis__forall_syn_tagged : forall L dD dE ee SS P,
    (forall X, X `notin` L ->
       d_pat_consis dD ((X ~ dbind_tvar) ++ dE)
         (open_typ_wrt_typ SS (typ_var_f X))
         (open_typ_wrt_typ P (typ_var_f X))) ->
    d_pat_consis dD dE (typ_all_eps ee SS) (typ_all_col colour_syn P)
| d_pat_consis__forall_syn_untagged : forall L dD dE SS P,
    (forall X, X `notin` L ->
       d_pat_consis dD ((X ~ dbind_tvar) ++ dE)
         (open_typ_wrt_typ SS (typ_var_f X))
         (open_typ_wrt_typ P (typ_var_f X))) ->
    d_pat_consis dD dE (typ_all_plain SS) (typ_all_col colour_syn P)
| d_pat_consis__ghost : forall dE P,
    no_forall_typ P ->
    d_pat_consis nil dE typ_hole P
| d_pat_consis__arrow : forall dD1 dD2 dE SS1 SS2 P1 P2,
    d_pat_consis dD1 dE SS1 P1 ->
    d_pat_consis dD2 dE SS2 P2 ->
    list_disjoint dD1 dD2 ->
    d_pat_consis (dD1 ++ dD2) dE (typ_arrow SS1 SS2) (typ_arrow P1 P2)
| d_pat_consis__univ_ghost_arr : forall dD dE SS P,
    d_pat_consis dD dE SS P ->
    d_pat_consis dD dE (typ_tophole SS) (typ_tophole P)
| d_pat_consis__univ_ghost_inh1 : forall L dD dE SS P,
    (forall X, X `notin` L ->
       d_pat_consis dD ((X ~ dbind_tvar) ++ dE)
         (typ_tophole SS) (open_typ_wrt_typ P (typ_var_f X))) ->
    d_pat_consis dD dE (typ_tophole SS) (typ_all_col colour_inh P)
| d_pat_consis__univ_ghost_pass : forall dD dE SS P,
    d_pat_consis dD dE SS P ->
    d_pat_consis dD dE (typ_tophole SS) P

with d_pat_sub :
  mode -> list atom -> list (atom * dbind) -> typ -> typ -> Prop :=
| d_pat_sub__infer : forall dE SS P,
    is_syn_skel P ->
    d_pat_consis nil dE SS P ->
    d_pat_sub mode_ti nil dE SS P
| d_pat_sub__univ_ghost_r : forall dE SS P,
    (forall ee SS', SS <> typ_all_eps ee SS') ->
    (forall SS', SS <> typ_all_plain SS') ->
    (forall SS', SS <> typ_tophole SS') ->
    SS <> typ_hole ->
    is_syn_skel P ->
    d_pat_consis nil dE SS P ->
    d_pat_sub mode_tc nil dE SS (typ_tophole P)
| d_pat_sub__ghost : forall dE m P,
    no_forall_typ P ->
    d_pat_sub (mode_fn m) nil dE typ_hole P
| d_pat_sub__univ_ghost_l : forall dD dE m SS P,
    m <> mode_ti ->
    d_pat_sub m dD dE SS P ->
    d_pat_sub m dD dE (typ_tophole SS) P
| d_pat_sub__arg : forall dD1 dD2 dE m SS1 SS2 P1 P2,
    d_pat_consis dD1 dE SS1 P1 ->
    d_pat_sub m dD2 dE SS2 P2 ->
    list_disjoint dD1 dD2 ->
    d_pat_sub (mode_fn m) (dD1 ++ dD2) dE (typ_arrow SS1 SS2) (typ_arrow P1 P2)
| d_pat_sub__forall_l_tagged : forall dD dD' dE m ee SS psi P,
    m <> mode_ti ->
    list_disjoint dD' dD ->
    d_wf_tskel dD' dE psi ->
    d_pat_sub m (dD ++ dD') dE (open_typ_wrt_typ SS psi) P ->
    d_pat_sub m dD dE (typ_all_eps ee SS) P
| d_pat_sub__forall_l_untagged : forall dD dD' dE m SS psi P,
    m <> mode_ti ->
    list_disjoint dD' dD ->
    d_wf_tskel dD' dE psi ->
    d_pat_sub m (dD ++ dD') dE (open_typ_wrt_typ SS psi) P ->
    d_pat_sub m dD dE (typ_all_plain SS) P
.
