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
