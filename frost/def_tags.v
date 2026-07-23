(** Syntactic quantifier tags of an unresolved skeleton.

    The ε tags occurring in a [uskl] ([∀^ε α.ψ] binders).  Tags are plain
    atoms (not a locally-nameless sort), so lngen generates no collector;
    this is the hand-written one.  Kept in its own leaf module (imports
    only the generated syntax) so both the declarative-algorithmic
    definitions and the completeness proof files can use it.

    Used by the completeness track: the paper's ForallL side condition
    [fresh Ψ'] means the instantiation's tags are GLOBALLY fresh — in
    particular fresh from the tags already in the subject — and
    mechanizing that prose-freshness requires a subject's tags
    syntactically (precision-substitution,
    docs/DESIGN-completeness-subtyping.md §5.2). *)

Require Import Metalib.Metatheory.
Require Import src.frost.def_ott.

Fixpoint ftag_in_uskl (R : uskl) : atoms :=
  match R with
  | uskl_unit => {}
  | uskl_var_b _ => {}
  | uskl_var_f _ => {}
  | uskl_arrow R1 R2 => ftag_in_uskl R1 `union` ftag_in_uskl R2
  | uskl_all_syn R0 => ftag_in_uskl R0
  | uskl_all_etag ε R0 => add ε (ftag_in_uskl R0)
  | uskl_hole => {}
  | uskl_tophole R0 => ftag_in_uskl R0
  | uskl_holeg => {}
  | uskl_topholeg R0 => ftag_in_uskl R0
  end.
