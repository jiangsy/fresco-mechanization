(** Failable-bind combinators for extraction, in a (pseudo-)monadic style.

    ⭐ COPIED, NOT REINVENTED, from McTT's
    [theories/Extraction/PseudoMonadic.v] (~/Documents/HKU/Research/mctt_ref).
    The hand-off's §7.2 says to take it as-is, and the reason is in its own
    header, reproduced below: a chain of failable decisions written with these
    binders extracts as plain nested [match]es, whereas the same chain written
    by hand extracts as a tower of [left]/[right] plumbing that no reader
    would diff against [type.ml].

    ⚠️ THIS CANNOT BE A TYPE CLASS, and the reason is a Coq limitation rather
    than a stylistic choice: there is no extractable polymorphism across
    [Prop] and [Set] (Coq issue #19452).  So the four combinators below are
    the four sort combinations, spelled out.  Do not try to tidy them into
    one — that is the trap this note exists to save.

    ⚙ WHY IT IS HERE BEFORE ITS CONSUMER.  M1.7's runner
    ([def_guess_impl.v]) is TOTAL, so it never fails and needs none of this.
    The judgements that scale next — [assign] / [unifyvar] / [consistency],
    and then [a_sub] — DO fail, and their runners will return [sumor]s.
    Landing the helper now keeps that step from starting with a detour. *)

From Coq Require Extraction.

Definition sumbool_failable_bind {A B} (ab : {A} + {B}) {C D : Prop}
    (fail : B -> D) (next : A -> {C} + {D}) :=
  match ab with
  | left a => next a
  | right b => right (fail b)
  end.
Transparent sumbool_failable_bind.
Arguments sumbool_failable_bind /.

Notation "'let*b' a ':=' ab 'while' fail 'in' next" :=
  (sumbool_failable_bind ab fail (fun a => next))
  (at level 0, a pattern, next at level 10, right associativity, only parsing).
Notation "'pureb' a" := (left a) (at level 0, only parsing).

Definition sumor_failable_bind {A B} (ab : A + {B}) {C} {D : Prop}
    (fail : B -> D) (next : A -> C + {D}) :=
  match ab with
  | inleft a => next a
  | inright b => inright (fail b)
  end.
Transparent sumor_failable_bind.
Arguments sumor_failable_bind /.

Notation "'let*o' a ':=' ab 'while' fail 'in' next" :=
  (sumor_failable_bind ab fail (fun a => next))
  (at level 0, a pattern, next at level 10, right associativity, only parsing).
Notation "'pureo' a" := (inleft a) (at level 0, only parsing).

Definition sumbool_sumor_failable_bind {A B} (ab : {A} + {B}) {C} {D : Prop}
    (fail : B -> D) (next : A -> C + {D}) :=
  match ab with
  | left a => next a
  | right b => inright (fail b)
  end.
Transparent sumbool_sumor_failable_bind.
Arguments sumbool_sumor_failable_bind /.

Notation "'let*b->o' a ':=' ab 'while' fail 'in' next" :=
  (sumbool_sumor_failable_bind ab fail (fun a => next))
  (at level 0, a pattern, next at level 10, right associativity, only parsing).

Definition sumor_sumbool_failable_bind {A B} (ab : A + {B}) {C} {D : Prop}
    (fail : B -> D) (next : A -> {C} + {D}) :=
  match ab with
  | inleft a => next a
  | inright b => right (fail b)
  end.
Transparent sumor_sumbool_failable_bind.
Arguments sumor_sumbool_failable_bind /.

Notation "'let*o->b' a ':=' ab 'while' fail 'in' next" :=
  (sumor_sumbool_failable_bind ab fail (fun a => next))
  (at level 0, a pattern, next at level 10, right associativity, only parsing).

Extraction Inline sumbool_failable_bind sumor_failable_bind
  sumbool_sumor_failable_bind sumor_sumbool_failable_bind.
