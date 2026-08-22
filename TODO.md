- [ ] finish extraction soundness
- [ ] finish extraction completeness
- [ ] clean over-designed proof path
- [ ] uniform statment about rename and swap
- [ ] build time optimization
- [x] define a combined relation for d_consis and join
      (`d_consis_join` / `ad_consis_join`, notation `{{ Ψ ⨟ Γ ⊢ˢ R ∼ᵣ Q }}d`;
       every consistency premise of `d_pat_sub` / `ad_pat_sub` /
       `ad_pat_sub_fuel` is now ONE join premise.  AUDIT ANSWER: at the
       SKELETON sort every join insertion is coupled with a consistency, by
       construction.  At the TYPE sort `d_consis` has no join at all — there
       are no ghosts there — and `d_consis_join_ty` (algo_decl/prop_conserv.v)
       is the one place a join is MANUFACTURED, by reflexivity of refinement.)
- [ ] frontend (mctt like)