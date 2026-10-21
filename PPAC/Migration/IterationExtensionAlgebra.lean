import PPAC.Migration.FiniteIterationSyntax

/-! 在后继端点插入下一并集值时，全部旧/新边组合仍满足递推规律。 -/
namespace PPAC.Migration.IterationExtensionAlgebra
open Source SourceAlgebra SourceLogic OmegaSyntax OmegaStructureSyntax GraphSyntax InsertSyntax IterationSyntax

theorem successor_subst_target {m} {Γ : Context m} (k s j : Fin m)
    (he : Derives Γ (.equal k s)) (hs : Derives Γ (successor k j)) : Derives Γ (successor s j) := by
  have hi : Derives Γ ((successor (Fin.last m) j.castSucc).instantiate k) := by
    simpa only [Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hs
  have h := Derives.eqSubst (successor (Fin.last m) j.castSucc) he hi
  simpa only [Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h

theorem union_subst_target {m} {Γ : Context m} (v t r : Fin m)
    (he : Derives Γ (.equal v t)) (hv : Derives Γ (unionOf v r)) : Derives Γ (unionOf t r) := by
  have hi : Derives Γ ((unionOf (Fin.last m) r.castSucc).instantiate v) := by
    simpa only [Formula.instantiate, unionOf_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hv
  have h := Derives.eqSubst (unionOf (Fin.last m) r.castSucc) he hi
  simpa only [Formula.instantiate, unionOf_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h

theorem old_to_new {m} {Γ : Context m} (f n s r v j k u t : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f s)) (hn : Derives Γ (transitive n))
    (hno : Derives Γ (Formula.mem n n).neg) (hsn : Derives Γ (successor s n))
    (hr : Derives Γ (edge f n r)) (hv : Derives Γ (unionOf v r))
    (hs : Derives Γ (successor k j)) (hu : Derives Γ (edge f j u))
    (hnew : Derives Γ ((Formula.equal k s).conj (.equal t v))) : Derives Γ (unionOf t u) := by
  have hsj := successor_subst_target k s j (.conjL hnew) hs
  have hnj := OmegaStructureAlgebra.successor_injective s n j hn hno hsn hsj
  have hnu := IterationValues.edge_subst_input f j n u (eq_symm hnj) hu
  have hur := GraphProperties.single_valued f s n u r he hf hnu hr
  have htr := union_subst_target v t r (eq_symm (.conjR hnew)) hv
  exact IterationValues.union_subst_source t r u (eq_symm hur) htr

theorem new_to_old_absurd {m} {Γ : Context m} (f s j k t : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f s)) (ht : Derives Γ (transitive s))
    (hno : Derives Γ (Formula.mem s s).neg) (hjs : Derives Γ (.equal j s))
    (hs : Derives Γ (successor k j)) (hk : Derives Γ (edge f k t)) : Derives Γ .bot := by
  have hks := GraphProperties.domain_of_edge f s k t he hf hk
  have hsk := mem_subst hjs (InsertLogic.new_member k j j hs)
  have hss := Derives.impE (RestrictionSyntax.subset_at k s s (.impE (transitive_at s k ht) hks)) hsk
  exact .impE hno hss

theorem new_to_new_absurd {m} {Γ : Context m} (s j k : Fin m)
    (hno : Derives Γ (Formula.mem s s).neg) (hjs : Derives Γ (.equal j s))
    (hks : Derives Γ (.equal k s)) (hs : Derives Γ (successor k j)) : Derives Γ .bot := by
  have hsk := mem_subst hjs (InsertLogic.new_member k j j hs)
  have hss := UnorderedPairLogic.mem_container_subst k s s hks hsk
  exact .impE hno hss

theorem all_cases {m} {Γ : Context m} (f n s r v j k u t : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f s)) (hnext : Derives Γ (next f))
    (hn : Derives Γ (transitive n)) (ht : Derives Γ (transitive s))
    (hno : Derives Γ (Formula.mem n n).neg) (hsno : Derives Γ (Formula.mem s s).neg)
    (hsn : Derives Γ (successor s n)) (hr : Derives Γ (edge f n r)) (hv : Derives Γ (unionOf v r))
    (hs : Derives Γ (successor k j))
    (hI : Derives Γ ((edge f j u).disj ((Formula.equal j s).conj (.equal u v))))
    (hK : Derives Γ ((edge f k t).disj ((Formula.equal k s).conj (.equal t v)))) : Derives Γ (unionOf t u) := by
  apply Derives.disjE hI
  · apply Derives.disjE (add hK _)
    · exact .impE (.impE (.impE (add (add (next_at f j k u t hnext) _) _) (add (add hs _) _))
        (.hyp (Or.inr (Or.inl rfl)))) (.hyp (Or.inl rfl))
    · exact old_to_new f n s r v j k u t (add (add he _) _) (add (add hf _) _)
        (add (add hn _) _) (add (add hno _) _) (add (add hsn _) _) (add (add hr _) _) (add (add hv _) _)
        (add (add hs _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))
  · apply Derives.disjE (add hK _)
    · exact .botE (new_to_old_absurd f s j k t (add (add he _) _) (add (add hf _) _) (add (add ht _) _)
        (add (add hsno _) _) (.conjL (.hyp (Or.inr (Or.inl rfl)))) (add (add hs _) _) (.hyp (Or.inl rfl)))
    · exact .botE (new_to_new_absurd s j k (add (add hsno _) _) (.conjL (.hyp (Or.inr (Or.inl rfl))))
        (.conjL (.hyp (Or.inl rfl))) (add (add hs _) _))
end PPAC.Migration.IterationExtensionAlgebra
