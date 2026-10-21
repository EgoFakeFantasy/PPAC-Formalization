import PPAC.Migration.OrdinalInitialSegment

/-! 任意两个原对象序数的三分支比较；所有集合与极小见证均在对象语言内。 -/
namespace PPAC.Migration.OrdinalComparison
open Source SourceAlgebra SourceLogic RestrictionSyntax OrdinalSyntax OrdinalDifference

def comparison {m} (a b : Fin m) : Formula m :=
  (Formula.equal a b).disj ((Formula.mem a b).disj (.mem b a))

theorem comparison_rename {m k} (a b : Fin m) (ρ : Fin m → Fin k) :
    (comparison a b).rename ρ = comparison (ρ a) (ρ b) := rfl

theorem from_subset {m} {Γ : Context m} (a b : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation outsideMatrix).rename Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hb : Derives Γ (ordinal b))
    (hab : Derives Γ (subset a b)) : Derives Γ (comparison a b) := by
  have hc := OrdinalInitialSegment.initial_segment b a he hf hs hb (.conjL ha) hab
  apply Derives.disjE hc
  · exact .disjL (.hyp (Or.inl rfl))
  · exact .disjR (.disjL (.hyp (Or.inl rfl)))

theorem compare {m} {Γ : Context m} (a b : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation outsideMatrix).rename Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hb : Derives Γ (ordinal b)) : Derives Γ (comparison a b) := by
  apply Derives.classical
  let Δ := Context.add (comparison a b).neg Γ
  have hno : Derives Δ (comparison a b).neg := .hyp (Or.inl rfl)
  have hn : Derives Δ (subset a b).neg := by
    apply Derives.impI
    have hc := from_subset (Γ := Context.add (subset a b) Δ) a b (add (add he _) _) (add (add hf _) _) (add (add hs _) _)
      (add (add ha _) _) (add (add hb _) _) (.hyp (Or.inl rfl))
    exact .impE (add hno _) hc
  have hex := exists_minimal a b (add hs _) (add hf _) (has_of_not_subset a b hn)
  let M := minimal a.castSucc b.castSucc (Fin.last m)
  let Ξ := Context.add M (Context.image Formula.raise Δ)
  apply Derives.exE (p := M) hex
  have he' : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under (add he _) M
  have hf' : Derives Ξ (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under (add hf _) M
  have hs' : Derives Ξ ((Source.SetLanguage.separation outsideMatrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under (add hs _) M
  have ha' : Derives Ξ (ordinal a.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under (add ha _) M
  have hb' : Derives Ξ (ordinal b.castSucc) := by
    simpa only [Formula.raise, ordinal_rename] using under (add hb _) M
  have hno' : Derives Ξ (comparison a.castSucc b.castSucc).neg := by
    simpa only [Formula.raise, Formula.neg, Formula.rename, comparison_rename] using under hno M
  have hm : Derives Ξ M := .hyp (Or.inl rfl)
  have hua : Derives Ξ (.mem (Fin.last m) a.castSucc) := .conjL (.conjL hm)
  have hnu : Derives Ξ (Formula.mem (Fin.last m) b.castSucc).neg := .conjR (.conjL hm)
  have ht := OrdinalTransitivity.member_transitive a.castSucc (Fin.last m) ha' hua
  have hub := minimal_subset a.castSucc b.castSucc (Fin.last m) (.conjL ha') hm
  have hc := OrdinalInitialSegment.initial_segment b.castSucc (Fin.last m) he' hf' hs' hb' ht hub
  apply Derives.disjE hc
  · have hba := mem_subst (Derives.hyp (Γ := Context.add (.equal (Fin.last m) b.castSucc) Ξ) (Or.inl rfl)) (add hua _)
    exact .impE (add hno' _) (.disjR (.disjR hba))
  · exact .impE (add hnu _) (.hyp (Or.inl rfl))

/-- a⊆b当且仅当a=b或a∈b；前向确实调用已证初段定理。 -/
theorem subset_iff {m} {Γ : Context m} (a b : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hs : Derives Γ ((Source.SetLanguage.separation outsideMatrix).rename Fin.elim0))
    (ha : Derives Γ (ordinal a)) (hb : Derives Γ (ordinal b)) :
    Derives Γ ((subset a b).iff ((Formula.equal a b).disj (.mem a b))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact OrdinalInitialSegment.initial_segment b a (add he _) (add hf _) (add hs _) (add hb _) (.conjL (add ha _)) (.hyp (Or.inl rfl))
  · apply Derives.impI
    apply Derives.disjE (Derives.hyp (Or.inl rfl))
    · apply Derives.allI
      let E := (Formula.equal a b).disj (.mem a b)
      let Δ := Context.add (.equal a b) (Context.add E Γ)
      have heq : Derives Δ (.equal a b) := .hyp (Or.inl rfl)
      have heq' := Derives.rename Fin.castSucc heq
      apply Derives.impI
      exact UnorderedPairLogic.mem_container_subst a.castSucc b.castSucc (Fin.last m) (add heq' _) (.hyp (Or.inl rfl))
    · exact OrdinalTransitivity.subset_of_member b a (.conjL (add (add hb _) _)) (.hyp (Or.inl rfl))

/-- 不可能a∈b且b∈a；只用序数传递性与其不自属性质。 -/
theorem asymmetric {m} {Γ : Context m} (a b : Fin m)
    (ha : Derives Γ (ordinal a))
    (hab : Derives Γ (.mem a b)) : Derives Γ (Formula.mem b a).neg := by
  apply Derives.impI
  have haa : Derives (Context.add (.mem b a) Γ) (.mem a a) := Derives.impE (Derives.impE (add (transitiveSet_at a b a (.conjL ha)) _) (.hyp (Or.inl rfl))) (add hab _)
  exact .impE (add (OrdinalEmpty.no_self a (.conjL (.conjR ha))) _) haa
end PPAC.Migration.OrdinalComparison
