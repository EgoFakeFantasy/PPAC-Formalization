import PPAC.Migration.PowerValueLogic

/-! 原Replacement对唯一幂集值实际取精确像，不使用Collection或对象AC。 -/
namespace PPAC.Migration.PowerValueCollection
open Source SourceAlgebra SourceLogic GraphSyntax PowerValueSyntax

theorem total_values {m} {Γ : Context m} (h a : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hp : Derives Γ (Source.SetLanguage.powerSet.rename Fin.elim0))
    (hf : Derives Γ (functionOn h a)) :
    Derives Γ (ReplacementPredicates.total matrix (fun _ => h) a) := by
  simp only [ReplacementPredicates.total, matrix_fiber, ReplacementPredicates.paramsUp]
  apply Derives.allI
  have he' : Derives (Context.image Formula.raise Γ) (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc he
  have hp' : Derives (Context.image Formula.raise Γ) (Source.SetLanguage.powerSet.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc hp
  have hf' : Derives (Context.image Formula.raise Γ) (functionOn h.castSucc a.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using Derives.rename Fin.castSucc hf
  apply Derives.impI
  exact PowerValueLogic.fiber_at h.castSucc a.castSucc (Fin.last m) (add he' _) (add hp' _) (add hf' _) (.hyp (Or.inl rfl))

theorem exists_range {m} {Γ : Context m} (h a : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hp : Derives Γ (Source.SetLanguage.powerSet.rename Fin.elim0))
    (hr : Derives Γ ((Source.SetLanguage.replacement matrix).rename Fin.elim0))
    (hf : Derives Γ (functionOn h a)) : Derives Γ (rangeExists a h) := by
  have hi := Derives.impE (IterationValueCollection.replacement_instance matrix (fun _ => h) a hr) (total_values h a he hp hf)
  simpa only [ReplacementPredicates.imageExists, matrix_range, rangeExists] using hi

theorem range_unique {m} {Γ : Context m} (c d a h : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hc : Derives Γ (range c a h)) (hd : Derives Γ (range d a h)) : Derives Γ (.equal c d) := by
  apply Derives.impE (PairSyntax.extensionality_instance c d he)
  apply Derives.allI
  have hc' : Derives (Context.image Formula.raise Γ) (range c.castSucc a.castSucc h.castSucc) := by
    simpa only [Formula.raise, range_rename] using Derives.rename Fin.castSucc hc
  have hd' : Derives (Context.image Formula.raise Γ) (range d.castSucc a.castSucc h.castSucc) := by
    simpa only [Formula.raise, range_rename] using Derives.rename Fin.castSucc hd
  have hcz := range_at c.castSucc a.castSucc h.castSucc (Fin.last m) hc'
  have hdz := range_at d.castSucc a.castSucc h.castSucc (Fin.last m) hd'
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (.conjR (add hdz _)) (.impE (.conjL (add hcz _)) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (.conjR (add hcz _)) (.impE (.conjL (add hdz _)) (.hyp (Or.inl rfl)))
end PPAC.Migration.PowerValueCollection
