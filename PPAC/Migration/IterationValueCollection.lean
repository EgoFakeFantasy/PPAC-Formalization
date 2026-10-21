import PPAC.Migration.IterationValueUniqueness
import PPAC.Migration.ReplacementInstances

/-! 用原完整Replacement实际收集全部内部长度的唯一末值，取得精确值域集合。 -/
namespace PPAC.Migration.IterationValueCollection
open Source SourceAlgebra SourceLogic OmegaSyntax IterationValueSyntax

theorem fiber_at {m} {Γ : Context m} (hA : IterationContext.Evidence Γ) (n z a w : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (hn : Derives Γ (.mem n w)) :
    Derives Γ (valueFiber n z a) := by
  have he := IterationValueExistence.exists_at hA n z a w hw hz hn
  let R := value n.castSucc z.castSucc a.castSucc (Fin.last m)
  let Γr := Context.add R (Context.image Formula.raise Γ)
  change Derives Γ (.ex R) at he
  apply Derives.exE (p := R) he
  have hAR := IterationContext.under hA R
  have hwR : Derives Γr (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw R
  have hzR : Derives Γr (empty z.castSucc) := by
    simpa only [Formula.raise, empty_rename] using under hz R
  have hnR : Derives Γr (.mem n.castSucc w.castSucc) := under hn R
  have hR : Derives Γr R := .hyp (Or.inl rfl)
  have hu := IterationValueUniqueness.unique_formula hAR n.castSucc z.castSucc a.castSucc w.castSucc (Fin.last m) hwR hzR hnR hR
  have hr : Derives Γr (valueFiber n.castSucc z.castSucc a.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, Formula.rename, value_rename, uniqueValue_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hR hu
  simpa only [Formula.raise, valueFiber_rename] using hr

theorem total_values {m} {Γ : Context m} (hA : IterationContext.Evidence Γ) (z a w : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ (ReplacementPredicates.total matrix (Source.SetLanguage.args2 z a) w) := by
  simp only [ReplacementPredicates.total, matrix_fiber, ReplacementPredicates.paramsUp, PairSyntax.args2_first, PairSyntax.args2_second]
  apply Derives.allI
  have hA' := IterationContext.rename hA Fin.castSucc
  have hw' : Derives (Context.image Formula.raise Γ) (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hw
  have hz' : Derives (Context.image Formula.raise Γ) (empty z.castSucc) := by
    simpa only [Formula.raise, empty_rename] using Derives.rename Fin.castSucc hz
  apply Derives.impI
  exact fiber_at (IterationContext.add hA' _) (Fin.last m) z.castSucc a.castSucc w.castSucc (add hw' _) (add hz' _) (.hyp (Or.inl rfl))

theorem replacement_instance {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w : Fin m)
    (h : Derives Γ ((Source.SetLanguage.replacement p).rename Fin.elim0)) :
    Derives Γ (ReplacementPredicates.replacementBody p ρ w) := by
  rw [ReplacementInstances.replacement_original] at h
  have hc := specialize_close (.all (ReplacementPredicates.replacementBody p Fin.castSucc (Fin.last n))) ρ h
  have hi := Derives.allE w hc
  simpa only [Formula.rename, Formula.instantiate, ReplacementPredicates.replacementBody_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem exists_range {m} {Γ : Context m} (hA : IterationContext.Evidence Γ) (z a w : Fin m)
    (hr : Derives Γ ((Source.SetLanguage.replacement matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) :
    Derives Γ (.ex (range (Fin.last m) w.castSucc z.castSucc a.castSucc)) := by
  have htotal := total_values hA z a w hw hz
  have hi := Derives.impE (replacement_instance matrix (Source.SetLanguage.args2 z a) w hr) htotal
  simpa only [ReplacementPredicates.imageExists, matrix_range, ReplacementPredicates.paramsUp,
    PairSyntax.args2_first, PairSyntax.args2_second] using hi
end PPAC.Migration.IterationValueCollection
