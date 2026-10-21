import PPAC.Migration.Internal.FormulaCodeConstruct

/-! 合法子式条件实际推出全部原输入自然守卫；量词不假定外部标准后继。 -/
namespace PPAC.Migration.Internal.FormulaCodeConstructInputs
open Source SourceAlgebra SourceLogic OmegaSyntax FormulaCodeSyntax FormulaCodeRecursiveSyntax

theorem advanced_natural {m} {Γ : Context m} (w x b f : Fin m)
    (ha : Derives Γ (advancedCode w x b f)) : Derives Γ (.mem x w) := by
  let K := (successor (Fin.last m) b.castSucc).conj (formulaCode w.castSucc x.castSucc (Fin.last m) f.castSucc)
  let Δ := Context.add K (Context.image Formula.raise Γ)
  apply Derives.exE (p := K) ha
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  exact .conjL (FormulaCodeProperties.guards w.castSucc x.castSucc (Fin.last m) f.castSucc (.conjR hK))

theorem step_natural {m} {Γ : Context m} (advance : Bool) (w x b f : Fin m)
    (ha : Derives Γ (stepCheck advance w x b f)) : Derives Γ (.mem x w) := by
  cases advance
  · exact .conjL (FormulaCodeProperties.guards w x b f ha)
  · exact advanced_natural w x b f ha
end PPAC.Migration.Internal.FormulaCodeConstructInputs
