import PPAC.Migration.Internal.FormulaCodeCriterionTransfer

/-! 公式码的全候选守卫、非法根/上下文拒绝和实际ω独立性。 -/
namespace PPAC.Migration.Internal.FormulaCodeProperties
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxTermSyntax FormulaCodeSyntax

theorem guards {m} {Γ : Context m} (w n b f : Fin m) (ht : Derives Γ (formulaCode w n b f)) :
    Derives Γ ((Formula.mem n w).conj (contexts w b f)) := by
  apply eliminate_code w n b f _ ht
  have hB : Derives (Context.add (body w n b f)
      (Context.image Formula.raise (Context.image Formula.raise Γ))) (body w n b f) := .hyp (Or.inl rfl)
  exact .conjI (.conjL (.conjR hB)) (.conjL (.conjR (.conjR hB)))

theorem reject_code {m} {Γ : Context m} (w n b f : Fin m) (hn : Derives Γ (Formula.mem n w).neg) :
    Derives Γ (formulaCode w n b f).neg := by
  apply Derives.impI
  exact .impE (add hn _) (.conjL (guards w n b f (.hyp (Or.inl rfl))))

theorem reject_context {m} {Γ : Context m} (w n b f : Fin m) (hc : Derives Γ (contexts w b f).neg) :
    Derives Γ (formulaCode w n b f).neg := by
  apply Derives.impI
  exact .impE (add hc _) (.conjR (guards w n b f (.hyp (Or.inl rfl))))

theorem omega_independent {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w v n b f : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (omega v)) :
    Derives Γ ((formulaCode w n b f).iff (formulaCode v n b f)) := by
  have he := OmegaAlgebra.unique w v (ZFContext.arithmetic hZ).base.extensionality hw hv
  apply Derives.conjI
  · apply Derives.impI
    exact FormulaCodeTransport.code_omega w n b f v (add he _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact FormulaCodeTransport.code_omega v n b f w (add (eq_symm he) _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.FormulaCodeProperties
