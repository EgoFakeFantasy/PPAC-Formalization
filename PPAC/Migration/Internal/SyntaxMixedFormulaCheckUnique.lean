import PPAC.Migration.Internal.SyntaxMixedFormulaFiberUnique
import PPAC.Migration.Internal.SyntaxMixedFormulaAdvancedOutput

/-! 混合量词两张环境码同时提升；目标类型与给定内部Property下的候选唯一性。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaCheckUnique
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMixedFormulaOutputSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem target_type {m} {Γ : Context m} (advance : Bool) (w x r s a b c d q : Fin m)
    (hc : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.check advance w x r s a b c d q)) :
    Derives Γ (FormulaCodeRecursiveSyntax.stepCheck advance w q c d) := by
  cases advance
  · exact SyntaxMixedFormulaJudgment.target_type w r s a b c d x q hc
  · change Derives Γ (FormulaCodeRecursiveSyntax.advancedCode w q c d)
    let B := SyntaxMixedFormulaRecursiveSyntax.advancedBody w x r s a b c d q
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
    apply SyntaxMixedFormulaAdvancedOutput.eliminate_advanced w x r s a b c d q _ hc
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hs := SyntaxCodedMixedBinderTyping.input_of_lifted w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) (.conjL hB)
    have ht := SyntaxMixedFormulaJudgment.target_type w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) (Fin.last m).castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc (.conjR hB)
    have ho := FormulaCodeRecursiveSyntax.intro_advanced w.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (.conjR (.conjR hs)) ht
    exact of_eq (by simp only [Formula.raise, FormulaCodeRecursiveSyntax.advancedCode_rename]) ho

theorem natural {m} {Γ : Context m} (advance : Bool) (w x r s a b c d q : Fin m)
    (hc : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.check advance w x r s a b c d q)) : Derives Γ (.mem q w) := by
  cases advance
  · exact SyntaxMixedFormulaOutput.output_natural w r s a b c d x q hc
  · let B := SyntaxMixedFormulaRecursiveSyntax.advancedBody w x r s a b c d q
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
    apply SyntaxMixedFormulaAdvancedOutput.eliminate_advanced w x r s a b c d q _ hc
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    exact SyntaxMixedFormulaOutput.output_natural w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) (Fin.last m).castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc (.conjR hB)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (advance : Bool) (w x r s a b c d q v : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (property w x))
    (hq : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.check advance w x r s a b c d q))
    (hv : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.check advance w x r s a b c d v)) : Derives Γ (.equal q v) := by
  cases advance
  · exact SyntaxMixedFormulaFiberUnique.property_unique hZ w r s a b c d x q v hw hp hq hv
  · change Derives Γ (SyntaxMixedFormulaRecursiveSyntax.advanced w x r s a b c d v) at hv
    let B := SyntaxMixedFormulaRecursiveSyntax.advancedBody w x r s a b c d q
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
    apply SyntaxMixedFormulaAdvancedOutput.eliminate_advanced w x r s a b c d q _ hq
    have hZ4 := SyntaxRenameBinders.zf_under_4 hZ B
    have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_4 hw B)
    have hp4 : Derives Δ (property w.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, property_rename]) (SyntaxRenameBinders.under_4 hp B)
    have hv4 : Derives Δ (SyntaxMixedFormulaRecursiveSyntax.advanced w.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, SyntaxMixedFormulaRecursiveSyntax.advanced_rename]) (SyntaxRenameBinders.under_4 hv B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hr := Derives.impE (.conjL (SyntaxMixedFormulaAdvancedOutput.at_lift hZ4 w.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) hw4 (.conjL hB))) hv4
    exact SyntaxMixedFormulaFiberUnique.property_unique hZ4 w.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) (Fin.last m).castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc.castSucc hw4 hp4 (.conjR hB) hr
end PPAC.Migration.Internal.SyntaxMixedFormulaCheckUnique
