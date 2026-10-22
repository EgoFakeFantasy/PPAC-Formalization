import PPAC.Migration.Internal.SyntaxRenameFiberUnique

/-! 普通及量词提升子判断的实际目标类型、范围和给定内部 Property 下的全候选唯一性。 -/
namespace PPAC.Migration.Internal.SyntaxRenameCheckUnique
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxRenameOutputSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem target_type {m} {Γ : Context m} (advance : Bool) (w x r s a b c d q : Fin m)
    (hc : Derives Γ (SyntaxRenameRecursiveSyntax.check advance w x r s a b c d q)) :
    Derives Γ (FormulaCodeRecursiveSyntax.stepCheck advance w q c d) := by
  cases advance
  · exact SyntaxRenameJudgment.target_type w r s a b c d x q hc
  · change Derives Γ (FormulaCodeRecursiveSyntax.advancedCode w q c d)
    let B := SyntaxRenameRecursiveSyntax.advancedBody w x r s a b c d q
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
    apply SyntaxRenameAdvancedKnown.eliminate_advanced w x r s a b c d q _ hc
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hs := SyntaxMapLiftParameters.successors _ _ _ _ _ _ _ (.conjL hB)
    have ht := SyntaxRenameJudgment.target_type _ _ _ _ _ _ _ _ _ (.conjR hB)
    have ho := FormulaCodeRecursiveSyntax.intro_advanced w.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (.conjR hs) ht
    exact of_eq (by simp only [Formula.raise, FormulaCodeRecursiveSyntax.advancedCode_rename]) ho

theorem natural {m} {Γ : Context m} (advance : Bool) (w x r s a b c d q : Fin m)
    (hc : Derives Γ (SyntaxRenameRecursiveSyntax.check advance w x r s a b c d q)) : Derives Γ (.mem q w) := by
  cases advance
  · exact SyntaxRenameOutput.output_natural w r s a b c d x q hc
  · let B := SyntaxRenameRecursiveSyntax.advancedBody w x r s a b c d q
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
    apply SyntaxRenameAdvancedKnown.eliminate_advanced w x r s a b c d q _ hc
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    exact SyntaxRenameOutput.output_natural _ _ _ _ _ _ _ _ _ (.conjR hB)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (advance : Bool) (w x r s a b c d q v : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (property w x))
    (hq : Derives Γ (SyntaxRenameRecursiveSyntax.check advance w x r s a b c d q))
    (hv : Derives Γ (SyntaxRenameRecursiveSyntax.check advance w x r s a b c d v)) : Derives Γ (.equal q v) := by
  cases advance
  · exact SyntaxRenameFiberUnique.property_unique hZ w r s a b c d x q v hw hp hq hv
  · change Derives Γ (SyntaxRenameRecursiveSyntax.advanced w x r s a b c d v) at hv
    let B := SyntaxRenameRecursiveSyntax.advancedBody w x r s a b c d q
    let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
    apply SyntaxRenameAdvancedKnown.eliminate_advanced w x r s a b c d q _ hq
    have hZ3 := SyntaxAtomLogic.zf_under_three hZ B
    have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxAtomLogic.under_three hw B)
    have hp3 : Derives Δ (property w.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, property_rename]) (SyntaxAtomLogic.under_three hp B)
    have hv3 : Derives Δ (SyntaxRenameRecursiveSyntax.advanced w.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc v.castSucc.castSucc.castSucc) :=
      of_eq (by simp only [Formula.raise, SyntaxRenameRecursiveSyntax.advanced_rename]) (SyntaxAtomLogic.under_three hv B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hr := Derives.impE (.conjL (SyntaxRenameAdvancedKnown.at_lift hZ3 _ _ _ _ _ _ _ _ _ (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hw3 (.conjL hB))) hv3
    exact SyntaxRenameFiberUnique.property_unique hZ3 _ _ _ _ _ _ _ _ _ _ hw3 hp3 (.conjR hB) hr
end PPAC.Migration.Internal.SyntaxRenameCheckUnique
