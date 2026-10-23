import PPAC.Migration.Internal.SyntaxMixedFormulaLogicalExistence

/-! 已知原源构造时筛出真实逻辑分支，并在内部 Earlier 下证明任意正式父输出唯一。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaLogicalKnown
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMixedFormulaOutputSyntax SyntaxLogicalSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single_of_substituted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w R S a b c d n q x : Fin m)
    (hw : Derives Γ (omega w))
    (hc : Derives Γ (singleCode tag w x n))
    (hq : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q)) :
    Derives Γ (SyntaxMixedFormulaRecursiveSyntax.single tag advance w R S a b c d n q) := by
  rcases valid with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact SyntaxMixedFormulaTagCases.of_substituted hZ 4 1 w R S a b c d n q (fun _ => x) hw hc hq
  · exact SyntaxMixedFormulaTagCases.of_substituted hZ 9 1 w R S a b c d n q (fun _ => x) hw hc hq
  · exact SyntaxMixedFormulaTagCases.of_substituted hZ 10 1 w R S a b c d n q (fun _ => x) hw hc hq

theorem single_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w R S a b c d n q v x : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))

    (hc : Derives Γ (singleCode tag w x n))
    (hq : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q))
    (hv : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n v)) : Derives Γ (.equal q v) := by
  have h1 := single_of_substituted hZ tag advance valid w R S a b c d n q x hw hc hq
  have h2 := single_of_substituted hZ tag advance valid w R S a b c d n v x hw hc hv
  exact SyntaxMixedFormulaLogicalUnique.single_unique hZ tag advance w R S a b c d n q v hw he h1 h2

theorem binary_of_substituted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w R S a b c d n q x y : Fin m)
    (hw : Derives Γ (omega w))
    (hc : Derives Γ (binaryCode kind w x y n))
    (hq : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q)) :
    Derives Γ (SyntaxMixedFormulaRecursiveSyntax.binary kind w R S a b c d n q) := by
  have hk : kind = (0 : Fin 4) ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
  rcases hk with rfl | rfl | rfl | rfl
  · exact SyntaxMixedFormulaTagCases.of_substituted hZ 5 2 w R S a b c d n q (SyntaxAtomSyntax.two x y) hw hc hq
  · exact SyntaxMixedFormulaTagCases.of_substituted hZ 6 2 w R S a b c d n q (SyntaxAtomSyntax.two x y) hw hc hq
  · exact SyntaxMixedFormulaTagCases.of_substituted hZ 7 2 w R S a b c d n q (SyntaxAtomSyntax.two x y) hw hc hq
  · exact SyntaxMixedFormulaTagCases.of_substituted hZ 8 2 w R S a b c d n q (SyntaxAtomSyntax.two x y) hw hc hq

theorem binary_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w R S a b c d n q v x y : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))

    (hc : Derives Γ (binaryCode kind w x y n))
    (hq : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q))
    (hv : Derives Γ (SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n v)) : Derives Γ (.equal q v) := by
  have h1 := binary_of_substituted hZ kind w R S a b c d n q x y hw hc hq
  have h2 := binary_of_substituted hZ kind w R S a b c d n v x y hw hc hv
  exact SyntaxMixedFormulaLogicalUnique.binary_unique hZ kind w R S a b c d n q v hw he h1 h2

end PPAC.Migration.Internal.SyntaxMixedFormulaLogicalKnown
