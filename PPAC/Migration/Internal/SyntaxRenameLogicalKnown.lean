import PPAC.Migration.Internal.SyntaxRenameLogicalExistence

/-! 已知原源构造时筛出真实逻辑分支，并在内部 Earlier 下证明任意正式父输出唯一。 -/
namespace PPAC.Migration.Internal.SyntaxRenameLogicalKnown
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxRenameOutputSyntax SyntaxMapCodeSyntax SyntaxLogicalSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single_of_renamed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w R S r s a b c d n q x : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (hc : Derives Γ (singleCode tag w x n))
    (hq : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q)) :
    Derives Γ (SyntaxRenameRecursiveSyntax.single tag advance w R S a b c d n q) := by
  rcases valid with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact SyntaxRenameTagCases.of_renamed hZ 4 1 w R S r s a b c d n q (fun _ => x) hw hr hs hc hq
  · exact SyntaxRenameTagCases.of_renamed hZ 9 1 w R S r s a b c d n q (fun _ => x) hw hr hs hc hq
  · exact SyntaxRenameTagCases.of_renamed hZ 10 1 w R S r s a b c d n q (fun _ => x) hw hr hs hc hq

theorem single_unique_at_graphs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w R S r s a b c d n q v x : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (hc : Derives Γ (singleCode tag w x n))
    (hq : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q))
    (hv : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n v)) : Derives Γ (.equal q v) := by
  have h1 := single_of_renamed hZ tag advance valid w R S r s a b c d n q x hw hr hs hc hq
  have h2 := single_of_renamed hZ tag advance valid w R S r s a b c d n v x hw hr hs hc hv
  exact SyntaxRenameLogicalUnique.single_unique hZ tag advance w R S a b c d n q v hw he h1 h2

theorem binary_of_renamed {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w R S r s a b c d n q x y : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (hc : Derives Γ (binaryCode kind w x y n))
    (hq : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q)) :
    Derives Γ (SyntaxRenameRecursiveSyntax.binary kind w R S a b c d n q) := by
  have hk : kind = (0 : Fin 4) ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
  rcases hk with rfl | rfl | rfl | rfl
  · exact SyntaxRenameTagCases.of_renamed hZ 5 2 w R S r s a b c d n q (SyntaxAtomSyntax.two x y) hw hr hs hc hq
  · exact SyntaxRenameTagCases.of_renamed hZ 6 2 w R S r s a b c d n q (SyntaxAtomSyntax.two x y) hw hr hs hc hq
  · exact SyntaxRenameTagCases.of_renamed hZ 7 2 w R S r s a b c d n q (SyntaxAtomSyntax.two x y) hw hr hs hc hq
  · exact SyntaxRenameTagCases.of_renamed hZ 8 2 w R S r s a b c d n q (SyntaxAtomSyntax.two x y) hw hr hs hc hq

theorem binary_unique_at_graphs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w R S r s a b c d n q v x y : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n))
    (hr : Derives Γ (encoded w r a c R)) (hs : Derives Γ (encoded w s b d S))
    (hc : Derives Γ (binaryCode kind w x y n))
    (hq : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n q))
    (hv : Derives Γ (SyntaxRenameJudgmentSyntax.renamed w R S a b c d n v)) : Derives Γ (.equal q v) := by
  have h1 := binary_of_renamed hZ kind w R S r s a b c d n q x y hw hr hs hc hq
  have h2 := binary_of_renamed hZ kind w R S r s a b c d n v x y hw hr hs hc hv
  exact SyntaxRenameLogicalUnique.binary_unique hZ kind w R S a b c d n q v hw he h1 h2

end PPAC.Migration.Internal.SyntaxRenameLogicalKnown
