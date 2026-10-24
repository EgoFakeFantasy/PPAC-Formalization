import PPAC.Migration.Internal.ProjectCompilerCompleteQueries

/-! Every actual logical source-field matrix obtains an output from member induction. -/
namespace PPAC.Migration.Internal.ProjectCompilerCompleteFields
open Source SourceAlgebra SourceLogic OmegaSyntax ProjectCompilerCompleteSyntax ProjectCompilerCompleteQuerySyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem single_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (hs : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w n b f z x : Fin m) (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hz : Derives Γ (empty z))
    (hI : Derives Γ (allIH w n)) (hd : Derives Γ (ProjectSourceCodeRecursiveSyntax.singleFields tag advance w b f x n)) :
    Derives Γ (existsOutput w n b) := by
  have he := ProjectCompilerCompleteQueries.source_check_output advance w n x b f z hz hI (.conjL (.conjR hd)) (.conjR (.conjR hd))
  let K := ProjectCompilerCaseSyntax.check advance ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w.castSucc)
    n.castSucc x.castSucc b.castSucc (Fin.last m)
  let Δ := Context.add K (Context.image Formula.raise Γ)
  apply Derives.exE (p := K) he
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw K)
  have hb1 : Derives Δ (.mem b.castSucc w.castSucc) := under hb K
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz K)
  have hc1 := of_eq (SyntaxLogicalSyntax.singleCode_rename tag w x n Fin.castSucc) (under (.conjL hd) K)
  have ho := ProjectCompilerCompleteConstructors.single_output (ZFContext.under hZ K) tag advance hs
    w.castSucc n.castSucc b.castSucc z.castSucc x.castSucc (Fin.last m) hw1 hb1 hz1 hc1 hK
  exact of_eq (existsOutput_rename w n b Fin.castSucc).symm ho

theorem binary_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w n b f z x y : Fin m) (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hz : Derives Γ (empty z))
    (hI : Derives Γ (allIH w n)) (hd : Derives Γ (ProjectSourceCodeRecursiveSyntax.binaryFields kind w b f x y n)) :
    Derives Γ (existsOutput w n b) := by
  have hx := Derives.conjL (Derives.conjR hd)
  have hy := Derives.conjL (Derives.conjR (Derives.conjR hd))
  have hsource := Derives.conjR (Derives.conjR (Derives.conjR hd))
  have heX := ProjectCompilerCompleteQueries.source_check_output false w n x b f z hz hI hx (.conjL hsource)
  have heY := ProjectCompilerCompleteQueries.source_check_output false w n y b f z hz hI hy (.conjR hsource)
  let X := ProjectCompilerCaseSyntax.queried ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w.castSucc)
    n.castSucc x.castSucc b.castSucc (Fin.last m)
  let Ξ := Context.add X (Context.image Formula.raise Γ)
  apply Derives.exE (p := X) heX
  have hX : Derives Ξ X := .hyp (Or.inl rfl)
  have heY1 := of_eq (someCheck_rename false w n y b Fin.castSucc) (under heY X)
  let Y := ProjectCompilerCaseSyntax.queried ProjectCompilerRecursiveSyntax.codeMatrix (ProjectCompilerRecursiveSyntax.parameters w.castSucc.castSucc)
    n.castSucc.castSucc y.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add Y (Context.image Formula.raise Ξ)
  apply Derives.exE (p := Y) heY1
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have hX2 := of_eq (ProjectCompilerCaseSyntax.queried_rename ProjectCompilerRecursiveSyntax.codeMatrix
    (ProjectCompilerRecursiveSyntax.parameters w.castSucc) n.castSucc x.castSucc b.castSucc (Fin.last m) Fin.castSucc) (under hX Y)
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw X) Y)
  have hb2 : Derives Δ (.mem b.castSucc.castSucc w.castSucc.castSucc) := under (under hb X) Y
  have hz2 : Derives Δ (empty z.castSucc.castSucc) := of_eq (by simp only [Formula.raise, empty_rename]) (under (under hz X) Y)
  have hd2 : Derives Δ (SyntaxLogicalSyntax.binaryCode kind w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxLogicalSyntax.binaryCode_rename]) (under (under (Derives.conjL hd) X) Y)
  have ho := ProjectCompilerCompleteConstructors.binary_output (ZFContext.under (ZFContext.under hZ X) Y) kind
    w.castSucc.castSucc n.castSucc.castSucc b.castSucc.castSucc z.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) hw2 hb2 hz2 hd2 hX2 hY
  exact of_eq (by simp only [Formula.raise, existsOutput_rename]) ho

end PPAC.Migration.Internal.ProjectCompilerCompleteFields
