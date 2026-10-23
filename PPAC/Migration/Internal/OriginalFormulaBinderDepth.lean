import PPAC.Migration.Internal.OriginalFormulaDataSubstitution

/-! 实际后继深度处的量词分支双条件；不同存在见证由原外延性唯一性对齐。 -/
namespace PPAC.Migration.Internal.OriginalFormulaBinderDepth
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalFormulaCaseSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem case_at_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat)
    (w mode depth parameter n q childDepth : Fin m) (hs : Derives Γ (successor childDepth depth)) :
    Derives Γ ((binderCase tag w mode depth parameter n q).iff (unaryCase tag w mode childDepth parameter n q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := binderCase tag w mode depth parameter n q
    let B := binderBody tag w mode depth parameter n q
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ E) B
    have hs1 : Derives Δ (successor childDepth.castSucc depth.castSucc) := of_eq (successor_rename childDepth depth Fin.castSucc) (under (add hs E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have he := InsertLogic.unique (Fin.last m) childDepth.castSucc depth.castSucc depth.castSucc (ZFContext.arithmetic hZ1).base.extensionality (.conjL hB) hs1
    have ho := OriginalFormulaDataSubstitution.unary_case_depth tag w.castSucc mode.castSucc (Fin.last m) parameter.castSucc n.castSucc q.castSucc childDepth.castSucc he (.conjR hB)
    exact of_eq (unaryCase_rename tag w mode childDepth parameter n q Fin.castSucc).symm ho
  · apply Derives.impI
    exact intro_binder tag w mode depth parameter n q childDepth (add hs _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.OriginalFormulaBinderDepth
