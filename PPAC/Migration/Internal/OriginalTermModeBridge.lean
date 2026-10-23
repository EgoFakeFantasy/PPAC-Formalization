import PPAC.Migration.Internal.ObjectOriginalArgumentRun

/-! 内部实际模式数码与原mode0/3项接口的精确桥；候选项/结果均任意内部对象。 -/
namespace PPAC.Migration.Internal.OriginalTermModeBridge
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

theorem intro_root {m} {Γ : Context m} (three : Bool) (w mode depth parameter input output r : Fin m)
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (hr : Derives Γ (OriginalTransformRowSyntax.row 1 w mode depth parameter input output r)) :
    Derives Γ (OriginalTermTraceSyntax.root three w depth parameter input output r) := by
  apply Derives.exI mode
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNumeralSyntax.numeral_rename, SyntaxNodeSyntax.constructor_rename, OriginalTransformRowSyntax.row, FreeWeakenResultSyntax.five_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hm hr)

theorem root_at_mode {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w mode depth parameter input output r : Fin m)
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (hr : Derives Γ (OriginalTermTraceSyntax.root three w depth parameter input output r)) :
    Derives Γ (OriginalTransformRowSyntax.row 1 w mode depth parameter input output r) := by
  let B := (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (Fin.last m)).conj
    (OriginalTransformRowSyntax.row 1 w.castSucc (Fin.last m) depth.castSucc parameter.castSucc input.castSucc output.castSucc r.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hr
  have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ _ Fin.castSucc) (under hm B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have he := SyntaxNumerals.unique (ZFContext.under hZ B) (OriginalScalarClasses.mode three) (Fin.last m) mode.castSucc (.conjL hB) hm1
  have ho := OriginalRowMetadataSubstitution.row_mode 1 _ _ _ _ _ _ _ _ he (.conjR hB)
  exact of_eq (OriginalTransformRowSyntax.row_rename 1 w mode depth parameter input output r Fin.castSucc).symm ho

theorem run_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w mode depth parameter input output : Fin m)
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode)) :
    Derives Γ ((OriginalTransformRowSyntax.run 1 w mode depth parameter input output).iff (OriginalTermTraceSyntax.run three w depth parameter input output)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := OriginalTransformRowSyntax.run 1 w mode depth parameter input output
    let B := (OriginalTransformRowSyntax.row 1 w.castSucc mode.castSucc depth.castSucc parameter.castSucc input.castSucc output.castSucc (Fin.last m)).conj (HornLookupConditionSyntax.condition w.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ _ Fin.castSucc) (under (add hm E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hroot := intro_root three _ _ _ _ _ _ _ hm1 (.conjL hB)
    exact of_eq (OriginalTermTraceSyntax.run_rename three w depth parameter input output Fin.castSucc).symm (OriginalTermTraceSyntax.intro_run three _ _ _ _ _ _ hroot (.conjR hB))
  · apply Derives.impI
    let E := OriginalTermTraceSyntax.run three w depth parameter input output
    let B := (OriginalTermTraceSyntax.root three w.castSucc depth.castSucc parameter.castSucc input.castSucc output.castSucc (Fin.last m)).conj (HornLookupConditionSyntax.condition w.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ _ Fin.castSucc) (under (add hm E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have hr := root_at_mode (ZFContext.under (ZFContext.add hZ E) B) three _ _ _ _ _ _ _ hm1 (.conjL hB)
    exact of_eq (OriginalTransformRowSyntax.run_rename 1 w mode depth parameter input output Fin.castSucc).symm (OriginalTransformRowSyntax.intro_run 1 _ _ _ _ _ _ _ hr (.conjR hB))

end PPAC.Migration.Internal.OriginalTermModeBridge
