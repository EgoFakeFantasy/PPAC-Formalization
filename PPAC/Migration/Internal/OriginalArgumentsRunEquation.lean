import PPAC.Migration.Internal.OriginalArgumentRoots

/-! 原mode0/3参数列表整体运行的精确双向方程，arity赋值与根行码均由对象量词消去。 -/
namespace PPAC.Migration.Internal.OriginalArgumentsRunEquation
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalArgumentCaseSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem run_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool)
    (w mode depth parameter input output : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode))
    (hd : Derives Γ (.mem depth w)) (hp : Derives Γ (.mem parameter w)) :
    Derives Γ ((OriginalTransformRowSyntax.run 2 w mode depth parameter input output).iff (outcomes w mode depth parameter input output)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := OriginalTransformRowSyntax.run 2 w mode depth parameter input output
    let B := (OriginalTransformRowSyntax.row 2 w.castSucc mode.castSucc depth.castSucc parameter.castSucc input.castSucc output.castSucc (Fin.last m)).conj (HornLookupConditionSyntax.condition w.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ _ Fin.castSucc) (under (add hm E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have he := OriginalArgumentsTraceEquation.at_row (ZFContext.under (ZFContext.add hZ E) B) three _ _ _ _ _ _ _ hw1 hm1 (.conjL hB)
    exact of_eq (outcomes_rename w mode depth parameter input output Fin.castSucc).symm (.impE (.conjL he) (.conjR hB))
  · apply Derives.impI
    let E := outcomes w mode depth parameter input output
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hZ0 := ZFContext.add hZ E
    have hnq := OriginalArgumentRoots.outcomes_natural hZ0 w mode depth parameter input output (add hw E) hE
    have hmNat := SyntaxNumerals.range hZ0 (OriginalScalarClasses.mode three) w mode (add hw E) (add hm E)
    have hex := OriginalArgumentRoots.exists_row hZ0 2 w mode depth parameter input output (add hw E) hmNat (add hd E) (add hp E) (.conjL hnq) (.conjR hnq)
    let B := (Formula.mem (Fin.last m) w.castSucc).conj (OriginalTransformRowSyntax.row 2 w.castSucc mode.castSucc depth.castSucc parameter.castSucc input.castSucc output.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) hex
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hm1 : Derives Δ (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) mode.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename _ _ Fin.castSucc) (under (add hm E) B)
    have ho1 : Derives Δ (outcomes w.castSucc mode.castSucc depth.castSucc parameter.castSucc input.castSucc output.castSucc) := of_eq (outcomes_rename w mode depth parameter input output Fin.castSucc) (under hE B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have he := OriginalArgumentsTraceEquation.at_row (ZFContext.under hZ0 B) three _ _ _ _ _ _ _ hw1 hm1 (.conjR hB)
    have ht := Derives.impE (.conjR he) ho1
    exact of_eq (OriginalTransformRowSyntax.run_rename 2 w mode depth parameter input output Fin.castSucc).symm
      (OriginalTransformRowSyntax.intro_run 2 _ _ _ _ _ _ _ (.conjR hB) ht)

end PPAC.Migration.Internal.OriginalArgumentsRunEquation
