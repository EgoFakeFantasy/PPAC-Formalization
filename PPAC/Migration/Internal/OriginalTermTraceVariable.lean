import PPAC.Migration.Internal.OriginalTermTraceSyntax
import PPAC.Migration.Internal.FreeReplaceResultRows

/-! 原项轨迹在任意内部变量码上与四分支规格双向对应，并实际取得原行码。 -/
namespace PPAC.Migration.Internal.OriginalTermTraceVariable
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalTermTraceSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem exists_root {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three : Bool) (w depth parameter input output : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem depth w)) (hp : Derives Γ (.mem parameter w))
    (hn : Derives Γ (.mem input w)) (hq : Derives Γ (.mem output w)) : Derives Γ (existsRoot three w depth parameter input output) := by
  cases three with
  | true => exact FreeReplaceResultRows.exists_root hZ w depth parameter input output hw hd hp hn hq
  | false => exact FreeWeakenResultRows.exists_root hZ w depth parameter input output hw hd hp hn hq

theorem value_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three bound : Bool)
    (w parameter input idx output : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (SyntaxVariableSyntax.code bound w idx input))
    (hv : Derives Γ (OriginalScalarValues.valueSpec three bound w parameter input idx output)) : Derives Γ (.mem output w) := by
  cases bound with
  | true => exact mem_subst (eq_symm hv) (HornVariableValue.code_natural hZ true w idx input hw hi)
  | false =>
    cases three with
    | true => exact .conjR (LookupTableJudgment.parameters_legal w parameter idx output hv)
    | false => exact FreeWeakenValue.natural hZ w idx output hw hv

theorem root_iff_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three bound : Bool)
    (w depth parameter input idx output row : Fin m) (hw : Derives Γ (omega w))
    (hi : Derives Γ (SyntaxVariableSyntax.code bound w idx input))
    (hr : Derives Γ (root three w depth parameter input output row)) :
    Derives Γ ((HornLookupConditionSyntax.condition w row).iff (OriginalScalarValues.valueSpec three bound w parameter input idx output)) := by
  let B := (SyntaxNumeralSyntax.numeral (OriginalScalarClasses.mode three) (Fin.last m)).conj
    (SyntaxNodeSyntax.constructor 5 1 w.castSucc (HornRowFields.five (Fin.last m) depth.castSucc parameter.castSucc input.castSucc output.castSucc) row.castSucc)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hr
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hi1 : Derives Δ (SyntaxVariableSyntax.code bound w.castSucc idx.castSucc input.castSucc) := of_eq (SyntaxVariableSyntax.code_rename bound w idx input Fin.castSucc) (under hi B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho := OriginalScalarValues.trace_iff_value (ZFContext.under hZ B) three bound w.castSucc row.castSucc idx.castSucc _ hw1 (.conjR hB) (.conjL hB) hi1
  have h2 : HornRowFields.five (Fin.last m) depth.castSucc parameter.castSucc input.castSucc output.castSucc (2 : Fin 5) = parameter.castSucc := rfl
  have h3 : HornRowFields.five (Fin.last m) depth.castSucc parameter.castSucc input.castSucc output.castSucc (3 : Fin 5) = input.castSucc := rfl
  have h4 : HornRowFields.five (Fin.last m) depth.castSucc parameter.castSucc input.castSucc output.castSucc (4 : Fin 5) = output.castSucc := rfl
  rw [h2, h3, h4] at ho
  simpa only [Formula.raise, Formula.iff, Formula.rename, HornLookupConditionSyntax.condition_rename, OriginalScalarValues.valueSpec_rename] using ho

theorem run_iff_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (three bound : Bool)
    (w depth parameter input idx output : Fin m) (hw : Derives Γ (omega w))
    (hm : Derives Γ (metadata w depth parameter)) (hi : Derives Γ (SyntaxVariableSyntax.code bound w idx input)) :
    Derives Γ ((run three w depth parameter input output).iff (OriginalScalarValues.valueSpec three bound w parameter input idx output)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := run three w depth parameter input output
    let B := (root three w.castSucc depth.castSucc parameter.castSucc input.castSucc output.castSucc (Fin.last m)).conj (HornLookupConditionSyntax.condition w.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hi1 : Derives Δ (SyntaxVariableSyntax.code bound w.castSucc idx.castSucc input.castSucc) := of_eq (SyntaxVariableSyntax.code_rename bound w idx input Fin.castSucc) (under (add hi E) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ho := Derives.impE (.conjL (root_iff_value (ZFContext.under (ZFContext.add hZ E) B) three bound _ _ _ _ _ _ _ hw1 hi1 (.conjL hB))) (.conjR hB)
    exact of_eq (OriginalScalarValues.valueSpec_rename three bound w parameter input idx output Fin.castSucc).symm ho
  · apply Derives.impI
    let E := OriginalScalarValues.valueSpec three bound w parameter input idx output
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hZ0 := ZFContext.add hZ E
    have hq := value_natural hZ0 three bound w parameter input idx output (add hw E) (add hi E) hE
    have hn := HornVariableValue.code_natural hZ0 bound w idx input (add hw E) (add hi E)
    have he := exists_root hZ0 three w depth parameter input output (add hw E) (add (.conjL hm) E) (add (.conjR hm) E) hn hq
    let B := (Formula.mem (Fin.last m) w.castSucc).conj (root three w.castSucc depth.castSucc parameter.castSucc input.castSucc output.castSucc (Fin.last m))
    let Δ := Context.add B (Context.image Formula.raise (Context.add E Γ))
    apply Derives.exE (p := B) he
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) B)
    have hi1 : Derives Δ (SyntaxVariableSyntax.code bound w.castSucc idx.castSucc input.castSucc) := of_eq (SyntaxVariableSyntax.code_rename bound w idx input Fin.castSucc) (under (add hi E) B)
    have hv1 : Derives Δ (OriginalScalarValues.valueSpec three bound w.castSucc parameter.castSucc input.castSucc idx.castSucc output.castSucc) := of_eq (OriginalScalarValues.valueSpec_rename three bound w parameter input idx output Fin.castSucc) (under hE B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have ht := Derives.impE (.conjR (root_iff_value (ZFContext.under hZ0 B) three bound _ _ _ _ _ _ _ hw1 hi1 (.conjR hB))) hv1
    exact of_eq (run_rename three w depth parameter input output Fin.castSucc).symm (intro_run three _ _ _ _ _ _ (.conjR hB) ht)

end PPAC.Migration.Internal.OriginalTermTraceVariable
