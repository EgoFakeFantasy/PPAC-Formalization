import PPAC.Migration.Internal.FormulaTransformProgramCodeSyntax

/-! 固定公式程序具有实际唯一内部码，并在同一个对象句子内对全部八个运行时参数正确。 -/
namespace PPAC.Migration.Internal.FormulaTransformProgramCode
open Source SourceAlgebra SourceLogic OmegaSyntax FormulaTransformProgramSyntax FormulaTransformProgramCodeSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem encoded_execution_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w P R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (code w P)) : Derives Γ (correctAt w P R S a b c d n q) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := encodedExecution w P R S a b c d n q
    have he := FormulaTransformRecursionCorrectness.execution_iff (ZFContext.add hZ E) w R S a b c d n q (add hw E)
    exact .impE (.conjL he) (.conjR (.hyp (Or.inl rfl)))
  · apply Derives.impI
    let E := SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q
    have he := FormulaTransformRecursionCorrectness.execution_iff (ZFContext.add hZ E) w R S a b c d n q (add hw E)
    exact .conjI (add hp E) (.impE (.conjR he) (.hyp (Or.inl rfl)))

theorem uniform_correctness {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w P : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (code w P)) : Derives Γ (uniform w P) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  have hZ1 := ZFContext.rename hZ Fin.castSucc
  have hw1 := Derives.rename Fin.castSucc hw
  have hp1 := Derives.rename Fin.castSucc hp
  have hZ2 := ZFContext.rename hZ1 Fin.castSucc
  have hw2 := Derives.rename Fin.castSucc hw1
  have hp2 := Derives.rename Fin.castSucc hp1
  have hZ3 := ZFContext.rename hZ2 Fin.castSucc
  have hw3 := Derives.rename Fin.castSucc hw2
  have hp3 := Derives.rename Fin.castSucc hp2
  have hZ4 := ZFContext.rename hZ3 Fin.castSucc
  have hw4 := Derives.rename Fin.castSucc hw3
  have hp4 := Derives.rename Fin.castSucc hp3
  have hZ5 := ZFContext.rename hZ4 Fin.castSucc
  have hw5 := Derives.rename Fin.castSucc hw4
  have hp5 := Derives.rename Fin.castSucc hp4
  have hZ6 := ZFContext.rename hZ5 Fin.castSucc
  have hw6 := Derives.rename Fin.castSucc hw5
  have hp6 := Derives.rename Fin.castSucc hp5
  have hZ7 := ZFContext.rename hZ6 Fin.castSucc
  have hw7 := Derives.rename Fin.castSucc hw6
  have hp7 := Derives.rename Fin.castSucc hp6
  have hZ8 := ZFContext.rename hZ7 Fin.castSucc
  have hw8 := Derives.rename Fin.castSucc hw7
  have hp8 := Derives.rename Fin.castSucc hp7
  exact encoded_execution_iff hZ8 w.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc P.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)).castSucc.castSucc.castSucc.castSucc (Fin.last (m+4)).castSucc.castSucc.castSucc (Fin.last (m+5)).castSucc.castSucc (Fin.last (m+6)).castSucc (Fin.last (m+7)) (of_eq (by simp only [omega_rename]) hw8) (of_eq (by simp only [code_rename]) hp8)

theorem unique_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w P : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (code w P)) : Derives Γ (uniqueCode w P) := by
  apply Derives.allI
  apply Derives.impI
  let Q := code w.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have hp1 : Derives Δ (code w.castSucc P.castSucc) := of_eq (code_rename w P Fin.castSucc) (under hp Q)
  exact OriginalTreeQuotationUnique.tree_unique (ZFContext.under hZ Q) (programTree formulaProgram) w.castSucc (Fin.last m) P.castSucc hw1 (.hyp (Or.inl rfl)) hp1

theorem at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w P : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (code w P)) : Derives Γ (programValue w P) :=
  .conjI (OriginalTreeQuotationProperties.tree_range hZ (programTree formulaProgram) w P hw hp)
    (.conjI hp (.conjI (uniform_correctness hZ w P hw hp) (unique_code hZ w P hw hp)))

theorem exists_correct_program {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (existsProgram w) := by
  have he := OriginalTreeQuotationExistence.tree_exists hZ (programTree formulaProgram) w hw
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (code w.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have ho := intro_existsProgram w.castSucc (Fin.last m) (at_code (ZFContext.under hZ P) w.castSucc (Fin.last m) hw1 (.conjR hP))
  exact of_eq (by simp only [Formula.raise, existsProgram_rename]) ho

end PPAC.Migration.Internal.FormulaTransformProgramCode
