import PPAC.Migration.Internal.LookupTableProgramCodeSyntax

/-! 固定查找程序具有实际唯一内部码，并在同一个对象句子内对全部三个运行时参数正确。 -/
namespace PPAC.Migration.Internal.LookupTableProgramCode
open Source SourceAlgebra SourceLogic OmegaSyntax LookupTableProgramSyntax LookupTableProgramCodeSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem encoded_execution_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w P n i y : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (code w P)) : Derives Γ (correctAt w P n i y) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := encodedExecution w P n i y
    have he := LookupTableCorrectness.execution_iff_checked (ZFContext.add hZ E) w n i y (add hw E)
    exact .impE (.conjL he) (.conjR (.hyp (Or.inl rfl)))
  · apply Derives.impI
    let E := StrictLookupSyntax.checked w n i y
    have he := LookupTableCorrectness.execution_iff_checked (ZFContext.add hZ E) w n i y (add hw E)
    exact .conjI (add hp E) (.impE (.conjR he) (.hyp (Or.inl rfl)))

theorem uniform_correctness {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w P : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (code w P)) : Derives Γ (uniform w P) := by
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
  exact encoded_execution_iff hZ3 w.castSucc.castSucc.castSucc P.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) (of_eq (by simp only [omega_rename]) hw3) (of_eq (by simp only [code_rename]) hp3)

theorem unique_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w P : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (code w P)) : Derives Γ (uniqueCode w P) := by
  apply Derives.allI
  apply Derives.impI
  let Q := code w.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have hp1 : Derives Δ (code w.castSucc P.castSucc) := of_eq (code_rename w P Fin.castSucc) (under hp Q)
  exact OriginalTreeQuotationUnique.tree_unique (ZFContext.under hZ Q) (programTree lookupProgram) w.castSucc (Fin.last m) P.castSucc hw1 (.hyp (Or.inl rfl)) hp1

theorem at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w P : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (code w P)) : Derives Γ (programValue w P) :=
  .conjI (OriginalTreeQuotationProperties.tree_range hZ (programTree lookupProgram) w P hw hp)
    (.conjI hp (.conjI (uniform_correctness hZ w P hw hp) (unique_code hZ w P hw hp)))

theorem exists_correct_program {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (existsProgram w) := by
  have he := OriginalTreeQuotationExistence.tree_exists hZ (programTree lookupProgram) w hw
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (code w.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have ho := intro_existsProgram w.castSucc (Fin.last m) (at_code (ZFContext.under hZ P) w.castSucc (Fin.last m) hw1 (.conjR hP))
  exact of_eq (by simp only [Formula.raise, existsProgram_rename]) ho

end PPAC.Migration.Internal.LookupTableProgramCode
