import PPAC.Migration.Internal.FreeSubstProgramValueSyntax

/-! 输入不合法即拒绝；合法输入实际取得唯一有类型输出，均在原对象推导关系内。 -/
namespace PPAC.Migration.Internal.FreeSubstProgramValue
open Source SourceAlgebra SourceLogic OmegaSyntax FreeSubstProgramSyntax FreeSubstProgramValueSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem input_of_execution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (executed w b a c L n q)) :
    Derives Γ (inputGuard w b a c L n) :=
  SyntaxFormulaFreeSubstOutput.input_of_substituted hZ w b a c L n q hw
    (.impE (.conjL (FreeSubstProgramCorrectness.executed_iff hZ w b a c L n q hw)) hq)

theorem source_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (executed w b a c L n q)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n b a) := .conjL (input_of_execution hZ w b a c L n q hw hq)

theorem reject_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n q : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxFreeSubstSyntax.termList w a c L).neg) :
    Derives Γ (executed w b a c L n q).neg := by
  apply Derives.impI
  exact .impE (add hi _) (.conjR (input_of_execution (ZFContext.add hZ _) w b a c L n q (add hw _) (.hyp (Or.inl rfl))))

theorem reject_source {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n q : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (FormulaCodeSyntax.formulaCode w n b a).neg) :
    Derives Γ (executed w b a c L n q).neg := by
  apply Derives.impI
  exact .impE (add hi _) (.conjL (input_of_execution (ZFContext.add hZ _) w b a c L n q (add hw _) (.hyp (Or.inl rfl))))

theorem reject_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n q : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (inputGuard w b a c L n).neg) :
    Derives Γ (executed w b a c L n q).neg := by
  apply Derives.impI
  exact .impE (add hi _) (input_of_execution (ZFContext.add hZ _) w b a c L n q (add hw _) (.hyp (Or.inl rfl)))

theorem target_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (executed w b a c L n q)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w q b c) :=
  SyntaxFormulaFreeSubstOutput.target_type w b a c L n q
    (.impE (.conjL (FreeSubstProgramCorrectness.executed_iff hZ w b a c L n q hw)) hq)

theorem output_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (executed w b a c L n q)) : Derives Γ (.mem q w) :=
  SyntaxFormulaFreeSubstOutput.output_natural w b a c L n q
    (.impE (.conjL (FreeSubstProgramCorrectness.executed_iff hZ w b a c L n q hw)) hq)

theorem reject_target {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n q : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (FormulaCodeSyntax.formulaCode w q b c).neg) :
    Derives Γ (executed w b a c L n q).neg := by
  apply Derives.impI
  exact .impE (add ht _) (target_type (ZFContext.add hZ _) w b a c L n q (add hw _) (.hyp (Or.inl rfl)))

theorem reject_output_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n q : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (Formula.mem q w).neg) :
    Derives Γ (executed w b a c L n q).neg := by
  apply Derives.impI
  exact .impE (add ht _) (output_natural (ZFContext.add hZ _) w b a c L n q (add hw _) (.hyp (Or.inl rfl)))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n q v : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (executed w b a c L n q))
    (hv : Derives Γ (executed w b a c L n v)) : Derives Γ (.equal q v) :=
  SyntaxFormulaFreeSubstUnique.unique hZ w b a c L n q v hw
    (.impE (.conjL (FreeSubstProgramCorrectness.executed_iff hZ w b a c L n q hw)) hq)
    (.impE (.conjL (FreeSubstProgramCorrectness.executed_iff hZ w b a c L n v hw)) hv)

theorem unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (executed w b a c L n q)) : Derives Γ (uniqueOutput w b a c L n q) := by
  apply Derives.allI
  apply Derives.impI
  let V := executed w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw V)
  have hq1 : Derives Δ (executed w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc q.castSucc) := of_eq (executed_rename w b a c L n q Fin.castSucc) (under hq V)
  exact unique (ZFContext.under hZ V) w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m) q.castSucc hw1 (.hyp (Or.inl rfl)) hq1

theorem at_candidate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (executed w b a c L n q)) : Derives Γ (value w b a c L n q) :=
  .conjI hq (.conjI (target_type hZ w b a c L n q hw hq)
    (.conjI (output_natural hZ w b a c L n q hw hq) (unique_output hZ w b a c L n q hw hq)))

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (inputGuard w b a c L n)) : Derives Γ (fiber w b a c L n) := by
  have he := SyntaxFormulaFreeSubstOutput.exists_output hZ w b a c L n hw hi
  let Q := SyntaxFormulaFreeSubstSyntax.substituted w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have hZ1 := ZFContext.under hZ Q
  have hq := Derives.impE (.conjR (FreeSubstProgramCorrectness.executed_iff hZ1 w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m) hw1)) (.hyp (Or.inl rfl))
  have ho := intro_fiber w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m)
    (at_candidate hZ1 w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m) hw1 hq)
  exact of_eq (by simp only [Formula.raise, fiber_rename]) ho

theorem input_of_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (fiber w b a c L n)) : Derives Γ (inputGuard w b a c L n) := by
  let V := value w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  apply Derives.exE hf
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw V)
  have hi := input_of_execution (ZFContext.under hZ V) w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m) hw1 (.conjL hV)
  exact of_eq (by simp only [Formula.raise, inputGuard_rename]) hi

theorem fiber_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((fiber w b a c L n).iff (inputGuard w b a c L n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact input_of_fiber (ZFContext.add hZ _) w b a c L n (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact actual_fiber (ZFContext.add hZ _) w b a c L n (add hw _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.FreeSubstProgramValue
