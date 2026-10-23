import PPAC.Migration.Internal.WeakenFreeProgramValueSyntax

/-! 输入不合法即拒绝；合法输入实际取得唯一有类型输出，均在原对象推导关系内。 -/
namespace PPAC.Migration.Internal.WeakenFreeProgramValue
open Source SourceAlgebra SourceLogic OmegaSyntax WeakenFreeProgramSyntax WeakenFreeProgramValueSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem input_of_execution {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (executed w a b B n q)) :
    Derives Γ (inputGuard w a b B n) :=
  SyntaxWeakenFreeOutput.input_of_weakened hZ w a b B n q hw
    (.impE (.conjL (WeakenFreeProgramCorrectness.executed_iff hZ w a b B n q hw)) hq)

theorem source_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (executed w a b B n q)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w n a b) := .conjL (input_of_execution hZ w a b B n q hw hq)

theorem reject_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n q : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (OmegaSyntax.successor B b).neg) :
    Derives Γ (executed w a b B n q).neg := by
  apply Derives.impI
  exact .impE (add hi _) (.conjR (input_of_execution (ZFContext.add hZ _) w a b B n q (add hw _) (.hyp (Or.inl rfl))))

theorem reject_source {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n q : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (FormulaCodeSyntax.formulaCode w n a b).neg) :
    Derives Γ (executed w a b B n q).neg := by
  apply Derives.impI
  exact .impE (add hi _) (.conjL (input_of_execution (ZFContext.add hZ _) w a b B n q (add hw _) (.hyp (Or.inl rfl))))

theorem reject_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n q : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (inputGuard w a b B n).neg) :
    Derives Γ (executed w a b B n q).neg := by
  apply Derives.impI
  exact .impE (add hi _) (input_of_execution (ZFContext.add hZ _) w a b B n q (add hw _) (.hyp (Or.inl rfl)))

theorem target_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (executed w a b B n q)) :
    Derives Γ (FormulaCodeSyntax.formulaCode w q a B) :=
  SyntaxWeakenFreeOutput.target_type w a b B n q
    (.impE (.conjL (WeakenFreeProgramCorrectness.executed_iff hZ w a b B n q hw)) hq)

theorem output_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (executed w a b B n q)) : Derives Γ (.mem q w) :=
  SyntaxWeakenFreeOutput.output_natural w a b B n q
    (.impE (.conjL (WeakenFreeProgramCorrectness.executed_iff hZ w a b B n q hw)) hq)

theorem reject_target {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n q : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (FormulaCodeSyntax.formulaCode w q a B).neg) :
    Derives Γ (executed w a b B n q).neg := by
  apply Derives.impI
  exact .impE (add ht _) (target_type (ZFContext.add hZ _) w a b B n q (add hw _) (.hyp (Or.inl rfl)))

theorem reject_output_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n q : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (Formula.mem q w).neg) :
    Derives Γ (executed w a b B n q).neg := by
  apply Derives.impI
  exact .impE (add ht _) (output_natural (ZFContext.add hZ _) w a b B n q (add hw _) (.hyp (Or.inl rfl)))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n q v : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (executed w a b B n q))
    (hv : Derives Γ (executed w a b B n v)) : Derives Γ (.equal q v) :=
  SyntaxWeakenFreeUnique.unique hZ w a b B n q v hw
    (.impE (.conjL (WeakenFreeProgramCorrectness.executed_iff hZ w a b B n q hw)) hq)
    (.impE (.conjL (WeakenFreeProgramCorrectness.executed_iff hZ w a b B n v hw)) hv)

theorem unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (executed w a b B n q)) : Derives Γ (uniqueOutput w a b B n q) := by
  apply Derives.allI
  apply Derives.impI
  let V := executed w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw V)
  have hq1 : Derives Δ (executed w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc q.castSucc) := of_eq (executed_rename w a b B n q Fin.castSucc) (under hq V)
  exact unique (ZFContext.under hZ V) w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m) q.castSucc hw1 (.hyp (Or.inl rfl)) hq1

theorem at_candidate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (executed w a b B n q)) : Derives Γ (value w a b B n q) :=
  .conjI hq (.conjI (target_type hZ w a b B n q hw hq)
    (.conjI (output_natural hZ w a b B n q hw hq) (unique_output hZ w a b B n q hw hq)))

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (inputGuard w a b B n)) : Derives Γ (fiber w a b B n) := by
  have he := SyntaxWeakenFreeOutput.exists_output hZ w a b B n hw hi
  let Q := SyntaxWeakenFreeSyntax.weakened w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have hZ1 := ZFContext.under hZ Q
  have hq := Derives.impE (.conjR (WeakenFreeProgramCorrectness.executed_iff hZ1 w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m) hw1)) (.hyp (Or.inl rfl))
  have ho := intro_fiber w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m)
    (at_candidate hZ1 w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m) hw1 hq)
  exact of_eq (by simp only [Formula.raise, fiber_rename]) ho

theorem input_of_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (fiber w a b B n)) : Derives Γ (inputGuard w a b B n) := by
  let V := value w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  apply Derives.exE hf
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw V)
  have hi := input_of_execution (ZFContext.under hZ V) w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m) hw1 (.conjL hV)
  exact of_eq (by simp only [Formula.raise, inputGuard_rename]) hi

theorem fiber_iff_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((fiber w a b B n).iff (inputGuard w a b B n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact input_of_fiber (ZFContext.add hZ _) w a b B n (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact actual_fiber (ZFContext.add hZ _) w a b B n (add hw _) (.hyp (Or.inl rfl))

theorem actual_state {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (FormulaCodeSyntax.formulaCode w n a b)) : Derives Γ (actualState w a b n) := by
  have he := InsertExistence.exists_insert b b (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union
  let H := successor (Fin.last m) b.castSucc
  let Δ := Context.add H (Context.image Formula.raise Γ)
  apply Derives.exE (p := H) he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw H)
  have hc1 : Derives Δ (FormulaCodeSyntax.formulaCode w.castSucc n.castSucc a.castSucc b.castSucc) :=
    of_eq (FormulaCodeSyntax.formulaCode_rename w n a b Fin.castSucc) (under hc H)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hf := actual_fiber (ZFContext.under hZ H) _ _ _ _ _ hw1 (.conjI hc1 hH)
  have ho : Derives Δ (actualState w.castSucc a.castSucc b.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [H, Formula.instantiate, Formula.rename, successor_rename,
      fiber_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hH hf)
  exact of_eq (actualState_rename w a b n Fin.castSucc).symm ho

end PPAC.Migration.Internal.WeakenFreeProgramValue
