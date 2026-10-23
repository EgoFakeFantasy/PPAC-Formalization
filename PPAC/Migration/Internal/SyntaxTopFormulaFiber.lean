import PPAC.Migration.Internal.SyntaxTopFormulaUnique

/-! 首槽公式的实际唯一输出纤维、准确输入双条件及非法输入拒绝；环境见证已全部消去。 -/
namespace PPAC.Migration.Internal.SyntaxTopFormulaFiber
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxTopFormulaSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem instantiate_actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (instantiateInput w a b A t n)) : Derives Γ (instantiateFiber w a b A t n) := by
  let Q := instantiated w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) (SyntaxTopFormulaExistence.instantiate_exists hZ w a b A t n hw hi)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hu := SyntaxTopFormulaUnique.instantiate_unique_output (ZFContext.under hZ Q) w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc (Fin.last m) hw1 hQ
  have ho := intro_instantiate_fiber w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc (Fin.last m) hQ hu
  exact of_eq (instantiateFiber_rename w a b A t n Fin.castSucc).symm ho

theorem instantiate_input_of_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (instantiateExists w a b A t n)) : Derives Γ (instantiateInput w a b A t n) := by
  let Q := instantiated w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have ho := SyntaxTopFormulaTyping.instantiate_input (ZFContext.under hZ Q) w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc (Fin.last m) hw1 hQ
  exact of_eq (instantiateInput_rename w a b A t n Fin.castSucc).symm ho

theorem instantiate_exists_of_fiber {m} {Γ : Context m} (w a b A t n : Fin m)
    (he : Derives Γ (instantiateFiber w a b A t n)) : Derives Γ (instantiateExists w a b A t n) := by
  let Q := (instantiated w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc (Fin.last m)).conj (instantiateUnique w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have ho := intro_instantiate_exists w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc (Fin.last m) (.conjL hQ)
  exact of_eq (instantiateExists_rename w a b A t n Fin.castSucc).symm ho

theorem instantiate_exists_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((instantiateExists w a b A t n).iff (instantiateInput w a b A t n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact instantiate_input_of_exists (ZFContext.add hZ _) w a b A t n (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact SyntaxTopFormulaExistence.instantiate_exists (ZFContext.add hZ _) w a b A t n (add hw _) (.hyp (Or.inl rfl))

theorem instantiate_fiber_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((instantiateFiber w a b A t n).iff (instantiateInput w a b A t n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact instantiate_input_of_exists (ZFContext.add hZ _) w a b A t n (add hw _) (instantiate_exists_of_fiber w a b A t n (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact instantiate_actual_fiber (ZFContext.add hZ _) w a b A t n (add hw _) (.hyp (Or.inl rfl))

theorem instantiate_reject_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A t n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (instantiateInput w a b A t n).neg) : Derives Γ (instantiateExists w a b A t n).neg := by
  apply Derives.impI
  exact .impE (add hi _) (instantiate_input_of_exists (ZFContext.add hZ _) w a b A t n (add hw _) (.hyp (Or.inl rfl)))

theorem abstract_actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (abstractInput w a b A B n)) : Derives Γ (abstractFiber w a b A B n) := by
  let Q := abstracted w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) (SyntaxTopFormulaExistence.abstract_exists hZ w a b A B n hw hi)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hu := SyntaxTopFormulaUnique.abstract_unique_output (ZFContext.under hZ Q) w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc (Fin.last m) hw1 hQ
  have ho := intro_abstract_fiber w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc (Fin.last m) hQ hu
  exact of_eq (abstractFiber_rename w a b A B n Fin.castSucc).symm ho

theorem abstract_input_of_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (abstractExists w a b A B n)) : Derives Γ (abstractInput w a b A B n) := by
  let Q := abstracted w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have ho := SyntaxTopFormulaTyping.abstract_input (ZFContext.under hZ Q) w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc (Fin.last m) hw1 hQ
  exact of_eq (abstractInput_rename w a b A B n Fin.castSucc).symm ho

theorem abstract_exists_of_fiber {m} {Γ : Context m} (w a b A B n : Fin m)
    (he : Derives Γ (abstractFiber w a b A B n)) : Derives Γ (abstractExists w a b A B n) := by
  let Q := (abstracted w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc (Fin.last m)).conj (abstractUnique w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have ho := intro_abstract_exists w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc (Fin.last m) (.conjL hQ)
  exact of_eq (abstractExists_rename w a b A B n Fin.castSucc).symm ho

theorem abstract_exists_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((abstractExists w a b A B n).iff (abstractInput w a b A B n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact abstract_input_of_exists (ZFContext.add hZ _) w a b A B n (add hw _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact SyntaxTopFormulaExistence.abstract_exists (ZFContext.add hZ _) w a b A B n (add hw _) (.hyp (Or.inl rfl))

theorem abstract_fiber_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B n : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((abstractFiber w a b A B n).iff (abstractInput w a b A B n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact abstract_input_of_exists (ZFContext.add hZ _) w a b A B n (add hw _) (abstract_exists_of_fiber w a b A B n (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact abstract_actual_fiber (ZFContext.add hZ _) w a b A B n (add hw _) (.hyp (Or.inl rfl))

theorem abstract_reject_input {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b A B n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (abstractInput w a b A B n).neg) : Derives Γ (abstractExists w a b A B n).neg := by
  apply Derives.impI
  exact .impE (add hi _) (abstract_input_of_exists (ZFContext.add hZ _) w a b A B n (add hw _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.SyntaxTopFormulaFiber
