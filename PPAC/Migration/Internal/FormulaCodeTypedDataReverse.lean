import PPAC.Migration.Internal.FormulaCodeTypedDataOperands

/-! 所有内部候选上TypedData反向识别；原11类完整实际字段检查恢复原FormulaCode。 -/
namespace PPAC.Migration.Internal.FormulaCodeTypedDataReverse
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNumeralSyntax
open FormulaCodeSyntax FormulaCodeTypedDataSyntax FormulaCodeAllowedAritySyntax FormulaCodeTypedDataOperands
open StructuralTreeOperatorSyntax (shape shape_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem root_check {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (ht : tag < 11)
    (w n b f t p l g : Fin m) (hw : Derives Γ (omega w)) (hs : Derives Γ (shape w n t p l g))
    (hnt : Derives Γ (numeral tag t)) (hnl : Derives Γ (numeral (expectedArity tag) l))
    (hcheck : Derives Γ (rootCheck tag w g b f)) : Derives Γ (formulaCode w n b f) := by
  have hh : tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4 ∨ tag = 5 ∨ tag = 6 ∨ tag = 7 ∨ tag = 8 ∨ tag = 9 ∨ tag = 10 := by omega
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Derives Γ (numeral 0 l) at hnl
    exact arity0 hZ 0 (by decide) (by decide) w n b f t p l g hw hs hnt hnl hcheck
  · change Derives Γ (numeral 0 l) at hnl
    exact arity0 hZ 1 (by decide) (by decide) w n b f t p l g hw hs hnt hnl hcheck
  · change Derives Γ (numeral 3 l) at hnl
    exact arity3 hZ 2 (by decide) (by decide) w n b f t p l g hw hs hnt hnl hcheck
  · change Derives Γ (numeral 2 l) at hnl
    exact arity2 hZ 3 (by decide) (by decide) w n b f t p l g hw hs hnt hnl hcheck
  · change Derives Γ (numeral 1 l) at hnl
    exact arity1 hZ 4 (by decide) (by decide) w n b f t p l g hw hs hnt hnl hcheck
  · change Derives Γ (numeral 2 l) at hnl
    exact arity2 hZ 5 (by decide) (by decide) w n b f t p l g hw hs hnt hnl hcheck
  · change Derives Γ (numeral 2 l) at hnl
    exact arity2 hZ 6 (by decide) (by decide) w n b f t p l g hw hs hnt hnl hcheck
  · change Derives Γ (numeral 2 l) at hnl
    exact arity2 hZ 7 (by decide) (by decide) w n b f t p l g hw hs hnt hnl hcheck
  · change Derives Γ (numeral 2 l) at hnl
    exact arity2 hZ 8 (by decide) (by decide) w n b f t p l g hw hs hnt hnl hcheck
  · change Derives Γ (numeral 1 l) at hnl
    exact arity1 hZ 9 (by decide) (by decide) w n b f t p l g hw hs hnt hnl hcheck
  · change Derives Γ (numeral 1 l) at hnl
    exact arity1 hZ 10 (by decide) (by decide) w n b f t p l g hw hs hnt hnl hcheck

theorem cases_imp {m} {Γ : Context m} (k : Nat) (w t l g b f : Fin m) (q : Formula m)
    (hh : ∀ j : Fin k, Derives Γ (((numeral j.val t).conj
      ((numeral (expectedArity j.val) l).conj (rootCheck j.val w g b f))).imp q)) :
    Derives Γ ((cases k w t l g b f).imp q) := by
  induction k with
  | zero => exact .impI (.botE (.hyp (Or.inl rfl)))
  | succ k ih => exact FormulaCodeCaseLogic.disj_imp (ih (fun j => hh j.castSucc)) (hh (Fin.last k))

theorem code_of_cases {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (shape w n t p l g))
    (hc : Derives Γ (cases 11 w t l g b f)) : Derives Γ (formulaCode w n b f) := by
  have hi : Derives Γ ((cases 11 w t l g b f).imp (formulaCode w n b f)) := by
    apply cases_imp
    intro j
    apply Derives.impI
    let B := (numeral j.val t).conj ((numeral (expectedArity j.val) l).conj (rootCheck j.val w g b f))
    have hB : Derives (Context.add B Γ) B := .hyp (Or.inl rfl)
    exact root_check (ZFContext.add hZ B) j.val j.isLt w n b f t p l g (add hw B) (add hs B)
      (.conjL hB) (.conjL (.conjR hB)) (.conjR (.conjR hB))
  exact .impE hi hc

theorem code_of_data {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (typedData w n b f t p l g)) :
    Derives Γ (formulaCode w n b f) :=
  code_of_cases hZ w n b f t p l g hw (.conjL (.conjL hd)) (.conjR (.conjR hd))

theorem data_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (shape w n t p l g)) :
    Derives Γ ((formulaCode w n b f).iff (typedData w n b f t p l g)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact FormulaCodeTypedDataForward.data_of_shape (ZFContext.add hZ _) w n b f t p l g
      (add hw _) (.hyp (Or.inl rfl)) (add hs _)
  · apply Derives.impI
    exact code_of_data (ZFContext.add hZ _) w n b f t p l g (add hw _) (.hyp (Or.inl rfl))

theorem cases_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n b f t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (shape w n t p l g)) :
    Derives Γ ((formulaCode w n b f).iff (cases 11 w t l g b f)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact FormulaCodeTypedDataForward.cases_of_shape (ZFContext.add hZ _) w n b f t p l g
      (add hw _) (.hyp (Or.inl rfl)) (add hs _)
  · apply Derives.impI
    exact code_of_cases (ZFContext.add hZ _) w n b f t p l g (add hw _) (add hs _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.FormulaCodeTypedDataReverse
