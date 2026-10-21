import PPAC.Migration.Internal.SyntaxCheckedSlotExists

/-! 原11个RootCheck实际给出每个所需槽位；类型谓词保留在原检查中。 -/
namespace PPAC.Migration.Internal.FormulaCodeRootSlots
open Source SourceAlgebra SourceLogic SyntaxAtomSyntax FormulaCodeGraphTyping FormulaCodeTypedFields
open FormulaCodeTypedDataSyntax FormulaCodeAllowedAritySyntax SyntaxCheckedSlotExists

theorem slot_exists {m} {Γ : Context m} (tag : Nat) (ht : tag < 11) (w g b f : Fin m)
    (j : Fin (expectedArity tag)) (hc : Derives Γ (rootCheck tag w g b f)) : Derives Γ (existsSlot g j.val) := by
  have hh : tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4 ∨ tag = 5 ∨ tag = 6 ∨ tag = 7 ∨ tag = 8 ∨ tag = 9 ∨ tag = 10 := by omega
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Fin 0 at j
    exact Fin.elim0 j
  · change Fin 0 at j
    exact Fin.elim0 j
  · change Fin 3 at j
    change Derives Γ (memberCheck w g b f) at hc
    have hj : j = (0 : Fin 3) ∨ j = (1 : Fin 3) ∨ j = (2 : Fin 3) := by omega
    rcases hj with rfl | rfl | rfl
    · exact of_checked zeroMatrix (fun _ => w) g 0 (.conjL hc)
    · exact of_checked termMatrix (three w b f) g 1 (.conjL (.conjR hc))
    · exact of_checked termMatrix (three w b f) g 2 (.conjR (.conjR hc))
  · change Fin 2 at j
    change Derives Γ (equalCheck w g b f) at hc
    have hj : j = (0 : Fin 2) ∨ j = (1 : Fin 2) := by omega
    rcases hj with rfl | rfl
    · exact of_checked termMatrix (three w b f) g 0 (.conjL hc)
    · exact of_checked termMatrix (three w b f) g 1 (.conjR hc)
  · change Fin 1 at j
    change Derives Γ (singleCheck false w g b f) at hc
    have hj : j = (0 : Fin 1) := by omega
    subst j
    exact of_checked codeMatrix (three w b f) g 0 (.conjR hc)
  · change Fin 2 at j
    change Derives Γ (binaryCheck w g b f) at hc
    have hj : j = (0 : Fin 2) ∨ j = (1 : Fin 2) := by omega
    rcases hj with rfl | rfl
    · exact of_checked codeMatrix (three w b f) g 0 (.conjL (.conjR hc))
    · exact of_checked codeMatrix (three w b f) g 1 (.conjR (.conjR hc))
  · change Fin 2 at j
    change Derives Γ (binaryCheck w g b f) at hc
    have hj : j = (0 : Fin 2) ∨ j = (1 : Fin 2) := by omega
    rcases hj with rfl | rfl
    · exact of_checked codeMatrix (three w b f) g 0 (.conjL (.conjR hc))
    · exact of_checked codeMatrix (three w b f) g 1 (.conjR (.conjR hc))
  · change Fin 2 at j
    change Derives Γ (binaryCheck w g b f) at hc
    have hj : j = (0 : Fin 2) ∨ j = (1 : Fin 2) := by omega
    rcases hj with rfl | rfl
    · exact of_checked codeMatrix (three w b f) g 0 (.conjL (.conjR hc))
    · exact of_checked codeMatrix (three w b f) g 1 (.conjR (.conjR hc))
  · change Fin 2 at j
    change Derives Γ (binaryCheck w g b f) at hc
    have hj : j = (0 : Fin 2) ∨ j = (1 : Fin 2) := by omega
    rcases hj with rfl | rfl
    · exact of_checked codeMatrix (three w b f) g 0 (.conjL (.conjR hc))
    · exact of_checked codeMatrix (three w b f) g 1 (.conjR (.conjR hc))
  · change Fin 1 at j
    change Derives Γ (singleCheck true w g b f) at hc
    have hj : j = (0 : Fin 1) := by omega
    subst j
    exact of_checked advancedMatrix (three w b f) g 0 (.conjR hc)
  · change Fin 1 at j
    change Derives Γ (singleCheck true w g b f) at hc
    have hj : j = (0 : Fin 1) := by omega
    subst j
    exact of_checked advancedMatrix (three w b f) g 0 (.conjR hc)

theorem at_arity {m} {Γ : Context m} (k tag : Nat) (ht : tag < 11) (hk : k = expectedArity tag)
    (w g b f : Fin m) (j : Fin k) (hc : Derives Γ (rootCheck tag w g b f)) : Derives Γ (existsSlot g j.val) := by
  subst k
  exact slot_exists tag ht w g b f j hc

theorem code_at_arity {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (ht : tag < 11)
    (hk : k = expectedArity tag) (w n b f t p l g : Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (OmegaSyntax.omega w)) (hs : Derives Γ (StructuralTreeOperatorSyntax.shape w n t p l g))
    (hnt : Derives Γ (SyntaxNumeralSyntax.numeral tag t)) (hnl : Derives Γ (SyntaxNumeralSyntax.numeral k l))
    (hslots : Derives Γ (SyntaxFieldsFromSlots.slots k g xs))
    (hcheck : Derives Γ (rootCheck tag w g b f)) : Derives Γ (FormulaCodeSyntax.formulaCode w n b f) := by
  subst k
  exact FormulaCodeTypedDataKnown.from_slots hZ tag ht w n b f t p l g xs hw hs hnt hnl hslots hcheck
end PPAC.Migration.Internal.FormulaCodeRootSlots
