import PPAC.Migration.Internal.SyntaxForestFromFields

/-! 任意原有限字段向量上的11类真实图类型双条件；供反向存在消去复用。 -/
namespace PPAC.Migration.Internal.FormulaCodeTypedDataKnown
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxAtomSyntax SyntaxLogicalSyntax
open FormulaCodeSyntax FormulaCodeTypedDataSyntax FormulaCodeAllowedAritySyntax FormulaCodeGraphTyping
open StructuralTreeOperatorSyntax (shape)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem empty_eta {α} (xs : Fin 0 → α) : xs = Fin.elim0 := by funext j; exact Fin.elim0 j

theorem one_eta {α} (xs : Fin 1 → α) : (fun _ : Fin 1 => xs 0) = xs := by
  funext j
  have hj : j = 0 := by omega
  subst j
  rfl

theorem two_eta {α} (xs : Fin 2 → α) : Fin.cases (xs 0) (Fin.cases (xs 1) Fin.elim0) = xs := by
  funext j
  refine Fin.cases rfl (fun i => ?_) j
  exact Fin.cases rfl (fun q => Fin.elim0 q) i

theorem three_eta {α} (xs : Fin 3 → α) :
    Fin.cases (xs 0) (Fin.cases (xs 1) (Fin.cases (xs 2) Fin.elim0)) = xs := by
  funext j
  refine Fin.cases rfl (fun i => ?_) j
  refine Fin.cases rfl (fun i => ?_) i
  exact Fin.cases rfl (fun q => Fin.elim0 q) i

theorem known_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (ht : tag < 11)
    (w n b f t p l g : Fin m) (xs : Fin (expectedArity tag) → Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (constructor (expectedArity tag) tag w xs n))
    (hs : Derives Γ (shape w n t p l g)) :
    Derives Γ ((formulaCode w n b f).iff (rootCheck tag w g b f)) := by
  have hh : tag = 0 ∨ tag = 1 ∨ tag = 2 ∨ tag = 3 ∨ tag = 4 ∨ tag = 5 ∨ tag = 6 ∨ tag = 7 ∨ tag = 8 ∨ tag = 9 ∨ tag = 10 := by omega
  rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change Fin 0 → Fin m at xs
    change Derives Γ (constructor 0 0 w xs n) at hc
    have h := FormulaCodeKnownAtomic.nullary_iff hZ false w b f n hw (by simpa only [nullaryTag, Bool.false_eq_true, ↓reduceIte, empty_eta] using hc)
    exact h
  · change Fin 0 → Fin m at xs
    change Derives Γ (constructor 0 1 w xs n) at hc
    have h := FormulaCodeKnownAtomic.nullary_iff hZ true w b f n hw (by simpa only [nullaryTag, ↓reduceIte, empty_eta] using hc)
    exact h
  · change Fin 3 → Fin m at xs
    change Derives Γ (constructor 3 2 w xs n) at hc
    have hctor : Derives Γ (memberCode w (xs 0) (xs 1) (xs 2) n) := by
      change Derives Γ (constructor 3 2 w (three (xs 0) (xs 1) (xs 2)) n)
      rw [show three (xs 0) (xs 1) (xs 2) = xs from three_eta xs]
      exact hc
    exact FormulaCodeGraphTyping.membership hZ w n b f (xs 0) (xs 1) (xs 2) t p l g hw hctor hs
  · change Fin 2 → Fin m at xs
    change Derives Γ (constructor 2 3 w xs n) at hc
    have hctor : Derives Γ (equalCode w (xs 0) (xs 1) n) := by
      change Derives Γ (constructor 2 3 w (two (xs 0) (xs 1)) n)
      rw [show two (xs 0) (xs 1) = xs from two_eta xs]
      exact hc
    exact FormulaCodeGraphTyping.equality hZ w n b f (xs 0) (xs 1) t p l g hw hctor hs
  · change Fin 1 → Fin m at xs
    change Derives Γ (constructor 1 4 w xs n) at hc
    have hctor : Derives Γ (singleCode 4 w (xs 0) n) := by
      simpa only [singleCode, one_eta] using hc
    exact FormulaCodeGraphTyping.negation hZ w n b f (xs 0) t p l g hw hctor hs
  · change Fin 2 → Fin m at xs
    change Derives Γ (constructor 2 5 w xs n) at hc
    have hctor : Derives Γ (binaryCode 0 w (xs 0) (xs 1) n) := by
      change Derives Γ (constructor 2 5 w (two (xs 0) (xs 1)) n)
      rw [show two (xs 0) (xs 1) = xs from two_eta xs]
      exact hc
    exact FormulaCodeGraphTyping.binary hZ 0 w n b f (xs 0) (xs 1) t p l g hw hctor hs
  · change Fin 2 → Fin m at xs
    change Derives Γ (constructor 2 6 w xs n) at hc
    have hctor : Derives Γ (binaryCode 1 w (xs 0) (xs 1) n) := by
      change Derives Γ (constructor 2 6 w (two (xs 0) (xs 1)) n)
      rw [show two (xs 0) (xs 1) = xs from two_eta xs]
      exact hc
    exact FormulaCodeGraphTyping.binary hZ 1 w n b f (xs 0) (xs 1) t p l g hw hctor hs
  · change Fin 2 → Fin m at xs
    change Derives Γ (constructor 2 7 w xs n) at hc
    have hctor : Derives Γ (binaryCode 2 w (xs 0) (xs 1) n) := by
      change Derives Γ (constructor 2 7 w (two (xs 0) (xs 1)) n)
      rw [show two (xs 0) (xs 1) = xs from two_eta xs]
      exact hc
    exact FormulaCodeGraphTyping.binary hZ 2 w n b f (xs 0) (xs 1) t p l g hw hctor hs
  · change Fin 2 → Fin m at xs
    change Derives Γ (constructor 2 8 w xs n) at hc
    have hctor : Derives Γ (binaryCode 3 w (xs 0) (xs 1) n) := by
      change Derives Γ (constructor 2 8 w (two (xs 0) (xs 1)) n)
      rw [show two (xs 0) (xs 1) = xs from two_eta xs]
      exact hc
    exact FormulaCodeGraphTyping.binary hZ 3 w n b f (xs 0) (xs 1) t p l g hw hctor hs
  · change Fin 1 → Fin m at xs
    change Derives Γ (constructor 1 9 w xs n) at hc
    have hctor : Derives Γ (singleCode (quantifierTag true) w (xs 0) n) := by
      change Derives Γ (constructor 1 9 w (fun _ => xs 0) n)
      rw [one_eta]
      exact hc
    exact FormulaCodeGraphTyping.quantifier hZ true w n b f (xs 0) t p l g hw hctor hs
  · change Fin 1 → Fin m at xs
    change Derives Γ (constructor 1 10 w xs n) at hc
    have hctor : Derives Γ (singleCode (quantifierTag false) w (xs 0) n) := by
      change Derives Γ (constructor 1 10 w (fun _ => xs 0) n)
      rw [one_eta]
      exact hc
    exact FormulaCodeGraphTyping.quantifier hZ false w n b f (xs 0) t p l g hw hctor hs

theorem from_slots {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (ht : tag < 11)
    (w n b f t p l g : Fin m) (xs : Fin (expectedArity tag) → Fin m)
    (hw : Derives Γ (omega w)) (hs : Derives Γ (shape w n t p l g))
    (hnt : Derives Γ (SyntaxNumeralSyntax.numeral tag t))
    (hnl : Derives Γ (SyntaxNumeralSyntax.numeral (expectedArity tag) l))
    (hslots : Derives Γ (SyntaxFieldsFromSlots.slots (expectedArity tag) g xs))
    (hcheck : Derives Γ (rootCheck tag w g b f)) : Derives Γ (formulaCode w n b f) := by
  have hc := SyntaxForestFromFields.constructor_of_shape hZ (expectedArity tag) tag w n t p l g xs hw hs hnt hnl hslots
  exact .impE (.conjR (known_iff hZ tag ht w n b f t p l g xs hw hc hs)) hcheck
end PPAC.Migration.Internal.FormulaCodeTypedDataKnown
