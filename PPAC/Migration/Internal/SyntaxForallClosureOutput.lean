import PPAC.Migration.Internal.SyntaxForallClosureTyping

/-! Closed formula outputs and unique fibers; input typing supplies every natural guard. -/
namespace PPAC.Migration.Internal.SyntaxForallClosureOutput
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

def result {m} (w a n z y : Fin m) : Formula m :=
  ((Formula.mem y w).conj (SyntaxUnaryIterationSyntax.forallClosure w a n y)).conj (FormulaCodeSyntax.formulaCode w y z z)

def fiber {m} (w a n z : Fin m) : Formula m := .ex
  ((result w.castSucc a.castSucc n.castSucc z.castSucc (Fin.last m)).conj (.all
    ((SyntaxUnaryIterationSyntax.forallClosure w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

theorem result_rename {m l} (w a n z y : Fin m) (ρ : Fin m → Fin l) :
    (result w a n z y).rename ρ = result (ρ w) (ρ a) (ρ n) (ρ z) (ρ y) := by
  simp only [result, Formula.rename, SyntaxUnaryIterationSyntax.forallClosure_rename, FormulaCodeSyntax.formulaCode_rename]

theorem fiber_rename {m l} (w a n z : Fin m) (ρ : Fin m → Fin l) :
    (fiber w a n z).rename ρ = fiber (ρ w) (ρ a) (ρ n) (ρ z) := by
  simp only [fiber, Formula.rename, result_rename, SyntaxUnaryIterationSyntax.forallClosure_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem closed_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n z y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hz : Derives Γ (empty z)) (hy : Derives Γ (SyntaxUnaryIterationSyntax.forallClosure w a n y)) :
    Derives Γ ((FormulaCodeSyntax.formulaCode w y z z).iff (FormulaCodeSyntax.formulaCode w a n z)) := by
  have hzW := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  exact SyntaxForallClosureTyping.typed_iff hZ w a n z n z y hw ha hzW hn hzW (ZFArithmetic.add_zero hZ w n z hw hn hz) hy

theorem closed_exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a n z : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z))
    (ht : Derives Γ (FormulaCodeSyntax.formulaCode w a n z)) : Derives Γ (fiber w a n z) := by
  have hg := FormulaCodeProperties.guards w a n z ht
  have ha := Derives.conjL hg
  have hn := Derives.conjL (Derives.conjR hg)
  have he := SyntaxUnaryIterationCore.exists_unique hZ 9 w a n hw ha hn
  let Y := ((Formula.mem (Fin.last m) w.castSucc).conj (SyntaxUnaryIterationSyntax.iterate 9 w.castSucc a.castSucc n.castSucc (Fin.last m))).conj
    (.all ((SyntaxUnaryIterationSyntax.iterate 9 w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc)))
  let Δ := Context.add Y (Context.image Formula.raise Γ)
  apply Derives.exE (p := Y) he
  have hZ1 := ZFContext.under hZ Y
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw Y)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz Y)
  have ht1 := of_eq (FormulaCodeSyntax.formulaCode_rename w a n z Fin.castSucc) (under ht Y)
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have hc := Derives.impE (.conjR (closed_iff hZ1 w.castSucc a.castSucc n.castSucc z.castSucc (Fin.last m)
    hw1 (under ha Y) (under hn Y) hz1 (.conjR (.conjL hY)))) ht1
  have ho : Derives Δ (fiber w.castSucc a.castSucc n.castSucc z.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, result_rename,
      SyntaxUnaryIterationSyntax.forallClosure_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]; rfl)
      (.conjI (.conjI (.conjL hY) hc) (.conjR hY))
  exact of_eq (by simp only [Formula.raise, fiber_rename]) ho

end PPAC.Migration.Internal.SyntaxForallClosureOutput
