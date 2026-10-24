import PPAC.Migration.Internal.SyntaxUnaryIterationSyntax

/-! Total, unique natural-valued iteration at every internal omega index. -/
namespace PPAC.Migration.Internal.SyntaxUnaryIterationCore
open Source SourceAlgebra SourceLogic OmegaSyntax ReplacementPredicates SyntaxUnaryIterationSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem recursors {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w a : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (OrdinalRecursionExistenceSyntax.allUnique
      (NaturalRecursionSyntax.matrix (SyntaxUnaryIterationStep.matrix tag)) (NaturalRecursionSyntax.extend (params w) w a)) :=
  ObjectNaturalRecursion.instantiate_unique (SyntaxUnaryIterationStep.matrix tag) (params w) w a
    (ZFContext.closed hZ (NaturalRecursion.source_uniqueness (SyntaxUnaryIterationStep.matrix tag))) hw
    (SyntaxUnaryIterationStep.total hZ tag (params w) hw) (SyntaxUnaryIterationStep.functional hZ tag (params w) hw)

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w a n y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hy : Derives Γ (iterate tag w a n y)) : Derives Γ (.mem y w) :=
  NaturalEvaluationRange.evaluation_range (SyntaxUnaryIterationStep.matrix tag) (params w) w a n y w ha
    (SyntaxUnaryIterationStep.range hZ tag (params w) hw) hy

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w a n y z : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hy : Derives Γ (iterate tag w a n y)) (hz : Derives Γ (iterate tag w a n z)) : Derives Γ (.equal y z) :=
  NaturalEvaluationUniqueness.evaluation_unique (SyntaxUnaryIterationStep.matrix tag) (params w) w a n y z
    (ZFContext.arithmetic hZ).base.extensionality hw hn
    (OmegaOrdinals.elements w (ZFContext.arithmetic hZ).base.foundation (ZFContext.arithmetic hZ).ordinalSeparation hw)
    (recursors hZ tag w a hw) hy hz

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w a n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w)) : Derives Γ (fiber tag w a n) := by
  have hy := NaturalEvaluationFiber.at_natural (SyntaxUnaryIterationStep.matrix tag) (params w) w a n
    (ZFContext.arithmetic hZ).base.extensionality hw hn
    (OmegaOrdinals.elements w (ZFContext.arithmetic hZ).base.foundation (ZFContext.arithmetic hZ).ordinalSeparation hw)
    (recursors hZ tag w a hw)
  let Y := (iterate tag w.castSucc a.castSucc n.castSucc (Fin.last m)).conj (.all
    ((iterate tag w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc)))
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hwY := of_eq (omega_rename w Fin.castSucc) (under hw Y)
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hm := range (ZFContext.under hZ Y) tag w.castSucc a.castSucc n.castSucc (Fin.last m) hwY (under ha Y) (.conjL hY)
  have ho : Derives Ξ (fiber tag w.castSucc a.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, Formula.rename, iterate_rename, Formula.liftRen,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI (.conjI hm (.conjL hY)) (.conjR hY))
  exact of_eq (by simp only [Formula.raise, SyntaxUnaryIterationSyntax.fiber_rename]) ho

theorem exists_iteration {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (w a n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w)) : Derives Γ (existsIteration tag w a n) := by
  have hy := exists_unique hZ tag w a n hw ha hn
  let Y := ((Formula.mem (Fin.last m) w.castSucc).conj (iterate tag w.castSucc a.castSucc n.castSucc (Fin.last m))).conj (.all
    ((iterate tag w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc)))
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  exact of_eq (by simp only [Formula.raise, existsIteration_rename])
    (intro_exists tag w.castSucc a.castSucc n.castSucc (Fin.last m) (.conjL (.conjL hY)) (.conjR (.conjL hY)))

end PPAC.Migration.Internal.SyntaxUnaryIterationCore
