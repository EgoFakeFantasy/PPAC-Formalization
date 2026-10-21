import PPAC.Migration.Internal.NaturalAdditionSyntax

/-! 在所有内部自然数上取得实际自然数和、唯一性及值域闭包；最终背景消去原递推证书参数。 -/
namespace PPAC.Migration.Internal.NaturalAdditionCore
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax OrdinalSyntax ReplacementPredicates
open NaturalAdditionSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem recursors {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) : Derives Γ (OrdinalRecursionExistenceSyntax.allUnique
      (NaturalRecursionSyntax.matrix NaturalSuccessorStep.matrix) (NaturalRecursionSyntax.extend (params w) w a)) :=
  ObjectNaturalRecursion.instantiate_unique NaturalSuccessorStep.matrix (params w) w a hc hw
    (NaturalSuccessorStep.total (params w) hw) (NaturalSuccessorStep.functional (params w) hA.base.extensionality)

theorem closure {m} {Γ : Context m} (w a n y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hy : Derives Γ (sum w a n y)) : Derives Γ (.mem y w) :=
  NaturalEvaluationRange.evaluation_range NaturalSuccessorStep.matrix (params w) w a n y w ha
    (NaturalSuccessorStep.range (params w) he hw) hy

theorem unique {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n y z : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hy : Derives Γ (sum w a n y)) (hz : Derives Γ (sum w a n z)) : Derives Γ (.equal y z) :=
  NaturalEvaluationUniqueness.evaluation_unique NaturalSuccessorStep.matrix (params w) w a n y z hA.base.extensionality hw hn
    (OmegaOrdinals.elements w hA.base.foundation hA.ordinalSeparation hw) (recursors hA w a hc hw) hy hz

theorem exists_unique {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w)) : Derives Γ (fiber w a n) := by
  have hy := NaturalEvaluationFiber.at_natural NaturalSuccessorStep.matrix (params w) w a n hA.base.extensionality hw hn
    (OmegaOrdinals.elements w hA.base.foundation hA.ordinalSeparation hw) (recursors hA w a hc hw)
  let Y := (sum w.castSucc a.castSucc n.castSucc (Fin.last m)).conj (.all
    ((sum w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc)))
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have heY : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hA.base.extensionality Y
  have hwY : Derives Ξ (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw Y
  have haY : Derives Ξ (.mem a.castSucc w.castSucc) := under ha Y
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hm := closure w.castSucc a.castSucc n.castSucc (Fin.last m) heY hwY haY (.conjL hY)
  have hout : Derives Ξ (fiber w.castSucc a.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, sum_rename, Formula.liftRen,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI (.conjI hm (.conjL hY)) (.conjR hY)
  simpa only [Formula.raise, NaturalAdditionSyntax.fiber_rename] using hout

theorem exists_sum {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w)) : Derives Γ (existsSum w a n) := by
  have hy := exists_unique hA w a n hc hw ha hn
  let Y := ((Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc a.castSucc n.castSucc (Fin.last m))).conj (.all
    ((sum w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc)))
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  simpa only [Formula.raise, existsSum_rename] using intro_exists w.castSucc a.castSucc n.castSucc (Fin.last m) (.conjL (.conjL hY)) (.conjR (.conjL hY))
end PPAC.Migration.Internal.NaturalAdditionCore
