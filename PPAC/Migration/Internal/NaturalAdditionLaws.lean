import PPAC.Migration.Internal.NaturalAdditionCore

/-! 加法的真实零点与双向后继递推律，域和所有见证均保持对象量词。 -/
namespace PPAC.Migration.Internal.NaturalAdditionLaws
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax ReplacementPredicates NaturalAdditionSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero_value {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a z : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hz : Derives Γ (empty z)) : Derives Γ (sum w a z a) := by
  have hzW := OmegaStructureAlgebra.zero_member w z hA.base.extensionality hw hz
  have hy := NaturalAdditionCore.exists_sum hA w a z hc hw ha hzW
  let Y := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc a.castSucc z.castSucc (Fin.last m))
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hzY : Derives Ξ (empty z.castSucc) := by
    simpa only [Formula.raise, empty_rename] using under hz Y
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have heq := NaturalRecursionLaws.evaluation_zero NaturalSuccessorStep.matrix (params w.castSucc) w.castSucc a.castSucc z.castSucc (Fin.last m) hzY (.conjR hY)
  simpa only [Formula.raise, sum_rename] using output_subst w.castSucc a.castSucc z.castSucc (Fin.last m) a.castSucc heq (.conjR hY)

theorem zero_iff {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a z y : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hz : Derives Γ (empty z)) :
    Derives Γ ((sum w a z y).iff (.equal y a)) := by
  have hza := zero_value hA w a z hc hw ha hz
  apply Derives.conjI
  · apply Derives.impI
    exact NaturalRecursionLaws.evaluation_zero NaturalSuccessorStep.matrix (params w) w a z y (add hz _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact output_subst w a z a y (eq_symm (.hyp (Or.inl rfl))) (add hza _)

theorem successor_forward {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n s y z : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hs : Derives Γ (successor s n)) (hy : Derives Γ (sum w a n y)) (hz : Derives Γ (sum w a s z)) :
    Derives Γ (successor z y) := by
  have hyW := NaturalAdditionCore.closure w a n y hA.base.extensionality hw ha hy
  have hrel := NaturalEvaluationStep.evaluation_step hA NaturalSuccessorStep.matrix (params w) w a n s y z hw hn hs
    (OmegaOrdinals.elements w hA.base.foundation hA.ordinalSeparation hw) (NaturalAdditionCore.recursors hA w a hc hw) hy hz
  have hstep : Derives Γ (NaturalSuccessorStep.step w y z) := by
    simpa only [NaturalSuccessorStep.matrix_rel, params] using hrel
  exact NaturalSuccessorStep.on_natural w y z hyW hstep

theorem successor_backward {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n s y z : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hs : Derives Γ (successor s n)) (hy : Derives Γ (sum w a n y)) (hz : Derives Γ (successor z y)) :
    Derives Γ (sum w a s z) := by
  have hsW := OmegaStructureAlgebra.successor_member w s n hA.base.extensionality hw hn hs
  have ht := NaturalAdditionCore.exists_sum hA w a s hc hw ha hsW
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc a.castSucc s.castSucc (Fin.last m))
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at ht
  apply Derives.exE (p := T) ht
  have hAT := ArithmeticContext.under hA T
  have hcT : Derives Ξ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hc T
  have hwT : Derives Ξ (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw T
  have haT : Derives Ξ (.mem a.castSucc w.castSucc) := under ha T
  have hnT : Derives Ξ (.mem n.castSucc w.castSucc) := under hn T
  have hsT : Derives Ξ (successor s.castSucc n.castSucc) := by
    simpa only [Formula.raise, successor_rename] using under hs T
  have hyT : Derives Ξ (sum w.castSucc a.castSucc n.castSucc y.castSucc) := by
    simpa only [Formula.raise, sum_rename] using under hy T
  have hzT : Derives Ξ (successor z.castSucc y.castSucc) := by
    simpa only [Formula.raise, successor_rename] using under hz T
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hty := successor_forward hAT w.castSucc a.castSucc n.castSucc s.castSucc y.castSucc (Fin.last m) hcT hwT haT hnT hsT hyT (.conjR hT)
  have heq := OmegaUniversal.successor_unique (Fin.last m) z.castSucc y.castSucc hAT.base.extensionality hty hzT
  simpa only [Formula.raise, sum_rename] using output_subst w.castSucc a.castSucc s.castSucc (Fin.last m) z.castSucc heq (.conjR hT)

theorem successor_iff {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n s y z : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hs : Derives Γ (successor s n)) (hy : Derives Γ (sum w a n y)) :
    Derives Γ ((sum w a s z).iff (successor z y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact successor_forward (ArithmeticContext.add hA _) w a n s y z (add hc _) (add hw _) (add ha _) (add hn _) (add hs _) (add hy _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact successor_backward (ArithmeticContext.add hA _) w a n s y z (add hc _) (add hw _) (add ha _) (add hn _) (add hs _) (add hy _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.NaturalAdditionLaws
