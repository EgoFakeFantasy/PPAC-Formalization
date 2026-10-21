import PPAC.Migration.Internal.NaturalMultiplicationCore

/-! 积的零点与双向后继律；加法关系由前述闭句证书正式支持。 -/
namespace PPAC.Migration.Internal.NaturalMultiplicationLaws
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax ReplacementPredicates NaturalMultiplicationSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem empty_subst {m} {Γ : Context m} (x y : Fin m) (he : Derives Γ (.equal x y))
    (hx : Derives Γ (empty x)) : Derives Γ (empty y) := by
  have hi : Derives Γ ((empty (Fin.last m)).instantiate x) := by
    simpa only [Formula.instantiate, empty_rename, Fin.lastCases_last] using hx
  have ho := Derives.eqSubst (empty (Fin.last m)) he hi
  simpa only [Formula.instantiate, empty_rename, Fin.lastCases_last] using ho

theorem zero_forward {m} {Γ : Context m} (w a n y : Fin m)
    (hn : Derives Γ (empty n)) (hy : Derives Γ (product w a n y)) : Derives Γ (empty y) := by
  let Y := (empty (Fin.last m)).conj (NaturalEvaluationSyntax.evaluation NaturalMultiplicationStep.matrix
    (paramsUp (params w a)) w.castSucc (Fin.last m) n.castSucc y.castSucc)
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hnY : Derives Ξ (empty n.castSucc) := by simpa only [Formula.raise, empty_rename] using under hn Y
  have heq := NaturalRecursionLaws.evaluation_zero NaturalMultiplicationStep.matrix (paramsUp (params w a))
    w.castSucc (Fin.last m) n.castSucc y.castSucc hnY (.conjR hY)
  simpa only [Formula.raise, empty_rename] using empty_subst (Fin.last m) y.castSucc (eq_symm heq) (.conjL hY)

theorem zero_backward {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n y : Fin m)
    (hAdd : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hMul : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalMultiplicationStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (empty n))
    (hy : Derives Γ (empty y)) : Derives Γ (product w a n y) := by
  have hnW := OmegaStructureAlgebra.zero_member w n hA.base.extensionality hw hn
  have ht := NaturalMultiplicationCore.exists_product hA w a n hAdd hMul hw ha hnW
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (product w.castSucc a.castSucc n.castSucc (Fin.last m))
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at ht
  apply Derives.exE (p := T) ht
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hnT : Derives Ξ (empty n.castSucc) := by simpa only [Formula.raise, empty_rename] using under hn T
  have hyT : Derives Ξ (empty y.castSucc) := by simpa only [Formula.raise, empty_rename] using under hy T
  have hextT : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hA.base.extensionality T
  have heq := OmegaUniversal.empty_unique (Fin.last m) y.castSucc hextT (zero_forward _ _ _ _ hnT (.conjR hT)) hyT
  simpa only [Formula.raise, product_rename] using output_subst _ _ _ _ _ heq (.conjR hT)

theorem zero_iff {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n y : Fin m)
    (hAdd : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hMul : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalMultiplicationStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (empty n)) :
    Derives Γ ((product w a n y).iff (empty y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact zero_forward w a n y (add hn _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact zero_backward (ArithmeticContext.add hA _) w a n y (add hAdd _) (add hMul _) (add hw _) (add ha _) (add hn _) (.hyp (Or.inl rfl))

theorem successor_forward {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n s y z : Fin m)
    (hAdd : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hMul : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalMultiplicationStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hs : Derives Γ (successor s n)) (hy : Derives Γ (product w a n y)) (hz : Derives Γ (product w a s z)) :
    Derives Γ (NaturalAdditionSyntax.sum w y a z) := by
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Ξ := Context.add E (Context.image Formula.raise Γ)
  have hzero : Derives Γ (.ex E) := .conjL (.conjL hw)
  apply Derives.exE (p := E) hzero
  have hA' : ArithmeticContext.Evidence Ξ := ArithmeticContext.under hA E
  have he : Derives Ξ (empty (Fin.last m)) := .conjR (.hyp (Or.inl rfl))
  have hAdd' : Derives Ξ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hAdd E
  have hMul' : Derives Ξ ((NaturalRecursion.uniquenessSentence NaturalMultiplicationStep.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hMul E
  have hw' : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw E
  have hs' : Derives Ξ (successor s.castSucc n.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs E
  have hy' : Derives Ξ (product w.castSucc a.castSucc n.castSucc y.castSucc) := by
    simpa only [Formula.raise, product_rename] using under hy E
  have hz' : Derives Ξ (product w.castSucc a.castSucc s.castSucc z.castSucc) := by
    simpa only [Formula.raise, product_rename] using under hz E
  have hyW := NaturalMultiplicationCore.closure _ _ _ _ hA'.base.extensionality hw' hy'
  have hrel := NaturalEvaluationStep.evaluation_step hA' NaturalMultiplicationStep.matrix (params w.castSucc a.castSucc)
    w.castSucc (Fin.last m) n.castSucc s.castSucc y.castSucc z.castSucc hw' (under hn E) hs'
    (OmegaOrdinals.elements w.castSucc hA'.base.foundation hA'.ordinalSeparation hw')
    (NaturalMultiplicationCore.recursors hA' _ _ _ hAdd' hMul' hw' (under ha E))
    (NaturalMultiplicationCore.evaluation_at_zero _ _ _ _ _ hA'.base.extensionality he hy')
    (NaturalMultiplicationCore.evaluation_at_zero _ _ _ _ _ hA'.base.extensionality he hz')
  have hst : Derives Ξ (NaturalMultiplicationStep.step w.castSucc a.castSucc y.castSucc z.castSucc) := by
    simpa only [NaturalMultiplicationStep.matrix_rel, params_0, params_1] using hrel
  simpa only [Formula.raise, NaturalAdditionSyntax.sum_rename] using NaturalMultiplicationStep.on_natural _ _ _ _ hyW hst

theorem successor_backward {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n s y z : Fin m)
    (hAdd : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hMul : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalMultiplicationStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hs : Derives Γ (successor s n)) (hy : Derives Γ (product w a n y)) (hz : Derives Γ (NaturalAdditionSyntax.sum w y a z)) :
    Derives Γ (product w a s z) := by
  have hsW := OmegaStructureAlgebra.successor_member w s n hA.base.extensionality hw hn hs
  have ht := NaturalMultiplicationCore.exists_product hA w a s hAdd hMul hw ha hsW
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (product w.castSucc a.castSucc s.castSucc (Fin.last m))
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at ht
  apply Derives.exE (p := T) ht
  have hAT : ArithmeticContext.Evidence Ξ := ArithmeticContext.under hA T
  have hAddT : Derives Ξ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hAdd T
  have hMulT : Derives Ξ ((NaturalRecursion.uniquenessSentence NaturalMultiplicationStep.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hMul T
  have hwT : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw T
  have hsT : Derives Ξ (successor s.castSucc n.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs T
  have hyT : Derives Ξ (product w.castSucc a.castSucc n.castSucc y.castSucc) := by
    simpa only [Formula.raise, product_rename] using under hy T
  have hzT : Derives Ξ (NaturalAdditionSyntax.sum w.castSucc y.castSucc a.castSucc z.castSucc) := by
    simpa only [Formula.raise, NaturalAdditionSyntax.sum_rename] using under hz T
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hsum := successor_forward hAT _ _ _ _ _ _ hAddT hMulT hwT (under ha T) (under hn T) hsT hyT (.conjR hT)
  have heq := NaturalAdditionCore.unique hAT w.castSucc y.castSucc a.castSucc (Fin.last m) z.castSucc hAddT hwT (under ha T) hsum hzT
  simpa only [Formula.raise, product_rename] using output_subst _ _ _ _ _ heq (.conjR hT)

theorem successor_iff {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n s y z : Fin m)
    (hAdd : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hMul : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalMultiplicationStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hs : Derives Γ (successor s n)) (hy : Derives Γ (product w a n y)) :
    Derives Γ ((product w a s z).iff (NaturalAdditionSyntax.sum w y a z)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact successor_forward (ArithmeticContext.add hA _) w a n s y z (add hAdd _) (add hMul _) (add hw _) (add ha _) (add hn _) (add hs _) (add hy _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact successor_backward (ArithmeticContext.add hA _) w a n s y z (add hAdd _) (add hMul _) (add hw _) (add ha _) (add hn _) (add hs _) (add hy _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.NaturalMultiplicationLaws
