import PPAC.Migration.Internal.NaturalMultiplicationSyntax

/-! 全部内部自然索引上的实际积。两个零见证先在原核内证明相等，再比较递推末值。 -/
namespace PPAC.Migration.Internal.NaturalMultiplicationCore
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax OrdinalSyntax ReplacementPredicates
open NaturalMultiplicationSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem recursors {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a e : Fin m)
    (hAdd : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hMul : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalMultiplicationStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) : Derives Γ (OrdinalRecursionExistenceSyntax.allUnique
      (NaturalRecursionSyntax.matrix NaturalMultiplicationStep.matrix) (NaturalRecursionSyntax.extend (params w a) w e)) :=
  ObjectNaturalRecursion.instantiate_unique NaturalMultiplicationStep.matrix (params w a) w e hMul hw
    (NaturalMultiplicationStep.total hA (params w a) hAdd hw ha)
    (NaturalMultiplicationStep.functional hA (params w a) hAdd hw ha)

theorem evaluation_at_zero {m} {Γ : Context m} (w a n y e : Fin m)
    (hext : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (he : Derives Γ (empty e)) (hy : Derives Γ (product w a n y)) :
    Derives Γ (NaturalEvaluationSyntax.evaluation NaturalMultiplicationStep.matrix (params w a) w e n y) := by
  let Y := (empty (Fin.last m)).conj (NaturalEvaluationSyntax.evaluation NaturalMultiplicationStep.matrix
    (paramsUp (params w a)) w.castSucc (Fin.last m) n.castSucc y.castSucc)
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hextY : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hext Y
  have heY : Derives Ξ (empty e.castSucc) := by
    simpa only [Formula.raise, empty_rename] using under he Y
  have heq := OmegaUniversal.empty_unique (Fin.last m) e.castSucc hextY (.conjL hY) heY
  have hout := initial_subst NaturalMultiplicationStep.matrix (paramsUp (params w a)) w.castSucc
    (Fin.last m) e.castSucc n.castSucc y.castSucc heq (.conjR hY)
  have hp : paramsUp (params w a) = params w.castSucc a.castSucc := params_rename w a Fin.castSucc
  rw [hp] at hout
  simpa only [Formula.raise, NaturalEvaluationSyntax.evaluation_rename, params_rename] using hout

theorem closure {m} {Γ : Context m} (w a n y : Fin m)
    (hext : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hw : Derives Γ (omega w)) (hy : Derives Γ (product w a n y)) : Derives Γ (.mem y w) := by
  let Y := (empty (Fin.last m)).conj (NaturalEvaluationSyntax.evaluation NaturalMultiplicationStep.matrix
    (paramsUp (params w a)) w.castSucc (Fin.last m) n.castSucc y.castSucc)
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hextY : Derives Ξ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hext Y
  have hwY : Derives Ξ (omega w.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw Y
  have hew := OmegaStructureAlgebra.zero_member w.castSucc (Fin.last m) hextY hwY (.conjL hY)
  exact NaturalEvaluationRange.evaluation_range NaturalMultiplicationStep.matrix (paramsUp (params w a)) w.castSucc
    (Fin.last m) n.castSucc y.castSucc w.castSucc hew
    (NaturalMultiplicationStep.range (paramsUp (params w a)) hextY hwY) (.conjR hY)

theorem unique {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n y z : Fin m)
    (hAdd : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hMul : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalMultiplicationStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w))
    (hy : Derives Γ (product w a n y)) (hz : Derives Γ (product w a n z)) : Derives Γ (.equal y z) := by
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
  have hy' : Derives Ξ (product w.castSucc a.castSucc n.castSucc y.castSucc) := by
    simpa only [Formula.raise, product_rename] using under hy E
  have hz' : Derives Ξ (product w.castSucc a.castSucc n.castSucc z.castSucc) := by
    simpa only [Formula.raise, product_rename] using under hz E
  exact NaturalEvaluationUniqueness.evaluation_unique NaturalMultiplicationStep.matrix (params w.castSucc a.castSucc)
    w.castSucc (Fin.last m) n.castSucc y.castSucc z.castSucc hA'.base.extensionality hw' (under hn E)
    (OmegaOrdinals.elements w.castSucc hA'.base.foundation hA'.ordinalSeparation hw')
    (recursors hA' w.castSucc a.castSucc (Fin.last m) hAdd' hMul' hw' (under ha E))
    (evaluation_at_zero w.castSucc a.castSucc n.castSucc y.castSucc (Fin.last m) hA'.base.extensionality he hy')
    (evaluation_at_zero w.castSucc a.castSucc n.castSucc z.castSucc (Fin.last m) hA'.base.extensionality he hz')

theorem exists_product {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n : Fin m)
    (hAdd : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hMul : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalMultiplicationStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w)) : Derives Γ (existsProduct w a n) := by
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Ξ := Context.add E (Context.image Formula.raise Γ)
  have hzero : Derives Γ (.ex E) := .conjL (.conjL hw)
  apply Derives.exE (p := E) hzero
  have hA' : ArithmeticContext.Evidence Ξ := ArithmeticContext.under hA E
  have hAdd' : Derives Ξ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hAdd E
  have hMul' : Derives Ξ ((NaturalRecursion.uniquenessSentence NaturalMultiplicationStep.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hMul E
  have hw' : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw E
  have hev := NaturalEvaluationExistence.at_natural NaturalMultiplicationStep.matrix (params w.castSucc a.castSucc)
    w.castSucc (Fin.last m) n.castSucc hw' (under hn E)
    (OmegaOrdinals.elements w.castSucc hA'.base.foundation hA'.ordinalSeparation hw')
    (recursors hA' w.castSucc a.castSucc (Fin.last m) hAdd' hMul' hw' (under ha E))
  let Y := NaturalEvaluationSyntax.evaluation NaturalMultiplicationStep.matrix (paramsUp (params w.castSucc a.castSucc))
    w.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add Y (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex Y) at hev
  apply Derives.exE (p := Y) hev
  have hE : Derives Δ E.raise := under (Derives.hyp (Γ := Ξ) (Or.inl rfl)) Y
  have he : Derives Δ (empty (Fin.last m).castSucc) := by
    simpa only [E, Formula.raise, Formula.rename, empty_rename] using Derives.conjR hE
  have hy : Derives Δ (product w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))) :=
    intro_product _ _ _ _ (Fin.last m).castSucc he (.hyp (Or.inl rfl))
  have hextΔ : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hA'.base.extensionality Y
  have hwΔ : Derives Δ (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using under hw' Y
  have hout := intro_exists _ _ _ _ (closure _ _ _ _ hextΔ hwΔ hy) hy
  simpa only [Formula.raise, existsProduct_rename] using hout

theorem exists_unique {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n : Fin m)
    (hAdd : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hMul : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalMultiplicationStep.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w)) : Derives Γ (fiber w a n) := by
  have hy := exists_product hA w a n hAdd hMul hw ha hn
  let Y := (Formula.mem (Fin.last m) w.castSucc).conj (product w.castSucc a.castSucc n.castSucc (Fin.last m))
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hy
  apply Derives.exE (p := Y) hy
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hA' : ArithmeticContext.Evidence Ξ := ArithmeticContext.under hA Y
  have hAdd' : Derives Ξ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hAdd Y
  have hMul' : Derives Ξ ((NaturalRecursion.uniquenessSentence NaturalMultiplicationStep.matrix).rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hMul Y
  have hw' : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Y
  have hu : Derives Ξ (.all ((product w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let Z := product w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add Z (Context.image Formula.raise Ξ)
    have hAddΔ : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using under hAdd' Z
    have hMulΔ : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalMultiplicationStep.matrix).rename Fin.elim0) := by
      simpa only [Formula.raise, closed_rename] using under hMul' Z
    have hwΔ : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw' Z
    have hp : Derives Δ (product w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [Formula.raise, product_rename] using under (Derives.conjR hY) Z
    exact unique (ArithmeticContext.under hA' Z) _ _ _ _ _ hAddΔ hMulΔ hwΔ
      (under (under ha Y) Z) (under (under hn Y) Z) (.hyp (Or.inl rfl)) hp
  have hout : Derives Ξ (fiber w.castSucc a.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, product_rename, Formula.liftRen,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hY hu
  simpa only [Formula.raise, NaturalMultiplicationSyntax.fiber_rename] using hout
end PPAC.Migration.Internal.NaturalMultiplicationCore
