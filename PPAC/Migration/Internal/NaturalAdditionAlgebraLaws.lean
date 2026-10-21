import PPAC.Migration.Internal.NaturalAdditionCancellation

/-! 前述对象归纳定理的双向代数形式及左抵消。 -/
namespace PPAC.Migration.Internal.NaturalAdditionAlgebraLaws
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax ReplacementPredicates NaturalAdditionSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem successor_output_subst {m} {Γ : Context m} (x z y : Fin m) (he : Derives Γ (.equal x z))
    (hx : Derives Γ (successor x y)) : Derives Γ (successor z y) := by
  have hi : Derives Γ ((successor (Fin.last m) y.castSucc).instantiate x) := by
    simpa only [Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hx
  have ho := Derives.eqSubst (successor (Fin.last m) y.castSucc) he hi
  simpa only [Formula.instantiate, successor_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem shift_forward {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b n y z : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation NaturalAdditionShift.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (successor b a))
    (hn : Derives Γ (.mem n w)) (hy : Derives Γ (sum w a n y)) (hz : Derives Γ (sum w b n z)) : Derives Γ (successor z y) := by
  have hyW := NaturalAdditionCore.closure _ _ _ _ hA.base.extensionality hw ha hy
  have hq := Derives.impE (step_at w y (.conjL hw)) hyW
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) y.castSucc)
  let Ξ := Context.add Q (Context.image Formula.raise Γ)
  change Derives Γ (.ex Q) at hq
  apply Derives.exE (p := Q) hq
  have hAQ : ArithmeticContext.Evidence Ξ := ArithmeticContext.under hA Q
  have hcQ : Derives Ξ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using under hc Q
  have hsepQ : Derives Ξ ((Source.SetLanguage.separation NaturalAdditionShift.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using under hsep Q
  have hwQ : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Q
  have hbQ : Derives Ξ (successor b.castSucc a.castSucc) := by simpa only [Formula.raise, successor_rename] using under hb Q
  have hyQ : Derives Ξ (sum w.castSucc a.castSucc n.castSucc y.castSucc) := by simpa only [Formula.raise, sum_rename] using under hy Q
  have hzQ : Derives Ξ (sum w.castSucc b.castSucc n.castSucc z.castSucc) := by simpa only [Formula.raise, sum_rename] using under hz Q
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hsum := NaturalAdditionShift.shift_at hAQ _ _ _ _ _ _ hcQ hsepQ hwQ (under ha Q) hbQ (under hn Q) hyQ (.conjR hQ)
  have heq := NaturalAdditionCore.unique hAQ _ _ _ _ _ hcQ hwQ (under hn Q) hzQ hsum
  simpa only [Formula.raise, successor_rename] using successor_output_subst _ _ _ (eq_symm heq) (.conjR hQ)

theorem shift_iff {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b n y z : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation NaturalAdditionShift.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (successor b a))
    (hn : Derives Γ (.mem n w)) (hy : Derives Γ (sum w a n y)) :
    Derives Γ ((sum w b n z).iff (successor z y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact shift_forward (ArithmeticContext.add hA _) _ _ _ _ _ _ (add hc _) (add hsep _) (add hw _) (add ha _) (add hb _) (add hn _) (add hy _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact NaturalAdditionShift.shift_at (ArithmeticContext.add hA _) _ _ _ _ _ _ (add hc _) (add hsep _) (add hw _) (add ha _) (add hb _) (add hn _) (add hy _) (.hyp (Or.inl rfl))

theorem associate_backward {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b u n v y : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation NaturalAdditionAssociative.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hab : Derives Γ (sum w a b u)) (hv : Derives Γ (sum w b n v)) (hy : Derives Γ (sum w a v y)) : Derives Γ (sum w u n y) := by
  have huW := NaturalAdditionCore.closure _ _ _ _ hA.base.extensionality hw ha hab
  have ht := NaturalAdditionCore.exists_sum hA w u n hc hw huW hn
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc u.castSucc n.castSucc (Fin.last m))
  let Ξ := Context.add T (Context.image Formula.raise Γ)
  change Derives Γ (.ex T) at ht
  apply Derives.exE (p := T) ht
  have hAT : ArithmeticContext.Evidence Ξ := ArithmeticContext.under hA T
  have hcT : Derives Ξ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using under hc T
  have hsepT : Derives Ξ ((Source.SetLanguage.separation NaturalAdditionAssociative.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using under hsep T
  have hwT : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw T
  have habT : Derives Ξ (sum w.castSucc a.castSucc b.castSucc u.castSucc) := by simpa only [Formula.raise, sum_rename] using under hab T
  have hvT : Derives Ξ (sum w.castSucc b.castSucc n.castSucc v.castSucc) := by simpa only [Formula.raise, sum_rename] using under hv T
  have hyT : Derives Ξ (sum w.castSucc a.castSucc v.castSucc y.castSucc) := by simpa only [Formula.raise, sum_rename] using under hy T
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have haVT := NaturalAdditionAssociative.associate hAT _ _ _ _ _ _ _ hcT hsepT hwT (under ha T) (under hb T) (under hn T) habT hvT (.conjR hT)
  have hvW := NaturalAdditionCore.closure _ _ _ _ hAT.base.extensionality hwT (under hb T) hvT
  have heq := NaturalAdditionCore.unique hAT _ _ _ _ _ hcT hwT hvW haVT hyT
  simpa only [Formula.raise, sum_rename] using output_subst _ _ _ _ _ heq (.conjR hT)

theorem associative_iff {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b u n v y : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hsep : Derives Γ ((Source.SetLanguage.separation NaturalAdditionAssociative.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hab : Derives Γ (sum w a b u)) (hv : Derives Γ (sum w b n v)) :
    Derives Γ ((sum w u n y).iff (sum w a v y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact NaturalAdditionAssociative.associate (ArithmeticContext.add hA _) _ _ _ _ _ _ _ (add hc _) (add hsep _) (add hw _) (add ha _) (add hb _) (add hn _) (add hab _) (add hv _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact associate_backward (ArithmeticContext.add hA _) _ _ _ _ _ _ _ (add hc _) (add hsep _) (add hw _) (add ha _) (add hb _) (add hn _) (add hab _) (add hv _) (.hyp (Or.inl rfl))

theorem cancel_left {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a b n y : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hcan : Derives Γ ((Source.SetLanguage.separation NaturalAdditionCancellation.matrix).rename Fin.elim0))
    (hcom : Derives Γ ((Source.SetLanguage.separation NaturalAdditionCommutative.matrix).rename Fin.elim0))
    (hshift : Derives Γ ((Source.SetLanguage.separation NaturalAdditionShift.matrix).rename Fin.elim0))
    (hzero : Derives Γ ((Source.SetLanguage.separation NaturalAdditionZero.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hn : Derives Γ (.mem n w))
    (hay : Derives Γ (sum w n a y)) (hby : Derives Γ (sum w n b y)) : Derives Γ (.equal a b) :=
  NaturalAdditionCancellation.cancel_right hA w a b n y hc hcan hw ha hb hn
    (NaturalAdditionCommutative.commute hA w n a y hc hcom hshift hzero hw hn ha hay)
    (NaturalAdditionCommutative.commute hA w n b y hc hcom hshift hzero hw hn hb hby)
end PPAC.Migration.Internal.NaturalAdditionAlgebraLaws
