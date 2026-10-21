import PPAC.Migration.Internal.NaturalAdditionBounds

/-! 加法的两侧不降界、正加数严格界及和值为零的精确条件。 -/
namespace PPAC.Migration.Internal.NaturalAdditionOrderLaws
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax ReplacementPredicates NaturalAdditionSyntax NaturalAdditionBounds
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem bounds {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n y : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hbound : Derives Γ ((Source.SetLanguage.separation NaturalAdditionBounds.matrix).rename Fin.elim0))
    (hcom : Derives Γ ((Source.SetLanguage.separation NaturalAdditionCommutative.matrix).rename Fin.elim0))
    (hshift : Derives Γ ((Source.SetLanguage.separation NaturalAdditionShift.matrix).rename Fin.elim0))
    (hzero : Derives Γ ((Source.SetLanguage.separation NaturalAdditionZero.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w)) (hy : Derives Γ (sum w a n y)) :
    Derives Γ ((below a y).conj (below n y)) :=
  .conjI (lower_bound hA w a n y hc hbound hw ha hn hy)
    (lower_bound hA w n a y hc hbound hw hn ha (NaturalAdditionCommutative.commute hA w a n y hc hcom hshift hzero hw ha hn hy))

theorem empty_below {m} {Γ : Context m} (a y : Fin m) (hb : Derives Γ (below a y))
    (hy : Derives Γ (empty y)) : Derives Γ (empty a) := by
  apply Derives.disjE hb
  · exact NaturalMultiplicationLaws.empty_subst y a (eq_symm (.hyp (Or.inl rfl))) (add hy _)
  · exact .botE (.impE (empty_at y a (add hy _)) (.hyp (Or.inl rfl)))

theorem empty_sum_iff {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n y : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hbound : Derives Γ ((Source.SetLanguage.separation NaturalAdditionBounds.matrix).rename Fin.elim0))
    (hcom : Derives Γ ((Source.SetLanguage.separation NaturalAdditionCommutative.matrix).rename Fin.elim0))
    (hshift : Derives Γ ((Source.SetLanguage.separation NaturalAdditionShift.matrix).rename Fin.elim0))
    (hzero : Derives Γ ((Source.SetLanguage.separation NaturalAdditionZero.matrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w)) (hy : Derives Γ (sum w a n y)) :
    Derives Γ ((empty y).iff ((empty a).conj (empty n))) := by
  have hb := bounds hA w a n y hc hbound hcom hshift hzero hw ha hn hy
  apply Derives.conjI
  · apply Derives.impI
    exact .conjI (empty_below a y (add (.conjL hb) _) (.hyp (Or.inl rfl))) (empty_below n y (add (.conjR hb) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    let Z := (empty a).conj (empty n)
    have hZ : Derives (Context.add Z Γ) Z := .hyp (Or.inl rfl)
    have heq := NaturalRecursionLaws.evaluation_zero NaturalSuccessorStep.matrix (params w) w a n y (.conjR hZ) (add hy Z)
    exact NaturalMultiplicationLaws.empty_subst a y (eq_symm heq) (.conjL hZ)

theorem strict_right {m} {Γ : Context m} (hA : ArithmeticContext.Evidence Γ) (w a n y : Fin m)
    (hc : Derives Γ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0))
    (hbound : Derives Γ ((Source.SetLanguage.separation NaturalAdditionBounds.matrix).rename Fin.elim0))
    (hsplit : Derives Γ ((Source.SetLanguage.separation OmegaStructureSyntax.splitMatrix).rename Fin.elim0))
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hn : Derives Γ (.mem n w)) (hy : Derives Γ (sum w a n y))
    (hn0 : Derives Γ (empty n).neg) : Derives Γ (.mem a y) := by
  have hd := OmegaStructureAlgebra.decomposition_at w n (OmegaStructureInduction.decomposition w hsplit hw) hn
  have hp := OmegaStructureAlgebra.nonzero_predecessor w n hd hn0
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (successor n.castSucc (Fin.last m))
  let Ξ := Context.add P (Context.image Formula.raise Γ)
  change Derives Γ (.ex P) at hp
  apply Derives.exE (p := P) hp
  have hAP : ArithmeticContext.Evidence Ξ := ArithmeticContext.under hA P
  have hcP : Derives Ξ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using under hc P
  have hbP : Derives Ξ ((Source.SetLanguage.separation NaturalAdditionBounds.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using under hbound P
  have hwP : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw P
  have hyP : Derives Ξ (sum w.castSucc a.castSucc n.castSucc y.castSucc) := by simpa only [Formula.raise, sum_rename] using under hy P
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hx := NaturalAdditionCore.exists_sum hAP w.castSucc a.castSucc (Fin.last m) hcP hwP (under ha P) (.conjL hP)
  let X := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (sum w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add X (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex X) at hx
  apply Derives.exE (p := X) hx
  have hA' : ArithmeticContext.Evidence Δ := ArithmeticContext.under hAP X
  have hc' : Derives Δ ((NaturalRecursion.uniquenessSentence NaturalSuccessorStep.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using under hcP X
  have hb' : Derives Δ ((Source.SetLanguage.separation NaturalAdditionBounds.matrix).rename Fin.elim0) := by simpa only [Formula.raise, closed_rename] using under hbP X
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hwP X
  have hy' : Derives Δ (sum w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc y.castSucc.castSucc) := by simpa only [Formula.raise, sum_rename] using under hyP X
  have hP' : Derives Δ P.raise := under hP X
  have hpW : Derives Δ (.mem (Fin.last m).castSucc w.castSucc.castSucc) := .conjL hP'
  have hps : Derives Δ (successor n.castSucc.castSucc (Fin.last m).castSucc) := by simpa only [P, Formula.raise, Formula.rename, successor_rename] using Derives.conjR hP'
  have hX : Derives Δ X := .hyp (Or.inl rfl)
  have ha' : Derives Δ (.mem a.castSucc.castSucc w.castSucc.castSucc) := under (under ha P) X
  have hs := NaturalAdditionLaws.successor_forward hA' _ _ _ _ _ _ hc' hw' ha' hpW hps (.conjR hX) hy'
  have hlo := lower_bound hA' _ _ _ _ hc' hb' hw' ha' hpW (.conjR hX)
  exact into_successor _ _ _ hlo hs
end PPAC.Migration.Internal.NaturalAdditionOrderLaws
