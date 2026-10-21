import PPAC.Migration.Internal.GodelPairArithmetic

/-! 原配数两个输入均不大于实际配数值；全部值仍为内部自然对象。 -/
namespace PPAC.Migration.Internal.GodelPairBounds
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic GodelPairSyntax GodelPairArithmetic
open NaturalAdditionBounds (below below_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem lower_components {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hp : Derives Γ (lower w a b p)) : Derives Γ ((below a p).conj (below b p)) := by
  let L := lowerWitness w a b p
  let Ξ := Context.add L (Context.image Formula.raise Γ)
  apply eliminate_lower w a b p _ hp
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ L
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw L
  have hL : Derives Ξ L := .hyp (Or.inl rfl)
  have hqW := mul_range hZ1 _ _ _ _ hw1 (.conjL hL)
  have hpW := add_range hZ1 _ _ _ _ hw1 hqW (.conjR hL)
  have hap := sum_right_bound hZ1 _ _ _ _ hw1 hqW (under ha L) (.conjR hL)
  have hqp := sum_left_bound hZ1 _ _ _ _ hw1 hqW (under ha L) (.conjR hL)
  have hbq := NaturalArithmeticBounds.square_bound hZ1 _ _ _ hw1 (under hb L) (.conjL hL)
  have hbp := NaturalOrderBasic.transitive hZ1 _ _ _ _ hw1 hpW hbq hqp
  have hout : Derives Ξ ((below a.castSucc p.castSucc).conj (below b.castSucc p.castSucc)) := .conjI hap hbp
  simpa only [Formula.raise, Formula.rename, below_rename] using hout

theorem upper_components {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hp : Derives Γ (upper w a b p)) : Derives Γ ((below a p).conj (below b p)) := by
  let U := upperWitness w a b p
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_upper w a b p _ hp
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have haW : Derives Δ (.mem a.castSucc.castSucc w.castSucc.castSucc) := OrderedPairElimination.under_two ha U
  have hbW : Derives Δ (.mem b.castSucc.castSucc w.castSucc.castSucc) := OrderedPairElimination.under_two hb U
  have hqW := mul_range hZ2 _ _ _ _ hw2 (.conjL hU)
  have htW := add_range hZ2 _ _ _ _ hw2 hqW (.conjL (.conjR hU))
  have hpW := add_range hZ2 _ _ _ _ hw2 htW (.conjR (.conjR hU))
  have haq := NaturalArithmeticBounds.square_bound hZ2 _ _ _ hw2 haW (.conjL hU)
  have hqt := sum_left_bound hZ2 _ _ _ _ hw2 hqW haW (.conjL (.conjR hU))
  have htp := sum_left_bound hZ2 _ _ _ _ hw2 htW hbW (.conjR (.conjR hU))
  have hat := NaturalOrderBasic.transitive hZ2 _ _ _ _ hw2 htW haq hqt
  have hap := NaturalOrderBasic.transitive hZ2 _ _ _ _ hw2 hpW hat htp
  have hbp := sum_right_bound hZ2 _ _ _ _ hw2 htW hbW (.conjR (.conjR hU))
  have hout : Derives Δ ((below a.castSucc.castSucc p.castSucc.castSucc).conj (below b.castSucc.castSucc p.castSucc.castSucc)) := .conjI hap hbp
  simpa only [Formula.raise, Formula.rename, below_rename] using hout

theorem components {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hp : Derives Γ (code w a b p)) : Derives Γ ((below a p).conj (below b p)) := by
  apply Derives.disjE hp
  · exact lower_components (ZFContext.add hZ _) _ _ _ _ (add hw _) (add ha _) (add hb _) (.conjR (.hyp (Or.inl rfl)))
  · exact upper_components (ZFContext.add hZ _) _ _ _ _ (add hw _) (add ha _) (add hb _) (.conjR (.hyp (Or.inl rfl)))
end PPAC.Migration.Internal.GodelPairBounds
