import PPAC.Migration.Internal.NaturalDifference

/-! 严格次序对应实际非零自然差值；零差值精确对应端点相等。 -/
namespace PPAC.Migration.Internal.NaturalDifferencePositive
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic NaturalDifferenceSyntax
open NaturalAdditionSyntax (sum sum_rename params)
open NaturalAdditionBounds (below)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem sum_positive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a d b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hd : Derives Γ (.mem d w))
    (hs : Derives Γ (sum w a d b)) (hn : Derives Γ (empty d).neg) : Derives Γ (.mem a b) :=
  NaturalAdditionOrderLaws.strict_right (ZFContext.arithmetic hZ) w a d b (ZFContext.recAdd hZ)
    (ZFContext.separation hZ NaturalAdditionBounds.matrix) (ZFContext.separation hZ OmegaStructureSyntax.splitMatrix) hw ha hd hs hn

theorem positive_of_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hab : Derives Γ (.mem a b)) :
    Derives Γ (positiveExists w a b) := by
  have hd := NaturalDifference.exists_of_below hZ w a b hw ha hb (.disjR hab)
  let D := witness w.castSucc a.castSucc b.castSucc (Fin.last m)
  let Ξ := Context.add D (Context.image Formula.raise Γ)
  change Derives Γ (.ex D) at hd
  apply Derives.exE (p := D) hd
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ D
  have hD : Derives Ξ D := .hyp (Or.inl rfl)
  have hab1 : Derives Ξ (.mem a.castSucc b.castSucc) := under hab D
  have hn : Derives Ξ (empty (Fin.last m)).neg := by
    apply Derives.impI
    let E := empty (Fin.last m)
    let Δ := Context.add E Ξ
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    have hSum : Derives Δ (sum w.castSucc a.castSucc (Fin.last m) b.castSucc) := add (.conjR hD) E
    have heq := NaturalRecursionLaws.evaluation_zero NaturalSuccessorStep.matrix (params w.castSucc)
      w.castSucc a.castSucc (Fin.last m) b.castSucc hE hSum
    have haa := UnorderedPairLogic.mem_container_subst b.castSucc a.castSucc a.castSucc heq (add hab1 E)
    exact .impE (NaturalOrderBasic.nonself (ZFContext.add hZ1 E) a.castSucc) haa
  simpa only [Formula.raise, positiveExists_rename] using intro_positive _ _ _ _ (.conjL hD) hn (.conjR hD)

theorem member_of_positive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hp : Derives Γ (positiveExists w a b)) : Derives Γ (.mem a b) := by
  let D := positiveWitness w.castSucc a.castSucc b.castSucc (Fin.last m)
  let Ξ := Context.add D (Context.image Formula.raise Γ)
  change Derives Γ (.ex D) at hp
  apply Derives.exE (p := D) hp
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ D
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw D
  have hD : Derives Ξ D := .hyp (Or.inl rfl)
  exact sum_positive hZ1 _ _ _ _ hw1 (under ha D) (.conjL (.conjL hD)) (.conjR hD) (.conjR (.conjL hD))

theorem strict_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) :
    Derives Γ ((Formula.mem a b).iff (positiveExists w a b)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact positive_of_member (ZFContext.add hZ _) _ _ _ (add hw _) (add ha _) (add hb _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact member_of_positive (ZFContext.add hZ _) _ _ _ (add hw _) (add ha _) (.hyp (Or.inl rfl))

theorem zero_of_same {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a d : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hd : Derives Γ (.mem d w))
    (hs : Derives Γ (sum w a d a)) : Derives Γ (empty d) := by
  apply Derives.classical
  have hh := sum_positive (ZFContext.add hZ _) w a d a (add hw _) (add ha _) (add hd _) (add hs _) (.hyp (Or.inl rfl))
  exact .impE (NaturalOrderBasic.nonself (ZFContext.add hZ _) a) hh

theorem zero_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b d : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hd : Derives Γ (.mem d w))
    (hs : Derives Γ (sum w a d b)) : Derives Γ ((empty d).iff (.equal a b)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact eq_symm (NaturalRecursionLaws.evaluation_zero NaturalSuccessorStep.matrix (params w) w a d b (.hyp (Or.inl rfl)) (add hs _))
  · apply Derives.impI
    have hsame := NaturalAdditionSyntax.output_subst w a d b a (eq_symm (.hyp (Or.inl rfl))) (add hs _)
    exact zero_of_same (ZFContext.add hZ _) _ _ _ (add hw _) (add ha _) (add hd _) hsame
end PPAC.Migration.Internal.NaturalDifferencePositive
