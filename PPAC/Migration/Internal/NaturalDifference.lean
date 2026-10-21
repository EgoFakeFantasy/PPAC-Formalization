import PPAC.Migration.Internal.NaturalDifferenceStep

/-! 全内部自然上界的差分存在、与真实顺序的等价及自然范围内唯一性。 -/
namespace PPAC.Migration.Internal.NaturalDifference
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic
open ReplacementPredicates (paramsUp)
open NaturalAdditionSyntax (sum sum_rename)
open NaturalAdditionBounds (below below_rename)
open NaturalDifferenceSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem base {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) :
    Derives Γ (OmegaInductionSyntax.base NaturalDifferenceSyntax.matrix (Source.SetLanguage.args2 w a)) := by
  simp only [OmegaInductionSyntax.base, NaturalDifferenceSyntax.matrix_pred, paramsUp, PairSyntax.args2_first, PairSyntax.args2_second]
  apply Derives.allI
  let Δ := Context.image Formula.raise Γ
  have hw' : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc hw
  apply Derives.impI
  apply Derives.impI
  exact NaturalDifferenceStep.zero_point (ZFContext.add (ZFContext.add (ZFContext.rename hZ Fin.castSucc) _) _) _ _ _ (add (add hw' _) _)
    (add (add (Derives.rename Fin.castSucc ha) _) _) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) :
    Derives Γ (OmegaInductionSyntax.step NaturalDifferenceSyntax.matrix (Source.SetLanguage.args2 w a) w) := by
  simp only [OmegaInductionSyntax.step, NaturalDifferenceSyntax.matrix_pred, paramsUp, PairSyntax.args2_first, PairSyntax.args2_second]
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hZ' := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
  have hw' : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw)
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact NaturalDifferenceStep.step_point (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.add hZ' _) _) _) _) _ _ _ _
    (add (add (add (add hw' _) _) _) _) (add (add (add (add (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc ha)) _) _) _) _)
    (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem exists_of_below {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hl : Derives Γ (below a b)) :
    Derives Γ (existsDifference w a b) := by
  have hall := ZFArithmetic.induction hZ NaturalDifferenceSyntax.matrix (Source.SetLanguage.args2 w a) w hw (base hZ w a hw ha) (step hZ w a hw ha)
  have hi : Derives Γ (.all ((Formula.mem (Fin.last m) w.castSucc).imp (property w.castSucc a.castSucc (Fin.last m)))) := by
    simpa only [OmegaInductionSyntax.holds, NaturalDifferenceSyntax.matrix_pred, paramsUp, PairSyntax.args2_first, PairSyntax.args2_second] using hall
  have hi' : Derives Γ ((Formula.mem b w).imp (property w a b)) := by
    simpa only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE b hi
  exact .impE (.impE hi' hb) hl

theorem below_of_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hd : Derives Γ (existsDifference w a b)) : Derives Γ (below a b) := by
  let D := witness w.castSucc a.castSucc b.castSucc (Fin.last m)
  let Ξ := Context.add D (Context.image Formula.raise Γ)
  change Derives Γ (.ex D) at hd
  apply Derives.exE (p := D) hd
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ D
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw D
  have hD : Derives Ξ D := .hyp (Or.inl rfl)
  have hlo := NaturalAdditionBounds.lower_bound (ZFContext.arithmetic hZ1) w.castSucc a.castSucc (Fin.last m) b.castSucc (ZFContext.recAdd hZ1)
    (ZFContext.separation hZ1 NaturalAdditionBounds.matrix) hw1 (under ha D) (.conjL hD) (.conjR hD)
  simpa only [Formula.raise, below_rename] using hlo

theorem difference_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) :
    Derives Γ ((below a b).iff (existsDifference w a b)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact exists_of_below (ZFContext.add hZ _) _ _ _ (add hw _) (add ha _) (add hb _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact below_of_exists (ZFContext.add hZ _) _ _ _ (add hw _) (add ha _) (.hyp (Or.inl rfl))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b d e : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hd : Derives Γ (.mem d w)) (he : Derives Γ (.mem e w))
    (hs : Derives Γ (sum w a d b)) (ht : Derives Γ (sum w a e b)) : Derives Γ (.equal d e) :=
  NaturalAdditionAlgebraLaws.cancel_left (ZFContext.arithmetic hZ) w d e a b (ZFContext.recAdd hZ)
    (ZFContext.separation hZ NaturalAdditionCancellation.matrix) (ZFContext.separation hZ NaturalAdditionCommutative.matrix)
    (ZFContext.separation hZ NaturalAdditionShift.matrix) (ZFContext.separation hZ NaturalAdditionZero.matrix) hw hd he ha hs ht

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hl : Derives Γ (below a b)) :
    Derives Γ (NaturalDifferenceSyntax.fiber w a b) := by
  have hd := exists_of_below hZ w a b hw ha hb hl
  let D := witness w.castSucc a.castSucc b.castSucc (Fin.last m)
  let Ξ := Context.add D (Context.image Formula.raise Γ)
  change Derives Γ (.ex D) at hd
  apply Derives.exE (p := D) hd
  have hD : Derives Ξ D := .hyp (Or.inl rfl)
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ D
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw D
  have hu : Derives Ξ (.all ((witness w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let E := witness w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add E (Context.image Formula.raise Ξ)
    have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 E
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 E
    have hD' : Derives Δ D.raise := under hD E
    have hOld : Derives Δ (witness w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [D, Formula.raise, witness_rename] using hD'
    have hE : Derives Δ E := .hyp (Or.inl rfl)
    exact unique hZ2 _ _ _ _ _ hw2 (under (under ha D) E) (.conjL hE) (.conjL hOld) (.conjR hE) (.conjR hOld)
  have hout : Derives Ξ (NaturalDifferenceSyntax.fiber w.castSucc a.castSucc b.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, witness_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hD hu
  simpa only [Formula.raise, NaturalDifferenceSyntax.fiber_rename] using hout
end PPAC.Migration.Internal.NaturalDifference
