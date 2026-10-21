import PPAC.Migration.Internal.NaturalDifferenceSyntax

/-! 差分的零点和后继步实际取得自然数见证，不使用宿主减法。 -/
namespace PPAC.Migration.Internal.NaturalDifferenceStep
open Source SourceAlgebra SourceLogic OmegaSyntax NaturalAdditionSyntax ZFArithmetic NaturalDifferenceSyntax
open NaturalAdditionBounds (below)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem reflexive {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) : Derives Γ (existsDifference w a a) := by
  let Z := (Formula.mem (Fin.last m) w.castSucc).conj (empty (Fin.last m))
  let Ξ := Context.add Z (Context.image Formula.raise Γ)
  have hz : Derives Γ (.ex Z) := .conjL (.conjL hw)
  apply Derives.exE (p := Z) hz
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ Z
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw Z
  have hZero : Derives Ξ Z := .hyp (Or.inl rfl)
  have hs := add_zero hZ1 w.castSucc a.castSucc (Fin.last m) hw1 (under ha Z) (.conjR hZero)
  simpa only [Formula.raise, existsDifference_rename] using intro_difference _ _ _ _ (.conjL hZero) hs

theorem zero_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (empty b))
    (hle : Derives Γ (below a b)) : Derives Γ (existsDifference w a b) := by
  apply Derives.disjE hle
  · let E := Formula.equal a b
    let Δ := Context.add E Γ
    have hZE : ZFContext.Evidence Δ := ZFContext.add hZ E
    have hwE : Derives Δ (omega w) := add hw E
    have hbE : Derives Δ (empty b) := add hb E
    have hbW := OmegaStructureAlgebra.zero_member w b (ZFContext.arithmetic hZE).base.extensionality hwE hbE
    have hsum := add_zero hZE w a b hwE (add ha E) hbE
    exact intro_difference w a b b hbW (NaturalAdditionSyntax.output_subst w a b a b (.hyp (Or.inl rfl)) hsum)
  · exact .botE (.impE (empty_at b a (add hb _)) (.hyp (Or.inl rfl)))

theorem advance {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b s d : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hd : Derives Γ (.mem d w))
    (hs : Derives Γ (successor s b)) (hSum : Derives Γ (sum w a d b)) : Derives Γ (existsDifference w a s) := by
  have he := Derives.impE (step_at w d (.conjL hw)) hd
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) d.castSucc)
  let Ξ := Context.add E (Context.image Formula.raise Γ)
  change Derives Γ (.ex E) at he
  apply Derives.exE (p := E) he
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ E
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw E
  have hs1 : Derives Ξ (successor s.castSucc b.castSucc) := by simpa only [Formula.raise, successor_rename] using under hs E
  have hSum1 : Derives Ξ (sum w.castSucc a.castSucc d.castSucc b.castSucc) := by simpa only [Formula.raise, sum_rename] using under hSum E
  have hE : Derives Ξ E := .hyp (Or.inl rfl)
  have hNew := add_succ_backward hZ1 w.castSucc a.castSucc d.castSucc (Fin.last m) b.castSucc s.castSucc hw1 (under ha E) (under hd E) (.conjR hE) hSum1 hs1
  simpa only [Formula.raise, existsDifference_rename] using intro_difference _ _ _ _ (.conjL hE) hNew

theorem step_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b s : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hi : Derives Γ (property w a b))
    (hs : Derives Γ (successor s b)) (hle : Derives Γ (below a s)) : Derives Γ (existsDifference w a s) := by
  apply Derives.disjE hle
  · exact target_subst w a a s (.hyp (Or.inl rfl)) (reflexive (ZFContext.add hZ _) w a (add hw _) (add ha _))
  · let M := Formula.mem a s
    let Γm := Context.add M Γ
    have hprev := NaturalOrderBasic.member_successor a b s (add hs M) (Derives.hyp (Γ := Γm) (Or.inl rfl))
    have hOld : Derives Γm (existsDifference w a b) := .impE (add hi M) hprev
    let D := witness w.castSucc a.castSucc b.castSucc (Fin.last m)
    let Ξ := Context.add D (Context.image Formula.raise Γm)
    change Derives Γm (.ex D) at hOld
    apply Derives.exE (p := D) hOld
    have hZ1 : ZFContext.Evidence Ξ := ZFContext.under (ZFContext.add hZ M) D
    have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under (add hw M) D
    have hs1 : Derives Ξ (successor s.castSucc b.castSucc) := by simpa only [Formula.raise, successor_rename] using under (add hs M) D
    have hD : Derives Ξ D := .hyp (Or.inl rfl)
    simpa only [Formula.raise, existsDifference_rename] using advance hZ1 w.castSucc a.castSucc b.castSucc s.castSucc (Fin.last m)
      hw1 (under (add ha M) D) (.conjL hD) hs1 (.conjR hD)
end PPAC.Migration.Internal.NaturalDifferenceStep
