import PPAC.Migration.Internal.SyntaxRenameLogicalUnique

/-! 给定内部 Property 和合法源类型时实际取得普通/提升子输出；所有后继与提升码在对象层存在消去。 -/
namespace PPAC.Migration.Internal.SyntaxRenameCheckExistence
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxRenameOutputSyntax SyntaxMapCodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def existsCheck {m} (advance : Bool) (w x r s a b c d : Fin m) : Formula m := .ex
  (SyntaxRenameRecursiveSyntax.check advance w.castSucc x.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m))

theorem existsCheck_rename {m k} (advance : Bool) (w x r s a b c d : Fin m) (ρ : Fin m → Fin k) :
    (existsCheck advance w x r s a b c d).rename ρ = existsCheck advance (ρ w) (ρ x) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) := by
  simp only [existsCheck, Formula.rename, SyntaxRenameRecursiveSyntax.check_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_exists {m} {Γ : Context m} (advance : Bool) (w x r s a b c d q : Fin m)
    (hq : Derives Γ (SyntaxRenameRecursiveSyntax.check advance w x r s a b c d q)) : Derives Γ (existsCheck advance w x r s a b c d) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, SyntaxRenameRecursiveSyntax.check_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq

theorem from_child_exists {m} {Γ : Context m} (w x r s a b c d u v l : Fin m)
    (hl : Derives Γ (SyntaxMapLiftSyntax.codedLift w a c r u v l))
    (he : Derives Γ (existsOutput w l s u b v d x)) : Derives Γ (existsCheck true w x r s a b c d) := by
  let Q := SyntaxRenameJudgmentSyntax.renamed w.castSucc l.castSucc s.castSucc u.castSucc b.castSucc v.castSucc d.castSucc x.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hl1 : Derives Δ (SyntaxMapLiftSyntax.codedLift w.castSucc a.castSucc c.castSucc r.castSucc u.castSucc v.castSucc l.castSucc) :=
    of_eq (SyntaxMapLiftSyntax.codedLift_rename w a c r u v l Fin.castSucc) (under hl Q)
  have hr := SyntaxRenameAdvancedKnown.intro_advanced w.castSucc x.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m) u.castSucc v.castSucc l.castSucc hl1 (.hyp (Or.inl rfl))
  have ho := intro_exists true w.castSucc x.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m) hr
  exact of_eq (existsCheck_rename true w x r s a b c d Fin.castSucc).symm ho

theorem at_lift_property {m} {Γ : Context m} (w x r s a b c d u v l : Fin m)
    (hp : Derives Γ (property w x)) (hl : Derives Γ (SyntaxMapLiftSyntax.codedLift w a c r u v l))
    (hc : Derives Γ (FormulaCodeSyntax.formulaCode w x u b)) (hs : Derives Γ (mapCode w b d s)) :
    Derives Γ (existsCheck true w x r s a b c d) := by
  have hi : Derives Γ (input w l s u b v d x) := .conjI hc (.conjI (SyntaxMapLiftFiber.output_code w a c r u v l hl) hs)
  have hf := Derives.impE (property_at w x l s u b v d hp) hi
  exact from_child_exists w x r s a b c d u v l hl (SyntaxRenameOutput.exists_of_fiber w l s u b v d x hf)

theorem exists_at_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (advance : Bool) (w x r s a b c d : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (property w x))
    (hc : Derives Γ (FormulaCodeRecursiveSyntax.stepCheck advance w x a b))
    (hr : Derives Γ (mapCode w a c r)) (hs : Derives Γ (mapCode w b d s)) : Derives Γ (existsCheck advance w x r s a b c d) := by
  cases advance
  · have hi : Derives Γ (input w r s a b c d x) := .conjI hc (.conjI hr hs)
    exact SyntaxRenameOutput.exists_of_fiber w r s a b c d x (.impE (property_at w x r s a b c d hp) hi)
  · let U := (successor (Fin.last m) a.castSucc).conj (FormulaCodeSyntax.formulaCode w.castSucc x.castSucc (Fin.last m) b.castSucc)
    let Ξ := Context.add U (Context.image Formula.raise Γ)
    apply Derives.exE (p := U) hc
    have hZ1 := ZFContext.under hZ U
    have heV := InsertExistence.exists_insert c.castSucc c.castSucc (ZFContext.arithmetic hZ1).base.pairing (ZFContext.arithmetic hZ1).base.union
    let V := successor (Fin.last (m+1)) c.castSucc.castSucc
    let Δ := Context.add V (Context.image Formula.raise Ξ)
    apply Derives.exE (p := V) heV
    have hZ2 := ZFContext.under hZ1 V
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (under hw U) V)
    have hr2 : Derives Δ (mapCode w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc r.castSucc.castSucc) := of_eq (by simp only [Formula.raise, mapCode_rename]) (under (under hr U) V)
    have hU : Derives Ξ U := .hyp (Or.inl rfl)
    have hu2 : Derives Δ (successor (Fin.last m).castSucc a.castSucc.castSucc) := of_eq (successor_rename _ _ Fin.castSucc) (under (Derives.conjL hU) V)
    have heL := SyntaxMapLift.exists_code hZ2 w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hr2 hu2 (.hyp (Or.inl rfl))
    let L := SyntaxMapLiftSyntax.codedLift w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))
    let Θ := Context.add L (Context.image Formula.raise Δ)
    apply Derives.exE (p := L) heL
    have hp3 : Derives Θ (property w.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, property_rename]) (under (under (under hp U) V) L)
    have hs3 : Derives Θ (mapCode w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, mapCode_rename]) (under (under (under hs U) V) L)
    have hc3 : Derives Θ (FormulaCodeSyntax.formulaCode w.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc b.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) (under (under (Derives.conjR hU) V) L)
    have ho := at_lift_property w.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hp3 (.hyp (Or.inl rfl)) hc3 hs3
    exact of_eq (by simp only [Formula.raise, existsCheck_rename]) ho
end PPAC.Migration.Internal.SyntaxRenameCheckExistence
