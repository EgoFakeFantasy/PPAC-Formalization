import PPAC.Migration.Internal.SyntaxMixedFormulaLogicalUnique

/-! 给定内部Property取得普通/量词提升子输出；两张提升表、后继和输出均由对象存在消去取得。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaCheckExistence
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMixedFormulaOutputSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

def existsCheck {m} (advance : Bool) (w x r s a b c d : Fin m) : Formula m := .ex
  (SyntaxMixedFormulaRecursiveSyntax.check advance w.castSucc x.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m))

theorem existsCheck_rename {m k} (advance : Bool) (w x r s a b c d : Fin m) (ρ : Fin m → Fin k) :
    (existsCheck advance w x r s a b c d).rename ρ = existsCheck advance (ρ w) (ρ x) (ρ r) (ρ s) (ρ a) (ρ b) (ρ c) (ρ d) := by
  simp only [existsCheck, Formula.rename, SyntaxMixedFormulaRecursiveSyntax.check_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_exists {m} {Γ : Context m} (advance : Bool) (w x r s a b c d q : Fin m)
    (hq : Derives Γ (SyntaxMixedFormulaRecursiveSyntax.check advance w x r s a b c d q)) : Derives Γ (existsCheck advance w x r s a b c d) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, SyntaxMixedFormulaRecursiveSyntax.check_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq

theorem from_child_exists {m} {Γ : Context m} (w x r s a b c d A C K H : Fin m)
    (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A C K H))
    (he : Derives Γ (existsOutput w K H A b C d x)) : Derives Γ (existsCheck true w x r s a b c d) := by
  let Q := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc K.castSucc H.castSucc A.castSucc b.castSucc C.castSucc d.castSucc x.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hl1 : Derives Δ (SyntaxCodedMixedBinderSyntax.lifted w.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc A.castSucc C.castSucc K.castSucc H.castSucc) :=
    of_eq (SyntaxCodedMixedBinderSyntax.lifted_rename w r s a b c d A C K H Fin.castSucc) (under hl Q)
  have hr := SyntaxMixedFormulaAdvancedOutput.intro_advanced w.castSucc x.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m) A.castSucc C.castSucc K.castSucc H.castSucc hl1 (.hyp (Or.inl rfl))
  have ho := intro_exists true w.castSucc x.castSucc r.castSucc s.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m) hr
  exact of_eq (existsCheck_rename true w x r s a b c d Fin.castSucc).symm ho

theorem at_lift_property {m} {Γ : Context m} (w x r s a b c d A C K H : Fin m)
    (hp : Derives Γ (property w x)) (hl : Derives Γ (SyntaxCodedMixedBinderSyntax.lifted w r s a b c d A C K H))
    (hc : Derives Γ (FormulaCodeSyntax.formulaCode w x A b)) :
    Derives Γ (existsCheck true w x r s a b c d) := by
  have hi : Derives Γ (input w K H A b C d x) :=
    .conjI hc (SyntaxCodedMixedBinderTyping.output_lists w r s a b c d A C K H hl)
  have hf := Derives.impE (property_at w x K H A b C d hp) hi
  exact from_child_exists w x r s a b c d A C K H hl (SyntaxMixedFormulaOutput.exists_of_fiber w K H A b C d x hf)

theorem exists_at_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (advance : Bool) (w x r s a b c d : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (property w x))
    (hc : Derives Γ (FormulaCodeRecursiveSyntax.stepCheck advance w x a b))
    (hl : Derives Γ (SyntaxMixedImageCodeSyntax.termLists w a b c d r s)) : Derives Γ (existsCheck advance w x r s a b c d) := by
  cases advance
  · have hi : Derives Γ (input w r s a b c d x) := .conjI hc hl
    exact SyntaxMixedFormulaOutput.exists_of_fiber w r s a b c d x (.impE (property_at w x r s a b c d hp) hi)
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
    have hl2 : Derives Δ (SyntaxMixedImageCodeSyntax.termLists w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxMixedImageCodeSyntax.termLists_rename]) (under (under hl U) V)
    have hU : Derives Ξ U := .hyp (Or.inl rfl)
    have hu2 : Derives Δ (successor (Fin.last m).castSucc a.castSucc.castSucc) := of_eq (successor_rename _ _ Fin.castSucc) (under (Derives.conjL hU) V)
    have heL := SyntaxCodedMixedBinderExistence.exists_pair hZ2 w.castSucc.castSucc r.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 (.conjI hl2 (.conjI hu2 (.hyp (Or.inl rfl))))
    let L := SyntaxCodedMixedBinderSyntax.lifted w.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))
    let Θ := Context.add L (Context.image Formula.raise (Context.image Formula.raise Δ))
    apply SyntaxRenameBinders.eliminate_2 L _ heL
    have hp4 : Derives Θ (property w.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, property_rename]) (SyntaxRenameBinders.under_2 (under (under hp U) V) L)
    have hc4 : Derives Θ (FormulaCodeSyntax.formulaCode w.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise, FormulaCodeSyntax.formulaCode_rename]) (SyntaxRenameBinders.under_2 (under (Derives.conjR hU) V) L)
    have ho := at_lift_property w.castSucc.castSucc.castSucc.castSucc x.castSucc.castSucc.castSucc.castSucc r.castSucc.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc.castSucc c.castSucc.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3)) hp4 (.hyp (Or.inl rfl)) hc4
    exact of_eq (by simp only [Formula.raise, existsCheck_rename]) ho
end PPAC.Migration.Internal.SyntaxMixedFormulaCheckExistence
