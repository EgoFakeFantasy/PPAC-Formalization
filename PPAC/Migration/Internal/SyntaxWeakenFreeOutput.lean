import PPAC.Migration.Internal.SyntaxWeakenFreeSyntax

/-! 全内部弱化判断的精确输入/输出类型和合法输入的实际输出存在。 -/
namespace PPAC.Migration.Internal.SyntaxWeakenFreeOutput
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxWeakenFreeSyntax
open SyntaxIdentityMapSyntax (identityCode identityCode_rename)
open SyntaxFreeShiftSyntax (shiftCode shiftCode_rename)
open SyntaxRenameJudgmentSyntax (renamed renamed_rename)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem input_of_weakened {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (weakened w a b B n q)) : Derives Γ (input w a b B n) := by
  let H := body w a b B n q
  let Δ := Context.add H (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_weakened w a b B n q _ hq
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw H)
  have hi := SyntaxRenameOutput.input_of_renamed (SyntaxRenameBinders.zf_under_2 hZ H)
    _ _ _ _ _ _ _ _ _ hw2 (.conjR (.conjR hH))
  have hs := SyntaxFreeShiftCode.input _ _ _ _ (.conjL (.conjR hH))
  have ho : Derives Δ (input w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc) :=
    .conjI (.conjL hi) (.conjR hs)
  exact of_eq (by simp only [Formula.raise, input_rename]) ho

theorem target_type {m} {Γ : Context m} (w a b B n q : Fin m)
    (hq : Derives Γ (weakened w a b B n q)) : Derives Γ (formulaCode w q a B) := by
  let H := body w a b B n q
  let Δ := Context.add H (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_weakened w a b B n q _ hq
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have ho := SyntaxRenameJudgment.target_type _ _ _ _ _ _ _ _ _ (.conjR (.conjR hH))
  exact of_eq (by simp only [Formula.raise, formulaCode_rename]) ho

theorem source_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (weakened w a b B n q)) : Derives Γ (formulaCode w n a b) :=
  .conjL (input_of_weakened hZ w a b B n q hw hq)

theorem output_natural {m} {Γ : Context m} (w a b B n q : Fin m)
    (hq : Derives Γ (weakened w a b B n q)) : Derives Γ (.mem q w) :=
  .conjL (FormulaCodeProperties.guards w q a B (target_type w a b B n q hq))

theorem exists_at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n R S : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (formulaCode w n a b))
    (hr : Derives Γ (identityCode w a R)) (hs : Derives Γ (shiftCode w b B S)) :
    Derives Γ (existsOutput w a b B n) := by
  have hi : Derives Γ (SyntaxRenameOutputSyntax.input w R S a b a B n) :=
    .conjI hc (.conjI (SyntaxIdentityCode.map_code w a R hr) (SyntaxFreeShiftCode.map_code w b B S hs))
  have he := SyntaxRenameOutputInduction.actual_exists hZ w R S a b a B n hw hi
  let Q := renamed w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc a.castSucc B.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hr1 : Derives Δ (identityCode w.castSucc a.castSucc R.castSucc) := of_eq (identityCode_rename w a R Fin.castSucc) (under hr Q)
  have hs1 : Derives Δ (shiftCode w.castSucc b.castSucc B.castSucc S.castSucc) := of_eq (shiftCode_rename w b B S Fin.castSucc) (under hs Q)
  have ho := intro_exists w.castSucc a.castSucc b.castSucc B.castSucc n.castSucc (Fin.last m)
    (intro_weakened _ _ _ _ _ _ _ _ hr1 hs1 (Derives.hyp (Or.inl rfl) : Derives Δ Q))
  exact of_eq (existsOutput_rename w a b B n Fin.castSucc).symm ho

theorem exists_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b B n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w a b B n)) : Derives Γ (existsOutput w a b B n) := by
  have hc := Derives.conjL hi
  have hg := FormulaCodeProperties.guards w n a b hc
  have he := SyntaxIdentityCode.exists_code hZ w a hw (.conjL (.conjR hg))
  let R := identityCode w.castSucc a.castSucc (Fin.last m)
  let Ξ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) he
  have hZ1 := ZFContext.under hZ R
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hb1 : Derives Ξ (.mem b.castSucc w.castSucc) := under (.conjR (.conjR hg)) R
  have hB1 : Derives Ξ (successor B.castSucc b.castSucc) := of_eq (successor_rename B b Fin.castSucc) (under (.conjR hi) R)
  let S := shiftCode w.castSucc.castSucc b.castSucc.castSucc B.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add S (Context.image Formula.raise Ξ)
  apply Derives.exE (p := S) (SyntaxFreeShiftCode.exists_code hZ1 _ _ _ hw1 hb1 hB1)
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (omega_rename _ Fin.castSucc) (under hw1 S)
  have hc2 : Derives Δ (formulaCode w.castSucc.castSucc n.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, formulaCode_rename]) (under (under hc R) S)
  have hR : Derives Ξ R := .hyp (Or.inl rfl)
  have hr2 : Derives Δ (identityCode w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc) :=
    of_eq (by simp only [R, Formula.raise, identityCode_rename]) (under hR S)
  have ho := exists_at_codes (ZFContext.under hZ1 S) _ _ _ _ _ _ _ hw2 hc2 hr2 (Derives.hyp (Or.inl rfl) : Derives Δ S)
  exact of_eq (by simp only [Formula.raise, existsOutput_rename]) ho
end PPAC.Migration.Internal.SyntaxWeakenFreeOutput
