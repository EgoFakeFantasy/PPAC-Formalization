import PPAC.Migration.Internal.SyntaxFormulaFreeSubstSyntax

/-! 原项列表参数的公式free替换：精确输入/输出类型与全内部实际输出存在。 -/
namespace PPAC.Migration.Internal.SyntaxFormulaFreeSubstOutput
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxFormulaFreeSubstSyntax
open SyntaxIdentityMapSyntax (identityCode identityCode_rename)
open SyntaxFreeSubstSyntax (codeConversion codeConversion_rename termList termList_rename)
open SyntaxRenameJudgmentSyntax (renamed renamed_rename)
open FormulaCodeSyntax (formulaCode formulaCode_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem input_of_substituted {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (substituted w b a c L n q)) : Derives Γ (input w b a c L n) := by
  let H := body w b a c L n q
  let Δ := Context.add H (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_substituted w b a c L n q _ hq
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw H)
  have hi := SyntaxRenameOutput.input_of_renamed (SyntaxRenameBinders.zf_under_2 hZ H)
    _ _ _ _ _ _ _ _ _ hw2 (.conjR (.conjR hH))
  have hs := SyntaxFreeSubstCode.list_of_conversion _ _ _ _ _ (.conjL (.conjR hH))
  have ho : Derives Δ (input w.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc n.castSucc.castSucc) :=
    .conjI (.conjL hi) hs
  exact of_eq (by simp only [Formula.raise, input_rename]) ho

theorem target_type {m} {Γ : Context m} (w b a c L n q : Fin m)
    (hq : Derives Γ (substituted w b a c L n q)) : Derives Γ (formulaCode w q b c) := by
  let H := body w b a c L n q
  let Δ := Context.add H (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_substituted w b a c L n q _ hq
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have ho := SyntaxRenameJudgment.target_type _ _ _ _ _ _ _ _ _ (.conjR (.conjR hH))
  exact of_eq (by simp only [Formula.raise, formulaCode_rename]) ho

theorem source_type {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n q : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (substituted w b a c L n q)) : Derives Γ (formulaCode w n b a) :=
  .conjL (input_of_substituted hZ w b a c L n q hw hq)

theorem output_natural {m} {Γ : Context m} (w b a c L n q : Fin m)
    (hq : Derives Γ (substituted w b a c L n q)) : Derives Γ (.mem q w) :=
  .conjL (FormulaCodeProperties.guards w q b c (target_type w b a c L n q hq))

theorem exists_at_codes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n R S : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (formulaCode w n b a))
    (hr : Derives Γ (identityCode w b R)) (hs : Derives Γ (codeConversion w a c L S)) :
    Derives Γ (existsOutput w b a c L n) := by
  have hi : Derives Γ (SyntaxRenameOutputSyntax.input w R S b a b c n) :=
    .conjI hc (.conjI (SyntaxIdentityCode.map_code w b R hr) (SyntaxFreeSubstCode.map_of_conversion w a c L S hs))
  have he := SyntaxRenameOutputInduction.actual_exists hZ w R S b a b c n hw hi
  let Q := renamed w.castSucc R.castSucc S.castSucc b.castSucc a.castSucc b.castSucc c.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) he
  have hr1 : Derives Δ (identityCode w.castSucc b.castSucc R.castSucc) := of_eq (identityCode_rename w b R Fin.castSucc) (under hr Q)
  have hs1 : Derives Δ (codeConversion w.castSucc a.castSucc c.castSucc L.castSucc S.castSucc) := of_eq (codeConversion_rename w a c L S Fin.castSucc) (under hs Q)
  have ho := intro_exists w.castSucc b.castSucc a.castSucc c.castSucc L.castSucc n.castSucc (Fin.last m)
    (intro_substituted _ _ _ _ _ _ _ _ _ hr1 hs1 (Derives.hyp (Or.inl rfl) : Derives Δ Q))
  exact of_eq (existsOutput_rename w b a c L n Fin.castSucc).symm ho

theorem exists_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b a c L n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (input w b a c L n)) : Derives Γ (existsOutput w b a c L n) := by
  have hc := Derives.conjL hi
  have hg := FormulaCodeProperties.guards w n b a hc
  have he := SyntaxIdentityCode.exists_code hZ w b hw (.conjL (.conjR hg))
  let R := identityCode w.castSucc b.castSucc (Fin.last m)
  let Ξ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) he
  have hZ1 := ZFContext.under hZ R
  have hw1 : Derives Ξ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hl1 : Derives Ξ (termList w.castSucc a.castSucc c.castSucc L.castSucc) :=
    of_eq (termList_rename w a c L Fin.castSucc) (under (.conjR hi) R)
  let S := codeConversion w.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc L.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add S (Context.image Formula.raise Ξ)
  apply Derives.exE (p := S) (SyntaxFreeSubstCode.from_list hZ1 _ _ _ _ hw1 hl1)
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (omega_rename _ Fin.castSucc) (under hw1 S)
  have hc2 : Derives Δ (formulaCode w.castSucc.castSucc n.castSucc.castSucc b.castSucc.castSucc a.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, formulaCode_rename]) (under (under hc R) S)
  have hR : Derives Ξ R := .hyp (Or.inl rfl)
  have hr2 : Derives Δ (identityCode w.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc) :=
    of_eq (by simp only [R, Formula.raise, identityCode_rename]) (under hR S)
  have ho := exists_at_codes (ZFContext.under hZ1 S) _ _ _ _ _ _ _ _ hw2 hc2 hr2 (Derives.hyp (Or.inl rfl) : Derives Δ S)
  exact of_eq (by simp only [Formula.raise, existsOutput_rename]) ho
end PPAC.Migration.Internal.SyntaxFormulaFreeSubstOutput
