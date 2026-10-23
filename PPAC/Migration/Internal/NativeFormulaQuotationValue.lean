import PPAC.Migration.Internal.NativeFormulaQuotationValueSyntax

/-! 原生公式替换实际取得同值quotation/类型，且唯一性比较全部内部原替换候选。 -/
namespace PPAC.Migration.Internal.NativeFormulaQuotationValue
open Source SourceAlgebra SourceLogic OmegaSyntax NativeSubstitutionSyntax NativeFormulaQuotationValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {sb sf tb tf : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm sb sf) (σ : Mapping sb tb tf) (τ : Mapping sf tb tf) (w R S a b c d n q v : Fin m)
    (hw : Derives Γ (omega w)) (hq : Derives Γ (value input σ τ w R S a b c d n q))
    (hv : Derives Γ (value input σ τ w R S a b c d n v)) : Derives Γ (.equal q v) :=
  SyntaxMixedFormulaOutputInduction.unique hZ w R S a b c d n q v hw (.conjL hq) (.conjL hv)

theorem unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {sb sf tb tf : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm sb sf) (σ : Mapping sb tb tf) (τ : Mapping sf tb tf) (w R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (value input σ τ w R S a b c d n q)) :
    Derives Γ (SyntaxMixedFormulaOutputSyntax.uniqueOutput w R S a b c d n q) := by
  apply Derives.allI
  apply Derives.impI
  let P := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hv1 : Derives Δ (value input σ τ w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc q.castSucc) := of_eq (by simp only [Formula.raise, value_rename]) (under hv P)
  exact SyntaxMixedFormulaOutputInduction.unique (ZFContext.under hZ P) w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) q.castSucc hw1 (.hyp (Or.inl rfl)) (.conjL hv1)

theorem at_candidate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {sb sf tb tf : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm sb sf) (σ : Mapping sb tb tf) (τ : Mapping sf tb tf) (w R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral sb.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral sf.length b))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral tb.length c))
    (hd : Derives Γ (SyntaxNumeralSyntax.numeral tf.length d))
    (he : Derives Γ (environment σ τ w a b c d R S))
    (hn : Derives Γ (PureQuotationSyntax.formula input w n))
    (hq : Derives Γ (PureQuotationSyntax.formula (input.substituteMapped σ τ) w q)) :
    Derives Γ (value input σ τ w R S a b c d n q) := by
  have hs := NativeFormulaQuotationConstruct.construct hZ input σ τ w R S a b c d n q hw ha hb hc hd he hn hq
  exact .conjI hs (.conjI hq (SyntaxMixedFormulaJudgment.target_type w R S a b c d n q hs))

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {sb sf tb tf : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm sb sf) (σ : Mapping sb tb tf) (τ : Mapping sf tb tf) (w R S a b c d n : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral sb.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral sf.length b))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral tb.length c))
    (hd : Derives Γ (SyntaxNumeralSyntax.numeral tf.length d))
    (he : Derives Γ (environment σ τ w a b c d R S))
    (hn : Derives Γ (PureQuotationSyntax.formula input w n)) :
    Derives Γ (NativeFormulaQuotationValueSyntax.fiber input σ τ w R S a b c d n) := by
  have hex := OriginalTreeQuotationExistence.tree_exists hZ (PureSyntaxQuotation.formulaTree (input.substituteMapped σ τ)) w hw
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (PureQuotationSyntax.formula (input.substituteMapped σ τ) w.castSucc (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) hex
  have hZ1 := ZFContext.under hZ Q
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw Q)
  have ha1 : Derives Δ (SyntaxNumeralSyntax.numeral sb.length a.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under ha Q)
  have hb1 : Derives Δ (SyntaxNumeralSyntax.numeral sf.length b.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hb Q)
  have hc1 : Derives Δ (SyntaxNumeralSyntax.numeral tb.length c.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hc Q)
  have hd1 : Derives Δ (SyntaxNumeralSyntax.numeral tf.length d.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hd Q)
  have he1 : Derives Δ (environment σ τ w.castSucc a.castSucc b.castSucc c.castSucc d.castSucc R.castSucc S.castSucc) := of_eq (by simp only [Formula.raise, environment_rename]) (under he Q)
  have hn1 : Derives Δ (PureQuotationSyntax.formula input w.castSucc n.castSucc) := of_eq (by simp only [Formula.raise, PureQuotationSyntax.formula_rename]) (under hn Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hv := at_candidate hZ1 input σ τ w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hw1 ha1 hb1 hc1 hd1 he1 hn1 (.conjR hQ)
  have hu := unique_output hZ1 input σ τ w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hw1 hv
  have ho := intro_fiber input σ τ w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hv hu
  exact of_eq (by simp only [Formula.raise, NativeFormulaQuotationValueSyntax.fiber_rename]) ho

end PPAC.Migration.Internal.NativeFormulaQuotationValue
