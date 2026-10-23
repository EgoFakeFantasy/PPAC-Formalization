import PPAC.Migration.Internal.NativeFormulaQuotationConstruct

/-! 全11原生公式替换的quotation双条件，所有候选输出码仍为内部对象。 -/
namespace PPAC.Migration.Internal.NativeFormulaQuotationCorrespondence
open Source SourceAlgebra SourceLogic OmegaSyntax NativeSubstitutionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem formula_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {sb sf : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm sb sf) {tb tf : PureSyntaxQuotation.Ctx} (σ : Mapping sb tb tf) (τ : Mapping sf tb tf)
    (w R S a b c d n q : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral sb.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral sf.length b))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral tb.length c))
    (hd : Derives Γ (SyntaxNumeralSyntax.numeral tf.length d))
    (he : Derives Γ (environment σ τ w a b c d R S))
    (hn : Derives Γ (PureQuotationSyntax.formula input w n)) :
    Derives Γ ((SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q).iff
      (PureQuotationSyntax.formula (input.substituteMapped σ τ) w q)) := by
  have hex := OriginalTreeQuotationExistence.tree_exists hZ (PureSyntaxQuotation.formulaTree (input.substituteMapped σ τ)) w hw
  apply Derives.conjI
  · apply Derives.impI
    let P := SyntaxMixedFormulaJudgmentSyntax.substituted w R S a b c d n q
    let Ξ := Context.add P Γ
    let Q := (Formula.mem (Fin.last m) w.castSucc).conj (PureQuotationSyntax.formula (input.substituteMapped σ τ) w.castSucc (Fin.last m))
    let Δ := Context.add Q (Context.image Formula.raise Ξ)
    apply Derives.exE (p := Q) (add hex P)
    have hZ1 := ZFContext.under (ZFContext.add hZ P) Q
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under (add hw P) Q)
    have ha1 : Derives Δ (SyntaxNumeralSyntax.numeral sb.length a.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under (add ha P) Q)
    have hb1 : Derives Δ (SyntaxNumeralSyntax.numeral sf.length b.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under (add hb P) Q)
    have hc1 : Derives Δ (SyntaxNumeralSyntax.numeral tb.length c.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under (add hc P) Q)
    have hd1 : Derives Δ (SyntaxNumeralSyntax.numeral tf.length d.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under (add hd P) Q)
    have he1 : Derives Δ (environment σ τ w.castSucc a.castSucc b.castSucc c.castSucc d.castSucc R.castSucc S.castSucc) := of_eq (by simp only [Formula.raise, environment_rename]) (under (add he P) Q)
    have hn1 : Derives Δ (PureQuotationSyntax.formula input w.castSucc n.castSucc) := of_eq (by simp only [Formula.raise, PureQuotationSyntax.formula_rename]) (under (add hn P) Q)
    have hP : Derives Ξ P := .hyp (Or.inl rfl)
    have hP1 : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc q.castSucc) := of_eq (by simp only [P, Formula.raise, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]) (under hP Q)
    have hQ : Derives Δ Q := .hyp (Or.inl rfl)
    have hSub := NativeFormulaQuotationConstruct.construct hZ1 input σ τ w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) hw1 ha1 hb1 hc1 hd1 he1 hn1 (.conjR hQ)
    have heq := SyntaxMixedFormulaOutputInduction.unique hZ1 w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m) q.castSucc hw1 hSub hP1
    have ho := OriginalQuotationValue.tree_output_subst (PureSyntaxQuotation.formulaTree (input.substituteMapped σ τ)) w.castSucc (Fin.last m) q.castSucc heq (.conjR hQ)
    exact of_eq (PureQuotationSyntax.formula_rename (input.substituteMapped σ τ) w q Fin.castSucc).symm ho
  · apply Derives.impI
    exact NativeFormulaQuotationConstruct.construct (ZFContext.add hZ _) input σ τ w R S a b c d n q (add hw _) (add ha _) (add hb _) (add hc _) (add hd _) (add he _) (add hn _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.NativeFormulaQuotationCorrespondence
