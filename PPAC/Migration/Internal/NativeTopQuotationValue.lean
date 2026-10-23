import PPAC.Migration.Internal.NativeTopQuotationValueSyntax

/-! 首槽实际输出同时具有原操作、准确quotation及类型；唯一性比较全部原首槽候选。 -/
namespace PPAC.Migration.Internal.NativeTopQuotationValue
open Source SourceAlgebra SourceLogic OmegaSyntax NativeTopQuotationValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem instantiate_at_candidate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free)
    (w a b A t n q : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bound.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (ht : Derives Γ (PureQuotationSyntax.term replacement w t))
    (hn : Derives Γ (PureQuotationSyntax.formula input w n))
    (hA : Derives Γ (successor A a))
    (hq : Derives Γ (PureQuotationSyntax.formula (input.instantiateTop replacement) w q)) :
    Derives Γ (instantiateValue input replacement w a b A t n q) := by
  have hiff := NativeTopQuotationCorrespondence.instantiate_iff hZ input replacement w a b A t n q hw ha hb ht hn hA
  have hjud := Derives.impE (.conjR hiff) hq
  exact .conjI hjud (.conjI hq (SyntaxTopFormulaTyping.instantiate_target_type w a b A t n q hjud))

theorem instantiate_actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free)
    (w a b A t n : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bound.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (ht : Derives Γ (PureQuotationSyntax.term replacement w t))
    (hn : Derives Γ (PureQuotationSyntax.formula input w n))
    (hA : Derives Γ (successor A a)) :
    Derives Γ (instantiateFiber input replacement w a b A t n) := by
  have hex := OriginalTreeQuotationExistence.tree_exists hZ (PureSyntaxQuotation.formulaTree (input.instantiateTop replacement)) w hw
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (PureQuotationSyntax.formula (input.instantiateTop replacement) w.castSucc (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) hex
  have hZ1 := ZFContext.under hZ Q
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw Q)
  have ha1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under ha Q)
  have hb1 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hb Q)
  have ht1 : Derives Δ (PureQuotationSyntax.term replacement w.castSucc t.castSucc) := of_eq (by simp only [Formula.raise, PureQuotationSyntax.term_rename]) (under ht Q)
  have hn1 : Derives Δ (PureQuotationSyntax.formula input w.castSucc n.castSucc) := of_eq (by simp only [Formula.raise, PureQuotationSyntax.formula_rename]) (under hn Q)
  have hA1 : Derives Δ (successor A.castSucc a.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (under hA Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hv := instantiate_at_candidate hZ1 input replacement w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc (Fin.last m) hw1 ha1 hb1 ht1 hn1 hA1 (.conjR hQ)
  have hu := SyntaxTopFormulaUnique.instantiate_unique_output hZ1 w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc (Fin.last m) hw1 (.conjL hv)
  have ho := intro_instantiate_fiber input replacement w.castSucc a.castSucc b.castSucc A.castSucc t.castSucc n.castSucc (Fin.last m) hv hu
  exact of_eq (by simp only [Formula.raise, instantiateFiber_rename]) ho

theorem abstract_at_candidate {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free))
    (w a b A B n q : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bound.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (hn : Derives Γ (PureQuotationSyntax.formula input w n))
    (hA : Derives Γ (successor A a))
    (hB : Derives Γ (successor B b))
    (hq : Derives Γ (PureQuotationSyntax.formula (input.abstractFreeTop) w q)) :
    Derives Γ (abstractValue input w a b A B n q) := by
  have hiff := NativeTopQuotationCorrespondence.abstract_iff hZ input w a b A B n q hw ha hb hn hA hB
  have hjud := Derives.impE (.conjR hiff) hq
  exact .conjI hjud (.conjI hq (SyntaxTopFormulaTyping.abstract_target_type w a b A B n q hjud))

theorem abstract_actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx} (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free))
    (w a b A B n : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bound.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (hn : Derives Γ (PureQuotationSyntax.formula input w n))
    (hA : Derives Γ (successor A a))
    (hB : Derives Γ (successor B b)) :
    Derives Γ (abstractFiber input w a b A B n) := by
  have hex := OriginalTreeQuotationExistence.tree_exists hZ (PureSyntaxQuotation.formulaTree (input.abstractFreeTop)) w hw
  let Q := (Formula.mem (Fin.last m) w.castSucc).conj (PureQuotationSyntax.formula (input.abstractFreeTop) w.castSucc (Fin.last m))
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply Derives.exE (p := Q) hex
  have hZ1 := ZFContext.under hZ Q
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (under hw Q)
  have ha1 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under ha Q)
  have hb1 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (under hb Q)
  have hn1 : Derives Δ (PureQuotationSyntax.formula input w.castSucc n.castSucc) := of_eq (by simp only [Formula.raise, PureQuotationSyntax.formula_rename]) (under hn Q)
  have hA1 : Derives Δ (successor A.castSucc a.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (under hA Q)
  have hB1 : Derives Δ (successor B.castSucc b.castSucc) := of_eq (by simp only [Formula.raise, successor_rename]) (under hB Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hv := abstract_at_candidate hZ1 input w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc (Fin.last m) hw1 ha1 hb1 hn1 hA1 hB1 (.conjR hQ)
  have hu := SyntaxTopFormulaUnique.abstract_unique_output hZ1 w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc (Fin.last m) hw1 (.conjL hv)
  have ho := intro_abstract_fiber input w.castSucc a.castSucc b.castSucc A.castSucc B.castSucc n.castSucc (Fin.last m) hv hu
  exact of_eq (by simp only [Formula.raise, abstractFiber_rename]) ho

end PPAC.Migration.Internal.NativeTopQuotationValue
