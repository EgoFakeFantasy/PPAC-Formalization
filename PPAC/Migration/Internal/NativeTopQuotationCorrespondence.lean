import PPAC.Migration.Internal.NativeTopQuotationAtCodes

/-! 原首槽公式操作的专门quotation双条件；实际环境码对在对象存在量词内取得并消去。 -/
namespace PPAC.Migration.Internal.NativeTopQuotationCorrespondence
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem instantiate_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) (replacement : PureSyntaxQuotation.Tm bound free)
    (w a b A t n q : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bound.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (ht : Derives Γ (PureQuotationSyntax.term replacement w t))
    (hn : Derives Γ (PureQuotationSyntax.formula input w n))
    (hA : Derives Γ (successor A a)) :
    Derives Γ ((SyntaxTopFormulaSyntax.instantiated w a b A t n q).iff (PureQuotationSyntax.formula (input.instantiateTop replacement) w q)) := by
  have htType := PureQuotationTermTyping.term_type hZ replacement w a b t hw ha hb ht
  have hex := SyntaxTopCodedEnvironmentExistence.instantiate_exists hZ w a b A t hw (.conjI htType hA)
  let E := SyntaxTopCodedEnvironmentSyntax.instantiateCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ hex
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw E)
  have ha2 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 ha E)
  have hb2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hb E)
  have ht2 : Derives Δ (PureQuotationSyntax.term replacement w.castSucc.castSucc t.castSucc.castSucc) := of_eq (by simp only [Formula.raise, PureQuotationSyntax.term_rename]) (SyntaxRenameBinders.under_2 ht E)
  have hn2 : Derives Δ (PureQuotationSyntax.formula input w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, PureQuotationSyntax.formula_rename]) (SyntaxRenameBinders.under_2 hn E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho := NativeTopQuotationAtCodes.instantiate_at_codes hZ2 input replacement w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 ha2 hb2 hE ht2 hn2
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, SyntaxTopFormulaSyntax.instantiated_rename, PureQuotationSyntax.formula_rename]) ho

theorem abstract_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (input : PureSyntaxQuotation.Fm bound (YesMetaZFC.SetTheory.SetSort.set :: free))
    (w a b A B n q : Fin m)
    (hw : Derives Γ (omega w))
    (ha : Derives Γ (SyntaxNumeralSyntax.numeral bound.length a))
    (hb : Derives Γ (SyntaxNumeralSyntax.numeral free.length b))
    (hn : Derives Γ (PureQuotationSyntax.formula input w n))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B b)) :
    Derives Γ ((SyntaxTopFormulaSyntax.abstracted w a b A B n q).iff (PureQuotationSyntax.formula (input.abstractFreeTop) w q)) := by
  have hContexts := PureQuotationTermTyping.contexts_of_lengths hZ bound.length free.length w a b hw ha hb
  have hex := SyntaxTopCodedEnvironmentExistence.abstract_exists hZ w a b A B hw (.conjI hContexts (.conjI hA hB))
  let E := SyntaxTopCodedEnvironmentSyntax.abstractCoded w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply SyntaxRenameBinders.eliminate_2 E _ hex
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ E
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw E)
  have ha2 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length a.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 ha E)
  have hb2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length b.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hb E)
  have hn2 : Derives Δ (PureQuotationSyntax.formula input w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, PureQuotationSyntax.formula_rename]) (SyntaxRenameBinders.under_2 hn E)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have ho := NativeTopQuotationAtCodes.abstract_at_codes hZ2 input w.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc A.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc q.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 ha2 hb2 hE hn2
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, SyntaxTopFormulaSyntax.abstracted_rename, PureQuotationSyntax.formula_rename]) ho

end PPAC.Migration.Internal.NativeTopQuotationCorrespondence
