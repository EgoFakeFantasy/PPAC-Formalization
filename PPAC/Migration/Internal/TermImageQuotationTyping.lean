import PPAC.Migration.Internal.TermImageQuotationFields

/-! 项像quotation码在全部内部域位置具有准确Term类型，因而实际构成原混合环境列表。 -/
namespace PPAC.Migration.Internal.TermImageQuotationTyping
open Source SourceAlgebra SourceLogic OmegaSyntax TermImageQuotationSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem typed_fields {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (values : List (PureSyntaxQuotation.Tm bound free)) (w a c d L : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (SyntaxNumeralSyntax.numeral values.length a))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral bound.length c)) (hd : Derives Γ (SyntaxNumeralSyntax.numeral free.length d))
    (hL : Derives Γ (images values w L)) : Derives Γ (SyntaxMixedImageCodeSyntax.typedFields w a c d L) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let B := (Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj
    (StructuralListFieldSyntax.field w.castSucc.castSucc L.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ B
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw B)
  have ha2 : Derives Δ (SyntaxNumeralSyntax.numeral values.length a.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 ha B)
  have hc2 : Derives Δ (SyntaxNumeralSyntax.numeral bound.length c.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hc B)
  have hd2 : Derives Δ (SyntaxNumeralSyntax.numeral free.length d.castSucc.castSucc) := of_eq (by simp only [Formula.raise, SyntaxNumeralSyntax.numeral_rename]) (SyntaxRenameBinders.under_2 hd B)
  have hL2 : Derives Δ (images values w.castSucc.castSucc L.castSucc.castSucc) := of_eq (by simp only [Formula.raise, images_rename]) (SyntaxRenameBinders.under_2 hL B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hBelow := Derives.impE (.conjL (SyntaxNumeralMembers.member_iff hZ2 values.length a.castSucc.castSucc (Fin.last m).castSucc ha2)) (.conjL hB)
  have hi : Derives Δ ((SyntaxPositionSyntax.below values.length (Fin.last m).castSucc).imp
      (SyntaxTermSyntax.term w.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)))) := by
    apply SyntaxPositionSyntax.below_imp
    intro j
    apply Derives.impI
    let J := SyntaxNumeralSyntax.numeral j.val (Fin.last m).castSucc
    let Ξ := Context.add J Δ
    have hJ : Derives Ξ J := .hyp (Or.inl rfl)
    have hQ := Derives.impE (.conjL (TermImageQuotationFields.field_at (ZFContext.add hZ2 J) values w.castSucc.castSucc L.castSucc.castSucc j (Fin.last m).castSucc (Fin.last (m+1)) (add hw2 J) (add hL2 J) hJ)) (.conjR (add hB J))
    exact PureQuotationTermTyping.term_type (ZFContext.add hZ2 J) (values.get j) w.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)) (add hw2 J) (add hc2 J) (add hd2 J) hQ
  exact Derives.impE hi hBelow

theorem term_list {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (values : List (PureSyntaxQuotation.Tm bound free)) (w a c d L : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (SyntaxNumeralSyntax.numeral values.length a))
    (hc : Derives Γ (SyntaxNumeralSyntax.numeral bound.length c)) (hd : Derives Γ (SyntaxNumeralSyntax.numeral free.length d))
    (hL : Derives Γ (images values w L)) : Derives Γ (SyntaxMixedImageCodeSyntax.termList w a c d L) :=
  .conjI (SyntaxNumerals.range hZ values.length w a hw ha)
    (.conjI (PureQuotationTermTyping.contexts_of_lengths hZ bound.length free.length w c d hw hc hd)
      (.conjI (.conjI (TermImageQuotationFields.range hZ values w L hw hL) (TermImageQuotationFields.length_at hZ values w L a hw hL ha))
        (typed_fields hZ values w a c d L hw ha hc hd hL)))

end PPAC.Migration.Internal.TermImageQuotationTyping
