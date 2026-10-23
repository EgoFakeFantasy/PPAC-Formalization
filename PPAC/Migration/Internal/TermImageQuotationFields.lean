import PPAC.Migration.Internal.TermImageQuotationSyntax

/-! 实际项像quotation列表的原长度、自然范围、精确字段和唯一性。 -/
namespace PPAC.Migration.Internal.TermImageQuotationFields
open Source SourceAlgebra SourceLogic OmegaSyntax TermImageQuotationSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem field_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (values : List (PureSyntaxQuotation.Tm bound free)) (w L : Fin m) (j : Fin values.length) (i q : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (images values w L)) (hi : Derives Γ (SyntaxNumeralSyntax.numeral j.val i)) :
    Derives Γ ((StructuralListFieldSyntax.field w L i q).iff (PureQuotationSyntax.term (values.get j) w q)) := by
  have ho := OriginalQuotationForestRead.field_at hZ (trees values) w L (mappedIndex values j) i q hw hL hi
  exact of_eq (by simp only [trees_get, PureQuotationSyntax.term]) ho

theorem length_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (values : List (PureSyntaxQuotation.Tm bound free)) (w L a : Fin m) (hw : Derives Γ (omega w))
    (hL : Derives Γ (images values w L)) (ha : Derives Γ (SyntaxNumeralSyntax.numeral values.length a)) :
    Derives Γ (StructuralListLengthSyntax.hasLength w L a) :=
  OriginalQuotationForestLength.at_numeral hZ (trees values) w L a hw hL (of_eq (by simp only [trees_length]) ha)

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (values : List (PureSyntaxQuotation.Tm bound free)) (w L : Fin m) (hw : Derives Γ (omega w)) (hL : Derives Γ (images values w L)) :
    Derives Γ (.mem L w) := OriginalTreeQuotationProperties.forest_range hZ (trees values) w L hw hL

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (values : List (PureSyntaxQuotation.Tm bound free)) (w L K : Fin m) (hw : Derives Γ (omega w))
    (hL : Derives Γ (images values w L)) (hK : Derives Γ (images values w K)) : Derives Γ (.equal L K) :=
  OriginalTreeQuotationUnique.forest_unique hZ (trees values) w L K hw hL hK

theorem exists_images {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) {bound free : PureSyntaxQuotation.Ctx}
    (values : List (PureSyntaxQuotation.Tm bound free)) (w : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (existsImages values w) :=
  OriginalTreeQuotationExistence.forest_exists hZ (trees values) w hw

end PPAC.Migration.Internal.TermImageQuotationFields
