import PPAC.Migration.Internal.OriginalQuotationForestLength

/-! 以真实原结构森林码表示任意纯项像列表；全部实际码与列表值为内部对象。 -/
namespace PPAC.Migration.Internal.TermImageQuotationSyntax
open Source SourceAlgebra SourceLogic
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree)

def trees {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) : List Tree :=
  values.map PureSyntaxQuotation.termTree

theorem trees_length {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) :
    (trees values).length = values.length := List.length_map _

def mappedIndex {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (j : Fin values.length) : Fin (trees values).length :=
  ⟨j.val, by simpa only [trees_length] using j.isLt⟩

theorem trees_get {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (j : Fin values.length) :
    (trees values).get (mappedIndex values j) = PureSyntaxQuotation.termTree (values.get j) := by
  simp only [trees, mappedIndex, List.get_eq_getElem, List.getElem_map]

def images {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w L : Fin m) : Formula m :=
  OriginalTreeQuotationSyntax.forest (trees values) w L

def existsImages {m} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (w : Fin m) : Formula m :=
  OriginalTreeQuotationSyntax.forestExists (trees values) w

theorem images_rename {m k} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free))
    (w L : Fin m) (ρ : Fin m → Fin k) : (images values w L).rename ρ = images values (ρ w) (ρ L) :=
  OriginalTreeQuotationSyntax.forest_rename _ w L ρ

theorem existsImages_rename {m k} {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free))
    (w : Fin m) (ρ : Fin m → Fin k) : (existsImages values w).rename ρ = existsImages values (ρ w) :=
  OriginalTreeQuotationSyntax.forestExists_rename _ w ρ

end PPAC.Migration.Internal.TermImageQuotationSyntax
