import PPAC.Migration.Internal.TermQuotationBinderValues

/-! 原混合binder对应的外部纯项模式：新增bound零头，两类旧项像均提升目标bound上下文。 -/
namespace PPAC.Migration.Internal.TermQuotationLiftSyntax
open Source SourceAlgebra SourceLogic

def shifted {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) :
    List (PureSyntaxQuotation.Tm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) :=
  values.map (fun t => t.weakenBound YesMetaZFC.SetTheory.SetSort.set)

def newBound {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) :
    List (PureSyntaxQuotation.Tm (YesMetaZFC.SetTheory.SetSort.set :: bound) free) := .bvar .here :: shifted values

theorem shifted_length {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) :
    (shifted values).length = values.length := List.length_map _

theorem newBound_length {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) :
    (newBound values).length = values.length+1 := by simp only [newBound, List.length_cons, shifted_length]

def originalIndex {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free))
    (j : Fin (shifted values).length) : Fin values.length := ⟨j.val, by simpa only [shifted_length] using j.isLt⟩

theorem shifted_get {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (j : Fin (shifted values).length) :
    (shifted values).get j = (values.get (originalIndex values j)).weakenBound YesMetaZFC.SetTheory.SetSort.set := by
  rcases j with ⟨j, hj⟩
  simp only [shifted, originalIndex, List.get_eq_getElem, List.getElem_map]

theorem newBound_get_zero {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) :
    (newBound values).get ⟨0, by exact Nat.zero_lt_succ (shifted values).length⟩ = .bvar .here := rfl

theorem newBound_get_succ {bound free : PureSyntaxQuotation.Ctx} (values : List (PureSyntaxQuotation.Tm bound free)) (j : Fin (shifted values).length) :
    (newBound values).get j.succ = (values.get (originalIndex values j)).weakenBound YesMetaZFC.SetTheory.SetSort.set := by
  simp only [newBound, List.get_cons_succ', shifted_get]

end PPAC.Migration.Internal.TermQuotationLiftSyntax
