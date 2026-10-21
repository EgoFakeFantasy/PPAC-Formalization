import PPAC.Migration.Internal.ZFArithmetic

/-! 乘法输入等词替换只使用原eqSubst，不抽取宿主算术函数。 -/
namespace PPAC.Migration.Internal.NaturalMultiplicationTransport
open Source SourceAlgebra SourceLogic NaturalMultiplicationSyntax

theorem index_subst {m} {Γ : Context m} (w a n s y : Fin m) (he : Derives Γ (.equal n s))
    (hy : Derives Γ (product w a n y)) : Derives Γ (product w a s y) := by
  have hi : Derives Γ ((product w.castSucc a.castSucc (Fin.last m) y.castSucc).instantiate n) := by
    simpa only [Formula.instantiate, product_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy
  have ho := Derives.eqSubst (product w.castSucc a.castSucc (Fin.last m) y.castSucc) he hi
  simpa only [Formula.instantiate, product_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem left_subst {m} {Γ : Context m} (w a b n y : Fin m) (he : Derives Γ (.equal a b))
    (hy : Derives Γ (product w a n y)) : Derives Γ (product w b n y) := by
  have hi : Derives Γ ((product w.castSucc (Fin.last m) n.castSucc y.castSucc).instantiate a) := by
    simpa only [Formula.instantiate, product_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy
  have ho := Derives.eqSubst (product w.castSucc (Fin.last m) n.castSucc y.castSucc) he hi
  simpa only [Formula.instantiate, product_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
end PPAC.Migration.Internal.NaturalMultiplicationTransport
