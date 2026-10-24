import PPAC.Migration.Internal.FixedAxiomPacketSyntax

/-! 叶包算术的输入等词传输与非零基数；均为原对象等词规则。 -/
namespace PPAC.Migration.Internal.FixedAxiomPacketArithmetic
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix NaturalMultiplicationSyntax.product NaturalAdditionSyntax.sum SyntaxNumeralSyntax.numeral

theorem mul_inputs {m} {Γ : Context m} (w a b c d y : Fin m)
    (ha : Derives Γ (.equal a c)) (hb : Derives Γ (.equal b d))
    (hy : Derives Γ (NaturalMultiplicationSyntax.product w a b y)) : Derives Γ (NaturalMultiplicationSyntax.product w c d y) := by
  let L := NaturalMultiplicationSyntax.product w.castSucc (Fin.last m) b.castSucc y.castSucc
  let R := NaturalMultiplicationSyntax.product w.castSucc c.castSucc (Fin.last m) y.castSucc
  have hL0 : L.instantiate a = NaturalMultiplicationSyntax.product w a b y := by simp only [L, Formula.instantiate, NaturalMultiplicationSyntax.product_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hL1 : L.instantiate c = NaturalMultiplicationSyntax.product w c b y := by simp only [L, Formula.instantiate, NaturalMultiplicationSyntax.product_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hR0 : R.instantiate b = NaturalMultiplicationSyntax.product w c b y := by simp only [R, Formula.instantiate, NaturalMultiplicationSyntax.product_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hR1 : R.instantiate d = NaturalMultiplicationSyntax.product w c d y := by simp only [R, Formula.instantiate, NaturalMultiplicationSyntax.product_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq hR1 (Derives.eqSubst R hb (of_eq hR0.symm (of_eq hL1 (Derives.eqSubst L ha (of_eq hL0.symm hy)))))

theorem add_inputs {m} {Γ : Context m} (w a b c d y : Fin m)
    (ha : Derives Γ (.equal a c)) (hb : Derives Γ (.equal b d))
    (hy : Derives Γ (NaturalAdditionSyntax.sum w a b y)) : Derives Γ (NaturalAdditionSyntax.sum w c d y) := by
  let L := NaturalAdditionSyntax.sum w.castSucc (Fin.last m) b.castSucc y.castSucc
  let R := NaturalAdditionSyntax.sum w.castSucc c.castSucc (Fin.last m) y.castSucc
  have hL0 : L.instantiate a = NaturalAdditionSyntax.sum w a b y := by simp only [L, Formula.instantiate, NaturalAdditionSyntax.sum_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hL1 : L.instantiate c = NaturalAdditionSyntax.sum w c b y := by simp only [L, Formula.instantiate, NaturalAdditionSyntax.sum_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hR0 : R.instantiate b = NaturalAdditionSyntax.sum w c b y := by simp only [R, Formula.instantiate, NaturalAdditionSyntax.sum_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have hR1 : R.instantiate d = NaturalAdditionSyntax.sum w c d y := by simp only [R, Formula.instantiate, NaturalAdditionSyntax.sum_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq hR1 (Derives.eqSubst R hb (of_eq hR0.symm (of_eq hL1 (Derives.eqSubst L ha (of_eq hL0.symm hy)))))

theorem base_nonempty {m} {Γ : Context m} (x : Fin m) (hx : Derives Γ (SyntaxNumeralSyntax.numeral 256 x)) :
    Derives Γ (empty x).neg := by
  let B := (SyntaxNumeralSyntax.numeral 255 (Fin.last m)).conj (successor x.castSucc (Fin.last m))
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply SyntaxNumeralSyntax.eliminate_succ 255 x _ hx
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hm := InsertLogic.new_member x.castSucc (Fin.last m) (Fin.last m) (.conjR hB)
  have ho : Derives Δ (empty x.castSucc).neg := by
    apply Derives.impI
    exact .impE (empty_at x.castSucc (Fin.last m) (.hyp (Or.inl rfl))) (add hm _)
  exact of_eq (by simp only [Formula.raise, Formula.neg, Formula.rename, empty_rename]) ho

end PPAC.Migration.Internal.FixedAxiomPacketArithmetic
