import PPAC.Migration.Internal.SyntaxMixedFormulaReadTransfer

/-! 严格子源码守卫下的全部逻辑字段双条件；仍使用原19条源规则。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaFieldsTransfer
open SyntaxRenameQuerySyntax (of_eq)
open Source SourceAlgebra SourceLogic OrdinalSyntax SyntaxMixedFormulaQuerySyntax FormulaCodeCongruence SyntaxTypeLocalTransfer
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem guarded_congr {m} {Γ : Context m} {B p q : Formula m}
    (hh : Derives (Context.add B Γ) (p.iff q)) : Derives Γ ((B.conj p).iff (B.conj q)) := by
  have hi := Derives.impI hh
  apply Derives.conjI
  · apply Derives.impI
    have hp : Derives (Context.add (B.conj p) Γ) (B.conj p) := .hyp (Or.inl rfl)
    have he := Derives.impE (add hi _) (.conjL hp)
    exact .conjI (.conjL hp) (.impE (.conjL he) (.conjR hp))
  · apply Derives.impI
    have hq : Derives (Context.add (B.conj q) Γ) (B.conj q) := .hyp (Or.inl rfl)
    have he := Derives.impE (add hi _) (.conjL hq)
    exact .conjI (.conjL hq) (.impE (.conjR he) (.conjR hq))

theorem single_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (w h r s a b c d n q x X : Fin m) (hn : Derives Γ (ordinal n))
    (hg : Derives Γ (SyntaxMixedFormulaRecursionSyntax.graph w h n)) :
    Derives Γ ((SyntaxMixedFormulaLogicalSyntax.singleData tag advance w h r s a b c d n q x X).iff
      (SyntaxMixedFormulaRecursiveSyntax.singleData tag advance w r s a b c d n q x X)) := by
  apply conj_congr (iff_refl (SyntaxLogicalSyntax.singleCode tag w x n))
  apply guarded_congr
  let B := Formula.mem x n
  have hx : Derives (Context.add B Γ) B := .hyp (Or.inl rfl)
  have he := SyntaxMixedFormulaReadTransfer.check_iff (ZFContext.add hZ B) advance w h n x r s a b c d X (add hn B) hx (add hg B)
  exact conj_congr (iff_refl (SyntaxLogicalSyntax.singleCode tag w X q)) he

theorem binary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w h r s a b c d n q x y X Y : Fin m) (hn : Derives Γ (ordinal n))
    (hg : Derives Γ (SyntaxMixedFormulaRecursionSyntax.graph w h n)) :
    Derives Γ ((SyntaxMixedFormulaLogicalSyntax.binaryData kind w h r s a b c d n q x y X Y).iff
      (SyntaxMixedFormulaRecursiveSyntax.binaryData kind w r s a b c d n q x y X Y)) := by
  apply conj_congr (iff_refl (SyntaxLogicalSyntax.binaryCode kind w x y n))
  apply guarded_congr
  apply guarded_congr
  let B := Formula.mem x n
  let C := Formula.mem y n
  let Δ := Context.add C (Context.add B Γ)
  have hx : Derives Δ B := .hyp (Or.inr (Or.inl rfl))
  have hy : Derives Δ C := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.add (ZFContext.add hZ B) C
  have hn2 := add (add hn B) C
  have hg2 := add (add hg B) C
  have hxI := SyntaxMixedFormulaJudgment.read_iff hZ2 w h n x r s a b c d X hn2 hx hg2
  have hyI := SyntaxMixedFormulaJudgment.read_iff hZ2 w h n y r s a b c d Y hn2 hy hg2
  exact conj_congr (iff_refl (SyntaxLogicalSyntax.binaryCode kind w X Y q)) (conj_congr hxI hyI)
end PPAC.Migration.Internal.SyntaxMixedFormulaFieldsTransfer
