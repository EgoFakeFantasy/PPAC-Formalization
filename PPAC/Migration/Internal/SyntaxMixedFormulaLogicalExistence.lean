import PPAC.Migration.Internal.SyntaxMixedFormulaLogicalConstruct

/-! 内部 Earlier 下七类逻辑模式实际取得父输出，量词真实提升已在子输出存在中消去。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaLogicalExistence
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxMixedFormulaOutputSyntax SyntaxLogicalSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (valid : (tag = 4 ∧ advance = false) ∨ (tag = 9 ∧ advance = true) ∨ (tag = 10 ∧ advance = true))
    (w R S a b c d n x : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n)) (hi : Derives Γ (input w R S a b c d n))

    (hc : Derives Γ (singleCode tag w x n)) : Derives Γ (existsOutput w R S a b c d n) := by
  have hn := SyntaxMixedFormulaOutput.input_natural w R S a b c d n hi
  have hb := SyntaxLogicalFields.single_bound hZ tag w x n hw hc
  have hT := Derives.impE (.conjL (SyntaxMixedFormulaLogicalConstruct.single_types hZ tag advance valid w a b x n hw hc)) (.conjL hi)
  have hxN := StructuralListTraceOrder.member_member hZ w x n hw hn hb
  have hp := earlier_at w n x he hxN hb
  have hEx := SyntaxMixedFormulaCheckExistence.exists_at_property hZ advance w x R S a b c d hw hp (.conjR hT) (.conjR hi)
  let X := SyntaxMixedFormulaRecursiveSyntax.check advance w.castSucc x.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m)
  let Ξ := Context.add X (Context.image Formula.raise Γ)
  apply Derives.exE (p := X) hEx
  have hw1 : Derives Ξ (omega w.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (under (hw) X)
  have hi1 : Derives Ξ (input w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc) :=
    of_eq (by simp only [Formula.raise, input_rename]) (under (hi) X)
  have hc1 : Derives Ξ (singleCode tag w.castSucc x.castSucc n.castSucc) :=
    of_eq (by simp only [Formula.raise, singleCode_rename]) (under (hc) X)
  have ho := SyntaxMixedFormulaLogicalConstruct.single_at_outputs (ZFContext.under hZ X) tag advance valid w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc n.castSucc x.castSucc (Fin.last m) hw1 hi1 hc1 (.hyp (Or.inl rfl))
  exact of_eq (existsOutput_rename w R S a b c d n Fin.castSucc).symm ho

theorem binary_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4)
    (w R S a b c d n x y : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (earlier w n)) (hi : Derives Γ (input w R S a b c d n))

    (hc : Derives Γ (binaryCode kind w x y n)) : Derives Γ (existsOutput w R S a b c d n) := by
  have hn := SyntaxMixedFormulaOutput.input_natural w R S a b c d n hi
  have hb := SyntaxLogicalFields.binary_bounds hZ kind w x y n hw hc
  have hT := Derives.impE (.conjL (SyntaxMixedFormulaLogicalConstruct.binary_types hZ kind w a b x y n hw hc)) (.conjL hi)
  have hxN := StructuralListTraceOrder.member_member hZ w x n hw hn (.conjL hb)
  have hp := earlier_at w n x he hxN (.conjL hb)
  have hyN := StructuralListTraceOrder.member_member hZ w y n hw hn (.conjR hb)
  have hpY := earlier_at w n y he hyN (.conjR hb)
  have hEx := SyntaxMixedFormulaCheckExistence.exists_at_property hZ false w x R S a b c d hw hp (.conjL (.conjR hT)) (.conjR hi)
  let X := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc x.castSucc (Fin.last m)
  let Ξ := Context.add X (Context.image Formula.raise Γ)
  apply Derives.exE (p := X) hEx
  have hw1 : Derives Ξ (omega w.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (under (hw) X)
  have hpY1 : Derives Ξ (property w.castSucc y.castSucc) :=
    of_eq (by simp only [Formula.raise, property_rename]) (under (hpY) X)
  have hy1 : Derives Ξ (FormulaCodeSyntax.formulaCode w.castSucc y.castSucc a.castSucc b.castSucc) := of_eq (FormulaCodeSyntax.formulaCode_rename w y a b Fin.castSucc) (under (Derives.conjR (.conjR hT)) X)
  have hL1 : Derives Ξ (SyntaxMixedImageCodeSyntax.termLists w.castSucc a.castSucc b.castSucc c.castSucc d.castSucc R.castSucc S.castSucc) := of_eq (SyntaxMixedImageCodeSyntax.termLists_rename w a b c d R S Fin.castSucc) (under (Derives.conjR hi) X)
  have hEy := SyntaxMixedFormulaCheckExistence.exists_at_property (ZFContext.under hZ X) false w.castSucc y.castSucc R.castSucc S.castSucc a.castSucc b.castSucc c.castSucc d.castSucc hw1 hpY1 hy1 hL1
  let Y := SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc y.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add Y (Context.image Formula.raise Ξ)
  apply Derives.exE (p := Y) hEy
  have hw2 : Derives Δ (omega w.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, omega_rename]) (under (under (hw) X) Y)
  have hi2 : Derives Δ (input w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, input_rename]) (under (under (hi) X) Y)
  have hc2 : Derives Δ (binaryCode kind w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, binaryCode_rename]) (under (under (hc) X) Y)
  have hX : Derives Ξ X := .hyp (Or.inl rfl)
  have hx2 : Derives Δ (SyntaxMixedFormulaJudgmentSyntax.substituted w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc) := of_eq (by simp only [X, Formula.raise, SyntaxMixedFormulaJudgmentSyntax.substituted_rename]) (under hX Y)
  have ho := SyntaxMixedFormulaLogicalConstruct.binary_at_outputs (ZFContext.under (ZFContext.under hZ X) Y) kind w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc a.castSucc.castSucc b.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 hi2 hc2 hx2 (.hyp (Or.inl rfl))
  exact of_eq (by simp only [Formula.raise, existsOutput_rename]) ho

end PPAC.Migration.Internal.SyntaxMixedFormulaLogicalExistence
