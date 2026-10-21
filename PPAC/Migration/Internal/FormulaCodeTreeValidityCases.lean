import PPAC.Migration.Internal.SyntaxAtomTreeValidity

/-! 全部逻辑/量词分支以严格子码的全上下文对象归纳假设取得原树有效性。 -/
namespace PPAC.Migration.Internal.FormulaCodeTreeValidityCases
open Source SourceAlgebra SourceLogic OmegaSyntax FormulaCodeSyntax FormulaCodeRecursiveSyntax FormulaCodeTreeValiditySyntax
open SyntaxTreeValiditySyntax StructuralTreeValiditySyntax
open SyntaxLogicalSyntax (binaryTag)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem advanced_child {m} {Γ : Context m} (w n x b f : Fin m) (hi : Derives Γ (earlier w n))
    (hb : Derives Γ (.mem x n)) (hc : Derives Γ (advancedCode w x b f)) : Derives Γ (valid w x) := by
  let C := (successor (Fin.last m) b.castSucc).conj (formulaCode w.castSucc x.castSucc (Fin.last m) f.castSucc)
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply Derives.exE (p := C) hc
  have hi1 : Derives Δ (earlier w.castSucc n.castSucc) := by
    simpa only [Formula.raise, earlier_rename] using under hi C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hout := child w.castSucc n.castSucc x.castSucc (Fin.last m) f.castSucc hi1 (under hb C) (.conjR hC)
  simpa only [Formula.raise, valid_rename] using hout

theorem step_child {m} {Γ : Context m} (advance : Bool) (w n x b f : Fin m) (hi : Derives Γ (earlier w n))
    (hb : Derives Γ (.mem x n)) (hc : Derives Γ (stepCheck advance w x b f)) : Derives Γ (valid w x) := by
  cases advance
  · exact child w n x b f hi hb hc
  · exact advanced_child w n x b f hi hb hc

theorem single {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool) (w n b f : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) (hc : Derives Γ (singleCase tag advance w b f n)) :
    Derives Γ (valid w n) := by
  let C := singleCaseBody tag advance w b f n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply eliminate_single tag advance w b f n _ hc
  have hZ1 := ZFContext.under hZ C
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hi1 : Derives Δ (earlier w.castSucc n.castSucc) := by simpa only [Formula.raise, earlier_rename] using under hi C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hx := step_child advance w.castSucc n.castSucc (Fin.last m) b.castSucc f.castSucc
    hi1 (.conjL (.conjR hC)) (.conjR (.conjR hC))
  have hout := SyntaxTreeValidity.constructor hZ1 1 tag w.castSucc (fun _ => Fin.last m) n.castSucc
    hw1 (.conjL hC) (.conjI hx (.eqRefl w.castSucc))
  simpa only [Formula.raise, valid_rename] using hout

theorem binary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w n b f : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) (hc : Derives Γ (binaryCase kind w b f n)) :
    Derives Γ (valid w n) := by
  let C := binaryCaseBody kind w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_binary kind w b f n _ hc
  have hZ2 := ZFContext.under_two hZ C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hi2 : Derives Δ (earlier w.castSucc.castSucc n.castSucc.castSucc) := by
    simpa only [Formula.raise, earlier_rename] using OrderedPairElimination.under_two hi C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hx := child w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc b.castSucc.castSucc f.castSucc.castSucc
    hi2 (.conjL (.conjR hC)) (.conjL (.conjR (.conjR (.conjR hC))))
  have hy := child w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) b.castSucc.castSucc f.castSucc.castSucc
    hi2 (.conjL (.conjR (.conjR hC))) (.conjR (.conjR (.conjR (.conjR hC))))
  have hin : Derives Δ (validInputs 2 w.castSucc.castSucc (SyntaxAtomSyntax.two (Fin.last m).castSucc (Fin.last (m+1)))) :=
    .conjI hx (.conjI hy (.eqRefl w.castSucc.castSucc))
  have hout := SyntaxTreeValidity.constructor hZ2 2 (binaryTag kind) _ _ _ hw2 (.conjL hC) hin
  simpa only [Formula.raise, valid_rename] using hout
end PPAC.Migration.Internal.FormulaCodeTreeValidityCases
