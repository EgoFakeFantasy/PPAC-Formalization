import PPAC.Migration.Internal.FormulaCodeBranchSyntax

/-! 已知原逻辑构造码的精确分支类型双条件；每个子式使用无额外载体的FormulaCode。 -/
namespace PPAC.Migration.Internal.FormulaCodeBranchTyping
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxTermSyntax SyntaxAtomSyntax
open SyntaxLogicalSyntax (singleCode singleCode_rename binaryCode binaryCode_rename binaryTag quantifierTag)
open FormulaCodeSyntax FormulaCodeRecursiveSyntax FormulaCodeBranchSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem single_types {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool) (w b f x n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (singleCode tag w x n)) (hs : Derives Γ (singleCase tag advance w b f n)) :
    Derives Γ (singleTypes advance w b f x) := by
  let C := singleCaseBody tag advance w b f n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply eliminate_single tag advance w b f n _ hs
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hc1 : Derives Δ (singleCode tag w.castSucc x.castSucc n.castSucc) := by
    simpa only [Formula.raise, singleCode_rename] using under hc C
  have hctx : Derives Δ (contexts w.castSucc b.castSucc f.castSucc) := by
    simpa only [Formula.raise, contexts_rename] using under (Derives.conjL hs) C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have he := SyntaxNodeInjective.constructor_input_eq (ZFContext.under hZ C) 1 tag tag _ _ _ _ 0 hw1 (.conjL hC) hc1
  have hcheck := check_subst_child advance _ _ _ _ _ he (.conjR (.conjR hC))
  have hout : Derives Δ (singleTypes advance w.castSucc b.castSucc f.castSucc x.castSucc) := .conjI hctx hcheck
  simpa only [Formula.raise, singleTypes_rename] using hout

theorem single_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool) (w b f x n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (singleCode tag w x n)) :
    Derives Γ ((singleCase tag advance w b f n).iff (singleTypes advance w b f x)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact single_types (ZFContext.add hZ _) tag advance w b f x n (add hw _) (add hc _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    have ht : Derives (Context.add (singleTypes advance w b f x) Γ) (singleTypes advance w b f x) := .hyp (Or.inl rfl)
    have hb := SyntaxConstructors.child_member (ZFContext.add hZ (singleTypes advance w b f x)) 1 tag w (fun _ => x) n 0 (add hw _) (add hc _)
    exact intro_single tag advance w b f x n (.conjL ht) (.conjI (add hc _) (.conjI hb (.conjR ht)))

theorem binary_types {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w b f x y n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (binaryCode kind w x y n)) (hs : Derives Γ (binaryCase kind w b f n)) :
    Derives Γ (binaryTypes w b f x y) := by
  let C := binaryCaseBody kind w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_binary kind w b f n _ hs
  have hw1 : Derives Δ (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hc1 : Derives Δ (binaryCode kind w.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc n.castSucc.castSucc) := by
    simpa only [Formula.raise, binaryCode_rename] using OrderedPairElimination.under_two hc C
  have hctx : Derives Δ (contexts w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc) := by
    simpa only [Formula.raise, contexts_rename] using OrderedPairElimination.under_two (Derives.conjL hs) C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hx := SyntaxNodeInjective.constructor_input_eq (ZFContext.under_two hZ C) 2 (binaryTag kind) (binaryTag kind) _ _ _ _ 0 hw1 (.conjL hC) hc1
  have hy := SyntaxNodeInjective.constructor_input_eq (ZFContext.under_two hZ C) 2 (binaryTag kind) (binaryTag kind) _ _ _ _ 1 hw1 (.conjL hC) hc1
  have hxRead := FormulaCodeTransport.code_root _ _ _ _ _ hx (.conjL (.conjR (.conjR (.conjR hC))))
  have hyRead := FormulaCodeTransport.code_root _ _ _ _ _ hy (.conjR (.conjR (.conjR (.conjR hC))))
  have hout : Derives Δ (binaryTypes w.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc) := .conjI hctx (.conjI hxRead hyRead)
  simpa only [Formula.raise, binaryTypes_rename] using hout

theorem binary_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w b f x y n : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (binaryCode kind w x y n)) :
    Derives Γ ((binaryCase kind w b f n).iff (binaryTypes w b f x y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact binary_types (ZFContext.add hZ _) kind w b f x y n (add hw _) (add hc _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    have ht : Derives (Context.add (binaryTypes w b f x y) Γ) (binaryTypes w b f x y) := .hyp (Or.inl rfl)
    have hx := SyntaxConstructors.child_member (ZFContext.add hZ (binaryTypes w b f x y)) 2 (binaryTag kind) w (two x y) n 0 (add hw _) (add hc _)
    have hy := SyntaxConstructors.child_member (ZFContext.add hZ (binaryTypes w b f x y)) 2 (binaryTag kind) w (two x y) n 1 (add hw _) (add hc _)
    exact intro_binary kind w b f x y n (.conjL ht) (.conjI (add hc _) (.conjI hx (.conjI hy (.conjR ht))))

theorem quantified_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (universal : Bool) (w b f x n k : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (singleCode (quantifierTag universal) w x n)) (hk : Derives Γ (successor k b)) :
    Derives Γ ((singleCase (quantifierTag universal) true w b f n).iff ((contexts w b f).conj (formulaCode w x k f))) := by
  have hh := single_iff hZ (quantifierTag universal) true w b f x n hw hc
  have ha := FormulaCodeBranchSyntax.at_successor hZ w x b f k hk
  apply Derives.conjI
  · apply Derives.impI
    have ht := Derives.impE (add (.conjL hh) (singleCase (quantifierTag universal) true w b f n)) (.hyp (Or.inl rfl))
    exact .conjI (.conjL ht) (.impE (add (.conjL ha) _) (.conjR ht))
  · apply Derives.impI
    have ht : Derives (Context.add ((contexts w b f).conj (formulaCode w x k f)) Γ)
        ((contexts w b f).conj (formulaCode w x k f)) := .hyp (Or.inl rfl)
    exact .impE (add (.conjR hh) _) (.conjI (.conjL ht) (.impE (add (.conjR ha) _) (.conjR ht)))
end PPAC.Migration.Internal.FormulaCodeBranchTyping
