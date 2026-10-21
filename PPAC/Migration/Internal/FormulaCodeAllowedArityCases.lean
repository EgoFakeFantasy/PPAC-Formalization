import PPAC.Migration.Internal.FormulaCodeAllowedAritySyntax

/-! 全部原局部分支的真实Shape必须满足精确内部标签/字段数分类。 -/
namespace PPAC.Migration.Internal.FormulaCodeAllowedArityCases
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxTermSyntax SyntaxAtomSyntax
open SyntaxLogicalSyntax (binaryTag)
open FormulaCodeRecursiveSyntax FormulaCodeAllowedAritySyntax
open StructuralTreeOperatorSyntax (shape shape_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem constructor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (ht : tag < 11)
    (hk : k = expectedArity tag) (w : Fin m) (xs : Fin k → Fin m) (n t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor k tag w xs n))
    (hs : Derives Γ (shape w n t p l g)) : Derives Γ (allowed 11 t l) := by
  have htag := FormulaCodeFieldArity.constructor_tag hZ k tag w xs n t p l g hw hc hs
  have hlen := FormulaCodeFieldArity.constructor_length hZ k tag w xs n t p l g hw hc hs
  apply intro_allowed 11 tag ht t l htag
  simpa only [hk] using hlen

theorem single {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (advance : Bool)
    (ht : tag < 11) (hk : 1 = expectedArity tag) (w b f n t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (singleCase tag advance w b f n))
    (hs : Derives Γ (shape w n t p l g)) : Derives Γ (allowed 11 t l) := by
  let C := singleCaseBody tag advance w b f n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply eliminate_single tag advance w b f n _ hc
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hs1 : Derives Δ (shape w.castSucc n.castSucc t.castSucc p.castSucc l.castSucc g.castSucc) := by
    simpa only [Formula.raise, shape_rename] using under hs C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hout := constructor (ZFContext.under hZ C) 1 tag ht hk w.castSucc (fun _ => Fin.last m)
    n.castSucc t.castSucc p.castSucc l.castSucc g.castSucc hw1 (.conjL hC) hs1
  simpa only [Formula.raise, allowed_rename] using hout

theorem binary {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 4) (w b f n t p l g : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (binaryCase kind w b f n))
    (hs : Derives Γ (shape w n t p l g)) : Derives Γ (allowed 11 t l) := by
  let C := binaryCaseBody kind w b f n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_binary kind w b f n _ hc
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by
    simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw C
  have hs2 : Derives Δ (shape w.castSucc.castSucc n.castSucc.castSucc t.castSucc.castSucc p.castSucc.castSucc l.castSucc.castSucc g.castSucc.castSucc) := by
    simpa only [Formula.raise, shape_rename] using OrderedPairElimination.under_two hs C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hbound : binaryTag kind < 11 := by dsimp only [binaryTag]; omega
  have hcount : 2 = expectedArity (binaryTag kind) := by
    have hk : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 := by omega
    rcases hk with rfl | rfl | rfl | rfl <;> decide
  have hout := constructor (ZFContext.under_two hZ C) 2 (binaryTag kind) hbound hcount _
    (two (Fin.last m).castSucc (Fin.last (m+1))) _ _ _ _ _ hw2 (.conjL hC) hs2
  simpa only [Formula.raise, allowed_rename] using hout
end PPAC.Migration.Internal.FormulaCodeAllowedArityCases
