import PPAC.Migration.Internal.SyntaxForestArity
import PPAC.Migration.Internal.SyntaxVariableDecode

/-! 原节点不同字段数互斥，变量单字段封装排除scalar叶和多余字段。 -/
namespace PPAC.Migration.Internal.SyntaxNodeArity
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxForestSyntax SyntaxNodeSyntax SyntaxVariableSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem disjoint {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k l : Nat) (hkl : k ≠ l) (w a b : Fin m)
    (xs : Fin k → Fin m) (ys : Fin l → Fin m) (n : Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (node k w a xs n)) (hy : Derives Γ (node l w b ys n)) : Derives Γ .bot := by
  let X := nodeBody k w a xs n
  let Ξ := Context.add X (Context.image Formula.raise Γ)
  apply eliminate_node k w a xs n _ hx
  have hy1 : Derives Ξ (node l w.castSucc b.castSucc (fun i => (ys i).castSucc) n.castSucc) := by simpa only [Formula.raise, node_rename] using under hy X
  let Y := nodeBody l w.castSucc b.castSucc (fun i => (ys i).castSucc) n.castSucc
  let Δ := Context.add Y (Context.image Formula.raise Ξ)
  apply eliminate_node l w.castSucc b.castSucc (fun i => (ys i).castSucc) n.castSucc _ hy1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ X) Y
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw X) Y
  have hX : Derives Ξ X := .hyp (Or.inl rfl)
  have hX2 : Derives Δ ((Formula.mem a.castSucc.castSucc w.castSucc.castSucc).conj
      ((forest k w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) (Fin.last m).castSucc).conj
        (StructuralNodeSyntax.raw w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc))) := by
    simpa only [X, nodeBody, Formula.raise, Formula.rename, forest_rename, StructuralNodeSyntax.raw_rename] using under hX Y
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have hp := SyntaxForests.range hZ2 k _ _ _ hw2 (.conjL (.conjR hX2))
  have hq := SyntaxForests.range hZ2 l _ _ _ hw2 (.conjL (.conjR hY))
  have heq := StructuralNodeCore.injective hZ2 _ _ _ _ _ _ hw2 (.conjL hX2) hp (.conjL hY) hq (.conjR (.conjR hX2)) (.conjR (.conjR hY))
  have hySame := SyntaxForestInjective.output_subst l _ _ _ _ (eq_symm (.conjR heq)) (.conjL (.conjR hY))
  exact SyntaxForestArity.disjoint hZ2 k l hkl _ _ _ _ hw2 (.conjL (.conjR hX2)) hySame

theorem variable_wrong_arity {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (k : Nat) (hk : k ≠ 1)
    (w a i n : Fin m) (xs : Fin k → Fin m) (hw : Derives Γ (omega w))
    (hx : Derives Γ (node k w a xs n)) (hv : Derives Γ (code bound w i n)) : Derives Γ .bot := by
  let V := codeBody bound w i n
  let Ξ := Context.add V (Context.image Formula.raise Γ)
  apply eliminate_code bound w i n _ hv
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  let C := constructorBody 1 (tag bound) w.castSucc (fun _ => Fin.last m) n.castSucc
  let Δ := Context.add C (Context.image Formula.raise Ξ)
  apply eliminate_constructor 1 (tag bound) w.castSucc (fun _ => Fin.last m) n.castSucc _ (Derives.conjR hV)
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ V) C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw V) C
  have hx2 : Derives Δ (node k w.castSucc.castSucc a.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) n.castSucc.castSucc) := by
    simpa only [Formula.raise, node_rename] using under (under hx V) C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact disjoint hZ2 k 1 hk _ _ _ _ _ _ hw2 hx2 (.conjR hC)
end PPAC.Migration.Internal.SyntaxNodeArity
