import PPAC.Migration.Internal.SyntaxForestInjective

/-! 原节点/有限标签构造器的反向字段恢复，以及scalar索引guard和输出替换。 -/
namespace PPAC.Migration.Internal.SyntaxNodeInjective
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxForestSyntax SyntaxNodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem tag_natural {m} {Γ : Context m} (k : Nat) (w tag : Fin m) (xs : Fin k → Fin m) (n : Fin m)
    (hn : Derives Γ (node k w tag xs n)) : Derives Γ (.mem tag w) := by
  apply eliminate_node k w tag xs n _ hn
  exact .conjL (.hyp (Or.inl rfl))

theorem input_eq {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w a b : Fin m) (xs ys : Fin k → Fin m) (n : Fin m) (i : Fin k)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (node k w a xs n)) (hy : Derives Γ (node k w b ys n)) : Derives Γ (.equal (xs i) (ys i)) := by
  let X := nodeBody k w a xs n
  let Ξ := Context.add X (Context.image Formula.raise Γ)
  apply eliminate_node k w a xs n _ hx
  have hy1 : Derives Ξ (node k w.castSucc b.castSucc (fun i => (ys i).castSucc) n.castSucc) := by simpa only [Formula.raise, node_rename] using under hy X
  let Y := nodeBody k w.castSucc b.castSucc (fun i => (ys i).castSucc) n.castSucc
  let Δ := Context.add Y (Context.image Formula.raise Ξ)
  apply eliminate_node k w.castSucc b.castSucc (fun i => (ys i).castSucc) n.castSucc _ hy1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ X) Y
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw X) Y
  have hX : Derives Ξ X := .hyp (Or.inl rfl)
  have hX2 : Derives Δ ((Formula.mem a.castSucc.castSucc w.castSucc.castSucc).conj
      ((forest k w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) (Fin.last m).castSucc).conj
        (StructuralNodeSyntax.raw w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc))) := by
    simpa only [X, nodeBody, Formula.raise, Formula.rename, forest_rename, StructuralNodeSyntax.raw_rename] using under hX Y
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have hp := SyntaxForests.range hZ2 k _ _ _ hw2 (.conjL (.conjR hX2))
  have hq := SyntaxForests.range hZ2 k _ _ _ hw2 (.conjL (.conjR hY))
  have heq := StructuralNodeCore.injective hZ2 _ _ _ _ _ _ hw2 (.conjL hX2) hp (.conjL hY) hq (.conjR (.conjR hX2)) (.conjR (.conjR hY))
  have hySame := SyntaxForestInjective.output_subst k _ _ _ _ (eq_symm (.conjR heq)) (.conjL (.conjR hY))
  exact SyntaxForestInjective.input_eq hZ2 k _ _ _ _ i hw2 (.conjL (.conjR hX2)) hySame

theorem constructor_input_eq {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k a b : Nat) (w : Fin m) (xs ys : Fin k → Fin m) (n : Fin m) (i : Fin k)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (constructor k a w xs n)) (hy : Derives Γ (constructor k b w ys n)) : Derives Γ (.equal (xs i) (ys i)) := by
  let X := constructorBody k a w xs n
  let Ξ := Context.add X (Context.image Formula.raise Γ)
  apply eliminate_constructor k a w xs n _ hx
  have hy1 : Derives Ξ (constructor k b w.castSucc (fun i => (ys i).castSucc) n.castSucc) := by simpa only [Formula.raise, constructor_rename] using under hy X
  let Y := constructorBody k b w.castSucc (fun i => (ys i).castSucc) n.castSucc
  let Δ := Context.add Y (Context.image Formula.raise Ξ)
  apply eliminate_constructor k b w.castSucc (fun i => (ys i).castSucc) n.castSucc _ hy1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ X) Y
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw X) Y
  have hX : Derives Ξ X := .hyp (Or.inl rfl)
  have hX2 : Derives Δ ((SyntaxNumeralSyntax.numeral a (Fin.last m).castSucc).conj
      (node k w.castSucc.castSucc (Fin.last m).castSucc (fun i => (xs i).castSucc.castSucc) n.castSucc.castSucc)) := by
    simpa only [X, constructorBody, Formula.raise, Formula.rename, SyntaxNumeralSyntax.numeral_rename, node_rename] using under hX Y
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  exact input_eq hZ2 k _ _ _ _ _ _ i hw2 (.conjR hX2) (.conjR hY)

theorem constructor_range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (constructor k tag w xs n)) : Derives Γ (.mem n w) := by
  let N := constructorBody k tag w xs n
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_constructor k tag w xs n _ hn
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  exact SyntaxNodes.range (ZFContext.under hZ N) k _ _ _ _ hw1 (.conjR hN)

theorem scalar_output_subst {m} {Γ : Context m} (w i n r : Fin m) (he : Derives Γ (.equal n r))
    (hn : Derives Γ (scalar w i n)) : Derives Γ (scalar w i r) := by
  have hi : Derives Γ ((scalar w.castSucc i.castSucc (Fin.last m)).instantiate n) := by
    simpa only [Formula.instantiate, scalar_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hn
  have ho := Derives.eqSubst (scalar w.castSucc i.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, scalar_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
theorem raw_tag_eq {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w a b p : Fin m) (xs : Fin k → Fin m) (n : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hp : Derives Γ (.mem p w))
    (hn : Derives Γ (node k w a xs n)) (hr : Derives Γ (StructuralNodeSyntax.raw w b p n)) : Derives Γ (.equal a b) := by
  let N := nodeBody k w a xs n
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_node k w a xs n _ hn
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw N
  have hr1 : Derives Δ (StructuralNodeSyntax.raw w.castSucc b.castSucc p.castSucc n.castSucc) := by simpa only [Formula.raise, StructuralNodeSyntax.raw_rename] using under hr N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hq := SyntaxForests.range hZ1 k _ _ _ hw1 (.conjL (.conjR hN))
  exact .conjL (StructuralNodeCore.injective hZ1 _ _ _ _ _ _ hw1 (.conjL hN) hq (under hb N) (under hp N) (.conjR (.conjR hN)) hr1)
end PPAC.Migration.Internal.SyntaxNodeInjective
