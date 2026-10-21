import PPAC.Migration.Internal.SyntaxForestFields

/-! 任意原Node/Constructor与同根实际Shape的完整字段图对应；payload相等由原配数单射性推出。 -/
namespace PPAC.Migration.Internal.SyntaxNodeFields
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxNodeSyntax SyntaxForestSyntax GraphSyntax SyntaxNumeralSyntax
open StructuralTreeOperatorSyntax (shape shape_rename)
open SyntaxForestFields (graphLaw graphLaw_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem forest_of_shape {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w a : Fin m) (xs : Fin k → Fin m)
    (n t p l g : Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (node k w a xs n))
    (hs : Derives Γ (shape w n t p l g)) : Derives Γ (forest k w xs p) := by
  let N := nodeBody k w a xs n
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_node k w a xs n _ hn
  have hZ1 := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw N
  have hs1 : Derives Δ (shape w.castSucc n.castSucc t.castSucc p.castSucc l.castSucc g.castSucc) := by
    simpa only [Formula.raise, shape_rename] using under hs N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hq := SyntaxForests.range hZ1 k w.castSucc (fun i => (xs i).castSucc) (Fin.last m) hw1 (.conjL (.conjR hN))
  have hp := StructuralListLengthBasic.code_member _ _ _ (.conjL (.conjR hs1))
  have he := StructuralNodeCore.injective hZ1 _ _ _ _ _ _ hw1 (.conjL hN) hq (.conjL (.conjL hs1)) hp
    (.conjR (.conjR hN)) (.conjR (.conjL hs1))
  have hout := SyntaxForestInjective.output_subst k w.castSucc (fun i => (xs i).castSucc) (Fin.last m) p.castSucc
    (.conjR he) (.conjL (.conjR hN))
  simpa only [Formula.raise, forest_rename] using hout

theorem node {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w a : Fin m) (xs : Fin k → Fin m)
    (n t p l g : Fin m) (hw : Derives Γ (omega w)) (hn : Derives Γ (SyntaxNodeSyntax.node k w a xs n))
    (hs : Derives Γ (shape w n t p l g)) : Derives Γ (graphLaw k xs g) :=
  SyntaxForestFields.all_edges hZ k w xs p l g hw (forest_of_shape hZ k w a xs n t p l g hw hn hs)
    (.conjL (.conjR hs)) (.conjR (.conjR hs))

theorem edge_at_node {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w a : Fin m) (xs : Fin k → Fin m)
    (n t p l g : Fin m) (j : Fin k) (i y : Fin m) (hw : Derives Γ (omega w))
    (hn : Derives Γ (SyntaxNodeSyntax.node k w a xs n)) (hs : Derives Γ (shape w n t p l g))
    (hi : Derives Γ (numeral j.val i)) : Derives Γ ((edge g i y).iff (.equal y (xs j))) :=
  SyntaxForestFields.edge_at hZ k w xs p l g j i y hw (forest_of_shape hZ k w a xs n t p l g hw hn hs)
    (.conjL (.conjR hs)) (.conjR (.conjR hs)) hi

theorem constructor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m)
    (n t p l g : Fin m) (hw : Derives Γ (omega w)) (hc : Derives Γ (SyntaxNodeSyntax.constructor k tag w xs n))
    (hs : Derives Γ (shape w n t p l g)) : Derives Γ (graphLaw k xs g) := by
  let C := constructorBody k tag w xs n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply eliminate_constructor k tag w xs n _ hc
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hs1 : Derives Δ (shape w.castSucc n.castSucc t.castSucc p.castSucc l.castSucc g.castSucc) := by
    simpa only [Formula.raise, shape_rename] using under hs C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hout := node (ZFContext.under hZ C) k w.castSucc (Fin.last m) (fun i => (xs i).castSucc)
    n.castSucc t.castSucc p.castSucc l.castSucc g.castSucc hw1 (.conjR hC) hs1
  simpa only [Formula.raise, graphLaw_rename] using hout

theorem edge_at_constructor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m)
    (n t p l g : Fin m) (j : Fin k) (i y : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor k tag w xs n)) (hs : Derives Γ (shape w n t p l g))
    (hi : Derives Γ (numeral j.val i)) : Derives Γ ((edge g i y).iff (.equal y (xs j))) := by
  let C := constructorBody k tag w xs n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply eliminate_constructor k tag w xs n _ hc
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw C
  have hs1 : Derives Δ (shape w.castSucc n.castSucc t.castSucc p.castSucc l.castSucc g.castSucc) := by
    simpa only [Formula.raise, shape_rename] using under hs C
  have hi1 : Derives Δ (numeral j.val i.castSucc) := by simpa only [Formula.raise, numeral_rename] using under hi C
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hout := edge_at_node (ZFContext.under hZ C) k w.castSucc (Fin.last m) (fun a => (xs a).castSucc)
    n.castSucc t.castSucc p.castSucc l.castSucc g.castSucc j i.castSucc y.castSucc hw1 (.conjR hC) hs1 hi1
  simpa only [Formula.raise, Formula.iff, Formula.rename, edge_rename] using hout
end PPAC.Migration.Internal.SyntaxNodeFields
