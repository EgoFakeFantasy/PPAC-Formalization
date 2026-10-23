import PPAC.Migration.Internal.OriginalQuotationForestFields

/-! 原树quotation与精确构造器字段的对象双条件，隐藏载荷和标签在原核中消去。 -/
namespace PPAC.Migration.Internal.OriginalQuotationNodeFields
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalQuotationFieldSyntax OriginalTreeQuotationSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem tree_of_node {m} {Γ : Context m} (tag : Nat) (children : List Tree) (w n t : Fin m)
    (xs : Fin children.length → Fin m) (hf : Derives Γ (fields children w xs))
    (ht : Derives Γ (SyntaxNumeralSyntax.numeral tag t)) (hn : Derives Γ (SyntaxNodeSyntax.node children.length w t xs n)) :
    Derives Γ (tree (.node tag children) w n) := by
  let C := SyntaxNodeSyntax.nodeBody children.length w t xs n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply SyntaxNodeSyntax.eliminate_node children.length w t xs n _ hn
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hf1 : Derives Δ (fields children w.castSucc (fun i => (xs i).castSucc)) := of_eq (fields_rename children w xs Fin.castSucc) (under hf C)
  have ht1 : Derives Δ (SyntaxNumeralSyntax.numeral tag t.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename tag t Fin.castSucc) (under ht C)
  have hp := OriginalQuotationForestFields.forest_of_fields children w.castSucc (Fin.last m) (fun i => (xs i).castSucc) hf1 (.conjL (.conjR hC))
  have ho := intro_tree tag children w.castSucc n.castSucc (Fin.last m) t.castSucc ht1 hp (.conjR (.conjR hC))
  exact of_eq (tree_rename (.node tag children) w n Fin.castSucc).symm ho

theorem tree_of_constructor {m} {Γ : Context m} (tag : Nat) (children : List Tree) (w n : Fin m)
    (xs : Fin children.length → Fin m) (hf : Derives Γ (fields children w xs))
    (hn : Derives Γ (SyntaxNodeSyntax.constructor children.length tag w xs n)) : Derives Γ (tree (.node tag children) w n) := by
  let C := SyntaxNodeSyntax.constructorBody children.length tag w xs n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply SyntaxNodeSyntax.eliminate_constructor children.length tag w xs n _ hn
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hf1 : Derives Δ (fields children w.castSucc (fun i => (xs i).castSucc)) := of_eq (fields_rename children w xs Fin.castSucc) (under hf C)
  have ho := tree_of_node tag children w.castSucc n.castSucc (Fin.last m) (fun i => (xs i).castSucc) hf1 (.conjL hC) (.conjR hC)
  exact of_eq (tree_rename (.node tag children) w n Fin.castSucc).symm ho

theorem tree_to_constructor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (children : List Tree) (w n : Fin m)
    (xs : Fin children.length → Fin m) (hw : Derives Γ (omega w)) (hf : Derives Γ (fields children w xs))
    (hn : Derives Γ (tree (.node tag children) w n)) : Derives Γ (SyntaxNodeSyntax.constructor children.length tag w xs n) := by
  let C := OriginalTreeQuotationSyntax.nodeBody tag children w n
  let Δ := Context.add C (Context.image Formula.raise (Context.image Formula.raise Γ))
  rw [tree] at hn
  apply SyntaxRenameBinders.eliminate_2 C _ hn
  have hZ2 := SyntaxRenameBinders.zf_under_2 hZ C
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise, omega_rename]) (SyntaxRenameBinders.under_2 hw C)
  have hf2 : Derives Δ (fields children w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc)) := of_eq (by simp only [Formula.raise, fields_rename]) (SyntaxRenameBinders.under_2 hf C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have htW := SyntaxNumerals.range hZ2 tag w.castSucc.castSucc (Fin.last (m+1)) hw2 (.conjL hC)
  have hp := OriginalQuotationForestFields.forest_to_fields hZ2 children w.castSucc.castSucc (Fin.last m).castSucc (fun i => (xs i).castSucc.castSucc) hw2 hf2 (.conjL (.conjR hC))
  have hNode := SyntaxNodeSyntax.intro_node children.length w.castSucc.castSucc (Fin.last (m+1)) (fun i => (xs i).castSucc.castSucc) n.castSucc.castSucc (Fin.last m).castSucc htW hp (.conjR (.conjR hC))
  have ho := SyntaxNodeSyntax.intro_constructor children.length tag w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) n.castSucc.castSucc (Fin.last (m+1)) (.conjL hC) hNode
  exact of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.constructor_rename]) ho

theorem tree_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (tag : Nat) (children : List Tree) (w n : Fin m)
    (xs : Fin children.length → Fin m) (hw : Derives Γ (omega w)) (hf : Derives Γ (fields children w xs)) :
    Derives Γ ((tree (.node tag children) w n).iff (SyntaxNodeSyntax.constructor children.length tag w xs n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact tree_to_constructor (ZFContext.add hZ _) tag children w n xs (add hw _) (add hf _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact tree_of_constructor tag children w n xs (add hf _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.OriginalQuotationNodeFields
