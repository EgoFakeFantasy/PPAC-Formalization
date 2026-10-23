import PPAC.Migration.Internal.OriginalQuotationNodeFields

/-! 标准有限索引quotation与原内部scalar/bvar/fvar关系的精确对应；实际索引和子码仍为对象见证。 -/
namespace PPAC.Migration.Internal.OriginalQuotationVariableFields
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalQuotationFieldSyntax OriginalTreeQuotationSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree leaf)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem tree_of_scalar {m} {Γ : Context m} (k : Nat) (w i n : Fin m)
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i)) (hn : Derives Γ (SyntaxNodeSyntax.scalar w i n)) :
    Derives Γ (tree (leaf k) w n) := by
  have hc := SyntaxNodeSyntax.intro_constructor 0 k w Fin.elim0 n i hi hn
  exact OriginalQuotationNodeFields.tree_of_constructor k List.nil w n Fin.elim0 (.eqRefl w) hc

theorem scalar_of_tree {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w i n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i)) (hn : Derives Γ (tree (leaf k) w n)) :
    Derives Γ (SyntaxNodeSyntax.scalar w i n) := by
  have hc := OriginalQuotationNodeFields.tree_to_constructor hZ k List.nil w n Fin.elim0 hw (.eqRefl w) hn
  let C := SyntaxNodeSyntax.constructorBody 0 k w Fin.elim0 n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply SyntaxNodeSyntax.eliminate_constructor 0 k w Fin.elim0 n _ hc
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hi1 : Derives Δ (SyntaxNumeralSyntax.numeral k i.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename k i Fin.castSucc) (under hi C)
  have he := SyntaxNumerals.unique (ZFContext.under hZ C) k (Fin.last m) i.castSucc (.conjL hC) hi1
  have hN : Derives Δ (SyntaxNodeSyntax.node 0 w.castSucc (Fin.last m) Fin.elim0 n.castSucc) :=
    of_eq (by simp only [SyntaxAtomSyntax.zero_map]) (.conjR hC)
  have ho := SyntaxNodeSyntax.tag_subst 0 w.castSucc (Fin.last m) i.castSucc Fin.elim0 n.castSucc he hN
  exact of_eq (by simp only [Formula.raise, SyntaxNodeSyntax.scalar, SyntaxNodeSyntax.node_rename, SyntaxAtomSyntax.zero_map]) ho

theorem scalar_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k : Nat) (w i n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i)) :
    Derives Γ ((tree (leaf k) w n).iff (SyntaxNodeSyntax.scalar w i n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact scalar_of_tree (ZFContext.add hZ _) k w i n (add hw _) (add hi _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact tree_of_scalar k w i n (add hi _) (.hyp (Or.inl rfl))

theorem variable_of_tree {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (k : Nat) (w i n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i))
    (hn : Derives Γ (tree (.node (SyntaxVariableSyntax.tag bound) [leaf k]) w n)) :
    Derives Γ (SyntaxVariableSyntax.code bound w i n) := by
  have hiW := SyntaxNumerals.range hZ k w i hw hi
  have he := SyntaxNodes.exists_node hZ 0 w i Fin.elim0 hw hiW (.eqRefl w)
  let C := (Formula.mem (Fin.last m) w.castSucc).conj (SyntaxNodeSyntax.scalar w.castSucc i.castSucc (Fin.last m))
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply Derives.exE (p := C) he
  have hZ1 := ZFContext.under hZ C
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw C)
  have hi1 : Derives Δ (SyntaxNumeralSyntax.numeral k i.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename k i Fin.castSucc) (under hi C)
  have hn1 : Derives Δ (tree (.node (SyntaxVariableSyntax.tag bound) [leaf k]) w.castSucc n.castSucc) := of_eq (tree_rename _ w n Fin.castSucc) (under hn C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hLeaf := tree_of_scalar k w.castSucc i.castSucc (Fin.last m) hi1 (.conjR hC)
  have hf : Derives Δ (fields [leaf k] w.castSucc (fun _ => Fin.last m)) := .conjI hLeaf (.eqRefl _)
  have hNode := OriginalQuotationNodeFields.tree_to_constructor hZ1 (SyntaxVariableSyntax.tag bound) [leaf k] w.castSucc n.castSucc (fun _ => Fin.last m) hw1 hf hn1
  have ho := SyntaxVariableSyntax.intro_code bound w.castSucc i.castSucc n.castSucc (Fin.last m) (.conjR hC) hNode
  exact of_eq (by simp only [Formula.raise, SyntaxVariableSyntax.code_rename]) ho

theorem tree_of_variable {m} {Γ : Context m} (bound : Bool) (k : Nat) (w i n : Fin m)
    (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i)) (hn : Derives Γ (SyntaxVariableSyntax.code bound w i n)) :
    Derives Γ (tree (.node (SyntaxVariableSyntax.tag bound) [leaf k]) w n) := by
  let C := SyntaxVariableSyntax.codeBody bound w i n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply SyntaxVariableSyntax.eliminate_code bound w i n _ hn
  have hi1 : Derives Δ (SyntaxNumeralSyntax.numeral k i.castSucc) := of_eq (SyntaxNumeralSyntax.numeral_rename k i Fin.castSucc) (under hi C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hLeaf := tree_of_scalar k w.castSucc i.castSucc (Fin.last m) hi1 (.conjL hC)
  have hf : Derives Δ (fields [leaf k] w.castSucc (fun _ => Fin.last m)) := .conjI hLeaf (.eqRefl _)
  have ho := OriginalQuotationNodeFields.tree_of_constructor (SyntaxVariableSyntax.tag bound) [leaf k] w.castSucc n.castSucc (fun _ => Fin.last m) hf (.conjR hC)
  exact of_eq (tree_rename _ w n Fin.castSucc).symm ho

theorem variable_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (k : Nat) (w i n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (SyntaxNumeralSyntax.numeral k i)) :
    Derives Γ ((tree (.node (SyntaxVariableSyntax.tag bound) [leaf k]) w n).iff (SyntaxVariableSyntax.code bound w i n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact variable_of_tree (ZFContext.add hZ _) bound k w i n (add hw _) (add hi _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact tree_of_variable bound k w i n (add hi _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.OriginalQuotationVariableFields
