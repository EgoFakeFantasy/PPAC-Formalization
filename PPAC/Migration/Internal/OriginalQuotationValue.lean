import PPAC.Migration.Internal.ObjectQuotationFields

/-! 任一实际quotation值的全候选相等刻画；使用对象等词传输，不选择宿主集合值。 -/
namespace PPAC.Migration.Internal.OriginalQuotationValue
open Source SourceAlgebra SourceLogic OmegaSyntax OriginalTreeQuotationSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.NatPacket (Tree)

theorem tree_output_subst {m} {Γ : Context m} (input : Tree) (w n q : Fin m) (he : Derives Γ (.equal n q))
    (hn : Derives Γ (tree input w n)) : Derives Γ (tree input w q) := by
  have hi : Derives Γ ((tree input w.castSucc (Fin.last m)).instantiate n) := of_eq
    (by simp only [Formula.instantiate, tree_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hn
  have ho := Derives.eqSubst (tree input w.castSucc (Fin.last m)) he hi
  exact of_eq (by simp only [Formula.instantiate, tree_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) ho

theorem at_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (input : Tree) (w n q : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (tree input w n)) :
    Derives Γ ((tree input w q).iff (.equal q n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact OriginalTreeQuotationUnique.tree_unique (ZFContext.add hZ _) input w q n (add hw _) (.hyp (Or.inl rfl)) (add hn _)
  · apply Derives.impI
    exact tree_output_subst input w n q (eq_symm (.hyp (Or.inl rfl))) (add hn _)

end PPAC.Migration.Internal.OriginalQuotationValue
