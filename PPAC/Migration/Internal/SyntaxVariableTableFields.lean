import PPAC.Migration.Internal.SyntaxVariableTableUnique

/-! 恒等/后移完整项码表的准确内部索引端点律。 -/
namespace PPAC.Migration.Internal.SyntaxVariableTableFields
open Source SourceAlgebra SourceLogic OmegaSyntax SyntaxRenameQuerySyntax SyntaxVariableTableSyntax
open SyntaxTermSyntax (limit limit_map)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem identity_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w c d f i q : Fin m)
    (hf : Derives Γ (identity bound w c d f)) (hi : Derives Γ (.mem i (limit bound c d))) :
    Derives Γ ((GraphSyntax.edge f i q).iff (SyntaxVariableSyntax.code bound w i q)) := by
  let B := identityBody bound w c d f
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hf
  have hi1 : Derives Δ (.mem i.castSucc (limit bound c.castSucc d.castSucc)) := of_eq (by simp only [Formula.raise, Formula.rename, limit_map]) (under hi B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have he := SyntaxIdentityUnique.diagonal_edge w.castSucc (limit bound c.castSucc d.castSucc) (Fin.last m) i.castSucc (.conjL (.conjL hB)) (.conjR (.conjL hB)) hi1
  have hh := SyntaxVariableImageFields.at_index (ZFContext.under hZ B) bound w.castSucc (Fin.last m) (limit bound c.castSucc d.castSucc) c.castSucc d.castSucc f.castSucc i.castSucc i.castSucc q.castSucc (.conjR hB) he
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, GraphSyntax.edge_rename, SyntaxVariableSyntax.code_rename]) hh

theorem shifted_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w a c d f i j q : Fin m)
    (hf : Derives Γ (shifted bound w a c d f)) (hi : Derives Γ (.mem i a)) (hj : Derives Γ (successor j i)) :
    Derives Γ ((GraphSyntax.edge f i q).iff (SyntaxVariableSyntax.code bound w j q)) := by
  let B := shiftedBody bound w a c d f
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hf
  have hj1 : Derives Δ (successor j.castSucc i.castSucc) := of_eq (successor_rename j i Fin.castSucc) (under hj B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have he := Derives.impE (.conjR (SyntaxFreeShiftGraph.edge_iff a.castSucc (Fin.last m) i.castSucc j.castSucc (SyntaxFreeShiftGraph.to_graph _ _ _ _ (.conjL hB)))) (.conjI (under hi B) hj1)
  have hh := SyntaxVariableImageFields.at_index (ZFContext.under hZ B) bound w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc f.castSucc i.castSucc j.castSucc q.castSucc (.conjR hB) he
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, GraphSyntax.edge_rename, SyntaxVariableSyntax.code_rename]) hh
end PPAC.Migration.Internal.SyntaxVariableTableFields
