import PPAC.Migration.Internal.IndexTermImageEnvironment

/-! 变量项表的每个内部字段按原索引图真边精确读出；索引数不冒充项码。 -/
namespace PPAC.Migration.Internal.IndexTermImageCodeFields
open Source SourceAlgebra SourceLogic IndexTermImageCodeSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_edge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (isBound : Bool) (w I T a c d r i j q : Fin m)
    (hc : Derives Γ (converted isBound w I T a c d))
    (hr : Derives Γ (SyntaxMapCodeSyntax.encoded w r a (SyntaxTermSyntax.limit isBound c d) I))
    (he : Derives Γ (GraphSyntax.edge r i j)) :
    Derives Γ (((Formula.mem i a).conj (StructuralListFieldSyntax.field w T i q)).iff (SyntaxVariableSyntax.code isBound w j q)) := by
  have hf := IndexTermImageCodeTyping.at_graph hZ isBound w I T a c d r hc hr
  let F := (SyntaxVariableImageSyntax.mapped isBound w.castSucc r.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m)).conj
    (SyntaxMixedImageCodeSyntax.encoded w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc T.castSucc)
  let Δ := Context.add F (Context.image Formula.raise Γ)
  apply Derives.exE hf
  have he1 : Derives Δ (GraphSyntax.edge r.castSucc i.castSucc j.castSucc) := of_eq (GraphSyntax.edge_rename r i j Fin.castSucc) (under he F)
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have hOld := SyntaxVariableImageFields.at_index (ZFContext.under hZ F) isBound w.castSucc r.castSucc a.castSucc c.castSucc d.castSucc (Fin.last m) i.castSucc j.castSucc q.castSucc (.conjL hF) he1
  have hNew := SyntaxMixedImageCodeFields.edges w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc T.castSucc i.castSucc q.castSucc (.conjR hF)
  have ho := SyntaxTypeLocalTransfer.iff_trans (.conjI (.conjR hNew) (.conjL hNew)) hOld
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, StructuralListFieldSyntax.field_rename, SyntaxVariableSyntax.code_rename]) ho

end PPAC.Migration.Internal.IndexTermImageCodeFields
