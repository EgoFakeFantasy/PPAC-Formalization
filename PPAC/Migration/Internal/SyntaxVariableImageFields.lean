import PPAC.Migration.Internal.SyntaxVariableImageGraph

/-! 已知真实索引图边时，项码表边精确等价于该索引的原变量码。 -/
namespace PPAC.Migration.Internal.SyntaxVariableImageFields
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxVariableImageSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem mapped_subst_index_graph {m} {Γ : Context m} (bound : Bool) (w r a c d f s : Fin m)
    (he : Derives Γ (.equal r s)) (hf : Derives Γ (mapped bound w r a c d f)) :
    Derives Γ (mapped bound w s a c d f) := by
  let P := mapped bound w.castSucc (Fin.last m) a.castSucc c.castSucc d.castSucc f.castSucc
  have e0 : P.instantiate r = mapped bound w r a c d f := by
    simp only [P, Formula.instantiate, mapped_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  have e1 : P.instantiate s = mapped bound w s a c d f := by
    simp only [P, Formula.instantiate, mapped_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact of_eq e1 (Derives.eqSubst P he (of_eq e0.symm hf))

theorem value_at_index {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w r a c d i j q : Fin m)
    (hi : Derives Γ (input bound w r a c d)) (he : Derives Γ (edge r i j)) :
    Derives Γ ((value bound w r c d i q).iff (SyntaxVariableSyntax.code bound w j q)) := by
  apply Derives.conjI
  · apply Derives.impI
    let V := value bound w r c d i q
    let B := body bound w r c d i q
    let Δ := Context.add B (Context.image Formula.raise (Context.add V Γ))
    apply Derives.exE (p := B) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ V) B
    have hi1 : Derives Δ (input bound w.castSucc r.castSucc a.castSucc c.castSucc d.castSucc) :=
      of_eq (input_rename bound w r a c d Fin.castSucc) (under (add hi V) B)
    have he1 : Derives Δ (edge r.castSucc i.castSucc j.castSucc) :=
      of_eq (edge_rename r i j Fin.castSucc) (under (add he V) B)
    have hB : Derives Δ B := .hyp (Or.inl rfl)
    have eq := GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ1).base.extensionality (.conjL (.conjR (.conjR hi1))) (.conjL hB) he1
    have hc := SyntaxVariableImagePoint.code_subst_index bound w.castSucc (Fin.last m) q.castSucc j.castSucc eq (.conjL (.conjR hB))
    exact of_eq (SyntaxVariableSyntax.code_rename bound w j q Fin.castSucc).symm hc
  · apply Derives.impI
    let C := SyntaxVariableSyntax.code bound w j q
    have hC : Derives (Context.add C Γ) C := .hyp (Or.inl rfl)
    have hj := SyntaxIndexMapSyntax.edge_target w r a (SyntaxTermSyntax.limit bound c d) i j (add (.conjR hi) C) (add he C)
    have ht := SyntaxTermSyntax.intro_term bound w c d q j (.conjI (add (.conjL hi) C) hj) hC
    exact intro_value bound w r c d i q j (add he C) hC ht

theorem at_index {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (bound : Bool) (w r a c d f i j q : Fin m)
    (hf : Derives Γ (mapped bound w r a c d f)) (he : Derives Γ (edge r i j)) :
    Derives Γ ((edge f i q).iff (SyntaxVariableSyntax.code bound w j q)) :=
  SyntaxTypeLocalTransfer.iff_trans (SyntaxVariableImageGraph.edge_iff hZ bound w r a c d f i q hf)
    (value_at_index hZ bound w r a c d i j q (.conjL hf) he)
end PPAC.Migration.Internal.SyntaxVariableImageFields
