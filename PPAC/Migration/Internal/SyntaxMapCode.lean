import PPAC.Migration.Internal.SyntaxMapCodeSyntax

/-! 实际索引图的原列表编码自然性、图/码唯一性和完整域恢复。 -/
namespace PPAC.Migration.Internal.SyntaxMapCode
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxIndexMapSyntax SyntaxMapCodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem omega_sequence {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (indexMap w r a c)) : Derives Γ (SequenceSyntax.sequence r a w) := by
  apply Derives.conjI (.conjL (.conjR hm))
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := edge r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw E
  have hm2 : Derives Δ (indexMap w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc) := by
    simpa only [Formula.raise, indexMap_rename] using OrderedPairElimination.under_two hm E
  have hy := edge_target _ _ _ _ _ _ hm2 (.hyp (Or.inl rfl))
  exact StructuralListTraceOrder.member_member (ZFContext.under_two hZ E) _ _ _ hw2 (.conjR (.conjL hm2)) hy

theorem code_natural {m} {Γ : Context m} (w r a c k : Fin m) (he : Derives Γ (encoded w r a c k)) : Derives Γ (.mem k w) :=
  .conjL (.conjL (.conjL he))

theorem code_valid {m} {Γ : Context m} (w r a c k : Fin m) (he : Derives Γ (encoded w r a c k)) :
    Derives Γ (StructuralListTraceSyntax.valid w k) := StructuralListEncodeReadback.encoding_valid w r a k (.conjL he)

theorem unique_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c k l : Fin m)
    (hw : Derives Γ (omega w)) (hk : Derives Γ (encoded w r a c k)) (hl : Derives Γ (encoded w r a c l)) :
    Derives Γ (.equal k l) := StructuralListCodeGraph.encoded_unique hZ w r a k l hw (.conjL hk) (.conjL hl)

theorem unique_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a c k : Fin m)
    (hr : Derives Γ (encoded w r a c k)) (hs : Derives Γ (encoded w s a c k)) : Derives Γ (.equal r s) := by
  have hfr := Derives.conjR (.conjL hr)
  have hfs := Derives.conjR (.conjL hs)
  exact StructuralListFieldGraphFiber.unique hZ w k a r s (.conjL (.conjR hfr)) (.conjL (.conjR hfs))

theorem source_and_graph_recovery {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s a b c d k : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (encoded w r a c k)) (hs : Derives Γ (encoded w s b d k)) :
    Derives Γ ((Formula.equal b a).conj (.equal s r)) :=
  StructuralListEncodeReadback.decode_after_encode hZ w r a k b s hw (.conjL hr) (.conjR (.conjL (.conjL hs))) (.conjR (.conjL hs))
end PPAC.Migration.Internal.SyntaxMapCode
