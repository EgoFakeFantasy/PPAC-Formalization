import PPAC.Migration.Internal.SyntaxFreeSubstExistence

/-! 原Replacement构造双向实际完整图；准确的项值域及索引范围都保留。 -/
namespace PPAC.Migration.Internal.SyntaxFreeSubstGraph
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax ReplacementPredicates SyntaxRenameQuerySyntax SyntaxFreeSubstSyntax
open SyntaxIndexMapSyntax (indexMap indexMap_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem decoded_index {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a c r : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (termGraph w f a c)) (hg : Derives Γ (decodedGraph w f a r)) :
    Derives Γ (indexMap w r a c) :=
  .conjI (.conjL hf) (RelationGraph.sequence decodeMatrix (Source.SetLanguage.args2 w f) a c r hg
    (SyntaxFreeSubstExistence.decode_outputs hZ _ a c hw hf))

theorem encoded_terms {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c f : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (indexMap w r a c)) (hg : Derives Γ (encodedGraph w r a f)) :
    Derives Γ (termGraph w f a c) := by
  apply Derives.conjI (.conjL hr)
  apply Derives.conjI (RelationGraph.sequence encodeMatrix (Source.SetLanguage.args2 w r) a w f hg
    (SyntaxFreeSubstExistence.encode_outputs hZ _ a hw))
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let E := edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Δ := Context.add E (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hr2 : Derives Δ (indexMap w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, indexMap_rename]) (SyntaxRenameBinders.under_2 hr E)
  have hg2 : Derives Δ (encodedGraph w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise, encodedGraph_rename]) (SyntaxRenameBinders.under_2 hg E)
  have he := RelationGraphSyntax.law_at encodeMatrix (Source.SetLanguage.args2 w.castSucc.castSucc r.castSucc.castSucc)
    a.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjR hg2)
  have hE : Derives Δ E := .hyp (Or.inl rfl)
  have hv : Derives Δ (encodedValue w.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))) :=
    of_eq (by simp only [encodeMatrix_rel, PairSyntax.args2_first, PairSyntax.args2_second]) (.conjR (.impE (.conjL he) hE))
  exact SyntaxFreeSubstPoint.encoded_free _ _ _ _ _ _ hr2 hv

theorem decode_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a c : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (termGraph w f a c)) :
    Derives Γ (.ex (conversion w.castSucc f.castSucc a.castSucc c.castSucc (Fin.last m))) := by
  let ρ := Source.SetLanguage.args2 w f
  have he := RelationGraphFunction.exists_graph hZ decodeMatrix ρ a
    (SyntaxFreeSubstExistence.decode_total hZ ρ a c hw hf)
  let G := decodedGraph w.castSucc f.castSucc a.castSucc (Fin.last m)
  let Δ := Context.add G (Context.image Formula.raise Γ)
  change Derives Γ (.ex G) at he
  apply Derives.exE (p := G) he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw G)
  have hf1 : Derives Δ (termGraph w.castSucc f.castSucc a.castSucc c.castSucc) := of_eq (termGraph_rename w f a c Fin.castSucc) (under hf G)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hm := decoded_index (ZFContext.under hZ G) _ _ _ _ _ hw1 hf1 hG
  have ho : Derives Δ (.ex (conversion w.castSucc.castSucc f.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc (Fin.last (m+1)))) := by
    apply Derives.exI (Fin.last m)
    have hv : Derives Δ (conversion w.castSucc f.castSucc a.castSucc c.castSucc (Fin.last m)) := .conjI hf1 (.conjI hm hG)
    exact of_eq (by simp only [Formula.instantiate, conversion_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hv
  exact of_eq (by simp only [Formula.raise, Formula.rename, conversion_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) ho

theorem encode_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (indexMap w r a c)) :
    Derives Γ (.ex ((encodedGraph w.castSucc r.castSucc a.castSucc (Fin.last m)).conj
      (termGraph w.castSucc (Fin.last m) a.castSucc c.castSucc))) := by
  let ρ := Source.SetLanguage.args2 w r
  have he := RelationGraphFunction.exists_graph hZ encodeMatrix ρ a
    (SyntaxFreeSubstExistence.encode_total hZ ρ a c hw hr)
  let G := encodedGraph w.castSucc r.castSucc a.castSucc (Fin.last m)
  let Δ := Context.add G (Context.image Formula.raise Γ)
  change Derives Γ (.ex G) at he
  apply Derives.exE (p := G) he
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw G)
  have hr1 : Derives Δ (indexMap w.castSucc r.castSucc a.castSucc c.castSucc) := of_eq (indexMap_rename w r a c Fin.castSucc) (under hr G)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hf := encoded_terms (ZFContext.under hZ G) _ _ _ _ _ hw1 hr1 hG
  have ho : Derives Δ (.ex ((encodedGraph w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc (Fin.last (m+1))).conj
      (termGraph w.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc c.castSucc.castSucc))) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [G, Formula.instantiate, Formula.rename, encodedGraph_rename, termGraph_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hG hf)
  exact of_eq (by simp only [Formula.raise, Formula.rename, encodedGraph_rename, termGraph_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]) ho

theorem decode_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a r s : Fin m)
    (hr : Derives Γ (decodedGraph w f a r)) (hs : Derives Γ (decodedGraph w f a s)) : Derives Γ (.equal r s) :=
  RelationGraph.unique_graph hZ decodeMatrix (Source.SetLanguage.args2 w f) a r s hr hs

theorem encode_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a f g : Fin m)
    (hf : Derives Γ (encodedGraph w r a f)) (hg : Derives Γ (encodedGraph w r a g)) : Derives Γ (.equal f g) :=
  RelationGraph.unique_graph hZ encodeMatrix (Source.SetLanguage.args2 w r) a f g hf hg

end PPAC.Migration.Internal.SyntaxFreeSubstGraph
