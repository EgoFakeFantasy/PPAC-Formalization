import PPAC.Migration.Internal.SyntaxFreeSubstGraph

/-! 任意实际fvar端点上的精确边对应；不同图见证不经宿主选择。 -/
namespace PPAC.Migration.Internal.SyntaxFreeSubstBridge
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxFreeSubstSyntax
open SyntaxVariableSyntax (code code_rename)
open SyntaxTermSyntax (branch branch_rename)
open SyntaxIndexMapSyntax (indexMap indexMap_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem encoded_law {m} {Γ : Context m} (w r a f i t : Fin m)
    (hg : Derives Γ (encodedGraph w r a f)) :
    Derives Γ ((edge f i t).iff ((Formula.mem i a).conj (encodedValue w r i t))) :=
  of_eq (by simp only [encodeMatrix_rel, PairSyntax.args2_first, PairSyntax.args2_second])
    (RelationGraphSyntax.law_at encodeMatrix (Source.SetLanguage.args2 w r) a f i t (.conjR hg))

theorem decoded_law {m} {Γ : Context m} (w f a r i j : Fin m)
    (hg : Derives Γ (decodedGraph w f a r)) :
    Derives Γ ((edge r i j).iff ((Formula.mem i a).conj (decodedValue w f i j))) :=
  of_eq (by simp only [decodeMatrix_rel, PairSyntax.args2_first, PairSyntax.args2_second])
    (RelationGraphSyntax.law_at decodeMatrix (Source.SetLanguage.args2 w f) a r i j (.conjR hg))

theorem encoded_at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c f i j t : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (indexMap w r a c))
    (hg : Derives Γ (encodedGraph w r a f)) (hc : Derives Γ (code false w j t)) :
    Derives Γ ((edge f i t).iff (edge r i j)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := edge f i t
    let Ξ := Context.add E Γ
    have hE : Derives Ξ E := .hyp (Or.inl rfl)
    have he := Derives.conjR (.impE (.conjL (encoded_law w r a f i t (add hg E))) hE)
    let J := (edge r.castSucc i.castSucc (Fin.last m)).conj (code false w.castSucc (Fin.last m) t.castSucc)
    let Δ := Context.add J (Context.image Formula.raise Ξ)
    apply Derives.exE (p := J) he
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) J)
    have hc1 : Derives Δ (code false w.castSucc j.castSucc t.castSucc) := of_eq (code_rename false w j t Fin.castSucc) (under (add hc E) J)
    have hJ : Derives Δ J := .hyp (Or.inl rfl)
    have heq := SyntaxVariableDecode.index_eq (ZFContext.under (ZFContext.add hZ E) J) false _ _ _ _ hw1 (.conjR hJ) hc1
    exact of_eq (edge_rename r i j Fin.castSucc).symm (GraphPointwiseSyntax.edge_subst_output _ _ _ _ heq (.conjL hJ))
  · apply Derives.impI
    let E := edge r i j
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hi := SyntaxIndexMapSyntax.edge_source (ZFContext.add hZ E) w r a c i j (add hr E) hE
    exact .impE (.conjR (encoded_law w r a f i t (add hg E)))
      (.conjI hi (intro_encoded w r i t j hE (add hc E)))

theorem decoded_at_code {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a c r i j t : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (termGraph w f a c))
    (hg : Derives Γ (decodedGraph w f a r)) (hc : Derives Γ (code false w j t)) :
    Derives Γ ((edge f i t).iff (edge r i j)) := by
  apply Derives.conjI
  · apply Derives.impI
    let E := edge f i t
    have hE : Derives (Context.add E Γ) E := .hyp (Or.inl rfl)
    have hi := GraphProperties.domain_of_edge f a i t (ZFContext.arithmetic (ZFContext.add hZ E)).base.extensionality
      (.conjL (.conjL (.conjR (add hf E)))) hE
    exact .impE (.conjR (decoded_law w f a r i j (add hg E)))
      (.conjI hi (intro_decoded w f i j t hE (add hc E)))
  · apply Derives.impI
    let E := edge r i j
    let Ξ := Context.add E Γ
    have hE : Derives Ξ E := .hyp (Or.inl rfl)
    have he := Derives.conjR (.impE (.conjL (decoded_law w f a r i j (add hg E))) hE)
    let T := (edge f.castSucc i.castSucc (Fin.last m)).conj (code false w.castSucc j.castSucc (Fin.last m))
    let Δ := Context.add T (Context.image Formula.raise Ξ)
    apply Derives.exE (p := T) he
    have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under (add hw E) T)
    have hc1 : Derives Δ (code false w.castSucc j.castSucc t.castSucc) := of_eq (code_rename false w j t Fin.castSucc) (under (add hc E) T)
    have hT : Derives Δ T := .hyp (Or.inl rfl)
    have heq := SyntaxVariables.unique (ZFContext.under (ZFContext.add hZ E) T) false _ _ _ _ hw1 (.conjR hT) hc1
    exact of_eq (edge_rename f i t Fin.castSucc).symm (GraphPointwiseSyntax.edge_subst_output _ _ _ _ heq (.conjL hT))

end PPAC.Migration.Internal.SyntaxFreeSubstBridge
