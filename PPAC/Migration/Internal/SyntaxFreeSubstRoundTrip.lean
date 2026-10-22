import PPAC.Migration.Internal.SyntaxFreeSubstBridge

/-! 实际项字段图与实际索引图互为准确逆转换，保留全部候选边。 -/
namespace PPAC.Migration.Internal.SyntaxFreeSubstRoundTrip
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SyntaxRenameQuerySyntax SyntaxFreeSubstSyntax SyntaxFreeSubstBridge
open SyntaxVariableSyntax (code code_rename)
open SyntaxIndexMapSyntax (indexMap indexMap_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem encoded_decode_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c f i j : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (indexMap w r a c))
    (hg : Derives Γ (encodedGraph w r a f)) (he : Derives Γ (edge r i j)) : Derives Γ (decodedValue w f i j) := by
  have hc := SyntaxIndexMapSyntax.edge_target w r a c i j hr he
  have hj := StructuralListTraceOrder.member_member hZ w j c hw (.conjR (.conjL hr)) hc
  let T := (Formula.mem (Fin.last m) w.castSucc).conj (code false w.castSucc j.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (SyntaxVariables.exists_code hZ false w j hw hj)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have hr1 : Derives Δ (indexMap w.castSucc r.castSucc a.castSucc c.castSucc) := of_eq (indexMap_rename w r a c Fin.castSucc) (under hr T)
  have hg1 : Derives Δ (encodedGraph w.castSucc r.castSucc a.castSucc f.castSucc) := of_eq (encodedGraph_rename w r a f Fin.castSucc) (under hg T)
  have he1 : Derives Δ (edge r.castSucc i.castSucc j.castSucc) := of_eq (edge_rename r i j Fin.castSucc) (under he T)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hb := encoded_at_code (ZFContext.under hZ T) w.castSucc r.castSucc a.castSucc c.castSucc f.castSucc i.castSucc j.castSucc (Fin.last m) hw1 hr1 hg1 (.conjR hT)
  have ho := intro_decoded w.castSucc f.castSucc i.castSucc j.castSucc (Fin.last m) (.impE (.conjR hb) he1) (.conjR hT)
  exact of_eq (decodedValue_rename w f i j Fin.castSucc).symm ho

theorem encoded_recover_edge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c f i j : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (indexMap w r a c))
    (hg : Derives Γ (encodedGraph w r a f)) (hd : Derives Γ (decodedValue w f i j)) : Derives Γ (edge r i j) := by
  let T := (edge f.castSucc i.castSucc (Fin.last m)).conj (code false w.castSucc j.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) hd
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have hr1 : Derives Δ (indexMap w.castSucc r.castSucc a.castSucc c.castSucc) := of_eq (indexMap_rename w r a c Fin.castSucc) (under hr T)
  have hg1 : Derives Δ (encodedGraph w.castSucc r.castSucc a.castSucc f.castSucc) := of_eq (encodedGraph_rename w r a f Fin.castSucc) (under hg T)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hb := encoded_at_code (ZFContext.under hZ T) w.castSucc r.castSucc a.castSucc c.castSucc f.castSucc i.castSucc j.castSucc (Fin.last m) hw1 hr1 hg1 (.conjR hT)
  exact of_eq (edge_rename r i j Fin.castSucc).symm (.impE (.conjL hb) (.conjL hT))

theorem decoded_encode_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a c r i t : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (termGraph w f a c))
    (hg : Derives Γ (decodedGraph w f a r)) (he : Derives Γ (edge f i t)) : Derives Γ (encodedValue w r i t) := by
  have hb := Derives.impE (values_at w f c i t (.conjR (.conjR hf))) he
  let J := SyntaxTermSyntax.branchWitness false w c t
  let Δ := Context.add J (Context.image Formula.raise Γ)
  apply SyntaxTermSyntax.eliminate_branch false w c t _ hb
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw J)
  have hf1 : Derives Δ (termGraph w.castSucc f.castSucc a.castSucc c.castSucc) := of_eq (termGraph_rename w f a c Fin.castSucc) (under hf J)
  have hg1 : Derives Δ (decodedGraph w.castSucc f.castSucc a.castSucc r.castSucc) := of_eq (decodedGraph_rename w f a r Fin.castSucc) (under hg J)
  have he1 : Derives Δ (edge f.castSucc i.castSucc t.castSucc) := of_eq (edge_rename f i t Fin.castSucc) (under he J)
  have hJ : Derives Δ J := .hyp (Or.inl rfl)
  have hk := decoded_at_code (ZFContext.under hZ J) w.castSucc f.castSucc a.castSucc c.castSucc r.castSucc i.castSucc (Fin.last m) t.castSucc hw1 hf1 hg1 (.conjR hJ)
  have ho := intro_encoded w.castSucc r.castSucc i.castSucc t.castSucc (Fin.last m) (.impE (.conjL hk) he1) (.conjR hJ)
  exact of_eq (encodedValue_rename w r i t Fin.castSucc).symm ho

theorem decoded_recover_edge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f a c r i t : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (termGraph w f a c))
    (hg : Derives Γ (decodedGraph w f a r)) (hd : Derives Γ (encodedValue w r i t)) : Derives Γ (edge f i t) := by
  let J := (edge r.castSucc i.castSucc (Fin.last m)).conj (code false w.castSucc (Fin.last m) t.castSucc)
  let Δ := Context.add J (Context.image Formula.raise Γ)
  apply Derives.exE (p := J) hd
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw J)
  have hf1 : Derives Δ (termGraph w.castSucc f.castSucc a.castSucc c.castSucc) := of_eq (termGraph_rename w f a c Fin.castSucc) (under hf J)
  have hg1 : Derives Δ (decodedGraph w.castSucc f.castSucc a.castSucc r.castSucc) := of_eq (decodedGraph_rename w f a r Fin.castSucc) (under hg J)
  have hJ : Derives Δ J := .hyp (Or.inl rfl)
  have hk := decoded_at_code (ZFContext.under hZ J) w.castSucc f.castSucc a.castSucc c.castSucc r.castSucc i.castSucc (Fin.last m) t.castSucc hw1 hf1 hg1 (.conjR hJ)
  exact of_eq (edge_rename f i t Fin.castSucc).symm (.impE (.conjR hk) (.conjL hJ))

theorem encoded_implies_decoded {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c f : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (indexMap w r a c)) (hg : Derives Γ (encodedGraph w r a f)) :
    Derives Γ (decodedGraph w f a r) := by
  apply Derives.conjI (.conjL (.conjR hp))
  simp only [RelationGraphSyntax.edgeLaw, decodeMatrix_rel, ReplacementPredicates.paramsUp, PairSyntax.args2_first, PairSyntax.args2_second]
  apply Derives.allI
  apply Derives.allI
  let Ξ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hZ2 := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [omega_rename]) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw))
  have hp2 : Derives Ξ (indexMap w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc ) := by
    simpa only [Formula.raise, indexMap_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hp)
  have hg2 : Derives Ξ (encodedGraph w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc f.castSucc.castSucc) := by
    simpa only [Formula.raise, encodedGraph_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hg)
  apply Derives.conjI
  · apply Derives.impI
    let E := edge r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    have hE : Derives (Context.add E Ξ) E := .hyp (Or.inl rfl)
    have hi := GraphProperties.domain_of_edge r.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
      (ZFContext.arithmetic (ZFContext.add hZ2 E)).base.extensionality (add (.conjL (.conjR hp2)) E) hE
    exact .conjI hi (encoded_decode_value (ZFContext.add hZ2 E) w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (add hw2 E) (add hp2 E) (add hg2 E) hE)
  · apply Derives.impI
    let V := (Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj (decodedValue w.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
    have hV : Derives (Context.add V Ξ) V := .hyp (Or.inl rfl)
    exact encoded_recover_edge (ZFContext.add hZ2 V) w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (add hw2 V) (add hp2 V) (add hg2 V) (.conjR hV)

theorem decoded_implies_encoded {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c f : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (termGraph w f a c)) (hg : Derives Γ (decodedGraph w f a r)) :
    Derives Γ (encodedGraph w r a f) := by
  apply Derives.conjI (.conjL (.conjL (.conjR hp)))
  simp only [RelationGraphSyntax.edgeLaw, encodeMatrix_rel, ReplacementPredicates.paramsUp, PairSyntax.args2_first, PairSyntax.args2_second]
  apply Derives.allI
  apply Derives.allI
  let Ξ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hZ2 := ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [omega_rename]) (Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hw))
  have hp2 : Derives Ξ (termGraph w.castSucc.castSucc f.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc ) := by
    simpa only [Formula.raise, termGraph_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hp)
  have hg2 : Derives Ξ (decodedGraph w.castSucc.castSucc f.castSucc.castSucc a.castSucc.castSucc r.castSucc.castSucc) := by
    simpa only [Formula.raise, decodedGraph_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hg)
  apply Derives.conjI
  · apply Derives.impI
    let E := edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    have hE : Derives (Context.add E Ξ) E := .hyp (Or.inl rfl)
    have hi := GraphProperties.domain_of_edge f.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
      (ZFContext.arithmetic (ZFContext.add hZ2 E)).base.extensionality (add (.conjL (.conjL (.conjR hp2))) E) hE
    exact .conjI hi (decoded_encode_value (ZFContext.add hZ2 E) w.castSucc.castSucc f.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (add hw2 E) (add hp2 E) (add hg2 E) hE)
  · apply Derives.impI
    let V := (Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj (encodedValue w.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
    have hV : Derives (Context.add V Ξ) V := .hyp (Or.inl rfl)
    exact decoded_recover_edge (ZFContext.add hZ2 V) w.castSucc.castSucc f.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (add hw2 V) (add hp2 V) (add hg2 V) (.conjR hV)

end PPAC.Migration.Internal.SyntaxFreeSubstRoundTrip
