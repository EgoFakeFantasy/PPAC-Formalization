import PPAC.Migration.Internal.PacketReaderCodedConsumption

/-! Every actual history edge has a genuine state carrier: zero seed or a real predecessor row, including nonstandard internal indices. -/
namespace PPAC.Migration.Internal.PacketReaderHistoryStates
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax HornBinderSyntax PacketReaderHistorySyntax PacketReaderHistoryLaws
open SyntaxRenameQuerySyntax (of_eq)

theorem target_on_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o f d p i n : Fin m)
    (hf : Derives Γ (SequenceSyntax.sequence f d w)) (hs : Derives Γ (successor i p))
    (hr : Derives Γ (row w B z o f p)) (he : Derives Γ (edge f i n)) : Derives Γ (PacketReaderStateSyntax.carrier w n) := by
  let R := rowBody w B z o f p
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hf3 := of_eq (SequenceSyntax.sequence_rename f d w (old 3)) (HornBinderRules.under_body 3 hf R)
  have hs3 := of_eq (successor_rename i p (old 3)) (HornBinderRules.under_body 3 hs R)
  have he3 := of_eq (edge_rename f i n (old 3)) (HornBinderRules.under_body 3 he R)
  have hj := OmegaUniversal.successor_unique _ _ _ (ZFContext.arithmetic hZ3).base.extensionality (.conjL hR) hs3
  have htarget := StructuralListTraceOrder.edge_input_subst _ _ _ _ hj (.conjL (.conjR (.conjR hR)))
  have hn := GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ3).base.extensionality (.conjL hf3) htarget he3
  have hc := Derives.conjR (PacketReaderCodedNormalize.carriers _ _ _ _ _ _ (.conjR (.conjR (.conjR hR))))
  exact of_eq (PacketReaderStateSyntax.carrier_rename w n (old 3)).symm (PacketReaderConsumptionTransport.carrier_code _ _ _ hn hc)

theorem zero_on_edge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f i N : Fin m)
    (hh : Derives Γ (history w B z o n r l d f)) (hi : Derives Γ (empty i)) (he : Derives Γ (edge f i N)) :
    Derives Γ (PacketReaderStateSyntax.carrier w N) := by
  have hz := OmegaUniversal.empty_unique i z (ZFContext.arithmetic hZ).base.extensionality hi (zero_at _ _ _ _ _ _ _ _ _ hh)
  have hEdge := StructuralListTraceOrder.edge_input_subst f i z N hz he
  have hN := GraphProperties.single_valued f d z n N (ZFContext.arithmetic hZ).base.extensionality
    (.conjL (sequence_at _ _ _ _ _ _ _ _ _ hh)) (seed_at _ _ _ _ _ _ _ _ _ hh) hEdge
  exact PacketReaderConsumptionTransport.carrier_code w n N hN (source_at _ _ _ _ _ _ _ _ _ hh)

theorem at_edge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r l d f i N : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o n r l d f)) (he : Derives Γ (edge f i N)) :
    Derives Γ (PacketReaderStateSyntax.carrier w N) := by
  have hseq := sequence_at _ _ _ _ _ _ _ _ _ hh
  have hiD := GraphProperties.domain_of_edge f d i N (ZFContext.arithmetic hZ).base.extensionality (.conjL hseq) he
  have hdN := OmegaStructureAlgebra.successor_member w d l (ZFContext.arithmetic hZ).base.extensionality hw
    (length_at _ _ _ _ _ _ _ _ _ hh) (successor_at _ _ _ _ _ _ _ _ _ hh)
  have hiN := StructuralListTraceOrder.member_member hZ w i d hw hdN hiD
  have hsplit := OmegaStructureAlgebra.decomposition_at w i
    (OmegaStructureInduction.decomposition w (ZFContext.separation hZ OmegaStructureSyntax.splitMatrix) hw) hiN
  apply Derives.disjE hsplit
  · exact zero_on_edge (ZFContext.add hZ _) _ _ _ _ _ _ _ _ _ _ _ (add hh _) (.hyp (Or.inl rfl)) (add he _)
  · let P := OmegaStructureSyntax.predecessor w i
    let R := (Formula.mem (Fin.last m) w.castSucc).conj (successor i.castSucc (Fin.last m))
    let Δ := Context.add R (Context.image Formula.raise (Context.add P Γ))
    apply Derives.exE (p := R) (.hyp (Or.inl rfl))
    have hR : Derives Δ R := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ P) R
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw P) R)
    have hh1 := of_eq (history_rename w B z o n r l d f Fin.castSucc) (under (add hh P) R)
    have he1 := of_eq (edge_rename f i N Fin.castSucc) (under (add he P) R)
    have hiD1 : Derives Δ (.mem i.castSucc d.castSucc) := under (add hiD P) R
    have hpL := SyntaxIndexLiftOrder.predecessor_member hZ1 _ _ _ _ _ hw1
      (length_at _ _ _ _ _ _ _ _ _ hh1) (successor_at _ _ _ _ _ _ _ _ _ hh1) hiD1 (.conjR hR)
    have hrow := row_at _ _ _ _ _ _ _ _ _ _ hh1 hpL
    have hout := target_on_row hZ1 _ _ _ _ _ _ _ _ _ (sequence_at _ _ _ _ _ _ _ _ _ hh1) (.conjR hR) hrow he1
    simpa only [Formula.raise,PacketReaderStateSyntax.carrier_rename] using hout

end PPAC.Migration.Internal.PacketReaderHistoryStates
