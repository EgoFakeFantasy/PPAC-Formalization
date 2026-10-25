import PPAC.Migration.Internal.SequencePrependEdges

/-! Actual predecessor/zero rows transfer to the exact prepended sequence, retaining the original coded step. -/
namespace PPAC.Migration.Internal.PacketReaderHistoryPrependRows
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax HornBinderSyntax PacketReaderHistorySyntax PacketReaderHistoryLaws
open SyntaxRenameQuerySyntax (of_eq)

theorem successor_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o f d n e g i j : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w)) (he : Derives Γ (successor e d))
    (hf : Derives Γ (SequenceSyntax.sequence f d w)) (hg : Derives Γ (SequencePrependSyntax.graph f d n e g))
    (hs : Derives Γ (successor i j)) (hr : Derives Γ (row w B z o f j)) : Derives Γ (row w B z o g i) := by
  let R := rowBody w B z o f j
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hd3 : Derives Δ (.mem (old 3 d) (old 3 w)) := HornBinderRules.under_body 3 hd R
  have he3 := of_eq (successor_rename e d (old 3)) (HornBinderRules.under_body 3 he R)
  have hf3 := of_eq (SequenceSyntax.sequence_rename f d w (old 3)) (HornBinderRules.under_body 3 hf R)
  have hg3 := of_eq (SequencePrependSyntax.graph_rename f d n e g (old 3)) (HornBinderRules.under_body 3 hg R)
  have hs3 := of_eq (successor_rename i j (old 3)) (HornBinderRules.under_body 3 hs R)
  have hk := OmegaUniversal.successor_unique (slot 3 0) (old 3 i) (old 3 j) (ZFContext.arithmetic hZ3).base.extensionality (.conjL hR) hs3
  have hOldTarget := StructuralListTraceOrder.edge_input_subst _ _ _ _ hk (.conjL (.conjR (.conjR hR)))
  have hjD := GraphProperties.domain_of_edge _ _ _ _ (ZFContext.arithmetic hZ3).base.extensionality (.conjL hf3) (.conjL (.conjR hR))
  have hiD := GraphProperties.domain_of_edge _ _ _ _ (ZFContext.arithmetic hZ3).base.extensionality (.conjL hf3) hOldTarget
  have hSource := SequencePrependEdges.forward_edge hZ3 _ _ _ _ _ _ _ _ _ hw3 hd3 he3 hg3 hjD hs3 (.conjL (.conjR hR))
  let V := successor (Fin.last (m+3)) (old 3 i).castSucc
  let Ξ := Context.add V (Context.image Formula.raise Δ)
  apply Derives.exE (p := V) (InsertExistence.exists_insert (old 3 i) (old 3 i) (ZFContext.arithmetic hZ3).base.pairing (ZFContext.arithmetic hZ3).base.union)
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  have hZ4 := ZFContext.under hZ3 V
  have hw4 := of_eq (omega_rename (old 3 w) Fin.castSucc) (under hw3 V)
  have he4 := of_eq (successor_rename (old 3 e) (old 3 d) Fin.castSucc) (under he3 V)
  have hg4 := of_eq (SequencePrependSyntax.graph_rename (old 3 f) (old 3 d) (old 3 n) (old 3 e) (old 3 g) Fin.castSucc) (under hg3 V)
  have hTargetOld := of_eq (edge_rename (old 3 f) (old 3 i) (slot 3 2) Fin.castSucc) (under hOldTarget V)
  have hTarget := SequencePrependEdges.forward_edge hZ4 _ _ _ _ _ _ _ _ _ hw4 (under hd3 V) he4 hg4 (under hiD V) hV hTargetOld
  have hSource4 := of_eq (edge_rename (old 3 g) (old 3 i) (slot 3 1) Fin.castSucc) (under hSource V)
  have hStep4 := of_eq (PacketReaderCodedSyntax.step_rename (old 3 w) (old 3 B) (old 3 z) (old 3 o) (slot 3 1) (slot 3 2) Fin.castSucc) (under (.conjR (.conjR (.conjR hR))) V)
  have hout := intro_row (old 3 w).castSucc (old 3 B).castSucc (old 3 z).castSucc (old 3 o).castSucc (old 3 g).castSucc (old 3 i).castSucc (Fin.last (m+3)) (slot 3 1).castSucc (slot 3 2).castSucc hV hSource4 hTarget hStep4
  simpa only [Formula.raise,row_rename] using hout

theorem zero_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o n r t l d e f g : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (history w B z o r t l d f))
    (he : Derives Γ (successor e d)) (hg : Derives Γ (SequencePrependSyntax.graph f d n e g))
    (ht : Derives Γ (PacketReaderCodedSyntax.step w B z o n r)) : Derives Γ (row w B z o g z) := by
  have hd := OmegaStructureAlgebra.successor_member w d l (ZFContext.arithmetic hZ).base.extensionality hw (length_at _ _ _ _ _ _ _ _ _ hh) (successor_at _ _ _ _ _ _ _ _ _ hh)
  have hf := sequence_at _ _ _ _ _ _ _ _ _ hh
  have hz := zero_at _ _ _ _ _ _ _ _ _ hh
  have hSeed := seed_at _ _ _ _ _ _ _ _ _ hh
  have hzD := GraphProperties.domain_of_edge _ _ _ _ (ZFContext.arithmetic hZ).base.extensionality (.conjL hf) hSeed
  have hNewSeed := SequencePrependEdges.zero_edge hZ _ _ _ _ _ _ _ hw hd he hg hz
  let U := successor (Fin.last m) z.castSucc
  let Δ := Context.add U (Context.image Formula.raise Γ)
  apply Derives.exE (p := U) (InsertExistence.exists_insert z z (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union)
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ U
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw U)
  have he1 := of_eq (successor_rename e d Fin.castSucc) (under he U)
  have hg1 := of_eq (SequencePrependSyntax.graph_rename f d n e g Fin.castSucc) (under hg U)
  have hSeed1 := of_eq (edge_rename f z r Fin.castSucc) (under hSeed U)
  have hTarget := SequencePrependEdges.forward_edge hZ1 _ _ _ _ _ _ _ _ _ hw1 (under hd U) he1 hg1 (under hzD U) hU hSeed1
  have hNew1 := of_eq (edge_rename g z n Fin.castSucc) (under hNewSeed U)
  have ht1 := of_eq (PacketReaderCodedSyntax.step_rename w B z o n r Fin.castSucc) (under ht U)
  simpa only [Formula.raise,row_rename] using intro_row _ _ _ _ _ _ _ _ _ hU hNew1 hTarget ht1

end PPAC.Migration.Internal.PacketReaderHistoryPrependRows
