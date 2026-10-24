import PPAC.Migration.Internal.PacketBytesTraceProperties

/-! Both original sequence append operations construct the full new byte-fold witness. -/
namespace PPAC.Migration.Internal.PacketBytesTraceAppend
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax GraphPointwiseSyntax
open PacketBytesTraceSyntax PacketBytesTraceProperties
open SyntaxRenameQuerySyntax (of_eq)

theorem from_append {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n t a z e l d f g h p b k F G : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (trace w C n t a z e l d f g))
    (hc : Derives Γ (StructuralListSyntax.consCode w h n p)) (ha : Derives Γ (PacketAffineSyntax.affine w C h a b))
    (hk : Derives Γ (successor k d)) (hF : Derives Γ (SequenceSyntax.append F k f d p w))
    (hG : Derives Γ (SequenceSyntax.append G k g d b w)) : Derives Γ (trace w C p t b z e d k F G) := by
  have hlist := list_trace _ _ _ _ _ _ _ _ _ _ _ ht
  have hh := PacketAffineCore.digit_natural hZ w C h a b hw ha
  have hnewlist := StructuralListTraceAppend.from_append hZ w z e l d f n h p k F hw hh hlist hc hk hF
  have hFi := StructuralListTraceRows.old_included _ _ _ _ (.conjL (.conjR hF))
  have hGi := StructuralListTraceRows.old_included _ _ _ _ (.conjL (.conjR hG))
  have hFl := Derives.impE (edgeIncluded_at _ _ _ _ hFi) (StructuralListTraceProperties.last_at _ _ _ _ _ _ _ hlist)
  have hGl := Derives.impE (edgeIncluded_at _ _ _ _ hGi) (last_edge _ _ _ _ _ _ _ _ _ _ _ ht)
  have hseed := Derives.impE (edgeIncluded_at _ _ _ _ hGi) (seed_edge _ _ _ _ _ _ _ _ _ _ _ ht)
  have hFp := StructuralListTraceRows.new_edge _ _ _ _ (.conjL (.conjR hF))
  have hGb := StructuralListTraceRows.new_edge _ _ _ _ (.conjL (.conjR hG))
  have hs := StructuralListTraceProperties.successor_at _ _ _ _ _ _ _ hlist
  have hrow := PacketBytesRowSyntax.intro_row w C F G l d h n p a b hs hFl hFp hc hGl hGb ha
  have hlinks := PacketBytesRowMap.append_links w C l d f g F G hs (byte_links _ _ _ _ _ _ _ _ _ _ _ ht) hFi hGi hrow
  exact intro_trace _ _ _ _ _ _ _ _ _ _ _ hnewlist (.conjL hG) hseed hGb hlinks

theorem at_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n t a z e l d f g h p b k : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (trace w C n t a z e l d f g))
    (hc : Derives Γ (StructuralListSyntax.consCode w h n p)) (ha : Derives Γ (PacketAffineSyntax.affine w C h a b))
    (hk : Derives Γ (successor k d)) : Derives Γ (foldAt w C p t b) := by
  have hp := StructuralConsCore.range hZ w h n p hw hc
  have hF := SequenceAppend.exists_append (ZFContext.arithmetic hZ).base k f d p w
    (StructuralListTraceProperties.sequence_at _ _ _ _ _ _ _ (list_trace _ _ _ _ _ _ _ _ _ _ _ ht)) hp hk
  let F := SequenceSyntax.append (Fin.last m) k.castSucc f.castSucc d.castSucc p.castSucc w.castSucc
  let ΓF := Context.add F (Context.image Formula.raise Γ)
  apply Derives.exE (p := F) hF
  have hZ1 := ZFContext.under hZ F
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw F)
  have ht1 := of_eq (trace_rename w C n t a z e l d f g Fin.castSucc) (under ht F)
  have hc1 := of_eq (StructuralListSyntax.consCode_rename w h n p Fin.castSucc) (under hc F)
  have ha1 := of_eq (PacketAffineSyntax.affine_rename w C h a b Fin.castSucc) (under ha F)
  have hk1 := of_eq (successor_rename k d Fin.castSucc) (under hk F)
  have hG := SequenceAppend.exists_append (ZFContext.arithmetic hZ1).base k.castSucc g.castSucc d.castSucc b.castSucc w.castSucc
    (value_sequence _ _ _ _ _ _ _ _ _ _ _ ht1) (PacketAffineCore.output_guard _ _ _ _ _ ha1) hk1
  let G := SequenceSyntax.append (Fin.last (m+1)) k.castSucc.castSucc g.castSucc.castSucc d.castSucc.castSucc b.castSucc.castSucc w.castSucc.castSucc
  let Δ := Context.add G (Context.image Formula.raise ΓF)
  apply Derives.exE (p := G) hG
  have hZ2 := ZFContext.under hZ1 G
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 G)
  have ht2 := of_eq (trace_rename w.castSucc C.castSucc n.castSucc t.castSucc a.castSucc z.castSucc e.castSucc l.castSucc d.castSucc f.castSucc g.castSucc Fin.castSucc) (under ht1 G)
  have hc2 := of_eq (StructuralListSyntax.consCode_rename w.castSucc h.castSucc n.castSucc p.castSucc Fin.castSucc) (under hc1 G)
  have ha2 := of_eq (PacketAffineSyntax.affine_rename w.castSucc C.castSucc h.castSucc a.castSucc b.castSucc Fin.castSucc) (under ha1 G)
  have hk2 := of_eq (successor_rename k.castSucc d.castSucc Fin.castSucc) (under hk1 G)
  have hFold : Derives ΓF F := .hyp (Or.inl rfl)
  have hF2 := of_eq (SequenceSyntax.append_rename (Fin.last m) k.castSucc f.castSucc d.castSucc p.castSucc w.castSucc Fin.castSucc) (under hFold G)
  have hG2 : Derives Δ G := .hyp (Or.inl rfl)
  have hnew := from_append hZ2 w.castSucc.castSucc C.castSucc.castSucc n.castSucc.castSucc t.castSucc.castSucc a.castSucc.castSucc
    z.castSucc.castSucc e.castSucc.castSucc l.castSucc.castSucc d.castSucc.castSucc f.castSucc.castSucc g.castSucc.castSucc
    h.castSucc.castSucc p.castSucc.castSucc b.castSucc.castSucc k.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 ht2 hc2 ha2 hk2 hF2 hG2
  simpa only [Formula.raise,foldAt_rename] using intro_fold _ _ _ _ _ _ _ _ _ _ _ hnew

theorem extend_trace {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n t a z e l d f g h p b : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (trace w C n t a z e l d f g))
    (hc : Derives Γ (StructuralListSyntax.consCode w h n p)) (ha : Derives Γ (PacketAffineSyntax.affine w C h a b)) :
    Derives Γ (foldAt w C p t b) := by
  have hd := StructuralListTraceProperties.domain_member hZ w z e l d f n hw (list_trace _ _ _ _ _ _ _ _ _ _ _ ht)
  let K := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) d.castSucc)
  let Δ := Context.add K (Context.image Formula.raise Γ)
  apply Derives.exE (p := K) (Derives.impE (step_at w d (.conjL hw)) hd)
  have hZ1 := ZFContext.under hZ K
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw K)
  have ht1 := of_eq (trace_rename w C n t a z e l d f g Fin.castSucc) (under ht K)
  have hc1 := of_eq (StructuralListSyntax.consCode_rename w h n p Fin.castSucc) (under hc K)
  have ha1 := of_eq (PacketAffineSyntax.affine_rename w C h a b Fin.castSucc) (under ha K)
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  simpa only [Formula.raise,foldAt_rename] using
    (at_successor hZ1 w.castSucc C.castSucc n.castSucc t.castSucc a.castSucc z.castSucc e.castSucc l.castSucc d.castSucc f.castSucc g.castSucc h.castSucc p.castSucc b.castSucc (Fin.last m) hw1 ht1 hc1 ha1 (.conjR hK))

theorem cons_fold {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n t a h p b : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (foldAt w C n t a))
    (hc : Derives Γ (StructuralListSyntax.consCode w h n p)) (ha : Derives Γ (PacketAffineSyntax.affine w C h a b)) :
    Derives Γ (foldAt w C p t b) := by
  let R := body w C n t a
  let Δ := Context.add R (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 R _ hf
  have hZ6 := HornBinderRules.zf_body 6 hZ R
  have hw6 := of_eq (omega_rename w (old 6)) (HornBinderRules.under_body 6 hw R)
  have hc6 := of_eq (StructuralListSyntax.consCode_rename w h n p (old 6)) (HornBinderRules.under_body 6 hc R)
  have ha6 := of_eq (PacketAffineSyntax.affine_rename w C h a b (old 6)) (HornBinderRules.under_body 6 ha R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact of_eq (foldAt_rename w C p t b (old 6)).symm
    (extend_trace hZ6 (old 6 w) (old 6 C) (old 6 n) (old 6 t) (old 6 a)
      (slot 6 0) (slot 6 1) (slot 6 2) (slot 6 3) (slot 6 4) (slot 6 5) (old 6 h) (old 6 p) (old 6 b) hw6 hR hc6 ha6)

end PPAC.Migration.Internal.PacketBytesTraceAppend
