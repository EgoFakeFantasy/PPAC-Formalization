import PPAC.Migration.Internal.PacketTokensBytesTraceTransport

/-! The empty-list fold is constructed by real singleton sequences and characterized exactly. -/
namespace PPAC.Migration.Internal.PacketTokensBytesTraceBase
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax PacketTokensBytesSyntax PacketTokensBytesTraceProperties
open SyntaxRenameQuerySyntax (of_eq)

theorem at_units {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e t : Fin m)
    (hw : Derives Γ (omega w)) (hz : Derives Γ (empty z)) (he : Derives Γ (successor e z)) (ht : Derives Γ (.mem t w)) :
    Derives Γ (raw w e t t) := by
  let F := StructuralListTraceSyntax.trace w.castSucc z.castSucc e.castSucc z.castSucc e.castSucc (Fin.last m) e.castSucc
  let ΓF := Context.add F (Context.image Formula.raise Γ)
  apply Derives.exE (p := F) (StructuralListTraceBase.exists_base hZ w z e hw hz he)
  have hZ1 := ZFContext.under hZ F
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz F)
  have he1 := of_eq (successor_rename e z Fin.castSucc) (under he F)
  have hg := SequenceAppend.exists_append (ZFContext.arithmetic hZ1).base e.castSucc z.castSucc z.castSucc t.castSucc w.castSucc
    (SequenceLogic.empty_sequence z.castSucc w.castSucc hz1) (under ht F) he1
  let G := SequenceSyntax.append (Fin.last (m+1)) e.castSucc.castSucc z.castSucc.castSucc z.castSucc.castSucc t.castSucc.castSucc w.castSucc.castSucc
  let Δ := Context.add G (Context.image Formula.raise ΓF)
  apply Derives.exE (p := G) hg
  have hF : Derives ΓF F := .hyp (Or.inl rfl)
  have hf2 := of_eq (StructuralListTraceSyntax.trace_rename w.castSucc z.castSucc e.castSucc z.castSucc e.castSucc (Fin.last m) e.castSucc Fin.castSucc) (under hF G)
  have hz2 := of_eq (empty_rename z.castSucc Fin.castSucc) (under hz1 G)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hedge := StructuralListTraceRows.new_edge _ _ _ _ (.conjL (.conjR hG))
  have hl := PacketTokensBytesRowSyntax.empty_links w.castSucc.castSucc z.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hz2
  have htr := intro_trace w.castSucc.castSucc e.castSucc.castSucc t.castSucc.castSucc t.castSucc.castSucc
    z.castSucc.castSucc e.castSucc.castSucc z.castSucc.castSucc e.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hf2 (.conjL hG) hedge hedge hl
  simpa only [Formula.raise,raw_rename] using intro_raw _ _ _ _ _ _ _ _ _ _ htr

theorem nil_fold {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListSyntax.nilCode w n)) (ht : Derives Γ (.mem t w)) :
    Derives Γ (raw w n t t) := by
  let U := StructuralListSyntax.unitWitness m
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralListUnits.with_units w _ hw
  have hZ2 := ZFContext.under_two hZ U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (OrderedPairElimination.under_two hw U)
  have hn2 : Derives Δ (StructuralListSyntax.nilCode w.castSucc.castSucc n.castSucc.castSucc) := of_eq (by simp only [Formula.raise,StructuralListSyntax.nilCode_rename]) (OrderedPairElimination.under_two hn U)
  have ht2 : Derives Δ (.mem t.castSucc.castSucc w.castSucc.castSucc) := OrderedPairElimination.under_two ht U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have heq := StructuralNil.value hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc hw2 (.conjL hU) (.conjR hU) hn2
  have hf := at_units hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) t.castSucc.castSucc hw2 (.conjL hU) (.conjR hU) ht2
  simpa only [Formula.raise,raw_rename] using PacketTokensBytesTraceTransport.input_subst _ _ _ _ _ (eq_symm heq) hf

theorem nil_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListSyntax.nilCode w n)) (hf : Derives Γ (raw w n t a)) :
    Derives Γ (.equal t a) := by
  let R := body w n t a
  let Δ := Context.add R (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 R _ hf
  have hZ6 := HornBinderRules.zf_body 6 hZ R
  have hw6 := of_eq (omega_rename w (old 6)) (HornBinderRules.under_body 6 hw R)
  have hn6 := of_eq (StructuralListSyntax.nilCode_rename w n (old 6)) (HornBinderRules.under_body 6 hn R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hl := StructuralListLengthRules.nil_empty hZ6 (old 6 w) (old 6 n) (slot 6 2) hw6 hn6 (length _ _ _ _ _ _ _ _ _ _ hR)
  have hz := StructuralListTraceProperties.zero_at _ _ _ _ _ _ _ (list_trace _ _ _ _ _ _ _ _ _ _ hR)
  have heq := OmegaUniversal.empty_unique (slot 6 0) (slot 6 2) (ZFContext.arithmetic hZ6).base.extensionality hz hl
  have hs := StructuralListTraceOrder.edge_input_subst (slot 6 5) (slot 6 0) (slot 6 2) (old 6 t) heq (seed_edge _ _ _ _ _ _ _ _ _ _ hR)
  exact GraphProperties.single_valued (slot 6 5) (slot 6 3) (slot 6 2) (old 6 t) (old 6 a) (ZFContext.arithmetic hZ6).base.extensionality
    (.conjL (value_sequence _ _ _ _ _ _ _ _ _ _ hR)) hs (last_edge _ _ _ _ _ _ _ _ _ _ hR)

theorem domain {m} {Γ : Context m} (w n t a : Fin m) (hf : Derives Γ (raw w n t a)) :
    Derives Γ ((StructuralListTraceSyntax.valid w n).conj ((Formula.mem t w).conj (.mem a w))) := by
  let R := body w n t a
  let Δ := Context.add R (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 R _ hf
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hout := Derives.conjI (valid _ _ _ _ _ _ _ _ _ _ hR) (.conjI (tail_natural _ _ _ _ _ _ _ _ _ _ hR) (output_natural _ _ _ _ _ _ _ _ _ _ hR))
  simpa only [Formula.rename,StructuralListTraceSyntax.valid_rename] using hout

theorem nil_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (StructuralListSyntax.nilCode w n)) :
    Derives Γ ((raw w n t a).iff ((Formula.mem t w).conj (.equal t a))) := by
  apply Derives.conjI
  · apply Derives.impI
    have hf : Derives (Context.add (raw w n t a) Γ) (raw w n t a) := .hyp (Or.inl rfl)
    exact .conjI (.conjL (.conjR (domain w n t a hf))) (nil_value (ZFContext.add hZ _) w n t a (add hw _) (add hn _) hf)
  · apply Derives.impI
    have hE : Derives (Context.add ((Formula.mem t w).conj (.equal t a)) Γ) ((Formula.mem t w).conj (.equal t a)) := .hyp (Or.inl rfl)
    exact PacketTokensBytesTraceTransport.output_subst w n t t a (.conjR hE) (nil_fold (ZFContext.add hZ _) w n t (add hw _) (add hn _) (.conjL hE))

end PPAC.Migration.Internal.PacketTokensBytesTraceBase
