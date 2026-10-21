import PPAC.Migration.Internal.StructuralListTerminal

/-! 原Nil长度为零，原Cons长度有实际前驱且保留固定前驱长度的完整尾轨迹。 -/
namespace PPAC.Migration.Internal.StructuralListLengthRules
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax StructuralListTraceSyntax StructuralListLengthSyntax
open StructuralListTraceProperties
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem trace_nil_empty {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e l d f n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (trace w z e l d f n)) (hn : Derives Γ (nilCode w n)) : Derives Γ (empty l) := by
  have hs := OmegaStructureAlgebra.decomposition_at w l
    (OmegaStructureInduction.decomposition w (ZFContext.separation hZ OmegaStructureSyntax.splitMatrix) hw) (length_at _ _ _ _ _ _ _ ht)
  apply Derives.disjE hs
  · exact .hyp (Or.inl rfl)
  · let P := OmegaStructureSyntax.predecessor w l
    let Γp := Context.add P Γ
    let Q := (Formula.mem (Fin.last m) w.castSucc).conj (successor l.castSucc (Fin.last m))
    let Δ := Context.add Q (Context.image Formula.raise Γp)
    have hq : Derives Γp (.ex Q) := .hyp (Or.inl rfl)
    apply Derives.exE (p := Q) hq
    have hZ1 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.add hZ P) Q
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under (add hw P) Q
    have ht1 : Derives Δ (trace w.castSucc z.castSucc e.castSucc l.castSucc d.castSucc f.castSucc n.castSucc) := by simpa only [Formula.raise, trace_rename] using under (add ht P) Q
    have hn1 : Derives Δ (nilCode w.castSucc n.castSucc) := by simpa only [Formula.raise, nilCode_rename] using under (add hn P) Q
    have hQ : Derives Δ Q := .hyp (Or.inl rfl)
    exact .botE (StructuralListTerminal.no_nil_successor hZ1 _ _ _ _ _ _ _ _ hw1 (.conjR hQ) ht1 hn1)

theorem trace_cons_predecessor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e l d f n h t : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hf : Derives Γ (trace w z e l d f n)) (hc : Derives Γ (consCode w h t n)) : Derives Γ (predecessorLength w t l) := by
  have hs := OmegaStructureAlgebra.decomposition_at w l
    (OmegaStructureInduction.decomposition w (ZFContext.separation hZ OmegaStructureSyntax.splitMatrix) hw) (length_at _ _ _ _ _ _ _ hf)
  apply Derives.disjE hs
  · have hnil := StructuralListTraceInvert.zero_case (ZFContext.add hZ _) _ _ _ _ _ _ _ (add hf _) (.hyp (Or.inl rfl))
    exact .botE (StructuralConsUnique.disjoint (ZFContext.add hZ _) _ _ _ _ (add hw _) hnil (add hc _))
  · let P := OmegaStructureSyntax.predecessor w l
    let Γp := Context.add P Γ
    let Q := (Formula.mem (Fin.last m) w.castSucc).conj (successor l.castSucc (Fin.last m))
    let Δ := Context.add Q (Context.image Formula.raise Γp)
    have hq : Derives Γp (.ex Q) := .hyp (Or.inl rfl)
    apply Derives.exE (p := Q) hq
    have hZ1 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.add hZ P) Q
    have lift {q : Formula m} (hq : Derives Γ q) : Derives Δ q.raise := under (add hq P) Q
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
    have hf1 : Derives Δ (trace w.castSucc z.castSucc e.castSucc l.castSucc d.castSucc f.castSucc n.castSucc) := by simpa only [Formula.raise, trace_rename] using lift hf
    have hc1 : Derives Δ (consCode w.castSucc h.castSucc t.castSucc n.castSucc) := by simpa only [Formula.raise, consCode_rename] using lift hc
    have hQ : Derives Δ Q := .hyp (Or.inl rfl)
    have hedge := StructuralListTerminal.known_tail_edge hZ1 _ _ _ _ _ _ _ _ _ _ hw1 (lift hh) (lift ht) (.conjR hQ) hf1 hc1
    have hprefix := StructuralListTracePrefix.exists_prefix_trace hZ1 _ _ _ _ _ _ _ _ _ hw1 (.conjL hQ) (.conjR hQ) hf1 hedge
    have hlen := StructuralListLengthBasic.from_existsTrace _ _ _ _ _ _ hprefix
    have hout := intro_predecessor _ _ _ _ (.conjL hQ) (.conjR hQ) hlen
    simpa only [Formula.raise, predecessorLength_rename] using hout

theorem nil_empty {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (nilCode w n)) (hl : Derives Γ (hasLength w n l)) : Derives Γ (empty l) := by
  let L := lengthBody w n l
  let Δ := Context.add L (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply eliminate_length w n l _ hl
  have hZ4 : ZFContext.Evidence Δ := zf_under_four hZ L
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under_four hw L
  have hn4 : Derives Δ (nilCode w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, nilCode_rename] using under_four hn L
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hout := trace_nil_empty hZ4 _ _ _ _ _ _ _ hw4 hL hn4
  simpa only [Formula.raise, empty_rename] using hout

theorem cons_predecessor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n l : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (consCode w h t n)) (hl : Derives Γ (hasLength w n l)) : Derives Γ (predecessorLength w t l) := by
  let L := lengthBody w n l
  let Δ := Context.add L (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))
  apply eliminate_length w n l _ hl
  have hZ4 : ZFContext.Evidence Δ := zf_under_four hZ L
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under_four hw L
  have hc4 : Derives Δ (consCode w.castSucc.castSucc.castSucc.castSucc h.castSucc.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, consCode_rename] using under_four hc L
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hout := trace_cons_predecessor hZ4 _ _ _ _ _ _ _ _ _ hw4 (under_four hh L) (under_four ht L) hL hc4
  simpa only [Formula.raise, predecessorLength_rename] using hout
end PPAC.Migration.Internal.StructuralListLengthRules
