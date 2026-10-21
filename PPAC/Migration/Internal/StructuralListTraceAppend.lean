import PPAC.Migration.Internal.StructuralListTraceBase

/-! 原Cons实际追加到完整轨迹；旧相邻步与新末步分别给出真实推导。 -/
namespace PPAC.Migration.Internal.StructuralListTraceAppend
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SequenceSyntax StructuralListSyntax StructuralListTraceSyntax GraphPointwiseSyntax
open StructuralListTraceProperties
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem from_append {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e l d f n h y k g : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (trace w z e l d f n))
    (hc : Derives Γ (consCode w h n y)) (hk : Derives Γ (successor k d))
    (hg : Derives Γ (SequenceSyntax.append g k f d y w)) : Derives Γ (trace w z e d k g y) := by
  have hdW := domain_member hZ _ _ _ _ _ _ _ hw ht
  have hlaw := Derives.conjL (Derives.conjR hg)
  have hinc := StructuralListTraceRows.old_included _ _ _ _ hlaw
  have hlast := Derives.impE (edgeIncluded_at _ _ _ _ hinc) (last_at _ _ _ _ _ _ _ ht)
  have hseed := Derives.impE (edgeIncluded_at _ _ _ _ hinc) (seed_at _ _ _ _ _ _ _ ht)
  have hnew := StructuralListTraceRows.new_edge _ _ _ _ hlaw
  have hrow := intro_row _ _ _ _ _ _ (successor_at _ _ _ _ _ _ _ ht) hlast hnew (intro_step _ _ _ _ hh hc)
  have hlinks := StructuralListTraceRows.append_links _ _ _ _ _ (successor_at _ _ _ _ _ _ _ ht) (links_at_trace _ _ _ _ _ _ _ ht) hinc hrow
  exact intro_trace _ _ _ _ _ _ _ (zero_at _ _ _ _ _ _ _ ht) (nil_at _ _ _ _ _ _ _ ht) hdW hk (.conjL hg) hseed hlinks hnew

theorem exists_append {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e l d f n h y k : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (trace w z e l d f n))
    (hc : Derives Γ (consCode w h n y)) (hk : Derives Γ (successor k d)) : Derives Γ (existsTrace w z e d k y) := by
  have hy := StructuralConsCore.range hZ _ _ _ _ hw hc
  have hg := SequenceAppend.exists_append (ZFContext.arithmetic hZ).base k f d y w (sequence_at _ _ _ _ _ _ _ ht) hy hk
  let G := SequenceSyntax.append (Fin.last m) k.castSucc f.castSucc d.castSucc y.castSucc w.castSucc
  let Δ := Context.add G (Context.image Formula.raise Γ)
  change Derives Γ (.ex G) at hg
  apply Derives.exE (p := G) hg
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ G
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw G
  have ht1 : Derives Δ (trace w.castSucc z.castSucc e.castSucc l.castSucc d.castSucc f.castSucc n.castSucc) := by simpa only [Formula.raise, trace_rename] using under ht G
  have hc1 : Derives Δ (consCode w.castSucc h.castSucc n.castSucc y.castSucc) := by simpa only [Formula.raise, consCode_rename] using under hc G
  have hk1 : Derives Δ (successor k.castSucc d.castSucc) := by simpa only [Formula.raise, successor_rename] using under hk G
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hnew := from_append hZ1 _ _ _ _ _ _ _ _ _ _ _ hw1 (under hh G) ht1 hc1 hk1 hG
  have hout := intro_existsTrace _ _ _ _ _ _ _ hnew
  simpa only [Formula.raise, existsTrace_rename] using hout

theorem extend_valid {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e l d f n h y : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (trace w z e l d f n))
    (hc : Derives Γ (consCode w h n y)) : Derives Γ (valid w y) := by
  have hdW := domain_member hZ _ _ _ _ _ _ _ hw ht
  have hk := Derives.impE (step_at w d (.conjL hw)) hdW
  let K := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) d.castSucc)
  let Ξ := Context.add K (Context.image Formula.raise Γ)
  change Derives Γ (.ex K) at hk
  apply Derives.exE (p := K) hk
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ K
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw K
  have ht1 : Derives Ξ (trace w.castSucc z.castSucc e.castSucc l.castSucc d.castSucc f.castSucc n.castSucc) := by simpa only [Formula.raise, trace_rename] using under ht K
  have hc1 : Derives Ξ (consCode w.castSucc h.castSucc n.castSucc y.castSucc) := by simpa only [Formula.raise, consCode_rename] using under hc K
  have hK : Derives Ξ K := .hyp (Or.inl rfl)
  have hf := exists_append hZ1 _ _ _ _ _ _ _ _ _ _ hw1 (under hh K) ht1 hc1 (.conjR hK)
  let F := trace w.castSucc.castSucc z.castSucc.castSucc e.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) y.castSucc.castSucc
  let Δ := Context.add F (Context.image Formula.raise Ξ)
  change Derives Ξ (.ex F) at hf
  apply Derives.exE (p := F) hf
  have hF : Derives Δ F := .hyp (Or.inl rfl)
  have hout := intro_valid _ _ _ _ _ _ _ hF
  simpa only [Formula.raise, valid_rename] using hout
end PPAC.Migration.Internal.StructuralListTraceAppend
