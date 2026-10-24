import PPAC.Migration.Internal.PacketVarintTerminal

/-! Original internal length decomposition and both constructed prefix graphs eliminate all reverse witnesses. -/
namespace PPAC.Migration.Internal.PacketVarintDecomposition
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax PacketVarintTraceSyntax PacketVarintTraceProperties PacketVarintRecursionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem successor_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n t a z e l d f g p : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (.mem p w)) (hs : Derives Γ (successor l p))
    (ht : Derives Γ (trace w C n t a z e l d f g)) : Derives Γ (consCase w C n t a) := by
  have hl := PacketVarintTerminal.terminal_row hZ w C n t a z e l d f g p hs ht
  let R := terminalBody w C f g p n a
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hl
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hp3 : Derives Δ (.mem (old 3 p) (old 3 w)) := HornBinderRules.under_body 3 hp R
  have hs3 := of_eq (successor_rename l p (old 3)) (HornBinderRules.under_body 3 hs R)
  have ht3 := of_eq (trace_rename w C n t a z e l d f g (old 3)) (HornBinderRules.under_body 3 ht R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hf := PacketVarintTracePrefix.exists_prefix hZ3 (old 3 w) (old 3 C) (old 3 n) (old 3 t) (old 3 a)
    (old 3 z) (old 3 e) (old 3 l) (old 3 d) (old 3 f) (old 3 g) (old 3 p) (slot 3 1) (slot 3 2)
    hw3 hp3 hs3 ht3 (.conjL hR) (.conjL (.conjR hR))
  exact of_eq (consCase_rename w C n t a (old 3)).symm
    (intro_cons (old 3 w) (old 3 C) (old 3 n) (old 3 t) (old 3 a) (slot 3 0) (slot 3 1) (slot 3 2)
      (.conjL (.conjR (.conjR hR))) hf (.conjR (.conjR (.conjR hR))))

theorem nil_trace_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n t a z e l d f g : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (trace w C n t a z e l d f g)) (hl : Derives Γ (empty l)) :
    Derives Γ (nilCase w n t a) := by
  have hn := StructuralListTraceInvert.zero_case hZ w z e l d f n (list_trace _ _ _ _ _ _ _ _ _ _ _ ht) hl
  have he := PacketVarintTraceBase.nil_value hZ w C n t a hw hn (intro_fold _ _ _ _ _ _ _ _ _ _ _ ht)
  exact .conjI hn (.conjI (tail_natural _ _ _ _ _ _ _ _ _ _ _ ht) he)

theorem trace_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n t a z e l d f g : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (trace w C n t a z e l d f g)) : Derives Γ (caseAt w C n t a) := by
  have hl := StructuralListTraceProperties.length_at _ _ _ _ _ _ _ (list_trace _ _ _ _ _ _ _ _ _ _ _ ht)
  have hd := OmegaStructureAlgebra.decomposition_at w l
    (OmegaStructureInduction.decomposition w (ZFContext.separation hZ OmegaStructureSyntax.splitMatrix) hw) hl
  apply Derives.disjE hd
  · exact .disjL (nil_trace_case (ZFContext.add hZ _) w C n t a z e l d f g (add hw _) (add ht _) (.hyp (Or.inl rfl)))
  · let P := OmegaStructureSyntax.predecessor w l
    let Q := (Formula.mem (Fin.last m) w.castSucc).conj (successor l.castSucc (Fin.last m))
    let Δ := Context.add Q (Context.image Formula.raise (Context.add P Γ))
    have hQ : Derives (Context.add P Γ) (.ex Q) := .hyp (Or.inl rfl)
    apply Derives.exE (p := Q) hQ
    have hZ1 := ZFContext.under (ZFContext.add hZ P) Q
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw P) Q)
    have ht1 := of_eq (trace_rename w C n t a z e l d f g Fin.castSucc) (under (add ht P) Q)
    have hP : Derives Δ Q := .hyp (Or.inl rfl)
    have hc := successor_case hZ1 w.castSucc C.castSucc n.castSucc t.castSucc a.castSucc z.castSucc e.castSucc l.castSucc d.castSucc f.castSucc g.castSucc (Fin.last m)
      hw1 (.conjL hP) (.conjR hP) ht1
    have hout : Derives Δ (caseAt w.castSucc C.castSucc n.castSucc t.castSucc a.castSucc) := .disjR hc
    simpa only [Formula.raise,caseAt_rename] using hout

theorem fold_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n t a : Fin m)
    (hw : Derives Γ (omega w)) (hf : Derives Γ (foldAt w C n t a)) : Derives Γ (caseAt w C n t a) := by
  let R := body w C n t a
  let Δ := Context.add R (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 R _ hf
  have hZ6 := HornBinderRules.zf_body 6 hZ R
  have hw6 := of_eq (omega_rename w (old 6)) (HornBinderRules.under_body 6 hw R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact of_eq (caseAt_rename w C n t a (old 6)).symm
    (trace_forward hZ6 (old 6 w) (old 6 C) (old 6 n) (old 6 t) (old 6 a)
      (slot 6 0) (slot 6 1) (slot 6 2) (slot 6 3) (slot 6 4) (slot 6 5) hw6 hR)

end PPAC.Migration.Internal.PacketVarintDecomposition
