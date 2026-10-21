import PPAC.Migration.Internal.StructuralListDecodeSyntax

/-! 内部长度零/后继分解和实际前缀给有效码的反向Nil/Cons分解。 -/
namespace PPAC.Migration.Internal.StructuralListTraceInvert
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax SequenceSyntax StructuralListSyntax StructuralListTraceSyntax StructuralListDecodeSyntax StructuralListTraceOrder
open StructuralListTraceProperties
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem zero_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e l d f n : Fin m)
    (ht : Derives Γ (trace w z e l d f n)) (hl : Derives Γ (empty l)) : Derives Γ (nilCode w n) := by
  have hzl := OmegaUniversal.empty_unique z l (ZFContext.arithmetic hZ).base.extensionality (zero_at _ _ _ _ _ _ _ ht) hl
  have hedge := edge_input_subst f z l e hzl (seed_at _ _ _ _ _ _ _ ht)
  have hen := GraphProperties.single_valued f d l e n (ZFContext.arithmetic hZ).base.extensionality
    (.conjL (sequence_at _ _ _ _ _ _ _ ht)) hedge (last_at _ _ _ _ _ _ _ ht)
  exact nil_output_subst w e n hen (nil_at _ _ _ _ _ _ _ ht)

theorem successor_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e l d f n p : Fin m)
    (hw : Derives Γ (omega w)) (hp : Derives Γ (.mem p w)) (hs : Derives Γ (successor l p))
    (ht : Derives Γ (trace w z e l d f n)) : Derives Γ (decomposition w n) := by
  have hr := StructuralListTraceSyntax.links_at w l f p (links_at_trace _ _ _ _ _ _ _ ht) (InsertLogic.new_member l p p hs)
  let R := rowWitness w f p
  let Δ := Context.add R (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))
  apply eliminate_row w f p _ hr
  have hZ3 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.rename (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) Fin.castSucc) R
  have lift {q : Formula m} (hq : Derives Γ q) : Derives Δ q.raise.raise.raise := GraphInsertElimination.under_three hq R
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hs3 : Derives Δ (successor l.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using lift hs
  have ht3 : Derives Δ (trace w.castSucc.castSucc.castSucc z.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc l.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc f.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := by
    simpa only [Formula.raise, trace_rename] using lift ht
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hjl := OmegaUniversal.successor_unique _ _ _ (ZFContext.arithmetic hZ3).base.extensionality (.conjL hR) hs3
  have hedge := edge_input_subst _ _ _ _ hjl (.conjL (.conjR (.conjR hR)))
  have hbn := GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ3).base.extensionality
    (.conjL (sequence_at _ _ _ _ _ _ _ ht3)) hedge (last_at _ _ _ _ _ _ _ ht3)
  have hstep := step_output_subst _ _ _ _ hbn (.conjR (.conjR (.conjR hR)))
  have htail := StructuralListTracePrefix.valid_prefix hZ3 _ _ _ _ _ _ _ _ _ hw3 (lift hp) hs3 ht3 (.conjL (.conjR hR))
  have hout : Derives Δ (decomposition w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) := .disjR (intro_tail _ _ _ htail hstep)
  simpa only [Formula.raise, decomposition_rename] using hout

theorem trace_decomposition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e l d f n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (trace w z e l d f n)) : Derives Γ (decomposition w n) := by
  have hlW := length_at _ _ _ _ _ _ _ ht
  have hd := OmegaStructureAlgebra.decomposition_at w l
    (OmegaStructureInduction.decomposition w (ZFContext.separation hZ OmegaStructureSyntax.splitMatrix) hw) hlW
  apply Derives.disjE hd
  · exact .disjL (zero_case (ZFContext.add hZ _) _ _ _ _ _ _ _ (add ht _) (.hyp (Or.inl rfl)))
  · let P := OmegaStructureSyntax.predecessor w l
    let Γp := Context.add P Γ
    let Q := (Formula.mem (Fin.last m) w.castSucc).conj (successor l.castSucc (Fin.last m))
    let Δ := Context.add Q (Context.image Formula.raise Γp)
    have hq : Derives Γp (.ex Q) := .hyp (Or.inl rfl)
    apply Derives.exE (p := Q) hq
    have hZ1 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.add hZ P) Q
    have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under (add hw P) Q
    have ht1 : Derives Δ (trace w.castSucc z.castSucc e.castSucc l.castSucc d.castSucc f.castSucc n.castSucc) := by simpa only [Formula.raise, trace_rename] using under (add ht P) Q
    have hQ : Derives Δ Q := .hyp (Or.inl rfl)
    have hout := successor_case hZ1 _ _ _ _ _ _ _ _ hw1 (.conjL hQ) (.conjR hQ) ht1
    simpa only [Formula.raise, decomposition_rename] using hout

theorem valid_decomposition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (valid w n)) : Derives Γ (decomposition w n) := by
  let V := validBody w n
  let Δ := Context.add V (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ)))))
  apply eliminate_valid w n _ hn
  have hZ5 : ZFContext.Evidence Δ := zf_under_five hZ V
  have hw5 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under_five hw V
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have hout := trace_decomposition hZ5 _ _ _ _ _ _ _ hw5 hV
  simpa only [Formula.raise, decomposition_rename] using hout
end PPAC.Migration.Internal.StructuralListTraceInvert
