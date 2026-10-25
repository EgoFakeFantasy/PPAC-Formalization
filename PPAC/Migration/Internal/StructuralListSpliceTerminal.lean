import PPAC.Migration.Internal.StructuralListSplicePushTransport

/-! The last real coupled Cons row is normalized using both full sequence functions, without chosen field or runtime witnesses. -/
namespace PPAC.Migration.Internal.StructuralListSpliceTerminal
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax StructuralListSpliceSyntax StructuralListSpliceTraceProperties StructuralListSpliceRecursionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem of_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a z e l d f g p : Fin m)
    (hs : Derives Γ (successor l p)) (ht : Derives Γ (trace w n t a z e l d f g))
    (hr : Derives Γ (StructuralListSpliceRowSyntax.row w f g p)) : Derives Γ (terminal w f g p n a) := by
  let R := StructuralListSpliceRowSyntax.rowBody w f g p
  let Δ := Context.add R (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 R _ hr
  have hZ6 := HornBinderRules.zf_body 6 hZ R
  have hs6 := of_eq (successor_rename l p (old 6)) (HornBinderRules.under_body 6 hs R)
  have ht6 := of_eq (trace_rename w n t a z e l d f g (old 6)) (HornBinderRules.under_body 6 ht R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hjl := OmegaUniversal.successor_unique _ _ _ (ZFContext.arithmetic hZ6).base.extensionality (.conjL hR) hs6
  have hy := StructuralListTraceOrder.edge_input_subst _ _ _ _ hjl (.conjL (.conjR (.conjR hR)))
  have hv := StructuralListTraceOrder.edge_input_subst _ _ _ _ hjl (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hR))))))
  have hyn := GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ6).base.extensionality
    (.conjL (StructuralListTraceProperties.sequence_at _ _ _ _ _ _ _ (list_trace _ _ _ _ _ _ _ _ _ _ ht6))) hy
    (StructuralListTraceProperties.last_at _ _ _ _ _ _ _ (list_trace _ _ _ _ _ _ _ _ _ _ ht6))
  have hva := GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ6).base.extensionality
    (.conjL (value_sequence _ _ _ _ _ _ _ _ _ _ ht6)) hv (last_edge _ _ _ _ _ _ _ _ _ _ ht6)
  have hc := cons_output (old 6 w) (slot 6 1) (slot 6 2) (slot 6 3) (old 6 n) hyn (.conjL (.conjR (.conjR (.conjR hR))))
  have ha := StructuralListSplicePushTransport.output (old 6 w) (slot 6 1) (slot 6 4) (slot 6 5) (old 6 a) hva
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hR))))))
  exact of_eq (terminal_rename w f g p n a (old 6)).symm
    (intro_terminal (old 6 w) (old 6 f) (old 6 g) (old 6 p) (old 6 n) (old 6 a) (slot 6 1) (slot 6 2) (slot 6 4)
      (.conjL (.conjR hR)) (.conjL (.conjR (.conjR (.conjR (.conjR hR))))) hc ha)

theorem terminal_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a z e l d f g p : Fin m)
    (hs : Derives Γ (successor l p)) (ht : Derives Γ (trace w n t a z e l d f g)) : Derives Γ (terminal w f g p n a) :=
  of_row hZ w n t a z e l d f g p hs ht
    (StructuralListSpliceRowSyntax.links_at _ _ _ _ _ (splice_links _ _ _ _ _ _ _ _ _ _ ht) (InsertLogic.new_member _ _ _ hs))

end PPAC.Migration.Internal.StructuralListSpliceTerminal
