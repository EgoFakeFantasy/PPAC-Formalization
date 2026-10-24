import PPAC.Migration.Internal.PacketBytesRecursionSyntax

/-! The last real byte row is normalized using both full sequence functions, without chosen field or runtime witnesses. -/
namespace PPAC.Migration.Internal.PacketBytesTerminal
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax PacketBytesTraceSyntax PacketBytesTraceProperties PacketBytesRecursionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem of_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n t a z e l d f g p : Fin m)
    (hs : Derives Γ (successor l p)) (ht : Derives Γ (trace w C n t a z e l d f g))
    (hr : Derives Γ (PacketBytesRowSyntax.row w C f g p)) : Derives Γ (terminal w C f g p n a) := by
  let R := PacketBytesRowSyntax.rowBody w C f g p
  let Δ := Context.add R (raisedContext 6 Γ)
  apply HornBinderRules.eliminate_many 6 R _ hr
  have hZ6 := HornBinderRules.zf_body 6 hZ R
  have hs6 := of_eq (successor_rename l p (old 6)) (HornBinderRules.under_body 6 hs R)
  have ht6 := of_eq (trace_rename w C n t a z e l d f g (old 6)) (HornBinderRules.under_body 6 ht R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hjl := OmegaUniversal.successor_unique _ _ _ (ZFContext.arithmetic hZ6).base.extensionality (.conjL hR) hs6
  have hy := StructuralListTraceOrder.edge_input_subst _ _ _ _ hjl (.conjL (.conjR (.conjR hR)))
  have hv := StructuralListTraceOrder.edge_input_subst _ _ _ _ hjl (.conjL (.conjR (.conjR (.conjR (.conjR (.conjR hR))))))
  have hyn := GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ6).base.extensionality
    (.conjL (StructuralListTraceProperties.sequence_at _ _ _ _ _ _ _ (list_trace _ _ _ _ _ _ _ _ _ _ _ ht6))) hy
    (StructuralListTraceProperties.last_at _ _ _ _ _ _ _ (list_trace _ _ _ _ _ _ _ _ _ _ _ ht6))
  have hva := GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ6).base.extensionality
    (.conjL (value_sequence _ _ _ _ _ _ _ _ _ _ _ ht6)) hv (last_edge _ _ _ _ _ _ _ _ _ _ _ ht6)
  have hc := cons_output (old 6 w) (slot 6 1) (slot 6 2) (slot 6 3) (old 6 n) hyn (.conjL (.conjR (.conjR (.conjR hR))))
  have ha := PacketAffineTransport.output (old 6 w) (old 6 C) (slot 6 1) (slot 6 4) (slot 6 5) (old 6 a) hva
    (.conjR (.conjR (.conjR (.conjR (.conjR (.conjR hR))))))
  exact of_eq (terminal_rename w C f g p n a (old 6)).symm
    (intro_terminal (old 6 w) (old 6 C) (old 6 f) (old 6 g) (old 6 p) (old 6 n) (old 6 a) (slot 6 1) (slot 6 2) (slot 6 4)
      (.conjL (.conjR hR)) (.conjL (.conjR (.conjR (.conjR (.conjR hR))))) hc ha)

theorem terminal_row {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w C n t a z e l d f g p : Fin m)
    (hs : Derives Γ (successor l p)) (ht : Derives Γ (trace w C n t a z e l d f g)) : Derives Γ (terminal w C f g p n a) :=
  of_row hZ w C n t a z e l d f g p hs ht
    (PacketBytesRowSyntax.links_at _ _ _ _ _ _ (byte_links _ _ _ _ _ _ _ _ _ _ _ ht) (InsertLogic.new_member _ _ _ hs))

end PPAC.Migration.Internal.PacketBytesTerminal
