import PPAC.Migration.Internal.PacketStructureTailChildren

/-! Actual tree and forest runs preserve the coupled tail property using only strictly smaller accepted children. -/
namespace PPAC.Migration.Internal.PacketStructureTailPoint
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketStructureAcceptedSyntax PacketStructureTailSyntax PacketStructureTailChildren
open NaturalAdditionBounds (below below_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem tree_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (hypothesis w n)) (ha : Derives Γ (tree w n t a)) : Derives Γ (below t a) := by
  let L := PacketStructureAcceptedSyntax.treeCaseBody w n t a
  let Δ := Context.add L (raisedContext 5 Γ)
  apply HornBinderRules.eliminate_many 5 L _ (PacketStructureRootLaws.tree_forward hZ w n t a hw ha)
  have hZ5 := HornBinderRules.zf_body 5 hZ L
  have hw5 := of_eq (omega_rename w (old 5)) (HornBinderRules.under_body 5 hw L)
  have hi5 := of_eq (hypothesis_rename w n (old 5)) (HornBinderRules.under_body 5 hi L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hf := Derives.conjL (.conjR hL)
  have h0 := Derives.conjL (.conjR (.conjR hL))
  have h1 := Derives.conjR (.conjR (.conjR hL))
  have hpn := raw_payload hZ5 (old 5 w) (slot 5 0) (slot 5 1) (old 5 n) (slot 5 2) (old 5 t) (slot 5 3) (slot 5 4) (old 5 a)
    hw5 (.conjL hL) hf h1
  have hpN := forest_natural hZ5 (old 5 w) (slot 5 1) (slot 5 2) (old 5 t) (slot 5 3) 0 hw5 hf
  have hP := ih_at (old 5 w) (old 5 n) (slot 5 1) hi5 hpN hpn
  have htu := forest_at (old 5 w) (slot 5 1) (slot 5 2) (old 5 t) (slot 5 3) (.conjR hP) hf
  have huv := PacketTokenBounds.tail_below hZ5 (old 5 w) (slot 5 2) (slot 5 3) (slot 5 4) hw5 h0
  have hva := PacketTokenBounds.tail_below hZ5 (old 5 w) (slot 5 0) (slot 5 4) (old 5 a) hw5 h1
  have hvN := token_natural hZ5 (old 5 w) (slot 5 2) (slot 5 3) (slot 5 4) 2 hw5 h0
  have haN := token_natural hZ5 (old 5 w) (slot 5 0) (slot 5 4) (old 5 a) 2 hw5 h1
  have htv := NaturalOrderBasic.transitive hZ5 (old 5 w) (old 5 t) (slot 5 3) (slot 5 4) hw5 hvN htu huv
  exact of_eq (below_rename t a (old 5)).symm (NaturalOrderBasic.transitive hZ5 (old 5 w) (old 5 t) (slot 5 4) (old 5 a) hw5 haN htv hva)

theorem forest_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n l t a : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (hypothesis w n)) (ha : Derives Γ (forest w n l t a)) : Derives Γ (below t a) := by
  apply Derives.disjE (PacketStructureRootLaws.forest_forward hZ w n l t a hw ha)
  · have hN : Derives (Context.add (PacketStructureRootSyntax.nilCase n l t a) Γ) (PacketStructureRootSyntax.nilCase n l t a) := .hyp (Or.inl rfl)
    exact .disjL (.conjR (.conjR hN))
  · let H := consCase w n l t a
    let L := PacketStructureAcceptedSyntax.consCaseBody w n l t a
    let Δ := Context.add L (raisedContext 4 (Context.add H Γ))
    apply HornBinderRules.eliminate_many 4 L _ (Derives.hyp (Γ := Context.add H Γ) (Or.inl rfl))
    have hZ4 := HornBinderRules.zf_body 4 (ZFContext.add hZ H) L
    have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 (add hw H) L)
    have hi4 := of_eq (hypothesis_rename w n (old 4)) (HornBinderRules.under_body 4 (add hi H) L)
    have hL : Derives Δ L := .hyp (Or.inl rfl)
    have hf := Derives.conjL (.conjR (.conjR hL))
    have ht := Derives.conjR (.conjR (.conjR hL))
    have hsub := cons_children hZ4 (old 4 w) (slot 4 0) (slot 4 1) (old 4 n) (slot 4 2) (old 4 t) (slot 4 3) (old 4 a) hw4 (.conjL hL) hf ht
    have hhN := tree_natural hZ4 (old 4 w) (slot 4 0) (slot 4 3) (old 4 a) 0 hw4 ht
    have hqN := forest_natural hZ4 (old 4 w) (slot 4 1) (slot 4 2) (old 4 t) (slot 4 3) 0 hw4 hf
    have hPh := ih_at (old 4 w) (old 4 n) (slot 4 0) hi4 hhN (.conjL hsub)
    have hPq := ih_at (old 4 w) (old 4 n) (slot 4 1) hi4 hqN (.conjR hsub)
    have htu := forest_at (old 4 w) (slot 4 1) (slot 4 2) (old 4 t) (slot 4 3) (.conjR hPq) hf
    have hua := tree_at (old 4 w) (slot 4 0) (slot 4 3) (old 4 a) (.conjL hPh) ht
    have haN := tree_natural hZ4 (old 4 w) (slot 4 0) (slot 4 3) (old 4 a) 2 hw4 ht
    exact of_eq (below_rename t a (old 4)).symm (NaturalOrderBasic.transitive hZ4 (old 4 w) (old 4 t) (slot 4 3) (old 4 a) hw4 haN htu hua)

end PPAC.Migration.Internal.PacketStructureTailPoint
