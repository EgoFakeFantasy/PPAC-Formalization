import PPAC.Migration.Internal.PacketReaderHistoryAgreementSyntax

/-! Both real adjacent-row witness blocks are eliminated before applying the coded transition functionality. -/
namespace PPAC.Migration.Internal.PacketReaderHistoryAgreementRows
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax HornBinderSyntax PacketReaderHistorySyntax PacketReaderHistoryAgreementSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem outputs_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B z o f g d e i j a b : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w))
    (hf : Derives Γ (SequenceSyntax.sequence f d w)) (hg : Derives Γ (SequenceSyntax.sequence g e w))
    (hi : Derives Γ (agree f g i)) (hs : Derives Γ (successor j i))
    (hr : Derives Γ (row w B z o f i)) (ht : Derives Γ (row w B z o g i))
    (ha : Derives Γ (edge f j a)) (hb : Derives Γ (edge g j b)) : Derives Γ (.equal a b) := by
  let R := rowBody w B z o f i
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hr
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hB3 : Derives Δ (.mem (old 3 B) (old 3 w)) := HornBinderRules.under_body 3 hB R
  have hf3 := of_eq (SequenceSyntax.sequence_rename f d w (old 3)) (HornBinderRules.under_body 3 hf R)
  have hg3 := of_eq (SequenceSyntax.sequence_rename g e w (old 3)) (HornBinderRules.under_body 3 hg R)
  have hi3 := of_eq (agree_rename f g i (old 3)) (HornBinderRules.under_body 3 hi R)
  have hs3 := of_eq (successor_rename j i (old 3)) (HornBinderRules.under_body 3 hs R)
  have ht3 := of_eq (row_rename w B z o g i (old 3)) (HornBinderRules.under_body 3 ht R)
  have ha3 := of_eq (edge_rename f j a (old 3)) (HornBinderRules.under_body 3 ha R)
  have hb3 := of_eq (edge_rename g j b (old 3)) (HornBinderRules.under_body 3 hb R)
  let T := rowBody (old 3 w) (old 3 B) (old 3 z) (old 3 o) (old 3 g) (old 3 i)
  let Ξ := Context.add T (raisedContext 3 Δ)
  apply HornBinderRules.eliminate_many 3 T _ ht3
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hZ6 := HornBinderRules.zf_body 3 hZ3 T
  have hw6 := of_eq (omega_rename (old 3 w) (old 3)) (HornBinderRules.under_body 3 hw3 T)
  have hB6 : Derives Ξ (.mem (old 3 (old 3 B)) (old 3 (old 3 w))) := HornBinderRules.under_body 3 hB3 T
  have hf6 := of_eq (SequenceSyntax.sequence_rename (old 3 f) (old 3 d) (old 3 w) (old 3)) (HornBinderRules.under_body 3 hf3 T)
  have hg6 := of_eq (SequenceSyntax.sequence_rename (old 3 g) (old 3 e) (old 3 w) (old 3)) (HornBinderRules.under_body 3 hg3 T)
  have hi6 := of_eq (agree_rename (old 3 f) (old 3 g) (old 3 i) (old 3)) (HornBinderRules.under_body 3 hi3 T)
  have hs6 := of_eq (successor_rename (old 3 j) (old 3 i) (old 3)) (HornBinderRules.under_body 3 hs3 T)
  have ha6 := of_eq (edge_rename (old 3 f) (old 3 j) (old 3 a) (old 3)) (HornBinderRules.under_body 3 ha3 T)
  have hb6 := of_eq (edge_rename (old 3 g) (old 3 j) (old 3 b) (old 3)) (HornBinderRules.under_body 3 hb3 T)
  have hR6 := of_eq (rowAt_rename (old 3 w) (old 3 B) (old 3 z) (old 3 o) (old 3 f) (old 3 i) (slot 3 0) (slot 3 1) (slot 3 2) (old 3)) (HornBinderRules.under_body 3 hR T)
  have heF := OmegaUniversal.successor_unique _ _ _ (ZFContext.arithmetic hZ6).base.extensionality (.conjL hR6) hs6
  have heG := OmegaUniversal.successor_unique _ _ _ (ZFContext.arithmetic hZ6).base.extensionality (.conjL hT) hs6
  have hfedge := StructuralListTraceOrder.edge_input_subst _ _ _ _ heF (.conjL (.conjR (.conjR hR6)))
  have hgedge := StructuralListTraceOrder.edge_input_subst _ _ _ _ heG (.conjL (.conjR (.conjR hT)))
  have heA := GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ6).base.extensionality (.conjL hf6) hfedge ha6
  have heB := GraphProperties.single_valued _ _ _ _ _ (ZFContext.arithmetic hZ6).base.extensionality (.conjL hg6) hgedge hb6
  have heN := at_values _ _ _ _ _ hi6 (.conjL (.conjR hR6)) (.conjL (.conjR hT))
  have hstep := step_source_subst _ _ _ _ _ _ _ (eq_symm heN) (.conjR (.conjR (.conjR hT)))
  have heO := PacketReaderCodedUnique.unique hZ6 _ _ _ _ _ _ _ hw6 hB6 (.conjR (.conjR (.conjR hR6))) hstep
  exact eq_trans (eq_trans (eq_symm heA) heO) heB

end PPAC.Migration.Internal.PacketReaderHistoryAgreementRows
