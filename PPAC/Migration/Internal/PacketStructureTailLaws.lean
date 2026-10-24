import PPAC.Migration.Internal.PacketStructureTailLawSyntax

/-! Only omega remains in both all-internal actual tail laws. -/
namespace PPAC.Migration.Internal.PacketStructureTailLaws
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketStructureAcceptedSyntax PacketStructureTailLawSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem all_tree {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (allTree w) := by
  apply OriginalUniversalBlock.intro_many 3
  apply Derives.impI
  let H := tree (old 3 w : Fin (m+3)) (slot 3 0) (slot 3 1) (slot 3 2)
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw H)
  exact PacketStructureTailBounds.tree_tail (HornBinderRules.zf_body 3 hZ H) (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2) hw3 (.hyp (Or.inl rfl))

theorem all_forest {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (allForest w) := by
  apply OriginalUniversalBlock.intro_many 4
  apply Derives.impI
  let H := forest (old 4 w : Fin (m+4)) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw H)
  exact PacketStructureTailBounds.forest_tail (HornBinderRules.zf_body 4 hZ H) (old 4 w) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hw4 (.hyp (Or.inl rfl))

theorem all_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (allLaw w) :=
  .conjI (all_tree hZ w hw) (all_forest hZ w hw)

end PPAC.Migration.Internal.PacketStructureTailLaws
