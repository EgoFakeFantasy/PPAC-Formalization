import PPAC.Migration.Internal.StructuralNodeExistence

/-! 原节点的自然范围、非零性及两个分量的严格子码界。 -/
namespace PPAC.Migration.Internal.StructuralNodeProperties
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralNodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w tag payload n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (raw w tag payload n)) : Derives Γ (.mem n w) := by
  let R := rawWitness w tag payload n
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply eliminate_raw w tag payload n _ hn
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ R
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw R
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hqW := GodelPairCore.range hZ1 _ _ _ _ hw1 (.conjL hR)
  exact OmegaStructureAlgebra.successor_member _ _ _ (ZFContext.arithmetic hZ1).base.extensionality hw1 hqW (.conjR hR)

theorem positive {m} {Γ : Context m} (w tag payload n : Fin m) (hn : Derives Γ (raw w tag payload n)) : Derives Γ (empty n).neg := by
  let R := rawWitness w tag payload n
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply eliminate_raw w tag payload n _ hn
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hout := OmegaStructureAlgebra.successor_not_empty _ _ (.conjR hR)
  simpa only [Formula.raise, Formula.neg, Formula.rename, empty_rename] using hout

theorem components {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w tag payload n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem tag w)) (hp : Derives Γ (.mem payload w))
    (hn : Derives Γ (raw w tag payload n)) : Derives Γ ((Formula.mem tag n).conj (.mem payload n)) := by
  let R := rawWitness w tag payload n
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply eliminate_raw w tag payload n _ hn
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ R
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw R
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hb := GodelPairBounds.components hZ1 _ _ _ _ hw1 (under ht R) (under hp R) (.conjL hR)
  have htn := NaturalOrderBasic.below_successor _ _ _ (.conjR hR) (.conjL hb)
  have hpn := NaturalOrderBasic.below_successor _ _ _ (.conjR hR) (.conjR hb)
  exact .conjI htn hpn
end PPAC.Migration.Internal.StructuralNodeProperties
