import PPAC.Migration.Internal.PairingProjectionNatural
import PPAC.Migration.Internal.GodelPairBounds

/-! 原裸配数／原始外壳的数值投影不超过自然输入码，包括实际补零分支。 -/
namespace PPAC.Migration.Internal.PairingProjectionBounds
open Source SourceAlgebra SourceLogic OmegaSyntax PairingProjectionSyntax
open NaturalAdditionBounds (below below_rename)
theorem of_eq {m} {Γ : Context m} {p q : Formula m} (he : p = q) (hp : Derives Γ p) : Derives Γ q := he ▸ hp


theorem selected_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (raw head : Bool) (w x y : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (selected raw head w x y)) : Derives Γ (below y x) := by
  let B := body raw head w.castSucc x.castSucc y.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hy
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have ho : Derives Δ (below y.castSucc x.castSucc) := by
    cases raw <;> cases head
    · exact .conjR (GodelPairBounds.components hZ1 _ _ _ _ hw1 (.conjR (.conjL hB)) (.conjL (.conjL hB)) (.conjR hB))
    · exact .conjL (GodelPairBounds.components hZ1 _ _ _ _ hw1 (.conjL (.conjL hB)) (.conjR (.conjL hB)) (.conjR hB))
    · exact .disjR (.conjR (StructuralNodeProperties.components hZ1 _ _ _ _ hw1 (.conjR (.conjL hB)) (.conjL (.conjL hB)) (.conjR hB)))
    · exact .disjR (.conjL (StructuralNodeProperties.components hZ1 _ _ _ _ hw1 (.conjL (.conjL hB)) (.conjR (.conjL hB)) (.conjR hB)))
  exact of_eq (below_rename y x Fin.castSucc).symm ho

theorem step_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (raw head : Bool) (w x y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.mem x w)) (hy : Derives Γ (step raw head w x y)) : Derives Γ (below y x) := by
  apply Derives.disjE hy
  · exact selected_bound (ZFContext.add hZ _) raw head w x y (add hw _) (.hyp (Or.inl rfl))
  · exact GodelUnpairArithmetic.zero_below (ZFContext.add hZ _) w y x (add hw _)
      (.conjR (.hyp (Or.inl rfl))) (add hx _)

end PPAC.Migration.Internal.PairingProjectionBounds
