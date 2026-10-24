import PPAC.Migration.Internal.PairingProjectionBounds
import PPAC.Migration.Internal.RawCodeProjection

/-! 任意自然原始外壳的head／tail实际数值不超过输入；不限制为规范Cons。 -/
namespace PPAC.Migration.Internal.RawCodeProjectionBounds
open Source SourceAlgebra SourceLogic OmegaSyntax
open NaturalAdditionBounds (below below_rename)
open PairingProjectionBounds (of_eq)

theorem step_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (head : Bool) (w x y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.mem x w)) (hy : Derives Γ (RawCodeProjectionSyntax.step head w x y)) :
    Derives Γ (below y x) := by
  let B := RawCodeProjectionSyntax.body head w.castSucc x.castSucc y.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hy
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hp := PairingProjection.range_point hZ1 true false _ _ _ hw1 (.conjL hB)
  have hpx := PairingProjectionBounds.step_bound hZ1 true false _ _ _ hw1 (under hx B) (.conjL hB)
  have hyp := PairingProjectionBounds.step_bound hZ1 false head _ _ _ hw1 hp (.conjR hB)
  have ho := NaturalOrderBasic.transitive hZ1 _ _ _ _ hw1 (under hx B) hyp hpx
  exact of_eq (below_rename y x Fin.castSucc).symm ho

end PPAC.Migration.Internal.RawCodeProjectionBounds
