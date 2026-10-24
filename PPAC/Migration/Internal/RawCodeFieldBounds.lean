import PPAC.Migration.Internal.RawCodeGetBounds
import PPAC.Migration.Internal.RawCodeField

/-! field在全部自然输入和内部自然索引上的实际值界；不要求合法证明／规范节点输入。 -/
namespace PPAC.Migration.Internal.RawCodeFieldBounds
open Source SourceAlgebra SourceLogic OmegaSyntax
open NaturalAdditionBounds (below below_rename)
open PairingProjectionBounds (of_eq)

theorem bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w x i y : Fin m)
    (hw : Derives Γ (omega w)) (hx : Derives Γ (.mem x w)) (hi : Derives Γ (.mem i w))
    (hy : Derives Γ (RawCodeFieldSyntax.field w x i y)) : Derives Γ (below y x) := by
  let B := RawCodeFieldSyntax.body w.castSucc x.castSucc i.castSucc y.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hy
  have hZ1 := ZFContext.under hZ B
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hp := PairingProjection.range_point hZ1 true false _ _ _ hw1 (.conjL hB)
  have hpx := PairingProjectionBounds.step_bound hZ1 true false _ _ _ hw1 (under hx B) (.conjL hB)
  have hyp := RawCodeGetBounds.bound hZ1 _ _ _ _ hw1 hp (under hi B) (.conjR hB)
  have ho := NaturalOrderBasic.transitive hZ1 _ _ _ _ hw1 (under hx B) hyp hpx
  exact of_eq (below_rename y x Fin.castSucc).symm ho

end PPAC.Migration.Internal.RawCodeFieldBounds
