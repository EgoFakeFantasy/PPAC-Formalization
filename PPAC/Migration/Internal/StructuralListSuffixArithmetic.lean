import PPAC.Migration.Internal.StructuralListSuffixSyntax

/-! 后缀编码的内部前驱成员界与源偏移加法后继转换。 -/
namespace PPAC.Migration.Internal.StructuralListSuffixArithmetic
open Source SourceAlgebra SourceLogic OmegaSyntax NaturalAdditionSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem iff_trans {m} {Γ : Context m} {p q r : Formula m} (hp : Derives Γ (p.iff q)) (hq : Derives Γ (q.iff r)) : Derives Γ (p.iff r) := by
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjL hq) _) (.impE (add (.conjL hp) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR hp) _) (.impE (add (.conjR hq) _) (.hyp (Or.inl rfl)))

theorem predecessor_inside {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r s p i : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (successor s r))
    (hi : Derives Γ (successor i p)) (hm : Derives Γ (.mem i s)) : Derives Γ (.mem p r) := by
  have hpi := InsertLogic.new_member i p p hi
  have ht := OmegaStructureAlgebra.element_transitive_at w r
    (OmegaStructureInduction.elements_transitive w (ZFContext.separation hZ OmegaStructureSyntax.transitiveMatrix) hw) hr
  have hb := NaturalOrderBasic.member_successor i r s hs hm
  apply Derives.disjE hb
  · exact UnorderedPairLogic.mem_container_subst i r p (.hyp (Or.inl rfl)) (add hpi _)
  · have hsub := Derives.impE (OmegaStructureSyntax.transitive_at r i (add ht _)) (.hyp (Or.inl rfl))
    exact .impE (RestrictionSyntax.subset_at i r p hsub) (add hpi _)

theorem offset_successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w k j p i q : Fin m)
    (hw : Derives Γ (omega w)) (hk : Derives Γ (.mem k w)) (hp : Derives Γ (.mem p w))
    (hj : Derives Γ (successor j k)) (hi : Derives Γ (successor i p)) (hs : Derives Γ (sum w k i q)) : Derives Γ (sum w j p q) := by
  have hiW := OmegaStructureAlgebra.successor_member w i p (ZFContext.arithmetic hZ).base.extensionality hw hp hi
  have hjW := OmegaStructureAlgebra.successor_member w j k (ZFContext.arithmetic hZ).base.extensionality hw hk hj
  have his := ZFArithmetic.add_commute hZ w k i q hw hk hiW hs
  have hsp := StructuralListPositionArithmetic.swap_successors hZ w p i k j q hw hp hk hi hj his
  exact ZFArithmetic.add_commute hZ w p j q hw hp hjW hsp
end PPAC.Migration.Internal.StructuralListSuffixArithmetic
