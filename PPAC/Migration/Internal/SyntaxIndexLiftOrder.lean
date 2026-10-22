import PPAC.Migration.Internal.RelationGraph

/-! 量词提升所需全内部零/后继成员界；使用原自然序数与传递性推导。 -/
namespace PPAC.Migration.Internal.SyntaxIndexLiftOrder
open Source SourceAlgebra SourceLogic OmegaSyntax OmegaStructureSyntax RestrictionSyntax

theorem zero_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a u z : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hu : Derives Γ (successor u a))
    (hz : Derives Γ (empty z)) : Derives Γ (.mem z u) := by
  have ho := NaturalOrderBasic.ordinal hZ w a hw ha
  have hs := OmegaElementary.empty_subset z a hz
  have ht := OrdinalTransitivity.from_canonical z (OmegaElementary.empty_transitive z hz)
  have hb := OrdinalInitialSegment.initial_segment a z (ZFContext.arithmetic hZ).base.extensionality
    (ZFContext.arithmetic hZ).base.foundation (ZFContext.separation hZ OrdinalDifference.outsideMatrix) ho ht hs
  exact NaturalOrderBasic.below_successor z a u hu hb

theorem successor_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b u v : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hab : Derives Γ (.mem a b)) (hu : Derives Γ (successor u a)) (hv : Derives Γ (successor v b)) :
    Derives Γ (.mem u v) := by
  have hoB := NaturalOrderBasic.ordinal hZ w b hw hb
  have hoU := NaturalOrderBasic.ordinal hZ w u hw
    (OmegaStructureAlgebra.successor_member w u a (ZFContext.arithmetic hZ).base.extensionality hw ha hu)
  have hs := OrdinalTransitivity.subset_of_member b a (.conjL hoB) hab
  have hsU := OmegaElementary.successor_subset u a b hu hab hs
  have hle := OrdinalInitialSegment.initial_segment b u (ZFContext.arithmetic hZ).base.extensionality
    (ZFContext.arithmetic hZ).base.foundation (ZFContext.separation hZ OrdinalDifference.outsideMatrix)
    hoB (.conjL hoU) hsU
  exact NaturalOrderBasic.below_successor u b v hv hle

theorem predecessor_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a u i k : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hu : Derives Γ (successor u a))
    (hi : Derives Γ (.mem i u)) (hk : Derives Γ (successor i k)) : Derives Γ (.mem k a) := by
  have hki := InsertLogic.new_member i k k hk
  have ho := NaturalOrderBasic.ordinal hZ w a hw ha
  apply Derives.disjE (InsertLogic.member_cases u a a i hu hi)
  · exact .impE (.impE (add (OrdinalSyntax.transitiveSet_at a i k (.conjL ho)) _) (.hyp (Or.inl rfl))) (add hki _)
  · exact UnorderedPairLogic.mem_container_subst i a k (.hyp (Or.inl rfl)) (add hki _)

theorem successor_injective {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w i k l : Fin m)
    (hw : Derives Γ (omega w)) (hk : Derives Γ (.mem k w))
    (hi : Derives Γ (successor i k)) (hj : Derives Γ (successor i l)) : Derives Γ (.equal k l) := by
  have ho := NaturalOrderBasic.ordinal hZ w k hw hk
  have ht := OrdinalTransitivity.to_canonical k (.conjL ho)
  exact OmegaStructureAlgebra.successor_injective i k l ht (NaturalOrderBasic.nonself hZ k) hi hj
end PPAC.Migration.Internal.SyntaxIndexLiftOrder
