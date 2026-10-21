import PPAC.Migration.Internal.StructuralListEncodeExistence

/-! 实际逆编码所得码有效，任意实际解码恢复原长度和原字段图；码唯一性仍待证明。 -/
namespace PPAC.Migration.Internal.StructuralListEncodeReadback
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListLengthSyntax StructuralListFieldGraphSyntax StructuralListEncodeSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem encoding_valid {m} {Γ : Context m} (w f l n : Fin m) (he : Derives Γ (encoding w f l n)) :
    Derives Γ (StructuralListTraceSyntax.valid w n) := StructuralListLengthBasic.valid_of_length w n l (.conjR (.conjL he))

theorem decode_after_encode {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f l n k g : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (encoding w f l n))
    (hk : Derives Γ (hasLength w n k)) (hg : Derives Γ (fields w n k g)) : Derives Γ ((Formula.equal k l).conj (.equal g f)) :=
  StructuralListFieldDecode.unique_pair hZ w n k l g f hw hk (.conjR (.conjL he)) hg (.conjR he)
end PPAC.Migration.Internal.StructuralListEncodeReadback
