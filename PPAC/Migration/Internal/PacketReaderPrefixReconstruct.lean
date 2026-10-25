import PPAC.Migration.Internal.ObjectPacketTokensByteInput

/-! Actual canonical-Cons reconstruction, strict suffix-code descent and source guards are preserved by the continuation prefix step. -/
namespace PPAC.Migration.Internal.PacketReaderPrefixReconstruct
open Source SourceAlgebra SourceLogic OmegaSyntax

theorem canonical_cons {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d k n b Q C : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hAff : Derives Γ (PacketAffineSyntax.affine w B d k n)) (hk : Derives Γ (empty k).neg)
    (hSum : Derives Γ (NaturalAdditionSyntax.sum w B d b))
    (hQ : Derives Γ (PacketVarintSyntax.canonical w k Q)) (hC : Derives Γ (StructuralListSyntax.consCode w b Q C)) :
    Derives Γ (PacketVarintSyntax.canonical w n C) := by
  have hBN := SyntaxNumerals.range hZ 128 w B hw hB
  have hd := PacketAffineCore.digit_natural hZ w B d k n hw hAff
  have hCom := ZFArithmetic.add_commute hZ w B d b hw hBN hd hSum
  have hLarge := PacketVarintCanonicalRecursionSyntax.intro_large true w B n C d k b Q hAff hk hCom hQ hC
  have hAt := Derives.impE (.conjR (PacketVarintCanonicalRecursionBridge.at_actual_iff hZ w B n C hw hB)) (.disjR hLarge)
  exact PacketVarintSyntax.intro_actual w B n C hB hAt

theorem suffix_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w L X T : Fin m)
    (hw : Derives Γ (omega w)) (hL : Derives Γ (.mem L w))
    (hXL : Derives Γ (.mem X L)) (hTX : Derives Γ (.mem T X)) : Derives Γ (.mem T L) := by
  have hTrans := OrdinalSyntax.transitiveSet_at L X T (.conjL (NaturalOrderBasic.ordinal hZ w L hw hL))
  exact .impE (.impE hTrans hXL) hTX

theorem nonzero_guard {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d k n o s : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hAff : Derives Γ (PacketAffineSyntax.affine w B d k n)) (hk : Derives Γ (empty k).neg) :
    Derives Γ (PacketReaderVarintSegmentSyntax.guard o n s) := by
  have hKN := Derives.impE (.conjR (PacketDivisionDescentCore.quotient_bounds hZ false w B d k n hw hB hAff)) hk
  apply Derives.disjR
  apply Derives.impI
  exact .impE (empty_at n k (.hyp (Or.inl rfl))) (add hKN _)

theorem splice_cons {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b Q C X T L : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w))
    (hC : Derives Γ (StructuralListSyntax.consCode w b Q C))
    (hSp : Derives Γ (StructuralListSpliceSyntax.splice w Q T X))
    (hL : Derives Γ (StructuralListSyntax.consCode w b X L)) : Derives Γ (StructuralListSpliceSyntax.splice w C T L) :=
  StructuralListSplice.cons_backward hZ w b Q C T L hw hb hC
    (StructuralListSplice.intro_remaining w b Q T L X hSp hL)

end PPAC.Migration.Internal.PacketReaderPrefixReconstruct
