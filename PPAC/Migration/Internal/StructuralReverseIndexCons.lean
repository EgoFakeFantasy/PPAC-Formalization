import PPAC.Migration.Internal.StructuralListReverseNil

/-! Advancing the original source field index advances the reversed list length by one, internally and without truncation. -/
namespace PPAC.Migration.Internal.StructuralReverseIndexCons
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralReverseIndexSyntax NaturalAdditionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem grow {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l L i j J : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (mirror w l i j))
    (hL : Derives Γ (successor L l)) (hJ : Derives Γ (successor J j)) : Derives Γ (mirror w L i J) := by
  let R := witness w.castSucc l.castSucc i.castSucc j.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (.conjR (.conjR hm))
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hi1 : Derives Δ (.mem i.castSucc w.castSucc) := under (.conjL hm) R
  have hj1 : Derives Δ (.mem j.castSucc w.castSucc) := under (.conjL (.conjR hm)) R
  have hL1 := of_eq (successor_rename L l Fin.castSucc) (under hL R)
  have hJ1 := of_eq (successor_rename J j Fin.castSucc) (under hJ R)
  have hl1 := OmegaStructureAlgebra.successor_member _ _ _ (ZFContext.arithmetic hZ1).base.extensionality hw1 (.conjL hR) (.conjR (.conjR hR))
  have hJN := OmegaStructureAlgebra.successor_member _ _ _ (ZFContext.arithmetic hZ1).base.extensionality hw1 hj1 hJ1
  have hs := ZFArithmetic.add_succ_backward hZ1 _ _ _ _ _ _ hw1 hi1 hj1 hJ1 (.conjL (.conjR hR)) (.conjR (.conjR hR))
  simpa only [Formula.raise,mirror_rename] using intro_mirror _ _ _ _ _ hi1 hJN (.conjI hl1 (.conjI hs hL1))

theorem last_zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l L z : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (.mem l w)) (hL : Derives Γ (successor L l))
    (hz : Derives Γ (empty z)) : Derives Γ (mirror w L l z) := by
  have hzN := OmegaStructureAlgebra.zero_member w z (ZFContext.arithmetic hZ).base.extensionality hw hz
  exact intro_mirror w L l z l hl hzN (.conjI hl (.conjI (ZFArithmetic.add_zero hZ w l z hw hl hz) hL))

end PPAC.Migration.Internal.StructuralReverseIndexCons
