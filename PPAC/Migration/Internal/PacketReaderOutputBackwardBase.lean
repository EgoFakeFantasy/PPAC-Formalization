import PPAC.Migration.Internal.PacketReaderOutputCons

/-! Actual reverse uniqueness normalizes the output relation at any genuine reverse witness; an actual Nil accumulator has the exact all-candidate identity fiber. -/
namespace PPAC.Migration.Internal.PacketReaderOutputBackwardBase
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderOutputOrder
open SyntaxRenameQuerySyntax (of_eq)

theorem accumulator_valid {m} {Γ : Context m} (w A T O : Fin m)
    (hOut : Derives Γ (output w A T O)) : Derives Γ (StructuralListTraceSyntax.valid w A) := by
  let R := (StructuralListReverseSyntax.reverses w.castSucc A.castSucc (Fin.last m)).conj
    (StructuralListSpliceSyntax.splice w.castSucc (Fin.last m) T.castSucc O.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hOut
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise,StructuralListTraceSyntax.valid_rename] using
    StructuralListReverseUnique.valid_input _ _ _ (.conjL hR)

theorem at_reverse {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w A T O R : Fin m)
    (hw : Derives Γ (omega w)) (hRev : Derives Γ (StructuralListReverseSyntax.reverses w A R)) :
    Derives Γ ((output w A T O).iff (StructuralListSpliceSyntax.splice w R T O)) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := output w A T O
    let P := (StructuralListReverseSyntax.reverses w.castSucc A.castSucc (Fin.last m)).conj
      (StructuralListSpliceSyntax.splice w.castSucc (Fin.last m) T.castSucc O.castSucc)
    let Δ := Context.add P (Context.image Formula.raise (Context.add H Γ))
    apply Derives.exE (p := P) (.hyp (Or.inl rfl))
    have hP : Derives Δ P := .hyp (Or.inl rfl)
    have hZ1 := ZFContext.under (ZFContext.add hZ H) P
    have hw1 := of_eq (omega_rename w Fin.castSucc) (under (add hw H) P)
    have hRev1 := of_eq (StructuralListReverseSyntax.reverses_rename w A R Fin.castSucc) (under (add hRev H) P)
    have he := StructuralListReverseUnique.unique hZ1 w.castSucc A.castSucc (Fin.last m) R.castSucc hw1 (.conjL hP) hRev1
    simpa only [Formula.raise,StructuralListSpliceSyntax.splice_rename] using
      StructuralListSpliceAlgebraTransport.prefix_subst w.castSucc (Fin.last m) T.castSucc O.castSucc R.castSucc he (.conjR hP)
  · apply Derives.impI
    exact intro_output w A T O R (add hRev _) (.hyp (Or.inl rfl))

theorem nil_accumulator {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w e T O : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (StructuralListSyntax.nilCode w e)) :
    Derives Γ ((output w e T O).iff ((StructuralListTraceSyntax.valid w T).conj (.equal T O))) := by
  have hRev := StructuralListReverseNil.nil_pair hZ w e e hw he he
  have hNorm := at_reverse hZ w e T O e hw hRev
  exact StructuralListSuffixArithmetic.iff_trans hNorm (StructuralListSplice.nil_iff hZ w e T O hw he)

end PPAC.Migration.Internal.PacketReaderOutputBackwardBase
