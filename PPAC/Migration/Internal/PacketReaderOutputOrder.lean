import PPAC.Migration.Internal.StructuralListSpliceSnoc
import PPAC.Migration.Internal.StructuralListSpliceAlgebra

/-! Exact reader output order is the actual reverse of the old accumulator followed by the actual token list. -/
namespace PPAC.Migration.Internal.PacketReaderOutputOrder
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)

def output {m} (w A T O : Fin m) : Formula m := .ex
  ((StructuralListReverseSyntax.reverses w.castSucc A.castSucc (Fin.last m)).conj (StructuralListSpliceSyntax.splice w.castSucc (Fin.last m) T.castSucc O.castSucc))

theorem output_rename {m k} (w A T O : Fin m) (ρ : Fin m → Fin k) :
    (output w A T O).rename ρ = output (ρ w) (ρ A) (ρ T) (ρ O) := by
  simp only [output,Formula.rename,StructuralListReverseSyntax.reverses_rename,StructuralListSpliceSyntax.splice_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_output {m} {Γ : Context m} (w A T O R : Fin m)
    (hR : Derives Γ (StructuralListReverseSyntax.reverses w A R)) (hS : Derives Γ (StructuralListSpliceSyntax.splice w R T O)) : Derives Γ (output w A T O) := by
  apply Derives.exI R
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,StructuralListReverseSyntax.reverses_rename,StructuralListSpliceSyntax.splice_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hR hS)

theorem reverse_cons_splice {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h A A1 R S R1 : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (hA : Derives Γ (StructuralListSyntax.consCode w h A A1))
    (hR : Derives Γ (StructuralListReverseSyntax.reverses w A R))
    (hS : Derives Γ (PacketVarintCanonicalRecursionSyntax.singleton w h S))
    (hSp : Derives Γ (StructuralListSpliceSyntax.splice w R S R1)) : Derives Γ (StructuralListReverseSyntax.reverses w A1 R1) := by
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (StructuralListReverseSyntax.atLength w.castSucc A.castSucc (Fin.last m) R.castSucc)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) hR
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ P
  let Q := successor (Fin.last (m+1)) (Fin.last m).castSucc
  let Ξ := Context.add Q (Context.image Formula.raise Δ)
  apply Derives.exE (p := Q) (InsertExistence.exists_insert (Fin.last m) (Fin.last m) (ZFContext.arithmetic hZ1).base.pairing (ZFContext.arithmetic hZ1).base.union)
  have hQ : Derives Ξ Q := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 Q
  have lift {φ : Formula m} (hp : Derives Γ φ) : Derives Ξ φ.raise.raise := under (under hp P) Q
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := by simpa only [Formula.raise,omega_rename] using lift hw
  have hA2 : Derives Ξ (StructuralListSyntax.consCode w.castSucc.castSucc h.castSucc.castSucc A.castSucc.castSucc A1.castSucc.castSucc) := by simpa only [Formula.raise,StructuralListSyntax.consCode_rename] using lift hA
  have hR2 : Derives Ξ (StructuralListReverseSyntax.reverses w.castSucc.castSucc A.castSucc.castSucc R.castSucc.castSucc) := by simpa only [Formula.raise,StructuralListReverseSyntax.reverses_rename] using lift hR
  have hS2 : Derives Ξ (PacketVarintCanonicalRecursionSyntax.singleton w.castSucc.castSucc h.castSucc.castSucc S.castSucc.castSucc) := by simpa only [Formula.raise,PacketVarintCanonicalRecursionSyntax.singleton_rename] using lift hS
  have hSp2 : Derives Ξ (StructuralListSpliceSyntax.splice w.castSucc.castSucc R.castSucc.castSucc S.castSucc.castSucc R1.castSucc.castSucc) := by simpa only [Formula.raise,StructuralListSpliceSyntax.splice_rename] using lift hSp
  have hLenA := of_eq (StructuralListLengthSyntax.hasLength_rename w.castSucc A.castSucc (Fin.last m) Fin.castSucc) (under (.conjL (.conjR hP)) Q)
  have hLenR := of_eq (StructuralListLengthSyntax.hasLength_rename w.castSucc R.castSucc (Fin.last m) Fin.castSucc) (under (.conjL (.conjR (.conjR hP))) Q)
  have hSnoc := StructuralListSpliceSnoc.at_splice hZ2 w.castSucc.castSucc R.castSucc.castSucc h.castSucc.castSucc S.castSucc.castSucc R1.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 (lift hh) hLenR hS2 hSp2 hQ
  simpa only [Formula.raise,StructuralListReverseSyntax.reverses_rename] using StructuralListReverseConsContract.backward hZ2 w.castSucc.castSucc h.castSucc.castSucc A.castSucc.castSucc A1.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) R.castSucc.castSucc R1.castSucc.castSucc hw2 (lift hh) hA2 hLenA hQ hR2 hSnoc

theorem nil_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w A T O : Fin m)
    (hw : Derives Γ (omega w)) (hT : Derives Γ (StructuralListSyntax.nilCode w T)) (hO : Derives Γ (output w A T O)) :
    Derives Γ (StructuralListReverseSyntax.reverses w A O) := by
  let R := (StructuralListReverseSyntax.reverses w.castSucc A.castSucc (Fin.last m)).conj (StructuralListSpliceSyntax.splice w.castSucc (Fin.last m) T.castSucc O.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hO
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hT1 := of_eq (StructuralListSyntax.nilCode_rename w T Fin.castSucc) (under hT R)
  have heq := Derives.conjR (Derives.impE (.conjL (StructuralListSpliceAlgebra.right_nil_iff hZ1 w.castSucc (Fin.last m) T.castSucc O.castSucc hw1 hT1)) (.conjR hR))
  simpa only [Formula.raise,StructuralListReverseSyntax.reverses_rename] using StructuralListReverseConsContract.output_subst _ _ _ _ (eq_symm heq) (.conjL hR)

end PPAC.Migration.Internal.PacketReaderOutputOrder
