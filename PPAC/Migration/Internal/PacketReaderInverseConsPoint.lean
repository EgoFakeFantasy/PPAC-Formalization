import PPAC.Migration.Internal.PacketReaderInverseSyntax
import PPAC.Migration.Internal.PacketReaderOutputBackward
import PPAC.Migration.Internal.PacketReaderTokenUnits
import PPAC.Migration.Internal.PacketReaderSuccess

/-! An actual token Cons is reconstructed internally from an independently encoded tail and the exact output relation. -/
namespace PPAC.Migration.Internal.PacketReaderInverseConsPoint
open Source SourceAlgebra SourceLogic OmegaSyntax
open PacketReaderInverseSyntax (result result_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem at_tokens {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z o L A O n C T c t N : Fin m)
    (hw : Derives Γ (omega w))
    (hz : Derives Γ (empty z))
    (ho : Derives Γ (successor o z))
    (hA : Derives Γ (StructuralListTraceSyntax.valid w A))
    (hC : Derives Γ (PacketVarintSyntax.canonical w n C))
    (hSp : Derives Γ (StructuralListSpliceSyntax.splice w C T L))
    (hCons : Derives Γ (StructuralListSyntax.consCode w n A c))
    (hEncoded : Derives Γ (PacketTokensBytes.encoded w t T))
    (hOutput : Derives Γ (PacketReaderOutputOrder.output w c t O))
    (hN : Derives Γ (StructuralListSyntax.consCode w n t N)) :
    Derives Γ (result w L A O) := by
  have hn := Derives.conjL (PacketVarintDomain.domain w n C hC)
  have ht := PacketTokensBytes.input_valid w t T hEncoded
  have htN := StructuralListValidity.range w t ht
  have hNil := StructuralNil.at_unit hZ w z o hw hz ho
  have hCase := PacketTokensBytes.intro_case w n t L C T hC hEncoded hSp
  have hFull := Derives.impE (.conjR (PacketTokensBytes.cons_iff hZ w n t N L hw hn htN hN)) hCase
  have hOut := PacketReaderOutputBackward.step hZ w n A c o t N O hw hn hNil hCons hA ht hN hOutput
  exact PacketReaderInverseSyntax.intro_result w L A O N hFull hOut

theorem with_tail {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z o L A O n C T c t : Fin m)
    (hw : Derives Γ (omega w))
    (hz : Derives Γ (empty z))
    (ho : Derives Γ (successor o z))
    (hA : Derives Γ (StructuralListTraceSyntax.valid w A))
    (hC : Derives Γ (PacketVarintSyntax.canonical w n C))
    (hSp : Derives Γ (StructuralListSpliceSyntax.splice w C T L))
    (hCons : Derives Γ (StructuralListSyntax.consCode w n A c))
    (hEncoded : Derives Γ (PacketTokensBytes.encoded w t T))
    (hOutput : Derives Γ (PacketReaderOutputOrder.output w c t O))
    : Derives Γ (result w L A O) := by
  have hn := Derives.conjL (PacketVarintDomain.domain w n C hC)
  have ht := StructuralListValidity.range w t (PacketTokensBytes.input_valid w t T hEncoded)
  let R := (Formula.mem (Fin.last m) w.castSucc).conj
    (StructuralListSyntax.consCode w.castSucc n.castSucc t.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (StructuralConsCore.exists_cons hZ w n t hw hn ht)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz R)
  have ho1 := of_eq (successor_rename o z Fin.castSucc) (under ho R)
  have hA1 := of_eq (StructuralListTraceSyntax.valid_rename w A Fin.castSucc) (under hA R)
  have hC1 := of_eq (PacketVarintSyntax.canonical_rename w n C Fin.castSucc) (under hC R)
  have hSp1 := of_eq (StructuralListSpliceSyntax.splice_rename w C T L Fin.castSucc) (under hSp R)
  have hCons1 := of_eq (StructuralListSyntax.consCode_rename w n A c Fin.castSucc) (under hCons R)
  have hEncoded1 := of_eq (PacketTokensBytes.encoded_rename w t T Fin.castSucc) (under hEncoded R)
  have hOutput1 := of_eq (PacketReaderOutputOrder.output_rename w c t O Fin.castSucc) (under hOutput R)
  simpa only [Formula.raise,result_rename] using at_tokens hZ1
    w.castSucc z.castSucc o.castSucc L.castSucc A.castSucc O.castSucc n.castSucc C.castSucc T.castSucc c.castSucc t.castSucc (Fin.last m)
    hw1 hz1 ho1 hA1 hC1 hSp1 hCons1 hEncoded1 hOutput1 (.conjR hR)

theorem from_tail_result {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (w z o L A O n C T c : Fin m)
    (hw : Derives Γ (omega w))
    (hz : Derives Γ (empty z))
    (ho : Derives Γ (successor o z))
    (hA : Derives Γ (StructuralListTraceSyntax.valid w A))
    (hC : Derives Γ (PacketVarintSyntax.canonical w n C))
    (hSp : Derives Γ (StructuralListSpliceSyntax.splice w C T L))
    (hCons : Derives Γ (StructuralListSyntax.consCode w n A c))
    (hTail : Derives Γ (result w T c O)) : Derives Γ (result w L A O) := by
  let R := (PacketTokensBytes.encoded w.castSucc (Fin.last m) T.castSucc).conj
    (PacketReaderOutputOrder.output w.castSucc c.castSucc (Fin.last m) O.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hTail
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz R)
  have ho1 := of_eq (successor_rename o z Fin.castSucc) (under ho R)
  have hA1 := of_eq (StructuralListTraceSyntax.valid_rename w A Fin.castSucc) (under hA R)
  have hC1 := of_eq (PacketVarintSyntax.canonical_rename w n C Fin.castSucc) (under hC R)
  have hSp1 := of_eq (StructuralListSpliceSyntax.splice_rename w C T L Fin.castSucc) (under hSp R)
  have hCons1 := of_eq (StructuralListSyntax.consCode_rename w n A c Fin.castSucc) (under hCons R)
  simpa only [Formula.raise,result_rename] using with_tail hZ1
    w.castSucc z.castSucc o.castSucc L.castSucc A.castSucc O.castSucc n.castSucc C.castSucc T.castSucc c.castSucc (Fin.last m)
    hw1 hz1 ho1 hA1 hC1 hSp1 hCons1 (.conjL hR) (.conjR hR)

end PPAC.Migration.Internal.PacketReaderInverseConsPoint
