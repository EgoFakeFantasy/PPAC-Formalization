import PPAC.Migration.Internal.PacketReaderOutputOrder

/-! Consuming a real head token changes the reversed accumulator while preserving exactly reverse(acc) ++ tokens as the final output. -/
namespace PPAC.Migration.Internal.PacketReaderOutputCons
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderOutputOrder
open SyntaxRenameQuerySyntax (of_eq)

theorem with_singleton {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h A A1 R e S T HT O : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (he : Derives Γ (StructuralListSyntax.nilCode w e))
    (hS : Derives Γ (StructuralListSyntax.consCode w h e S)) (hA : Derives Γ (StructuralListSyntax.consCode w h A A1))
    (hRev : Derives Γ (StructuralListReverseSyntax.reverses w A R)) (hT : Derives Γ (StructuralListTraceSyntax.valid w T))
    (hHT : Derives Γ (StructuralListSyntax.consCode w h T HT)) (hOut : Derives Γ (StructuralListSpliceSyntax.splice w R HT O)) :
    Derives Γ (output w A1 T O) := by
  have hRV := StructuralListReverseUnique.valid_output _ _ _ hRev
  have hSV := StructuralListValidity.cons_valid hZ _ _ _ _ hw hh (StructuralListTraceBase.valid_nil hZ _ _ hw he) hS
  let P := StructuralListSpliceTotalSyntax.fiberBody w R S
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (StructuralListSpliceTotal.exists_unique hZ w R S hw hRV hSV)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have he1 := of_eq (StructuralListSyntax.nilCode_rename w e Fin.castSucc) (under he P)
  have hS1 := of_eq (StructuralListSyntax.consCode_rename w h e S Fin.castSucc) (under hS P)
  have hA1 := of_eq (StructuralListSyntax.consCode_rename w h A A1 Fin.castSucc) (under hA P)
  have hRev1 := of_eq (StructuralListReverseSyntax.reverses_rename w A R Fin.castSucc) (under hRev P)
  have hT1 := of_eq (StructuralListTraceSyntax.valid_rename w T Fin.castSucc) (under hT P)
  have hHT1 := of_eq (StructuralListSyntax.consCode_rename w h T HT Fin.castSucc) (under hHT P)
  have hOut1 := of_eq (StructuralListSpliceSyntax.splice_rename w R HT O Fin.castSucc) (under hOut P)
  have hSingleton := PacketVarintCanonicalRecursionSyntax.intro_singleton _ _ _ _ he1 hS1
  have hNewRev := reverse_cons_splice hZ1 w.castSucc h.castSucc A.castSucc A1.castSucc R.castSucc S.castSucc (Fin.last m) hw1 (under hh P) hA1 hRev1 hSingleton (.conjR (.conjL hP))
  have hAssoc := StructuralListSpliceAlgebra.snoc_cons_iff hZ1 w.castSucc R.castSucc e.castSucc h.castSucc S.castSucc (Fin.last m) T.castSucc HT.castSucc O.castSucc hw1 (under hh P) he1 hS1 (.conjR (.conjL hP)) hT1 hHT1
  have hNewOut := Derives.impE (.conjR hAssoc) hOut1
  simpa only [Formula.raise,output_rename] using intro_output _ _ _ _ _ hNewRev hNewOut

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h A A1 e T HT O : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (he : Derives Γ (StructuralListSyntax.nilCode w e))
    (hA : Derives Γ (StructuralListSyntax.consCode w h A A1)) (hT : Derives Γ (StructuralListTraceSyntax.valid w T))
    (hHT : Derives Γ (StructuralListSyntax.consCode w h T HT)) (hOut : Derives Γ (output w A HT O)) :
    Derives Γ (output w A1 T O) := by
  let R := (StructuralListReverseSyntax.reverses w.castSucc A.castSucc (Fin.last m)).conj (StructuralListSpliceSyntax.splice w.castSucc (Fin.last m) HT.castSucc O.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hOut
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have heN := StructuralNil.range hZ w e hw he
  let S := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (StructuralListSyntax.consCode w.castSucc.castSucc h.castSucc.castSucc e.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add S (Context.image Formula.raise Δ)
  apply Derives.exE (p := S) (StructuralConsCore.exists_cons hZ1 w.castSucc h.castSucc e.castSucc hw1 (under hh R) (under heN R))
  have hS : Derives Ξ S := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 S
  have lift {φ : Formula m} (hp : Derives Γ φ) : Derives Ξ φ.raise.raise := under (under hp R) S
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := by simpa only [Formula.raise,omega_rename] using lift hw
  have he2 : Derives Ξ (StructuralListSyntax.nilCode w.castSucc.castSucc e.castSucc.castSucc) := by simpa only [Formula.raise,StructuralListSyntax.nilCode_rename] using lift he
  have hA2 : Derives Ξ (StructuralListSyntax.consCode w.castSucc.castSucc h.castSucc.castSucc A.castSucc.castSucc A1.castSucc.castSucc) := by simpa only [Formula.raise,StructuralListSyntax.consCode_rename] using lift hA
  have hT2 : Derives Ξ (StructuralListTraceSyntax.valid w.castSucc.castSucc T.castSucc.castSucc) := by simpa only [Formula.raise,StructuralListTraceSyntax.valid_rename] using lift hT
  have hHT2 : Derives Ξ (StructuralListSyntax.consCode w.castSucc.castSucc h.castSucc.castSucc T.castSucc.castSucc HT.castSucc.castSucc) := by simpa only [Formula.raise,StructuralListSyntax.consCode_rename] using lift hHT
  have hRev2 := of_eq (StructuralListReverseSyntax.reverses_rename w.castSucc A.castSucc (Fin.last m) Fin.castSucc) (under (.conjL hR) S)
  have hOut2 := of_eq (StructuralListSpliceSyntax.splice_rename w.castSucc (Fin.last m) HT.castSucc O.castSucc Fin.castSucc) (under (.conjR hR) S)
  simpa only [Formula.raise,output_rename] using with_singleton hZ2 w.castSucc.castSucc h.castSucc.castSucc A.castSucc.castSucc A1.castSucc.castSucc (Fin.last m).castSucc e.castSucc.castSucc (Fin.last (m+1)) T.castSucc.castSucc HT.castSucc.castSucc O.castSucc.castSucc hw2 (lift hh) he2 (.conjR hS) hA2 hRev2 hT2 hHT2 hOut2

end PPAC.Migration.Internal.PacketReaderOutputCons
