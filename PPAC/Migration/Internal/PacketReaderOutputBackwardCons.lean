import PPAC.Migration.Internal.PacketReaderOutputBackwardBase

/-! The same genuine singleton splice reverses a Cons accumulator and reassociates the remaining token head in the backward direction. -/
namespace PPAC.Migration.Internal.PacketReaderOutputBackwardCons
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderOutputOrder
open SyntaxRenameQuerySyntax (of_eq)

theorem with_singleton {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h A A1 R e S T HT O : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w))
    (he : Derives Γ (StructuralListSyntax.nilCode w e))
    (hS : Derives Γ (StructuralListSyntax.consCode w h e S))
    (hA : Derives Γ (StructuralListSyntax.consCode w h A A1))
    (hRev : Derives Γ (StructuralListReverseSyntax.reverses w A R))
    (hT : Derives Γ (StructuralListTraceSyntax.valid w T))
    (hHT : Derives Γ (StructuralListSyntax.consCode w h T HT))
    (hOut : Derives Γ (output w A1 T O)) : Derives Γ (output w A HT O) := by
  have hRV := StructuralListReverseUnique.valid_output w A R hRev
  have hSV := StructuralListValidity.cons_valid hZ w h e S hw hh (StructuralListTraceBase.valid_nil hZ w e hw he) hS
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
  have hOut1 := of_eq (output_rename w A1 T O Fin.castSucc) (under hOut P)
  have hSingleton := PacketVarintCanonicalRecursionSyntax.intro_singleton _ _ _ _ he1 hS1
  have hNewRev := reverse_cons_splice hZ1 w.castSucc h.castSucc A.castSucc A1.castSucc R.castSucc S.castSucc (Fin.last m)
    hw1 (under hh P) hA1 hRev1 hSingleton (.conjR (.conjL hP))
  have hOldSplice := Derives.impE (.conjL (PacketReaderOutputBackwardBase.at_reverse hZ1 w.castSucc A1.castSucc T.castSucc O.castSucc (Fin.last m) hw1 hNewRev)) hOut1
  have hAssoc := StructuralListSpliceAlgebra.snoc_cons_iff hZ1 w.castSucc R.castSucc e.castSucc h.castSucc S.castSucc (Fin.last m) T.castSucc HT.castSucc O.castSucc
    hw1 (under hh P) he1 hS1 (.conjR (.conjL hP)) hT1 hHT1
  have hNewSplice := Derives.impE (.conjL hAssoc) hOldSplice
  simpa only [Formula.raise,output_rename] using intro_output w.castSucc A.castSucc HT.castSucc O.castSucc R.castSucc hRev1 hNewSplice

theorem with_reverse {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h A A1 e T HT O R : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w))
    (he : Derives Γ (StructuralListSyntax.nilCode w e))
    (hA : Derives Γ (StructuralListSyntax.consCode w h A A1))
    (hT : Derives Γ (StructuralListTraceSyntax.valid w T))
    (hHT : Derives Γ (StructuralListSyntax.consCode w h T HT))
    (hOut : Derives Γ (output w A1 T O))
    (hRev : Derives Γ (StructuralListReverseSyntax.reverses w A R)) : Derives Γ (output w A HT O) := by
  have heN := StructuralNil.range hZ w e hw he
  let S := (Formula.mem (Fin.last m) w.castSucc).conj
    (StructuralListSyntax.consCode w.castSucc h.castSucc e.castSucc (Fin.last m))
  let Δ := Context.add S (Context.image Formula.raise Γ)
  apply Derives.exE (p := S) (StructuralConsCore.exists_cons hZ w h e hw hh heN)
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ S
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw S)
  have he1 := of_eq (StructuralListSyntax.nilCode_rename w e Fin.castSucc) (under he S)
  have hA1 := of_eq (StructuralListSyntax.consCode_rename w h A A1 Fin.castSucc) (under hA S)
  have hT1 := of_eq (StructuralListTraceSyntax.valid_rename w T Fin.castSucc) (under hT S)
  have hHT1 := of_eq (StructuralListSyntax.consCode_rename w h T HT Fin.castSucc) (under hHT S)
  have hOut1 := of_eq (output_rename w A1 T O Fin.castSucc) (under hOut S)
  have hRev1 := of_eq (StructuralListReverseSyntax.reverses_rename w A R Fin.castSucc) (under hRev S)
  simpa only [Formula.raise,output_rename] using
    with_singleton hZ1 w.castSucc h.castSucc A.castSucc A1.castSucc R.castSucc e.castSucc (Fin.last m) T.castSucc HT.castSucc O.castSucc
      hw1 (under hh S) he1 (.conjR hS) hA1 hRev1 hT1 hHT1 hOut1

end PPAC.Migration.Internal.PacketReaderOutputBackwardCons
