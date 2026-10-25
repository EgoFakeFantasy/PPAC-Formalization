import PPAC.Migration.Internal.PacketReaderOutputBackwardCons

/-! Backward actual Cons consumption preserves exact output order; validity is an explicit genuine-list premise, and a natural-tail variant derives it from the old output. -/
namespace PPAC.Migration.Internal.PacketReaderOutputBackward
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderOutputOrder
open SyntaxRenameQuerySyntax (of_eq)

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h A A1 e T HT O : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w))
    (he : Derives Γ (StructuralListSyntax.nilCode w e))
    (hA : Derives Γ (StructuralListSyntax.consCode w h A A1))
    (ha : Derives Γ (StructuralListTraceSyntax.valid w A))
    (hT : Derives Γ (StructuralListTraceSyntax.valid w T))
    (hHT : Derives Γ (StructuralListSyntax.consCode w h T HT))
    (hOut : Derives Γ (output w A1 T O)) : Derives Γ (output w A HT O) := by
  let R := (Formula.mem (Fin.last m) w.castSucc).conj
    (StructuralListReverseSyntax.reverses w.castSucc A.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (StructuralListReverseEncoding.exists_reverse hZ w A hw ha)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have he1 := of_eq (StructuralListSyntax.nilCode_rename w e Fin.castSucc) (under he R)
  have hA1 := of_eq (StructuralListSyntax.consCode_rename w h A A1 Fin.castSucc) (under hA R)
  have hT1 := of_eq (StructuralListTraceSyntax.valid_rename w T Fin.castSucc) (under hT R)
  have hHT1 := of_eq (StructuralListSyntax.consCode_rename w h T HT Fin.castSucc) (under hHT R)
  have hOut1 := of_eq (output_rename w A1 T O Fin.castSucc) (under hOut R)
  simpa only [Formula.raise,output_rename] using
    PacketReaderOutputBackwardCons.with_reverse hZ1 w.castSucc h.castSucc A.castSucc A1.castSucc e.castSucc T.castSucc HT.castSucc O.castSucc (Fin.last m)
      hw1 (under hh R) he1 hA1 hT1 hHT1 hOut1 (.conjR hR)

theorem step_at_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h A A1 e T HT O : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w))
    (he : Derives Γ (StructuralListSyntax.nilCode w e))
    (hA : Derives Γ (StructuralListSyntax.consCode w h A A1)) (ha : Derives Γ (.mem A w))
    (hT : Derives Γ (StructuralListTraceSyntax.valid w T))
    (hHT : Derives Γ (StructuralListSyntax.consCode w h T HT))
    (hOut : Derives Γ (output w A1 T O)) : Derives Γ (output w A HT O) := by
  have hA1Valid := PacketReaderOutputBackwardBase.accumulator_valid w A1 T O hOut
  have hAValid := StructuralListDecode.tail_valid hZ w h A A1 hw hh ha hA hA1Valid
  exact step hZ w h A A1 e T HT O hw hh he hA hAValid hT hHT hOut

theorem step_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h A A1 e T HT O : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w))
    (he : Derives Γ (StructuralListSyntax.nilCode w e))
    (hA : Derives Γ (StructuralListSyntax.consCode w h A A1))
    (ha : Derives Γ (StructuralListTraceSyntax.valid w A))
    (hT : Derives Γ (StructuralListTraceSyntax.valid w T))
    (hHT : Derives Γ (StructuralListSyntax.consCode w h T HT)) :
    Derives Γ ((output w A1 T O).iff (output w A HT O)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact step (ZFContext.add hZ _) w h A A1 e T HT O (add hw _) (add hh _) (add he _) (add hA _) (add ha _) (add hT _) (add hHT _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact PacketReaderOutputCons.step (ZFContext.add hZ _) w h A A1 e T HT O (add hw _) (add hh _) (add he _) (add hA _) (add hT _) (add hHT _) (.hyp (Or.inl rfl))

theorem nil_accumulator {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w e T O : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (StructuralListSyntax.nilCode w e)) :
    Derives Γ ((output w e T O).iff ((StructuralListTraceSyntax.valid w T).conj (.equal T O))) :=
  PacketReaderOutputBackwardBase.nil_accumulator hZ w e T O hw he

end PPAC.Migration.Internal.PacketReaderOutputBackward
