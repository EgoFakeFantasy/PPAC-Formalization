import PPAC.Migration.Internal.PacketByteInputBridge

/-! Only omega remains in the independent valid-byte guard and its exact all-internal recursion. -/
namespace PPAC.Migration.Internal.PacketByteInputLaws
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketByteInputSyntax PacketByteInputRecursionSyntax
open SyntaxRenameQuerySyntax (of_eq)

def allLaw {m} (w : Fin m) : Formula m := .all
  ((byteList w.castSucc (Fin.last m)).iff (criterion w.castSucc (Fin.last m)))

theorem allLaw_rename {m k} (w : Fin m) (ρ : Fin m → Fin k) : (allLaw w).rename ρ = allLaw (ρ w) := by
  simp only [allLaw,Formula.rename,Formula.iff,byteList_rename,criterion_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem byte_natural {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h : Fin m) (hw : Derives Γ (omega w))
    (hb : Derives Γ (byte h)) : Derives Γ (.mem h w) := by
  let R := (SyntaxNumeralSyntax.numeral 256 (Fin.last m)).conj (.mem h.castSucc (Fin.last m))
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hb
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hC := SyntaxNumerals.range hZ1 256 w.castSucc (Fin.last m) hw1 (.conjL hR)
  exact StructuralListTraceOrder.member_member hZ1 w.castSucc h.castSucc (Fin.last m) hw1 hC (.conjR hR)

theorem valid {m} {Γ : Context m} (w n : Fin m) (hi : Derives Γ (byteList w n)) : Derives Γ (StructuralListTraceSyntax.valid w n) := by
  let R := (SyntaxNumeralSyntax.numeral 256 (Fin.last m)).conj (inputAt w.castSucc (Fin.last m) n.castSucc)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hi
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  simpa only [Formula.raise,StructuralListTraceSyntax.valid_rename] using PacketByteInputProperties.valid w.castSucc (Fin.last m) n.castSucc (.conjR hR)

theorem natural {m} {Γ : Context m} (w n : Fin m) (hi : Derives Γ (byteList w n)) : Derives Γ (.mem n w) := StructuralListValidity.range _ _ (valid w n hi)

theorem actual_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((byteList w n).iff (criterion w n)) := by
  let R := PacketAffineLiteralSyntax.frame true w.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (SyntaxNumerals.exists_numeral hZ 256 w hw)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have h0 := PacketByteInputBridge.actual_iff_at hZ1 w.castSucc (Fin.last m) n.castSucc (.conjR hR)
  have h1 := PacketByteInputDecomposition.input_iff hZ1 w.castSucc (Fin.last m) n.castSucc hw1 (.conjL hR)
  have h2 := PacketByteInputBridge.cases_iff hZ1 w.castSucc (Fin.last m) n.castSucc (.conjR hR)
  have ho := SyntaxTypeLocalTransfer.iff_trans (SyntaxTypeLocalTransfer.iff_trans h0 h1) h2
  simpa only [Formula.raise,Formula.iff,Formula.rename,byteList_rename,criterion_rename] using ho

theorem all_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (allLaw w) := by
  apply Derives.allI
  have hw1 := of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw)
  exact actual_iff (ZFContext.rename hZ Fin.castSucc) w.castSucc (Fin.last m) hw1

end PPAC.Migration.Internal.PacketByteInputLaws
