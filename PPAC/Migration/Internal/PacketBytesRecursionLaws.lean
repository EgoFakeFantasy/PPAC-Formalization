import PPAC.Migration.Internal.PacketBytesRecursionBridge

/-! Only omega remains in the exact independent ordered-byte recursion for every internal candidate. -/
namespace PPAC.Migration.Internal.PacketBytesRecursionLaws
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketBytesTraceSyntax PacketBytesRecursionSyntax
open SyntaxRenameQuerySyntax (of_eq)

def lawBody {m} (w : Fin m) : Formula (m+3) :=
  (bytes (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2)).iff (criterion (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2))

def allLaw {m} (w : Fin m) : Formula m := OriginalUniversalBlock.allMany 3 (lawBody w)

theorem lawBody_lift {m k} (w : Fin m) (ρ : Fin m → Fin k) : (lawBody w).rename (lift 3 ρ) = lawBody (ρ w) := by
  simp only [lawBody,Formula.iff,Formula.rename,bytes_rename,criterion_rename,lift_old,lift_slot]

theorem allLaw_rename {m k} (w : Fin m) (ρ : Fin m → Fin k) : (allLaw w).rename ρ = allLaw (ρ w) := by
  simp only [allLaw,OriginalUniversalBlock.allMany_rename,lawBody_lift]

theorem actual_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((bytes w n t a).iff (criterion w n t a)) := by
  let R := PacketAffineLiteralSyntax.frame true w.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (SyntaxNumerals.exists_numeral hZ 256 w hw)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have h0 := PacketBytesLaws.fold_iff hZ1 w.castSucc (Fin.last m) n.castSucc t.castSucc a.castSucc (.conjR hR)
  have h1 := PacketBytesRecursionEquation.fold_iff hZ1 w.castSucc (Fin.last m) n.castSucc t.castSucc a.castSucc hw1
  have h2 := PacketBytesRecursionBridge.cases_iff hZ1 w.castSucc (Fin.last m) n.castSucc t.castSucc a.castSucc hw1 (.conjR hR)
  have ho := SyntaxTypeLocalTransfer.iff_trans (SyntaxTypeLocalTransfer.iff_trans h0 h1) h2
  simpa only [Formula.raise,Formula.iff,Formula.rename,bytes_rename,criterion_rename] using ho

theorem all_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (allLaw w) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_many 3 hw)
  exact actual_iff (HornBinderRules.zf_many 3 hZ) (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2) hw3

end PPAC.Migration.Internal.PacketBytesRecursionLaws
