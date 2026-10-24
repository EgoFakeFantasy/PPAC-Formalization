import PPAC.Migration.Internal.PacketTokenSystemSyntax

/-! Both radices and the canonical root set are obtained internally; only omega remains as a premise. -/
namespace PPAC.Migration.Internal.PacketTokenSystem
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketTokenSystemSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem all_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C V : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hv : Derives Γ (PacketTraceCore.value w V)) :
    Derives Γ (allLaw w B C V) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := PacketTokenSyntax.row (old 4 w : Fin (m+4)) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw H)
  have hB4 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 4)) (HornBinderRules.under_body 4 hB H)
  have hC4 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 4)) (HornBinderRules.under_body 4 hC H)
  have hv4 := of_eq (PacketTraceCore.value_rename w V (old 4)) (HornBinderRules.under_body 4 hv H)
  exact PacketTokenDispatch.condition_iff_outcomes (HornBinderRules.zf_body 4 hZ H) (old 4 w) (old 4 B) (old 4 C)
    (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) (old 4 V) hw4 hB4 hC4 hv4 (.hyp (Or.inl rfl))

theorem exists_system {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (existsSystem w) := by
  let P := PacketAffineLiteralSyntax.frame false w.castSucc (Fin.last m)
  let ΓP := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (SyntaxNumerals.exists_numeral hZ 128 w hw)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  let Q := PacketAffineLiteralSyntax.frame true w.castSucc.castSucc (Fin.last (m+1))
  let ΓQ := Context.add Q (Context.image Formula.raise ΓP)
  apply Derives.exE (p := Q) (SyntaxNumerals.exists_numeral hZ1 256 w.castSucc hw1)
  have hZ2 := ZFContext.under hZ1 Q
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Q)
  let R := PacketTraceCore.value w.castSucc.castSucc.castSucc (Fin.last (m+2))
  let Δ := Context.add R (Context.image Formula.raise ΓQ)
  apply Derives.exE (p := R) (PacketTraceCore.exists_value hZ2 w.castSucc.castSucc)
  have hZ3 := ZFContext.under hZ2 R
  have hw3 := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 R)
  have hP : Derives ΓP P := .hyp (Or.inl rfl)
  have hP3 : Derives Δ (PacketAffineLiteralSyntax.frame false w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc) :=
    of_eq (by simp only [P,Formula.raise,PacketAffineLiteralSyntax.frame_rename]) (under (under hP Q) R)
  have hQ : Derives ΓQ Q := .hyp (Or.inl rfl)
  have hQ3 : Derives Δ (PacketAffineLiteralSyntax.frame true w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc) :=
    of_eq (by simp only [Q,Formula.raise,PacketAffineLiteralSyntax.frame_rename]) (under hQ R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hS : Derives Δ (system w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))) :=
    .conjI hP3 (.conjI hQ3 (.conjI hR (all_law hZ3 w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc
      (Fin.last (m+1)).castSucc (Fin.last (m+2)) hw3 (.conjR hP3) (.conjR hQ3) hR)))
  have ho := intro_system w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hS
  simpa only [Formula.raise,existsSystem_rename] using ho

end PPAC.Migration.Internal.PacketTokenSystem
