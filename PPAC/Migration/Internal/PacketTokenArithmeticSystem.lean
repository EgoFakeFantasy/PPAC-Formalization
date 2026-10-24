import PPAC.Migration.Internal.PacketTokenArithmeticSystemSyntax

/-! Both actual radix values are internally obtained; all root and acceptance witnesses are discharged. -/
namespace PPAC.Migration.Internal.PacketTokenArithmeticSystem
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketTokenArithmeticSystemSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem all_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) :
    Derives Γ (allLaw w B C) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_many 3 hw)
  have hB3 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 3)) (HornBinderRules.under_many 3 hB)
  have hC3 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 3)) (HornBinderRules.under_many 3 hC)
  exact PacketTokenArithmeticEquation.accepted_iff (HornBinderRules.zf_many 3 hZ) (old 3 w) (old 3 B) (old 3 C)
    (slot 3 0) (slot 3 1) (slot 3 2) hw3 hB3 hC3

theorem all_root_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) :
    Derives Γ (allRootLaw w B C) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := PacketTokenSyntax.row (old 4 w : Fin (m+4)) (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3)
  have hw4 := of_eq (omega_rename w (old 4)) (HornBinderRules.under_body 4 hw H)
  have hB4 := of_eq (SyntaxNumeralSyntax.numeral_rename 128 B (old 4)) (HornBinderRules.under_body 4 hB H)
  have hC4 := of_eq (SyntaxNumeralSyntax.numeral_rename 256 C (old 4)) (HornBinderRules.under_body 4 hC H)
  exact PacketTokenArithmeticEquation.condition_iff (HornBinderRules.zf_body 4 hZ H) (old 4 w) (old 4 B) (old 4 C)
    (slot 4 0) (slot 4 1) (slot 4 2) (slot 4 3) hw4 hB4 hC4 (.hyp (Or.inl rfl))

theorem exists_system {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ (existsSystem w) := by
  let P := PacketAffineLiteralSyntax.frame false w.castSucc (Fin.last m)
  let ΓP := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (SyntaxNumerals.exists_numeral hZ 128 w hw)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  let Q := PacketAffineLiteralSyntax.frame true w.castSucc.castSucc (Fin.last (m+1))
  let Δ := Context.add Q (Context.image Formula.raise ΓP)
  apply Derives.exE (p := Q) (SyntaxNumerals.exists_numeral hZ1 256 w.castSucc hw1)
  have hZ2 := ZFContext.under hZ1 Q
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Q)
  have hP : Derives ΓP P := .hyp (Or.inl rfl)
  have hP2 : Derives Δ (PacketAffineLiteralSyntax.frame false w.castSucc.castSucc (Fin.last m).castSucc) :=
    of_eq (by simp only [P,Formula.raise,PacketAffineLiteralSyntax.frame_rename]) (under hP Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hS : Derives Δ (system w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))) := .conjI hP2
    (.conjI hQ (.conjI (all_law hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 (.conjR hP2) (.conjR hQ))
      (all_root_law hZ2 w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hw2 (.conjR hP2) (.conjR hQ))))
  have ho := intro_system w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hS
  simpa only [Formula.raise,existsSystem_rename] using ho

end PPAC.Migration.Internal.PacketTokenArithmeticSystem
