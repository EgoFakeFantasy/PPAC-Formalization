import PPAC.Migration.Internal.PacketStructureAcceptedSyntax

/-! Canonical trace entries and independent real acceptance agree for every internal candidate. -/
namespace PPAC.Migration.Internal.PacketStructureCanonicalCases
open Source SourceAlgebra SourceLogic HornBinderSyntax PacketStructureSyntax PacketStructureAcceptedSyntax PacketStructureDispatchData
open SyntaxRenameQuerySyntax (of_eq)

theorem entry_iff {m} {Γ : Context m} (k tag : Nat) (w V : Fin m) (xs : Fin k → Fin m)
    (hv : Derives Γ (PacketTraceCore.value w V)) : Derives Γ ((entry k tag w V xs).iff (accepted k tag w xs)) := by
  apply FormulaCodeCongruence.ex_congr
  have hv1 := of_eq (PacketTraceCore.value_rename w V Fin.castSucc) (Derives.rename Fin.castSucc hv)
  exact FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
    (PacketTraceCore.member_iff w.castSucc V.castSucc (Fin.last m) hv1)

theorem tree_iff {m} {Γ : Context m} (w V n t a : Fin m) (hv : Derives Γ (PacketTraceCore.value w V)) :
    Derives Γ ((PacketStructureRootSyntax.treeCase w V n t a).iff (treeCase w n t a)) := by
  apply FormulaCodeCongruence.ex_congr
  apply FormulaCodeCongruence.ex_congr
  apply FormulaCodeCongruence.ex_congr
  apply FormulaCodeCongruence.ex_congr
  apply FormulaCodeCongruence.ex_congr
  have hv5 := of_eq (PacketTraceCore.value_rename w V (old 5)) (HornBinderRules.under_many 5 hv)
  exact FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
    (FormulaCodeCongruence.conj_congr (entry_iff 4 4 (old 5 w) (old 5 V) (four (slot 5 1) (slot 5 2) (old 5 t) (slot 5 3)) hv5)
      (FormulaCodeCongruence.conj_congr (PacketTokenCanonicalEntry.entry_iff 2 (old 5 w) (old 5 V) (slot 5 2) (slot 5 3) (slot 5 4) hv5)
        (PacketTokenCanonicalEntry.entry_iff 2 (old 5 w) (old 5 V) (slot 5 0) (slot 5 4) (old 5 a) hv5)))

theorem cons_iff {m} {Γ : Context m} (w V n l t a : Fin m) (hv : Derives Γ (PacketTraceCore.value w V)) :
    Derives Γ ((PacketStructureRootSyntax.consCase w V n l t a).iff (consCase w n l t a)) := by
  apply FormulaCodeCongruence.ex_congr
  apply FormulaCodeCongruence.ex_congr
  apply FormulaCodeCongruence.ex_congr
  apply FormulaCodeCongruence.ex_congr
  have hv4 := of_eq (PacketTraceCore.value_rename w V (old 4)) (HornBinderRules.under_many 4 hv)
  exact FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
    (FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
      (FormulaCodeCongruence.conj_congr (entry_iff 4 4 (old 4 w) (old 4 V) (four (slot 4 1) (slot 4 2) (old 4 t) (slot 4 3)) hv4)
        (entry_iff 3 3 (old 4 w) (old 4 V) (SyntaxAtomSyntax.three (slot 4 0) (slot 4 3) (old 4 a)) hv4)))

theorem packet_iff {m} {Γ : Context m} (w V a n : Fin m) (hv : Derives Γ (PacketTraceCore.value w V)) :
    Derives Γ ((PacketStructureRootSyntax.packetCase w V a n).iff (packetCase w a n)) := by
  apply FormulaCodeCongruence.ex_congr
  apply FormulaCodeCongruence.ex_congr
  have hv2 := of_eq (PacketTraceCore.value_rename w V (old 2)) (HornBinderRules.under_many 2 hv)
  exact FormulaCodeCongruence.conj_congr (SyntaxTypeLocalTransfer.iff_refl _)
    (FormulaCodeCongruence.conj_congr (PacketTokenCanonicalEntry.entry_iff 1 (old 2 w) (old 2 V) (slot 2 0) (slot 2 1) (old 2 a) hv2)
      (entry_iff 3 3 (old 2 w) (old 2 V) (SyntaxAtomSyntax.three (old 2 n) (slot 2 0) (slot 2 1)) hv2))

theorem criterion_iff {m} {Γ : Context m} (f : Family) (w V : Fin m) (xs : Fin (width f) → Fin m)
    (hv : Derives Γ (PacketTraceCore.value w V)) :
    Derives Γ ((PacketStructureRootSyntax.criterion f w V xs).iff (criterion f w xs)) := by
  cases f
  · exact tree_iff _ _ _ _ _ hv
  · exact SyntaxTypeLocalTransfer.disj_congr (SyntaxTypeLocalTransfer.iff_refl _) (cons_iff _ _ _ _ _ _ hv)
  · exact packet_iff _ _ _ _ hv

end PPAC.Migration.Internal.PacketStructureCanonicalCases
