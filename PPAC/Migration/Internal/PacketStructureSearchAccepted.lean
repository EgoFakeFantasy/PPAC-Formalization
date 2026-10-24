import PPAC.Migration.Internal.PacketStructureSearchEquation

/-! The exact actual recursive equations retain all original field-naturality guards, including the Nil tail. -/
namespace PPAC.Migration.Internal.PacketStructureSearchAccepted
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax PacketStructureSyntax PacketStructureAcceptedSyntax PacketStructureDispatchData
open SyntaxRenameQuerySyntax (of_eq)

theorem backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (w : Fin m) (xs : Fin (width f) → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat (width f) w xs)) (hc : Derives Γ (criterion f w xs)) :
    Derives Γ (accepted (width f) (tag f) w xs) := by
  let P := PacketTraceCore.value w.castSucc (Fin.last m)
  let ΓP := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (PacketTraceCore.exists_value hZ w)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hn1 := of_eq (environmentNat_rename (width f) w xs Fin.castSucc) (under hn P)
  have hc1 := of_eq (criterion_rename f w xs Fin.castSucc) (under hc P)
  have hP : Derives ΓP P := .hyp (Or.inl rfl)
  have ht1 := Derives.impE (.conjR (PacketStructureCanonicalCases.criterion_iff f w.castSucc (Fin.last m) (fun i => (xs i).castSucc) hP)) hc1
  have hin := SyntaxForestSyntax.intro_inputs (width f) w.castSucc (fun i => (xs i).castSucc) (fun i => environmentNat_at _ _ hn1 i)
  let Q := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (row (width f) (tag f) w.castSucc.castSucc (fun i => (xs i).castSucc.castSucc) (Fin.last (m+1)))
  let Δ := Context.add Q (Context.image Formula.raise ΓP)
  apply Derives.exE (p := Q) (SyntaxConstructors.exists_constructor hZ1 (width f) (tag f) w.castSucc (fun i => (xs i).castSucc) hw1 hin)
  have hZ2 := ZFContext.under hZ1 Q
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Q)
  have hv2 := of_eq (PacketTraceCore.value_rename w.castSucc (Fin.last m) Fin.castSucc) (under hP Q)
  have ht2 := of_eq (PacketStructureRootSyntax.criterion_rename f w.castSucc (Fin.last m) (fun i => (xs i).castSucc) Fin.castSucc) (under ht1 Q)
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hcond := Derives.impE (.conjR (PacketStructureSearchEquation.condition_iff_criterion hZ2 f w.castSucc.castSucc (Fin.last m).castSucc
    (Fin.last (m+1)) (fun i => (xs i).castSucc.castSucc) hw2 hv2 (.conjR hQ))) ht2
  have ha := PacketStructureAcceptedSyntax.intro_accepted (width f) (tag f) w.castSucc.castSucc (Fin.last (m+1))
    (fun i => (xs i).castSucc.castSucc) (.conjR hQ) hcond
  simpa only [Formula.raise,accepted_rename] using ha

theorem accepted_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (w : Fin m) (xs : Fin (width f) → Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((accepted (width f) (tag f) w xs).iff
      ((environmentNat (width f) w xs).conj (criterion f w xs))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact .conjI (PacketStructureAcceptedForward.accepted_environment (ZFContext.add hZ _) (width f) (tag f) w xs (add hw _) (.hyp (Or.inl rfl)))
      (PacketStructureAcceptedForward.accepted_forward (ZFContext.add hZ _) f w xs (add hw _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    have hH : Derives (Context.add ((environmentNat (width f) w xs).conj (criterion f w xs)) Γ)
      ((environmentNat (width f) w xs).conj (criterion f w xs)) := .hyp (Or.inl rfl)
    exact backward (ZFContext.add hZ _) f w xs (add hw _) (.conjL hH) (.conjR hH)

end PPAC.Migration.Internal.PacketStructureSearchAccepted
