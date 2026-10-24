import PPAC.Migration.Internal.PacketStructureCanonicalCases

/-! Exact all-internal accepted input fields imply the independent recursive structural cases; all auxiliary traces are eliminated. -/
namespace PPAC.Migration.Internal.PacketStructureAcceptedForward
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprSyntax PacketStructureSyntax PacketStructureAcceptedSyntax PacketStructureDispatchData
open SyntaxRenameQuerySyntax (of_eq)

theorem row_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w r : Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row k tag w xs r)) : Derives Γ (environmentNat k w xs) := by
  have hN := SyntaxNodeInjective.constructor_range hZ k tag w xs r hw hr
  exact HornApplicationRules.intro_nat w xs (fun i => StructuralListTraceOrder.member_member hZ w (xs i) r hw hN
    (SyntaxConstructors.child_member hZ k tag w xs r i hw hr))

theorem accepted_environment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (accepted k tag w xs)) : Derives Γ (environmentNat k w xs) := by
  let P := (row k tag w.castSucc (fun i => (xs i).castSucc) (Fin.last m)).conj (PacketTraceSyntax.condition w.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) ha
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  exact of_eq (environmentNat_rename k w xs Fin.castSucc).symm
    (row_environment (ZFContext.under hZ P) k tag w.castSucc (Fin.last m) (fun i => (xs i).castSucc) hw1 (.conjL hP))

theorem root_at_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (w V r : Fin m) (xs : Fin (width f) → Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (PacketTraceCore.value w V)) (hr : Derives Γ (row (width f) (tag f) w xs r))
    (hc : Derives Γ (PacketTraceSyntax.condition w r)) : Derives Γ (criterion f w xs) :=
  .impE (.conjL (PacketStructureCanonicalCases.criterion_iff f w V xs hv))
    (PacketStructureRootEquation.condition_forward hZ f w V r xs hw hv hr hc)

theorem root_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (w r : Fin m) (xs : Fin (width f) → Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row (width f) (tag f) w xs r))
    (hc : Derives Γ (PacketTraceSyntax.condition w r)) : Derives Γ (criterion f w xs) := by
  let P := PacketTraceCore.value w.castSucc (Fin.last m)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (PacketTraceCore.exists_value hZ w)
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hr1 := of_eq (row_rename (width f) (tag f) w r xs Fin.castSucc) (under hr P)
  have hc1 := of_eq (PacketTraceSyntax.condition_rename w r Fin.castSucc) (under hc P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  exact of_eq (criterion_rename f w xs Fin.castSucc).symm
    (root_at_value (ZFContext.under hZ P) f w.castSucc (Fin.last m) r.castSucc (fun i => (xs i).castSucc) hw1 hP hr1 hc1)

theorem accepted_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (w : Fin m) (xs : Fin (width f) → Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (accepted (width f) (tag f) w xs)) : Derives Γ (criterion f w xs) := by
  let P := (row (width f) (tag f) w.castSucc (fun i => (xs i).castSucc) (Fin.last m)).conj (PacketTraceSyntax.condition w.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) ha
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  exact of_eq (criterion_rename f w xs Fin.castSucc).symm
    (root_forward (ZFContext.under hZ P) f w.castSucc (Fin.last m) (fun i => (xs i).castSucc) hw1 (.conjL hP) (.conjR hP))

end PPAC.Migration.Internal.PacketStructureAcceptedForward
