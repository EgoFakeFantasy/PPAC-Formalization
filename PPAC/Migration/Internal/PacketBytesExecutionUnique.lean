import PPAC.Migration.Internal.PacketBytesExecutionUniqueValues

/-! Full independent recursion covers both mixed branches and all internal output candidates. -/
namespace PPAC.Migration.Internal.PacketBytesExecutionUnique
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketBytesTraceSyntax PacketBytesExecutionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a b : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) (ha : Derives Γ (bytes w n t a)) (hb : Derives Γ (bytes w n t b)) :
    Derives Γ (.equal a b) := by
  have hca := Derives.impE (.conjL (PacketBytesRecursionLaws.actual_iff hZ w n t a hw)) ha
  apply Derives.disjE hca
  · have hN : Derives (Context.add (PacketBytesRecursionSyntax.nilCase w n t a) Γ) (PacketBytesRecursionSyntax.nilCase w n t a) := .hyp (Or.inl rfl)
    have htb := PacketBytesLaws.nil_value (ZFContext.add hZ _) w n t b (add hw _) (.conjL hN) (add hb _)
    exact eq_trans (eq_symm (.conjR (.conjR hN))) htb
  · let A := PacketBytesRecursionSyntax.actualCons w n t a
    have hZ1 := ZFContext.add hZ A
    have hcb := Derives.impE (.conjL (PacketBytesRecursionLaws.actual_iff hZ1 w n t b (add hw A))) (add hb A)
    apply Derives.disjE hcb
    · have hN : Derives (Context.add (PacketBytesRecursionSyntax.nilCase w n t b) (Context.add A Γ)) (PacketBytesRecursionSyntax.nilCase w n t b) := .hyp (Or.inl rfl)
      exact .botE (PacketBytesExecutionUniqueValues.nil_cons_false (ZFContext.add hZ1 _) w n t a (add (add hw A) _) (.conjL hN) (.hyp (Or.inr (Or.inl rfl))))
    · exact PacketBytesExecutionUniqueValues.cases_unique (ZFContext.add hZ1 _) w n t a b (add (add hw A) _) (add (add hi A) _)
        (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

theorem unique_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) : Derives Γ (unique w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let H := bytes (old 3 w : Fin (m+3)) (old 3 n) (slot 3 0) (slot 3 1)
  let K := bytes (old 3 w : Fin (m+3)) (old 3 n) (slot 3 0) (slot 3 2)
  let Δ := Context.add K (Context.add H (raisedContext 3 Γ))
  have hZ3 := ZFContext.add (ZFContext.add (HornBinderRules.zf_many 3 hZ) H) K
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_many 3 hw)
  have hi3 := of_eq (earlier_rename w n (old 3)) (HornBinderRules.under_many 3 hi)
  have hH : Derives Δ H := .hyp (Or.inr (Or.inl rfl))
  have hK : Derives Δ K := .hyp (Or.inl rfl)
  exact point hZ3 (old 3 w) (old 3 n) (slot 3 0) (slot 3 1) (slot 3 2) (add (add hw3 H) K) (add (add hi3 H) K) hH hK

end PPAC.Migration.Internal.PacketBytesExecutionUnique
