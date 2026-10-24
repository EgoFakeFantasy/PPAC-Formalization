import PPAC.Migration.Internal.PacketBytesExecutionTotal

/-! Every actual execution has an independently valid byte input; the exact input domain is included in the joint induction. -/
namespace PPAC.Migration.Internal.PacketBytesExecutionDomain
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketBytesTraceSyntax PacketByteInputSyntax PacketBytesExecutionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem cons_point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a h x u : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) (hc : Derives Γ (StructuralListSyntax.consCode w h x n))
    (hx : Derives Γ (bytes w x t u)) (ha : Derives Γ (PacketAffineAcceptedSyntax.accepted true w h u a)) : Derives Γ (byteList w n) := by
  have hp := PacketBytesExecutionDescent.accepted_tail_property hZ w n t a h x u hw hi hc hx ha
  have hinput := domain_at w x t u hp hx
  have hh := Derives.conjL (PacketBytesExecutionAffine.data hZ w h u a hw ha)
  have hcase := PacketByteInputRecursionSyntax.intro_actual_cons w n h x hc hh hinput
  exact .impE (.conjR (PacketByteInputLaws.actual_iff hZ w n hw)) (.disjR hcase)

theorem cons_case {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) (hc : Derives Γ (PacketBytesRecursionSyntax.actualCons w n t a)) :
    Derives Γ (byteList w n) := by
  let R := PacketBytesRecursionSyntax.actualBody w n t a
  let Δ := Context.add R (raisedContext 3 Γ)
  apply HornBinderRules.eliminate_many 3 R _ hc
  have hZ3 := HornBinderRules.zf_body 3 hZ R
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_body 3 hw R)
  have hi3 := of_eq (earlier_rename w n (old 3)) (HornBinderRules.under_body 3 hi R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact of_eq (byteList_rename w n (old 3)).symm
    (cons_point hZ3 (old 3 w) (old 3 n) (old 3 t) (old 3 a) (slot 3 0) (slot 3 1) (slot 3 2) hw3 hi3
      (.conjL hR) (.conjL (.conjR hR)) (.conjR (.conjR hR)))

theorem point {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) (hb : Derives Γ (bytes w n t a)) : Derives Γ (byteList w n) := by
  have hc := Derives.impE (.conjL (PacketBytesRecursionLaws.actual_iff hZ w n t a hw)) hb
  apply Derives.disjE hc
  · exact .impE (.conjR (PacketByteInputLaws.actual_iff (ZFContext.add hZ _) w n (add hw _))) (.disjL (.conjL (.hyp (Or.inl rfl))))
  · exact cons_case (ZFContext.add hZ _) w n t a (add hw _) (add hi _) (.hyp (Or.inl rfl))

theorem domain_property {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hw : Derives Γ (omega w)) (hi : Derives Γ (earlier w n)) : Derives Γ (domain w n) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let H := bytes (old 2 w : Fin (m+2)) (old 2 n) (slot 2 0) (slot 2 1)
  have hw2 := of_eq (omega_rename w (old 2)) (HornBinderRules.under_body 2 hw H)
  have hi2 := of_eq (earlier_rename w n (old 2)) (HornBinderRules.under_body 2 hi H)
  exact point (HornBinderRules.zf_body 2 hZ H) (old 2 w) (old 2 n) (slot 2 0) (slot 2 1) hw2 hi2 (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.PacketBytesExecutionDomain
