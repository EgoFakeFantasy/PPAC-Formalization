import PPAC.Migration.Internal.PacketTokenCanonicalLiterals

/-! Only omega remains in the exact original Tok versus independent canonical byte Prefix agreement, including invalid candidates. -/
namespace PPAC.Migration.Internal.PacketTokenCanonicalLaws
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PacketVarintPrefixSyntax PacketTokenCanonicalSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem actual_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (agreement w n t a) := by
  apply Derives.conjI
  · apply Derives.impI
    let H := PacketTokenAcceptedSyntax.accepted w n t a
    have hZ1 := ZFContext.add hZ H
    have hH : Derives (Context.add H Γ) H := .hyp (Or.inl rfl)
    have hn := HornExprSyntax.environmentNat_at w (SyntaxAtomSyntax.three n t a) (PacketTokenAcceptedNatural.accepted_environment hZ1 w n t a (add hw H) hH) 0
    have hp := PacketTokenCanonicalLiterals.at_code hZ1 w n (add hw H) hn
    exact .impE (.conjL (property_at w n t a hp)) hH
  · apply Derives.impI
    let H := prefixCode w n t a
    have hZ1 := ZFContext.add hZ H
    have hH : Derives (Context.add H Γ) H := .hyp (Or.inl rfl)
    have hn := Derives.conjL (PacketVarintPrefixDomain.domain w n t a hH)
    have hp := PacketTokenCanonicalLiterals.at_code hZ1 w n (add hw H) hn
    exact .impE (.conjR (property_at w n t a hp)) hH

theorem all_law {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) (hw : Derives Γ (omega w)) : Derives Γ (allLaw w) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.allI
  have hw3 := of_eq (omega_rename w (old 3)) (HornBinderRules.under_many 3 hw)
  exact actual_iff (HornBinderRules.zf_many 3 hZ) (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2) hw3

theorem prefix_at_given_list {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n s t a : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (PacketVarintSyntax.canonical w n s)) (hp : Derives Γ (prefixCode w n t a)) : Derives Γ (PacketBytesTraceSyntax.bytes w s t a) := by
  let R := PacketVarintPrefixSyntax.body w n t a
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hp
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hc1 := of_eq (PacketVarintSyntax.canonical_rename w n s Fin.castSucc) (under hc R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have he := PacketVarintExecutionLiterals.list_unique hZ1 w.castSucc n.castSucc s.castSucc (Fin.last m) hw1 hc1 (.conjL hR)
  simpa only [Formula.raise,PacketBytesTraceSyntax.bytes_rename] using PacketBytesExecutionTransport.input_subst w.castSucc (Fin.last m) t.castSucc a.castSucc s.castSucc (eq_symm he) (.conjR hR)

theorem at_canonical_list {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n s t a : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (PacketVarintSyntax.canonical w n s)) :
    Derives Γ ((PacketTokenAcceptedSyntax.accepted w n t a).iff (PacketBytesTraceSyntax.bytes w s t a)) := by
  apply Derives.conjI
  · apply Derives.impI
    have hp := Derives.impE (.conjL (actual_iff (ZFContext.add hZ _) w n t a (add hw _))) (.hyp (Or.inl rfl))
    exact prefix_at_given_list (ZFContext.add hZ _) w n s t a (add hw _) (add hc _) hp
  · apply Derives.impI
    exact .impE (.conjR (actual_iff (ZFContext.add hZ _) w n t a (add hw _))) (intro_prefix w n t a s (add hc _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.PacketTokenCanonicalLaws
