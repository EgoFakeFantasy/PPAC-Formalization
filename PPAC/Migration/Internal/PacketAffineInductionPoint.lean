import PPAC.Migration.Internal.PacketAffineInductionPredecessor

/-! Base and successor correctness compare the actual Packet trace membership to affine arithmetic. -/
namespace PPAC.Migration.Internal.PacketAffineInductionPoint
open Source SourceAlgebra SourceLogic OmegaSyntax PacketAffineInductionSyntax PacketAffineRootSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem no_empty_predecessor {m} {Γ : Context m} (wide : Bool) (w B V d z n : Fin m)
    (hz : Derives Γ (empty z)) (hp : Derives Γ (predecessor wide w B V d z n)) : Derives Γ .bot := by
  let P := predecessorBody wide w B V d z n
  let Δ := Context.add P (HornBinderSyntax.raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 P _ hp
  have hz2 := of_eq (empty_rename z (HornBinderSyntax.old 2)) (HornBinderRules.under_body 2 hz P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  exact .impE (OmegaStructureAlgebra.successor_not_empty (HornBinderSyntax.old 2 z) (HornBinderSyntax.slot 2 0) (.conjL hP)) hz2

theorem zero {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B V d z n r : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hv : Derives Γ (PacketTraceCore.value w V)) (hz : Derives Γ (empty z))
    (hr : Derives Γ (PacketHornAffineSyntax.row wide w d z n r)) :
    Derives Γ ((Formula.mem r V).iff (PacketAffineSyntax.affine w B d z n)) := by
  have hR := PacketAffineRootEquation.member_iff hZ wide w B V d z n r hw hB hv hr
  have hBN := SyntaxNumerals.range hZ (PacketAffineRuleData.radix wide) w B hw hB
  have hA := PacketAffineZero.zero_iff hZ w B d z n hw hBN hz
  apply Derives.conjI
  · apply Derives.impI
    have hc := Derives.impE (add (.conjL hR) _) (.hyp (Or.inl rfl))
    apply Derives.disjE hc
    · exact .impE (add (add (.conjR hA) _) _) (.conjR (.hyp (Or.inl rfl)))
    · exact .botE (no_empty_predecessor wide w B V d z n (add (add hz _) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    have hD := Derives.impE (add (.conjL hA) _) (.hyp (Or.inl rfl))
    exact .impE (add (.conjR hR) _) (.disjL (.conjI (add hz _) hD))

theorem successor {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B V d t s n r : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hv : Derives Γ (PacketTraceCore.value w V)) (ht : Derives Γ (.mem t w))
    (hI : Derives Γ (correct wide w B V t)) (hs : Derives Γ (successor s t))
    (hr : Derives Γ (PacketHornAffineSyntax.row wide w d s n r)) :
    Derives Γ ((Formula.mem r V).iff (PacketAffineSyntax.affine w B d s n)) := by
  have hR := PacketAffineRootEquation.member_iff hZ wide w B V d s n r hw hB hv hr
  apply Derives.conjI
  · apply Derives.impI
    have hc := Derives.impE (add (.conjL hR) _) (.hyp (Or.inl rfl))
    apply Derives.disjE hc
    · exact .botE (.impE (add (add (OmegaStructureAlgebra.successor_not_empty s t hs) _) _) (.conjL (.hyp (Or.inl rfl))))
    · exact PacketAffineInductionPredecessor.sound (ZFContext.add (ZFContext.add hZ _) _) wide w B V d t s n
        (add (add hw _) _) (add (add ht _) _) (add (add hI _) _) (add (add hs _) _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    have hp := PacketAffineInductionPredecessor.complete (ZFContext.add hZ _) wide w B V d t s n
      (add hw _) (add ht _) (add hI _) (add hs _) (.hyp (Or.inl rfl))
    exact .impE (add (.conjR hR) _) (.disjR hp)

end PPAC.Migration.Internal.PacketAffineInductionPoint
