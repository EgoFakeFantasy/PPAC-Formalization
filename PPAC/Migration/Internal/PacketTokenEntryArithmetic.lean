import PPAC.Migration.Internal.PacketTokenNatural

/-! Canonical Packet entry membership gives previously proved arithmetic, without new IH premises. -/
namespace PPAC.Migration.Internal.PacketTokenEntryArithmetic
open Source SourceAlgebra SourceLogic OmegaSyntax PacketTokenSyntax PacketAffineSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem affine_of_entry {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B V d q n : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (PacketAffineRuleData.radix wide) B))
    (hv : Derives Γ (PacketTraceCore.value w V)) (he : Derives Γ (tagEntry (PacketAffineRuleData.relation wide) w V d q n)) :
    Derives Γ (affine w B d q n) := by
  let P := (PacketHornAffineSyntax.row wide w.castSucc d.castSucc q.castSucc n.castSucc (Fin.last m)).conj (.mem (Fin.last m) V.castSucc)
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) he
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have hB1 := of_eq (SyntaxNumeralSyntax.numeral_rename (PacketAffineRuleData.radix wide) B Fin.castSucc) (under hB P)
  have hv1 := of_eq (PacketTraceCore.value_rename w V Fin.castSucc) (under hv P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  exact of_eq (affine_rename w B d q n Fin.castSucc).symm
    (.impE (.conjL (PacketAffineInduction.membership_iff (ZFContext.under hZ P) wide w.castSucc B.castSucc V.castSucc
      d.castSucc q.castSucc n.castSucc (Fin.last m) hw1 hB1 hv1 (.conjL hP))) (.conjR hP))

theorem digit_below_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d q n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (affine w B d q n)) : Derives Γ (NaturalAdditionBounds.below d n) := by
  let P := equationBody w B d q n
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (PacketAffineCore.equation_of_affine w B d q n ha)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have ha1 := of_eq (affine_rename w B d q n Fin.castSucc) (under ha P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  exact of_eq (NaturalAdditionBounds.below_rename d n Fin.castSucc).symm
    (GodelPairArithmetic.sum_left_bound hZ1 w.castSucc d.castSucc (Fin.last m) n.castSucc hw1
      (PacketAffineCore.digit_natural hZ1 _ _ _ _ _ hw1 ha1) (ZFArithmetic.mul_range hZ1 _ _ _ _ hw1 (.conjL hP)) (.conjR hP))

end PPAC.Migration.Internal.PacketTokenEntryArithmetic
