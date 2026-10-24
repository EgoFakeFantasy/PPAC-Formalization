import PPAC.Migration.Internal.PacketDivisionSyntax

/-! Exact internal increment and carry transitions; quotient and remainder are never host naturals. -/
namespace PPAC.Migration.Internal.PacketDivisionTransitions
open Source SourceAlgebra SourceLogic OmegaSyntax PacketAffineSyntax PacketAffineCore ZFArithmetic
open SyntaxRenameQuerySyntax (of_eq)

theorem increment {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d q n s e : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (affine w B d q n))
    (hs : Derives Γ (successor s n)) (he : Derives Γ (successor e d)) (hb : Derives Γ (.mem e B)) :
    Derives Γ (affine w B e q s) := by
  let P := equationBody w B d q n
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (equation_of_affine w B d q n ha)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have ha1 := of_eq (affine_rename w B d q n Fin.castSucc) (under ha P)
  have hs1 := of_eq (successor_rename s n Fin.castSucc) (under hs P)
  have he1 := of_eq (successor_rename e d Fin.castSucc) (under he P)
  have hb1 : Derives Δ (.mem e.castSucc B.castSucc) := under hb P
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hBN := radix_guard _ _ _ _ _ ha1
  have hdN := digit_natural hZ1 _ _ _ _ _ hw1 ha1
  have hpN := mul_range hZ1 w.castSucc B.castSucc q.castSucc (Fin.last m) hw1 (.conjL hP)
  have heN := StructuralListTraceOrder.member_member hZ1 w.castSucc e.castSucc B.castSucc hw1 hBN hb1
  have hnS := OmegaStructureAlgebra.successor_member w.castSucc s.castSucc n.castSucc (ZFContext.arithmetic hZ1).base.extensionality hw1
    (output_guard _ _ _ _ _ ha1) hs1
  have hpd := add_commute hZ1 w.castSucc d.castSucc (Fin.last m) n.castSucc hw1 hdN hpN (.conjR hP)
  have hpe := add_succ_backward hZ1 w.castSucc (Fin.last m) d.castSucc e.castSucc n.castSucc s.castSucc hw1 hpN hdN he1 hpd hs1
  have hep := add_commute hZ1 w.castSucc (Fin.last m) e.castSucc s.castSucc hw1 hpN heN hpe
  exact of_eq (affine_rename w B e q s Fin.castSucc).symm
    (intro_affine w.castSucc B.castSucc e.castSucc q.castSucc s.castSucc (Fin.last m) hBN hb1
      (tail_guard _ _ _ _ _ ha1) hnS (.conjL hP) hep)

theorem carry {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d q n s Q z : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (affine w B d q n)) (hs : Derives Γ (successor s n))
    (hB : Derives Γ (successor B d)) (hQ : Derives Γ (successor Q q)) (hz : Derives Γ (empty z))
    (hzB : Derives Γ (.mem z B)) : Derives Γ (affine w B z Q s) := by
  let P := equationBody w B d q n
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (equation_of_affine w B d q n ha)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have ha1 := of_eq (affine_rename w B d q n Fin.castSucc) (under ha P)
  have hs1 := of_eq (successor_rename s n Fin.castSucc) (under hs P)
  have hB1 := of_eq (successor_rename B d Fin.castSucc) (under hB P)
  have hQ1 := of_eq (successor_rename Q q Fin.castSucc) (under hQ P)
  have hz1 := of_eq (empty_rename z Fin.castSucc) (under hz P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hBN := radix_guard _ _ _ _ _ ha1
  have hdN := digit_natural hZ1 _ _ _ _ _ hw1 ha1
  have hqN := tail_guard _ _ _ _ _ ha1
  have hpN := mul_range hZ1 w.castSucc B.castSucc q.castSucc (Fin.last m) hw1 (.conjL hP)
  have hsN := OmegaStructureAlgebra.successor_member w.castSucc s.castSucc n.castSucc (ZFContext.arithmetic hZ1).base.extensionality hw1
    (output_guard _ _ _ _ _ ha1) hs1
  have hQN := OmegaStructureAlgebra.successor_member w.castSucc Q.castSucc q.castSucc (ZFContext.arithmetic hZ1).base.extensionality hw1 hqN hQ1
  have hpd := add_commute hZ1 w.castSucc d.castSucc (Fin.last m) n.castSucc hw1 hdN hpN (.conjR hP)
  have hpB := add_succ_backward hZ1 w.castSucc (Fin.last m) d.castSucc B.castSucc n.castSucc s.castSucc hw1 hpN hdN hB1 hpd hs1
  have hProd := mul_succ_backward hZ1 w.castSucc B.castSucc q.castSucc Q.castSucc (Fin.last m) s.castSucc hw1 hBN hqN hQ1 (.conjL hP) hpB
  have hSum := NaturalArithmeticBounds.add_zero_left hZ1 w.castSucc z.castSucc s.castSucc hw1 hz1 hsN
  exact of_eq (affine_rename w B z Q s Fin.castSucc).symm
    (intro_affine w.castSucc B.castSucc z.castSucc Q.castSucc s.castSucc s.castSucc hBN (under hzB P) hQN hsN hProd hSum)

end PPAC.Migration.Internal.PacketDivisionTransitions
