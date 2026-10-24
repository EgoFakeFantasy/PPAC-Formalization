import PPAC.Migration.Internal.PacketDivisionInduction

/-! Exact internal quotient bands: B*q <= n < B*(q+1), proved from the actual affine witnesses. -/
namespace PPAC.Migration.Internal.PacketDivisionBand
open Source SourceAlgebra SourceLogic OmegaSyntax PacketAffineSyntax PacketAffineCore ZFArithmetic
open NaturalAdditionSyntax (sum sum_rename)
open NaturalMultiplicationSyntax (product product_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem sum_at_product {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d q n p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (affine w B d q n)) (hp : Derives Γ (product w B q p)) :
    Derives Γ (sum w d p n) := by
  let C := equationBody w B d q n
  let Δ := Context.add C (Context.image Formula.raise Γ)
  apply Derives.exE (p := C) (equation_of_affine w B d q n ha)
  have hZ1 := ZFContext.under hZ C
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw C)
  have ha1 := of_eq (affine_rename w B d q n Fin.castSucc) (under ha C)
  have hp1 := of_eq (product_rename w B q p Fin.castSucc) (under hp C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have he := mul_unique hZ1 w.castSucc B.castSucc q.castSucc (Fin.last m) p.castSucc hw1
    (radix_guard _ _ _ _ _ ha1) (tail_guard _ _ _ _ _ ha1) (.conjL hC) hp1
  exact of_eq (sum_rename w d p n Fin.castSucc).symm
    (PacketAffineTransport.sum_right w.castSucc d.castSucc (Fin.last m) n.castSucc p.castSucc he (.conjR hC))

theorem lower {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d q n p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (affine w B d q n)) (hp : Derives Γ (product w B q p)) :
    Derives Γ (NaturalAdditionBounds.below p n) := by
  have hdN := digit_natural hZ w B d q n hw ha
  have hpN := mul_range hZ w B q p hw hp
  have hs := add_commute hZ w d p n hw hdN hpN (sum_at_product hZ w B d q n p hw ha hp)
  exact NaturalAdditionBounds.lower_bound (ZFContext.arithmetic hZ) w p d n (ZFContext.recAdd hZ)
    (ZFContext.separation hZ NaturalAdditionBounds.matrix) hw hpN hdN hs

theorem upper {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d q n Q y : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (affine w B d q n)) (hQ : Derives Γ (successor Q q))
    (hy : Derives Γ (product w B Q y)) : Derives Γ (.mem n y) := by
  have he := mul_exists hZ w B q hw (radix_guard _ _ _ _ _ ha) (tail_guard _ _ _ _ _ ha)
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (product w.castSucc B.castSucc q.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) he
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have ha1 := of_eq (affine_rename w B d q n Fin.castSucc) (under ha P)
  have hQ1 := of_eq (successor_rename Q q Fin.castSucc) (under hQ P)
  have hy1 := of_eq (product_rename w B Q y Fin.castSucc) (under hy P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hBN := radix_guard _ _ _ _ _ ha1
  have hqN := tail_guard _ _ _ _ _ ha1
  have hdN := digit_natural hZ1 _ _ _ _ _ hw1 ha1
  have hs := sum_at_product hZ1 w.castSucc B.castSucc d.castSucc q.castSucc n.castSucc (Fin.last m) hw1 ha1 (.conjR hP)
  have hb := mul_succ_forward hZ1 w.castSucc B.castSucc q.castSucc Q.castSucc (Fin.last m) y.castSucc
    hw1 hBN hqN hQ1 (.conjR hP) hy1
  have hBp := add_commute hZ1 w.castSucc (Fin.last m) B.castSucc y.castSucc hw1 (.conjL hP) hBN hb
  exact NaturalAdditionMonotone.strict_monotone hZ1 w.castSucc d.castSucc B.castSucc (Fin.last m) n.castSucc y.castSucc
    hw1 hdN hBN (.conjL hP) hs hBp (digit_guard _ _ _ _ _ ha1)

end PPAC.Migration.Internal.PacketDivisionBand
