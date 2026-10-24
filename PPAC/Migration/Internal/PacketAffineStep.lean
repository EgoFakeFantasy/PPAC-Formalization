import PPAC.Migration.Internal.PacketAffineFiber

/-! Exact forward/backward successor transitions of bounded affine Packet values. -/
namespace PPAC.Migration.Internal.PacketAffineStep
open Source SourceAlgebra SourceLogic OmegaSyntax PacketAffineSyntax PacketAffineCore ZFArithmetic
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem advance {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d t a s n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (affine w B d t a)) (hs : Derives Γ (successor s t))
    (hn : Derives Γ (NaturalAdditionSyntax.sum w a B n)) : Derives Γ (affine w B d s n) := by
  have hsN := OmegaStructureAlgebra.successor_member w s t (ZFContext.arithmetic hZ).base.extensionality hw (tail_guard w B d t a ha) hs
  have hnN := add_range hZ w a B n hw (output_guard w B d t a ha) hn
  let P := equationBody w B d t a
  let Ξ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (equation_of_affine w B d t a ha)
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have ha1 := of_eq (affine_rename w B d t a Fin.castSucc) (under ha P)
  have hpN := mul_range hZ1 w.castSucc B.castSucc t.castSucc (Fin.last m) hw1 (.conjL hP)
  have he := add_exists hZ1 w.castSucc (Fin.last m) B.castSucc hw1 hpN (radix_guard _ _ _ _ _ ha1)
  let Q := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (NaturalAdditionSyntax.sum w.castSucc.castSucc (Fin.last m).castSucc B.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add Q (Context.image Formula.raise Ξ)
  apply Derives.exE (p := Q) he
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 Q
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Q)
  have ha2 := of_eq (affine_rename w.castSucc B.castSucc d.castSucc t.castSucc a.castSucc Fin.castSucc) (under ha1 Q)
  have hs2 : Derives Δ (successor s.castSucc.castSucc t.castSucc.castSucc) := of_eq
    (by simp only [Formula.raise, successor_rename]) (under (under hs P) Q)
  have hn2 : Derives Δ (NaturalAdditionSyntax.sum w.castSucc.castSucc a.castSucc.castSucc B.castSucc.castSucc n.castSucc.castSucc) := of_eq
    (by simp only [Formula.raise, NaturalAdditionSyntax.sum_rename]) (under (under hn P) Q)
  have hp2 := of_eq (NaturalMultiplicationSyntax.product_rename w.castSucc B.castSucc t.castSucc (Fin.last m) Fin.castSucc) (under (.conjL hP) Q)
  have hv2 := of_eq (NaturalAdditionSyntax.sum_rename w.castSucc d.castSucc (Fin.last m) a.castSucc Fin.castSucc) (under (.conjR hP) Q)
  have hpN2 : Derives Δ (.mem (Fin.last m).castSucc w.castSucc.castSucc) := under hpN Q
  have hB2 := radix_guard _ _ _ _ _ ha2
  have hdN2 := digit_natural hZ2 _ _ _ _ _ hw2 ha2
  have ht2 := tail_guard _ _ _ _ _ ha2
  have hpNew := mul_succ_backward hZ2 w.castSucc.castSucc B.castSucc.castSucc t.castSucc.castSucc s.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) hw2 hB2 ht2 hs2 hp2 (.conjR hQ)
  have hvNew := add_associate hZ2 w.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc
    B.castSucc.castSucc (Fin.last (m+1)) n.castSucc.castSucc hw2 hdN2 hpN2 hB2 hv2 (.conjR hQ) hn2
  have hsN2 : Derives Δ (.mem s.castSucc.castSucc w.castSucc.castSucc) := under (under hsN P) Q
  have hnN2 : Derives Δ (.mem n.castSucc.castSucc w.castSucc.castSucc) := under (under hnN P) Q
  have ho := intro_affine w.castSucc.castSucc B.castSucc.castSucc d.castSucc.castSucc s.castSucc.castSucc n.castSucc.castSucc
    (Fin.last (m+1)) hB2 (digit_guard _ _ _ _ _ ha2) hsN2 hnN2 hpNew hvNew
  exact of_eq (by simp only [Formula.raise, affine_rename]) ho

theorem retreat {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d t s n : Fin m)
    (hw : Derives Γ (omega w)) (ht : Derives Γ (.mem t w)) (hs : Derives Γ (successor s t))
    (ha : Derives Γ (affine w B d s n)) : Derives Γ (stepCase w B d s n) := by
  let P := equationBody w B d s n
  let Ξ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (equation_of_affine w B d s n ha)
  have hP : Derives Ξ P := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have ha1 := of_eq (affine_rename w B d s n Fin.castSucc) (under ha P)
  have ht1 : Derives Ξ (.mem t.castSucc w.castSucc) := under ht P
  have heP := mul_exists hZ1 w.castSucc B.castSucc t.castSucc hw1 (radix_guard _ _ _ _ _ ha1) ht1
  let Q := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (NaturalMultiplicationSyntax.product w.castSucc.castSucc B.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1)))
  let Δ := Context.add Q (Context.image Formula.raise Ξ)
  apply Derives.exE (p := Q) heP
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 Q
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 Q)
  have ha2 := of_eq (affine_rename w.castSucc B.castSucc d.castSucc s.castSucc n.castSucc Fin.castSucc) (under ha1 Q)
  have ht2 : Derives Δ (.mem t.castSucc.castSucc w.castSucc.castSucc) := under ht1 Q
  have hs2 : Derives Δ (successor s.castSucc.castSucc t.castSucc.castSucc) := of_eq
    (by simp only [Formula.raise, successor_rename]) (under (under hs P) Q)
  have hp2 := of_eq (NaturalMultiplicationSyntax.product_rename w.castSucc B.castSucc s.castSucc (Fin.last m) Fin.castSucc) (under (.conjL hP) Q)
  have hv2 := of_eq (NaturalAdditionSyntax.sum_rename w.castSucc d.castSucc (Fin.last m) n.castSucc Fin.castSucc) (under (.conjR hP) Q)
  have hB2 := radix_guard _ _ _ _ _ ha2
  have hdN2 := digit_natural hZ2 _ _ _ _ _ hw2 ha2
  have hProdAdd := mul_succ_forward hZ2 w.castSucc.castSucc B.castSucc.castSucc t.castSucc.castSucc s.castSucc.castSucc
    (Fin.last (m+1)) (Fin.last m).castSucc hw2 hB2 ht2 hs2 (.conjR hQ) hp2
  have heA := add_exists hZ2 w.castSucc.castSucc d.castSucc.castSucc (Fin.last (m+1)) hw2 hdN2 (.conjL hQ)
  let R := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
    (NaturalAdditionSyntax.sum w.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))
  let Θ := Context.add R (Context.image Formula.raise Δ)
  apply Derives.exE (p := R) heA
  have hR : Derives Θ R := .hyp (Or.inl rfl)
  have hZ3 := ZFContext.under hZ2 R
  have hw3 := of_eq (omega_rename w.castSucc.castSucc Fin.castSucc) (under hw2 R)
  have ha3 := of_eq (affine_rename w.castSucc.castSucc B.castSucc.castSucc d.castSucc.castSucc s.castSucc.castSucc n.castSucc.castSucc Fin.castSucc) (under ha2 R)
  have ht3 : Derives Θ (.mem t.castSucc.castSucc.castSucc w.castSucc.castSucc.castSucc) := under ht2 R
  have hs3 := of_eq (successor_rename s.castSucc.castSucc t.castSucc.castSucc Fin.castSucc) (under hs2 R)
  have hPrevProd := of_eq (NaturalMultiplicationSyntax.product_rename w.castSucc.castSucc B.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1)) Fin.castSucc) (under (.conjR hQ) R)
  have hPrevNat : Derives Θ (.mem (Fin.last (m+1)).castSucc w.castSucc.castSucc.castSucc) := under (Derives.conjL hQ) R
  have hProdAdd3 := of_eq (NaturalAdditionSyntax.sum_rename w.castSucc.castSucc (Fin.last (m+1)) B.castSucc.castSucc (Fin.last m).castSucc Fin.castSucc) (under hProdAdd R)
  have hv3 := of_eq (NaturalAdditionSyntax.sum_rename w.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc Fin.castSucc) (under hv2 R)
  have hB3 := radix_guard _ _ _ _ _ ha3
  have hdN3 := digit_natural hZ3 _ _ _ _ _ hw3 ha3
  have hOld := intro_affine w.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc
    (Fin.last (m+2)) (Fin.last (m+1)).castSucc hB3 (digit_guard _ _ _ _ _ ha3) ht3 (.conjL hR) hPrevProd (.conjR hR)
  have hLast := add_unassociate hZ3 w.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))
    B.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc n.castSucc.castSucc.castSucc hw3 hdN3 hPrevNat hB3 (.conjR hR) hProdAdd3 hv3
  have ho := intro_step w.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc
    n.castSucc.castSucc.castSucc t.castSucc.castSucc.castSucc (Fin.last (m+2)) hs3 hOld hLast
  exact of_eq (by simp only [Formula.raise, stepCase_rename]) ho

end PPAC.Migration.Internal.PacketAffineStep
