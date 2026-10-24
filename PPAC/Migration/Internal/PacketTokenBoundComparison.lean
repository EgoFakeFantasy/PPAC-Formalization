import PPAC.Migration.Internal.ObjectPacketTokenExecution

/-! Two-coordinate object arithmetic compares the real affine input with its recursive byte output. -/
namespace PPAC.Migration.Internal.PacketTokenBoundComparison
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic
open NaturalAdditionSyntax (sum sum_rename)
open NaturalMultiplicationSyntax (product product_rename)
open NaturalAdditionBounds (below below_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem sum_compare {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w d y p r n a : Fin m)
    (hw : Derives Γ (omega w)) (hd : Derives Γ (.mem d w)) (hy : Derives Γ (.mem y w))
    (hp : Derives Γ (.mem p w)) (hr : Derives Γ (.mem r w)) (hn : Derives Γ (sum w d p n)) (ha : Derives Γ (sum w y r a))
    (hdy : Derives Γ (below d y)) (hpr : Derives Γ (below p r)) : Derives Γ (below n a) := by
  let S := (Formula.mem (Fin.last m) w.castSucc).conj (sum w.castSucc y.castSucc p.castSucc (Fin.last m))
  let Δ := Context.add S (Context.image Formula.raise Γ)
  apply Derives.exE (p := S) (add_exists hZ w y p hw hy hp)
  have hZ1 := ZFContext.under hZ S
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw S)
  have hn1 := of_eq (sum_rename w d p n Fin.castSucc) (under hn S)
  have ha1 := of_eq (sum_rename w y r a Fin.castSucc) (under ha S)
  have hdy1 := of_eq (below_rename d y Fin.castSucc) (under hdy S)
  have hpr1 := of_eq (below_rename p r Fin.castSucc) (under hpr S)
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have hns := NaturalAdditionMonotone.monotone hZ1 w.castSucc d.castSucc y.castSucc p.castSucc n.castSucc (Fin.last m)
    hw1 (under hd S) (under hy S) (under hp S) hn1 (.conjR hS) hdy1
  have hsa := Derives.impE (.conjL (NaturalAdditionMonotone.left_weak_iff hZ1 w.castSucc p.castSucc r.castSucc y.castSucc (Fin.last m) a.castSucc
    hw1 (under hp S) (under hr S) (under hy S) (.conjR hS) ha1)) hpr1
  exact of_eq (below_rename n a Fin.castSucc).symm
    (NaturalOrderBasic.transitive hZ1 w.castSucc n.castSucc (Fin.last m) a.castSucc hw1
      (add_range hZ1 _ _ _ _ hw1 (under hy S) ha1) hns hsa)

theorem product_compare {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C q u p r : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (.mem B w)) (hC : Derives Γ (.mem C w))
    (hq : Derives Γ (.mem q w)) (hu : Derives Γ (.mem u w)) (hp : Derives Γ (product w B q p)) (hr : Derives Γ (product w C u r))
    (hBC : Derives Γ (below B C)) (hqu : Derives Γ (below q u)) : Derives Γ (below p r) := by
  let S := (Formula.mem (Fin.last m) w.castSucc).conj (product w.castSucc C.castSucc q.castSucc (Fin.last m))
  let Δ := Context.add S (Context.image Formula.raise Γ)
  apply Derives.exE (p := S) (mul_exists hZ w C q hw hC hq)
  have hZ1 := ZFContext.under hZ S
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw S)
  have hp1 := of_eq (product_rename w B q p Fin.castSucc) (under hp S)
  have hr1 := of_eq (product_rename w C u r Fin.castSucc) (under hr S)
  have hBC1 := of_eq (below_rename B C Fin.castSucc) (under hBC S)
  have hqu1 := of_eq (below_rename q u Fin.castSucc) (under hqu S)
  have hS : Derives Δ S := .hyp (Or.inl rfl)
  have hps := NaturalMultiplicationMonotone.monotone hZ1 w.castSucc B.castSucc C.castSucc q.castSucc p.castSucc (Fin.last m)
    hw1 (under hB S) (under hC S) (under hq S) hp1 (.conjR hS) hBC1
  have hsr := NaturalMultiplicationOrderLaws.left_monotone hZ1 w.castSucc q.castSucc u.castSucc C.castSucc (Fin.last m) r.castSucc
    hw1 (under hq S) (under hu S) (under hC S) (.conjR hS) hr1 hqu1
  exact of_eq (below_rename p r Fin.castSucc).symm
    (NaturalOrderBasic.transitive hZ1 w.castSucc p.castSucc (Fin.last m) r.castSucc hw1 (mul_range hZ1 _ _ _ _ hw1 hr1) hps hsr)

theorem affine_compare {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C d q n y u a : Fin m)
    (hw : Derives Γ (omega w)) (h0 : Derives Γ (PacketAffineSyntax.affine w B d q n))
    (h1 : Derives Γ (PacketAffineSyntax.affine w C y u a)) (hBC : Derives Γ (below B C))
    (hdy : Derives Γ (below d y)) (hqu : Derives Γ (below q u)) : Derives Γ (below n a) := by
  let P := PacketAffineSyntax.equationBody w B d q n
  let ΓP := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) (PacketAffineCore.equation_of_affine w B d q n h0)
  have h11 := of_eq (PacketAffineSyntax.affine_rename w C y u a Fin.castSucc) (under h1 P)
  let R := PacketAffineSyntax.equationBody w.castSucc C.castSucc y.castSucc u.castSucc a.castSucc
  let Δ := Context.add R (Context.image Formula.raise ΓP)
  apply Derives.exE (p := R) (PacketAffineCore.equation_of_affine _ _ _ _ _ h11)
  have hZ2 := ZFContext.under (ZFContext.under hZ P) R
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (under (under hw P) R)
  have h02 : Derives Δ (PacketAffineSyntax.affine w.castSucc.castSucc B.castSucc.castSucc d.castSucc.castSucc q.castSucc.castSucc n.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,PacketAffineSyntax.affine_rename]) (under (under h0 P) R)
  have h12 := of_eq (PacketAffineSyntax.affine_rename w.castSucc C.castSucc y.castSucc u.castSucc a.castSucc Fin.castSucc) (under h11 R)
  have hBC2 : Derives Δ (below B.castSucc.castSucc C.castSucc.castSucc) := of_eq (by simp only [Formula.raise,below_rename]) (under (under hBC P) R)
  have hdy2 : Derives Δ (below d.castSucc.castSucc y.castSucc.castSucc) := of_eq (by simp only [Formula.raise,below_rename]) (under (under hdy P) R)
  have hqu2 : Derives Δ (below q.castSucc.castSucc u.castSucc.castSucc) := of_eq (by simp only [Formula.raise,below_rename]) (under (under hqu P) R)
  have hP : Derives ΓP P := .hyp (Or.inl rfl)
  have hP2 : Derives Δ ((product w.castSucc.castSucc B.castSucc.castSucc q.castSucc.castSucc (Fin.last m).castSucc).conj
      (sum w.castSucc.castSucc d.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc)) :=
    of_eq (by simp only [P,PacketAffineSyntax.equationBody,Formula.raise,Formula.rename,product_rename,sum_rename]) (under hP R)
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hpr := product_compare hZ2 w.castSucc.castSucc B.castSucc.castSucc C.castSucc.castSucc q.castSucc.castSucc u.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) hw2 (PacketAffineCore.radix_guard _ _ _ _ _ h02) (PacketAffineCore.radix_guard _ _ _ _ _ h12)
    (PacketAffineCore.tail_guard _ _ _ _ _ h02) (PacketAffineCore.tail_guard _ _ _ _ _ h12) (.conjL hP2) (.conjL hR) hBC2 hqu2
  have ho := sum_compare hZ2 w.castSucc.castSucc d.castSucc.castSucc y.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
    n.castSucc.castSucc a.castSucc.castSucc hw2 (PacketAffineCore.digit_natural hZ2 _ _ _ _ _ hw2 h02)
    (PacketAffineCore.digit_natural hZ2 _ _ _ _ _ hw2 h12) (mul_range hZ2 _ _ _ _ hw2 (.conjL hP2)) (mul_range hZ2 _ _ _ _ hw2 (.conjL hR))
    (.conjR hP2) (.conjR hR) hdy2 hpr
  exact of_eq (by simp only [Formula.raise,below_rename]) ho

end PPAC.Migration.Internal.PacketTokenBoundComparison
