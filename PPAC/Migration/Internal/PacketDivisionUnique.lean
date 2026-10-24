import PPAC.Migration.Internal.PacketDivisionBand

/-! Distinct quotient bands are disjoint; equal quotients reduce remainder equality to object addition cancellation. -/
namespace PPAC.Migration.Internal.PacketDivisionUnique
open Source SourceAlgebra SourceLogic OmegaSyntax PacketAffineSyntax PacketAffineCore ZFArithmetic
open NaturalMultiplicationSyntax (product product_rename)
open NaturalAdditionBounds (below below_rename)
open SyntaxRenameQuerySyntax (of_eq)

theorem quotient_not_less {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d q e p n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (affine w B d q n)) (hb : Derives Γ (affine w B e p n))
    (hl : Derives Γ (.mem q p)) : Derives Γ .bot := by
  have hE := OriginalBinderStepSyntax.successor_exists w q hw (tail_guard _ _ _ _ _ ha)
  let E := (Formula.mem (Fin.last m) w.castSucc).conj (successor (Fin.last m) q.castSucc)
  let ΓE := Context.add E (Context.image Formula.raise Γ)
  apply Derives.exE (p := E) hE
  have hZE := ZFContext.under hZ E
  have hwE := of_eq (omega_rename w Fin.castSucc) (under hw E)
  have haE := of_eq (affine_rename w B d q n Fin.castSucc) (under ha E)
  have hbE := of_eq (affine_rename w B e p n Fin.castSucc) (under hb E)
  have hlE : Derives ΓE (.mem q.castSucc p.castSucc) := under hl E
  have hEv : Derives ΓE E := .hyp (Or.inl rfl)
  have hQp := GodelPairArithmetic.successor_below hZE w.castSucc q.castSucc p.castSucc (Fin.last m)
    hwE (tail_guard _ _ _ _ _ haE) (tail_guard _ _ _ _ _ hbE) (.conjR hEv) hlE
  have hY := mul_exists hZE w.castSucc B.castSucc (Fin.last m) hwE (radix_guard _ _ _ _ _ haE) (.conjL hEv)
  let Y := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj
    (product w.castSucc.castSucc B.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let ΓY := Context.add Y (Context.image Formula.raise ΓE)
  apply Derives.exE (p := Y) hY
  have hZY := ZFContext.under hZE Y
  have hwY := of_eq (omega_rename w.castSucc Fin.castSucc) (under hwE Y)
  have hbY := of_eq (affine_rename w.castSucc B.castSucc e.castSucc p.castSucc n.castSucc Fin.castSucc) (under hbE Y)
  have hZprod := mul_exists hZY w.castSucc.castSucc B.castSucc.castSucc p.castSucc.castSucc hwY
    (radix_guard _ _ _ _ _ hbY) (tail_guard _ _ _ _ _ hbY)
  let Z := (Formula.mem (Fin.last (m+2)) w.castSucc.castSucc.castSucc).conj
    (product w.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc (Fin.last (m+2)))
  let Δ := Context.add Z (Context.image Formula.raise ΓY)
  apply Derives.exE (p := Z) hZprod
  have hZ3 := ZFContext.under hZY Z
  have lift {f : Formula m} (hf : Derives Γ f) : Derives Δ f.raise.raise.raise := under (under (under hf E) Y) Z
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (lift hw)
  have ha3 : Derives Δ (affine w.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc q.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,affine_rename]) (lift ha)
  have hb3 : Derives Δ (affine w.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,affine_rename]) (lift hb)
  have hE3 : Derives Δ ((Formula.mem (Fin.last m).castSucc.castSucc w.castSucc.castSucc.castSucc).conj
      (successor (Fin.last m).castSucc.castSucc q.castSucc.castSucc.castSucc)) := by
    simpa only [E,Formula.raise,Formula.rename,successor_rename] using under (under hEv Y) Z
  have hYv : Derives ΓY Y := .hyp (Or.inl rfl)
  have hY3 : Derives Δ ((Formula.mem (Fin.last (m+1)).castSucc w.castSucc.castSucc.castSucc).conj
      (product w.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc)) := by
    simpa only [Y,Formula.raise,Formula.rename,product_rename] using under hYv Z
  have hQp3 : Derives Δ (below (Fin.last m).castSucc.castSucc p.castSucc.castSucc.castSucc) :=
    of_eq (by simp only [Formula.raise,below_rename]) (under (under hQp Y) Z)
  have hZv : Derives Δ Z := .hyp (Or.inl rfl)
  have hnY := PacketDivisionBand.upper hZ3 w.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc d.castSucc.castSucc.castSucc
    q.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc hw3 ha3 (.conjR hE3) (.conjR hY3)
  have hYZ := NaturalMultiplicationOrderLaws.left_monotone hZ3 w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc
    p.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)) hw3
    (.conjL hE3) (tail_guard _ _ _ _ _ hb3) (radix_guard _ _ _ _ _ ha3) (.conjR hY3) (.conjR hZv) hQp3
  have hZn := PacketDivisionBand.lower hZ3 w.castSucc.castSucc.castSucc B.castSucc.castSucc.castSucc e.castSucc.castSucc.castSucc
    p.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last (m+2)) hw3 hb3 (.conjR hZv)
  have hYn := NaturalOrderBasic.transitive hZ3 w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))
    n.castSucc.castSucc.castSucc hw3 (output_guard _ _ _ _ _ ha3) hYZ hZn
  exact NaturalOrderBasic.below_not_reverse hZ3 w.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc n.castSucc.castSucc.castSucc
    hw3 (.conjL hY3) hYn hnY

theorem quotient_equal {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d q e p n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (affine w B d q n)) (hb : Derives Γ (affine w B e p n)) :
    Derives Γ (.equal q p) := by
  apply Derives.disjE (NaturalOrderBasic.compare hZ w q p hw (tail_guard _ _ _ _ _ ha) (tail_guard _ _ _ _ _ hb))
  · exact .hyp (Or.inl rfl)
  · apply Derives.disjE (.hyp (Or.inl rfl))
    · exact .botE (quotient_not_less (ZFContext.add (ZFContext.add hZ _) _) w B d q e p n
        (add (add hw _) _) (add (add ha _) _) (add (add hb _) _) (.hyp (Or.inl rfl)))
    · exact .botE (quotient_not_less (ZFContext.add (ZFContext.add hZ _) _) w B e p d q n
        (add (add hw _) _) (add (add hb _) _) (add (add ha _) _) (.hyp (Or.inl rfl)))

theorem digit_same_quotient {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d e q n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (affine w B d q n)) (hb : Derives Γ (affine w B e q n)) :
    Derives Γ (.equal d e) := by
  have he := mul_exists hZ w B q hw (radix_guard _ _ _ _ _ ha) (tail_guard _ _ _ _ _ ha)
  let P := (Formula.mem (Fin.last m) w.castSucc).conj (product w.castSucc B.castSucc q.castSucc (Fin.last m))
  let Δ := Context.add P (Context.image Formula.raise Γ)
  apply Derives.exE (p := P) he
  have hZ1 := ZFContext.under hZ P
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw P)
  have ha1 := of_eq (affine_rename w B d q n Fin.castSucc) (under ha P)
  have hb1 := of_eq (affine_rename w B e q n Fin.castSucc) (under hb P)
  have hP : Derives Δ P := .hyp (Or.inl rfl)
  have hs1 := PacketDivisionBand.sum_at_product hZ1 w.castSucc B.castSucc d.castSucc q.castSucc n.castSucc (Fin.last m) hw1 ha1 (.conjR hP)
  have hs2 := PacketDivisionBand.sum_at_product hZ1 w.castSucc B.castSucc e.castSucc q.castSucc n.castSucc (Fin.last m) hw1 hb1 (.conjR hP)
  exact NaturalAdditionCancellation.cancel_right (ZFContext.arithmetic hZ1) w.castSucc d.castSucc e.castSucc (Fin.last m) n.castSucc
    (ZFContext.recAdd hZ1) (ZFContext.separation hZ1 NaturalAdditionCancellation.matrix) hw1
    (digit_natural hZ1 _ _ _ _ _ hw1 ha1) (digit_natural hZ1 _ _ _ _ _ hw1 hb1) (.conjL hP) hs1 hs2

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B d q e p n : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (affine w B d q n)) (hb : Derives Γ (affine w B e p n)) :
    Derives Γ ((Formula.equal d e).conj (.equal q p)) := by
  have hq := quotient_equal hZ w B d q e p n hw ha hb
  have haP := PacketAffineTransport.tail w B d q n p hq ha
  exact .conjI (digit_same_quotient hZ w B d e p n hw haP hb) hq

end PPAC.Migration.Internal.PacketDivisionUnique
