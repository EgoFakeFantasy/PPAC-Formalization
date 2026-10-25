import PPAC.Migration.Internal.StructuralReverseIndexSyntax

/-! Internal reverse positions are symmetric, in range, and unique over every candidate object. -/
namespace PPAC.Migration.Internal.StructuralReverseIndexArithmetic
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralReverseIndexSyntax NaturalAdditionSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem symmetric {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l i j : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (mirror w l i j)) : Derives Γ (mirror w l j i) := by
  let R := witness w.castSucc l.castSucc i.castSucc j.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (.conjR (.conjR hm))
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hi : Derives Δ (.mem i.castSucc w.castSucc) := under (.conjL hm) R
  have hj : Derives Δ (.mem j.castSucc w.castSucc) := under (.conjL (.conjR hm)) R
  have hs := ZFArithmetic.add_commute hZ1 _ _ _ _ hw1 hi hj (.conjL (.conjR hR))
  simpa only [Formula.raise,mirror_rename] using intro_mirror _ _ _ _ _ hj hi (.conjI (.conjL hR) (.conjI hs (.conjR (.conjR hR))))

theorem input_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l i j : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (mirror w l i j)) : Derives Γ (.mem i l) := by
  let R := witness w.castSucc l.castSucc i.castSucc j.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (.conjR (.conjR hm))
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ R
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw R)
  have hi : Derives Δ (.mem i.castSucc w.castSucc) := under (.conjL hm) R
  have hj : Derives Δ (.mem j.castSucc w.castSucc) := under (.conjL (.conjR hm)) R
  have hb := PacketReaderLengthArithmetic.index_bound hZ1 _ _ _ _ hw1 hi hj (.conjL (.conjR hR))
  exact NaturalAdditionBounds.into_successor _ _ _ hb (.conjR (.conjR hR))

theorem output_bound {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l i j : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (mirror w l i j)) : Derives Γ (.mem j l) :=
  input_bound hZ w l j i hw (symmetric hZ w l i j hw hm)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w l i j k : Fin m)
    (hw : Derives Γ (omega w)) (hj : Derives Γ (mirror w l i j)) (hk : Derives Γ (mirror w l i k)) : Derives Γ (.equal j k) := by
  let R := witness w.castSucc l.castSucc i.castSucc j.castSucc (Fin.last m)
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) (.conjR (.conjR hj))
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hk1 := of_eq (mirror_rename w l i k Fin.castSucc) (under hk R)
  let T := witness w.castSucc.castSucc l.castSucc.castSucc i.castSucc.castSucc k.castSucc.castSucc (Fin.last (m+1))
  let Ξ := Context.add T (Context.image Formula.raise Δ)
  apply Derives.exE (p := T) (.conjR (.conjR hk1))
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under (ZFContext.under hZ R) T
  have hw2 : Derives Ξ (omega w.castSucc.castSucc) := of_eq (by simp only [Formula.raise,omega_rename]) (under (under hw R) T)
  have hR2 := of_eq (witness_rename w.castSucc l.castSucc i.castSucc j.castSucc (Fin.last m) Fin.castSucc) (under hR T)
  have hi2 : Derives Ξ (.mem i.castSucc.castSucc w.castSucc.castSucc) := under (under (.conjL hj) R) T
  have hj2 : Derives Ξ (.mem j.castSucc.castSucc w.castSucc.castSucc) := under (under (.conjL (.conjR hj)) R) T
  have hk2 : Derives Ξ (.mem k.castSucc.castSucc w.castSucc.castSucc) := under (.conjL (.conjR hk1)) T
  have he := SyntaxIndexLiftOrder.successor_injective hZ2 _ _ _ _ hw2 (.conjL hR2) (.conjR (.conjR hR2)) (.conjR (.conjR hT))
  have hs := sum_output _ _ _ _ _ he (.conjL (.conjR hR2))
  exact NaturalDifference.unique hZ2 _ _ _ _ _ hw2 hi2 hj2 hk2 hs (.conjL (.conjR hT))

end PPAC.Migration.Internal.StructuralReverseIndexArithmetic
