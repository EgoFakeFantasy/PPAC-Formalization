import PPAC.Migration.Internal.GodelPairBandUnique

/-! 固定平方指标后抵消余数；混合分支由严格和界排除。 -/
namespace PPAC.Migration.Internal.GodelPairCancellation
open Source SourceAlgebra SourceLogic OmegaSyntax ZFArithmetic GodelPairSyntax GodelPairArithmetic
open NaturalAdditionSyntax (sum sum_rename)
open NaturalMultiplicationSyntax (product product_rename)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem lower_index_subst {m} {Γ : Context m} (w a b d p : Fin m) (he : Derives Γ (.equal b d))
    (hp : Derives Γ (lower w a b p)) : Derives Γ (lower w a d p) := by
  have hi : Derives Γ ((lower w.castSucc a.castSucc (Fin.last m) p.castSucc).instantiate b) := by
    simpa only [Formula.instantiate, lower_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp
  have ho := Derives.eqSubst (lower w.castSucc a.castSucc (Fin.last m) p.castSucc) he hi
  simpa only [Formula.instantiate, lower_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem upper_left_subst {m} {Γ : Context m} (w a c b p : Fin m) (he : Derives Γ (.equal a c))
    (hp : Derives Γ (upper w a b p)) : Derives Γ (upper w c b p) := by
  have hi : Derives Γ ((upper w.castSucc (Fin.last m) b.castSucc p.castSucc).instantiate a) := by
    simpa only [Formula.instantiate, upper_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp
  have ho := Derives.eqSubst (upper w.castSucc (Fin.last m) b.castSucc p.castSucc) he hi
  simpa only [Formula.instantiate, upper_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem lower_cancel {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c b p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hc : Derives Γ (.mem c w)) (hb : Derives Γ (.mem b w))
    (hp : Derives Γ (lower w a b p)) (hr : Derives Γ (lower w c b p)) : Derives Γ (.equal a c) := by
  let L := lowerWitness w a b p
  let Ξ := Context.add L (Context.image Formula.raise Γ)
  apply eliminate_lower w a b p _ hp
  have hr1 : Derives Ξ (lower w.castSucc c.castSucc b.castSucc p.castSucc) := by simpa only [Formula.raise, lower_rename] using under hr L
  let R := lowerWitness w.castSucc c.castSucc b.castSucc p.castSucc
  let Δ := Context.add R (Context.image Formula.raise Ξ)
  apply eliminate_lower w.castSucc c.castSucc b.castSucc p.castSucc _ hr1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ L) R
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise := under (under h L) R
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hL : Derives Ξ L := .hyp (Or.inl rfl)
  have hL2 : Derives Δ ((product w.castSucc.castSucc b.castSucc.castSucc b.castSucc.castSucc (Fin.last m).castSucc).conj
      (sum w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc p.castSucc.castSucc)) := by
    simpa only [L, lowerWitness, Formula.raise, Formula.rename, product_rename, sum_rename] using under hL R
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have heq := mul_unique hZ2 _ _ _ _ _ hw2 (lift hb) (lift hb) (.conjL hL2) (.conjL hR)
  have hs := NaturalAdditionTransport.left_subst _ _ _ _ _ heq (.conjR hL2)
  have hqW := mul_range hZ2 _ _ _ _ hw2 (.conjL hR)
  exact cancel_sum_left hZ2 _ _ _ _ _ hw2 hqW (lift ha) (lift hc) hs (.conjR hR)

theorem upper_cancel {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b d p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hd : Derives Γ (.mem d w))
    (hp : Derives Γ (upper w a b p)) (hr : Derives Γ (upper w a d p)) : Derives Γ (.equal b d) := by
  let U := upperWitness w a b p
  let Ξ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_upper w a b p _ hp
  have hr2 : Derives Ξ (upper w.castSucc.castSucc a.castSucc.castSucc d.castSucc.castSucc p.castSucc.castSucc) := by
    simpa only [Formula.raise, upper_rename] using OrderedPairElimination.under_two hr U
  let V := upperWitness w.castSucc.castSucc a.castSucc.castSucc d.castSucc.castSucc p.castSucc.castSucc
  let Δ := Context.add V (Context.image Formula.raise (Context.image Formula.raise Ξ))
  apply eliminate_upper w.castSucc.castSucc a.castSucc.castSucc d.castSucc.castSucc p.castSucc.castSucc _ hr2
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise.raise.raise :=
    OrderedPairElimination.under_two (OrderedPairElimination.under_two h U) V
  have hZ4 : ZFContext.Evidence Δ := ZFContext.under_two (ZFContext.under_two hZ U) V
  have hw4 : Derives Δ (omega w.castSucc.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  let q1 : Fin (m+4) := (Fin.last m).castSucc.castSucc.castSucc
  let t1 : Fin (m+4) := (Fin.last (m+1)).castSucc.castSucc
  have hU : Derives Ξ U := .hyp (Or.inl rfl)
  have hU4 : Derives Δ ((product w.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc.castSucc q1).conj
      ((sum w.castSucc.castSucc.castSucc.castSucc q1 a.castSucc.castSucc.castSucc.castSucc t1).conj
        (sum w.castSucc.castSucc.castSucc.castSucc t1 b.castSucc.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc.castSucc))) := by
    simpa only [U, upperWitness, Formula.raise, Formula.rename, product_rename, sum_rename] using OrderedPairElimination.under_two hU V
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have heq := mul_unique hZ4 _ _ _ _ _ hw4 (lift ha) (lift ha) (.conjL hU4) (.conjL hV)
  have ht := NaturalAdditionTransport.left_subst _ _ _ _ _ heq (.conjL (.conjR hU4))
  have he := add_unique hZ4 _ _ _ _ _ hw4 (lift ha) ht (.conjL (.conjR hV))
  have hs := NaturalAdditionTransport.left_subst _ _ _ _ _ he (.conjR (.conjR hU4))
  have hqW := mul_range hZ4 _ _ _ _ hw4 (.conjL hV)
  have htW := add_range hZ4 _ _ _ _ hw4 hqW (.conjL (.conjR hV))
  exact cancel_sum_left hZ4 _ _ _ _ _ hw4 htW (lift hb) (lift hd) hs (.conjR (.conjR hV))

theorem mixed_disjoint {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b d p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w)) (hd : Derives Γ (.mem d w))
    (hab : Derives Γ (.mem a b)) (hp : Derives Γ (lower w a b p)) (hr : Derives Γ (upper w b d p)) : Derives Γ .bot := by
  let L := lowerWitness w a b p
  let Ξ := Context.add L (Context.image Formula.raise Γ)
  apply eliminate_lower w a b p _ hp
  have hr1 : Derives Ξ (upper w.castSucc b.castSucc d.castSucc p.castSucc) := by simpa only [Formula.raise, upper_rename] using under hr L
  let U := upperWitness w.castSucc b.castSucc d.castSucc p.castSucc
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Ξ))
  apply eliminate_upper w.castSucc b.castSucc d.castSucc p.castSucc _ hr1
  have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f.raise.raise.raise := OrderedPairElimination.under_two (under h L) U
  have hZ3 : ZFContext.Evidence Δ := ZFContext.under_two (ZFContext.under hZ L) U
  have hw3 : Derives Δ (omega w.castSucc.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hL : Derives Ξ L := .hyp (Or.inl rfl)
  have hL3 : Derives Δ ((product w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc).conj
      (sum w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc a.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc)) := by
    simpa only [L, lowerWitness, Formula.raise, Formula.rename, product_rename, sum_rename] using OrderedPairElimination.under_two hL U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have he := mul_unique hZ3 _ _ _ _ _ hw3 (lift hb) (lift hb) (.conjL hL3) (.conjL hU)
  have hs := NaturalAdditionTransport.left_subst _ _ _ _ _ he (.conjR hL3)
  have hqW := mul_range hZ3 _ _ _ _ hw3 (.conjL hU)
  have htW := add_range hZ3 _ _ _ _ hw3 hqW (.conjL (.conjR hU))
  have hpt := Derives.impE (Derives.conjL (NaturalAdditionMonotone.left_strict_iff hZ3 _ _ _ _ _ _ hw3 (lift ha) (lift hb) hqW hs (.conjL (.conjR hU)))) (lift hab)
  have htp := sum_left_bound hZ3 _ _ _ _ hw3 htW (lift hd) (.conjR (.conjR hU))
  exact NaturalOrderBasic.below_not_reverse hZ3 _ _ _ hw3 htW htp hpt
end PPAC.Migration.Internal.GodelPairCancellation
