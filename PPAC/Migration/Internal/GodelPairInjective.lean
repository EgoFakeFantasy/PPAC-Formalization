import PPAC.Migration.Internal.GodelPairCancellation

/-! 原Gödel配数的完整输入单射性；四种分支组合均在对象ZF中排除碰撞。 -/
namespace PPAC.Migration.Internal.GodelPairInjective
open Source SourceAlgebra SourceLogic OmegaSyntax GodelPairSyntax GodelPairBandSyntax
open GodelPairCancellation
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem injective {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a b c d p : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (.mem a w)) (hb : Derives Γ (.mem b w))
    (hc : Derives Γ (.mem c w)) (hd : Derives Γ (.mem d w))
    (hp : Derives Γ (code w a b p)) (hq : Derives Γ (code w c d p)) :
    Derives Γ ((Formula.equal a c).conj (.equal b d)) := by
  have hpW := GodelPairCore.range hZ _ _ _ _ hw hp
  apply Derives.disjE hp
  · apply Derives.disjE (add hq _)
    · let H := ((Formula.mem a b)).conj (lower w a b p)
      let K := ((Formula.mem c d)).conj (lower w c d p)
      let Δ := Context.add K (Context.add H Γ)
      have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add hZ H) K
      have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f := add (add h H) K
      have hH : Derives Δ H := .hyp (Or.inr (Or.inl rfl))
      have hK : Derives Δ K := .hyp (Or.inl rfl)
      have hA := GodelPairBands.lower_band hZ2 _ _ _ _ (lift hw) (lift ha) (lift hb) (.conjL hH) (.conjR hH)
      have hB := GodelPairBands.lower_band hZ2 _ _ _ _ (lift hw) (lift hc) (lift hd) (.conjL hK) (.conjR hK)
      have he := GodelPairBandUnique.index_unique hZ2 w b d p (lift hw) (lift hb) (lift hd) (lift hpW) hA hB
      have hr := lower_index_subst w c d b p (eq_symm he) (.conjR hK)
      exact .conjI (lower_cancel hZ2 w a c b p (lift hw) (lift ha) (lift hc) (lift hb) (.conjR hH) hr) he
    · let H := ((Formula.mem a b)).conj (lower w a b p)
      let K := ((Formula.mem c d).neg).conj (upper w c d p)
      let Δ := Context.add K (Context.add H Γ)
      have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add hZ H) K
      have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f := add (add h H) K
      have hH : Derives Δ H := .hyp (Or.inr (Or.inl rfl))
      have hK : Derives Δ K := .hyp (Or.inl rfl)
      have hA := GodelPairBands.lower_band hZ2 _ _ _ _ (lift hw) (lift ha) (lift hb) (.conjL hH) (.conjR hH)
      have hB := GodelPairBands.upper_band hZ2 _ _ _ _ (lift hw) (lift hc) (lift hd) (.conjL hK) (.conjR hK)
      have he := GodelPairBandUnique.index_unique hZ2 w b c p (lift hw) (lift hb) (lift hc) (lift hpW) hA hB
      have hr := upper_left_subst w c b d p (eq_symm he) (.conjR hK)
      exact .botE (mixed_disjoint hZ2 w a b d p (lift hw) (lift ha) (lift hb) (lift hd) (.conjL hH) (.conjR hH) hr)
  · apply Derives.disjE (add hq _)
    · let H := ((Formula.mem a b).neg).conj (upper w a b p)
      let K := ((Formula.mem c d)).conj (lower w c d p)
      let Δ := Context.add K (Context.add H Γ)
      have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add hZ H) K
      have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f := add (add h H) K
      have hH : Derives Δ H := .hyp (Or.inr (Or.inl rfl))
      have hK : Derives Δ K := .hyp (Or.inl rfl)
      have hA := GodelPairBands.upper_band hZ2 _ _ _ _ (lift hw) (lift ha) (lift hb) (.conjL hH) (.conjR hH)
      have hB := GodelPairBands.lower_band hZ2 _ _ _ _ (lift hw) (lift hc) (lift hd) (.conjL hK) (.conjR hK)
      have he := GodelPairBandUnique.index_unique hZ2 w a d p (lift hw) (lift ha) (lift hd) (lift hpW) hA hB
      have hr := upper_left_subst w a d b p he (.conjR hH)
      exact .botE (mixed_disjoint hZ2 w c d b p (lift hw) (lift hc) (lift hd) (lift hb) (.conjL hK) (.conjR hK) hr)
    · let H := ((Formula.mem a b).neg).conj (upper w a b p)
      let K := ((Formula.mem c d).neg).conj (upper w c d p)
      let Δ := Context.add K (Context.add H Γ)
      have hZ2 : ZFContext.Evidence Δ := ZFContext.add (ZFContext.add hZ H) K
      have lift {f : Formula m} (h : Derives Γ f) : Derives Δ f := add (add h H) K
      have hH : Derives Δ H := .hyp (Or.inr (Or.inl rfl))
      have hK : Derives Δ K := .hyp (Or.inl rfl)
      have hA := GodelPairBands.upper_band hZ2 _ _ _ _ (lift hw) (lift ha) (lift hb) (.conjL hH) (.conjR hH)
      have hB := GodelPairBands.upper_band hZ2 _ _ _ _ (lift hw) (lift hc) (lift hd) (.conjL hK) (.conjR hK)
      have he := GodelPairBandUnique.index_unique hZ2 w a c p (lift hw) (lift ha) (lift hc) (lift hpW) hA hB
      have hr := upper_left_subst w c a d p (eq_symm he) (.conjR hK)
      exact .conjI he (upper_cancel hZ2 w a b d p (lift hw) (lift ha) (lift hb) (lift hd) (.conjR hH) hr)
end PPAC.Migration.Internal.GodelPairInjective
