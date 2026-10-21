import PPAC.Migration.Internal.StructuralNil

/-! 给定实际单位标签时的Cons内层配数：自然范围、严格界、输出唯一和输入单射。 -/
namespace PPAC.Migration.Internal.StructuralConsAt
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w e h t n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (consAt w e h t n)) : Derives Γ (.mem n w) := by
  let N := consAtWitness w e h t n
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_consAt w e h t n _ hn
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  exact StructuralNodeProperties.range hZ1 _ _ _ _ hw1 (.conjR hN)

theorem positive {m} {Γ : Context m} (w e h t n : Fin m) (hn : Derives Γ (consAt w e h t n)) : Derives Γ (empty n).neg := by
  let N := consAtWitness w e h t n
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_consAt w e h t n _ hn
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hout := StructuralNodeProperties.positive _ _ _ _ (.conjR hN)
  simpa only [Formula.raise, Formula.neg, Formula.rename, empty_rename] using hout

theorem components {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w e h t n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (.mem e w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hn : Derives Γ (consAt w e h t n)) : Derives Γ ((Formula.mem h n).conj (.mem t n)) := by
  let N := consAtWitness w e h t n
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_consAt w e h t n _ hn
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hqW := GodelPairCore.range hZ1 _ _ _ _ hw1 (.conjL hN)
  have hnW := StructuralNodeProperties.range hZ1 _ _ _ _ hw1 (.conjR hN)
  have hqn := Derives.conjR (StructuralNodeProperties.components hZ1 _ _ _ _ hw1 (under he N) hqW (.conjR hN))
  have hb := GodelPairBounds.components hZ1 _ _ _ _ hw1 (under hh N) (under ht N) (.conjL hN)
  exact .conjI (NaturalArithmeticBounds.below_mem_trans hZ1 _ _ _ _ hw1 hnW (.conjL hb) hqn)
    (NaturalArithmeticBounds.below_mem_trans hZ1 _ _ _ _ hw1 hnW (.conjR hb) hqn)

theorem value_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w e h t n r q p : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (.mem e w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hq : Derives Γ (GodelPairSyntax.code w h t q)) (hp : Derives Γ (GodelPairSyntax.code w h t p))
    (hn : Derives Γ (StructuralNodeSyntax.raw w e q n)) (hr : Derives Γ (StructuralNodeSyntax.raw w e p r)) : Derives Γ (.equal n r) := by
  have hqp := GodelPairCore.unique hZ _ _ _ _ _ hw hh ht hq hp
  have hpW := GodelPairCore.range hZ _ _ _ _ hw hp
  exact StructuralNodeCore.unique hZ _ _ _ _ _ hw he hpW (StructuralListUnits.payload_subst _ _ _ _ _ hqp hn) hr

theorem input_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w e f h t c d n q p : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (.mem e w)) (hf : Derives Γ (.mem f w))
    (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) (hc : Derives Γ (.mem c w)) (hd : Derives Γ (.mem d w))
    (hq : Derives Γ (GodelPairSyntax.code w h t q)) (hp : Derives Γ (GodelPairSyntax.code w c d p))
    (hn : Derives Γ (StructuralNodeSyntax.raw w e q n)) (hr : Derives Γ (StructuralNodeSyntax.raw w f p n)) : Derives Γ ((Formula.equal h c).conj (.equal t d)) := by
  have hqW := GodelPairCore.range hZ _ _ _ _ hw hq
  have hpW := GodelPairCore.range hZ _ _ _ _ hw hp
  have hi := StructuralNodeCore.injective hZ _ _ _ _ _ _ hw he hqW hf hpW hn hr
  exact GodelPairInjective.injective hZ _ _ _ _ _ _ hw hh ht hc hd (StructuralNodeCore.pair_output_subst _ _ _ _ _ (.conjR hi) hq) hp

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w e h t n r : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (.mem e w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hn : Derives Γ (consAt w e h t n)) (hr : Derives Γ (consAt w e h t r)) : Derives Γ (Formula.equal n r) := by
  let N := consAtWitness w e h t n
  let Ξ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_consAt w e h t n _ hn
  have hr1 : Derives Ξ (consAt w.castSucc e.castSucc h.castSucc t.castSucc r.castSucc) := by simpa only [Formula.raise, consAt_rename] using under hr N
  let R := consAtWitness w.castSucc e.castSucc h.castSucc t.castSucc r.castSucc
  let Δ := Context.add R (Context.image Formula.raise Ξ)
  apply eliminate_consAt w.castSucc e.castSucc h.castSucc t.castSucc r.castSucc _ hr1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ N) R
  have lift {a : Formula m} (ha : Derives Γ a) : Derives Δ a.raise.raise := under (under ha N) R
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hN : Derives Ξ N := .hyp (Or.inl rfl)
  have hN2 : Derives Δ ((GodelPairSyntax.code w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc).conj
      (StructuralNodeSyntax.raw w.castSucc.castSucc e.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc)) := by
    simpa only [N, consAtWitness, Formula.raise, Formula.rename, GodelPairSyntax.code_rename, StructuralNodeSyntax.raw_rename] using under hN R
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact value_unique hZ2 _ _ _ _ _ _ _ _ hw2 (lift he) (lift hh) (lift ht) (.conjL hN2) (.conjL hR) (.conjR hN2) (.conjR hR)

theorem injective {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w e f h t c d n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (.mem e w)) (hf : Derives Γ (.mem f w))
    (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (.mem c w)) (hd : Derives Γ (.mem d w))
    (hn : Derives Γ (consAt w e h t n)) (hr : Derives Γ (consAt w f c d n)) : Derives Γ ((Formula.equal h c).conj (.equal t d)) := by
  let N := consAtWitness w e h t n
  let Ξ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_consAt w e h t n _ hn
  have hr1 : Derives Ξ (consAt w.castSucc f.castSucc c.castSucc d.castSucc n.castSucc) := by simpa only [Formula.raise, consAt_rename] using under hr N
  let R := consAtWitness w.castSucc f.castSucc c.castSucc d.castSucc n.castSucc
  let Δ := Context.add R (Context.image Formula.raise Ξ)
  apply eliminate_consAt w.castSucc f.castSucc c.castSucc d.castSucc n.castSucc _ hr1
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under (ZFContext.under hZ N) R
  have lift {a : Formula m} (ha : Derives Γ a) : Derives Δ a.raise.raise := under (under ha N) R
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hN : Derives Ξ N := .hyp (Or.inl rfl)
  have hN2 : Derives Δ ((GodelPairSyntax.code w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc).conj
      (StructuralNodeSyntax.raw w.castSucc.castSucc e.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc)) := by
    simpa only [N, consAtWitness, Formula.raise, Formula.rename, GodelPairSyntax.code_rename, StructuralNodeSyntax.raw_rename] using under hN R
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  exact input_unique hZ2 _ _ _ _ _ _ _ _ _ _ hw2 (lift he) (lift hf) (lift hh) (lift ht) (lift hc) (lift hd) (.conjL hN2) (.conjL hR) (.conjR hN2) (.conjR hR)

end PPAC.Migration.Internal.StructuralConsAt
