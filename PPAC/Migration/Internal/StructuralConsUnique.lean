import PPAC.Migration.Internal.StructuralConsCore

/-! 隐藏零/单位见证下的原Cons唯一性、输入单射、实际纤维与Nil互斥。 -/
namespace PPAC.Migration.Internal.StructuralConsUnique
open Source SourceAlgebra SourceLogic OmegaSyntax StructuralListSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n r : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hn : Derives Γ (consCode w h t n)) (hr : Derives Γ (consCode w h t r)) : Derives Γ (Formula.equal n r) := by
  let U := unitWitness m
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralListUnits.with_units w _ hw
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ U
  have lift {a : Formula m} (ha : Derives Γ a) : Derives Δ a.raise.raise := OrderedPairElimination.under_two ha U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hn2 : Derives Δ (consCode w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, consCode_rename] using lift hn
  have hr2 : Derives Δ (consCode w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc r.castSucc.castSucc) := by simpa only [Formula.raise, consCode_rename] using lift hr
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have heW := StructuralListUnits.member hZ2 _ _ _ hw2 (.conjL hU) (.conjR hU)
  have hnAt := StructuralConsCore.specialize hZ2 _ _ _ _ _ _ (.conjL hU) (.conjR hU) hn2
  have hrAt := StructuralConsCore.specialize hZ2 _ _ _ _ _ _ (.conjL hU) (.conjR hU) hr2
  exact StructuralConsAt.unique hZ2 _ _ _ _ _ _ hw2 heW (lift hh) (lift ht) hnAt hrAt

theorem injective {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t c d n : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w))
    (hc : Derives Γ (.mem c w)) (hd : Derives Γ (.mem d w))
    (hn : Derives Γ (consCode w h t n)) (hr : Derives Γ (consCode w c d n)) : Derives Γ ((Formula.equal h c).conj (.equal t d)) := by
  let U := unitWitness m
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralListUnits.with_units w _ hw
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ U
  have lift {a : Formula m} (ha : Derives Γ a) : Derives Δ a.raise.raise := OrderedPairElimination.under_two ha U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using lift hw
  have hn2 : Derives Δ (consCode w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, consCode_rename] using lift hn
  have hr2 : Derives Δ (consCode w.castSucc.castSucc c.castSucc.castSucc d.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, consCode_rename] using lift hr
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have heW := StructuralListUnits.member hZ2 _ _ _ hw2 (.conjL hU) (.conjR hU)
  have hnAt := StructuralConsCore.specialize hZ2 _ _ _ _ _ _ (.conjL hU) (.conjR hU) hn2
  have hrAt := StructuralConsCore.specialize hZ2 _ _ _ _ _ _ (.conjL hU) (.conjR hU) hr2
  exact StructuralConsAt.injective hZ2 _ _ _ _ _ _ _ _ hw2 heW heW (lift hh) (lift ht) (lift hc) (lift hd) hnAt hrAt

theorem unique_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t : Fin m)
    (hw : Derives Γ (omega w)) (hh : Derives Γ (.mem h w)) (ht : Derives Γ (.mem t w)) : Derives Γ (fiberCons w h t) := by
  have hn := StructuralConsCore.exists_cons hZ w h t hw hh ht
  let N := (Formula.mem (Fin.last m) w.castSucc).conj (consCode w.castSucc h.castSucc t.castSucc (Fin.last m))
  let Ξ := Context.add N (Context.image Formula.raise Γ)
  change Derives Γ (.ex N) at hn
  apply Derives.exE (p := N) hn
  have hN : Derives Ξ N := .hyp (Or.inl rfl)
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ N
  have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw N
  have hu : Derives Ξ (.all ((consCode w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let C := consCode w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add C (Context.image Formula.raise Ξ)
    have hZ2 : ZFContext.Evidence Δ := ZFContext.under hZ1 C
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw1 C
    have hOld : Derives Δ (consCode w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [Formula.raise, consCode_rename] using under (Derives.conjR hN) C
    exact unique hZ2 _ _ _ _ _ hw2 (under (under hh N) C) (under (under ht N) C) (.hyp (Or.inl rfl)) hOld
  have hout : Derives Ξ (fiberCons w.castSucc h.castSucc t.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, consCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hN hu
  simpa only [Formula.raise, fiberCons_rename] using hout

theorem tag_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w e h t n : Fin m)
    (hw : Derives Γ (omega w)) (he : Derives Γ (.mem e w)) (hn : Derives Γ (consAt w e h t n)) : Derives Γ (.mem e n) := by
  let N := consAtWitness w e h t n
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply eliminate_consAt w e h t n _ hn
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ N
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw N
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hqW := GodelPairCore.range hZ1 _ _ _ _ hw1 (.conjL hN)
  exact .conjL (StructuralNodeProperties.components hZ1 _ _ _ _ hw1 (under he N) hqW (.conjR hN))

theorem disjoint {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w h t n : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (nilCode w n)) (hc : Derives Γ (consCode w h t n)) : Derives Γ .bot := by
  let U := unitWitness m
  let Δ := Context.add U (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply StructuralListUnits.with_units w _ hw
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ U
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw U
  have hn2 : Derives Δ (nilCode w.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, nilCode_rename] using OrderedPairElimination.under_two hn U
  have hc2 : Derives Δ (consCode w.castSucc.castSucc h.castSucc.castSucc t.castSucc.castSucc n.castSucc.castSucc) := by simpa only [Formula.raise, consCode_rename] using OrderedPairElimination.under_two hc U
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have heW := StructuralListUnits.member hZ2 _ _ _ hw2 (.conjL hU) (.conjR hU)
  have hne := StructuralNil.value hZ2 _ _ _ _ hw2 (.conjL hU) (.conjR hU) hn2
  have hcAt := StructuralConsCore.specialize hZ2 _ _ _ _ _ _ (.conjL hU) (.conjR hU) hc2
  have hen := tag_member hZ2 _ _ _ _ _ hw2 heW hcAt
  have hee := UnorderedPairLogic.mem_container_subst _ _ _ hne hen
  exact .impE (NaturalOrderBasic.nonself hZ2 (Fin.last (m+1))) hee
end PPAC.Migration.Internal.StructuralConsUnique
