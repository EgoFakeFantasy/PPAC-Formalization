import PPAC.Migration.Internal.ProjectSourceTypeStateRows

/-! 一个原Separation实例实际构造唯一上下文状态；集合外延性证明总单值性和真实状态纤维。 -/
namespace PPAC.Migration.Internal.ProjectSourceTypeStateExistence
open Source SourceAlgebra SourceLogic PairSyntax RestrictionSyntax PowerSetSyntax SyntaxAtomSyntax ProjectSourceTypeStateSyntax
open ReplacementPredicates (paramsUp)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem exists_state {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c n h : Fin m) : Derives Γ (existsState w c n h) := by
  have he := MinimalInstances.separation_instance selectionMatrix (three w n h) c (ZFContext.separation hZ selectionMatrix)
  have hmap : paramsUp (three w n h) = three w.castSucc n.castSucc h.castSucc := three_map w n h Fin.castSucc
  simpa only [MinimalPredicates.separationExists, existsState, state, hmap] using he

theorem subset {m} {Γ : Context m} (w c n h v : Fin m) (hs : Derives Γ (state w c n h v)) : Derives Γ (RestrictionSyntax.subset v c) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) v.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hs1 : Derives Δ (state w.castSucc c.castSucc n.castSucc h.castSucc v.castSucc) := by
    simpa only [Formula.raise, state_rename] using under hs M
  exact .conjL (.impE (.conjL (state_at _ _ _ _ _ _ hs1)) (.hyp (Or.inl rfl)))

theorem member_universe {m} {Γ : Context m} (w c u n h v : Fin m)
    (hu : Derives Γ (powerOf u c)) (hs : Derives Γ (state w c n h v)) : Derives Γ (.mem v u) :=
  SyntaxContextCarrier.state_member c u v hu (subset w c n h v hs)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c n h v t : Fin m)
    (hv : Derives Γ (state w c n h v)) (ht : Derives Γ (state w c n h t)) : Derives Γ (.equal v t) := by
  apply Derives.impE (extensionality_instance v t (ZFContext.arithmetic hZ).base.extensionality)
  apply Derives.allI
  have hv1 : Derives (Context.image Formula.raise Γ) (state w.castSucc c.castSucc n.castSucc h.castSucc v.castSucc) := by
    simpa only [Formula.raise, state_rename] using Derives.rename Fin.castSucc hv
  have ht1 : Derives (Context.image Formula.raise Γ) (state w.castSucc c.castSucc n.castSucc h.castSucc t.castSucc) := by
    simpa only [Formula.raise, state_rename] using Derives.rename Fin.castSucc ht
  have hvl := state_at _ _ _ _ _ (Fin.last m) hv1
  have htl := state_at _ _ _ _ _ (Fin.last m) ht1
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjR htl) _) (.impE (add (.conjL hvl) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR hvl) _) (.impE (add (.conjL htl) _) (.hyp (Or.inl rfl)))

theorem unique_at {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c n h v : Fin m)
    (hv : Derives Γ (state w c n h v)) : Derives Γ (uniqueState w c n h v) := by
  apply Derives.allI
  apply Derives.impI
  let T := state w.castSucc c.castSucc n.castSucc h.castSucc (Fin.last m)
  have hv1 : Derives (Context.add T (Context.image Formula.raise Γ)) (state w.castSucc c.castSucc n.castSucc h.castSucc v.castSucc) := by
    simpa only [Formula.raise, state_rename] using under hv T
  exact unique (ZFContext.under hZ T) _ _ _ _ _ _ (.hyp (Or.inl rfl)) hv1

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c n h : Fin m) : Derives Γ (fiber w c n h) := by
  have he := exists_state hZ w c n h
  let V := state w.castSucc c.castSucc n.castSucc h.castSucc (Fin.last m)
  let Δ := Context.add V (Context.image Formula.raise Γ)
  apply Derives.exE (p := V) he
  have hV : Derives Δ V := .hyp (Or.inl rfl)
  have hu := unique_at (ZFContext.under hZ V) _ _ _ _ _ hV
  have hout : Derives Δ (fiber w.castSucc c.castSucc n.castSucc h.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, state_rename, uniqueState_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hV hu
  simpa only [Formula.raise, fiber_rename] using hout
end PPAC.Migration.Internal.ProjectSourceTypeStateExistence
