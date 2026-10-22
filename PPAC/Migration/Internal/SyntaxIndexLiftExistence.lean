import PPAC.Migration.Internal.SyntaxIndexLiftUnique

/-! 所有内部后继域输入实际取得唯一提升值；总性前提在对象层完全消去。 -/
namespace PPAC.Migration.Internal.SyntaxIndexLiftExistence
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax ReplacementPredicates SyntaxIndexMapSyntax SyntaxIndexLiftSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem point_exists {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m) (w c u x : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (indexMap w (ρ 0) (ρ 1) c))
    (hu : Derives Γ (successor u (ρ 1))) (hx : Derives Γ (.mem x u)) :
    Derives Γ (hasValue SyntaxIndexLiftSyntax.matrix ρ x) := by
  have huNat := OmegaStructureAlgebra.successor_member w u (ρ 1) (ZFContext.arithmetic hZ).base.extensionality hw (.conjL (.conjL hm)) hu
  have hxNat := StructuralListTraceOrder.member_member hZ w x u hw huNat hx
  have hd := OmegaStructureInduction.decomposition w (ZFContext.separation hZ OmegaStructureSyntax.splitMatrix) hw
  have hs := OmegaStructureAlgebra.decomposition_at w x hd hxNat
  apply Derives.disjE hs
  · apply Derives.exI x
    simp only [Formula.instantiate, matrix_rel, value_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .disjL (.conjI (.hyp (Or.inl rfl)) (.hyp (Or.inl rfl)))
  · let V := OmegaStructureSyntax.predecessor w x
    let K := (Formula.mem (Fin.last m) w.castSucc).conj (successor x.castSucc (Fin.last m))
    let Ξ := Context.add K (Context.image Formula.raise (Context.add V Γ))
    apply Derives.exE (p := K) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ V) K
    have hw1 : Derives Ξ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under (add hw V) K
    have hm1 : Derives Ξ (indexMap w.castSucc (ρ 0).castSucc (ρ 1).castSucc c.castSucc) := by
      simpa only [Formula.raise, indexMap_rename] using under (add hm V) K
    have hu1 : Derives Ξ (successor u.castSucc (ρ 1).castSucc) := by simpa only [Formula.raise, successor_rename] using under (add hu V) K
    have hK : Derives Ξ K := .hyp (Or.inl rfl)
    have hk := SyntaxIndexLiftOrder.predecessor_member hZ1 _ _ _ _ _ hw1 (.conjL (.conjL hm1)) hu1
      (under (add hx V) K) (.conjR hK)
    have he := SyntaxIndexMapSyntax.value_exists _ _ _ _ _ hm1 hk
    let J := (Formula.mem (Fin.last (m+1)) c.castSucc.castSucc).conj
      (valueAt (ρ 0).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
    let Ψ := Context.add J (Context.image Formula.raise Ξ)
    change Derives Ξ (.ex J) at he
    apply Derives.exE he
    have hZ2 := ZFContext.under hZ1 J
    have hJ : Derives Ψ J := .hyp (Or.inl rfl)
    have hy := InsertExistence.exists_insert (Fin.last (m+1)) (Fin.last (m+1))
      (ZFContext.arithmetic hZ2).base.pairing (ZFContext.arithmetic hZ2).base.union
    let Y := successor (Fin.last (m+2)) (Fin.last (m+1)).castSucc
    let Δ := Context.add Y (Context.image Formula.raise Ψ)
    change Derives Ψ (.ex Y) at hy
    apply Derives.exE hy
    have hk3 : Derives Δ (.mem (Fin.last m).castSucc.castSucc (ρ 1).castSucc.castSucc.castSucc) := under (under hk J) Y
    have he3 : Derives Δ (edge (ρ 0).castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc) := by
      simpa only [Formula.raise, edge_rename] using under (Derives.conjL (.conjR hJ)) Y
    have hx3 : Derives Δ (successor x.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc) := by
      simpa only [Formula.raise, successor_rename] using under (under (Derives.conjR hK) J) Y
    have hY : Derives Δ Y := .hyp (Or.inl rfl)
    have hshift := intro_shifted _ _ _ _ _ _ hk3 he3 hx3 hY
    have ho : Derives Δ (hasValue SyntaxIndexLiftSyntax.matrix (paramsUp (paramsUp (paramsUp ρ))) x.castSucc.castSucc.castSucc) := by
      apply Derives.exI (Fin.last (m+2))
      simp only [Formula.instantiate, matrix_rel, value_rename, paramsUp,
        Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
      exact .disjR hshift
    simpa only [Formula.raise, hasValue_rename, paramsUp] using ho

theorem point_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m) (w c u x : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (indexMap w (ρ 0) (ρ 1) c))
    (hu : Derives Γ (successor u (ρ 1))) (hx : Derives Γ (.mem x u)) :
    Derives Γ (fiber SyntaxIndexLiftSyntax.matrix ρ x) := by
  have he := point_exists hZ ρ w c u x hw hm hu hx
  let Y := rel SyntaxIndexLiftSyntax.matrix (paramsUp ρ) x.castSucc (Fin.last m)
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at he
  apply Derives.exE he
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hi : Derives Ξ (unique SyntaxIndexLiftSyntax.matrix (paramsUp ρ) x.castSucc (Fin.last m)) := by
    apply Derives.allI
    apply Derives.impI
    let Z := rel SyntaxIndexLiftSyntax.matrix (paramsUp (paramsUp ρ)) x.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add Z (Context.image Formula.raise Ξ)
    have hZ2 := ZFContext.under (ZFContext.under hZ Y) Z
    have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using under (under hw Y) Z
    have hm2 : Derives Δ (indexMap w.castSucc.castSucc (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc c.castSucc.castSucc) := by
      simpa only [Formula.raise, indexMap_rename] using under (under hm Y) Z
    have hy2 : Derives Δ (value (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [Y, Formula.raise, rel_rename, matrix_rel, value_rename, paramsUp] using under hY Z
    have hz2 : Derives Δ (value (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc x.castSucc.castSucc (Fin.last (m+1))) := by
      simpa only [Z, matrix_rel, paramsUp] using (Derives.hyp (Or.inl rfl) : Derives Δ Z)
    exact SyntaxIndexLiftUnique.unique hZ2 _ _ _ _ _ _ _ hw2 hm2 hz2 hy2
  have ho : Derives Ξ (fiber SyntaxIndexLiftSyntax.matrix (paramsUp ρ) x.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, rel_rename, unique_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hY hi
  simpa only [Formula.raise, fiber_rename, paramsUp] using ho

theorem total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m) (w c u : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (indexMap w (ρ 0) (ρ 1) c))
    (hu : Derives Γ (successor u (ρ 1))) : Derives Γ (ReplacementPredicates.total SyntaxIndexLiftSyntax.matrix ρ u) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) u.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw M
  have hm1 : Derives Δ (indexMap w.castSucc (ρ 0).castSucc (ρ 1).castSucc c.castSucc) := by simpa only [Formula.raise, indexMap_rename] using under hm M
  have hu1 : Derives Δ (successor u.castSucc (ρ 1).castSucc) := by simpa only [Formula.raise, successor_rename] using under hu M
  exact point_fiber (ZFContext.under hZ M) (paramsUp ρ) _ _ _ _ hw1 hm1 hu1 (.hyp (Or.inl rfl))

theorem outputs {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m) (w c u v : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (indexMap w (ρ 0) (ρ 1) c))
    (hv : Derives Γ (successor v c)) : Derives Γ (RelationGraph.outputsInto SyntaxIndexLiftSyntax.matrix ρ u v) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let B := (Formula.mem (Fin.last m).castSucc u.castSucc.castSucc).conj
    (rel SyntaxIndexLiftSyntax.matrix (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  have hw2 : Derives Δ (omega w.castSucc.castSucc) := by simpa only [Formula.raise, omega_rename] using OrderedPairElimination.under_two hw B
  have hm2 : Derives Δ (indexMap w.castSucc.castSucc (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc c.castSucc.castSucc) := by
    simpa only [Formula.raise, indexMap_rename] using OrderedPairElimination.under_two hm B
  have hv2 : Derives Δ (successor v.castSucc.castSucc c.castSucc.castSucc) := by simpa only [Formula.raise, successor_rename] using OrderedPairElimination.under_two hv B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hh : Derives Δ (value (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))) := by
    simpa only [matrix_rel, paramsUp] using Derives.conjR hB
  exact SyntaxIndexLiftPoint.target_member (ZFContext.under_two hZ B) _ _ _ _ _ _ _ hw2 hm2 hv2 hh
end PPAC.Migration.Internal.SyntaxIndexLiftExistence
