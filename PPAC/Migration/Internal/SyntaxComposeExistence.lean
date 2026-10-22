import PPAC.Migration.Internal.SyntaxComposePoint

/-! 每个实际域点取得唯一复合值；原Replacement的总单值前提完全在对象层证明。 -/
namespace PPAC.Migration.Internal.SyntaxComposeExistence
open Source SourceAlgebra SourceLogic GraphSyntax ReplacementPredicates SyntaxIndexMapSyntax SyntaxComposeSyntax SyntaxRenameQuerySyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem point_exists {m} {Γ : Context m} (ρ : Fin 2 → Fin m) (w a c e i : Fin m)
    (hr : Derives Γ (indexMap w (ρ 0) a c)) (ht : Derives Γ (indexMap w (ρ 1) c e)) (hi : Derives Γ (.mem i a)) :
    Derives Γ (hasValue SyntaxComposeSyntax.matrix ρ i) := by
  have hk := SyntaxIndexMapSyntax.value_exists w (ρ 0) a c i hr hi
  let K := (Formula.mem (Fin.last m) c.castSucc).conj (valueAt (ρ 0).castSucc i.castSucc (Fin.last m))
  let Ξ := Context.add K (Context.image Formula.raise Γ)
  apply Derives.exE (p := K) hk
  have hK : Derives Ξ K := .hyp (Or.inl rfl)
  have ht1 : Derives Ξ (indexMap w.castSucc (ρ 1).castSucc c.castSucc e.castSucc) := of_eq (indexMap_rename _ _ _ _ Fin.castSucc) (under ht K)
  have hj := SyntaxIndexMapSyntax.value_exists _ _ _ _ _ ht1 (.conjL hK)
  let J := (Formula.mem (Fin.last (m+1)) e.castSucc.castSucc).conj (valueAt (ρ 1).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add J (Context.image Formula.raise Ξ)
  apply Derives.exE (p := J) hj
  have he2 : Derives Δ (edge (ρ 0).castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc) := of_eq (by simp only [Formula.raise, edge_rename]) (under (.conjL (.conjR hK)) J)
  have hJ : Derives Δ J := .hyp (Or.inl rfl)
  have hv := intro_value (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc he2 (.conjL (.conjR hJ))
  have ho : Derives Δ (hasValue SyntaxComposeSyntax.matrix (paramsUp (paramsUp ρ)) i.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate, matrix_rel, value_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hv
  exact of_eq (by simp only [Formula.raise, hasValue_rename]) ho

theorem point_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m) (w a c e i : Fin m)
    (hr : Derives Γ (indexMap w (ρ 0) a c)) (ht : Derives Γ (indexMap w (ρ 1) c e)) (hi : Derives Γ (.mem i a)) :
    Derives Γ (fiber SyntaxComposeSyntax.matrix ρ i) := by
  have he := point_exists ρ w a c e i hr ht hi
  let Y := rel SyntaxComposeSyntax.matrix (paramsUp ρ) i.castSucc (Fin.last m)
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  apply Derives.exE (p := Y) he
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hu : Derives Ξ (unique SyntaxComposeSyntax.matrix (paramsUp ρ) i.castSucc (Fin.last m)) := by
    apply Derives.allI
    apply Derives.impI
    let Z := rel SyntaxComposeSyntax.matrix (paramsUp (paramsUp ρ)) i.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add Z (Context.image Formula.raise Ξ)
    have hZ2 := ZFContext.under (ZFContext.under hZ Y) Z
    have hr2 : Derives Δ (indexMap w.castSucc.castSucc (ρ 0).castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc) := of_eq (by simp only [Formula.raise, indexMap_rename]) (under (under hr Y) Z)
    have ht2 : Derives Δ (indexMap w.castSucc.castSucc (ρ 1).castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc) := of_eq (by simp only [Formula.raise, indexMap_rename]) (under (under ht Y) Z)
    have hy2 : Derives Δ (value (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc i.castSucc.castSucc (Fin.last m).castSucc) := of_eq (by simp only [Y, Formula.raise, matrix_rel, value_rename, paramsUp]) (under hY Z)
    have hz2 : Derives Δ (value (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))) := of_eq (by simp only [Z, matrix_rel, paramsUp]) (Derives.hyp (Or.inl rfl) : Derives Δ Z)
    exact SyntaxComposePoint.unique hZ2 _ _ _ _ _ _ _ _ _ hr2 ht2 hz2 hy2
  have ho : Derives Ξ (fiber SyntaxComposeSyntax.matrix (paramsUp ρ) i.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Y, Formula.instantiate, Formula.rename, rel_rename, unique_rename, paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hY hu)
  exact of_eq (by simp only [Formula.raise, fiber_rename]) ho

theorem total {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (ρ : Fin 2 → Fin m) (w a c e : Fin m)
    (hr : Derives Γ (indexMap w (ρ 0) a c)) (ht : Derives Γ (indexMap w (ρ 1) c e)) :
    Derives Γ (ReplacementPredicates.total SyntaxComposeSyntax.matrix ρ a) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) a.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hr1 : Derives Δ (indexMap w.castSucc (ρ 0).castSucc a.castSucc c.castSucc) := of_eq (indexMap_rename _ _ _ _ Fin.castSucc) (under hr M)
  have ht1 : Derives Δ (indexMap w.castSucc (ρ 1).castSucc c.castSucc e.castSucc) := of_eq (indexMap_rename _ _ _ _ Fin.castSucc) (under ht M)
  exact point_fiber (ZFContext.under hZ M) (paramsUp ρ) _ _ _ _ _ hr1 ht1 (.hyp (Or.inl rfl))

theorem outputs {m} {Γ : Context m} (ρ : Fin 2 → Fin m) (w a c e : Fin m)
    (ht : Derives Γ (indexMap w (ρ 1) c e)) : Derives Γ (RelationGraph.outputsInto SyntaxComposeSyntax.matrix ρ a e) := by
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let B := (Formula.mem (Fin.last m).castSucc a.castSucc.castSucc).conj (rel SyntaxComposeSyntax.matrix (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  have ht2 : Derives Δ (indexMap w.castSucc.castSucc (ρ 1).castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc) := of_eq (by simp only [Formula.raise, indexMap_rename]) (SyntaxRenameBinders.under_2 ht B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hv : Derives Δ (value (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))) := of_eq (by simp only [matrix_rel, paramsUp]) (.conjR hB)
  exact SyntaxComposePoint.target_member _ _ _ _ _ _ _ ht2 hv
end PPAC.Migration.Internal.SyntaxComposeExistence
