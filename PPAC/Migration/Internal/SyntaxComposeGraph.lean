import PPAC.Migration.Internal.SyntaxComposeExistence

/-! 原Replacement实际构造唯一完整复合索引图；边双条件覆盖全部内部候选。 -/
namespace PPAC.Migration.Internal.SyntaxComposeGraph
open Source SourceAlgebra SourceLogic GraphSyntax ReplacementPredicates SyntaxIndexMapSyntax SyntaxComposeSyntax SyntaxRenameQuerySyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem target_map {m} {Γ : Context m} (w r t a c e g : Fin m) (hg : Derives Γ (composed w r t a c e g)) :
    Derives Γ (indexMap w g a e) := .conjL (.conjR (.conjR hg))

theorem as_function_graph {m} {Γ : Context m} (w r t a c e g : Fin m) (hg : Derives Γ (composed w r t a c e g)) :
    Derives Γ (RelationGraphSyntax.functionGraph SyntaxComposeSyntax.matrix (Source.SetLanguage.args2 r t) a g) :=
  .conjI (.conjL (.conjR (target_map w r t a c e g hg))) (.conjR (.conjR (.conjR hg)))

theorem exists_graph {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c e : Fin m)
    (hr : Derives Γ (indexMap w r a c)) (ht : Derives Γ (indexMap w t c e)) : Derives Γ (existsGraph w r t a c e) := by
  let ρ := Source.SetLanguage.args2 r t
  have he := RelationGraphFunction.exists_graph hZ SyntaxComposeSyntax.matrix ρ a (SyntaxComposeExistence.total hZ ρ w a c e hr ht)
  let G := RelationGraphSyntax.functionGraph SyntaxComposeSyntax.matrix (paramsUp ρ) a.castSucc (Fin.last m)
  let Δ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) he
  have hr1 : Derives Δ (indexMap w.castSucc r.castSucc a.castSucc c.castSucc) := of_eq (indexMap_rename _ _ _ _ Fin.castSucc) (under hr G)
  have ht1 : Derives Δ (indexMap w.castSucc t.castSucc c.castSucc e.castSucc) := of_eq (indexMap_rename _ _ _ _ Fin.castSucc) (under ht G)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hb := SyntaxComposeExistence.outputs (paramsUp ρ) w.castSucc a.castSucc c.castSucc e.castSucc ht1
  have hs := RelationGraph.sequence SyntaxComposeSyntax.matrix (paramsUp ρ) a.castSucc e.castSucc (Fin.last m) hG hb
  have hg : Derives Δ (composed w.castSucc r.castSucc t.castSucc a.castSucc c.castSucc e.castSucc (Fin.last m)) :=
    .conjI hr1 (.conjI ht1 (.conjI (.conjI (.conjI (.conjL (.conjL hr1)) (.conjR (.conjL ht1))) hs) (.conjR hG)))
  have ho : Derives Δ (existsGraph w.castSucc r.castSucc t.castSucc a.castSucc c.castSucc e.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, composed_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hg
  exact of_eq (existsGraph_rename w r t a c e Fin.castSucc).symm ho

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c e g h : Fin m)
    (hg : Derives Γ (composed w r t a c e g)) (hh : Derives Γ (composed w r t a c e h)) : Derives Γ (.equal g h) :=
  RelationGraph.unique_graph hZ SyntaxComposeSyntax.matrix (Source.SetLanguage.args2 r t) a g h
    (as_function_graph _ _ _ _ _ _ _ hg) (as_function_graph _ _ _ _ _ _ _ hh)

theorem edge_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c e g i j : Fin m)
    (hg : Derives Γ (composed w r t a c e g)) : Derives Γ ((edge g i j).iff (value r t i j)) := by
  have he : Derives Γ ((edge g i j).iff ((Formula.mem i a).conj (value r t i j))) := of_eq
    (by simp only [matrix_rel, PairSyntax.args2_first, PairSyntax.args2_second])
    (RelationGraphSyntax.law_at SyntaxComposeSyntax.matrix (Source.SetLanguage.args2 r t) a g i j (.conjR (as_function_graph _ _ _ _ _ _ _ hg)))
  apply Derives.conjI
  · apply Derives.impI
    exact .conjR (.impE (add (.conjL he) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    let V := value r t i j
    have hV : Derives (Context.add V Γ) V := .hyp (Or.inl rfl)
    have hi := SyntaxComposePoint.source_member (ZFContext.add hZ V) w r t a c i j (add (.conjL hg) V) hV
    exact .impE (add (.conjR he) V) (.conjI hi hV)

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r t a c e : Fin m)
    (hr : Derives Γ (indexMap w r a c)) (ht : Derives Γ (indexMap w t c e)) : Derives Γ (graphFiber w r t a c e) := by
  let G := composed w.castSucc r.castSucc t.castSucc a.castSucc c.castSucc e.castSucc (Fin.last m)
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) (exists_graph hZ w r t a c e hr ht)
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hu : Derives Ξ (.all ((composed w.castSucc.castSucc r.castSucc.castSucc t.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let H := composed w.castSucc.castSucc r.castSucc.castSucc t.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add H (Context.image Formula.raise Ξ)
    have hg2 : Derives Δ (composed w.castSucc.castSucc r.castSucc.castSucc t.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc e.castSucc.castSucc (Fin.last m).castSucc) := of_eq (by simp only [G, Formula.raise, composed_rename]) (under hG H)
    exact unique (ZFContext.under (ZFContext.under hZ G) H) _ _ _ _ _ _ _ _ (.hyp (Or.inl rfl)) hg2
  have ho : Derives Ξ (graphFiber w.castSucc r.castSucc t.castSucc a.castSucc c.castSucc e.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [G, Formula.instantiate, Formula.rename, composed_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hG hu)
  exact of_eq (graphFiber_rename w r t a c e Fin.castSucc).symm ho
end PPAC.Migration.Internal.SyntaxComposeGraph
