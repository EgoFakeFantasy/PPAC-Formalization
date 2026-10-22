import PPAC.Migration.Internal.SyntaxIndexLiftExistence

/-! 原Replacement实际构造唯一完整binder提升图；输入/输出后继和所有图边均为内部对象。 -/
namespace PPAC.Migration.Internal.SyntaxIndexLift
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax ReplacementPredicates SyntaxIndexMapSyntax SyntaxIndexLiftSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem as_function_graph {m} {Γ : Context m} (w r a c u v g : Fin m)
    (hh : Derives Γ (lifted w r a c u v g)) :
    Derives Γ (RelationGraphSyntax.functionGraph SyntaxIndexLiftSyntax.matrix (Source.SetLanguage.args2 r a) u g) := by
  have ht : Derives Γ (indexMap w g u v) := .conjL (.conjR (.conjR (.conjR hh)))
  exact .conjI (.conjL (.conjR ht)) (.conjR (.conjR (.conjR (.conjR hh))))

theorem target_map {m} {Γ : Context m} (w r a c u v g : Fin m)
    (hh : Derives Γ (lifted w r a c u v g)) : Derives Γ (indexMap w g u v) := .conjL (.conjR (.conjR (.conjR hh)))

theorem exists_lift {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c u v : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (indexMap w r a c))
    (hu : Derives Γ (successor u a)) (hv : Derives Γ (successor v c)) : Derives Γ (existsLift w r a c u v) := by
  let ρ := Source.SetLanguage.args2 r a
  have ht := SyntaxIndexLiftExistence.total hZ ρ w c u hw hm hu
  have hb := SyntaxIndexLiftExistence.outputs hZ ρ w c u v hw hm hv
  have he := RelationGraphFunction.exists_graph hZ SyntaxIndexLiftSyntax.matrix ρ u ht
  let G := RelationGraphSyntax.functionGraph SyntaxIndexLiftSyntax.matrix (paramsUp ρ) u.castSucc (Fin.last m)
  let Δ := Context.add G (Context.image Formula.raise Γ)
  change Derives Γ (.ex G) at he
  apply Derives.exE he
  have hZ1 := ZFContext.under hZ G
  have hw1 : Derives Δ (omega w.castSucc) := by simpa only [Formula.raise, omega_rename] using under hw G
  have hm1 : Derives Δ (indexMap w.castSucc r.castSucc a.castSucc c.castSucc) := by simpa only [Formula.raise, indexMap_rename] using under hm G
  have hu1 : Derives Δ (successor u.castSucc a.castSucc) := by simpa only [Formula.raise, successor_rename] using under hu G
  have hv1 : Derives Δ (successor v.castSucc c.castSucc) := by simpa only [Formula.raise, successor_rename] using under hv G
  have hb1 : Derives Δ (RelationGraph.outputsInto SyntaxIndexLiftSyntax.matrix (paramsUp ρ) u.castSucc v.castSucc) := by
    simpa only [Formula.raise, RelationGraph.outputsInto_rename, paramsUp] using under hb G
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hs := RelationGraph.sequence SyntaxIndexLiftSyntax.matrix _ _ _ _ hG hb1
  have huNat := OmegaStructureAlgebra.successor_member _ _ _ (ZFContext.arithmetic hZ1).base.extensionality hw1 (.conjL (.conjL hm1)) hu1
  have hvNat := OmegaStructureAlgebra.successor_member _ _ _ (ZFContext.arithmetic hZ1).base.extensionality hw1 (.conjR (.conjL hm1)) hv1
  have hL : Derives Δ (lifted w.castSucc r.castSucc a.castSucc c.castSucc u.castSucc v.castSucc (Fin.last m)) :=
    .conjI hm1 (.conjI hu1 (.conjI hv1 (.conjI (.conjI (.conjI huNat hvNat) hs) (.conjR hG))))
  have ho : Derives Δ (existsLift w.castSucc r.castSucc a.castSucc c.castSucc u.castSucc v.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, lifted_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hL
  simpa only [Formula.raise, existsLift_rename] using ho

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c u v g h : Fin m)
    (hg : Derives Γ (lifted w r a c u v g)) (hh : Derives Γ (lifted w r a c u v h)) : Derives Γ (.equal g h) :=
  RelationGraph.unique_graph hZ SyntaxIndexLiftSyntax.matrix (Source.SetLanguage.args2 r a) u g h
    (as_function_graph _ _ _ _ _ _ _ hg) (as_function_graph _ _ _ _ _ _ _ hh)

theorem actual_fiber {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c u v : Fin m)
    (hw : Derives Γ (omega w)) (hm : Derives Γ (indexMap w r a c))
    (hu : Derives Γ (successor u a)) (hv : Derives Γ (successor v c)) : Derives Γ (liftFiber w r a c u v) := by
  have he := exists_lift hZ w r a c u v hw hm hu hv
  let G := lifted w.castSucc r.castSucc a.castSucc c.castSucc u.castSucc v.castSucc (Fin.last m)
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  change Derives Γ (.ex G) at he
  apply Derives.exE he
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have huniq : Derives Ξ (.all ((lifted w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc
      u.castSucc.castSucc v.castSucc.castSucc (Fin.last (m+1))).imp
        (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let H := lifted w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc
      u.castSucc.castSucc v.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add H (Context.image Formula.raise Ξ)
    have hg2 : Derives Δ (lifted w.castSucc.castSucc r.castSucc.castSucc a.castSucc.castSucc c.castSucc.castSucc
        u.castSucc.castSucc v.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [G, Formula.raise, lifted_rename] using under hG H
    exact unique (ZFContext.under (ZFContext.under hZ G) H) _ _ _ _ _ _ _ _ (.hyp (Or.inl rfl)) hg2
  have ho : Derives Ξ (liftFiber w.castSucc r.castSucc a.castSucc c.castSucc u.castSucc v.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, lifted_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hG huniq
  simpa only [Formula.raise, liftFiber_rename] using ho

theorem edge_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w r a c u v g i j : Fin m)
    (hw : Derives Γ (omega w)) (hl : Derives Γ (lifted w r a c u v g)) :
    Derives Γ ((edge g i j).iff (value r a i j)) := by
  have hh := RelationGraphSyntax.law_at SyntaxIndexLiftSyntax.matrix (Source.SetLanguage.args2 r a) u g i j
    (.conjR (as_function_graph w r a c u v g hl))
  have he : Derives Γ ((edge g i j).iff ((Formula.mem i u).conj (value r a i j))) := by
    simpa only [SyntaxIndexLiftSyntax.matrix_rel, PairSyntax.args2_first, PairSyntax.args2_second] using hh
  apply Derives.conjI
  · apply Derives.impI
    exact .conjR (.impE (add (.conjL he) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    let V := value r a i j
    have hV : Derives (Context.add V Γ) V := .hyp (Or.inl rfl)
    have hi := SyntaxIndexLiftPoint.source_member (ZFContext.add hZ V) w r a u i j (add hw V)
      (add (.conjL (.conjL (.conjL hl))) V) (add (.conjL (.conjR hl)) V) hV
    exact .impE (add (.conjR he) V) (.conjI hi hV)
end PPAC.Migration.Internal.SyntaxIndexLift
