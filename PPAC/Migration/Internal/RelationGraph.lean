import PPAC.Migration.Internal.RelationGraphFunction

/-! 任意参数对象函数关系的实际唯一完整图纤维及指定值域保持。 -/
namespace PPAC.Migration.Internal.RelationGraph
open Source SourceAlgebra SourceLogic GraphSyntax ReplacementPredicates RelationGraphSyntax

def outputsInto {n m} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d c : Fin m) : Formula m := .all (.all
  (((Formula.mem (Fin.last m).castSucc d.castSucc.castSucc).conj
    (rel P (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1)))).imp
      (.mem (Fin.last (m+1)) c.castSucc.castSucc)))

theorem outputsInto_rename {n m k} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d c : Fin m) (r : Fin m → Fin k) :
    (outputsInto P ρ d c).rename r = outputsInto P (fun i => r (ρ i)) (r d) (r c) := by
  simp only [outputsInto, Formula.rename, rel_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem outputs_at {n m} {Γ : Context m} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d c x y : Fin m)
    (hh : Derives Γ (outputsInto P ρ d c)) :
    Derives Γ (((Formula.mem x d).conj (rel P ρ x y)).imp (.mem y c)) := by
  simpa only [outputsInto, Formula.instantiate, Formula.rename, rel_rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE y (Derives.allE x hh)

theorem included {n m} {Γ : Context m} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d g h : Fin m)
    (hg : Derives Γ (edgeLaw P ρ d g)) (hh : Derives Γ (edgeLaw P ρ d h)) :
    Derives Γ (GraphPointwiseSyntax.edgeIncluded g h) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hg2 : Derives Δ (edgeLaw P (paramsUp (paramsUp ρ)) d.castSucc.castSucc g.castSucc.castSucc) := by
    simpa only [Formula.raise, edgeLaw_rename, paramsUp] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hg)
  have hh2 : Derives Δ (edgeLaw P (paramsUp (paramsUp ρ)) d.castSucc.castSucc h.castSucc.castSucc) := by
    simpa only [Formula.raise, edgeLaw_rename, paramsUp] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hh)
  have hl := law_at P _ _ _ (Fin.last m).castSucc (Fin.last (m+1)) hg2
  have hr := law_at P _ _ _ (Fin.last m).castSucc (Fin.last (m+1)) hh2
  apply Derives.impI
  exact .impE (add (.conjR hr) _) (.impE (add (.conjL hl) _) (.hyp (Or.inl rfl)))

theorem unique_graph {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (P : Formula (n+2)) (ρ : Fin n → Fin m)
    (d g h : Fin m) (hg : Derives Γ (functionGraph P ρ d g)) (hh : Derives Γ (functionGraph P ρ d h)) :
    Derives Γ (.equal g h) :=
  GraphPointwiseEntries.equal_of_edges g h d d (ZFContext.arithmetic hZ).base.extensionality
    (.conjL (.conjL hg)) (.conjL (.conjL hh))
    (.conjI (included P ρ d g h (.conjR hg) (.conjR hh)) (included P ρ d h g (.conjR hh) (.conjR hg)))

theorem actual_fiber {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (P : Formula (n+2)) (ρ : Fin n → Fin m)
    (d : Fin m) (ht : Derives Γ (total P ρ d)) : Derives Γ (graphFiber P ρ d) := by
  have he := RelationGraphFunction.exists_graph hZ P ρ d ht
  let G := functionGraph P (paramsUp ρ) d.castSucc (Fin.last m)
  let Ξ := Context.add G (Context.image Formula.raise Γ)
  change Derives Γ (.ex G) at he
  apply Derives.exE he
  have hG : Derives Ξ G := .hyp (Or.inl rfl)
  have hu : Derives Ξ (.all
      ((functionGraph P (paramsUp (paramsUp ρ)) d.castSucc.castSucc (Fin.last (m+1))).imp
        (.equal (Fin.last (m+1)) (Fin.last m).castSucc))) := by
    apply Derives.allI
    apply Derives.impI
    let H := functionGraph P (paramsUp (paramsUp ρ)) d.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add H (Context.image Formula.raise Ξ)
    have hg2 : Derives Δ (functionGraph P (paramsUp (paramsUp ρ)) d.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [G, Formula.raise, functionGraph_rename, paramsUp] using under hG H
    exact unique_graph (ZFContext.under (ZFContext.under hZ G) H) P _ _ _ _ (.hyp (Or.inl rfl)) hg2
  have ho : Derives Ξ (graphFiber P (paramsUp ρ) d.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, functionGraph_rename, paramsUp,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hG hu
  simpa only [Formula.raise, graphFiber_rename, paramsUp] using ho

theorem bounded {n m} {Γ : Context m} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d c g : Fin m)
    (hg : Derives Γ (functionGraph P ρ d g)) (hb : Derives Γ (outputsInto P ρ d c)) :
    Derives Γ (SequenceSyntax.bounded g c) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hg2 : Derives Δ (functionGraph P (paramsUp (paramsUp ρ)) d.castSucc.castSucc g.castSucc.castSucc) := by
    simpa only [Formula.raise, functionGraph_rename, paramsUp] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hg)
  have hb2 : Derives Δ (outputsInto P (paramsUp (paramsUp ρ)) d.castSucc.castSucc c.castSucc.castSucc) := by
    simpa only [Formula.raise, outputsInto_rename, paramsUp] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hb)
  have hl := law_at P _ _ _ (Fin.last m).castSucc (Fin.last (m+1)) (.conjR hg2)
  have hr := outputs_at P _ _ _ (Fin.last m).castSucc (Fin.last (m+1)) hb2
  apply Derives.impI
  exact .impE (add hr _) (.impE (add (.conjL hl) _) (.hyp (Or.inl rfl)))

theorem sequence {n m} {Γ : Context m} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d c g : Fin m)
    (hg : Derives Γ (functionGraph P ρ d g)) (hb : Derives Γ (outputsInto P ρ d c)) :
    Derives Γ (SequenceSyntax.sequence g d c) := .conjI (.conjL hg) (bounded P ρ d c g hg hb)
end PPAC.Migration.Internal.RelationGraph
