import PPAC.Migration.Internal.RelationGraphPairs

/-! 关系精确像的原图排杂项和全内部边双条件，保留任意矩阵及参数。 -/
namespace PPAC.Migration.Internal.RelationGraphEdges
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax ReplacementPredicates RelationGraphSyntax

theorem decode_entry {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (P : Formula (n+2)) (ρ : Fin n → Fin m)
    (d g p x y : Fin m) (hg : Derives Γ (pairGraph P ρ d g)) (hp : Derives Γ (.mem p g))
    (ho : Derives Γ (ordered p x y)) : Derives Γ ((Formula.mem x d).conj (rel P ρ x y)) := by
  have he := Derives.impE (.conjL (graph_at P ρ d g p hg)) hp
  let X := (Formula.mem (Fin.last m) d.castSucc).conj (entry P (paramsUp ρ) (Fin.last m) p.castSucc)
  let Ξ := Context.add X (Context.image Formula.raise Γ)
  change Derives Γ (.ex X) at he
  apply Derives.exE he
  have hX : Derives Ξ X := .hyp (Or.inl rfl)
  let Y := (rel P (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1))).conj
    (ordered p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add Y (Context.image Formula.raise Ξ)
  have hy : Derives Ξ (.ex Y) := .conjR hX
  apply Derives.exE hy
  have hZ2 := ZFContext.under (ZFContext.under hZ X) Y
  have ho2 : Derives Δ (ordered p.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using under (under ho X) Y
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have heq := OrderedPairLogic.injective _ _ _ _ _ _ (ZFContext.arithmetic hZ2).base.extensionality (.conjR hY) ho2 (.eqRefl _)
  have hm := mem_subst (.conjL heq) (under (.conjL hX) Y)
  have hr := CheckedSequence.rel_subst_left P _ _ _ _ (.conjL heq) (.conjL hY)
  have hs := CheckedSequence.rel_subst_right P _ _ _ _ (.conjR heq) hr
  simpa only [Formula.raise, Formula.rename, rel_rename, paramsUp] using Derives.conjI hm hs

theorem entry_on {n m} {Γ : Context m} (P : Formula (n+2)) (ρ : Fin n → Fin m)
    (d g p : Fin m) (hg : Derives Γ (pairGraph P ρ d g)) (hp : Derives Γ (.mem p g)) : Derives Γ (entryOn d p) := by
  have he := Derives.impE (.conjL (graph_at P ρ d g p hg)) hp
  let X := (Formula.mem (Fin.last m) d.castSucc).conj (entry P (paramsUp ρ) (Fin.last m) p.castSucc)
  let Ξ := Context.add X (Context.image Formula.raise Γ)
  change Derives Γ (.ex X) at he
  apply Derives.exE he
  have hX : Derives Ξ X := .hyp (Or.inl rfl)
  let Y := (rel P (paramsUp (paramsUp ρ)) (Fin.last m).castSucc (Fin.last (m+1))).conj
    (ordered p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))
  let Δ := Context.add Y (Context.image Formula.raise Ξ)
  have hy : Derives Ξ (.ex Y) := .conjR hX
  apply Derives.exE hy
  have hY : Derives Δ Y := .hyp (Or.inl rfl)
  have hout := GraphLogic.entry_intro _ _ _ _ (under (.conjL hX) Y) (.conjR hY)
  simpa only [Formula.raise, entryOn_rename] using hout

theorem entries {n m} {Γ : Context m} (P : Formula (n+2)) (ρ : Fin n → Fin m) (d g : Fin m)
    (hg : Derives Γ (pairGraph P ρ d g)) : Derives Γ (entriesOn g d) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) g.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hg1 : Derives Δ (pairGraph P (paramsUp ρ) d.castSucc g.castSucc) := by
    simpa only [Formula.raise, pairGraph_rename, paramsUp] using under hg M
  exact entry_on P _ _ _ _ hg1 (.hyp (Or.inl rfl))

theorem decode_edge {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (P : Formula (n+2)) (ρ : Fin n → Fin m)
    (d g x y : Fin m) (hg : Derives Γ (pairGraph P ρ d g)) (hy : Derives Γ (edge g x y)) :
    Derives Γ ((Formula.mem x d).conj (rel P ρ x y)) := by
  let Q := (Formula.mem (Fin.last m) g.castSucc).conj (ordered (Fin.last m) x.castSucc y.castSucc)
  let Δ := Context.add Q (Context.image Formula.raise Γ)
  apply GraphLogic.edge_elim g x y _ hy
  have hg1 : Derives Δ (pairGraph P (paramsUp ρ) d.castSucc g.castSucc) := by
    simpa only [Formula.raise, pairGraph_rename, paramsUp] using under hg Q
  have hQ : Derives Δ Q := .hyp (Or.inl rfl)
  have ho := decode_entry (ZFContext.under hZ Q) P _ _ _ _ _ _ hg1 (.conjL hQ) (.conjR hQ)
  simpa only [Formula.raise, Formula.rename, rel_rename, paramsUp] using ho

theorem build_edge {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (P : Formula (n+2)) (ρ : Fin n → Fin m)
    (d g x y : Fin m) (hg : Derives Γ (pairGraph P ρ d g)) (hx : Derives Γ (.mem x d))
    (hy : Derives Γ (rel P ρ x y)) : Derives Γ (edge g x y) := by
  have he := OrderedPairExistence.exists_pair x y (ZFContext.arithmetic hZ).base.pairing
  let O := ordered (Fin.last m) x.castSucc y.castSucc
  let Δ := Context.add O (Context.image Formula.raise Γ)
  change Derives Γ (.ex O) at he
  apply Derives.exE he
  have hg1 : Derives Δ (pairGraph P (paramsUp ρ) d.castSucc g.castSucc) := by
    simpa only [Formula.raise, pairGraph_rename, paramsUp] using under hg O
  have hy1 : Derives Δ (rel P (paramsUp ρ) x.castSucc y.castSucc) := by
    simpa only [Formula.raise, rel_rename, paramsUp] using under hy O
  have hO : Derives Δ O := .hyp (Or.inl rfl)
  have he1 := intro_entry P _ _ _ _ hy1 hO
  have hi := intro_image P _ _ _ _ (under hx O) he1
  have hm := Derives.impE (.conjR (graph_at P _ _ _ _ hg1)) hi
  have ho := GraphLogic.edge_intro _ _ _ _ hm hO
  simpa only [Formula.raise, edge_rename] using ho

theorem edge_iff {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (P : Formula (n+2)) (ρ : Fin n → Fin m)
    (d g x y : Fin m) (hg : Derives Γ (pairGraph P ρ d g)) :
    Derives Γ ((edge g x y).iff ((Formula.mem x d).conj (rel P ρ x y))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact decode_edge (ZFContext.add hZ _) P ρ d g x y (add hg _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    have hB : Derives (Context.add ((Formula.mem x d).conj (rel P ρ x y)) Γ) ((Formula.mem x d).conj (rel P ρ x y)) := .hyp (Or.inl rfl)
    exact build_edge (ZFContext.add hZ _) P ρ d g x y (add hg _) (.conjL hB) (.conjR hB)

theorem full_law {n m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (P : Formula (n+2)) (ρ : Fin n → Fin m)
    (d g : Fin m) (hg : Derives Γ (pairGraph P ρ d g)) : Derives Γ (edgeLaw P ρ d g) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have hg2 : Derives Δ (pairGraph P (paramsUp (paramsUp ρ)) d.castSucc.castSucc g.castSucc.castSucc) := by
    simpa only [Formula.raise, pairGraph_rename, paramsUp] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hg)
  exact edge_iff (ZFContext.rename (ZFContext.rename hZ Fin.castSucc) Fin.castSucc) P _ _ _ _ _ hg2
end PPAC.Migration.Internal.RelationGraphEdges
