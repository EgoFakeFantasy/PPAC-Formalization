import PPAC.Migration.GraphDomainSyntax

/-! 原Kuratowski编码的边输入在∪∪G中，无外部秩/良基假设。 -/
namespace PPAC.Migration.GraphDomainBound
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax GraphLogic InsertSyntax InsertLogic
open OrderedPairElimination UnorderedPairLogic

theorem has_edge_intro {m} {Γ : Context m} (g x y : Fin m) (h : Derives Γ (edge g x y)) :
    Derives Γ (hasEdge g x) := by
  apply Derives.exI y
  simpa only [Formula.instantiate, edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h

theorem code_bound {m} {Γ : Context m} (g u v p x y : Fin m)
    (hu : Derives Γ (unionOf u g)) (hv : Derives Γ (unionOf v u))
    (hp : Derives Γ (.mem p g)) (hk : Derives Γ (ordered p x y)) : Derives Γ (.mem x v) := by
  let B := witnesses p x y
  let Γb := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate p x y _ hk
  have huB : Derives Γb (unionOf u.castSucc.castSucc g.castSucc.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using under_two hu B
  have hvB : Derives Γb (unionOf v.castSucc.castSucc u.castSucc.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using under_two hv B
  have hpB : Derives Γb (.mem p.castSucc.castSucc g.castSucc.castSucc) := under_two hp B
  have hB : Derives Γb B := .hyp (Or.inl rfl)
  have hsP := member_left p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) (.conjR (.conjR hB))
  have hsU := Derives.impE (.conjR (union_at u.castSucc.castSucc g.castSucc.castSucc (Fin.last m).castSucc huB))
    (fiber_intro _ _ _ hpB hsP)
  have hxS := member_left (Fin.last m).castSucc x.castSucc.castSucc x.castSucc.castSucc (.conjL hB)
  exact .impE (.conjR (union_at v.castSucc.castSucc u.castSucc.castSucc x.castSucc.castSucc hvB))
    (fiber_intro _ _ _ hsU hxS)

theorem edge_bound {m} {Γ : Context m} (g u v x y : Fin m)
    (hu : Derives Γ (unionOf u g)) (hv : Derives Γ (unionOf v u))
    (he : Derives Γ (edge g x y)) : Derives Γ (.mem x v) := by
  let Q := (Formula.mem (Fin.last m) g.castSucc).conj (ordered (Fin.last m) x.castSucc y.castSucc)
  let Γq := Context.add Q (Context.image Formula.raise Γ)
  apply edge_elim g x y _ he
  have huQ : Derives Γq (unionOf u.castSucc g.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using under hu Q
  have hvQ : Derives Γq (unionOf v.castSucc u.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using under hv Q
  have hQ : Derives Γq Q := .hyp (Or.inl rfl)
  exact code_bound g.castSucc u.castSucc v.castSucc (Fin.last m) x.castSucc y.castSucc huQ hvQ (.conjL hQ) (.conjR hQ)

theorem input_bound {m} {Γ : Context m} (g u v x : Fin m)
    (hu : Derives Γ (unionOf u g)) (hv : Derives Γ (unionOf v u))
    (he : Derives Γ (hasEdge g x)) : Derives Γ (.mem x v) := by
  let E := edge g.castSucc x.castSucc (Fin.last m)
  let Γe := Context.add E (Context.image Formula.raise Γ)
  change Derives Γ (.ex E) at he
  apply Derives.exE (p := E) he
  have huE : Derives Γe (unionOf u.castSucc g.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using under hu E
  have hvE : Derives Γe (unionOf v.castSucc u.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using under hv E
  exact edge_bound g.castSucc u.castSucc v.castSucc x.castSucc (Fin.last m) huE hvE (.hyp (Or.inl rfl))
end PPAC.Migration.GraphDomainBound
