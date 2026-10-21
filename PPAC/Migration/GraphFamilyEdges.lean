import PPAC.Migration.GraphFamilySyntax

/-! 任意内部图集合族的并图具有精确的逐成员边关系。 -/
namespace PPAC.Migration.GraphFamilyEdges
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax GraphLogic InsertSyntax InsertLogic GraphFamilySyntax

theorem code_from_union {m} {Γ : Context m} (g f p x y : Fin m)
    (hu : Derives Γ (unionOf g f)) (hm : Derives Γ (.mem p g)) (hk : Derives Γ (ordered p x y)) :
    Derives Γ (memberEdge f x y) := by
  have he := Derives.impE (.conjL (union_at g f p hu)) hm
  let H := (Formula.mem (Fin.last m) f.castSucc).conj (.mem p.castSucc (Fin.last m))
  let Γh := Context.add H (Context.image Formula.raise Γ)
  change Derives Γ (.ex H) at he
  apply Derives.exE (p := H) he
  have hkH : Derives Γh (ordered p.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using under hk H
  have hH : Derives Γh H := .hyp (Or.inl rfl)
  have hr := member_edge_intro f.castSucc (Fin.last m) x.castSucc y.castSucc (.conjL hH)
    (edge_intro (Fin.last m) x.castSucc y.castSucc p.castSucc (.conjR hH) hkH)
  simpa only [Formula.raise, memberEdge_rename] using hr

theorem edge_from_union {m} {Γ : Context m} (g f x y : Fin m)
    (hu : Derives Γ (unionOf g f)) (he : Derives Γ (edge g x y)) : Derives Γ (memberEdge f x y) := by
  let Q := (Formula.mem (Fin.last m) g.castSucc).conj (ordered (Fin.last m) x.castSucc y.castSucc)
  let Γq := Context.add Q (Context.image Formula.raise Γ)
  apply edge_elim g x y _ he
  have huQ : Derives Γq (unionOf g.castSucc f.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using under hu Q
  have hQ : Derives Γq Q := .hyp (Or.inl rfl)
  have hr := code_from_union g.castSucc f.castSucc (Fin.last m) x.castSucc y.castSucc huQ (.conjL hQ) (.conjR hQ)
  simpa only [Formula.raise, memberEdge_rename] using hr

theorem edge_into_union {m} {Γ : Context m} (g f h x y : Fin m)
    (hu : Derives Γ (unionOf g f)) (hm : Derives Γ (.mem h f)) (he : Derives Γ (edge h x y)) :
    Derives Γ (edge g x y) := by
  let Q := (Formula.mem (Fin.last m) h.castSucc).conj (ordered (Fin.last m) x.castSucc y.castSucc)
  let Γq := Context.add Q (Context.image Formula.raise Γ)
  apply edge_elim h x y _ he
  have huQ : Derives Γq (unionOf g.castSucc f.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using under hu Q
  have hmQ : Derives Γq (.mem h.castSucc f.castSucc) := under hm Q
  have hQ : Derives Γq Q := .hyp (Or.inl rfl)
  have hpG := Derives.impE (.conjR (union_at g.castSucc f.castSucc (Fin.last m) huQ))
    (fiber_intro f.castSucc (Fin.last m) h.castSucc hmQ (.conjL hQ))
  have hr := edge_intro g.castSucc x.castSucc y.castSucc (Fin.last m) hpG (.conjR hQ)
  simpa only [Formula.raise, edge_rename] using hr

theorem member_into_union {m} {Γ : Context m} (g f x y : Fin m)
    (hu : Derives Γ (unionOf g f)) (he : Derives Γ (memberEdge f x y)) : Derives Γ (edge g x y) := by
  let H := (Formula.mem (Fin.last m) f.castSucc).conj (edge (Fin.last m) x.castSucc y.castSucc)
  let Γh := Context.add H (Context.image Formula.raise Γ)
  change Derives Γ (.ex H) at he
  apply Derives.exE (p := H) he
  have huH : Derives Γh (unionOf g.castSucc f.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using under hu H
  have hH : Derives Γh H := .hyp (Or.inl rfl)
  have hr := edge_into_union g.castSucc f.castSucc (Fin.last m) x.castSucc y.castSucc huH (.conjL hH) (.conjR hH)
  simpa only [Formula.raise, edge_rename] using hr

theorem all_edges {m} {Γ : Context m} (g f : Fin m)
    (hu : Derives Γ (unionOf g f)) : Derives Γ (edgeLaw g f) := by
  apply Derives.allI
  apply Derives.allI
  have hu' : Derives (Context.image Formula.raise (Context.image Formula.raise Γ))
      (unionOf g.castSucc.castSucc f.castSucc.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hu)
  apply Derives.conjI
  · apply Derives.impI
    exact edge_from_union g.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
      (add hu' _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact member_into_union g.castSucc.castSucc f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
      (add hu' _) (.hyp (Or.inl rfl))
end PPAC.Migration.GraphFamilyEdges
