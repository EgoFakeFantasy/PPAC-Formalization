import PPAC.Migration.RestrictionSyntax

/-! 限制图的全部边：原边与输入属于限制集合的合取。 -/
namespace PPAC.Migration.RestrictionEdges
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax GraphLogic RestrictionSyntax

theorem old_edge {m} {Γ : Context m} (g f b x y : Fin m)
    (hr : Derives Γ (restrict g f b)) (hxy : Derives Γ (edge g x y)) : Derives Γ (edge f x y) := by
  let Q := (Formula.mem (Fin.last m) g.castSucc).conj (ordered (Fin.last m) x.castSucc y.castSucc)
  let Γq := Context.add Q (Context.image Formula.raise Γ)
  apply edge_elim g x y _ hxy
  have hrQ : Derives Γq (restrict g.castSucc f.castSucc b.castSucc) := by
    simpa only [Formula.raise, restrict_rename] using under hr Q
  have hQ : Derives Γq Q := .hyp (Or.inl rfl)
  have hc := Derives.impE (.conjL (restrict_at g.castSucc f.castSucc b.castSucc (Fin.last m) hrQ)) (.conjL hQ)
  have he := edge_intro f.castSucc x.castSucc y.castSucc (Fin.last m) (.conjL hc) (.conjR hQ)
  simpa only [Formula.raise, edge_rename] using he

theorem input_in_subset {m} {Γ : Context m} (g f b x y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hr : Derives Γ (restrict g f b)) (hxy : Derives Γ (edge g x y)) : Derives Γ (.mem x b) := by
  let Q := (Formula.mem (Fin.last m) g.castSucc).conj (ordered (Fin.last m) x.castSucc y.castSucc)
  let Γq := Context.add Q (Context.image Formula.raise Γ)
  apply edge_elim g x y _ hxy
  have heQ : Derives Γq (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he Q
  have hrQ : Derives Γq (restrict g.castSucc f.castSucc b.castSucc) := by
    simpa only [Formula.raise, restrict_rename] using under hr Q
  have hQ : Derives Γq Q := .hyp (Or.inl rfl)
  have hc := Derives.impE (.conjL (restrict_at g.castSucc f.castSucc b.castSucc (Fin.last m) hrQ)) (.conjL hQ)
  exact GraphProperties.entry_input b.castSucc (Fin.last m) x.castSucc y.castSucc heQ (.conjR hQ) (.conjR hc)

theorem restricted_edge {m} {Γ : Context m} (g f b x y : Fin m)
    (hr : Derives Γ (restrict g f b)) (hxy : Derives Γ (edge f x y)) (hx : Derives Γ (.mem x b)) :
    Derives Γ (edge g x y) := by
  let Q := (Formula.mem (Fin.last m) f.castSucc).conj (ordered (Fin.last m) x.castSucc y.castSucc)
  let Γq := Context.add Q (Context.image Formula.raise Γ)
  apply edge_elim f x y _ hxy
  have hrQ : Derives Γq (restrict g.castSucc f.castSucc b.castSucc) := by
    simpa only [Formula.raise, restrict_rename] using under hr Q
  have hxQ : Derives Γq (.mem x.castSucc b.castSucc) := under hx Q
  have hQ : Derives Γq Q := .hyp (Or.inl rfl)
  have hc := entry_intro b.castSucc (Fin.last m) x.castSucc y.castSucc hxQ (.conjR hQ)
  have hm := Derives.impE (.conjR (restrict_at g.castSucc f.castSucc b.castSucc (Fin.last m) hrQ)) (.conjI (.conjL hQ) hc)
  have he := edge_intro g.castSucc x.castSucc y.castSucc (Fin.last m) hm (.conjR hQ)
  simpa only [Formula.raise, edge_rename] using he

theorem edge_iff {m} {Γ : Context m} (g f b x y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0)) (hr : Derives Γ (restrict g f b)) :
    Derives Γ ((edge g x y).iff ((edge f x y).conj (.mem x b))) := by
  apply Derives.conjI
  · apply Derives.impI
    exact .conjI (old_edge g f b x y (add hr _) (.hyp (Or.inl rfl)))
      (input_in_subset g f b x y (add he _) (add hr _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact restricted_edge g f b x y (add hr _) (.conjL (.hyp (Or.inl rfl))) (.conjR (.hyp (Or.inl rfl)))

theorem all_edges {m} {Γ : Context m} (g f b : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0)) (hr : Derives Γ (restrict g f b)) :
    Derives Γ (edgeLaw g f b) := by
  apply Derives.allI
  apply Derives.allI
  let Δ := Context.image Formula.raise (Context.image Formula.raise Γ)
  have he' : Derives Δ (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc he)
  have hr' : Derives Δ (restrict g.castSucc.castSucc f.castSucc.castSucc b.castSucc.castSucc) := by
    simpa only [Formula.raise, restrict_rename] using Derives.rename Fin.castSucc (Derives.rename Fin.castSucc hr)
  exact edge_iff g.castSucc.castSucc f.castSucc.castSucc b.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) he' hr'
end PPAC.Migration.RestrictionEdges
