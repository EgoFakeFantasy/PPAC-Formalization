import PPAC.Migration.GraphLogic

/-! 完整原functionOn推出精确边定义域及单值性，适用于任意集合图。 -/
namespace PPAC.Migration.GraphProperties
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax GraphLogic OrderedPairElimination

theorem entry_input {m} {Γ : Context m} (d p x y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hp : Derives Γ (ordered p x y)) (hd : Derives Γ (entryOn d p)) : Derives Γ (.mem x d) := by
  let B := entryWitnesses d p
  let Γb := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply entry_elim d p _ hd
  have heB : Derives Γb (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under_two he B
  have hpB : Derives Γb (ordered p.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using under_two hp B
  have hB : Derives Γb B := .hyp (Or.inl rfl)
  have hc := OrderedPairLogic.injective p.castSucc.castSucc p.castSucc.castSucc
    x.castSucc.castSucc y.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) heB hpB (.conjR hB)
    (.eqRefl p.castSucc.castSucc)
  have hx := mem_subst (eq_symm (.conjL hc)) (.conjL hB)
  simpa only [Formula.raise, Formula.rename] using hx

theorem domain_of_edge {m} {Γ : Context m} (f d x y : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f d)) (hxy : Derives Γ (edge f x y)) : Derives Γ (.mem x d) := by
  let P := (Formula.mem (Fin.last m) f.castSucc).conj (ordered (Fin.last m) x.castSucc y.castSucc)
  let Γp := Context.add P (Context.image Formula.raise Γ)
  apply edge_elim f x y _ hxy
  have heP : Derives Γp (Source.SetLanguage.extensionality.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under he P
  have hfP : Derives Γp (functionOn f.castSucc d.castSucc) := by
    simpa only [Formula.raise, functionOn_rename] using under hf P
  have hP : Derives Γp P := .hyp (Or.inl rfl)
  exact entry_input d.castSucc (Fin.last m) x.castSucc y.castSucc heP (.conjR hP)
    (.impE (entries_at f.castSucc d.castSucc (Fin.last m) (.conjL hfP)) (.conjL hP))

theorem single_valued {m} {Γ : Context m} (f d x y z : Fin m)
    (he : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0))
    (hf : Derives Γ (functionOn f d)) (hy : Derives Γ (edge f x y)) (hz : Derives Γ (edge f x z)) :
    Derives Γ (.equal y z) := by
  have hx := domain_of_edge f d x y he hf hy
  have hv := Derives.impE (total_at f d x (.conjR hf)) hx
  let V := valueAt f.castSucc x.castSucc (Fin.last m)
  let Γv := Context.add V (Context.image Formula.raise Γ)
  change Derives Γ (.ex V) at hv
  apply Derives.exE (p := V) hv
  have hyV : Derives Γv (edge f.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, edge_rename] using under hy V
  have hzV : Derives Γv (edge f.castSucc x.castSucc z.castSucc) := by
    simpa only [Formula.raise, edge_rename] using under hz V
  have hV : Derives Γv V := .hyp (Or.inl rfl)
  exact eq_trans (.impE (unique_at f.castSucc x.castSucc (Fin.last m) y.castSucc hV) hyV)
    (eq_symm (.impE (unique_at f.castSucc x.castSucc (Fin.last m) z.castSucc hV) hzV))

/-- 定义域内每点都有对象输出；不从存在证明中抽取宿主数据。 -/
theorem output_exists {m} {Γ : Context m} (f d x : Fin m)
    (hf : Derives Γ (functionOn f d)) (hx : Derives Γ (.mem x d)) : Derives Γ (hasEdge f x) := by
  have hv := Derives.impE (total_at f d x (.conjR hf)) hx
  let V := valueAt f.castSucc x.castSucc (Fin.last m)
  let Γv := Context.add V (Context.image Formula.raise Γ)
  change Derives Γ (.ex V) at hv
  apply Derives.exE (p := V) hv
  have he : Derives Γv (edge f.castSucc x.castSucc (Fin.last m)) := .conjL (.hyp (Or.inl rfl))
  have hr : Derives Γv (hasEdge f.castSucc x.castSucc) := by
    apply Derives.exI (Fin.last m)
    simpa only [Formula.instantiate, edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using he
  simpa only [Formula.raise, hasEdge_rename] using hr
end PPAC.Migration.GraphProperties
