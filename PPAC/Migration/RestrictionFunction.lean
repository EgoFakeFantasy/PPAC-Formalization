import PPAC.Migration.RestrictionEdges

/-! 子定义域限制保持完整原functionOn；每个域内点的唯一值实际回放。 -/
namespace PPAC.Migration.RestrictionFunction
open Source SourceAlgebra SourceLogic PairSyntax GraphSyntax GraphLogic RestrictionSyntax RestrictionEdges

theorem restricted_value {m} {Γ : Context m} (g f b x y : Fin m)
    (hr : Derives Γ (restrict g f b)) (hx : Derives Γ (.mem x b)) (hv : Derives Γ (valueAt f x y)) :
    Derives Γ (valueAt g x y) := by
  apply Derives.conjI (restricted_edge g f b x y hr (.conjL hv) hx)
  apply Derives.allI
  have hr' : Derives (Context.image Formula.raise Γ) (restrict g.castSucc f.castSucc b.castSucc) := by
    simpa only [Formula.raise, restrict_rename] using Derives.rename Fin.castSucc hr
  have hv' : Derives (Context.image Formula.raise Γ) (valueAt f.castSucc x.castSucc y.castSucc) := by
    simpa only [Formula.raise, valueAt_rename] using Derives.rename Fin.castSucc hv
  apply Derives.impI
  have he := old_edge g.castSucc f.castSucc b.castSucc x.castSucc (Fin.last m)
    (add hr' (edge g.castSucc x.castSucc (Fin.last m))) (.hyp (Or.inl rfl))
  exact .impE (unique_at f.castSucc x.castSucc y.castSucc (Fin.last m) (add hv' _)) he

theorem restricted_total {m} {Γ : Context m} (g f d b x : Fin m)
    (hf : Derives Γ (functionOn f d)) (hr : Derives Γ (restrict g f b))
    (hb : Derives Γ (.mem x b)) (hd : Derives Γ (.mem x d)) : Derives Γ (valueExists g x) := by
  have hv := Derives.impE (total_at f d x (.conjR hf)) hd
  let V := valueAt f.castSucc x.castSucc (Fin.last m)
  let Γv := Context.add V (Context.image Formula.raise Γ)
  change Derives Γ (.ex V) at hv
  apply Derives.exE (p := V) hv
  have hrV : Derives Γv (restrict g.castSucc f.castSucc b.castSucc) := by
    simpa only [Formula.raise, restrict_rename] using under hr V
  have hbV : Derives Γv (.mem x.castSucc b.castSucc) := under hb V
  have hV : Derives Γv V := .hyp (Or.inl rfl)
  have ho := value_exists g.castSucc x.castSucc (Fin.last m)
    (restricted_value g.castSucc f.castSucc b.castSucc x.castSucc (Fin.last m) hrV hbV hV)
  simpa only [Formula.raise, valueExists_rename] using ho

theorem function_restrict {m} {Γ : Context m} (g f d b : Fin m)
    (hf : Derives Γ (functionOn f d)) (hb : Derives Γ (subset b d)) (hr : Derives Γ (restrict g f b)) :
    Derives Γ (functionOn g b) := by
  apply Derives.conjI
  · apply Derives.allI
    have hr' : Derives (Context.image Formula.raise Γ) (restrict g.castSucc f.castSucc b.castSucc) := by
      simpa only [Formula.raise, restrict_rename] using Derives.rename Fin.castSucc hr
    apply Derives.impI
    exact .conjR (.impE (.conjL (restrict_at g.castSucc f.castSucc b.castSucc (Fin.last m) (add hr' _))) (.hyp (Or.inl rfl)))
  · apply Derives.allI
    have hf' : Derives (Context.image Formula.raise Γ) (functionOn f.castSucc d.castSucc) := by
      simpa only [Formula.raise, functionOn_rename] using Derives.rename Fin.castSucc hf
    have hb' : Derives (Context.image Formula.raise Γ) (subset b.castSucc d.castSucc) := by
      simpa only [Formula.raise, subset_rename] using Derives.rename Fin.castSucc hb
    have hr' : Derives (Context.image Formula.raise Γ) (restrict g.castSucc f.castSucc b.castSucc) := by
      simpa only [Formula.raise, restrict_rename] using Derives.rename Fin.castSucc hr
    apply Derives.impI
    let M := Formula.mem (Fin.last m) b.castSucc
    have hx : Derives (Context.add M (Context.image Formula.raise Γ)) M := .hyp (Or.inl rfl)
    exact restricted_total g.castSucc f.castSucc d.castSucc b.castSucc (Fin.last m)
      (add hf' M) (add hr' M) hx (.impE (subset_at b.castSucc d.castSucc (Fin.last m) (add hb' M)) hx)
end PPAC.Migration.RestrictionFunction
