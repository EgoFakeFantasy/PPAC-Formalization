import PPAC.Migration.GraphFamilyEntries

/-! 相容图族并图的实际定义域上，每点存在唯一输出。 -/
namespace PPAC.Migration.GraphFamilyFunction
open Source SourceAlgebra SourceLogic GraphSyntax GraphLogic InsertSyntax GraphDomainSyntax GraphFamilySyntax

theorem value_exists_from_edge {m} {Γ : Context m} (g f x : Fin m)
    (hu : Derives Γ (unionOf g f)) (hc : Derives Γ (compatible f)) (hx : Derives Γ (hasEdge g x)) :
    Derives Γ (valueExists g x) := by
  let Y := edge g.castSucc x.castSucc (Fin.last m)
  let Γy := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hx
  apply Derives.exE (p := Y) hx
  have huY : Derives Γy (unionOf g.castSucc f.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using under hu Y
  have hcY : Derives Γy (compatible f.castSucc) := by
    simpa only [Formula.raise, compatible_rename] using under hc Y
  have hy : Derives Γy Y := .hyp (Or.inl rfl)
  have hv : Derives Γy (valueAt g.castSucc x.castSucc (Fin.last m)) := by
    apply Derives.conjI hy
    apply Derives.allI
    have huZ : Derives (Context.image Formula.raise Γy) (unionOf g.castSucc.castSucc f.castSucc.castSucc) := by
      simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc huY
    have hcZ : Derives (Context.image Formula.raise Γy) (compatible f.castSucc.castSucc) := by
      simpa only [Formula.raise, compatible_rename] using Derives.rename Fin.castSucc hcY
    have hyZ : Derives (Context.image Formula.raise Γy) (edge g.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [Formula.raise, Y, edge_rename] using Derives.rename Fin.castSucc hy
    apply Derives.impI
    exact GraphFamilyValues.single_valued g.castSucc.castSucc f.castSucc.castSucc x.castSucc.castSucc
      (Fin.last (m+1)) (Fin.last m).castSucc (add huZ _) (add hcZ _) (.hyp (Or.inl rfl)) (add hyZ _)
  have hr := value_exists g.castSucc x.castSucc (Fin.last m) hv
  simpa only [Formula.raise, valueExists_rename] using hr

theorem total_on {m} {Γ : Context m} (g d f : Fin m)
    (hu : Derives Γ (unionOf g f)) (hd : Derives Γ (domain d g)) (hc : Derives Γ (compatible f)) :
    Derives Γ (totalOn g d) := by
  apply Derives.allI
  have hu' : Derives (Context.image Formula.raise Γ) (unionOf g.castSucc f.castSucc) := by
    simpa only [Formula.raise, unionOf_rename] using Derives.rename Fin.castSucc hu
  have hd' : Derives (Context.image Formula.raise Γ) (domain d.castSucc g.castSucc) := by
    simpa only [Formula.raise, domain_rename] using Derives.rename Fin.castSucc hd
  have hc' : Derives (Context.image Formula.raise Γ) (compatible f.castSucc) := by
    simpa only [Formula.raise, compatible_rename] using Derives.rename Fin.castSucc hc
  apply Derives.impI
  let M := Formula.mem (Fin.last m) d.castSucc
  have hx := Derives.impE (.conjL (domain_at d.castSucc g.castSucc (Fin.last m) (add hd' M))) (.hyp (Or.inl rfl))
  exact value_exists_from_edge g.castSucc f.castSucc (Fin.last m) (add hu' M) (add hc' M) hx

theorem function_on {m} {Γ : Context m} (g d f : Fin m)
    (hu : Derives Γ (unionOf g f)) (hd : Derives Γ (domain d g))
    (hf : Derives Γ (graphs f)) (hc : Derives Γ (compatible f)) : Derives Γ (functionOn g d) :=
  .conjI (GraphFamilyEntries.entries_on g d f hu hd hf) (total_on g d f hu hd hc)
end PPAC.Migration.GraphFamilyFunction
