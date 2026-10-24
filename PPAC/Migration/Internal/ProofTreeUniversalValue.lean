import PPAC.Migration.Internal.ProofTreeUniversalSyntax

/-! ZF内实际取得全部原轨迹根集合，并包含每个内部闭轨迹；不选择外部轨迹函数。 -/
namespace PPAC.Migration.Internal.ProofTreeUniversalValue
open Source SourceAlgebra SourceLogic ProofTreeUniversalSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem exists_value {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w : Fin m) : Derives Γ (existsValue test w) := by
  have hh := MinimalInstances.separation_instance (ProofTreeUniversalSyntax.matrix test) (one w) w (ZFContext.separation hZ (ProofTreeUniversalSyntax.matrix test))
  have hm : ReplacementPredicates.paramsUp (one w) = one w.castSucc := rfl
  exact of_eq (by simp only [MinimalPredicates.separationExists, existsValue, value, hm]) hh

theorem subset {m} {Γ : Context m} (test : Formula 1) (w V : Fin m) (hv : Derives Γ (value test w V)) : Derives Γ (RestrictionSyntax.subset V w) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) V.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hv1 : Derives Δ (value test w.castSucc V.castSucc) := of_eq (value_rename test w V Fin.castSucc) (under hv M)
  exact .conjL (.impE (.conjL (value_at test _ _ _ hv1)) (.hyp (Or.inl rfl)))

theorem condition_natural {m} {Γ : Context m} (test : Formula 1) (w r : Fin m)
    (hc : Derives Γ (ProofTreeTraceSyntax.condition test w r)) : Derives Γ (.mem r w) := by
  let B := ProofTreeTraceSyntax.witness test w.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) hc
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  exact .impE (RestrictionSyntax.subset_at _ _ _ (.conjL hB)) (.conjL (.conjR hB))

theorem member_iff {m} {Γ : Context m} (test : Formula 1) (w V r : Fin m) (hv : Derives Γ (value test w V)) :
    Derives Γ ((Formula.mem r V).iff (ProofTreeTraceSyntax.condition test w r)) := by
  have he := value_at test w V r hv
  apply Derives.conjI
  · apply Derives.impI
    exact .conjR (.impE (add (.conjL he) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    have hc : Derives (Context.add (ProofTreeTraceSyntax.condition test w r) Γ) (ProofTreeTraceSyntax.condition test w r) := .hyp (Or.inl rfl)
    exact .impE (add (.conjR he) _) (.conjI (condition_natural test w r hc) hc)

theorem subtrace_included {m} {Γ : Context m} (test : Formula 1) (w V R : Fin m) (hv : Derives Γ (value test w V))
    (hs : Derives Γ (RestrictionSyntax.subset R w)) (hc : Derives Γ (ProofTreeTraceSyntax.closed test w R)) :
    Derives Γ (RestrictionSyntax.subset R V) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) R.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hv1 : Derives Δ (value test w.castSucc V.castSucc) := of_eq (value_rename test w V Fin.castSucc) (under hv M)
  have hs1 : Derives Δ (RestrictionSyntax.subset R.castSucc w.castSucc) := of_eq (RestrictionSyntax.subset_rename R w Fin.castSucc) (under hs M)
  have hc1 : Derives Δ (ProofTreeTraceSyntax.closed test w.castSucc R.castSucc) := of_eq (ProofTreeTraceSyntax.closed_rename test w R Fin.castSucc) (under hc M)
  have hm : Derives Δ M := .hyp (Or.inl rfl)
  have ht := ProofTreeTraceSyntax.intro_condition test w.castSucc (Fin.last m) R.castSucc (.conjI hs1 (.conjI hm hc1))
  exact .impE (.conjR (member_iff test _ _ _ hv1)) ht

end PPAC.Migration.Internal.ProofTreeUniversalValue
