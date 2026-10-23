import PPAC.Migration.Internal.HornLookupTraceValueSyntax

/-! 原Separation实际构造规范成功行集合，取得每个真实成功行的成员性。 -/
namespace PPAC.Migration.Internal.HornLookupTraceValue
open Source SourceAlgebra SourceLogic OmegaSyntax HornLookupRowSyntax HornLookupTraceValueSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem exists_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w : Fin m) : Derives Γ (existsValue w) := by
  have hh := MinimalInstances.separation_instance HornLookupTraceValueSyntax.matrix (one w) w (ZFContext.separation hZ HornLookupTraceValueSyntax.matrix)
  have hm : ReplacementPredicates.paramsUp (one w) = one w.castSucc := rfl
  exact of_eq (by simp only [MinimalPredicates.separationExists, existsValue, value, hm]) hh

theorem subset {m} {Γ : Context m} (w R : Fin m) (hv : Derives Γ (value w R)) : Derives Γ (RestrictionSyntax.subset R w) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) R.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hv1 : Derives Δ (value w.castSucc R.castSucc) := of_eq (value_rename w R Fin.castSucc) (under hv M)
  exact .conjL (.impE (.conjL (value_at _ _ _ hv1)) (.hyp (Or.inl rfl)))

theorem successful_member {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R n i y r : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (value w R)) (hr : Derives Γ (row w n i y r))
    (he : Derives Γ (LookupTableExecutionSyntax.executed w n i y)) : Derives Γ (.mem r R) :=
  .impE (.conjR (value_at w R r hv)) (.conjI (code_natural hZ w n i y r hw hr) (intro_good w n i y r hr he))

end PPAC.Migration.Internal.HornLookupTraceValue
