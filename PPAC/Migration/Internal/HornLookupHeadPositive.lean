import PPAC.Migration.Internal.HornLookupPositiveSyntax

/-! 零索引实际Cons头返回原lookupHead量化应用及完整原规则表步骤。 -/
namespace PPAC.Migration.Internal.HornLookupHeadPositive
open Source SourceAlgebra SourceLogic OmegaSyntax HornLookupRowSyntax HornLookupPositiveSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem step {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R n i y r : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ (row w n i y r))
    (hc : Derives Γ (LookupTableProgramSyntax.zeroCase w n i y)) : Derives Γ (HornStepSyntax.originalStep w r R) := by
  let T := StructuralListProjectionSyntax.body true w.castSucc n.castSucc y.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (.conjR hc)
  have hZ1 := ZFContext.under hZ T
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw T)
  have hr1 : Derives Δ (row w.castSucc n.castSucc i.castSucc y.castSucc r.castSucc) := of_eq (row_rename _ _ _ _ _ Fin.castSucc) (under hr T)
  have hi1 : Derives Δ (empty i.castSucc) := of_eq (empty_rename i Fin.castSucc) (under (.conjL hc) T)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have he := env2_natural w.castSucc y.castSucc (Fin.last m) (.conjL (.conjL hT)) (.conjR (.conjL hT))
  have hm := Derives.impE (.conjR (OriginalLookupRuleMatrix.head_matrix_iff hZ1 w.castSucc n.castSucc i.castSucc r.castSucc R.castSucc (env2 y.castSucc (Fin.last m)) hw1 he (.conjR hT) hi1)) hr1
  have ha := HornApplicationRules.lookup_head_intro hZ1 w.castSucc r.castSucc R.castSucc (env2 y.castSucc (Fin.last m)) hw1 he hm
  have ho := OriginalLookupDispatch.lookup_intro _ _ _ (.disjL ha)
  exact of_eq (HornStepSyntax.originalStep_rename w r R Fin.castSucc).symm ho

end PPAC.Migration.Internal.HornLookupHeadPositive
