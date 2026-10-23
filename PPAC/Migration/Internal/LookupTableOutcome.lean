import PPAC.Migration.Internal.LookupTableOutcomeSyntax

/-! 成功图、无输出、穷尽性及单值性均由原 ZF 对象推导取得。 -/
namespace PPAC.Migration.Internal.LookupTableOutcome
open Source SourceAlgebra SourceLogic OmegaSyntax LookupTableOutcomeSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem has_output_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hi : Derives Γ (.mem i w)) :
    Derives Γ ((hasOutput w n i).iff (StrictLookupSyntax.hasOutput w n i)) := by
  apply FormulaCodeCongruence.ex_congr
  exact LookupTableCorrectnessInduction.execution_iff_at_natural (ZFContext.rename hZ Fin.castSucc)
    w.castSucc n.castSucc i.castSucc (Fin.last m) (of_eq (omega_rename w Fin.castSucc) (Derives.rename Fin.castSucc hw))
    (Derives.rename Fin.castSucc hn) (Derives.rename Fin.castSucc hi)

theorem no_output_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w)) (hi : Derives Γ (.mem i w)) :
    Derives Γ ((noOutput w n i).iff (StrictLookupSyntax.rejected w n i)) :=
  FormulaTransformCongruence.imp_congr (has_output_iff hZ w n i hw hn hi) (SyntaxTypeLocalTransfer.iff_refl .bot)

theorem exhaustive {m} {Γ : Context m} (w n i : Fin m) :
    Derives Γ ((hasOutput w n i).disj (noOutput w n i)) := by
  apply SourcePropositional.by_cases (hasOutput w n i)
  · exact .disjL (.hyp (Or.inl rfl))
  · exact .disjR (.hyp (Or.inl rfl))

theorem incompatible {m} {Γ : Context m} (w n i : Fin m) :
    Derives Γ (((hasOutput w n i).conj (noOutput w n i)).neg) := by
  apply Derives.impI
  exact .impE (.conjR (.hyp (Or.inl rfl))) (.conjL (.hyp (Or.inl rfl)))

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y z : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (LookupTableExecutionSyntax.executed w n i y))
    (hz : Derives Γ (LookupTableExecutionSyntax.executed w n i z)) : Derives Γ (.equal y z) := by
  have hey := Derives.impE (.conjL (LookupTableCorrectness.execution_iff_checked hZ w n i y hw)) hy
  have hez := Derives.impE (.conjL (LookupTableCorrectness.execution_iff_checked hZ w n i z hw)) hz
  exact StrictLookupValue.unique hZ w n i y z hw (.conjR (.conjL hey)) (.conjR hey) (.conjR hez)

theorem unique_output {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n i y : Fin m)
    (hw : Derives Γ (omega w)) (hy : Derives Γ (LookupTableExecutionSyntax.executed w n i y)) :
    Derives Γ (uniqueOutput w n i y) := by
  apply Derives.allI
  apply Derives.impI
  let Z := LookupTableExecutionSyntax.executed w.castSucc n.castSucc i.castSucc (Fin.last m)
  let Δ := Context.add Z (Context.image Formula.raise Γ)
  have hw1 : Derives Δ (omega w.castSucc) := of_eq (omega_rename w Fin.castSucc) (under hw Z)
  have hy1 : Derives Δ (LookupTableExecutionSyntax.executed w.castSucc n.castSucc i.castSucc y.castSucc) := of_eq (LookupTableExecutionSyntax.executed_rename w n i y Fin.castSucc) (under hy Z)
  exact unique (ZFContext.under hZ Z) w.castSucc n.castSucc i.castSucc (Fin.last m) y.castSucc hw1 (.hyp (Or.inl rfl)) hy1

end PPAC.Migration.Internal.LookupTableOutcome
