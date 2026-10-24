import PPAC.Migration.Internal.ProjectCompilerStateSyntax

/-! Actual compiler set recursion or guarded output relation; output correctness and functionality remain unproved. -/
namespace PPAC.Migration.Internal.ProjectCompilerStateRows
open Source SourceAlgebra SourceLogic PairSyntax ProjectCompilerLocalSyntax ProjectCompilerStateSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_pair {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n h p b f : Fin m)
    (hp : Derives Γ (ordered p b f)) (hr : Derives Γ (row w n h p)) : Derives Γ (localStep w b f h n) := by
  let B := rowBody w n h p
  let Δ := Context.add B (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_row w n h p _ hr
  have hp2 : Derives Δ (ordered p.castSucc.castSucc b.castSucc.castSucc f.castSucc.castSucc) := by
    simpa only [Formula.raise, ordered_rename] using OrderedPairElimination.under_two hp B
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have he := OrderedPairLogic.injective _ _ _ _ _ _ (ZFContext.arithmetic (ZFContext.under_two hZ B)).base.extensionality
    (.conjL hB) hp2 (.eqRefl p.castSucc.castSucc)
  have hb := subst_bound _ _ _ _ _ _ (.conjL he) (.conjR hB)
  have hout := subst_output _ _ _ _ _ _ (.conjR he) hb
  simpa only [Formula.raise, localStep_rename] using hout

theorem pair_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n h p b f : Fin m)
    (hp : Derives Γ (ordered p b f)) : Derives Γ ((row w n h p).iff (localStep w b f h n)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact at_pair (ZFContext.add hZ _) w n h p b f (add hp _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact intro_row w n h p b f (add hp _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.ProjectCompilerStateRows
