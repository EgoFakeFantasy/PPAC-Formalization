import PPAC.Migration.Internal.SyntaxMixedFormulaEvaluationExistence

/-! 实际后继域与完整图任意改变时，原混合替换状态求值仍相同；全部候选输出在对象层比较。 -/
namespace PPAC.Migration.Internal.SyntaxMixedFormulaEvaluationUnique
open SyntaxRenameQuerySyntax (of_eq)
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax OrdinalSyntax SyntaxMixedFormulaEvaluationSyntax
open SyntaxMixedFormulaRecursionSyntax
open SyntaxMixedFormulaRecursionSyntax (one one_map)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem graphs_agree {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f g d t : Fin m)
    (hd : Derives Γ (ordinal d)) (ht : Derives Γ (ordinal t)) (hf : Derives Γ (graph w f d))
    (hg : Derives Γ (graph w g t)) : Derives Γ (GraphFamilySyntax.agrees f g) :=
  OrdinalRecursionCompatibility.compatible matrix (one w) f g d t
    (ZFContext.arithmetic hZ).base.extensionality (ZFContext.arithmetic hZ).base.foundation
    (ZFContext.separation hZ IterationSyntax.agreementMatrix.neg) (SyntaxMixedFormulaRecursionStep.deterministic hZ (one w)) hd ht hf hg

theorem data_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n y u s f t g : Fin m)
    (hn : Derives Γ (ordinal n)) (hy : Derives Γ (data w s f n y)) (hu : Derives Γ (data w t g n u)) : Derives Γ (.equal y u) := by
  have hs := OrdinalSuccessor.ordinal s n (ZFContext.arithmetic hZ).base.foundation (.conjL hy) hn
  have ht := OrdinalSuccessor.ordinal t n (ZFContext.arithmetic hZ).base.foundation (.conjL hu) hn
  have hc := graphs_agree hZ w f g s t hs ht (.conjL (.conjR hy)) (.conjL (.conjR hu))
  exact .impE (.impE (GraphFamilySyntax.agrees_at f g n y u hc) (.conjR (.conjR hy))) (.conjR (.conjR hu))

theorem against_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n y u s f : Fin m)
    (hn : Derives Γ (ordinal n)) (hy : Derives Γ (data w s f n y)) (hu : Derives Γ (evaluation w n u)) : Derives Γ (.equal y u) := by
  let D := witnesses w n u
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_value w n u _ hu
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ D
  have hn2 : Derives Δ (ordinal n.castSucc.castSucc) := by exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, ordinal_rename]) (OrderedPairElimination.under_two hn D)
  have hy2 : Derives Δ (data w.castSucc.castSucc s.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc y.castSucc.castSucc) := by
    exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, data_rename]) (OrderedPairElimination.under_two hy D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  exact data_unique hZ2 _ _ _ _ _ _ _ _ hn2 hy2 hD

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n y u : Fin m)
    (hn : Derives Γ (ordinal n)) (hy : Derives Γ (evaluation w n y)) (hu : Derives Γ (evaluation w n u)) : Derives Γ (.equal y u) := by
  let D := witnesses w n y
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_value w n y _ hy
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ D
  have hn2 : Derives Δ (ordinal n.castSucc.castSucc) := by exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, ordinal_rename]) (OrderedPairElimination.under_two hn D)
  have hu2 : Derives Δ (evaluation w.castSucc.castSucc n.castSucc.castSucc u.castSucc.castSucc) := by
    exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, evaluation_rename]) (OrderedPairElimination.under_two hu D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  exact against_value hZ2 _ _ _ _ _ _ hn2 hD hu2

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n : Fin m)
    (hn : Derives Γ (ordinal n)) : Derives Γ (fiber w n) := by
  have hx := SyntaxMixedFormulaEvaluationExistence.exists_value hZ w n hn
  let Y := evaluation w.castSucc n.castSucc (Fin.last m)
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hx
  apply Derives.exE (p := Y) hx
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ Y
  have hn1 : Derives Ξ (ordinal n.castSucc) := by exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, ordinal_rename]) (under hn Y)
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hu : Derives Ξ (uniqueValue w.castSucc n.castSucc (Fin.last m)) := by
    apply Derives.allI
    apply Derives.impI
    let U := evaluation w.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add U (Context.image Formula.raise Ξ)
    have hn2 : Derives Δ (ordinal n.castSucc.castSucc) := by exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, ordinal_rename]) (under hn1 U)
    have hOld : Derives Δ (evaluation w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) := by
      exact SyntaxRenameQuerySyntax.of_eq (by simp only [Y, Formula.raise, evaluation_rename]) (under hY U)
    exact unique (ZFContext.under hZ1 U) _ _ _ _ hn2 (.hyp (Or.inl rfl)) hOld
  have hout : Derives Ξ (fiber w.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, evaluation_rename, uniqueValue_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hY hu
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, fiber_rename]) (hout)
end PPAC.Migration.Internal.SyntaxMixedFormulaEvaluationUnique
