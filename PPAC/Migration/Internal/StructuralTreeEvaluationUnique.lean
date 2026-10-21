import PPAC.Migration.Internal.StructuralTreeEvaluationExistence

/-! 实际后继域与完整图任意改变时，原树求值仍相同；全部候选输出在对象层比较。 -/
namespace PPAC.Migration.Internal.StructuralTreeEvaluationUnique
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax OrdinalSyntax StructuralTreeEvaluationSyntax
open StructuralTreeOperatorSyntax (matrix params3_map)
open NaturalAdditionTransport (params3)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem graphs_agree {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e f g d t : Fin m)
    (hd : Derives Γ (ordinal d)) (ht : Derives Γ (ordinal t)) (hf : Derives Γ (graph w z e f d))
    (hg : Derives Γ (graph w z e g t)) : Derives Γ (GraphFamilySyntax.agrees f g) :=
  OrdinalRecursionCompatibility.compatible matrix (params3 w z e) f g d t
    (ZFContext.arithmetic hZ).base.extensionality (ZFContext.arithmetic hZ).base.foundation
    (ZFContext.separation hZ IterationSyntax.agreementMatrix.neg) (StructuralTreeOperatorStep.deterministic (params3 w z e)) hd ht hf hg

theorem data_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n y u s f t g : Fin m)
    (hn : Derives Γ (ordinal n)) (hy : Derives Γ (data w z e s f n y)) (hu : Derives Γ (data w z e t g n u)) : Derives Γ (.equal y u) := by
  have hs := OrdinalSuccessor.ordinal s n (ZFContext.arithmetic hZ).base.foundation (.conjL hy) hn
  have ht := OrdinalSuccessor.ordinal t n (ZFContext.arithmetic hZ).base.foundation (.conjL hu) hn
  have hc := graphs_agree hZ w z e f g s t hs ht (.conjL (.conjR hy)) (.conjL (.conjR hu))
  exact .impE (.impE (GraphFamilySyntax.agrees_at f g n y u hc) (.conjR (.conjR hy))) (.conjR (.conjR hu))

theorem against_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n y u s f : Fin m)
    (hn : Derives Γ (ordinal n)) (hy : Derives Γ (data w z e s f n y)) (hu : Derives Γ (evaluation w z e n u)) : Derives Γ (.equal y u) := by
  let D := witnesses w z e n u
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_value w z e n u _ hu
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ D
  have hn2 : Derives Δ (ordinal n.castSucc.castSucc) := by simpa only [Formula.raise, ordinal_rename] using OrderedPairElimination.under_two hn D
  have hy2 : Derives Δ (data w.castSucc.castSucc z.castSucc.castSucc e.castSucc.castSucc s.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc y.castSucc.castSucc) := by
    simpa only [Formula.raise, data_rename] using OrderedPairElimination.under_two hy D
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  exact data_unique hZ2 _ _ _ _ _ _ _ _ _ _ hn2 hy2 hD

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n y u : Fin m)
    (hn : Derives Γ (ordinal n)) (hy : Derives Γ (evaluation w z e n y)) (hu : Derives Γ (evaluation w z e n u)) : Derives Γ (.equal y u) := by
  let D := witnesses w z e n y
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_value w z e n y _ hy
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ D
  have hn2 : Derives Δ (ordinal n.castSucc.castSucc) := by simpa only [Formula.raise, ordinal_rename] using OrderedPairElimination.under_two hn D
  have hu2 : Derives Δ (evaluation w.castSucc.castSucc z.castSucc.castSucc e.castSucc.castSucc n.castSucc.castSucc u.castSucc.castSucc) := by
    simpa only [Formula.raise, evaluation_rename] using OrderedPairElimination.under_two hu D
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  exact against_value hZ2 _ _ _ _ _ _ _ _ hn2 hD hu2

theorem exists_unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w z e n : Fin m)
    (hn : Derives Γ (ordinal n)) : Derives Γ (fiber w z e n) := by
  have hx := StructuralTreeEvaluationExistence.exists_value hZ w z e n hn
  let Y := evaluation w.castSucc z.castSucc e.castSucc n.castSucc (Fin.last m)
  let Ξ := Context.add Y (Context.image Formula.raise Γ)
  change Derives Γ (.ex Y) at hx
  apply Derives.exE (p := Y) hx
  have hZ1 : ZFContext.Evidence Ξ := ZFContext.under hZ Y
  have hn1 : Derives Ξ (ordinal n.castSucc) := by simpa only [Formula.raise, ordinal_rename] using under hn Y
  have hY : Derives Ξ Y := .hyp (Or.inl rfl)
  have hu : Derives Ξ (uniqueValue w.castSucc z.castSucc e.castSucc n.castSucc (Fin.last m)) := by
    apply Derives.allI
    apply Derives.impI
    let U := evaluation w.castSucc.castSucc z.castSucc.castSucc e.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))
    let Δ := Context.add U (Context.image Formula.raise Ξ)
    have hn2 : Derives Δ (ordinal n.castSucc.castSucc) := by simpa only [Formula.raise, ordinal_rename] using under hn1 U
    have hOld : Derives Δ (evaluation w.castSucc.castSucc z.castSucc.castSucc e.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc) := by
      simpa only [Y, Formula.raise, evaluation_rename] using under hY U
    exact unique (ZFContext.under hZ1 U) _ _ _ _ _ _ hn2 (.hyp (Or.inl rfl)) hOld
  have hout : Derives Ξ (fiber w.castSucc z.castSucc e.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    simp only [Formula.instantiate, Formula.rename, evaluation_rename, uniqueValue_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
    exact .conjI hY hu
  simpa only [Formula.raise, fiber_rename] using hout
end PPAC.Migration.Internal.StructuralTreeEvaluationUnique
