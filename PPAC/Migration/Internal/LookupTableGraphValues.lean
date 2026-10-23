import PPAC.Migration.Internal.LookupTableEvaluationUnique

/-! 任意内部原序数递归图的每条边，恰为相应索引的实际后继域查找状态求值。 -/
namespace PPAC.Migration.Internal.LookupTableGraphValues
open SyntaxRenameQuerySyntax (of_eq)
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax OrdinalSyntax LookupTableEvaluationSyntax LookupTableRecursionSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem against_data {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f d n y u s g : Fin m)
    (hd : Derives Γ (ordinal d)) (hn : Derives Γ (.mem n d)) (hf : Derives Γ (graph w f d))
    (hy : Derives Γ (edge f n y)) (hu : Derives Γ (data w s g n u)) : Derives Γ (.equal y u) := by
  have hnO := OrdinalRestriction.member d n hd hn
  have hsO := OrdinalSuccessor.ordinal s n (ZFContext.arithmetic hZ).base.foundation (.conjL hu) hnO
  have hc := LookupTableEvaluationUnique.graphs_agree hZ w f g d s hd hsO hf (.conjL (.conjR hu))
  exact .impE (.impE (GraphFamilySyntax.agrees_at f g n y u hc) hy) (.conjR (.conjR hu))

theorem against_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f d n y u : Fin m)
    (hd : Derives Γ (ordinal d)) (hn : Derives Γ (.mem n d)) (hf : Derives Γ (graph w f d))
    (hy : Derives Γ (edge f n y)) (hu : Derives Γ (evaluation w n u)) : Derives Γ (.equal y u) := by
  let D := witnesses w n u
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_value w n u _ hu
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ D
  have hd2 : Derives Δ (ordinal d.castSucc.castSucc) := by exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, ordinal_rename]) (OrderedPairElimination.under_two hd D)
  have hn2 := OrderedPairElimination.under_two hn D
  have hf2 : Derives Δ (graph w.castSucc.castSucc f.castSucc.castSucc d.castSucc.castSucc) := by
    exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, graph_rename]) (OrderedPairElimination.under_two hf D)
  have hy2 : Derives Δ (edge f.castSucc.castSucc n.castSucc.castSucc y.castSucc.castSucc) := by
    exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, edge_rename]) (OrderedPairElimination.under_two hy D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  exact against_data hZ2 _ _ _ _ _ _ _ _ hd2 hn2 hf2 hy2 hD

theorem value_of_edge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f d n y : Fin m)
    (hd : Derives Γ (ordinal d)) (hn : Derives Γ (.mem n d)) (hf : Derives Γ (graph w f d))
    (hy : Derives Γ (edge f n y)) : Derives Γ (evaluation w n y) := by
  have hv := LookupTableEvaluationExistence.exists_value hZ w n (OrdinalRestriction.member d n hd hn)
  let U := evaluation w.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add U (Context.image Formula.raise Γ)
  change Derives Γ (.ex U) at hv
  apply Derives.exE (p := U) hv
  have hZ1 : ZFContext.Evidence Δ := ZFContext.under hZ U
  have hd1 : Derives Δ (ordinal d.castSucc) := by exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, ordinal_rename]) (under hd U)
  have hf1 : Derives Δ (graph w.castSucc f.castSucc d.castSucc) := by exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, graph_rename]) (under hf U)
  have hy1 : Derives Δ (edge f.castSucc n.castSucc y.castSucc) := by exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, edge_rename]) (under hy U)
  have hU : Derives Δ U := .hyp (Or.inl rfl)
  have heq := against_value hZ1 _ _ _ _ _ _ hd1 (under hn U) hf1 hy1 hU
  have hout := output_subst _ _ _ _ (eq_symm heq) hU
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, evaluation_rename]) (hout)

theorem edge_of_data {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f d n y s g : Fin m)
    (hd : Derives Γ (ordinal d)) (hn : Derives Γ (.mem n d)) (hf : Derives Γ (graph w f d))
    (hy : Derives Γ (data w s g n y)) : Derives Γ (edge f n y) := by
  have hnO := OrdinalRestriction.member d n hd hn
  have hsO := OrdinalSuccessor.ordinal s n (ZFContext.arithmetic hZ).base.foundation (.conjL hy) hnO
  have hsub := OmegaElementary.successor_subset s n d (.conjL hy) hn (OrdinalTransitivity.subset_of_member d n (.conjL hd) hn)
  have hc := LookupTableEvaluationUnique.graphs_agree hZ w g f s d hsO hd (.conjL (.conjR hy)) hf
  exact GraphPointwise.transfer_edge g f s d n y (ZFContext.arithmetic hZ).base.extensionality
    (.conjL (.conjL (.conjR hy))) (.conjL hf) hsub hc (.conjR (.conjR hy))

theorem edge_of_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f d n y : Fin m)
    (hd : Derives Γ (ordinal d)) (hn : Derives Γ (.mem n d)) (hf : Derives Γ (graph w f d))
    (hy : Derives Γ (evaluation w n y)) : Derives Γ (edge f n y) := by
  let D := witnesses w n y
  let Δ := Context.add D (Context.image Formula.raise (Context.image Formula.raise Γ))
  apply eliminate_value w n y _ hy
  have hZ2 : ZFContext.Evidence Δ := ZFContext.under_two hZ D
  have hd2 : Derives Δ (ordinal d.castSucc.castSucc) := by exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, ordinal_rename]) (OrderedPairElimination.under_two hd D)
  have hf2 : Derives Δ (graph w.castSucc.castSucc f.castSucc.castSucc d.castSucc.castSucc) := by
    exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, graph_rename]) (OrderedPairElimination.under_two hf D)
  have hD : Derives Δ D := .hyp (Or.inl rfl)
  have hout := edge_of_data hZ2 _ _ _ _ _ _ _ hd2 (OrderedPairElimination.under_two hn D) hf2 hD
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.raise, edge_rename]) (hout)

theorem edge_iff_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w f d n y : Fin m)
    (hd : Derives Γ (ordinal d)) (hn : Derives Γ (.mem n d)) (hf : Derives Γ (graph w f d)) :
    Derives Γ ((edge f n y).iff (evaluation w n y)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact value_of_edge (ZFContext.add hZ _) _ _ _ _ _ (add hd _) (add hn _) (add hf _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact edge_of_value (ZFContext.add hZ _) _ _ _ _ _ (add hd _) (add hn _) (add hf _) (.hyp (Or.inl rfl))
end PPAC.Migration.Internal.LookupTableGraphValues
