import PPAC.Migration.Internal.ProjectSourceTypeJudgmentSyntax

/-! 原实际状态值的逐上下文成员恰好等于类型判断，不依赖所选后继域或递归图。 -/
namespace PPAC.Migration.Internal.ProjectSourceTypeJudgment
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax OrdinalSyntax SyntaxTermSyntax ProjectSourceTypeRecursionSyntax ProjectSourceTypeEvaluationSyntax ProjectSourceTypeStateSyntax ProjectSourceTypeJudgmentSyntax
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem context_of_value_edge {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c n v b f : Fin m)
    (hn : Derives Γ (ordinal n)) (hv : Derives Γ (evaluation w c n v)) (he : Derives Γ (edge v b f)) :
    Derives Γ (contexts w b f) := by
  have hh := ProjectSourceTypeHistory.from_value hZ w c n v hn hv
  let H := (graph w.castSucc c.castSucc (Fin.last m) n.castSucc).conj
    (state w.castSucc c.castSucc n.castSucc (Fin.last m) v.castSucc)
  let Δ := Context.add H (Context.image Formula.raise Γ)
  apply Derives.exE (p := H) hh
  have he1 : Derives Δ (edge v.castSucc b.castSucc f.castSucc) := by simpa only [Formula.raise, edge_rename] using under he H
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hl := ProjectSourceTypeStateMembership.local_of_edge (ZFContext.under hZ H) _ _ _ _ _ _ _ (.conjR hH) he1
  have hout := ProjectSourceLocal.context _ _ _ _ _ hl
  simpa only [Formula.raise, contexts_rename] using hout

theorem at_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c n b f v : Fin m)
    (hn : Derives Γ (ordinal n)) (hw : Derives Γ (.mem n w)) (hv : Derives Γ (evaluation w c n v)) :
    Derives Γ ((typed w c n b f).iff (edge v b f)) := by
  apply Derives.conjI
  · apply Derives.impI
    let T := typed w c n b f
    let Ξ := Context.add T Γ
    let V := (evaluation w.castSucc c.castSucc n.castSucc (Fin.last m)).conj (edge (Fin.last m) b.castSucc f.castSucc)
    let Δ := Context.add V (Context.image Formula.raise Ξ)
    apply eliminate_typed w c n b f _ (.hyp (Or.inl rfl))
    have hn1 : Derives Δ (ordinal n.castSucc) := by simpa only [Formula.raise, ordinal_rename] using under (add hn T) V
    have hv1 : Derives Δ (evaluation w.castSucc c.castSucc n.castSucc v.castSucc) := by
      simpa only [Formula.raise, evaluation_rename] using under (add hv T) V
    have hV : Derives Δ V := .hyp (Or.inl rfl)
    have heq := ProjectSourceTypeEvaluationUnique.unique (ZFContext.under (ZFContext.add hZ T) V) _ _ _ _ _ hn1 (.conjL hV) hv1
    have hout := IterationValueUniqueness.edge_subst_graph _ _ _ _ heq (.conjR hV)
    simpa only [Formula.raise, edge_rename] using hout
  · apply Derives.impI
    have hc := context_of_value_edge (ZFContext.add hZ (edge v b f)) w c n v b f (add hn _) (add hv _) (.hyp (Or.inl rfl))
    exact intro_typed w c n b f v (add hw _) hc (add hv _) (.hyp (Or.inl rfl))

theorem read_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w c h d x b f : Fin m)
    (hd : Derives Γ (ordinal d)) (hx : Derives Γ (.mem x d)) (hw : Derives Γ (.mem x w))
    (hg : Derives Γ (graph w c h d)) :
    Derives Γ ((SyntaxContextReadSyntax.read h x b f).iff (typed w c x b f)) := by
  apply Derives.conjI
  · apply Derives.impI
    let R := SyntaxContextReadSyntax.read h x b f
    let Ξ := Context.add R Γ
    let V := (edge h.castSucc x.castSucc (Fin.last m)).conj (edge (Fin.last m) b.castSucc f.castSucc)
    let Δ := Context.add V (Context.image Formula.raise Ξ)
    apply Derives.exE (p := V) (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ R) V
    have hd1 : Derives Δ (ordinal d.castSucc) := by simpa only [Formula.raise, ordinal_rename] using under (add hd R) V
    have hg1 : Derives Δ (graph w.castSucc c.castSucc h.castSucc d.castSucc) := by
      simpa only [Formula.raise, graph_rename] using under (add hg R) V
    have hV : Derives Δ V := .hyp (Or.inl rfl)
    have hEval := ProjectSourceTypeGraphValues.value_of_edge hZ1 _ _ _ _ _ _ hd1 (under (add hx R) V) hg1 (.conjL hV)
    have ho := OrdinalRestriction.member d.castSucc x.castSucc hd1 (under (add hx R) V)
    have hc := context_of_value_edge hZ1 _ _ _ _ _ _ ho hEval (.conjR hV)
    have hout := intro_typed _ _ _ _ _ (Fin.last m) (under (add hw R) V) hc hEval (.conjR hV)
    simpa only [Formula.raise, typed_rename] using hout
  · apply Derives.impI
    let T := typed w c x b f
    let Ξ := Context.add T Γ
    let V := (evaluation w.castSucc c.castSucc x.castSucc (Fin.last m)).conj (edge (Fin.last m) b.castSucc f.castSucc)
    let Δ := Context.add V (Context.image Formula.raise Ξ)
    apply eliminate_typed w c x b f _ (.hyp (Or.inl rfl))
    have hZ1 := ZFContext.under (ZFContext.add hZ T) V
    have hd1 : Derives Δ (ordinal d.castSucc) := by simpa only [Formula.raise, ordinal_rename] using under (add hd T) V
    have hg1 : Derives Δ (graph w.castSucc c.castSucc h.castSucc d.castSucc) := by
      simpa only [Formula.raise, graph_rename] using under (add hg T) V
    have hV : Derives Δ V := .hyp (Or.inl rfl)
    have he := ProjectSourceTypeGraphValues.edge_of_value hZ1 _ _ _ _ _ _ hd1 (under (add hx T) V) hg1 (.conjL hV)
    have hout := SyntaxContextReadSyntax.intro_read _ _ _ _ (Fin.last m) he (.conjR hV)
    simpa only [Formula.raise, SyntaxContextReadSyntax.read_rename] using hout
end PPAC.Migration.Internal.ProjectSourceTypeJudgment
