import PPAC.Migration.Internal.ProjectCompilerLocalBridge

/-! Actual states and evaluations give the direct recursive equation before eliminating witnesses. -/
namespace PPAC.Migration.Internal.ProjectCompilerRecursivePoint
open Source SourceAlgebra SourceLogic OmegaSyntax
open SyntaxRenameQuerySyntax (of_eq)
attribute [local irreducible] NaturalRecursionSyntax.matrix

theorem at_state {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c n h v b q : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hc : Derives Γ (ProjectCompilerCodeSyntax.carrier w a c))
    (hg : Derives Γ (ProjectCompilerRecursionSyntax.graph w c h n))
    (hs : Derives Γ (ProjectCompilerStateSyntax.state w c n h v)) :
    Derives Γ ((GraphSyntax.edge v b q).iff (ProjectCompilerRecursiveSyntax.criterion w n b q)) :=
  ProjectSourceTypeLocalTransfer.iff_trans
    (ProjectCompilerStateMembership.edge_iff hZ w a c n h v b q (.conjL hc) (.conjR hc) hs)
    (ProjectCompilerLocalBridge.local_iff hZ w a c h n b q hw hn hc hg)

theorem at_value {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w a c n v b q : Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (.mem n w))
    (hc : Derives Γ (ProjectCompilerCodeSyntax.carrier w a c))
    (hv : Derives Γ (ProjectCompilerEvaluationSyntax.evaluation w c n v)) :
    Derives Γ ((ProjectCompilerCodeSyntax.compiled w n b q).iff (ProjectCompilerRecursiveSyntax.criterion w n b q)) := by
  have ho := NaturalOrderBasic.ordinal hZ w n hw hn
  let H := (ProjectCompilerRecursionSyntax.graph w.castSucc c.castSucc (Fin.last m) n.castSucc).conj
    (ProjectCompilerStateSyntax.state w.castSucc c.castSucc n.castSucc (Fin.last m) v.castSucc)
  let Δ := Context.add H (Context.image Formula.raise Γ)
  apply Derives.exE (p := H) (ProjectCompilerHistory.from_value hZ w c n v ho hv)
  have hH : Derives Δ H := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ H
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw H)
  have hn1 : Derives Δ (.mem n.castSucc w.castSucc) := under hn H
  have ho1 := of_eq (OrdinalSyntax.ordinal_rename n Fin.castSucc) (under ho H)
  have hc1 := of_eq (ProjectCompilerCodeSyntax.carrier_rename w a c Fin.castSucc) (under hc H)
  have hv1 := of_eq (ProjectCompilerEvaluationSyntax.evaluation_rename w c n v Fin.castSucc) (under hv H)
  have h0 := ProjectCompilerCodeCarrier.code_iff_atCarrier hZ1 w.castSucc a.castSucc c.castSucc n.castSucc b.castSucc q.castSucc hc1
  have h1 := ProjectCompilerJudgment.at_value hZ1 w.castSucc c.castSucc n.castSucc b.castSucc q.castSucc v.castSucc ho1 hn1 hv1
  have h2 := at_state hZ1 w.castSucc a.castSucc c.castSucc n.castSucc (Fin.last m) v.castSucc b.castSucc q.castSucc
    hw1 hn1 hc1 (.conjL hH) (.conjR hH)
  have hr := ProjectSourceTypeLocalTransfer.iff_trans h0 (ProjectSourceTypeLocalTransfer.iff_trans h1 h2)
  exact of_eq (by simp only [Formula.raise, Formula.iff, Formula.rename, ProjectCompilerCodeSyntax.compiled_rename,
    ProjectCompilerRecursiveSyntax.criterion_rename]) hr

end PPAC.Migration.Internal.ProjectCompilerRecursivePoint
