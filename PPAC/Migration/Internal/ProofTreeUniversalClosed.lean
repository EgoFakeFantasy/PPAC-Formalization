import PPAC.Migration.Internal.ProofTreeUniversalValue

/-! 全部原轨迹根的实际集合仍对原12分支表闭合，并给出无外部有限性前提的原一步展开。 -/
namespace PPAC.Migration.Internal.ProofTreeUniversalClosed
open Source SourceAlgebra SourceLogic ProofTreeUniversalSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem condition_step {m} {Γ : Context m} (test : Formula 1) (w V r : Fin m) (hv : Derives Γ (value test w V))
    (ht : Derives Γ (ProofTreeTraceSyntax.condition test w r)) : Derives Γ (ProofTreeTraceSyntax.step test w r V) := by
  let B := ProofTreeTraceSyntax.witness test w.castSucc r.castSucc (Fin.last m)
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) ht
  have hv1 : Derives Δ (value test w.castSucc V.castSucc) := of_eq (value_rename test w V Fin.castSucc) (under hv B)
  have hB : Derives Δ B := .hyp (Or.inl rfl)
  have hi := ProofTreeUniversalValue.subtrace_included test _ _ _ hv1 (.conjL hB) (.conjR (.conjR hB))
  have hs := ProofTreeTraceSyntax.closed_at test _ _ _ (.conjR (.conjR hB)) (.conjL (.conjR hB))
  exact of_eq (ProofTreeTraceSyntax.step_rename test w r V Fin.castSucc).symm (ProofTreeTraceMonotone.step test _ _ _ _ hi hs)

theorem closed {m} {Γ : Context m} (test : Formula 1) (w V : Fin m) (hv : Derives Γ (value test w V)) : Derives Γ (ProofTreeTraceSyntax.closed test w V) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) V.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hv1 : Derives Δ (value test w.castSucc V.castSucc) := of_eq (value_rename test w V Fin.castSucc) (under hv M)
  exact condition_step test _ _ _ hv1 (.impE (.conjL (ProofTreeUniversalValue.member_iff test _ _ _ hv1)) (.hyp (Or.inl rfl)))

theorem step_condition {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w V r : Fin m)
    (hv : Derives Γ (value test w V)) (hn : Derives Γ (.mem r w))
    (hs : Derives Γ (ProofTreeTraceSyntax.step test w r V)) : Derives Γ (ProofTreeTraceSyntax.condition test w r) :=
  ProofTreeTraceExtension.condition test hZ w V r (ProofTreeUniversalValue.subset test w V hv) hn (closed test w V hv) hs

theorem unfold_iff {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w V r : Fin m)
    (hv : Derives Γ (value test w V)) (hn : Derives Γ (.mem r w)) :
    Derives Γ ((ProofTreeTraceSyntax.condition test w r).iff (ProofTreeTraceSyntax.step test w r V)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact condition_step test w V r (add hv _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact step_condition test (ZFContext.add hZ _) w V r (add hv _) (add hn _) (.hyp (Or.inl rfl))

end PPAC.Migration.Internal.ProofTreeUniversalClosed
