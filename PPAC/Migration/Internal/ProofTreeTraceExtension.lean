import PPAC.Migration.Internal.ProofTreeTraceMonotone

/-! Pairing/Union实际插入根行；原12规则及每个节点的局部检查均在闭轨迹中保留。 -/
namespace PPAC.Migration.Internal.ProofTreeTraceExtension
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

theorem closed {m} {Γ : Context m} (test : Formula 1) (w R r S : Fin m)
    (hc : Derives Γ (ProofTreeTraceSyntax.closed test w R)) (hr : Derives Γ (ProofTreeTraceSyntax.step test w r R))
    (hi : Derives Γ (InsertSyntax.insert S R r)) : Derives Γ (ProofTreeTraceSyntax.closed test w S) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) S.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hi1 : Derives Δ (InsertSyntax.insert S.castSucc R.castSucc r.castSucc) := of_eq (InsertSyntax.insert_rename S R r Fin.castSucc) (under hi M)
  have hc1 : Derives Δ (ProofTreeTraceSyntax.closed test w.castSucc R.castSucc) := of_eq (ProofTreeTraceSyntax.closed_rename test w R Fin.castSucc) (under hc M)
  have hr1 : Derives Δ (ProofTreeTraceSyntax.step test w.castSucc r.castSucc R.castSucc) := of_eq (ProofTreeTraceSyntax.step_rename test w r R Fin.castSucc) (under hr M)
  have hs1 := HornTraceExtension.includes _ _ _ hi1
  apply Derives.disjE (InsertLogic.member_cases _ _ _ _ hi1 (.hyp (Or.inl rfl)))
  · exact ProofTreeTraceMonotone.step test _ _ _ _ (add hs1 _) (ProofTreeTraceSyntax.closed_at test _ _ _ (add hc1 _) (.hyp (Or.inl rfl)))
  · exact ProofTreeTraceMonotone.row_subst test _ _ _ _ (eq_symm (.hyp (Or.inl rfl)))
      (ProofTreeTraceMonotone.step test _ _ _ _ (add hs1 _) (add hr1 _))

theorem witness {m} {Γ : Context m} (test : Formula 1) (w R r S : Fin m)
    (hs : Derives Γ (RestrictionSyntax.subset R w)) (hn : Derives Γ (.mem r w))
    (hc : Derives Γ (ProofTreeTraceSyntax.closed test w R)) (hr : Derives Γ (ProofTreeTraceSyntax.step test w r R))
    (hi : Derives Γ (InsertSyntax.insert S R r)) : Derives Γ (ProofTreeTraceSyntax.witness test w r S) :=
  .conjI (HornTraceExtension.subset w R r S hs hn hi) (.conjI (InsertLogic.new_member _ _ _ hi) (closed test w R r S hc hr hi))

theorem condition {m} {Γ : Context m} (test : Formula 1) (hZ : ZFContext.Evidence Γ) (w R r : Fin m)
    (hs : Derives Γ (RestrictionSyntax.subset R w)) (hn : Derives Γ (.mem r w))
    (hc : Derives Γ (ProofTreeTraceSyntax.closed test w R)) (hr : Derives Γ (ProofTreeTraceSyntax.step test w r R)) :
    Derives Γ (ProofTreeTraceSyntax.condition test w r) := by
  have he := InsertExistence.exists_insert R r (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union
  let B := InsertSyntax.insert (Fin.last m) R.castSucc r.castSucc
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hs1 : Derives Δ (RestrictionSyntax.subset R.castSucc w.castSucc) := of_eq (RestrictionSyntax.subset_rename R w Fin.castSucc) (under hs B)
  have hn1 : Derives Δ (.mem r.castSucc w.castSucc) := under hn B
  have hc1 : Derives Δ (ProofTreeTraceSyntax.closed test w.castSucc R.castSucc) := of_eq (ProofTreeTraceSyntax.closed_rename test w R Fin.castSucc) (under hc B)
  have hr1 : Derives Δ (ProofTreeTraceSyntax.step test w.castSucc r.castSucc R.castSucc) := of_eq (ProofTreeTraceSyntax.step_rename test w r R Fin.castSucc) (under hr B)
  exact of_eq (ProofTreeTraceSyntax.condition_rename test w r Fin.castSucc).symm
    (ProofTreeTraceSyntax.intro_condition test _ _ _ (witness test _ _ _ _ hs1 hn1 hc1 hr1 (.hyp (Or.inl rfl))))

end PPAC.Migration.Internal.ProofTreeTraceExtension
