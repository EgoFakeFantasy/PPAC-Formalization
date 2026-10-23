import PPAC.Migration.Internal.HornTraceExtension
import PPAC.Migration.Internal.PureSyntaxTraceRules

/-! 原Pairing/Union为纯十五规则闭轨迹实际插入根行。 -/
namespace PPAC.Migration.Internal.PureSyntaxTraceExtension
open Source SourceAlgebra SourceLogic PureSyntaxTrace
open SyntaxRenameQuerySyntax (of_eq)

theorem closed {m} {Γ : Context m} (w R r S : Fin m)
    (hc : Derives Γ (PureSyntaxTrace.closed w R)) (hr : Derives Γ (HornStepSyntax.step PureSyntaxRules.rules w r R))
    (hi : Derives Γ (InsertSyntax.insert S R r)) : Derives Γ (PureSyntaxTrace.closed w S) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) S.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hi1 : Derives Δ (InsertSyntax.insert S.castSucc R.castSucc r.castSucc) := of_eq (InsertSyntax.insert_rename S R r Fin.castSucc) (under hi M)
  have hc1 : Derives Δ (PureSyntaxTrace.closed w.castSucc R.castSucc) := of_eq (closed_rename w R Fin.castSucc) (under hc M)
  have hr1 : Derives Δ (HornStepSyntax.step PureSyntaxRules.rules w.castSucc r.castSucc R.castSucc) := of_eq (HornStepSyntax.step_rename PureSyntaxRules.rules w r R Fin.castSucc) (under hr M)
  have hs1 := HornTraceExtension.includes _ _ _ hi1
  apply Derives.disjE (InsertLogic.member_cases _ _ _ _ hi1 (.hyp (Or.inl rfl)))
  · exact HornTraceMonotone.step PureSyntaxRules.rules _ _ _ _ (add hs1 _) (closed_at _ _ _ (add hc1 _) (.hyp (Or.inl rfl)))
  · exact PureSyntaxTraceRules.step_subst_row _ _ _ _ (eq_symm (.hyp (Or.inl rfl)))
      (HornTraceMonotone.step PureSyntaxRules.rules _ _ _ _ (add hs1 _) (add hr1 _))

theorem witness {m} {Γ : Context m} (w R r S : Fin m)
    (hs : Derives Γ (RestrictionSyntax.subset R w)) (hn : Derives Γ (.mem r w))
    (hc : Derives Γ (PureSyntaxTrace.closed w R)) (hr : Derives Γ (HornStepSyntax.step PureSyntaxRules.rules w r R))
    (hi : Derives Γ (InsertSyntax.insert S R r)) : Derives Γ (PureSyntaxTrace.witness w r S) :=
  .conjI (HornTraceExtension.subset w R r S hs hn hi) (.conjI (InsertLogic.new_member _ _ _ hi) (closed w R r S hc hr hi))

theorem condition {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w R r : Fin m)
    (hs : Derives Γ (RestrictionSyntax.subset R w)) (hn : Derives Γ (.mem r w))
    (hc : Derives Γ (PureSyntaxTrace.closed w R)) (hr : Derives Γ (HornStepSyntax.step PureSyntaxRules.rules w r R)) :
    Derives Γ (PureSyntaxTrace.condition w r) := by
  have he := InsertExistence.exists_insert R r (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union
  let B := InsertSyntax.insert (Fin.last m) R.castSucc r.castSucc
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hs1 : Derives Δ (RestrictionSyntax.subset R.castSucc w.castSucc) := of_eq (RestrictionSyntax.subset_rename R w Fin.castSucc) (under hs B)
  have hn1 : Derives Δ (.mem r.castSucc w.castSucc) := under hn B
  have hc1 : Derives Δ (PureSyntaxTrace.closed w.castSucc R.castSucc) := of_eq (closed_rename w R Fin.castSucc) (under hc B)
  have hr1 : Derives Δ (HornStepSyntax.step PureSyntaxRules.rules w.castSucc r.castSucc R.castSucc) := of_eq (HornStepSyntax.step_rename PureSyntaxRules.rules w r R Fin.castSucc) (under hr B)
  exact of_eq (condition_rename w r Fin.castSucc).symm
    (intro_condition _ _ _ (witness _ _ _ _ hs1 hn1 hc1 hr1 (.hyp (Or.inl rfl))))

end PPAC.Migration.Internal.PureSyntaxTraceExtension
