import PPAC.Migration.Internal.HornClosedTraceSyntax

/-! Original Pairing/Union insertion preserves closure for the explicitly supplied finite rule table. -/
namespace PPAC.Migration.Internal.HornClosedTraceExtension
open Source SourceAlgebra SourceLogic HornClosedTraceSyntax
open HornTraceExtension (includes subset)
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Rule)

theorem closed {m} {Γ : Context m} (rules : List Rule) (w R r S : Fin m)
    (hc : Derives Γ (HornClosedTraceSyntax.closed rules w R)) (hr : Derives Γ (HornStepSyntax.step rules w r R))
    (hi : Derives Γ (InsertSyntax.insert S R r)) : Derives Γ (HornClosedTraceSyntax.closed rules w S) := by
  apply Derives.allI
  apply Derives.impI
  let M := Formula.mem (Fin.last m) S.castSucc
  let Δ := Context.add M (Context.image Formula.raise Γ)
  have hi1 : Derives Δ (InsertSyntax.insert S.castSucc R.castSucc r.castSucc) := of_eq (InsertSyntax.insert_rename S R r Fin.castSucc) (under hi M)
  have hc1 : Derives Δ (HornClosedTraceSyntax.closed rules w.castSucc R.castSucc) := of_eq (closed_rename rules w R Fin.castSucc) (under hc M)
  have hr1 : Derives Δ (HornStepSyntax.step rules w.castSucc r.castSucc R.castSucc) := of_eq (HornStepSyntax.step_rename rules w r R Fin.castSucc) (under hr M)
  have hs1 := includes _ _ _ hi1
  apply Derives.disjE (InsertLogic.member_cases _ _ _ _ hi1 (.hyp (Or.inl rfl)))
  · exact HornTraceMonotone.step rules _ _ _ _ (add hs1 _) (closed_at rules _ _ _ (add hc1 _) (.hyp (Or.inl rfl)))
  · exact HornClosedTraceSyntax.step_row_subst rules _ _ _ _ (eq_symm (.hyp (Or.inl rfl)))
      (HornTraceMonotone.step rules _ _ _ _ (add hs1 _) (add hr1 _))

theorem witness {m} {Γ : Context m} (rules : List Rule) (w R r S : Fin m)
    (hs : Derives Γ (RestrictionSyntax.subset R w)) (hn : Derives Γ (.mem r w))
    (hc : Derives Γ (HornClosedTraceSyntax.closed rules w R)) (hr : Derives Γ (HornStepSyntax.step rules w r R))
    (hi : Derives Γ (InsertSyntax.insert S R r)) : Derives Γ (HornClosedTraceSyntax.witness rules w r S) :=
  .conjI (subset w R r S hs hn hi) (.conjI (InsertLogic.new_member _ _ _ hi) (closed rules w R r S hc hr hi))

theorem condition {m} {Γ : Context m} (rules : List Rule) (hZ : ZFContext.Evidence Γ) (w R r : Fin m)
    (hs : Derives Γ (RestrictionSyntax.subset R w)) (hn : Derives Γ (.mem r w))
    (hc : Derives Γ (HornClosedTraceSyntax.closed rules w R)) (hr : Derives Γ (HornStepSyntax.step rules w r R)) :
    Derives Γ (HornClosedTraceSyntax.condition rules w r) := by
  have he := InsertExistence.exists_insert R r (ZFContext.arithmetic hZ).base.pairing (ZFContext.arithmetic hZ).base.union
  let B := InsertSyntax.insert (Fin.last m) R.castSucc r.castSucc
  let Δ := Context.add B (Context.image Formula.raise Γ)
  apply Derives.exE (p := B) he
  have hs1 : Derives Δ (RestrictionSyntax.subset R.castSucc w.castSucc) := of_eq (RestrictionSyntax.subset_rename R w Fin.castSucc) (under hs B)
  have hn1 : Derives Δ (.mem r.castSucc w.castSucc) := under hn B
  have hc1 : Derives Δ (HornClosedTraceSyntax.closed rules w.castSucc R.castSucc) := of_eq (closed_rename rules w R Fin.castSucc) (under hc B)
  have hr1 : Derives Δ (HornStepSyntax.step rules w.castSucc r.castSucc R.castSucc) := of_eq (HornStepSyntax.step_rename rules w r R Fin.castSucc) (under hr B)
  exact of_eq (condition_rename rules w r Fin.castSucc).symm
    (intro_condition rules _ _ _ (witness rules _ _ _ _ hs1 hn1 hc1 hr1 (.hyp (Or.inl rfl))))

end PPAC.Migration.Internal.HornClosedTraceExtension
