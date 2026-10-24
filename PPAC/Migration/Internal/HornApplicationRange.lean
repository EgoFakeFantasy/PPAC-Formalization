import PPAC.Migration.Internal.PacketAffineApplication

/-! Every original bounded rule application yields an internal natural row, for any fixed rule. -/
namespace PPAC.Migration.Internal.HornApplicationRange
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Rule)

theorem range {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule) (w r V : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (HornApplicationSyntax.application rule w r V)) : Derives Γ (.mem r w) := by
  let C := HornApplicationSyntax.body rule w r V
  let Δ := Context.add C (raisedContext rule.arity Γ)
  apply HornApplicationRules.eliminate_application rule w r V _ ha
  have hwN := of_eq (omega_rename w (old rule.arity)) (HornBinderRules.under_body rule.arity hw C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  exact HornExprRange.range (HornBinderRules.zf_body rule.arity hZ C) rule.head (old rule.arity w)
    (old rule.arity r) (slot rule.arity) hwN (.conjL hC) (.conjL (.conjR (.conjR hC)))

theorem reject {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule) (w r V : Fin m)
    (hw : Derives Γ (omega w)) (hr : Derives Γ ((Formula.mem r w).neg)) :
    Derives Γ ((HornApplicationSyntax.application rule w r V).neg) := by
  apply Derives.impI
  exact .impE (add hr _) (range (ZFContext.add hZ _) rule w r V (add hw _) (.hyp (Or.inl rfl)))

end PPAC.Migration.Internal.HornApplicationRange
