import PPAC.Migration.Internal.PacketStructureApplicationSyntax

/-! Exact bounded applications and their forward structural expansion; unbounded reverse search is a separate obligation. -/
namespace PPAC.Migration.Internal.PacketStructureApplication
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprSyntax PacketStructureApplicationSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem local_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (b : Branch) (w V r : Fin m) (env : Fin (rule b).arity → Fin m)
    (hw : Derives Γ (omega w)) (hn : Derives Γ (environmentNat (rule b).arity w env)) :
    Derives Γ ((HornRuleSyntax.matrix (rule b) w r V env).iff (localCase b w V r env)) := by
  cases b
  · exact PacketStructureLocal.tree_iff hZ w V r env hw hn
  · exact PacketStructureLocal.nil_iff hZ w V r env hw hn
  · exact PacketStructureLocal.cons_iff hZ w V r env hw hn
  · exact PacketStructureLocal.packet_iff hZ w V r env hw hn

theorem bounded_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (b : Branch) (w V r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (HornApplicationSyntax.application (rule b) w r V)) :
    Derives Γ (boundedOutcome b w V r) := by
  let L := HornApplicationSyntax.body (rule b) w r V
  let Δ := Context.add L (raisedContext (rule b).arity Γ)
  apply HornApplicationRules.eliminate_application (rule b) w r V _ ha
  have hwk := of_eq (omega_rename w (old (rule b).arity)) (HornBinderRules.under_body (rule b).arity hw L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hl := Derives.impE (.conjL (local_iff (HornBinderRules.zf_body (rule b).arity hZ L) b
    (old (rule b).arity w) (old (rule b).arity V) (old (rule b).arity r) (slot (rule b).arity) hwk (.conjL hL))) (.conjR (.conjR hL))
  exact of_eq (boundedOutcome_rename b w V r (old (rule b).arity)).symm
    (intro_bounded b (old (rule b).arity w) (old (rule b).arity V) (old (rule b).arity r) (slot (rule b).arity)
      (.conjI (.conjL hL) (.conjI (.conjL (.conjR hL)) hl)))

theorem bounded_backward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (b : Branch) (w V r : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (boundedOutcome b w V r)) :
    Derives Γ (HornApplicationSyntax.application (rule b) w r V) := by
  let L := boundedBody b w V r
  let Δ := Context.add L (raisedContext (rule b).arity Γ)
  apply HornBinderRules.eliminate_many (rule b).arity L _ hb
  have hwk := of_eq (omega_rename w (old (rule b).arity)) (HornBinderRules.under_body (rule b).arity hw L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hm := Derives.impE (.conjR (local_iff (HornBinderRules.zf_body (rule b).arity hZ L) b
    (old (rule b).arity w) (old (rule b).arity V) (old (rule b).arity r) (slot (rule b).arity) hwk (.conjL hL))) (.conjR (.conjR hL))
  exact of_eq (HornApplicationSyntax.application_rename (rule b) w r V (old (rule b).arity)).symm
    (HornApplicationRules.intro_application (rule b) (old (rule b).arity w) (old (rule b).arity r) (old (rule b).arity V) (slot (rule b).arity)
      (.conjL hL) (.conjL (.conjR hL)) hm)

theorem bounded_iff {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (b : Branch) (w V r : Fin m)
    (hw : Derives Γ (omega w)) : Derives Γ ((HornApplicationSyntax.application (rule b) w r V).iff (boundedOutcome b w V r)) := by
  apply Derives.conjI
  · exact .impI (bounded_forward (ZFContext.add hZ _) b w V r (add hw _) (.hyp (Or.inl rfl)))
  · exact .impI (bounded_backward (ZFContext.add hZ _) b w V r (add hw _) (.hyp (Or.inl rfl)))

theorem outcome_of_bounded {m} {Γ : Context m} (b : Branch) (w V r : Fin m)
    (hb : Derives Γ (boundedOutcome b w V r)) : Derives Γ (outcome b w V r) := by
  let L := boundedBody b w V r
  let Δ := Context.add L (raisedContext (rule b).arity Γ)
  apply HornBinderRules.eliminate_many (rule b).arity L _ hb
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  exact of_eq (outcome_rename b w V r (old (rule b).arity)).symm
    (intro_outcome b (old (rule b).arity w) (old (rule b).arity V) (old (rule b).arity r) (slot (rule b).arity) (.conjR (.conjR hL)))

theorem forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (b : Branch) (w V r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (HornApplicationSyntax.application (rule b) w r V)) : Derives Γ (outcome b w V r) :=
  outcome_of_bounded b w V r (bounded_forward hZ b w V r hw ha)

end PPAC.Migration.Internal.PacketStructureApplication
