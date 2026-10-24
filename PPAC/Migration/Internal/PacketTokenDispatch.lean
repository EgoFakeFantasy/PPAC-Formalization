import PPAC.Migration.Internal.PacketTokenDispatchData

/-! Every actual token root unfolds through precisely its two original rules. -/
namespace PPAC.Migration.Internal.PacketTokenDispatch
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprSyntax PacketTokenSyntax PacketTokenRuleData
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Rule)

theorem application_contradiction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (rule : Rule)
    (hr : rule ∈ PacketTokenDispatchData.others) (w n t a r V : Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (row w n t a r)) (ha : Derives Γ (HornApplicationSyntax.application rule w r V)) : Derives Γ .bot := by
  rcases PacketAffineDispatchData.outer_shape 2 rule.head (PacketTokenDispatchData.others_different rule hr) with ⟨tag,payload,hk,he⟩
  let L := HornApplicationSyntax.body rule w r V
  let Δ := Context.add L (raisedContext rule.arity Γ)
  apply HornApplicationRules.eliminate_application rule w r V .bot ha
  have hw1 := of_eq (omega_rename w (old rule.arity)) (HornBinderRules.under_body rule.arity hw L)
  have hc1 := of_eq (row_rename w n t a r (old rule.arity)) (HornBinderRules.under_body rule.arity hc L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hg : Derives Δ (graph rule.head (old rule.arity w) (slot rule.arity) (old rule.arity r)) := .conjL (.conjR (.conjR hL))
  rw [he] at hg
  exact HornNodeDisjoint.node_contradiction (HornBinderRules.zf_body rule.arity hZ L) tag 2 3 hk payload
    (old rule.arity w) (old rule.arity r) (slot rule.arity) (SyntaxAtomSyntax.three (old rule.arity n) (old rule.arity t) (old rule.arity a))
    hw1 (.conjL hL) hg hc1

theorem dispatch {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a r V : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (row w n t a r)) (hs : Derives Γ (PacketTraceSyntax.step w r V)) :
    Derives Γ ((HornApplicationSyntax.application smallRule w r V).disj (HornApplicationSyntax.application largeRule w r V)) := by
  apply HornStepSyntax.step_elim ObjectPacket.rules w r V _ hs
  intro rule hr
  apply Derives.impI
  rcases PacketTokenDispatchData.rule_cases rule hr with hb | hb | ho
  · subst rule
    exact .disjL (.hyp (Or.inl rfl))
  · subst rule
    exact .disjR (.hyp (Or.inl rfl))
  · exact .botE (application_contradiction (ZFContext.add hZ _) rule ho w n t a r V (add hw _) (add hc _) (.hyp (Or.inl rfl)))

theorem step_iff_applications {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w n t a r V : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (row w n t a r)) : Derives Γ ((PacketTraceSyntax.step w r V).iff
      ((HornApplicationSyntax.application smallRule w r V).disj (HornApplicationSyntax.application largeRule w r V))) := by
  apply Derives.conjI
  · exact .impI (dispatch (ZFContext.add hZ _) w n t a r V (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    apply Derives.disjE (.hyp (Or.inl rfl))
    · exact HornStepSyntax.rule_intro ObjectPacket.rules smallRule PacketTokenDispatchData.small_member w r V (.hyp (Or.inl rfl))
    · exact HornStepSyntax.rule_intro ObjectPacket.rules largeRule PacketTokenDispatchData.large_member w r V (.hyp (Or.inl rfl))

theorem step_iff_outcomes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a r V : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hv : Derives Γ (PacketTraceCore.value w V))
    (hc : Derives Γ (row w n t a r)) : Derives Γ ((PacketTraceSyntax.step w r V).iff
      ((PacketTokenApplicationSyntax.smallOutcome w B V r).disj (PacketTokenApplicationSyntax.largeOutcome w B V r))) :=
  SyntaxTypeLocalTransfer.iff_trans (step_iff_applications hZ w n t a r V hw hc)
    (SyntaxTypeLocalTransfer.disj_congr (PacketTokenApplication.small_iff hZ w B r V hw hB)
      (PacketTokenApplication.large_iff hZ w B C r V hw hB hC hv))

theorem condition_iff_outcomes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w B C n t a r V : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B))
    (hC : Derives Γ (SyntaxNumeralSyntax.numeral 256 C)) (hv : Derives Γ (PacketTraceCore.value w V))
    (hc : Derives Γ (row w n t a r)) : Derives Γ ((PacketTraceSyntax.condition w r).iff
      ((PacketTokenApplicationSyntax.smallOutcome w B V r).disj (PacketTokenApplicationSyntax.largeOutcome w B V r))) :=
  SyntaxTypeLocalTransfer.iff_trans (PacketTraceCore.unfold_iff hZ w V r hw hv) (step_iff_outcomes hZ w B C n t a r V hw hB hC hv hc)

end PPAC.Migration.Internal.PacketTokenDispatch
