import PPAC.Migration.Internal.HornClosedTraceValueClosed
import PPAC.Migration.Internal.HornNodeDisjoint

/-! Every actual Packet rule is considered; object tag disjointness removes all eight foreign branches. -/
namespace PPAC.Migration.Internal.PacketAffineDispatch
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open PacketAffineRuleData (baseRule stepRule relation radix)
open YesMetaZFC.Automation
open YesMetaZFC.Automation.ObjectHorn (Rule)

theorem application_contradiction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (rule : Rule)
    (hr : rule ∈ PacketAffineDispatchData.others wide) (w d t n r R : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (PacketHornAffineSyntax.row wide w d t n r))
    (ha : Derives Γ (HornApplicationSyntax.application rule w r R)) : Derives Γ .bot := by
  rcases PacketAffineDispatchData.outer_shape (relation wide) rule.head
    (PacketAffineDispatchData.others_different wide rule hr) with ⟨tag,payload,hk,he⟩
  let C := HornApplicationSyntax.body rule w r R
  let Δ := Context.add C (raisedContext rule.arity Γ)
  apply HornApplicationRules.eliminate_application rule w r R .bot ha
  have hZ1 := HornBinderRules.zf_body rule.arity hZ C
  have hw1 := of_eq (omega_rename w (old rule.arity)) (HornBinderRules.under_body rule.arity hw C)
  have hc1 := of_eq (PacketHornAffineSyntax.row_rename wide w d t n r (old rule.arity))
    (HornBinderRules.under_body rule.arity hc C)
  have hC : Derives Δ C := .hyp (Or.inl rfl)
  have hg : Derives Δ (graph rule.head (old rule.arity w) (slot rule.arity) (old rule.arity r)) := .conjL (.conjR (.conjR hC))
  rw [he] at hg
  exact HornNodeDisjoint.node_contradiction hZ1 tag (relation wide) 3 hk payload (old rule.arity w) (old rule.arity r)
    (slot rule.arity) (SyntaxAtomSyntax.three (old rule.arity d) (old rule.arity t) (old rule.arity n)) hw1 (.conjL hC) hg hc1

theorem dispatch {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w d t n r R : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (PacketHornAffineSyntax.row wide w d t n r))
    (hs : Derives Γ (PacketTraceSyntax.step w r R)) :
    Derives Γ ((HornApplicationSyntax.application (baseRule wide) w r R).disj
      (HornApplicationSyntax.application (stepRule wide) w r R)) := by
  apply HornStepSyntax.step_elim ObjectPacket.rules w r R _ hs
  intro rule hr
  apply Derives.impI
  rcases PacketAffineDispatchData.rule_cases wide rule hr with hb | hb | ho
  · subst rule
    exact .disjL (.hyp (Or.inl rfl))
  · subst rule
    exact .disjR (.hyp (Or.inl rfl))
  · exact .botE (application_contradiction (ZFContext.add hZ _) wide rule ho w d t n r R
      (add hw _) (add hc _) (.hyp (Or.inl rfl)))

theorem step_iff_applications {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w d t n r R : Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (PacketHornAffineSyntax.row wide w d t n r)) :
    Derives Γ ((PacketTraceSyntax.step w r R).iff
      ((HornApplicationSyntax.application (baseRule wide) w r R).disj (HornApplicationSyntax.application (stepRule wide) w r R))) := by
  apply Derives.conjI
  · exact .impI (dispatch (ZFContext.add hZ _) wide w d t n r R (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    apply Derives.disjE (.hyp (Or.inl rfl))
    · exact HornStepSyntax.rule_intro ObjectPacket.rules (baseRule wide) (PacketAffineDispatchData.base_member wide) w r R (.hyp (Or.inl rfl))
    · exact HornStepSyntax.rule_intro ObjectPacket.rules (stepRule wide) (PacketAffineDispatchData.step_member wide) w r R (.hyp (Or.inl rfl))

theorem step_iff_outcomes {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (wide : Bool) (w B d t n r R : Fin m)
    (hw : Derives Γ (omega w)) (hB : Derives Γ (SyntaxNumeralSyntax.numeral (radix wide) B))
    (hc : Derives Γ (PacketHornAffineSyntax.row wide w d t n r)) :
    Derives Γ ((PacketTraceSyntax.step w r R).iff
      ((PacketAffineApplicationSyntax.baseOutcome wide w B r).disj (PacketAffineApplicationSyntax.stepOutcome wide w B R r))) :=
  SyntaxTypeLocalTransfer.iff_trans (step_iff_applications hZ wide w d t n r R hw hc)
    (SyntaxTypeLocalTransfer.disj_congr (PacketAffineApplication.base_iff hZ wide w B r R hw hB)
      (PacketAffineApplication.step_iff hZ wide w B r R hw hB))

end PPAC.Migration.Internal.PacketAffineDispatch
