import PPAC.Migration.Internal.PacketStructureDispatchData

/-! Actual ten-rule root dispatch and complete structural forward unfolding; reverse unbounded search remains open. -/
namespace PPAC.Migration.Internal.PacketStructureDispatch
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax HornExprSyntax PacketStructureSyntax PacketStructureApplicationSyntax PacketStructureDispatchData
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation
open ObjectHorn (Rule)

def applications {m} : Family → Fin m → Fin m → Fin m → Formula m
  | .tree, w, V, r => HornApplicationSyntax.application (rule .tree) w r V
  | .forest, w, V, r => (HornApplicationSyntax.application (rule .nil) w r V).disj (HornApplicationSyntax.application (rule .cons) w r V)
  | .packet, w, V, r => HornApplicationSyntax.application (rule .packet) w r V

def results {m} (bounded : Bool) (f : Family) (w V r : Fin m) : Formula m :=
  let R := if bounded then boundedOutcome else outcome
  match f with
  | .tree => R .tree w V r
  | .forest => (R .nil w V r).disj (R .cons w V r)
  | .packet => R .packet w V r

theorem applications_rename {m j} (f : Family) (w V r : Fin m) (ρ : Fin m → Fin j) :
    (applications f w V r).rename ρ = applications f (ρ w) (ρ V) (ρ r) := by
  cases f
  · exact HornApplicationSyntax.application_rename (rule .tree) w r V ρ
  · simp only [applications,Formula.rename,HornApplicationSyntax.application_rename]
  · exact HornApplicationSyntax.application_rename (rule .packet) w r V ρ

theorem results_rename {m j} (bounded : Bool) (f : Family) (w V r : Fin m) (ρ : Fin m → Fin j) :
    (results bounded f w V r).rename ρ = results bounded f (ρ w) (ρ V) (ρ r) := by
  cases bounded with
  | false =>
    cases f with
    | tree => exact outcome_rename .tree w V r ρ
    | forest =>
      change ((outcome .nil w V r).disj (outcome .cons w V r)).rename ρ =
        (outcome .nil (ρ w) (ρ V) (ρ r)).disj (outcome .cons (ρ w) (ρ V) (ρ r))
      simp only [Formula.rename,outcome_rename]
    | packet => exact outcome_rename .packet w V r ρ
  | true =>
    cases f with
    | tree => exact boundedOutcome_rename .tree w V r ρ
    | forest =>
      change ((boundedOutcome .nil w V r).disj (boundedOutcome .cons w V r)).rename ρ =
        (boundedOutcome .nil (ρ w) (ρ V) (ρ r)).disj (boundedOutcome .cons (ρ w) (ρ V) (ρ r))
      simp only [Formula.rename,boundedOutcome_rename]
    | packet => exact boundedOutcome_rename .packet w V r ρ

theorem introduce_case {m} {Γ : Context m} (f : Family) (b : Branch) (hb : b ∈ branches f) (w V r : Fin m)
    (ha : Derives Γ (HornApplicationSyntax.application (rule b) w r V)) : Derives Γ (applications f w V r) := by
  cases f with
  | tree =>
    have he : b = .tree := by simpa only [branches,List.mem_cons,List.not_mem_nil,or_false] using hb
    subst b
    exact ha
  | forest =>
    have he : b = .nil ∨ b = .cons := by simpa only [branches,List.mem_cons,List.not_mem_nil,or_false] using hb
    rcases he with rfl | rfl
    · exact .disjL ha
    · exact .disjR ha
  | packet =>
    have he : b = .packet := by simpa only [branches,List.mem_cons,List.not_mem_nil,or_false] using hb
    subst b
    exact ha

theorem application_contradiction {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (rul : Rule)
    (hr : rul ∈ others f) (w V r : Fin m) (xs : Fin (width f) → Fin m) (hw : Derives Γ (omega w))
    (hc : Derives Γ (row (width f) (tag f) w xs r)) (ha : Derives Γ (HornApplicationSyntax.application rul w r V)) : Derives Γ .bot := by
  rcases PacketAffineDispatchData.outer_shape (tag f) rul.head (others_different f rul hr) with ⟨t,payload,hk,he⟩
  let L := HornApplicationSyntax.body rul w r V
  let Δ := Context.add L (raisedContext rul.arity Γ)
  apply HornApplicationRules.eliminate_application rul w r V .bot ha
  have hwk := of_eq (omega_rename w (old rul.arity)) (HornBinderRules.under_body rul.arity hw L)
  have hck := of_eq (row_rename (width f) (tag f) w r xs (old rul.arity)) (HornBinderRules.under_body rul.arity hc L)
  have hL : Derives Δ L := .hyp (Or.inl rfl)
  have hg : Derives Δ (graph rul.head (old rul.arity w) (slot rul.arity) (old rul.arity r)) := .conjL (.conjR (.conjR hL))
  rw [he] at hg
  exact HornNodeDisjoint.node_contradiction (HornBinderRules.zf_body rul.arity hZ L) t (tag f) (width f) hk payload
    (old rul.arity w) (old rul.arity r) (slot rul.arity) (fun i => old rul.arity (xs i)) hwk (.conjL hL) hg hck

theorem dispatch {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (w V r : Fin m) (xs : Fin (width f) → Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (row (width f) (tag f) w xs r)) (hs : Derives Γ (PacketTraceSyntax.step w r V)) :
    Derives Γ (applications f w V r) := by
  apply HornStepSyntax.step_elim ObjectPacket.rules w r V _ hs
  intro rul hr
  apply Derives.impI
  rcases rule_cases f rul hr with ⟨b,hb,he⟩ | ho
  · subst rul
    exact introduce_case f b hb w V r (.hyp (Or.inl rfl))
  · exact .botE (application_contradiction (ZFContext.add hZ _) f rul ho w V r xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))

theorem step_of_applications {m} {Γ : Context m} (f : Family) (w V r : Fin m) (ha : Derives Γ (applications f w V r)) :
    Derives Γ (PacketTraceSyntax.step w r V) := by
  cases f with
  | tree => exact HornStepSyntax.rule_intro ObjectPacket.rules (rule .tree) (branch_member .tree) w r V ha
  | forest =>
    apply Derives.disjE ha
    · exact HornStepSyntax.rule_intro ObjectPacket.rules (rule .nil) (branch_member .nil) w r V (.hyp (Or.inl rfl))
    · exact HornStepSyntax.rule_intro ObjectPacket.rules (rule .cons) (branch_member .cons) w r V (.hyp (Or.inl rfl))
  | packet => exact HornStepSyntax.rule_intro ObjectPacket.rules (rule .packet) (branch_member .packet) w r V ha

theorem step_iff_applications {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (w V r : Fin m) (xs : Fin (width f) → Fin m)
    (hw : Derives Γ (omega w)) (hc : Derives Γ (row (width f) (tag f) w xs r)) :
    Derives Γ ((PacketTraceSyntax.step w r V).iff (applications f w V r)) := by
  apply Derives.conjI
  · exact .impI (dispatch (ZFContext.add hZ _) f w V r xs (add hw _) (add hc _) (.hyp (Or.inl rfl)))
  · exact .impI (step_of_applications f w V r (.hyp (Or.inl rfl)))

theorem applications_iff_bounded {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (w V r : Fin m) (hw : Derives Γ (omega w)) :
    Derives Γ ((applications f w V r).iff (results true f w V r)) := by
  cases f with
  | tree => exact PacketStructureApplication.bounded_iff hZ .tree w V r hw
  | forest => exact SyntaxTypeLocalTransfer.disj_congr (PacketStructureApplication.bounded_iff hZ .nil w V r hw) (PacketStructureApplication.bounded_iff hZ .cons w V r hw)
  | packet => exact PacketStructureApplication.bounded_iff hZ .packet w V r hw

theorem applications_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (w V r : Fin m)
    (hw : Derives Γ (omega w)) (ha : Derives Γ (applications f w V r)) : Derives Γ (results false f w V r) := by
  cases f with
  | tree => exact PacketStructureApplication.forward hZ .tree w V r hw ha
  | forest =>
    apply Derives.disjE ha
    · exact .disjL (PacketStructureApplication.forward (ZFContext.add hZ _) .nil w V r (add hw _) (.hyp (Or.inl rfl)))
    · exact .disjR (PacketStructureApplication.forward (ZFContext.add hZ _) .cons w V r (add hw _) (.hyp (Or.inl rfl)))
  | packet => exact PacketStructureApplication.forward hZ .packet w V r hw ha

theorem condition_iff_bounded {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (w V r : Fin m) (xs : Fin (width f) → Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (PacketTraceCore.value w V)) (hc : Derives Γ (row (width f) (tag f) w xs r)) :
    Derives Γ ((PacketTraceSyntax.condition w r).iff (results true f w V r)) :=
  SyntaxTypeLocalTransfer.iff_trans (PacketTraceCore.unfold_iff hZ w V r hw hv)
    (SyntaxTypeLocalTransfer.iff_trans (step_iff_applications hZ f w V r xs hw hc) (applications_iff_bounded hZ f w V r hw))

theorem condition_forward {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (f : Family) (w V r : Fin m) (xs : Fin (width f) → Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (PacketTraceCore.value w V)) (hc : Derives Γ (row (width f) (tag f) w xs r))
    (hr : Derives Γ (PacketTraceSyntax.condition w r)) : Derives Γ (results false f w V r) :=
  applications_forward hZ f w V r hw (dispatch hZ f w V r xs hw hc (.impE (.conjL (PacketTraceCore.unfold_iff hZ w V r hw hv)) hr))

end PPAC.Migration.Internal.PacketStructureDispatch
