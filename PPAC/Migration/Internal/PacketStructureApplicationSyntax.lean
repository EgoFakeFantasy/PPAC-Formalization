import PPAC.Migration.Internal.PacketStructureLocal

/-! All four original arities retain their natural and numeric search guards in the exact bounded outcome. -/
namespace PPAC.Migration.Internal.PacketStructureApplicationSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax HornExprSyntax HornExprBounds PacketStructureLocalSyntax PacketStructureRuleData
open SyntaxRenameQuerySyntax (of_eq)
open YesMetaZFC.Automation.ObjectHorn (Rule)

inductive Branch where
  | tree | nil | cons | packet

def rule : Branch → Rule
  | .tree => treeRule
  | .nil => nilRule
  | .cons => consRule
  | .packet => packetRule

def localCase {m} : (b : Branch) → Fin m → Fin m → Fin m → (Fin (rule b).arity → Fin m) → Formula m
  | .tree, w, V, r, env => treeLocal w V r env
  | .nil, w, V, r, env => nilLocal w V r env
  | .cons, w, V, r, env => consLocal w V r env
  | .packet, w, V, r, env => packetLocal w V r env

def outcomeBody {m} (b : Branch) (w V r : Fin m) : Formula (m+(rule b).arity) :=
  localCase b (old (rule b).arity w) (old (rule b).arity V) (old (rule b).arity r) (slot (rule b).arity)

def outcome {m} (b : Branch) (w V r : Fin m) : Formula m := existsMany (rule b).arity (outcomeBody b w V r)

def boundedAt {m} (b : Branch) (w V r : Fin m) (env : Fin (rule b).arity → Fin m) : Formula m :=
  (environmentNat (rule b).arity w env).conj ((environmentBound (rule b).arity r env).conj (localCase b w V r env))

def boundedBody {m} (b : Branch) (w V r : Fin m) : Formula (m+(rule b).arity) :=
  boundedAt b (old (rule b).arity w) (old (rule b).arity V) (old (rule b).arity r) (slot (rule b).arity)

def boundedOutcome {m} (b : Branch) (w V r : Fin m) : Formula m := existsMany (rule b).arity (boundedBody b w V r)

theorem localCase_rename {m j} (b : Branch) (w V r : Fin m) (env : Fin (rule b).arity → Fin m) (ρ : Fin m → Fin j) :
    (localCase b w V r env).rename ρ = localCase b (ρ w) (ρ V) (ρ r) (fun i => ρ (env i)) := by
  cases b
  · exact treeLocal_rename w V r env ρ
  · exact nilLocal_rename w V r env ρ
  · exact consLocal_rename w V r env ρ
  · exact packetLocal_rename w V r env ρ

theorem boundedAt_rename {m j} (b : Branch) (w V r : Fin m) (env : Fin (rule b).arity → Fin m) (ρ : Fin m → Fin j) :
    (boundedAt b w V r env).rename ρ = boundedAt b (ρ w) (ρ V) (ρ r) (fun i => ρ (env i)) := by
  simp only [boundedAt,Formula.rename,environmentNat_rename,environmentBound_rename,localCase_rename]

theorem outcomeBody_lift {m j} (b : Branch) (w V r : Fin m) (ρ : Fin m → Fin j) :
    (outcomeBody b w V r).rename (lift (rule b).arity ρ) = outcomeBody b (ρ w) (ρ V) (ρ r) := by
  simp only [outcomeBody,localCase_rename,lift_old,lift_slot]

theorem boundedBody_lift {m j} (b : Branch) (w V r : Fin m) (ρ : Fin m → Fin j) :
    (boundedBody b w V r).rename (lift (rule b).arity ρ) = boundedBody b (ρ w) (ρ V) (ρ r) := by
  simp only [boundedBody,boundedAt_rename,lift_old,lift_slot]

theorem outcome_rename {m j} (b : Branch) (w V r : Fin m) (ρ : Fin m → Fin j) :
    (outcome b w V r).rename ρ = outcome b (ρ w) (ρ V) (ρ r) := by
  simp only [outcome,existsMany_rename,outcomeBody_lift]

theorem boundedOutcome_rename {m j} (b : Branch) (w V r : Fin m) (ρ : Fin m → Fin j) :
    (boundedOutcome b w V r).rename ρ = boundedOutcome b (ρ w) (ρ V) (ρ r) := by
  simp only [boundedOutcome,existsMany_rename,boundedBody_lift]

theorem intro_outcome {m} {Γ : Context m} (b : Branch) (w V r : Fin m) (env : Fin (rule b).arity → Fin m)
    (hl : Derives Γ (localCase b w V r env)) : Derives Γ (outcome b w V r) := by
  apply HornBinderRules.intro_many (rule b).arity (outcomeBody b w V r) env
  exact of_eq (by simp only [outcomeBody,localCase_rename,assign_old,assign_slot]) hl

theorem intro_bounded {m} {Γ : Context m} (b : Branch) (w V r : Fin m) (env : Fin (rule b).arity → Fin m)
    (hl : Derives Γ (boundedAt b w V r env)) : Derives Γ (boundedOutcome b w V r) := by
  apply HornBinderRules.intro_many (rule b).arity (boundedBody b w V r) env
  exact of_eq (by simp only [boundedBody,boundedAt_rename,assign_old,assign_slot]) hl

end PPAC.Migration.Internal.PacketStructureApplicationSyntax
