import PPAC.Migration.Internal.HornClosedTraceExtension

/-! The Packet trace uses the pinned actual ten-rule table, not the Transform table. -/
namespace PPAC.Migration.Internal.PacketTraceSyntax
open Source SourceAlgebra SourceLogic
open YesMetaZFC.Automation

def step {m} (w r R : Fin m) : Formula m := HornStepSyntax.step ObjectPacket.rules w r R

def closed {m} (w R : Fin m) : Formula m := HornClosedTraceSyntax.closed ObjectPacket.rules w R

def witness {m} (w r R : Fin m) : Formula m := HornClosedTraceSyntax.witness ObjectPacket.rules w r R

def condition {m} (w r : Fin m) : Formula m := HornClosedTraceSyntax.condition ObjectPacket.rules w r

theorem step_rename {m j} (w r R : Fin m) (ρ : Fin m → Fin j) :
    (step w r R).rename ρ = step (ρ w) (ρ r) (ρ R) := HornStepSyntax.step_rename ObjectPacket.rules w r R ρ

theorem closed_rename {m j} (w R : Fin m) (ρ : Fin m → Fin j) :
    (closed w R).rename ρ = closed (ρ w) (ρ R) := HornClosedTraceSyntax.closed_rename ObjectPacket.rules w R ρ

theorem witness_rename {m j} (w r R : Fin m) (ρ : Fin m → Fin j) :
    (witness w r R).rename ρ = witness (ρ w) (ρ r) (ρ R) := HornClosedTraceSyntax.witness_rename ObjectPacket.rules w r R ρ

theorem condition_rename {m j} (w r : Fin m) (ρ : Fin m → Fin j) :
    (condition w r).rename ρ = condition (ρ w) (ρ r) := HornClosedTraceSyntax.condition_rename ObjectPacket.rules w r ρ

end PPAC.Migration.Internal.PacketTraceSyntax
