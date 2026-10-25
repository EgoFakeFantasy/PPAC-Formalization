import PPAC.Migration.Internal.PacketTokensBytesRowSyntax

/-! Two internally finite sequences give the independent ordered coupled-seeded graph. -/
namespace PPAC.Migration.Internal.PacketTokensBytesSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax PacketTokensBytesRowSyntax
open SyntaxRenameQuerySyntax (of_eq)

def trace {m} (w n t a z e l d f g : Fin m) : Formula m :=
  (StructuralListTraceSyntax.trace w z e l d f n).conj
    ((SequenceSyntax.sequence g d w).conj ((edge g z t).conj ((edge g l a).conj (links w l f g))))

def body {m} (w n t a : Fin m) : Formula (m+6) :=
  trace (old 6 w) (old 6 n) (old 6 t) (old 6 a)
    (slot 6 0) (slot 6 1) (slot 6 2) (slot 6 3) (slot 6 4) (slot 6 5)

def raw {m} (w n t a : Fin m) : Formula m := existsMany 6 (body w n t a)

def seeded {m} (w n t a : Fin m) : Formula m :=
  (StructuralListTraceSyntax.valid w t).conj ((StructuralListTraceSyntax.valid w a).conj (raw w n t a))

theorem trace_rename {m k} (w n t a z e l d f g : Fin m) (ρ : Fin m → Fin k) :
    (trace w n t a z e l d f g).rename ρ = trace (ρ w) (ρ n) (ρ t) (ρ a) (ρ z) (ρ e) (ρ l) (ρ d) (ρ f) (ρ g) := by
  simp only [trace,Formula.rename,StructuralListTraceSyntax.trace_rename,SequenceSyntax.sequence_rename,edge_rename,links_rename]

theorem body_lift {m k} (w n t a : Fin m) (ρ : Fin m → Fin k) :
    (body w n t a).rename (lift 6 ρ) = body (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [body,trace_rename,lift_old,lift_slot]

theorem raw_rename {m k} (w n t a : Fin m) (ρ : Fin m → Fin k) :
    (raw w n t a).rename ρ = raw (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [raw,existsMany_rename,body_lift]

theorem seeded_rename {m k} (w n t a : Fin m) (ρ : Fin m → Fin k) :
    (seeded w n t a).rename ρ = seeded (ρ w) (ρ n) (ρ t) (ρ a) := by
  simp only [seeded,Formula.rename,StructuralListTraceSyntax.valid_rename,raw_rename]

theorem intro_trace {m} {Γ : Context m} (w n t a z e l d f g : Fin m)
    (hf : Derives Γ (StructuralListTraceSyntax.trace w z e l d f n)) (hg : Derives Γ (SequenceSyntax.sequence g d w))
    (ht : Derives Γ (edge g z t)) (ha : Derives Γ (edge g l a)) (hl : Derives Γ (links w l f g)) :
    Derives Γ (trace w n t a z e l d f g) := .conjI hf (.conjI hg (.conjI ht (.conjI ha hl)))

theorem intro_raw {m} {Γ : Context m} (w n t a z e l d f g : Fin m) (hf : Derives Γ (trace w n t a z e l d f g)) :
    Derives Γ (raw w n t a) := by
  apply HornBinderRules.intro_many 6 (body w n t a) (six z e l d f g)
  exact of_eq (by simp only [body,trace_rename,assign_old,assign_slot]; rfl) hf

end PPAC.Migration.Internal.PacketTokensBytesSyntax
