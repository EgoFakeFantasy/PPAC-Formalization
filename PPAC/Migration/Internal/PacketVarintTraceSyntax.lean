import PPAC.Migration.Internal.PacketVarintRowSyntax

/-! Two internally finite sequences give the independent ordered independent varint-fold graph. -/
namespace PPAC.Migration.Internal.PacketVarintTraceSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax GraphSyntax PacketVarintRowSyntax
open SyntaxRenameQuerySyntax (of_eq)

def trace {m} (w C n t a z e l d f g : Fin m) : Formula m :=
  (StructuralListTraceSyntax.trace w z e l d f n).conj
    ((SequenceSyntax.sequence g d w).conj ((edge g z t).conj ((edge g l a).conj (links w C l f g))))

def body {m} (w C n t a : Fin m) : Formula (m+6) :=
  trace (old 6 w) (old 6 C) (old 6 n) (old 6 t) (old 6 a)
    (slot 6 0) (slot 6 1) (slot 6 2) (slot 6 3) (slot 6 4) (slot 6 5)

def foldAt {m} (w C n t a : Fin m) : Formula m := existsMany 6 (body w C n t a)

theorem trace_rename {m k} (w C n t a z e l d f g : Fin m) (ρ : Fin m → Fin k) :
    (trace w C n t a z e l d f g).rename ρ = trace (ρ w) (ρ C) (ρ n) (ρ t) (ρ a) (ρ z) (ρ e) (ρ l) (ρ d) (ρ f) (ρ g) := by
  simp only [trace,Formula.rename,StructuralListTraceSyntax.trace_rename,SequenceSyntax.sequence_rename,edge_rename,links_rename]

theorem body_lift {m k} (w C n t a : Fin m) (ρ : Fin m → Fin k) :
    (body w C n t a).rename (lift 6 ρ) = body (ρ w) (ρ C) (ρ n) (ρ t) (ρ a) := by
  simp only [body,trace_rename,lift_old,lift_slot]

theorem foldAt_rename {m k} (w C n t a : Fin m) (ρ : Fin m → Fin k) :
    (foldAt w C n t a).rename ρ = foldAt (ρ w) (ρ C) (ρ n) (ρ t) (ρ a) := by
  simp only [foldAt,existsMany_rename,body_lift]

theorem intro_trace {m} {Γ : Context m} (w C n t a z e l d f g : Fin m)
    (hf : Derives Γ (StructuralListTraceSyntax.trace w z e l d f n)) (hg : Derives Γ (SequenceSyntax.sequence g d w))
    (ht : Derives Γ (edge g z t)) (ha : Derives Γ (edge g l a)) (hl : Derives Γ (links w C l f g)) :
    Derives Γ (trace w C n t a z e l d f g) := .conjI hf (.conjI hg (.conjI ht (.conjI ha hl)))

theorem intro_fold {m} {Γ : Context m} (w C n t a z e l d f g : Fin m) (hf : Derives Γ (trace w C n t a z e l d f g)) :
    Derives Γ (foldAt w C n t a) := by
  apply HornBinderRules.intro_many 6 (body w C n t a) (six z e l d f g)
  exact of_eq (by simp only [body,trace_rename,assign_old,assign_slot]; rfl) hf

end PPAC.Migration.Internal.PacketVarintTraceSyntax
