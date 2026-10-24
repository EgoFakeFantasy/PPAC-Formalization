import PPAC.Migration.Internal.PacketTokenApplicationBounds

/-! Complete arity-three and arity-six token outcomes keep every original assignment. -/
namespace PPAC.Migration.Internal.PacketTokenApplicationSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax PacketTokenSyntax
open SyntaxRenameQuerySyntax (of_eq)

def smallBody {m} (w B V r : Fin m) : Formula (m+3) :=
  small (old 3 w) (old 3 B) (old 3 V) (slot 3 0) (slot 3 1) (slot 3 2) (old 3 r)

def smallOutcome {m} (w B V r : Fin m) : Formula m := existsMany 3 (smallBody w B V r)

def largeOutcomeBody {m} (w B V r : Fin m) : Formula (m+6) := large (old 6 w) (old 6 B) (old 6 V) (old 6 r) (slot 6)

def largeOutcome {m} (w B V r : Fin m) : Formula m := existsMany 6 (largeOutcomeBody w B V r)

theorem smallBody_lift {m j} (w B V r : Fin m) (ρ : Fin m → Fin j) :
    (smallBody w B V r).rename (lift 3 ρ) = smallBody (ρ w) (ρ B) (ρ V) (ρ r) := by
  simp only [smallBody, small_rename, lift_old, lift_slot]

theorem smallOutcome_rename {m j} (w B V r : Fin m) (ρ : Fin m → Fin j) :
    (smallOutcome w B V r).rename ρ = smallOutcome (ρ w) (ρ B) (ρ V) (ρ r) := by
  simp only [smallOutcome, existsMany_rename, smallBody_lift]

theorem largeOutcomeBody_lift {m j} (w B V r : Fin m) (ρ : Fin m → Fin j) :
    (largeOutcomeBody w B V r).rename (lift 6 ρ) = largeOutcomeBody (ρ w) (ρ B) (ρ V) (ρ r) := by
  simp only [largeOutcomeBody, large_rename, lift_old, lift_slot]

theorem largeOutcome_rename {m j} (w B V r : Fin m) (ρ : Fin m → Fin j) :
    (largeOutcome w B V r).rename ρ = largeOutcome (ρ w) (ρ B) (ρ V) (ρ r) := by
  simp only [largeOutcome, existsMany_rename, largeOutcomeBody_lift]

theorem intro_small {m} {Γ : Context m} (w B V r n t a : Fin m)
    (hs : Derives Γ (small w B V n t a r)) : Derives Γ (smallOutcome w B V r) := by
  apply HornBinderRules.intro_many 3 (smallBody w B V r) (SyntaxAtomSyntax.three n t a)
  exact of_eq (by simp only [smallBody, small_rename, assign_old, assign_slot]; rfl) hs

theorem intro_large {m} {Γ : Context m} (w B V r : Fin m) (env : Fin 6 → Fin m)
    (hl : Derives Γ (large w B V r env)) : Derives Γ (largeOutcome w B V r) := by
  apply HornBinderRules.intro_many 6 (largeOutcomeBody w B V r) env
  exact of_eq (by simp only [largeOutcomeBody, large_rename, assign_old, assign_slot]) hl

end PPAC.Migration.Internal.PacketTokenApplicationSyntax
