import PPAC.Migration.Internal.PacketAffineApplicationBounds

/-! Exact structural outcomes of the original bounded affine applications; no extra naturality oracle. -/
namespace PPAC.Migration.Internal.PacketAffineApplicationSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax PacketHornAffineSyntax
open SyntaxRenameQuerySyntax (of_eq)

def baseOutcome {m} (wide : Bool) (w B r : Fin m) : Formula m := .ex
  (base wide w.castSucc B.castSucc (Fin.last m) r.castSucc)

def stepOutcomeBody {m} (wide : Bool) (w B V r : Fin m) : Formula (m+3) :=
  step wide (old 3 w) (old 3 B) (old 3 V) (slot 3 0) (slot 3 1) (slot 3 2) (old 3 r)

def stepOutcome {m} (wide : Bool) (w B V r : Fin m) : Formula m := existsMany 3 (stepOutcomeBody wide w B V r)

theorem baseOutcome_rename {m j} (wide : Bool) (w B r : Fin m) (ρ : Fin m → Fin j) :
    (baseOutcome wide w B r).rename ρ = baseOutcome wide (ρ w) (ρ B) (ρ r) := by
  simp only [baseOutcome, Formula.rename, base_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem stepOutcomeBody_lift {m j} (wide : Bool) (w B V r : Fin m) (ρ : Fin m → Fin j) :
    (stepOutcomeBody wide w B V r).rename (lift 3 ρ) = stepOutcomeBody wide (ρ w) (ρ B) (ρ V) (ρ r) := by
  simp only [stepOutcomeBody, step_rename, lift_old, lift_slot]

theorem stepOutcome_rename {m j} (wide : Bool) (w B V r : Fin m) (ρ : Fin m → Fin j) :
    (stepOutcome wide w B V r).rename ρ = stepOutcome wide (ρ w) (ρ B) (ρ V) (ρ r) := by
  simp only [stepOutcome, existsMany_rename, stepOutcomeBody_lift]

theorem intro_base {m} {Γ : Context m} (wide : Bool) (w B r d : Fin m)
    (hb : Derives Γ (base wide w B d r)) : Derives Γ (baseOutcome wide w B r) := by
  apply Derives.exI d
  exact of_eq (by simp only [Formula.instantiate, base_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hb

theorem intro_step {m} {Γ : Context m} (wide : Bool) (w B V r d t a : Fin m)
    (hs : Derives Γ (step wide w B V d t a r)) : Derives Γ (stepOutcome wide w B V r) := by
  apply HornBinderRules.intro_many 3 (stepOutcomeBody wide w B V r) (SyntaxAtomSyntax.three d t a)
  exact of_eq (by simp only [stepOutcomeBody, step_rename, assign_old, assign_slot]; rfl) hs

end PPAC.Migration.Internal.PacketAffineApplicationSyntax
