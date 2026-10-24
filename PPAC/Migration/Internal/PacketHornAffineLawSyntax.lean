import PPAC.Migration.Internal.PacketHornAffineLocal

/-! Universally quantified actual local-matrix laws and an internally constructed literal radix frame. -/
namespace PPAC.Migration.Internal.PacketHornAffineLawSyntax
open Source SourceAlgebra SourceLogic HornExprSyntax HornBinderSyntax PacketHornAffineSyntax
open PacketAffineRuleData (baseRule stepRule)

def baseAt {m} (wide : Bool) (w B d r V : Fin m) : Formula m :=
  (environmentNat 1 w (fun _ => d)).imp
    ((HornRuleSyntax.matrix (baseRule wide) w r V (fun _ => d)).iff (base wide w B d r))

def stepAt {m} (wide : Bool) (w B d t a r V : Fin m) : Formula m :=
  (environmentNat 3 w (SyntaxAtomSyntax.three d t a)).imp
    ((HornRuleSyntax.matrix (stepRule wide) w r V (SyntaxAtomSyntax.three d t a)).iff (step wide w B V d t a r))

def baseBody {m} (wide : Bool) (w B : Fin m) : Formula (m+3) :=
  baseAt wide (old 3 w) (old 3 B) (slot 3 0) (slot 3 1) (slot 3 2)

def stepLawBody {m} (wide : Bool) (w B : Fin m) : Formula (m+5) :=
  stepAt wide (old 5 w) (old 5 B) (slot 5 0) (slot 5 1) (slot 5 2) (slot 5 3) (slot 5 4)

def baseLaw {m} (wide : Bool) (w B : Fin m) : Formula m := OriginalUniversalBlock.allMany 3 (baseBody wide w B)

def stepLaw {m} (wide : Bool) (w B : Fin m) : Formula m := OriginalUniversalBlock.allMany 5 (stepLawBody wide w B)

def system {m} (wide : Bool) (w B : Fin m) : Formula m :=
  (PacketAffineLiteralSyntax.frame wide w B).conj ((baseLaw wide w B).conj (stepLaw wide w B))

def existsSystem {m} (wide : Bool) (w : Fin m) : Formula m := .ex (system wide w.castSucc (Fin.last m))

theorem baseAt_rename {m j} (wide : Bool) (w B d r V : Fin m) (ρ : Fin m → Fin j) :
    (baseAt wide w B d r V).rename ρ = baseAt wide (ρ w) (ρ B) (ρ d) (ρ r) (ρ V) := by
  simp only [baseAt, Formula.iff, Formula.rename, environmentNat_rename, HornRuleSyntax.matrix_rename, base_rename]

theorem stepAt_rename {m j} (wide : Bool) (w B d t a r V : Fin m) (ρ : Fin m → Fin j) :
    (stepAt wide w B d t a r V).rename ρ = stepAt wide (ρ w) (ρ B) (ρ d) (ρ t) (ρ a) (ρ r) (ρ V) := by
  have he := SyntaxAtomSyntax.three_map d t a ρ
  have hm := (HornRuleSyntax.matrix_rename (stepRule wide) w r V (SyntaxAtomSyntax.three d t a) ρ).trans
    (congrArg (fun env : Fin 3 → Fin j => HornRuleSyntax.matrix (stepRule wide) (ρ w) (ρ r) (ρ V) env) he)
  simp only [stepAt, Formula.iff, Formula.rename, environmentNat_rename, hm,
    step_rename, SyntaxAtomSyntax.three_map]

theorem baseBody_lift {m j} (wide : Bool) (w B : Fin m) (ρ : Fin m → Fin j) :
    (baseBody wide w B).rename (lift 3 ρ) = baseBody wide (ρ w) (ρ B) := by
  simp only [baseBody, baseAt_rename, lift_old, lift_slot]

theorem stepLawBody_lift {m j} (wide : Bool) (w B : Fin m) (ρ : Fin m → Fin j) :
    (stepLawBody wide w B).rename (lift 5 ρ) = stepLawBody wide (ρ w) (ρ B) := by
  simp only [stepLawBody, stepAt_rename, lift_old, lift_slot]

theorem baseLaw_rename {m j} (wide : Bool) (w B : Fin m) (ρ : Fin m → Fin j) :
    (baseLaw wide w B).rename ρ = baseLaw wide (ρ w) (ρ B) := by
  simp only [baseLaw, OriginalUniversalBlock.allMany_rename, baseBody_lift]

theorem stepLaw_rename {m j} (wide : Bool) (w B : Fin m) (ρ : Fin m → Fin j) :
    (stepLaw wide w B).rename ρ = stepLaw wide (ρ w) (ρ B) := by
  simp only [stepLaw, OriginalUniversalBlock.allMany_rename, stepLawBody_lift]

theorem system_rename {m j} (wide : Bool) (w B : Fin m) (ρ : Fin m → Fin j) :
    (system wide w B).rename ρ = system wide (ρ w) (ρ B) := by
  simp only [system, Formula.rename, PacketAffineLiteralSyntax.frame_rename, baseLaw_rename, stepLaw_rename]

theorem existsSystem_rename {m j} (wide : Bool) (w : Fin m) (ρ : Fin m → Fin j) :
    (existsSystem wide w).rename ρ = existsSystem wide (ρ w) := by
  simp only [existsSystem, Formula.rename, system_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

end PPAC.Migration.Internal.PacketHornAffineLawSyntax
