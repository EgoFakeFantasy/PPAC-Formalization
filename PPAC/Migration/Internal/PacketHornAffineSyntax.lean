import PPAC.Migration.Internal.HornExprAddConst

/-! Exact structural rows and local matrices for the two pinned Packet affine relations. -/
namespace PPAC.Migration.Internal.PacketHornAffineSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def row {m} (wide : Bool) (w d t n r : Fin m) : Formula m :=
  SyntaxNodeSyntax.constructor 3 (PacketAffineRuleData.relation wide) w (SyntaxAtomSyntax.three d t n) r

def entry {m} (wide : Bool) (w V d t n : Fin m) : Formula m := .ex
  ((row wide w.castSucc d.castSucc t.castSucc n.castSucc (Fin.last m)).conj (.mem (Fin.last m) V.castSucc))

def base {m} (wide : Bool) (w B d r : Fin m) : Formula m := .ex
  ((empty (Fin.last m)).conj ((row wide w.castSucc d.castSucc (Fin.last m) d.castSucc r.castSucc).conj (.mem d.castSucc B.castSucc)))

def stepBody {m} (wide : Bool) (w B V d t a r : Fin m) : Formula (m+2) :=
  (successor (slot 2 0) (old 2 t)).conj
    ((NaturalAdditionSyntax.sum (old 2 w) (old 2 a) (old 2 B) (slot 2 1)).conj
      ((row wide (old 2 w) (old 2 d) (slot 2 0) (slot 2 1) (old 2 r)).conj
        (entry wide (old 2 w) (old 2 V) (old 2 d) (old 2 t) (old 2 a))))

def step {m} (wide : Bool) (w B V d t a r : Fin m) : Formula m := existsMany 2 (stepBody wide w B V d t a r)

theorem row_rename {m k} (wide : Bool) (w d t n r : Fin m) (ρ : Fin m → Fin k) :
    (row wide w d t n r).rename ρ = row wide (ρ w) (ρ d) (ρ t) (ρ n) (ρ r) := by
  simp only [row, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.three_map]

theorem entry_rename {m k} (wide : Bool) (w V d t n : Fin m) (ρ : Fin m → Fin k) :
    (entry wide w V d t n).rename ρ = entry wide (ρ w) (ρ V) (ρ d) (ρ t) (ρ n) := by
  simp only [entry, Formula.rename, row_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem base_rename {m k} (wide : Bool) (w B d r : Fin m) (ρ : Fin m → Fin k) :
    (base wide w B d r).rename ρ = base wide (ρ w) (ρ B) (ρ d) (ρ r) := by
  simp only [base, Formula.rename, row_rename, empty_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem stepBody_lift {m k} (wide : Bool) (w B V d t a r : Fin m) (ρ : Fin m → Fin k) :
    (stepBody wide w B V d t a r).rename (lift 2 ρ) = stepBody wide (ρ w) (ρ B) (ρ V) (ρ d) (ρ t) (ρ a) (ρ r) := by
  simp only [stepBody, Formula.rename, successor_rename, NaturalAdditionSyntax.sum_rename, row_rename, entry_rename, lift_old, lift_slot]

theorem step_rename {m k} (wide : Bool) (w B V d t a r : Fin m) (ρ : Fin m → Fin k) :
    (step wide w B V d t a r).rename ρ = step wide (ρ w) (ρ B) (ρ V) (ρ d) (ρ t) (ρ a) (ρ r) := by
  simp only [step, existsMany_rename, stepBody_lift]

theorem intro_step {m} {Γ : Context m} (wide : Bool) (w B V d t a r s y : Fin m)
    (hs : Derives Γ (successor s t)) (hy : Derives Γ (NaturalAdditionSyntax.sum w a B y))
    (hr : Derives Γ (row wide w d s y r)) (hp : Derives Γ (entry wide w V d t a)) :
    Derives Γ (step wide w B V d t a r) := by
  apply HornBinderRules.intro_many 2 (stepBody wide w B V d t a r) (SyntaxAtomSyntax.two s y)
  exact of_eq (by simp only [stepBody, Formula.rename, successor_rename, NaturalAdditionSyntax.sum_rename,
    row_rename, entry_rename, assign_slot, assign_old]; rfl) (.conjI hs (.conjI hy (.conjI hr hp)))

end PPAC.Migration.Internal.PacketHornAffineSyntax
