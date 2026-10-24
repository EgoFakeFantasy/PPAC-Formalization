import PPAC.Migration.Internal.ObjectForallClosure
import PPAC.Migration.Internal.SyntaxComposeGraph

/-! The two-successor shift is the actual composite of two complete successor maps. -/
namespace PPAC.Migration.Internal.SchemaDoubleShiftSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def displacement {m} (i j : Fin m) : Formula m := .ex
  ((successor (Fin.last m) i.castSucc).conj (successor j.castSucc (Fin.last m)))

def matrix {m} (w n b c g : Fin m) (env : Fin 2 → Fin m) : Formula m :=
  (SyntaxFreeShiftSyntax.shiftMap w n b (env 0)).conj
    ((SyntaxFreeShiftSyntax.shiftMap w b c (env 1)).conj (SyntaxComposeSyntax.composed w (env 0) (env 1) n b c g))

def body {m} (w n b c g : Fin m) : Formula (m+2) := matrix (old 2 w) (old 2 n) (old 2 b) (old 2 c) (old 2 g) (slot 2)

def map {m} (w n b c g : Fin m) : Formula m := existsMany 2 (body w n b c g)

def existsMap {m} (w n b c : Fin m) : Formula m := .ex (map w.castSucc n.castSucc b.castSucc c.castSucc (Fin.last m))

theorem displacement_rename {m l} (i j : Fin m) (ρ : Fin m → Fin l) :
    (displacement i j).rename ρ = displacement (ρ i) (ρ j) := by
  simp only [displacement, Formula.rename, successor_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_rename {m l} (w n b c g : Fin m) (env : Fin 2 → Fin m) (ρ : Fin m → Fin l) :
    (matrix w n b c g env).rename ρ = matrix (ρ w) (ρ n) (ρ b) (ρ c) (ρ g) (fun i => ρ (env i)) := by
  simp only [matrix, Formula.rename, SyntaxFreeShiftSyntax.shiftMap_rename, SyntaxComposeSyntax.composed_rename]

theorem body_lift {m l} (w n b c g : Fin m) (ρ : Fin m → Fin l) :
    (body w n b c g).rename (lift 2 ρ) = body (ρ w) (ρ n) (ρ b) (ρ c) (ρ g) := by
  simp only [body, matrix_rename, lift_old, lift_slot]

theorem map_rename {m l} (w n b c g : Fin m) (ρ : Fin m → Fin l) :
    (map w n b c g).rename ρ = map (ρ w) (ρ n) (ρ b) (ρ c) (ρ g) := by
  simp only [map, existsMany_rename, body_lift]

theorem existsMap_rename {m l} (w n b c : Fin m) (ρ : Fin m → Fin l) :
    (existsMap w n b c).rename ρ = existsMap (ρ w) (ρ n) (ρ b) (ρ c) := by
  simp only [existsMap, Formula.rename, map_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_displacement {m} {Γ : Context m} (i j k : Fin m) (hi : Derives Γ (successor k i))
    (hj : Derives Γ (successor j k)) : Derives Γ (displacement i j) := by
  apply Derives.exI k
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, successor_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hi hj)

theorem intro_map {m} {Γ : Context m} (w n b c g r t : Fin m)
    (hr : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w n b r))
    (ht : Derives Γ (SyntaxFreeShiftSyntax.shiftMap w b c t))
    (hg : Derives Γ (SyntaxComposeSyntax.composed w r t n b c g)) : Derives Γ (map w n b c g) := by
  apply HornBinderRules.intro_many 2 (body w n b c g) (Source.SetLanguage.args2 r t)
  exact of_eq (by simp only [body, matrix_rename, assign_old, assign_slot]; rfl) (.conjI hr (.conjI ht hg))

theorem intro_exists {m} {Γ : Context m} (w n b c g : Fin m)
    (hg : Derives Γ (map w n b c g)) : Derives Γ (existsMap w n b c) := by
  apply Derives.exI g
  exact of_eq (by simp only [Formula.instantiate, map_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hg

end PPAC.Migration.Internal.SchemaDoubleShiftSyntax
