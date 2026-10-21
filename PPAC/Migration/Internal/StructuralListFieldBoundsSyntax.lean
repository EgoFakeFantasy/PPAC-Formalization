import PPAC.Migration.Internal.ObjectStructuralListCheck

/-! 全内部长度、全部域内字段的原码严格成员界。 -/
namespace PPAC.Migration.Internal.StructuralListFieldBoundsSyntax
open Source SourceAlgebra SourceLogic StructuralListFieldSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)

def property {m} (w r : Fin m) : Formula m := .all (.all (.all
  ((hasLength w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc r.castSucc.castSucc.castSucc).imp
    ((Formula.mem (Fin.last (m+1)).castSucc r.castSucc.castSucc.castSucc).imp
      ((field w.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))).imp
        (.mem (Fin.last (m+2)) (Fin.last m).castSucc.castSucc))))))

def matrix : Formula 2 := property 0 1

theorem property_rename {m k} (w r : Fin m) (s : Fin m → Fin k) : (property w r).rename s = property (s w) (s r) := by
  simp only [property, Formula.rename, hasLength_rename, field_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = property (ρ 0) x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 2) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 1).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 2) = x := by
    change Fin.lastCases x ρ (Fin.last 1) = x
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, matrix, property_rename, h0, h1]

theorem at_field {m} {Γ : Context m} (w r n i y : Fin m) (hp : Derives Γ (property w r))
    (hl : Derives Γ (hasLength w n r)) (hi : Derives Γ (.mem i r)) (hy : Derives Γ (field w n i y)) : Derives Γ (.mem y n) := by
  have h : Derives Γ ((hasLength w n r).imp ((Formula.mem i r).imp ((field w n i y).imp (.mem y n)))) := by
    simpa only [property, Formula.instantiate, Formula.rename, hasLength_rename, field_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE y (Derives.allE i (Derives.allE n hp))
  exact .impE (.impE (.impE h hl) hi) hy
end PPAC.Migration.Internal.StructuralListFieldBoundsSyntax
