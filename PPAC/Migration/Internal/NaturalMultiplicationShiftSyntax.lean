import PPAC.Migration.Internal.NaturalMultiplicationDistributive

/-! b=Succ(a)时，b*n=a*n+n的内部归纳矩阵。 -/
namespace PPAC.Migration.Internal.NaturalMultiplicationShiftSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax NaturalAdditionSyntax
open NaturalMultiplicationSyntax (product product_rename)

def property {m} (w a b n : Fin m) : Formula m := .all (.all
  ((product w.castSucc.castSucc a.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc).imp
    ((sum w.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
      (product w.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))))))
def matrix : Formula 4 := property 0 1 2 3

theorem property_rename {m k} (w a b n : Fin m) (r : Fin m → Fin k) :
    (property w a b n).rename r = property (r w) (r a) (r b) (r n) := by
  simp only [property, Formula.rename, product_rename, sum_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 3 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = property (ρ 0) (ρ 1) (ρ 2) x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 4) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 3).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 4) = ρ 1 := by
    change Fin.lastCases x ρ (1 : Fin 3).castSucc = ρ 1
    exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases x ρ (2 : Fin 4) = ρ 2 := by
    change Fin.lastCases x ρ (2 : Fin 3).castSucc = ρ 2
    exact Fin.lastCases_castSucc _
  have h3 : Fin.lastCases x ρ (3 : Fin 4) = x := by
    change Fin.lastCases x ρ (Fin.last 3) = x
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, matrix, property_rename, h0, h1, h2, h3]

theorem property_at {m} {Γ : Context m} (w a b n p r : Fin m) (hi : Derives Γ (property w a b n))
    (hp : Derives Γ (product w a n p)) (hr : Derives Γ (sum w p n r)) : Derives Γ (product w b n r) := by
  have hp' := Derives.allE r (Derives.allE p hi)
  have h : Derives Γ ((product w a n p).imp ((sum w p n r).imp (product w b n r))) := by
    simpa only [property, Formula.instantiate, Formula.rename, product_rename, sum_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp'
  exact .impE (.impE h hp) hr
end PPAC.Migration.Internal.NaturalMultiplicationShiftSyntax
