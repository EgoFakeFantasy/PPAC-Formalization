import PPAC.Migration.Internal.NaturalMultiplicationCommutative

/-! 结合律固定实际a*b=u，比较所有内部第三参数的真实乘积。 -/
namespace PPAC.Migration.Internal.NaturalMultiplicationAssociativeSyntax
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax ReplacementPredicates NaturalMultiplicationSyntax NaturalAdditionTransport
attribute [local irreducible] NaturalRecursionSyntax.matrix

def property {m} (w a b u n : Fin m) : Formula m := .all (.all
  ((product w.castSucc.castSucc b.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc).imp
    ((product w.castSucc.castSucc u.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))).imp
      (product w.castSucc.castSucc a.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))
def matrix : Formula 5 := property 0 1 2 3 4

theorem property_rename {m k} (w a b u n : Fin m) (r : Fin m → Fin k) :
    (property w a b u n).rename r = property (r w) (r a) (r b) (r u) (r n) := by
  simp only [property, Formula.rename, product_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 4 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = property (ρ 0) (ρ 1) (ρ 2) (ρ 3) x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 5) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 4).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 5) = ρ 1 := by
    change Fin.lastCases x ρ (1 : Fin 4).castSucc = ρ 1
    exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases x ρ (2 : Fin 5) = ρ 2 := by
    change Fin.lastCases x ρ (2 : Fin 4).castSucc = ρ 2
    exact Fin.lastCases_castSucc _
  have h3 : Fin.lastCases x ρ (3 : Fin 5) = ρ 3 := by
    change Fin.lastCases x ρ (3 : Fin 4).castSucc = ρ 3
    exact Fin.lastCases_castSucc _
  have h4 : Fin.lastCases x ρ (4 : Fin 5) = x := by
    change Fin.lastCases x ρ (Fin.last 4) = x
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, matrix, property_rename, h0, h1, h2, h3, h4]

theorem property_at {m} {Γ : Context m} (w a b u n v y : Fin m) (hi : Derives Γ (property w a b u n))
    (hv : Derives Γ (product w b n v)) (hy : Derives Γ (product w u n y)) : Derives Γ (product w a v y) := by
  have hp := Derives.allE y (Derives.allE v hi)
  have h : Derives Γ ((product w b n v).imp ((product w u n y).imp (product w a v y))) := by
    simpa only [property, Formula.instantiate, Formula.rename, product_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp
  exact .impE (.impE h hv) hy

end PPAC.Migration.Internal.NaturalMultiplicationAssociativeSyntax
