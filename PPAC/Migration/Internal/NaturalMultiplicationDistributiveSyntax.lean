import PPAC.Migration.Internal.NaturalAdditionReassociation

/-! 固定实际a*b=p，在内部n上归纳a*(b+n)=p+a*n。 -/
namespace PPAC.Migration.Internal.NaturalMultiplicationDistributiveSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax NaturalAdditionSyntax
open NaturalMultiplicationSyntax (product product_rename)

def property {m} (w a b p n : Fin m) : Formula m := .all (.all (.all
  ((sum w.castSucc.castSucc.castSucc b.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc).imp
    ((product w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc).imp
      ((sum w.castSucc.castSucc.castSucc p.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))).imp
        (product w.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))))))))
def matrix : Formula 5 := property 0 1 2 3 4

theorem property_rename {m k} (w a b p n : Fin m) (r : Fin m → Fin k) :
    (property w a b p n).rename r = property (r w) (r a) (r b) (r p) (r n) := by
  simp only [property, Formula.rename, sum_rename, product_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

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

theorem property_at {m} {Γ : Context m} (w a b p n d q r : Fin m) (hi : Derives Γ (property w a b p n))
    (hd : Derives Γ (sum w b n d)) (hq : Derives Γ (product w a n q)) (hr : Derives Γ (sum w p q r)) : Derives Γ (product w a d r) := by
  have hp := Derives.allE r (Derives.allE q (Derives.allE d hi))
  have h : Derives Γ ((sum w b n d).imp ((product w a n q).imp ((sum w p q r).imp (product w a d r)))) := by
    simpa only [property, Formula.instantiate, Formula.rename, sum_rename, product_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hp
  exact .impE (.impE (.impE h hd) hq) hr
end PPAC.Migration.Internal.NaturalMultiplicationDistributiveSyntax
