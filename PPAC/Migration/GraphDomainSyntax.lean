import PPAC.Migration.InsertLogic
import PPAC.Migration.MinimalInstances

/-! 任意集合图的实际对象定义域与分离矩阵。 -/
namespace PPAC.Migration.GraphDomainSyntax
open Source SourceAlgebra GraphSyntax

def domain {m} (d g : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) d.castSucc).iff (hasEdge g.castSucc (Fin.last m)))

def domainExists {m} (g : Fin m) : Formula m := .ex (domain (Fin.last m) g.castSucc)

def separated {m} (d v g : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) d.castSucc).iff
    ((Formula.mem (Fin.last m) v.castSucc).conj (hasEdge g.castSucc (Fin.last m))))

def matrix : Formula 2 := hasEdge 0 1

theorem domain_rename {m k} (d g : Fin m) (r : Fin m → Fin k) :
    (domain d g).rename r = domain (r d) (r g) := by
  simp only [domain, Formula.iff, Formula.rename, hasEdge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem domainExists_rename {m k} (g : Fin m) (r : Fin m → Fin k) :
    (domainExists g).rename r = domainExists (r g) := by
  simp only [domainExists, Formula.rename, domain_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem separated_rename {m k} (d v g : Fin m) (r : Fin m → Fin k) :
    (separated d v g).rename r = separated (r d) (r v) (r g) := by
  simp only [separated, Formula.iff, Formula.rename, hasEdge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem domain_at {m} {Γ : Context m} (d g x : Fin m) (h : Derives Γ (domain d g)) :
    Derives Γ ((Formula.mem x d).iff (hasEdge g x)) := by
  have hi := Derives.allE x h
  simpa only [Formula.instantiate, Formula.rename, hasEdge_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem separated_at {m} {Γ : Context m} (d v g x : Fin m) (h : Derives Γ (separated d v g)) :
    Derives Γ ((Formula.mem x d).iff ((Formula.mem x v).conj (hasEdge g x))) := by
  have hi := Derives.allE x h
  simpa only [Formula.instantiate, Formula.rename, hasEdge_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (x : Fin m) :
    MinimalPredicates.pred matrix ρ x = hasEdge (ρ 0) x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 2) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 1).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 2) = x := by
    change Fin.lastCases x ρ (Fin.last 1) = x
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, matrix, hasEdge_rename, h0, h1]

theorem separate_domain {m} {Γ : Context m} (v g : Fin m)
    (hs : Derives Γ ((Source.SetLanguage.separation matrix).rename Fin.elim0)) :
    Derives Γ (.ex (separated (Fin.last m) v.castSucc g.castSucc)) := by
  have hi := MinimalInstances.separation_instance matrix (fun _ : Fin 1 => g) v hs
  simpa only [MinimalPredicates.separationExists, MinimalPredicates.separated, MinimalPredicates.satisfying,
    matrix_pred, separated] using hi
end PPAC.Migration.GraphDomainSyntax
