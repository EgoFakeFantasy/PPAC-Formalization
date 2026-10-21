import PPAC.Migration.Internal.SyntaxTermTreeValidity

/-! 树有效性的对象成员归纳性质：所有bound/free参数在性质内部全称量化。 -/
namespace PPAC.Migration.Internal.FormulaCodeTreeValiditySyntax
open Source SourceAlgebra SourceLogic FormulaCodeSyntax
open StructuralTreeValiditySyntax (valid valid_rename)
open MinimalPredicates (pred)
open ReplacementPredicates (paramsUp)

def property {m} (w n : Fin m) : Formula m := .all (.all
  ((formulaCode w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
    (valid w.castSucc.castSucc n.castSucc.castSucc)))

def earlier {m} (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp (property w.castSucc (Fin.last m))))

def matrix : Formula 2 := property (0 : Fin 1).castSucc (Fin.last 1)

theorem property_rename {m k} (w n : Fin m) (r : Fin m → Fin k) :
    (property w n).rename r = property (r w) (r n) := by
  simp only [property, Formula.rename, formulaCode_rename, valid_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem earlier_rename {m k} (w n : Fin m) (r : Fin m → Fin k) :
    (earlier w n).rename r = earlier (r w) (r n) := by
  simp only [earlier, Formula.rename, property_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (x : Fin m) : pred matrix ρ x = property (ρ 0) x := by
  simp only [matrix, pred, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem property_at {m} {Γ : Context m} (w n b f : Fin m) (hp : Derives Γ (property w n)) :
    Derives Γ ((formulaCode w n b f).imp (valid w n)) := by
  simpa only [property, Formula.instantiate, Formula.rename, formulaCode_rename, valid_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE f (Derives.allE b hp)

theorem earlier_at {m} {Γ : Context m} (w n x : Fin m) (hi : Derives Γ (earlier w n))
    (hx : Derives Γ (.mem x w)) (hb : Derives Γ (.mem x n)) : Derives Γ (property w x) := by
  have hh : Derives Γ ((Formula.mem x w).imp ((Formula.mem x n).imp (property w x))) := by
    simpa only [earlier, Formula.instantiate, Formula.rename, property_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE x hi
  exact .impE (.impE hh hx) hb

theorem child {m} {Γ : Context m} (w n x b f : Fin m) (hi : Derives Γ (earlier w n))
    (hb : Derives Γ (.mem x n)) (hc : Derives Γ (formulaCode w x b f)) : Derives Γ (valid w x) :=
  .impE (property_at w x b f (earlier_at w n x hi (.conjL (FormulaCodeProperties.guards w x b f hc)) hb)) hc
end PPAC.Migration.Internal.FormulaCodeTreeValiditySyntax
