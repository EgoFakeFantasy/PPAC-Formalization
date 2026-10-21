import PPAC.Migration.Internal.StructuralListShift

/-! 原构造迹长度与实际tail递归终端的纯公式合同。 -/
namespace PPAC.Migration.Internal.StructuralListEndSyntax
open Source SourceAlgebra SourceLogic StructuralListProjectionSyntax StructuralListLengthSyntax

def ends {m} (w n : Fin m) : Formula m := .all (.all
  ((hasLength w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc).imp
    ((iteration false w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
      (StructuralListSyntax.nilCode w.castSucc.castSucc (Fin.last (m+1))))))

def matrix : Formula 2 := ends 0 1

def earlier {m} (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp (ends w.castSucc (Fin.last m))))

def terminalWitness {m} (w n : Fin m) : Formula (m+2) :=
  (((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj (hasLength w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc)).conj
    (iteration false w.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))).conj
      (StructuralListSyntax.nilCode w.castSucc.castSucc (Fin.last (m+1)))

def existsTerminal {m} (w n : Fin m) : Formula m := .ex (.ex (terminalWitness w n))

theorem ends_rename {m k} (w n : Fin m) (s : Fin m → Fin k) : (ends w n).rename s = ends (s w) (s n) := by
  simp only [ends, Formula.rename, hasLength_rename, iteration_rename, StructuralListSyntax.nilCode_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem earlier_rename {m k} (w n : Fin m) (s : Fin m → Fin k) : (earlier w n).rename s = earlier (s w) (s n) := by
  simp only [earlier, Formula.rename, ends_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsTerminal_rename {m k} (w n : Fin m) (s : Fin m → Fin k) :
    (existsTerminal w n).rename s = existsTerminal (s w) (s n) := by
  simp only [existsTerminal, terminalWitness, Formula.rename, hasLength_rename, iteration_rename, StructuralListSyntax.nilCode_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 1 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = ends (ρ 0) x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 2) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 1).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 2) = x := by
    change Fin.lastCases x ρ (Fin.last 1) = x
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, matrix, ends_rename, h0, h1]

theorem at_values {m} {Γ : Context m} (w n l y : Fin m) (he : Derives Γ (ends w n))
    (hl : Derives Γ (hasLength w n l)) (hy : Derives Γ (iteration false w n l y)) : Derives Γ (StructuralListSyntax.nilCode w y) := by
  have h : Derives Γ ((hasLength w n l).imp ((iteration false w n l y).imp (StructuralListSyntax.nilCode w y))) := by
    simpa only [ends, Formula.instantiate, Formula.rename, hasLength_rename, iteration_rename, StructuralListSyntax.nilCode_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE y (Derives.allE l he)
  exact .impE (.impE h hl) hy

theorem earlier_at {m} {Γ : Context m} (w n t : Fin m) (he : Derives Γ (earlier w n))
    (ht : Derives Γ (.mem t w)) (hb : Derives Γ (.mem t n)) : Derives Γ (ends w t) := by
  have h : Derives Γ ((Formula.mem t w).imp ((Formula.mem t n).imp (ends w t))) := by
    simpa only [earlier, Formula.instantiate, Formula.rename, ends_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE t he
  exact .impE (.impE h ht) hb

theorem intro_terminal {m} {Γ : Context m} (w n l y : Fin m) (hl : Derives Γ (.mem l w))
    (hL : Derives Γ (hasLength w n l)) (hy : Derives Γ (iteration false w n l y))
    (hn : Derives Γ (StructuralListSyntax.nilCode w y)) : Derives Γ (existsTerminal w n) := by
  apply Derives.exI l
  apply Derives.exI y
  simp only [Formula.instantiate, terminalWitness, Formula.rename, hasLength_rename, iteration_rename, StructuralListSyntax.nilCode_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI (.conjI (.conjI hl hL) hy) hn
end PPAC.Migration.Internal.StructuralListEndSyntax
