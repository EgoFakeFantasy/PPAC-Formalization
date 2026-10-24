import PPAC.Migration.Internal.ProofTreeNodeBackward
import PPAC.Migration.SetInduction

/-! 内部证明树归纳的显式二元对象性质模式；局部闭包条件为对象公式，非宿主判定。 -/
namespace PPAC.Migration.Internal.ProofTreeInductionSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ProofTreeBranchConstruction (shape)

def property {m} (P : Formula 2) (w code : Fin m) : Formula m := P.rename (SetLanguage.args2 w code)

def children {m a} (P : Formula 2) : List (Fin a) → Fin m → (Fin a → Fin m) → Formula m
  | .nil, _, _ => HornRuleSyntax.truth
  | .cons i is, w, env => (property P w (env i)).conj (children P is w env)

def matrix {m} (P : Formula 2) (kind : Fin 6) (w code : Fin m) (env : Fin ((shape kind).extra+2) → Fin m) : Formula m :=
  (environmentNat ((shape kind).extra+2) w env).conj
    ((SyntaxNodeSyntax.constructor ((shape kind).extra+2) (shape kind).tag w env code).conj
      (children P (shape kind).children w env))

def body {m} (P : Formula 2) (kind : Fin 6) (w code : Fin m) : Formula (m+((shape kind).extra+2)) :=
  matrix P kind (old ((shape kind).extra+2) w) (old ((shape kind).extra+2) code) (slot ((shape kind).extra+2))

def branch {m} (P : Formula 2) (kind : Fin 6) (w code : Fin m) : Formula m :=
  existsMany ((shape kind).extra+2) (body P kind w code)

def cases {m} (P : Formula 2) (w code : Fin m) : Formula m :=
  LogicalAllPatterns.disjoin (ProofTreeRootSyntax.kinds.map (fun kind => branch P kind w code))

def normalized {m} (test : Formula 1) (P : Formula 2) (w code : Fin m) : Formula m :=
  (ProofAllNodeSyntax.table test w code).conj (cases P w code)

def closure {m} (test : Formula 1) (P : Formula 2) (w : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp
    ((normalized test P w.castSucc (Fin.last m)).imp (property P w.castSucc (Fin.last m))))

def correct {m} (test : Formula 1) (P : Formula 2) (w code : Fin m) : Formula m :=
  (ProofTreeEntrySyntax.node test w code).imp (property P w code)

def allIH {m} (test : Formula 1) (P : Formula 2) (w code : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) code.castSucc).imp (correct test P w.castSucc (Fin.last m)))

theorem property_rename {m l} (P : Formula 2) (w code : Fin m) (ρ : Fin m → Fin l) :
    (property P w code).rename ρ = property P (ρ w) (ρ code) := by
  simp only [property, rename_comp, ProofTreeEntryFacts.args2_map]

theorem children_rename {m a l} (P : Formula 2) (is : List (Fin a)) (w : Fin m) (env : Fin a → Fin m) (ρ : Fin m → Fin l) :
    (children P is w env).rename ρ = children P is (ρ w) (fun i => ρ (env i)) := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [children, Formula.rename, property_rename, ih]

theorem matrix_rename {m l} (P : Formula 2) (kind : Fin 6) (w code : Fin m) (env : Fin ((shape kind).extra+2) → Fin m) (ρ : Fin m → Fin l) :
    (matrix P kind w code env).rename ρ = matrix P kind (ρ w) (ρ code) (fun i => ρ (env i)) := by
  simp only [matrix, Formula.rename, environmentNat_rename, SyntaxNodeSyntax.constructor_rename, children_rename]

theorem body_lift {m l} (P : Formula 2) (kind : Fin 6) (w code : Fin m) (ρ : Fin m → Fin l) :
    (body P kind w code).rename (lift ((shape kind).extra+2) ρ) = body P kind (ρ w) (ρ code) := by
  simp only [body, matrix_rename, lift_old, lift_slot]

theorem branch_rename {m l} (P : Formula 2) (kind : Fin 6) (w code : Fin m) (ρ : Fin m → Fin l) :
    (branch P kind w code).rename ρ = branch P kind (ρ w) (ρ code) := by
  simp only [branch, existsMany_rename, body_lift]

theorem cases_rename {m l} (P : Formula 2) (w code : Fin m) (ρ : Fin m → Fin l) :
    (cases P w code).rename ρ = cases P (ρ w) (ρ code) := by
  unfold cases
  rw [LogicalTableRenaming.disjoin_rename, List.map_map]
  congr 1
  apply List.map_congr_left
  intro kind _
  exact branch_rename P kind w code ρ

theorem normalized_rename {m l} (test : Formula 1) (P : Formula 2) (w code : Fin m) (ρ : Fin m → Fin l) :
    (normalized test P w code).rename ρ = normalized test P (ρ w) (ρ code) := by
  simp only [normalized, Formula.rename, ProofAllTableRenaming.table_rename, cases_rename]

theorem closure_rename {m l} (test : Formula 1) (P : Formula 2) (w : Fin m) (ρ : Fin m → Fin l) :
    (closure test P w).rename ρ = closure test P (ρ w) := by
  simp only [closure, Formula.rename, normalized_rename, property_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem correct_rename {m l} (test : Formula 1) (P : Formula 2) (w code : Fin m) (ρ : Fin m → Fin l) :
    (correct test P w code).rename ρ = correct test P (ρ w) (ρ code) := by
  simp only [correct, Formula.rename, ProofTreeEntryFacts.node_rename, property_rename]

theorem allIH_rename {m l} (test : Formula 1) (P : Formula 2) (w code : Fin m) (ρ : Fin m → Fin l) :
    (allIH test P w code).rename ρ = allIH test P (ρ w) (ρ code) := by
  simp only [allIH, Formula.rename, correct_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

end PPAC.Migration.Internal.ProofTreeInductionSyntax
