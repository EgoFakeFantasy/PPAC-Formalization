import PPAC.Migration.Internal.OriginalFreeWeaken

/-! 原mode0自由变量的成功图：实际原行与完整原闭轨迹，不以后继值规格为定义。 -/
namespace PPAC.Migration.Internal.FreeWeakenResultSyntax
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

theorem five_map {m k} (a b c d e : Fin m) (ρ : Fin m → Fin k) :
    (fun i => ρ (HornRowFields.five a b c d e i)) = HornRowFields.five (ρ a) (ρ b) (ρ c) (ρ d) (ρ e) := by
  funext i
  refine Fin.cases rfl (fun j => Fin.cases rfl (fun l => Fin.cases rfl (fun t => Fin.cases rfl (fun _ => rfl) t) l) j) i

def root {m} (w d p x y r : Fin m) : Formula m := .ex
  ((SyntaxNumeralSyntax.numeral 0 (Fin.last m)).conj
    (SyntaxNodeSyntax.constructor 5 1 w.castSucc (HornRowFields.five (Fin.last m) d.castSucc p.castSucc x.castSucc y.castSucc) r.castSucc))

def existsRoot {m} (w d p x y : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (root w.castSucc d.castSucc p.castSucc x.castSucc y.castSucc (Fin.last m)))

def run {m} (w d p x y : Fin m) : Formula m := .ex
  ((root w.castSucc d.castSucc p.castSucc x.castSucc y.castSucc (Fin.last m)).conj (HornLookupConditionSyntax.condition w.castSucc (Fin.last m)))

def returned {m} (w d p x idx y : Fin m) : Formula m :=
  (SyntaxVariableSyntax.code false w idx x).conj (run w d p x y)

def guard {m} (w d p x idx : Fin m) : Formula m :=
  (Formula.mem d w).conj ((Formula.mem p w).conj (SyntaxVariableSyntax.code false w idx x))

def hasOutput {m} (w d p x idx : Fin m) : Formula m := .ex
  (returned w.castSucc d.castSucc p.castSucc x.castSucc idx.castSucc (Fin.last m))

def noOutput {m} (w d p x idx : Fin m) : Formula m := (hasOutput w d p x idx).neg

theorem root_rename {m k} (w d p x y r : Fin m) (ρ : Fin m → Fin k) :
    (root w d p x y r).rename ρ = root (ρ w) (ρ d) (ρ p) (ρ x) (ρ y) (ρ r) := by
  simp only [root, Formula.rename, SyntaxNumeralSyntax.numeral_rename, SyntaxNodeSyntax.constructor_rename, five_map,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsRoot_rename {m k} (w d p x y : Fin m) (ρ : Fin m → Fin k) :
    (existsRoot w d p x y).rename ρ = existsRoot (ρ w) (ρ d) (ρ p) (ρ x) (ρ y) := by
  simp only [existsRoot, Formula.rename, root_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem run_rename {m k} (w d p x y : Fin m) (ρ : Fin m → Fin k) :
    (run w d p x y).rename ρ = run (ρ w) (ρ d) (ρ p) (ρ x) (ρ y) := by
  simp only [run, Formula.rename, root_rename, HornLookupConditionSyntax.condition_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem returned_rename {m k} (w d p x idx y : Fin m) (ρ : Fin m → Fin k) :
    (returned w d p x idx y).rename ρ = returned (ρ w) (ρ d) (ρ p) (ρ x) (ρ idx) (ρ y) := by
  simp only [returned, Formula.rename, SyntaxVariableSyntax.code_rename, run_rename]

theorem guard_rename {m k} (w d p x idx : Fin m) (ρ : Fin m → Fin k) :
    (guard w d p x idx).rename ρ = guard (ρ w) (ρ d) (ρ p) (ρ x) (ρ idx) := by
  simp only [guard, Formula.rename, SyntaxVariableSyntax.code_rename]

theorem hasOutput_rename {m k} (w d p x idx : Fin m) (ρ : Fin m → Fin k) :
    (hasOutput w d p x idx).rename ρ = hasOutput (ρ w) (ρ d) (ρ p) (ρ x) (ρ idx) := by
  simp only [hasOutput, Formula.rename, returned_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem noOutput_rename {m k} (w d p x idx : Fin m) (ρ : Fin m → Fin k) :
    (noOutput w d p x idx).rename ρ = noOutput (ρ w) (ρ d) (ρ p) (ρ x) (ρ idx) := by
  simp only [noOutput, Formula.neg, Formula.rename, hasOutput_rename]

theorem intro_root {m} {Γ : Context m} (w d p x y r mode : Fin m)
    (hm : Derives Γ (SyntaxNumeralSyntax.numeral 0 mode))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor 5 1 w (HornRowFields.five mode d p x y) r)) : Derives Γ (root w d p x y r) := by
  apply Derives.exI mode
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxNumeralSyntax.numeral_rename, SyntaxNodeSyntax.constructor_rename, five_map, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hm hc)

theorem intro_run {m} {Γ : Context m} (w d p x y r : Fin m) (hr : Derives Γ (root w d p x y r))
    (ht : Derives Γ (HornLookupConditionSyntax.condition w r)) : Derives Γ (run w d p x y) := by
  apply Derives.exI r
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, root_rename, HornLookupConditionSyntax.condition_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hr ht)

end PPAC.Migration.Internal.FreeWeakenResultSyntax
