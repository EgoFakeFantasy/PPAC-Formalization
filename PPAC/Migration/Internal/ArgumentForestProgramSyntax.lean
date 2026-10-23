import PPAC.Migration.Internal.ObjectOriginalMemberApplication

/-! 固定有限原子参数向量的类型及独立项程序逐字段关系；运行值均为对象变量。 -/
namespace PPAC.Migration.Internal.ArgumentForestProgramSyntax
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

def typedInputs {m} : (k : Nat) → Fin m → Fin m → Fin m → (Fin k → Fin m) → Formula m
  | 0, w, _, _, _ => .equal w w
  | k+1, w, a, b, xs => (SyntaxTermSyntax.term w a b (xs 0)).conj (typedInputs k w a b (fun i => xs i.succ))

def runs {m} : (k : Nat) → Fin m → Fin m → Fin m → (Fin k → Fin m) → (Fin k → Fin m) → Formula m
  | 0, w, _, _, _, _ => .equal w w
  | k+1, w, R, S, xs, ys => (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S (xs 0) (ys 0)).conj
    (runs k w R S (fun i => xs i.succ) (fun i => ys i.succ))

theorem typedInputs_rename {m j} (k : Nat) (w a b : Fin m) (xs : Fin k → Fin m) (ρ : Fin m → Fin j) :
    (typedInputs k w a b xs).rename ρ = typedInputs k (ρ w) (ρ a) (ρ b) (fun i => ρ (xs i)) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [typedInputs, Formula.rename, SyntaxTermSyntax.term_rename, ih]

theorem runs_rename {m j} (k : Nat) (w R S : Fin m) (xs ys : Fin k → Fin m) (ρ : Fin m → Fin j) :
    (runs k w R S xs ys).rename ρ = runs k (ρ w) (ρ R) (ρ S) (fun i => ρ (xs i)) (fun i => ρ (ys i)) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [runs, Formula.rename, TermTransformProgramSyntax.run_rename, ih]

theorem typed_at {m} {Γ : Context m} (k : Nat) (w a b : Fin m) (xs : Fin k → Fin m)
    (hh : Derives Γ (typedInputs k w a b xs)) (i : Fin k) : Derives Γ (SyntaxTermSyntax.term w a b (xs i)) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih => exact Fin.cases (.conjL hh) (fun j => ih (fun i => xs i.succ) (.conjR hh) j) i

theorem intro_typed {m} {Γ : Context m} (k : Nat) (w a b : Fin m) (xs : Fin k → Fin m)
    (hh : ∀ i, Derives Γ (SyntaxTermSyntax.term w a b (xs i))) : Derives Γ (typedInputs k w a b xs) := by
  induction k with
  | zero => exact .eqRefl w
  | succ k ih => exact .conjI (hh 0) (ih (fun i => xs i.succ) (fun i => hh i.succ))

theorem run_at {m} {Γ : Context m} (k : Nat) (w R S : Fin m) (xs ys : Fin k → Fin m)
    (hh : Derives Γ (runs k w R S xs ys)) (i : Fin k) : Derives Γ (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S (xs i) (ys i)) := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih => exact Fin.cases (.conjL hh) (fun j => ih (fun i => xs i.succ) (fun i => ys i.succ) (.conjR hh) j) i

theorem intro_runs {m} {Γ : Context m} (k : Nat) (w R S : Fin m) (xs ys : Fin k → Fin m)
    (hh : ∀ i, Derives Γ (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S (xs i) (ys i))) : Derives Γ (runs k w R S xs ys) := by
  induction k with
  | zero => exact .eqRefl w
  | succ k ih => exact .conjI (hh 0) (ih (fun i => xs i.succ) (fun i => ys i.succ) (fun i => hh i.succ))

theorem run_input_subst {m} {Γ : Context m} (w R S x X y : Fin m) (he : Derives Γ (.equal x X))
    (hr : Derives Γ (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S x y)) :
    Derives Γ (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S X y) := by
  let P := TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w.castSucc R.castSucc S.castSucc (Fin.last m) y.castSucc
  exact of_eq (by simp only [P, Formula.instantiate, TermTransformProgramSyntax.run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, TermTransformProgramSyntax.run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hr))

theorem run_output_subst {m} {Γ : Context m} (w R S x y Y : Fin m) (he : Derives Γ (.equal y Y))
    (hr : Derives Γ (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S x y)) :
    Derives Γ (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S x Y) := by
  let P := TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w.castSucc R.castSucc S.castSucc x.castSucc (Fin.last m)
  exact of_eq (by simp only [P, Formula.instantiate, TermTransformProgramSyntax.run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, TermTransformProgramSyntax.run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hr))

end PPAC.Migration.Internal.ArgumentForestProgramSyntax
