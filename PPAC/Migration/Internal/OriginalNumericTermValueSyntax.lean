import PPAC.Migration.Internal.ObjectTypedArgumentList
import PPAC.Migration.Internal.TermTransformProgramValue

/-! 原Run₁实际有类型唯一输出纤维；执行仍为未改写的原完整规则表。 -/
namespace PPAC.Migration.Internal.OriginalNumericTermValueSyntax
open Source SourceAlgebra SourceLogic

def agreement {m} (w mode depth parameter R S n : Fin m) : Formula m := .all
  ((OriginalTransformRowSyntax.run 1 w.castSucc mode.castSucc depth.castSucc parameter.castSucc n.castSucc (Fin.last m)).iff
    (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w.castSucc R.castSucc S.castSucc n.castSucc (Fin.last m)))

def uniqueOutput {m} (w mode depth parameter n q : Fin m) : Formula m := .all
  ((OriginalTransformRowSyntax.run 1 w.castSucc mode.castSucc depth.castSucc parameter.castSucc n.castSucc (Fin.last m)).imp (.equal (Fin.last m) q.castSucc))

def value {m} (w mode depth parameter c d n q : Fin m) : Formula m :=
  (OriginalTransformRowSyntax.run 1 w mode depth parameter n q).conj
    ((SyntaxTermSyntax.term w c d q).conj ((Formula.mem q w).conj (uniqueOutput w mode depth parameter n q)))

def fiber {m} (w mode depth parameter c d n : Fin m) : Formula m := .ex
  (value w.castSucc mode.castSucc depth.castSucc parameter.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m))

def promise {m} (w mode depth parameter a b c d : Fin m) : Formula m := .all
  ((SyntaxTermSyntax.term w.castSucc a.castSucc b.castSucc (Fin.last m)).imp
    (fiber w.castSucc mode.castSucc depth.castSucc parameter.castSucc c.castSucc d.castSucc (Fin.last m)))

theorem agreement_rename {m k} (w mode depth parameter R S n : Fin m) (ρ : Fin m → Fin k) :
    (agreement w mode depth parameter R S n).rename ρ = agreement (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ R) (ρ S) (ρ n) := by
  simp only [agreement, Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, TermTransformProgramSyntax.run_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueOutput_rename {m k} (w mode depth parameter n q : Fin m) (ρ : Fin m → Fin k) :
    (uniqueOutput w mode depth parameter n q).rename ρ = uniqueOutput (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ n) (ρ q) := by
  simp only [uniqueOutput, Formula.rename, OriginalTransformRowSyntax.run_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem value_rename {m k} (w mode depth parameter c d n q : Fin m) (ρ : Fin m → Fin k) :
    (value w mode depth parameter c d n q).rename ρ = value (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [value, Formula.rename, OriginalTransformRowSyntax.run_rename, SyntaxTermSyntax.term_rename, uniqueOutput_rename]

theorem fiber_rename {m k} (w mode depth parameter c d n : Fin m) (ρ : Fin m → Fin k) :
    (fiber w mode depth parameter c d n).rename ρ = fiber (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ c) (ρ d) (ρ n) := by
  simp only [fiber, Formula.rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem promise_rename {m k} (w mode depth parameter a b c d : Fin m) (ρ : Fin m → Fin k) :
    (promise w mode depth parameter a b c d).rename ρ = promise (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ a) (ρ b) (ρ c) (ρ d) := by
  simp only [promise, Formula.rename, SyntaxTermSyntax.term_rename, fiber_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem promise_at {m} {Γ : Context m} (w mode depth parameter a b c d n : Fin m)
    (hp : Derives Γ (promise w mode depth parameter a b c d))
    (ht : Derives Γ (SyntaxTermSyntax.term w a b n)) : Derives Γ (fiber w mode depth parameter c d n) := by
  have h := Derives.allE n hp
  have hi : Derives Γ ((SyntaxTermSyntax.term w a b n).imp (fiber w mode depth parameter c d n)) :=
    SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, Formula.rename, SyntaxTermSyntax.term_rename, fiber_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) h
  exact .impE hi ht

theorem agreement_at {m} {Γ : Context m} (w mode depth parameter R S n q : Fin m)
    (ha : Derives Γ (agreement w mode depth parameter R S n)) :
    Derives Γ ((OriginalTransformRowSyntax.run 1 w mode depth parameter n q).iff (TermTransformProgramSyntax.run TermTransformProgramSyntax.termProgram w R S n q)) :=
  SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, Formula.iff, Formula.rename, OriginalTransformRowSyntax.run_rename, TermTransformProgramSyntax.run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.allE q ha)

theorem intro_fiber {m} {Γ : Context m} (w mode depth parameter c d n q : Fin m)
    (hq : Derives Γ (value w mode depth parameter c d n q)) : Derives Γ (fiber w mode depth parameter c d n) := by
  apply Derives.exI q
  exact SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hq

theorem run_of_value {m} {Γ : Context m} (w mode depth parameter c d n q : Fin m)
    (hv : Derives Γ (value w mode depth parameter c d n q)) : Derives Γ (OriginalTransformRowSyntax.run 1 w mode depth parameter n q) := .conjL hv

theorem target_type {m} {Γ : Context m} (w mode depth parameter c d n q : Fin m)
    (hv : Derives Γ (value w mode depth parameter c d n q)) : Derives Γ (SyntaxTermSyntax.term w c d q) := .conjL (.conjR hv)

theorem output_natural {m} {Γ : Context m} (w mode depth parameter c d n q : Fin m)
    (hv : Derives Γ (value w mode depth parameter c d n q)) : Derives Γ (.mem q w) := .conjL (.conjR (.conjR hv))

theorem unique {m} {Γ : Context m} (w mode depth parameter c d n q v : Fin m)
    (hv : Derives Γ (value w mode depth parameter c d n q))
    (hr : Derives Γ (OriginalTransformRowSyntax.run 1 w mode depth parameter n v)) : Derives Γ (.equal v q) := by
  have hi := Derives.allE v (.conjR (.conjR (.conjR hv)))
  have hi1 : Derives Γ ((OriginalTransformRowSyntax.run 1 w mode depth parameter n v).imp (.equal v q)) :=
    SyntaxRenameQuerySyntax.of_eq (by simp only [Formula.instantiate, Formula.rename, OriginalTransformRowSyntax.run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hi
  exact .impE hi1 hr

end PPAC.Migration.Internal.OriginalNumericTermValueSyntax
