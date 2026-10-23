import PPAC.Migration.Internal.OriginalRunValueSubstitution

/-! 原参数列表运行的实际唯一有类型输出；长度与输入码均为内部变量。 -/
namespace PPAC.Migration.Internal.OriginalArgumentValueSyntax
open Source SourceAlgebra SourceLogic
open SyntaxRenameQuerySyntax (of_eq)

def uniqueOutput {m} (w mode depth parameter n q : Fin m) : Formula m := .all
  ((OriginalTransformRowSyntax.run 2 w.castSucc mode.castSucc depth.castSucc parameter.castSucc n.castSucc (Fin.last m)).imp (.equal (Fin.last m) q.castSucc))

def value {m} (w mode depth parameter k c d n q : Fin m) : Formula m :=
  (OriginalTransformRowSyntax.run 2 w mode depth parameter n q).conj
    ((SyntaxMixedImageCodeSyntax.termList w k c d q).conj (uniqueOutput w mode depth parameter n q))

def fiber {m} (w mode depth parameter k c d n : Fin m) : Formula m := .ex
  (value w.castSucc mode.castSucc depth.castSucc parameter.castSucc k.castSucc c.castSucc d.castSucc n.castSucc (Fin.last m))

def property {m} (w mode depth parameter a b c d n : Fin m) : Formula m := .all
  ((SyntaxMixedImageCodeSyntax.termList w.castSucc (Fin.last m) a.castSucc b.castSucc n.castSucc).imp
    (fiber w.castSucc mode.castSucc depth.castSucc parameter.castSucc (Fin.last m) c.castSucc d.castSucc n.castSucc))

def earlier {m} (w mode depth parameter a b c d n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((Formula.mem (Fin.last m) n.castSucc).imp
    (property w.castSucc mode.castSucc depth.castSucc parameter.castSucc a.castSucc b.castSucc c.castSucc d.castSucc (Fin.last m))))

theorem uniqueOutput_rename {m j} (w mode depth parameter n q : Fin m) (ρ : Fin m → Fin j) :
    (uniqueOutput w mode depth parameter n q).rename ρ = uniqueOutput (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ n) (ρ q) := by
  simp only [uniqueOutput, Formula.rename, OriginalTransformRowSyntax.run_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem value_rename {m j} (w mode depth parameter k c d n q : Fin m) (ρ : Fin m → Fin j) :
    (value w mode depth parameter k c d n q).rename ρ = value (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ k) (ρ c) (ρ d) (ρ n) (ρ q) := by
  simp only [value, Formula.rename, OriginalTransformRowSyntax.run_rename, SyntaxMixedImageCodeSyntax.termList_rename, uniqueOutput_rename]

theorem fiber_rename {m j} (w mode depth parameter k c d n : Fin m) (ρ : Fin m → Fin j) :
    (fiber w mode depth parameter k c d n).rename ρ = fiber (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ k) (ρ c) (ρ d) (ρ n) := by
  simp only [fiber, Formula.rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem property_rename {m j} (w mode depth parameter a b c d n : Fin m) (ρ : Fin m → Fin j) :
    (property w mode depth parameter a b c d n).rename ρ = property (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) := by
  simp only [property, Formula.rename, SyntaxMixedImageCodeSyntax.termList_rename, fiber_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem earlier_rename {m j} (w mode depth parameter a b c d n : Fin m) (ρ : Fin m → Fin j) :
    (earlier w mode depth parameter a b c d n).rename ρ = earlier (ρ w) (ρ mode) (ρ depth) (ρ parameter) (ρ a) (ρ b) (ρ c) (ρ d) (ρ n) := by
  simp only [earlier, Formula.rename, property_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_fiber {m} {Γ : Context m} (w mode depth parameter k c d n q : Fin m)
    (hv : Derives Γ (value w mode depth parameter k c d n q)) : Derives Γ (fiber w mode depth parameter k c d n) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hv

theorem target_type {m} {Γ : Context m} (w mode depth parameter k c d n q : Fin m)
    (hv : Derives Γ (value w mode depth parameter k c d n q)) : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k c d q) := .conjL (.conjR hv)

theorem output_natural {m} {Γ : Context m} (w mode depth parameter k c d n q : Fin m)
    (hv : Derives Γ (value w mode depth parameter k c d n q)) : Derives Γ (.mem q w) := .conjL (.conjL (.conjR (.conjR (target_type _ _ _ _ _ _ _ _ _ hv))))

theorem unique {m} {Γ : Context m} (w mode depth parameter k c d n q v : Fin m)
    (hv : Derives Γ (value w mode depth parameter k c d n q)) (hr : Derives Γ (OriginalTransformRowSyntax.run 2 w mode depth parameter n v)) : Derives Γ (.equal v q) := by
  have hi := Derives.allE v (.conjR (.conjR hv))
  have hi1 : Derives Γ ((OriginalTransformRowSyntax.run 2 w mode depth parameter n v).imp (.equal v q)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, OriginalTransformRowSyntax.run_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hi
  exact .impE hi1 hr

theorem property_at {m} {Γ : Context m} (w mode depth parameter a b c d n k : Fin m)
    (hp : Derives Γ (property w mode depth parameter a b c d n)) (hL : Derives Γ (SyntaxMixedImageCodeSyntax.termList w k a b n)) : Derives Γ (fiber w mode depth parameter k c d n) := by
  have hi : Derives Γ ((SyntaxMixedImageCodeSyntax.termList w k a b n).imp (fiber w mode depth parameter k c d n)) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, SyntaxMixedImageCodeSyntax.termList_rename, fiber_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE k hp)
  exact .impE hi hL

theorem earlier_at {m} {Γ : Context m} (w mode depth parameter a b c d n t : Fin m)
    (he : Derives Γ (earlier w mode depth parameter a b c d n)) (ht : Derives Γ (.mem t w)) (htn : Derives Γ (.mem t n)) : Derives Γ (property w mode depth parameter a b c d t) := by
  have hi : Derives Γ ((Formula.mem t w).imp ((Formula.mem t n).imp (property w mode depth parameter a b c d t))) := of_eq
    (by simp only [Formula.instantiate, Formula.rename, property_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (Derives.allE t he)
  exact .impE (.impE hi ht) htn

end PPAC.Migration.Internal.OriginalArgumentValueSyntax
