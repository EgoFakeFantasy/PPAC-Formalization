import PPAC.Migration.Internal.RawCodeIterationTransport

/-! 原get值是任意原始外壳tail求值之后的原head投影；所有中间值保持内部对象见证。 -/
namespace PPAC.Migration.Internal.RawCodeGetSyntax
open Source SourceAlgebra SourceLogic RawCodeProjectionSyntax

def get {m} (w n i y : Fin m) : Formula m := .ex
  ((iteration false w.castSucc n.castSucc i.castSucc (Fin.last m)).conj (step true w.castSucc (Fin.last m) y.castSucc))

def existsGet {m} (w n i : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (get w.castSucc n.castSucc i.castSucc (Fin.last m)))

def fiber {m} (w n i : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (get w.castSucc n.castSucc i.castSucc (Fin.last m))).conj (.all
    ((get w.castSucc.castSucc n.castSucc.castSucc i.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

theorem get_rename {m k} (w n i y : Fin m) (s : Fin m → Fin k) :
    (get w n i y).rename s = get (s w) (s n) (s i) (s y) := by
  simp only [get, Formula.rename, iteration_rename, step_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem existsGet_rename {m k} (w n i : Fin m) (s : Fin m → Fin k) :
    (existsGet w n i).rename s = existsGet (s w) (s n) (s i) := by
  simp only [existsGet, Formula.rename, get_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m k} (w n i : Fin m) (s : Fin m → Fin k) : (fiber w n i).rename s = fiber (s w) (s n) (s i) := by
  simp only [fiber, Formula.rename, get_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_get {m} {Γ : Context m} (w n i y t : Fin m)
    (ht : Derives Γ (iteration false w n i t)) (hy : Derives Γ (step true w t y)) : Derives Γ (get w n i y) := by
  apply Derives.exI t
  simp only [Formula.instantiate, Formula.rename, iteration_rename, step_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI ht hy

theorem intro_exists {m} {Γ : Context m} (w n i y : Fin m) (hy : Derives Γ (.mem y w))
    (hf : Derives Γ (get w n i y)) : Derives Γ (existsGet w n i) := by
  apply Derives.exI y
  simp only [Formula.instantiate, Formula.rename, get_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hy hf

theorem output_subst {m} {Γ : Context m} (w n i y z : Fin m) (he : Derives Γ (.equal y z))
    (hy : Derives Γ (get w n i y)) : Derives Γ (get w n i z) := by
  have hi : Derives Γ ((get w.castSucc n.castSucc i.castSucc (Fin.last m)).instantiate y) := by
    simpa only [Formula.instantiate, get_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy
  have ho := Derives.eqSubst (get w.castSucc n.castSucc i.castSucc (Fin.last m)) he hi
  simpa only [Formula.instantiate, get_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho

theorem index_subst {m} {Γ : Context m} (w n i j y : Fin m) (he : Derives Γ (.equal i j))
    (hy : Derives Γ (get w n i y)) : Derives Γ (get w n j y) := by
  have hi : Derives Γ ((get w.castSucc n.castSucc (Fin.last m) y.castSucc).instantiate i) := by
    simpa only [Formula.instantiate, get_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hy
  have ho := Derives.eqSubst (get w.castSucc n.castSucc (Fin.last m) y.castSucc) he hi
  simpa only [Formula.instantiate, get_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using ho
end PPAC.Migration.Internal.RawCodeGetSyntax
