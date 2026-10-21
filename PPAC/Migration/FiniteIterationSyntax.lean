import PPAC.Migration.ObjectIterationUniqueness
import PPAC.Migration.ObjectGraphInsert

/-! 每个内部长度n的有限轨迹，实际域为n的后继；存在量词仍在对象层。 -/
namespace PPAC.Migration.FiniteIterationSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax IterationSyntax

def witness {m} (f d n z a : Fin m) : Formula m := (successor d n).conj (track f d z a)

def existsTrack {m} (n z a : Fin m) : Formula m := .ex (.ex
  (witness (Fin.last (m+1)) (Fin.last m).castSucc n.castSucc.castSucc z.castSucc.castSucc a.castSucc.castSucc))

theorem witness_rename {m k} (f d n z a : Fin m) (r : Fin m → Fin k) :
    (witness f d n z a).rename r = witness (r f) (r d) (r n) (r z) (r a) := by
  simp only [witness, Formula.rename, successor_rename, track_rename]

theorem existsTrack_rename {m k} (n z a : Fin m) (r : Fin m → Fin k) :
    (existsTrack n z a).rename r = existsTrack (r n) (r z) (r a) := by
  simp only [existsTrack, Formula.rename, witness_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_track {m} {Γ : Context m} (f d n z a : Fin m) (h : Derives Γ (witness f d n z a)) :
    Derives Γ (existsTrack n z a) := by
  apply Derives.exI d
  apply Derives.exI f
  simpa only [Formula.instantiate, Formula.rename, witness_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using h
end PPAC.Migration.FiniteIterationSyntax
