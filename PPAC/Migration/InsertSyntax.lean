import PPAC.Migration.GraphLogic

/-! 对象并集与单元素插入公式；Source.successor保持原编码。 -/
namespace PPAC.Migration.InsertSyntax
open Source SourceAlgebra PairSyntax

def unionFiber {m} (a z : Fin m) : Formula m :=
  .ex ((Formula.mem (Fin.last m) a.castSucc).conj (.mem z.castSucc (Fin.last m)))

def unionOf {m} (u a : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) u.castSucc).iff (unionFiber a.castSucc (Fin.last m)))

def unionExists {m} (a : Fin m) : Formula m := .ex (unionOf (Fin.last m) a.castSucc)

def insert {m} (b a x : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) b.castSucc).iff
    ((Formula.mem (Fin.last m) a.castSucc).disj (.equal (Fin.last m) x.castSucc)))

def insertExists {m} (a x : Fin m) : Formula m := .ex (insert (Fin.last m) a.castSucc x.castSucc)

theorem unionFiber_rename {m k} (a z : Fin m) (r : Fin m → Fin k) :
    (unionFiber a z).rename r = unionFiber (r a) (r z) := by
  simp only [unionFiber, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem unionOf_rename {m k} (u a : Fin m) (r : Fin m → Fin k) :
    (unionOf u a).rename r = unionOf (r u) (r a) := by
  simp only [unionOf, Formula.iff, Formula.rename, unionFiber_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem unionExists_rename {m k} (a : Fin m) (r : Fin m → Fin k) :
    (unionExists a).rename r = unionExists (r a) := by
  simp only [unionExists, Formula.rename, unionOf_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem insert_rename {m k} (b a x : Fin m) (r : Fin m → Fin k) :
    (insert b a x).rename r = insert (r b) (r a) (r x) := by
  simp only [insert, Formula.iff, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem insertExists_rename {m k} (a x : Fin m) (r : Fin m → Fin k) :
    (insertExists a x).rename r = insertExists (r a) (r x) := by
  simp only [insertExists, Formula.rename, insert_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem successor_original {m} (b a : Fin m) : Source.SetLanguage.successor b a = insert b a a := rfl

theorem union_core : Source.SetLanguage.union = (unionExists (0 : Fin 1)).close := rfl

theorem union_instance {m} {Γ : Context m} (a : Fin m)
    (h : Derives Γ (Source.SetLanguage.union.rename Fin.elim0)) : Derives Γ (unionExists a) := by
  rw [union_core] at h
  have hi := specialize_close (unionExists (0 : Fin 1)) (fun _ => a) h
  simpa only [unionExists_rename] using hi

theorem union_at {m} {Γ : Context m} (u a z : Fin m) (h : Derives Γ (unionOf u a)) :
    Derives Γ ((Formula.mem z u).iff (unionFiber a z)) := by
  have hi := Derives.allE z h
  simpa only [Formula.instantiate, Formula.rename, unionFiber_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem insert_at {m} {Γ : Context m} (b a x z : Fin m) (h : Derives Γ (insert b a x)) :
    Derives Γ ((Formula.mem z b).iff ((Formula.mem z a).disj (.equal z x))) := by
  have hi := Derives.allE z h
  simpa only [Formula.instantiate, Formula.rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
end PPAC.Migration.InsertSyntax
