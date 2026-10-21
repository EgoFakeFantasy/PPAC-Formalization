import PPAC.Migration.SourceLogic
import PPAC.Migration.SourceStatements

/-! 与锁定源定义逐式相同的Kuratowski对语法，变量与见证都在对象语言内。 -/
namespace PPAC.Migration.PairSyntax
open Source SourceAlgebra

def pair {m} (p x y : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) p.castSucc).iff
    ((Formula.equal (Fin.last m) x.castSucc).disj (.equal (Fin.last m) y.castSucc)))

def pairExists {m} (x y : Fin m) : Formula m := .ex (pair (Fin.last m) x.castSucc y.castSucc)

def ordered {m} (p x y : Fin m) : Formula m :=
  .ex (.ex ((pair (Fin.last m).castSucc x.castSucc.castSucc x.castSucc.castSucc).conj
    ((pair (Fin.last (m+1)) x.castSucc.castSucc y.castSucc.castSucc).conj
      (pair p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))

def orderedExists {m} (x y : Fin m) : Formula m := .ex (ordered (Fin.last m) x.castSucc y.castSucc)

def sameMembers {m} (p q : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) p.castSucc).iff (.mem (Fin.last m) q.castSucc))

theorem pair_original {m} (p x y : Fin m) : Source.SetLanguage.unorderedPair p x y = pair p x y := rfl

theorem ordered_original {m} (p x y : Fin m) : Source.SetLanguage.orderedPair p x y = ordered p x y := rfl

theorem pair_rename {m k} (p x y : Fin m) (r : Fin m → Fin k) :
    (pair p x y).rename r = pair (r p) (r x) (r y) := by
  simp only [pair, Formula.iff, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem pairExists_rename {m k} (x y : Fin m) (r : Fin m → Fin k) :
    (pairExists x y).rename r = pairExists (r x) (r y) := by
  simp only [pairExists, Formula.rename, pair_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem ordered_rename {m k} (p x y : Fin m) (r : Fin m → Fin k) :
    (ordered p x y).rename r = ordered (r p) (r x) (r y) := by
  simp only [ordered, Formula.rename, pair_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem orderedExists_rename {m k} (x y : Fin m) (r : Fin m → Fin k) :
    (orderedExists x y).rename r = orderedExists (r x) (r y) := by
  simp only [orderedExists, Formula.rename, ordered_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem sameMembers_rename {m k} (p q : Fin m) (r : Fin m → Fin k) :
    (sameMembers p q).rename r = sameMembers (r p) (r q) := by
  simp only [sameMembers, Formula.iff, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem pairing_core : Source.SetLanguage.pairing = (pairExists (0 : Fin 2) 1).close := rfl

theorem extensionality_core : Source.SetLanguage.extensionality =
    ((sameMembers (0 : Fin 2) 1).imp (.equal 0 1)).close := rfl

theorem args2_first {α : Type u} (x y : α) : Source.SetLanguage.args2 x y 0 = x := rfl

theorem args2_second {α : Type u} (x y : α) : Source.SetLanguage.args2 x y 1 = y := by
  change Fin.cases x (Source.SetLanguage.args1 y) (Fin.succ (0 : Fin 1)) = y
  rw [Fin.cases_succ]
  rfl

theorem pairing_instance {m} {Γ : Context m} (x y : Fin m)
    (h : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0)) : Derives Γ (pairExists x y) := by
  rw [pairing_core] at h
  have hi := specialize_close (pairExists (0 : Fin 2) 1) (Source.SetLanguage.args2 x y) h
  simpa only [pairExists_rename, args2_first, args2_second] using hi

theorem extensionality_instance {m} {Γ : Context m} (p q : Fin m)
    (h : Derives Γ (Source.SetLanguage.extensionality.rename Fin.elim0)) :
    Derives Γ ((sameMembers p q).imp (.equal p q)) := by
  rw [extensionality_core] at h
  have hi := specialize_close ((sameMembers (0 : Fin 2) 1).imp (.equal 0 1)) (Source.SetLanguage.args2 p q) h
  simpa only [Formula.rename, sameMembers_rename, args2_first, args2_second] using hi
end PPAC.Migration.PairSyntax
