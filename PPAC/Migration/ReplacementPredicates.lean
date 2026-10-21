import PPAC.Migration.SourceLogic
import PPAC.Migration.SourceStatements

/-! 精确像证明的源公式；所有函数都构造对象AST，参数和见证均为对象变量槽。 -/
namespace PPAC.Migration.ReplacementPredicates
open Source SourceAlgebra

abbrev paramsUp {n m} (ρ : Fin n → Fin m) : Fin n → Fin (m+1) := fun i => (ρ i).castSucc

def rel {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x y : Fin m) : Formula m :=
  Source.SetLanguage.relation p ρ x y

def unique {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x u : Fin m) : Formula m :=
  .all ((rel p (paramsUp ρ) x.castSucc (Fin.last m)).imp (.equal (Fin.last m) u.castSucc))

def fiber {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x : Fin m) : Formula m :=
  .ex ((rel p (paramsUp ρ) x.castSucc (Fin.last m)).conj
    (unique p (paramsUp ρ) x.castSucc (Fin.last m)))

def total {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) a.castSucc).imp (fiber p (paramsUp ρ) (Fin.last m)))

def boundFiber {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w x : Fin m) : Formula m :=
  .ex ((Formula.mem (Fin.last m) w.castSucc).conj (rel p (paramsUp ρ) x.castSucc (Fin.last m)))

def covered {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a w : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) a.castSucc).imp (boundFiber p (paramsUp ρ) w.castSucc (Fin.last m)))

def image {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a y : Fin m) : Formula m :=
  .ex ((Formula.mem (Fin.last m) a.castSucc).conj (rel p (paramsUp ρ) (Fin.last m) y.castSucc))

def separated {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a w c : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) c.castSucc).iff
    ((Formula.mem (Fin.last m) w.castSucc).conj (image p (paramsUp ρ) a.castSucc (Fin.last m))))

def exactImage {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a c : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) c.castSucc).iff (image p (paramsUp ρ) a.castSucc (Fin.last m)))

theorem rel_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x y : Fin m) (r : Fin m → Fin k) :
    (rel p ρ x y).rename r = rel p (fun i => r (ρ i)) (r x) (r y) := by
  rw [rel, Source.SetLanguage.relation, rename_comp]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.lastCases_last]
  · refine Fin.lastCases ?_ (fun k => ?_) j <;> simp only [Fin.lastCases_castSucc, Fin.lastCases_last]

theorem unique_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x u : Fin m) (r : Fin m → Fin k) :
    (unique p ρ x u).rename r = unique p (fun i => r (ρ i)) (r x) (r u) := by
  simp only [unique, Formula.rename, rel_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x : Fin m) (r : Fin m → Fin k) :
    (fiber p ρ x).rename r = fiber p (fun i => r (ρ i)) (r x) := by
  simp only [fiber, Formula.rename, rel_rename, unique_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem total_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a : Fin m) (r : Fin m → Fin k) :
    (total p ρ a).rename r = total p (fun i => r (ρ i)) (r a) := by
  simp only [total, Formula.rename, fiber_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem boundFiber_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (w x : Fin m) (r : Fin m → Fin k) :
    (boundFiber p ρ w x).rename r = boundFiber p (fun i => r (ρ i)) (r w) (r x) := by
  simp only [boundFiber, Formula.rename, rel_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem covered_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a w : Fin m) (r : Fin m → Fin k) :
    (covered p ρ a w).rename r = covered p (fun i => r (ρ i)) (r a) (r w) := by
  simp only [covered, Formula.rename, boundFiber_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem image_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a y : Fin m) (r : Fin m → Fin k) :
    (image p ρ a y).rename r = image p (fun i => r (ρ i)) (r a) (r y) := by
  simp only [image, Formula.rename, rel_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem separated_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a w c : Fin m) (r : Fin m → Fin k) :
    (separated p ρ a w c).rename r = separated p (fun i => r (ρ i)) (r a) (r w) (r c) := by
  simp only [separated, Formula.rename, image_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem exactImage_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a c : Fin m) (r : Fin m → Fin k) :
    (exactImage p ρ a c).rename r = exactImage p (fun i => r (ρ i)) (r a) (r c) := by
  simp only [exactImage, Formula.rename, image_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

/-- 从唯一纤维和界内见证推出任意输出在界中，是精确像构造的关键逻辑步。 -/
theorem specialize_unique {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m)
    (x u t : Fin m) (h : Derives Γ (unique p ρ x u)) :
    Derives Γ ((rel p ρ x t).imp (.equal t u)) := by
  have hi := Derives.allE t h
  simpa only [Formula.instantiate, Formula.rename, rel_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem specialize_total {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m)
    (a x : Fin m) (h : Derives Γ (total p ρ a)) :
    Derives Γ ((Formula.mem x a).imp (fiber p ρ x)) := by
  have hi := Derives.allE x h
  simpa only [Formula.instantiate, Formula.rename, fiber_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem specialize_covered {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m)
    (a w x : Fin m) (h : Derives Γ (covered p ρ a w)) :
    Derives Γ ((Formula.mem x a).imp (boundFiber p ρ w x)) := by
  have hi := Derives.allE x h
  simpa only [Formula.instantiate, Formula.rename, boundFiber_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
theorem specialize_separated {n m} {Γ : Context m} (p : Formula (n+2)) (ρ : Fin n → Fin m)
    (a w c y : Fin m) (h : Derives Γ (separated p ρ a w c)) :
    Derives Γ ((Formula.mem y c).iff ((Formula.mem y w).conj (image p ρ a y))) := by
  have hi := Derives.allE y h
  simpa only [Formula.instantiate, Formula.rename, image_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi
def hasValue {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x : Fin m) : Formula m :=
  .ex (rel p (paramsUp ρ) x.castSucc (Fin.last m))

def totalRelation {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) a.castSucc).imp (hasValue p (paramsUp ρ) (Fin.last m)))

def collects {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a : Fin m) : Formula m :=
  .ex (covered p (paramsUp ρ) a.castSucc (Fin.last m))

def separationExists {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a w : Fin m) : Formula m :=
  .ex (separated p (paramsUp ρ) a.castSucc w.castSucc (Fin.last m))

def imageExists {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a : Fin m) : Formula m :=
  .ex (exactImage p (paramsUp ρ) a.castSucc (Fin.last m))

def collectionBody {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a : Fin m) : Formula m :=
  (totalRelation p ρ a).imp (collects p ρ a)

def replacementBody {n m} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a : Fin m) : Formula m :=
  (total p ρ a).imp (imageExists p ρ a)

theorem hasValue_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (x : Fin m) (r : Fin m → Fin k) :
    (hasValue p ρ x).rename r = hasValue p (fun i => r (ρ i)) (r x) := by
  simp only [hasValue, Formula.rename, rel_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem totalRelation_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a : Fin m) (r : Fin m → Fin k) :
    (totalRelation p ρ a).rename r = totalRelation p (fun i => r (ρ i)) (r a) := by
  simp only [totalRelation, Formula.rename, hasValue_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem collects_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a : Fin m) (r : Fin m → Fin k) :
    (collects p ρ a).rename r = collects p (fun i => r (ρ i)) (r a) := by
  simp only [collects, Formula.rename, covered_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem separationExists_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a w : Fin m) (r : Fin m → Fin k) :
    (separationExists p ρ a w).rename r = separationExists p (fun i => r (ρ i)) (r a) (r w) := by
  simp only [separationExists, Formula.rename, separated_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem imageExists_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a : Fin m) (r : Fin m → Fin k) :
    (imageExists p ρ a).rename r = imageExists p (fun i => r (ρ i)) (r a) := by
  simp only [imageExists, Formula.rename, exactImage_rename, paramsUp, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc]

theorem collectionBody_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a : Fin m) (r : Fin m → Fin k) :
    (collectionBody p ρ a).rename r = collectionBody p (fun i => r (ρ i)) (r a) := by
  simp only [collectionBody, Formula.rename, totalRelation_rename, collects_rename]

theorem replacementBody_rename {n m k} (p : Formula (n+2)) (ρ : Fin n → Fin m) (a : Fin m) (r : Fin m → Fin k) :
    (replacementBody p ρ a).rename r = replacementBody p (fun i => r (ρ i)) (r a) := by
  simp only [replacementBody, Formula.rename, total_rename, imageExists_rename]
end PPAC.Migration.ReplacementPredicates
