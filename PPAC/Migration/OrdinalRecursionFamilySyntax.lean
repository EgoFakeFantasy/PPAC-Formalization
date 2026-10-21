import PPAC.Migration.OrdinalRecursionContext

/-! 前驱递归图、实际唯一后继图的精确像、覆盖及族成员数据，均为纯对象公式。 -/
namespace PPAC.Migration.OrdinalRecursionFamilySyntax
open Source SourceAlgebra SourceLogic OrdinalRecursionSyntax OrdinalRecursionSuccessorSyntax
open ReplacementPredicates (paramsUp)

def predecessors {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) a.castSucc).imp (recursorExists p (paramsUp ρ) (Fin.last m)))

def image {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a g : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) a.castSucc).conj (successorGraph p (paramsUp ρ) (Fin.last m) g.castSucc))

def range {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (c a : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) c.castSucc).iff (image p (paramsUp ρ) a.castSucc (Fin.last m)))

def rangeExists {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a : Fin m) : Formula m := .ex
  (range p (paramsUp ρ) (Fin.last m) a.castSucc)

def memberAt {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (c b : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) c.castSucc).conj (successorGraph p (paramsUp ρ) b.castSucc (Fin.last m)))

def coverage {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (c a : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) a.castSucc).imp (memberAt p (paramsUp ρ) c.castSucc (Fin.last m)))

def family {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (c a : Fin m) : Formula m :=
  (range p ρ c a).conj (coverage p ρ c a)

def familyExists {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a : Fin m) : Formula m := .ex
  (family p (paramsUp ρ) (Fin.last m) a.castSucc)

def memberData {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a g b s : Fin m) : Formula m :=
  (Formula.mem b a).conj ((OmegaSyntax.successor s b).conj (recursor p ρ g s))

def memberDataExists {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a g : Fin m) : Formula m := .ex (.ex
  (memberData p (paramsUp (paramsUp ρ)) a.castSucc.castSucc g.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))

theorem predecessors_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a : Fin m) (r : Fin m → Fin k) :
    (predecessors p ρ a).rename r = predecessors p (fun i => r (ρ i)) (r a) := by
  simp only [predecessors, recursorExists_rename, Formula.rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]


theorem image_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a g : Fin m) (r : Fin m → Fin k) :
    (image p ρ a g).rename r = image p (fun i => r (ρ i)) (r a) (r g) := by
  simp only [image, successorGraph_rename, Formula.rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]


theorem range_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (c a : Fin m) (r : Fin m → Fin k) :
    (range p ρ c a).rename r = range p (fun i => r (ρ i)) (r c) (r a) := by
  simp only [range, Formula.iff, image_rename, Formula.rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]


theorem rangeExists_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a : Fin m) (r : Fin m → Fin k) :
    (rangeExists p ρ a).rename r = rangeExists p (fun i => r (ρ i)) (r a) := by
  simp only [rangeExists, range_rename, Formula.rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]


theorem memberAt_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (c b : Fin m) (r : Fin m → Fin k) :
    (memberAt p ρ c b).rename r = memberAt p (fun i => r (ρ i)) (r c) (r b) := by
  simp only [memberAt, successorGraph_rename, Formula.rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]


theorem coverage_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (c a : Fin m) (r : Fin m → Fin k) :
    (coverage p ρ c a).rename r = coverage p (fun i => r (ρ i)) (r c) (r a) := by
  simp only [coverage, memberAt_rename, Formula.rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]


theorem family_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (c a : Fin m) (r : Fin m → Fin k) :
    (family p ρ c a).rename r = family p (fun i => r (ρ i)) (r c) (r a) := by
  simp only [family, range_rename, coverage_rename, Formula.rename]


theorem familyExists_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a : Fin m) (r : Fin m → Fin k) :
    (familyExists p ρ a).rename r = familyExists p (fun i => r (ρ i)) (r a) := by
  simp only [familyExists, family_rename, Formula.rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]


theorem memberData_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a g b s : Fin m) (r : Fin m → Fin k) :
    (memberData p ρ a g b s).rename r = memberData p (fun i => r (ρ i)) (r a) (r g) (r b) (r s) := by
  simp only [memberData, OmegaSyntax.successor_rename, recursor_rename, Formula.rename]


theorem memberDataExists_rename {n m k} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a g : Fin m) (r : Fin m → Fin k) :
    (memberDataExists p ρ a g).rename r = memberDataExists p (fun i => r (ρ i)) (r a) (r g) := by
  simp only [memberDataExists, memberData_rename, Formula.rename, paramsUp,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem predecessors_at {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a b : Fin m)
    (hh : Derives Γ (predecessors p ρ a)) : Derives Γ ((Formula.mem b a).imp (recursorExists p ρ b)) := by
  have hi := Derives.allE b hh
  simpa only [Formula.instantiate, Formula.rename, recursorExists_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem range_at {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (c a g : Fin m)
    (hh : Derives Γ (range p ρ c a)) : Derives Γ ((Formula.mem g c).iff (image p ρ a g)) := by
  have hi := Derives.allE g hh
  simpa only [Formula.instantiate, Formula.rename, image_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem coverage_at {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (c a b : Fin m)
    (hh : Derives Γ (coverage p ρ c a)) : Derives Γ ((Formula.mem b a).imp (memberAt p ρ c b)) := by
  have hi := Derives.allE b hh
  simpa only [Formula.instantiate, Formula.rename, memberAt_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem image_intro {n m} {Γ : Context m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a g b : Fin m)
    (hb : Derives Γ (.mem b a)) (hg : Derives Γ (successorGraph p ρ b g)) : Derives Γ (image p ρ a g) := by
  apply Derives.exI b
  simpa only [Formula.instantiate, Formula.rename, successorGraph_rename, paramsUp,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.conjI hb hg

theorem matrix_image {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a g : Fin m) :
    ReplacementPredicates.image (OrdinalRecursionSuccessorUnique.successorMatrix p) ρ a g = image p ρ a g := by
  simp only [ReplacementPredicates.image, OrdinalRecursionSuccessorUnique.matrix_relation, image]

theorem matrix_range {n m} (p : Formula (n+3)) (ρ : Fin n → Fin m) (a c : Fin m) :
    ReplacementPredicates.exactImage (OrdinalRecursionSuccessorUnique.successorMatrix p) ρ a c = range p ρ c a := by
  simp only [ReplacementPredicates.exactImage, matrix_image, range]
end PPAC.Migration.OrdinalRecursionFamilySyntax
