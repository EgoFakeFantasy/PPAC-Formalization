import PPAC.Migration.RestrictionSyntax
import PPAC.Migration.InsertLogic

/-! 纯对象归纳集、最小归纳集与实际分离构造；不引用宿主Nat作为对象域。 -/
namespace PPAC.Migration.OmegaSyntax
open Source SourceAlgebra RestrictionSyntax InsertSyntax

def empty {m} (z : Fin m) : Formula m := .all ((Formula.mem (Fin.last m) z.castSucc).neg)

def successor {m} (s x : Fin m) : Formula m := insert s x x

def zeroIn {m} (i : Fin m) : Formula m := .ex ((Formula.mem (Fin.last m) i.castSucc).conj (empty (Fin.last m)))

def stepIn {m} (i x : Fin m) : Formula m :=
  .ex ((Formula.mem (Fin.last m) i.castSucc).conj (successor (Fin.last m) x.castSucc))

def isInductive {m} (i : Fin m) : Formula m :=
  (zeroIn i).conj (.all ((Formula.mem (Fin.last m) i.castSucc).imp (stepIn i.castSucc (Fin.last m))))

def universal {m} (x : Fin m) : Formula m := .all ((isInductive (Fin.last m)).imp (.mem x.castSucc (Fin.last m)))

def omega {m} (w : Fin m) : Formula m :=
  (isInductive w).conj (.all ((isInductive (Fin.last m)).imp (RestrictionSyntax.subset w.castSucc (Fin.last m))))

def omegaExists : Source.Sentence := .ex (omega (0 : Fin 1))

def cut {m} (w i : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) w.castSucc).iff
    ((Formula.mem (Fin.last m) i.castSucc).conj (universal (Fin.last m))))

def matrix : Formula 1 := universal 0

theorem empty_original {m} (z : Fin m) : Source.SetLanguage.empty z = empty z := rfl

theorem successor_original {m} (s x : Fin m) : Source.SetLanguage.successor s x = successor s x := rfl

theorem infinity_original : Source.SetLanguage.infinity = .ex (isInductive (0 : Fin 1)) := rfl

theorem empty_rename {m k} (z : Fin m) (r : Fin m → Fin k) :
    (empty z).rename r = empty (r z) := by
  simp only [empty, Formula.rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem successor_rename {m k} (s x : Fin m) (r : Fin m → Fin k) :
    (successor s x).rename r = successor (r s) (r x) := by
  simp only [successor, insert_rename]

theorem zeroIn_rename {m k} (i : Fin m) (r : Fin m → Fin k) :
    (zeroIn i).rename r = zeroIn (r i) := by
  simp only [zeroIn, Formula.rename, empty_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem stepIn_rename {m k} (i x : Fin m) (r : Fin m → Fin k) :
    (stepIn i x).rename r = stepIn (r i) (r x) := by
  simp only [stepIn, Formula.rename, successor_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem isInductive_rename {m k} (i : Fin m) (r : Fin m → Fin k) :
    (isInductive i).rename r = isInductive (r i) := by
  simp only [isInductive, Formula.rename, zeroIn_rename, stepIn_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem universal_rename {m k} (x : Fin m) (r : Fin m → Fin k) :
    (universal x).rename r = universal (r x) := by
  simp only [universal, Formula.rename, isInductive_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem omega_rename {m k} (w : Fin m) (r : Fin m → Fin k) :
    (omega w).rename r = omega (r w) := by
  simp only [omega, Formula.rename, isInductive_rename, RestrictionSyntax.subset_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem cut_rename {m k} (w i : Fin m) (r : Fin m → Fin k) :
    (cut w i).rename r = cut (r w) (r i) := by
  simp only [cut, Formula.iff, Formula.rename, universal_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem empty_at {m} {Γ : Context m} (z x : Fin m) (h : Derives Γ (empty z)) : Derives Γ (Formula.mem x z).neg := by
  have hi := Derives.allE x h
  simpa only [Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem step_at {m} {Γ : Context m} (i x : Fin m) (h : Derives Γ (isInductive i)) :
    Derives Γ ((Formula.mem x i).imp (stepIn i x)) := by
  have hi := Derives.allE x (Derives.conjR h)
  simpa only [Formula.instantiate, Formula.rename, stepIn_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem universal_at {m} {Γ : Context m} (x i : Fin m) (h : Derives Γ (universal x)) :
    Derives Γ ((isInductive i).imp (.mem x i)) := by
  have hi := Derives.allE i h
  simpa only [Formula.instantiate, Formula.rename, isInductive_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem omega_at {m} {Γ : Context m} (w i : Fin m) (h : Derives Γ (omega w)) :
    Derives Γ ((isInductive i).imp (RestrictionSyntax.subset w i)) := by
  have hi := Derives.allE i (Derives.conjR h)
  simpa only [Formula.instantiate, Formula.rename, isInductive_rename, RestrictionSyntax.subset_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem cut_at {m} {Γ : Context m} (w i x : Fin m) (h : Derives Γ (cut w i)) :
    Derives Γ ((Formula.mem x w).iff ((Formula.mem x i).conj (universal x))) := by
  have hi := Derives.allE x h
  simpa only [Formula.instantiate, Formula.rename, universal_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem matrix_pred {m} (ρ : Fin 0 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = universal x := by
  rw [MinimalPredicates.pred, matrix, universal_rename]
  congr 1

theorem separate_cut {m} {Γ : Context m} (i : Fin m)
    (hs : Derives Γ ((Source.SetLanguage.separation matrix).rename Fin.elim0)) :
    Derives Γ (.ex (cut (Fin.last m) i.castSucc)) := by
  have hi := MinimalInstances.separation_instance matrix (Fin.elim0 : Fin 0 → Fin m) i hs
  simpa only [MinimalPredicates.separationExists, MinimalPredicates.separated, MinimalPredicates.satisfying,
    matrix_pred, cut] using hi

theorem omegaExists_at {m} : omegaExists.rename (Fin.elim0 : Fin 0 → Fin m) = .ex (omega (Fin.last m)) := by
  have h0 : Formula.liftRen (Fin.elim0 : Fin 0 → Fin m) (0 : Fin 1) = Fin.last m := by
    change Fin.lastCases (Fin.last m) (fun i : Fin 0 => (Fin.elim0 i : Fin m).castSucc) (Fin.last 0) = Fin.last m
    exact Fin.lastCases_last
  simp only [omegaExists, Formula.rename, omega_rename, h0]

theorem infinity_at {m} {Γ : Context m} (h : Derives Γ (Source.SetLanguage.infinity.rename Fin.elim0)) :
    Derives Γ (.ex (isInductive (Fin.last m))) := by
  have h0 : Formula.liftRen (Fin.elim0 : Fin 0 → Fin m) (0 : Fin 1) = Fin.last m := by
    change Fin.lastCases (Fin.last m) (fun i : Fin 0 => (Fin.elim0 i : Fin m).castSucc) (Fin.last 0) = Fin.last m
    exact Fin.lastCases_last
  simpa only [infinity_original, Formula.rename, isInductive_rename, h0] using h
end PPAC.Migration.OmegaSyntax
