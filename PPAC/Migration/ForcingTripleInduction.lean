/- The four exact recursive dependencies of pinned AtomicForcing.atomic_laws.
Six permutations strengthen the predicate. Three applications of the existing
Child schema provide the internal induction, without external WellFounded or
an invented equivalence with a lexicographic order. The actual consumer is
ForcingAtomicLaws.atomic_laws. -/
import PPAC.Migration.ForcingPairInduction

namespace PPAC.Migration.ForcingTripleInduction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingNameRecursion (Step)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def symmetric {n : Nat} (p : Formula (n+3)) : Formula (n+3) :=
  let rho : Fin n → Fin (n+3) := fun i => i.castSucc.castSucc.castSucc
  let x := (Fin.last n).castSucc.castSucc
  let y := (Fin.last (n+1)).castSucc
  let z := Fin.last (n+2)
  p.conj ((ForcingNameRecursion.op p rho y x z).conj
    ((ForcingNameRecursion.op p rho z x y).conj ((ForcingNameRecursion.op p rho x z y).conj
      ((ForcingNameRecursion.op p rho y z x).conj (ForcingNameRecursion.op p rho z y x)))))

def Symmetric {n : Nat} (p : Formula (n+3)) (params : Fin n → M.Carrier .set) (x y z : M.Carrier .set) : Prop :=
  Step p params x y z ∧ Step p params y x z ∧ Step p params z x y ∧
    Step p params x z y ∧ Step p params y z x ∧ Step p params z y x

def allLast {n : Nat} (p : Formula (n+3)) : Formula (n+2) := .all (symmetric p)

def allOther {n : Nat} (p : Formula (n+3)) : Formula (n+1) := .all (allLast p)

theorem symmetric_semantics {n : Nat} (p : Formula (n+3)) (params : Fin n → M.Carrier .set) (x y z : M.Carrier .set) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases z (Fin.lastCases y (Fin.lastCases x params))) (symmetric p) ↔ Symmetric p params x y z := by
  simp only [symmetric,Symmetric,Formula.Realize,ForcingNameRecursion.op_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc,Step]

theorem allLast_semantics {n : Nat} (p : Formula (n+3)) (params : Fin n → M.Carrier .set) (x y : M.Carrier .set) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem
      (Fin.lastCases y (Fin.lastCases x params)) (allLast p) ↔ ∀ z, Symmetric p params x y z := by
  simp only [allLast,Formula.Realize,symmetric_semantics (M := M)]
  rfl

theorem allOther_semantics {n : Nat} (p : Formula (n+3)) (params : Fin n → M.Carrier .set) (x : M.Carrier .set) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases x params) (allOther p) ↔
      ∀ y z, Symmetric p params x y z := by
  simp only [allOther,Formula.Realize,allLast_semantics (M := M)]
  rfl

theorem formula_induction (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (p : Formula (n+3)) (params : Fin n → M.Carrier .set)
    (step : ∀ a b c,
      (∀ nu r, PureKuratowski.PairMember M nu r a → Step p params nu b c) →
      (∀ nu r, PureKuratowski.PairMember M nu r c → Step p params nu b a) →
      (∀ nu r, PureKuratowski.PairMember M nu r c → Step p params b a nu) →
      (∀ nu r, PureKuratowski.PairMember M nu r b → Step p params nu a c) → Step p params a b c) :
    ∀ a b c, Step p params a b c := by
  have first := ForcingMapLaws.formula_induction hM (allOther p) params (by
    intro a ia
    apply (allOther_semantics p params a).mpr
    have second := ForcingMapLaws.formula_induction hM (allLast p) (Fin.lastCases a params) (by
      intro b ib
      apply (allLast_semantics p params a b).mpr
      have third := ForcingMapLaws.formula_induction hM (symmetric p) (Fin.lastCases b (Fin.lastCases a params)) (by
        intro c ic
        apply (symmetric_semantics p params a b c).mpr
        have iA := fun nu r h => (allOther_semantics p params nu).mp (ia nu r h)
        have iB := fun nu r h => (allLast_semantics p params a nu).mp (ib nu r h)
        have iC := fun nu r h => (symmetric_semantics p params a b nu).mp (ic nu r h)
        refine ⟨?_,?_,?_,?_,?_,?_⟩
        · exact step a b c
            (fun nu r h => (iA nu r h b c).1)
            (fun nu r h => (iC nu r h).2.2.2.2.2)
            (fun nu r h => (iC nu r h).2.1)
            (fun nu r h => (iB nu r h c).2.1)
        · exact step b a c
            (fun nu r h => (iB nu r h c).2.1)
            (fun nu r h => (iC nu r h).2.2.1)
            (fun nu r h => (iC nu r h).1)
            (fun nu r h => (iA nu r h b c).1)
        · exact step c a b
            (fun nu r h => (iC nu r h).2.2.1)
            (fun nu r h => (iB nu r h c).2.1)
            (fun nu r h => (iB nu r h c).2.2.2.1)
            (fun nu r h => (iA nu r h b c).2.2.2.1)
        · exact step a c b
            (fun nu r h => (iA nu r h b c).2.2.2.1)
            (fun nu r h => (iB nu r h c).2.2.2.2.1)
            (fun nu r h => (iB nu r h c).2.2.1)
            (fun nu r h => (iC nu r h).2.2.1)
        · exact step b c a
            (fun nu r h => (iB nu r h c).2.2.2.2.1)
            (fun nu r h => (iA nu r h b c).2.2.2.1)
            (fun nu r h => (iA nu r h b c).2.2.2.2.2)
            (fun nu r h => (iC nu r h).2.2.2.2.2)
        · exact step c b a
            (fun nu r h => (iC nu r h).2.2.2.2.2)
            (fun nu r h => (iA nu r h b c).1)
            (fun nu r h => (iA nu r h b c).2.2.2.2.1)
            (fun nu r h => (iB nu r h c).2.2.2.2.1)
      )
      intro c
      exact (symmetric_semantics p params a b c).mp (third c))
    intro b c
    exact (allLast_semantics p params a b).mp (second b) c)
  intro a b c
  exact ((allOther_semantics p params a).mp (first a) b c).1

end PPAC.Migration.ForcingTripleInduction
