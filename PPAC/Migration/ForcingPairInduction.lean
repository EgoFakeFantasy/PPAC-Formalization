/- The exact three recursive dependencies of pinned AtomicForcing.relations:
left child, right child, and right child with the pair swapped. Two uses of the
existing Child formula-induction schema prove the required internal induction.
This does not assert external well-foundedness or identify a plain lexicographic
relation with the source multiset rank relation. -/
import PPAC.Migration.ForcingCheckNameLaws

namespace PPAC.Migration.ForcingPairInduction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ReplacementPredicates (paramsUp)
open ForcingMapConditions (MapRel)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def symmetric {n : Nat} (p : Formula (n+2)) : Formula (n+2) :=
  p.conj (ReplacementPredicates.rel p (fun i => i.castSucc.castSucc) (Fin.last (n+1)) (Fin.last n).castSucc)

def rightAll {n : Nat} (p : Formula (n+2)) : Formula (n+1) := .all (symmetric p)

theorem symmetric_semantics {n : Nat} (p : Formula (n+2)) (params : Fin n → M.Carrier .set) (x y : M.Carrier .set) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases y (Fin.lastCases x params))
      (symmetric p) ↔ MapRel p params x y ∧ MapRel p params y x := by
  simp only [symmetric, Formula.Realize, ForcingMapConditions.rel_semantics (M := M),
    Fin.lastCases_last, Fin.lastCases_castSucc, MapRel]

theorem rightAll_semantics {n : Nat} (p : Formula (n+2)) (params : Fin n → M.Carrier .set) (x : M.Carrier .set) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases x params) (rightAll p) ↔
      ∀ y, MapRel p params x y ∧ MapRel p params y x := by
  simp only [rightAll, Formula.Realize, symmetric_semantics (M := M)]
  rfl

theorem formula_induction (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (p : Formula (n+2)) (params : Fin n → M.Carrier .set)
    (step : ∀ x y,
      (∀ z c, PureKuratowski.PairMember M z c x → MapRel p params z y) →
      (∀ z c, PureKuratowski.PairMember M z c y → MapRel p params x z) →
      (∀ z c, PureKuratowski.PairMember M z c y → MapRel p params z x) → MapRel p params x y) :
    ∀ x y, MapRel p params x y := by
  have all := ForcingMapLaws.formula_induction hM (rightAll p) params (by
    intro x ix
    apply (rightAll_semantics p params x).mpr
    have inner := ForcingMapLaws.formula_induction hM (symmetric p) (Fin.lastCases x params) (by
      intro y iy
      apply (symmetric_semantics p params x y).mpr
      constructor
      · exact step x y
          (fun z c hz => ((rightAll_semantics p params z).mp (ix z c hz) y).1)
          (fun z c hz => ((symmetric_semantics p params x z).mp (iy z c hz)).1)
          (fun z c hz => ((symmetric_semantics p params x z).mp (iy z c hz)).2)
      · exact step y x
          (fun z c hz => ((symmetric_semantics p params x z).mp (iy z c hz)).2)
          (fun z c hz => ((rightAll_semantics p params z).mp (ix z c hz) y).2)
          (fun z c hz => ((rightAll_semantics p params z).mp (ix z c hz) y).1))
    intro y
    exact (symmetric_semantics p params x y).mp (inner y))
  intro x y
  exact ((rightAll_semantics p params x).mp (all x) y).1

def leftBelow {n m : Nat} (p : Formula (n+2)) (rho : Fin n → Fin m) (x y : Fin m) : Formula m :=
  .all ((ForcingNameInduction.child (Fin.last m) x.castSucc).imp
    (ReplacementPredicates.rel p (paramsUp rho) (Fin.last m) y.castSucc))

def rightBelow {n m : Nat} (p : Formula (n+2)) (rho : Fin n → Fin m) (x y : Fin m) : Formula m :=
  .all ((ForcingNameInduction.child (Fin.last m) y.castSucc).imp
    (ReplacementPredicates.rel p (paramsUp rho) x.castSucc (Fin.last m)))

def swapBelow {n m : Nat} (p : Formula (n+2)) (rho : Fin n → Fin m) (x y : Fin m) : Formula m :=
  .all ((ForcingNameInduction.child (Fin.last m) y.castSucc).imp
    (ReplacementPredicates.rel p (paramsUp rho) (Fin.last m) x.castSucc))

def progressive {n : Nat} (p : Formula (n+2)) : Formula n :=
  let rho : Fin n → Fin (n+2) := fun i => i.castSucc.castSucc
  let x := (Fin.last n).castSucc
  let y := Fin.last (n+1)
  .all (.all ((leftBelow p rho x y).imp ((rightBelow p rho x y).imp
    ((swapBelow p rho x y).imp (ReplacementPredicates.rel p rho x y)))))

def holds {n : Nat} (p : Formula (n+2)) : Formula n := .all (.all p)

theorem progressive_semantics {n : Nat} (p : Formula (n+2)) (v : Fin n → M.Carrier .set) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (progressive p) ↔
      ∀ x y,
        (∀ z c, PureKuratowski.PairMember M z c x → MapRel p v z y) →
        (∀ z c, PureKuratowski.PairMember M z c y → MapRel p v x z) →
        (∀ z c, PureKuratowski.PairMember M z c y → MapRel p v z x) → MapRel p v x y := by
  simp only [progressive, leftBelow, rightBelow, swapBelow, Formula.Realize,
    ForcingNameInduction.child, KuratowskiZF.source_edge, ForcingMapConditions.rel_semantics (M := M),
    paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc]
  constructor
  · intro h x y hl hr hs
    exact h x y (fun z ⟨c, hc⟩ => hl z c hc) (fun z ⟨c, hc⟩ => hr z c hc) (fun z ⟨c, hc⟩ => hs z c hc)
  · intro h x y hl hr hs
    exact h x y (fun z c hc => hl z ⟨c, hc⟩) (fun z c hc => hr z ⟨c, hc⟩) (fun z c hc => hs z ⟨c, hc⟩)

def sentence {n : Nat} (p : Formula (n+2)) : Source.Sentence := ((progressive p).imp (holds p)).close

theorem models {n : Nat} (p : Formula (n+2)) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (sentence p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v h
  exact formula_induction hM p v ((progressive_semantics p v).mp h)

theorem kernel_certificate {n : Nat} (p : Formula (n+2)) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (sentence p)) :=
  ModelTransfer.derives (fun _ hM => models p hM)

end PPAC.Migration.ForcingPairInduction
