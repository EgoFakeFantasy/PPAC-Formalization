/- Partial graph compatibility for the original AtomicForcing.relations.
The concrete step is ForcingAtomicStep. Pair induction is the already accepted
left/right/swap schema, not an external well-foundedness assumption. This file
proves compatibility and uniqueness; existence of closed graphs is separate. -/
import PPAC.Migration.ForcingAtomicStep
import PPAC.Migration.ForcingPairInduction

namespace PPAC.Migration.ForcingAtomicGraphs
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ReplacementPredicates (paramsUp)
open ForcingAtomicStep (Row Equation)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def lookup {m : Nat} (g x y output : Fin m) : Formula m :=
  .ex ((PairSyntax.ordered (Fin.last m) x.castSucc y.castSucc).conj
    (Source.SetLanguage.edge g.castSucc (Fin.last m) output.castSucc))

def Lookup (g x y output : M.Carrier .set) : Prop :=
  ∃ key, PureKuratowski.Code M key x y ∧ PureKuratowski.PairMember M key output g

theorem lookup_semantics {m : Nat} (v : Fin m → M.Carrier .set) (g x y output : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (lookup g x y output) ↔
      Lookup (v g) (v x) (v y) (v output) := by
  simp only [lookup, Lookup, Formula.Realize, KuratowskiZF.source_code, KuratowskiZF.source_edge,
    Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

def below {m : Nat} (swap : Bool) (g x y : Fin m) : Formula m :=
  .all (.all ((Source.SetLanguage.edge y.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
    (.ex (lookup g.castSucc.castSucc.castSucc
      (if swap then (Fin.last m).castSucc.castSucc else x.castSucc.castSucc.castSucc)
      (if swap then x.castSucc.castSucc.castSucc else (Fin.last m).castSucc.castSucc) (Fin.last (m+2))))))

def covered {m : Nat} (g x y : Fin m) : Formula m :=
  (below true g y x).conj ((below false g x y).conj (below true g x y))

def Covered (g x y : M.Carrier .set) : Prop :=
  (∀ nu r, PureKuratowski.PairMember M nu r x → ∃ output, Lookup g nu y output) ∧
  (∀ nu r, PureKuratowski.PairMember M nu r y → ∃ output, Lookup g x nu output) ∧
  (∀ nu r, PureKuratowski.PairMember M nu r y → ∃ output, Lookup g nu x output)

theorem below_semantics {m : Nat} (v : Fin m → M.Carrier .set) (swap : Bool) (g x y : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (below swap g x y) ↔
      ∀ nu r, PureKuratowski.PairMember M nu r (v y) →
        ∃ output, Lookup (v g) (if swap then nu else v x) (if swap then v x else nu) output := by
  cases swap <;> simp only [below, Formula.Realize, KuratowskiZF.source_edge, lookup_semantics (M := M),
    Bool.false_eq_true, if_false, if_true, Fin.lastCases_last, Fin.lastCases_castSucc] <;> rfl

theorem covered_semantics {m : Nat} (v : Fin m → M.Carrier .set) (g x y : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (covered g x y) ↔
      Covered (v g) (v x) (v y) := by
  simp only [covered, Covered, Formula.Realize, below_semantics (M := M), Bool.false_eq_true, if_true, if_false]

def good {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (P g : Fin m) : Formula m :=
  .all (.all (.all ((lookup g.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))).imp
      ((covered g.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc).conj
        (ForcingAtomicStep.equation R (fun i => (rho i).castSucc.castSucc.castSucc)
          P.castSucc.castSucc.castSucc g.castSucc.castSucc.castSucc
          (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))))))

def Good {n : Nat} (R : Formula (n+2)) (params : Fin n → M.Carrier .set) (P g : M.Carrier .set) : Prop :=
  ∀ x y output, Lookup g x y output → Covered g x y ∧ Equation R params P g x y output

theorem good_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (R : Formula (n+2))
    (rho : Fin n → Fin m) (P g : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (good R rho P g) ↔
      Good R (fun i => v (rho i)) (v P) (v g) := by
  simp only [good, Good, Formula.Realize, lookup_semantics (M := M), covered_semantics (M := M),
    ForcingAtomicStep.equation_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

def comparison {m : Nat} (g h x y : Fin m) : Formula m :=
  .all (.all ((lookup g.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc (Fin.last m).castSucc).imp
    ((lookup h.castSucc.castSucc x.castSucc.castSucc y.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last m).castSucc (Fin.last (m+1))))))

theorem comparison_semantics {m : Nat} (v : Fin m → M.Carrier .set) (g h x y : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (comparison g h x y) ↔
      ∀ a b, Lookup (v g) (v x) (v y) a → Lookup (v h) (v x) (v y) b → a = b := by
  simp only [comparison, Formula.Realize, lookup_semantics (M := M), Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem row_congr {g h x y : M.Carrier .set}
    (ha : ∀ output, Lookup g x y output ↔ Lookup h x y output) : ∀ a b, Row g x y a b ↔ Row h x y a b := by
  intro a b
  constructor
  · rintro ⟨key,value,hkey,hvalue,he⟩
    obtain ⟨key',hk',he'⟩ := (ha value).mp ⟨key,hkey,he⟩
    exact ⟨key',value,hk',hvalue,he'⟩
  · rintro ⟨key,value,hkey,hvalue,he⟩
    obtain ⟨key',hk',he'⟩ := (ha value).mpr ⟨key,hkey,he⟩
    exact ⟨key',value,hk',hvalue,he'⟩

theorem lookup_agreement {g h x y : M.Carrier .set}
    (hg : ∃ output, Lookup g x y output) (hh : ∃ output, Lookup h x y output)
    (ih : ∀ a b, Lookup g x y a → Lookup h x y b → a = b) :
    ∀ output, Lookup g x y output ↔ Lookup h x y output := by
  intro output
  constructor
  · intro ho
    obtain ⟨v,hv⟩ := hh
    exact (ih output v ho hv).symm ▸ hv
  · intro ho
    obtain ⟨v,hv⟩ := hg
    exact (ih v output hv ho) ▸ hv

theorem compatible (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P g h : M.Carrier .set}
    (hg : Good R params P g) (hh : Good R params P h) :
    ∀ x y a b, Lookup g x y a → Lookup h x y b → a = b := by
  let p := comparison (0 : Fin 4) 1 2 3
  let inputs : Fin 2 → M.Carrier .set := Fin.cases g (fun _ => h)
  have hp : ∀ x y, ForcingMapConditions.MapRel p inputs x y ↔
      ∀ a b, Lookup g x y a → Lookup h x y b → a = b := by
    intro x y
    exact comparison_semantics (M := M) (Fin.lastCases y (Fin.lastCases x inputs)) 0 1 2 3
  have all := ForcingPairInduction.formula_induction hM p inputs (by
    intro x y il ir isw
    apply (hp x y).mpr
    intro a b ha hb
    obtain ⟨cg,sg⟩ := hg x y a ha
    obtain ⟨ch,sh⟩ := hh x y b hb
    have hl := fun nu r he => row_congr (lookup_agreement (cg.1 nu r he) (ch.1 nu r he)
      ((hp nu y).mp (il nu r he)))
    have hr := fun nu r he => row_congr (lookup_agreement (cg.2.1 nu r he) (ch.2.1 nu r he)
      ((hp x nu).mp (ir nu r he)))
    have hs := fun nu r he => row_congr (lookup_agreement (cg.2.2 nu r he) (ch.2.2 nu r he)
      ((hp nu x).mp (isw nu r he)))
    exact ForcingAtomicStep.equation_unique hM ((ForcingAtomicStep.equation_congr hl hr hs).mp sg) sh)
  intro x y
  exact (hp x y).mp (all x y)

def value {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (P x y output : Fin m) : Formula m :=
  .ex ((good R (paramsUp rho) P.castSucc (Fin.last m)).conj
    (lookup (Fin.last m) x.castSucc y.castSucc output.castSucc))

def Value {n : Nat} (R : Formula (n+2)) (params : Fin n → M.Carrier .set)
    (P x y output : M.Carrier .set) : Prop := ∃ g, Good R params P g ∧ Lookup g x y output

theorem value_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (R : Formula (n+2))
    (rho : Fin n → Fin m) (P x y output : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (value R rho P x y output) ↔
      Value R (fun i => v (rho i)) (v P) (v x) (v y) (v output) := by
  simp only [value, Value, Formula.Realize, good_semantics (M := M), lookup_semantics (M := M),
    paramsUp, Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

theorem unique (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P x y a b : M.Carrier .set}
    (ha : Value R params P x y a) (hb : Value R params P x y b) : a = b := by
  obtain ⟨g,hg,ha⟩ := ha
  obtain ⟨h,hh,hb⟩ := hb
  exact compatible hM hg hh x y a b ha hb

def uniquenessSentence {n : Nat} (R : Formula (n+2)) (P x y a b : Fin n) : Source.Sentence :=
  ((value R id P x y a).imp ((value R id P x y b).imp (.equal a b))).close

theorem uniqueness_models {n : Nat} (R : Formula (n+2)) (P x y a b : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (uniquenessSentence R P x y a b)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v ha hb
  exact unique hM ((value_semantics (M := M) v R id P x y a).mp ha)
    ((value_semantics (M := M) v R id P x y b).mp hb)

theorem uniqueness_kernel_certificate {n : Nat} (R : Formula (n+2)) (P x y a b : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (uniquenessSentence R P x y a b)) :=
  ModelTransfer.derives (fun _ hM => uniqueness_models R P x y a b hM)

end PPAC.Migration.ForcingAtomicGraphs
