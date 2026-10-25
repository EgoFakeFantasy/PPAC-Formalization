/- Exact recursive membership and equality equations from pinned AtomicForcing.
Conditions are internal codes in P, with a formula-defined order R. Identification
with the source condition presentation is a later adapter; no arbitrary external
class condition domain is claimed. The graph witnesses have been constructed,
not assumed. Every name is an arbitrary internal set, without a rank bound. -/
import PPAC.Migration.ForcingAtomicRecursion

namespace PPAC.Migration.ForcingAtomicRelations
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open ForcingAtomicGraphs (Lookup Good Value)
open ForcingAtomicStep (Query)
open ForcingMapConditions (MapRel)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def forces {n m : Nat} (equality : Bool) (R : Formula (n+2)) (rho : Fin n → Fin m) (P x y p : Fin m) : Formula m :=
  .ex ((ForcingAtomicGraphs.good R (paramsUp rho) P.castSucc (Fin.last m)).conj
    (ForcingAtomicStep.query equality (Fin.last m) x.castSucc y.castSucc p.castSucc))

def Forces {n : Nat} (equality : Bool) (R : Formula (n+2)) (params : Fin n → M.Carrier .set)
    (P x y p : M.Carrier .set) : Prop := ∃ g, Good R params P g ∧ Query equality g x y p

theorem forces_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (equality : Bool) (R : Formula (n+2))
    (rho : Fin n → Fin m) (P x y p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (forces equality R rho P x y p) ↔
      Forces equality R (fun i => v (rho i)) (v P) (v x) (v y) (v p) := by
  simp only [forces,Forces,Formula.Realize,ForcingAtomicGraphs.good_semantics (M := M),
    ForcingAtomicStep.query_semantics (M := M),paramsUp,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem query_iff_forces (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P g x y p : M.Carrier .set}
    (hg : Good R params P g) (hc : ∃ output, Lookup g x y output) (equality : Bool) :
    Query equality g x y p ↔ Forces equality R params P x y p := by
  constructor
  · intro h
    exact ⟨g,hg,h⟩
  · rintro ⟨h,hh,hquery⟩
    have hcover : ∃ output, Lookup h x y output := by
      obtain ⟨a,b,⟨key,value,hkey,_,he⟩,_⟩ := hquery
      exact ⟨value,key,hkey,he⟩
    have ha := ForcingAtomicGraphs.lookup_agreement hc hcover (ForcingAtomicGraphs.compatible hM hg hh x y)
    exact (ForcingAtomicStep.query_congr equality (ForcingAtomicGraphs.row_congr ha)).mpr hquery

theorem query_at_value (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P g x y output a b p : M.Carrier .set}
    (hg : Good R params P g) (hv : Lookup g x y output) (hc : PureKuratowski.Code M output a b) (equality : Bool) :
    Query equality g x y p ↔ (Definitional.Project.FirstOrderSemantics.reduct M).mem p (if equality then b else a) := by
  constructor
  · rintro ⟨c,d,⟨key,value,hkey,hcode,he⟩,hp⟩
    have hv' : Lookup g x y value := ⟨key,hkey,he⟩
    have h : output = value := ForcingAtomicGraphs.compatible hM hg hg x y output value hv hv'
    subst value
    obtain ⟨ha,hb⟩ := PureKuratowski.code_injective hcode hc
    subst c
    subst d
    exact hp
  · intro hp
    obtain ⟨key,hkey,he⟩ := hv
    exact ⟨a,b,⟨key,output,hkey,hc,he⟩,hp⟩

def memClause {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (P x y p : Fin m) : Formula m :=
  let up : Fin m → Fin (m+4) := fun i => i.castSucc.castSucc.castSucc.castSucc
  let q := (Fin.last m).castSucc.castSucc.castSucc
  let s := (Fin.last (m+1)).castSucc.castSucc
  let nu := (Fin.last (m+2)).castSucc
  let r := Fin.last (m+3)
  .all ((Formula.mem (Fin.last m) P.castSucc).imp
    ((ReplacementPredicates.rel R (paramsUp rho) (Fin.last m) p.castSucc).imp
      (.ex (.ex (.ex ((Formula.mem s (up P)).conj
        ((ReplacementPredicates.rel R (fun i => up (rho i)) s q).conj
          ((Formula.mem r (up P)).conj ((Source.SetLanguage.edge (up y) nu r).conj
            ((ReplacementPredicates.rel R (fun i => up (rho i)) s r).conj
              (forces true R (fun i => up (rho i)) (up P) (up x) nu s)))))))))))

def MemClause {n : Nat} (R : Formula (n+2)) (params : Fin n → M.Carrier .set) (P x y p : M.Carrier .set) : Prop :=
  ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R params q p →
    ∃ s nu r, (Definitional.Project.FirstOrderSemantics.reduct M).mem s P ∧ MapRel R params s q ∧
      (Definitional.Project.FirstOrderSemantics.reduct M).mem r P ∧ PureKuratowski.PairMember M nu r y ∧
        MapRel R params s r ∧ Forces true R params P x nu s

def eqHalf {n m : Nat} (R : Formula (n+2)) (rho : Fin n → Fin m) (P x y p : Fin m) : Formula m :=
  .all (.all ((Formula.mem (Fin.last (m+1)) P.castSucc.castSucc).imp
    ((Source.SetLanguage.edge x.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
      (.all ((Formula.mem (Fin.last (m+2)) P.castSucc.castSucc.castSucc).imp
        ((ReplacementPredicates.rel R (fun i => (rho i).castSucc.castSucc.castSucc)
          (Fin.last (m+2)) p.castSucc.castSucc.castSucc).imp
          ((ReplacementPredicates.rel R (fun i => (rho i).castSucc.castSucc.castSucc)
            (Fin.last (m+2)) (Fin.last (m+1)).castSucc).imp
            (forces false R (fun i => (rho i).castSucc.castSucc.castSucc) P.castSucc.castSucc.castSucc
              (Fin.last m).castSucc.castSucc y.castSucc.castSucc.castSucc (Fin.last (m+2))))))))))

def EqHalf {n : Nat} (R : Formula (n+2)) (params : Fin n → M.Carrier .set) (P x y p : M.Carrier .set) : Prop :=
  ∀ nu r, (Definitional.Project.FirstOrderSemantics.reduct M).mem r P → PureKuratowski.PairMember M nu r x →
    ∀ q, (Definitional.Project.FirstOrderSemantics.reduct M).mem q P → MapRel R params q p →
      MapRel R params q r → Forces false R params P nu y q

theorem memClause_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (R : Formula (n+2))
    (rho : Fin n → Fin m) (P x y p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (memClause R rho P x y p) ↔
      MemClause R (fun i => v (rho i)) (v P) (v x) (v y) (v p) := by
  simp only [memClause,MemClause,Formula.Realize,KuratowskiZF.source_edge,
    ForcingMapConditions.rel_semantics (M := M),forces_semantics (M := M),paramsUp,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem eqHalf_semantics {n m : Nat} (v : Fin m → M.Carrier .set) (R : Formula (n+2))
    (rho : Fin n → Fin m) (P x y p : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (eqHalf R rho P x y p) ↔
      EqHalf R (fun i => v (rho i)) (v P) (v x) (v y) (v p) := by
  simp only [eqHalf,EqHalf,Formula.Realize,KuratowskiZF.source_edge,
    ForcingMapConditions.rel_semantics (M := M),forces_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

theorem memBody_iff (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P g x y p : M.Carrier .set}
    (hg : Good R params P g)
    (hc : ∀ nu r, PureKuratowski.PairMember M nu r y → ∃ output, Lookup g x nu output) :
    ForcingAtomicStep.MemBody R params P g x y p ↔ MemClause R params P x y p := by
  constructor
  · intro h q hq hqp
    obtain ⟨s,nu,r,hs,hsq,hr,hy,hsr,hforce⟩ := h q hq hqp
    exact ⟨s,nu,r,hs,hsq,hr,hy,hsr,(query_iff_forces hM hg (hc nu r hy) true).mp hforce⟩
  · intro h q hq hqp
    obtain ⟨s,nu,r,hs,hsq,hr,hy,hsr,hforce⟩ := h q hq hqp
    exact ⟨s,nu,r,hs,hsq,hr,hy,hsr,(query_iff_forces hM hg (hc nu r hy) true).mpr hforce⟩

theorem eqHalf_iff (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    {R : Formula (n+2)} {params : Fin n → M.Carrier .set} {P g x y p : M.Carrier .set}
    (hg : Good R params P g)
    (hc : ∀ nu r, PureKuratowski.PairMember M nu r x → ∃ output, Lookup g nu y output) :
    ForcingAtomicStep.EqHalf R params P g x y p ↔ EqHalf R params P x y p := by
  constructor
  · intro h nu r hr hx q hq hqp hqr
    exact (query_iff_forces hM hg (hc nu r hx) false).mp (h nu r hr hx q hq hqp hqr)
  · intro h nu r hr hx q hq hqp hqr
    exact (query_iff_forces hM hg (hc nu r hx) false).mpr (h nu r hr hx q hq hqp hqr)

theorem mem_iff (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Formula (n+2)) (params : Fin n → M.Carrier .set) (P x y p : M.Carrier .set) :
    Forces false R params P x y p ↔
      (Definitional.Project.FirstOrderSemantics.reduct M).mem p P ∧ MemClause R params P x y p := by
  obtain ⟨output,g,hg,hv⟩ := ForcingAtomicRecursion.exists_value hM R params P x y
  obtain ⟨hc,a,b,hcode,ha,_⟩ := hg x y output hv
  exact (query_iff_forces hM hg ⟨output,hv⟩ false).symm.trans
    ((query_at_value hM hg hv hcode false).trans ((ha p).trans (and_congr Iff.rfl (memBody_iff hM hg hc.2.1))))

theorem eq_iff (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (R : Formula (n+2)) (params : Fin n → M.Carrier .set) (P x y p : M.Carrier .set) :
    Forces true R params P x y p ↔
      (Definitional.Project.FirstOrderSemantics.reduct M).mem p P ∧
        EqHalf R params P x y p ∧ EqHalf R params P y x p := by
  obtain ⟨output,g,hg,hv⟩ := ForcingAtomicRecursion.exists_value hM R params P x y
  obtain ⟨hc,a,b,hcode,_,hb⟩ := hg x y output hv
  exact (query_iff_forces hM hg ⟨output,hv⟩ true).symm.trans
    ((query_at_value hM hg hv hcode true).trans ((hb p).trans
      (and_congr Iff.rfl (and_congr (eqHalf_iff hM hg hc.1) (eqHalf_iff hM hg hc.2.2)))))

def membershipSentence {n : Nat} (R : Formula (n+2)) (P x y p : Fin n) : Source.Sentence :=
  ((forces false R id P x y p).iff ((Formula.mem p P).conj (memClause R id P x y p))).close

def equalitySentence {n : Nat} (R : Formula (n+2)) (P x y p : Fin n) : Source.Sentence :=
  ((forces true R id P x y p).iff ((Formula.mem p P).conj
    ((eqHalf R id P x y p).conj (eqHalf R id P y x p)))).close

theorem membership_models {n : Nat} (R : Formula (n+2)) (P x y p : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (membershipSentence R P x y p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v
  have h := (forces_semantics (M := M) v false R id P x y p).trans
    ((mem_iff hM R v (v P) (v x) (v y) (v p)).trans
      (and_congr Iff.rfl (memClause_semantics (M := M) v R id P x y p).symm))
  exact ⟨h.mp,h.mpr⟩

theorem equality_models {n : Nat} (R : Formula (n+2)) (P x y p : Fin n)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (equalitySentence R P x y p)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v
  have h := (forces_semantics (M := M) v true R id P x y p).trans
    ((eq_iff hM R v (v P) (v x) (v y) (v p)).trans
      (and_congr Iff.rfl (and_congr (eqHalf_semantics (M := M) v R id P x y p).symm
        (eqHalf_semantics (M := M) v R id P y x p).symm)))
  exact ⟨h.mp,h.mpr⟩

theorem membership_kernel_certificate {n : Nat} (R : Formula (n+2)) (P x y p : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (membershipSentence R P x y p)) :=
  ModelTransfer.derives (fun _ hM => membership_models R P x y p hM)

theorem equality_kernel_certificate {n : Nat} (R : Formula (n+2)) (P x y p : Fin n) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (equalitySentence R P x y p)) :=
  ModelTransfer.derives (fun _ hM => equality_models R P x y p hM)

end PPAC.Migration.ForcingAtomicRelations
