/- Pinned SliceGeometry.SliceData.slice/B/occurrence/Ypart/Spart.
Reuse actual ordered-pair names, the existing formula front end, literal
child selection and internal least occurrence. No given slice-correctness
structure or simultaneous family of defaults is introduced. -/
import PPAC.Migration.ForcingSliceSelection

namespace PPAC.Migration.ForcingSliceGeometry
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args1 args2 args3)
open ForcingMapConditions (MapRel)
open ForcingAtomicRelations (Forces)
open ForcingFormula (Force)
open ForcingClassEvaluation (Predicate)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingPairUnion (domain domain_semantics)
open ForcingHS (HS)
open ForcingSupportedNames (Supported)
open ForcingOrderedPairName (OrderedPairName)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 400000
universe u v v2
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Finite SOURCE parameter tuple; never an object-theory choice function. -/
def four {a : Type v} (s A X ci : a) : Fin 4 → a := Fin.cases s (args3 A X ci)

private theorem four_map {a : Type v} {b : Type u} (g : a → b) (s A X ci : a) :
    (fun j => g (four s A X ci j)) = four (g s) (g A) (g X) (g ci) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t)))) j

private theorem five_map {α : Type v} {β : Type v2} (f : α → β) (a b c d e : α) :
    (fun j => f (ForcingMapCalculus.five a b c d e j)) = ForcingMapCalculus.five (f a) (f b) (f c) (f d) (f e) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))))) j

private theorem args3_map {α : Type v} {β : Type v2} (f : α → β) (a b c : α) :
    (fun j => f (args3 a b c j)) = args3 (f a) (f b) (f c) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i))) j

/-- The existing forcing-formula front end with one queried name. -/
def unaryOf {k n : Nat} (rho : Fin 7 → Fin k) (G F mul : Fin k)
    (names : Fin n → Fin k) (phi : Formula (n+1)) : Formula (k+2) :=
  let b : Fin k → Fin (k+2) := fun j => j.castSucc.castSucc
  ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) b
    (Fin.lastCases (Fin.last (k+1)) (fun j => b (names j))) (b (rho 6)) (Fin.last k).castSucc phi

theorem unaryOf_semantics {k n : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul : Fin k) (names : Fin n → Fin k) (phi : Formula (n+1)) (p x : M.Carrier .set) :
    MapRel (unaryOf rho G F mul names phi) env p x ↔
      Force (orderFormula (rho 0) mul) (domain rho G F) env
        (Fin.lastCases x (fun j => env (names j))) (env (rho 6)) p phi := by
  unfold MapRel unaryOf
  rw [ForcingFormula.formula_semantics]
  simp only [Fin.lastCases_last,Fin.lastCases_castSucc]
  have hv : (fun j => Fin.lastCases x (Fin.lastCases p env)
      (Fin.lastCases (Fin.last (k+1)) (fun j => (names j).castSucc.castSucc) j)) =
      Fin.lastCases x (fun j => env (names j)) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp only [Fin.lastCases_last,Fin.lastCases_castSucc]
  rw [hv]

/-- Actual source formula symmetry discharges the unary selector movement. -/
theorem construct_formula_selection (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F S mul X : Fin k)
    (names : Fin n → Fin k) (phi : Formula (n+1))
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hS : ForcingConjugationGraph.Subgroup (env I) (env G) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env F))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hFixX : Supported (fun j => env (rho j)) (env S) (env X))
    (hFixed : ∀ j, Supported (fun j => env (rho j)) (env S) (env (names j))) :
    ∃ name, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
      Supported (fun j => env (rho j)) (env S) name ∧
      ForcingSliceSelection.Selected (orderFormula (rho 0) mul) (unaryOf rho G F mul names phi)
        env (env (rho 6)) (env X) name := by
  apply ForcingSliceSelection.construct hM (unaryOf rho G F mul names phi) env rho
    I K B w G F S mul X hPres hG hF hS hSF hX hFixX
  intro pi hpi act hAct p q x x' hp hpq _hx hxx hQ
  apply (unaryOf_semantics env rho G F mul names phi q x').mpr
  apply (ForcingSeparation.symmetry hM env rho G F mul hPres hG hF
    ((hG pi).mp (hS.1 pi hpi)) hAct phi
    (Fin.lastCases x (fun j => env (names j))) (Fin.lastCases x' (fun j => env (names j)))
    (by
      intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [Fin.lastCases_last] using hxx
      · simpa only [Fin.lastCases_castSucc] using hFixed i pi hpi act hAct) hp hpq).mp
  exact (unaryOf_semantics env rho G F mul names phi p x).mp hQ

private theorem app_congr (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p f g x x' y y' : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hf : Forces true R env P f g p) (hx : Forces true R env P x x' p) (hy : Forces true R env P y y' p)
    (hh : Force R H env (args3 f x y) P p (Source.SetLanguage.edge 0 1 2)) :
    Force R H env (args3 g x' y') P p (Source.SetLanguage.edge 0 1 2) := by
  apply (ForcingFormula.tuple_congr hM hpre (Source.SetLanguage.edge 0 1 2) _ _ p hp ?_).mp hh
  intro j
  exact Fin.cases hf (Fin.cases hx (Fin.cases hy (fun i => Fin.elim0 i))) j

/-- Parameters s,A,X,check(i), then a,x. The pair binder denotes the genuine
ordered pair formula; the equivalence with the literal name is proved below. -/
def sliceFormula : Formula 6 :=
  (Formula.mem 4 1).conj ((Formula.mem 5 2).conj
    (.ex ((Source.SetLanguage.orderedPair 6 4 3).conj (Source.SetLanguage.edge 0 6 5))))

private def sliceSwap : Fin 6 → Fin 6 :=
  Fin.cases 0 (Fin.cases 1 (Fin.cases 2 (Fin.cases 3 (Fin.cases 5 (Fin.cases 4 (fun t => Fin.elim0 t))))))

/-- Source BinaryRelation.image of exactly the Cartesian slice, not a
different approximation to the image. The HS input witness is internally bound. -/
def bFormula : Formula 5 := .ex (sliceFormula.rename sliceSwap)

def BPredicate {k : Nat} (rho : Fin 7 → Fin k) (G F mul s A X ci : Fin k) : Formula (k+2) :=
  unaryOf rho G F mul (four s A X ci) bFormula

private theorem swap_values (s A X ci x a : M.Carrier .set) :
    (fun j => Fin.lastCases a (Fin.lastCases x (four s A X ci)) (sliceSwap j)) =
      Fin.lastCases x (Fin.lastCases a (four s A X ci)) := by
  funext j
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun t => Fin.elim0 t)))))) j
  all_goals rfl

theorem b_force_dense (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p s A X ci x : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P) :
    Force R H env (Fin.lastCases x (four s A X ci)) P p bFormula ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p → ∃ r,
        (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧
          ∃ a, Predicate H env a ∧ Force R H env (Fin.lastCases x (Fin.lastCases a (four s A X ci))) P r sliceFormula := by
  change (∀ q, _ → _ → ∃ r, _ ∧ _ ∧ ∃ a, _ ∧
    Force R H env (Fin.lastCases a (Fin.lastCases x (four s A X ci))) P r (sliceFormula.rename sliceSwap)) ↔ _
  constructor
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,a,ha,hSlice⟩ := h q hq hqp
    exact ⟨r,hr,hrq,a,ha,by
      rw [ForcingSound.rename hM hpre _ _ _ _ hr,swap_values] at hSlice
      exact hSlice⟩
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,a,ha,hSlice⟩ := h q hq hqp
    exact ⟨r,hr,hrq,a,ha,by
      rw [ForcingSound.rename hM hpre _ _ _ _ hr,swap_values]
      exact hSlice⟩

/-- The source slice uses the literal ordered-pair NAME. Existential object
pair witnesses in sliceFormula give exactly the same relation, at every
internal condition; no equality or application law is assumed. -/
theorem slice_force_iff (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w top s A X ci a x pair p : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F)) (ht : ForcingWithTopCarrier.Empty top)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (ha : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) a)
    (hCi : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) ci)
    (hPair : OrderedPairName top a ci pair)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env
      (Fin.lastCases x (Fin.lastCases a (four s A X ci))) (env (rho 6)) p sliceFormula ↔
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) a A p ∧
        Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x X p ∧
        Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 s pair x)
          (env (rho 6)) p (Source.SetLanguage.edge 0 1 2) := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  let values : Fin 6 → M.Carrier .set := Fin.lastCases x (Fin.lastCases a (four s A X ci))
  have hPairHS := ForcingOrderedPairName.orderedPair_hs hM (fun j => env (rho j)) hPres hG hF ht ha hCi hPair
  change (Forces false R env W a A p ∧ Forces false R env W x X p ∧
    (∀ q, (Project.FirstOrderSemantics.reduct M).mem q W → MapRel R env q p → ∃ r,
      (Project.FirstOrderSemantics.reduct M).mem r W ∧ MapRel R env r q ∧ ∃ candidate,
        Predicate H env candidate ∧
        Force R H env (Fin.lastCases candidate values) W r (Source.SetLanguage.orderedPair 6 4 3) ∧
        Force R H env (Fin.lastCases candidate values) W r (Source.SetLanguage.edge 0 6 5))) ↔ _
  constructor
  · rintro ⟨haA,hxX,h⟩
    refine ⟨haA,hxX,?_⟩
    apply ForcingFormula.of_dense hM hpre (Source.SetLanguage.edge 0 1 2) (args3 s pair x) hp
    intro q hq hqp
    obtain ⟨r,hr,hrq,candidate,hCandidate,hPairF,hApp⟩ := h q hq hqp
    let vv : Fin 7 → M.Carrier .set := Fin.lastCases candidate values
    have e6 : vv 6 = candidate := by simp only [vv,show (6 : Fin 7) = Fin.last 6 from rfl,Fin.lastCases_last]
    have e4 : vv 4 = a := by simp only [vv,values,show (4 : Fin 7) = (Fin.last 4).castSucc.castSucc from rfl,Fin.lastCases_last,Fin.lastCases_castSucc]
    have e3 : vv 3 = ci := by rfl
    have hEq := (ForcingPairFormula.forces_orderedPair (m := 7) hM env rho G F mul vv (6 : Fin 7) 4 3 hPres hG hF ht hpre
      (by simpa only [e6] using (domain_semantics env rho G F candidate).mp hCandidate)
      (by simpa only [e4] using ha) (by simpa only [e3] using hCi)
      (by simpa only [e4,e3] using hPair) hr).mp hPairF
    have hEq' : Forces true R env W candidate pair r := by simpa only [e6] using hEq
    have e0 : vv 0 = s := by rfl
    have e5 : vv 5 = x := by simp only [vv,values,show (5 : Fin 7) = (Fin.last 5).castSucc from rfl,Fin.lastCases_last,Fin.lastCases_castSucc]
    have hAppSmall := (ForcingRelationClass.edge_formula (H := H) (n := 7) hM hpre hr vv (0 : Fin 7) 6 5).mp hApp
    have hApp' : Force R H env (args3 s candidate x) W r (Source.SetLanguage.edge 0 1 2) := by
      simpa only [e0,e6,e5] using hAppSmall
    exact ⟨r,hr,hrq,app_congr hM hpre hr (ForcingAtomicBasic.eq_refl hM hpre s r hr)
      hEq' (ForcingAtomicBasic.eq_refl hM hpre x r hr) hApp'⟩
  · rintro ⟨haA,hxX,hApp⟩
    refine ⟨haA,hxX,?_⟩
    intro q hq hqp
    refine ⟨q,hq,hpre.1 q hq,pair,(domain_semantics env rho G F pair).mpr hPairHS,?_,?_⟩
    · let vv : Fin 7 → M.Carrier .set := Fin.lastCases pair values
      have e6 : vv 6 = pair := by simp only [vv,show (6 : Fin 7) = Fin.last 6 from rfl,Fin.lastCases_last]
      have e4 : vv 4 = a := by simp only [vv,values,show (4 : Fin 7) = (Fin.last 4).castSucc.castSucc from rfl,Fin.lastCases_last,Fin.lastCases_castSucc]
      have e3 : vv 3 = ci := by rfl
      apply (ForcingPairFormula.forces_orderedPair (m := 7) hM env rho G F mul vv (6 : Fin 7) 4 3 hPres hG hF ht hpre
        (by simpa only [e6] using hPairHS) (by simpa only [e4] using ha) (by simpa only [e3] using hCi)
        (by simpa only [e4,e3] using hPair) hq).mpr
      simpa only [e6] using ForcingAtomicBasic.eq_refl hM hpre pair q hq
    · let vv : Fin 7 → M.Carrier .set := Fin.lastCases pair values
      have e0 : vv 0 = s := by rfl
      have e6 : vv 6 = pair := by simp only [vv,show (6 : Fin 7) = Fin.last 6 from rfl,Fin.lastCases_last]
      have e5 : vv 5 = x := by simp only [vv,values,show (5 : Fin 7) = (Fin.last 5).castSucc from rfl,Fin.lastCases_last,Fin.lastCases_castSucc]
      apply (ForcingRelationClass.edge_formula (H := H) (n := 7) hM hpre hq vv (0 : Fin 7) 6 5).mpr
      simpa only [e0,e6,e5] using
        ForcingFormula.mono hM hpre (Source.SetLanguage.edge 0 1 2) (args3 s pair x) hp hq hqp hApp

/-- Source B is the actual collected image of this slice. The check name is
fixed for EVERY ground index, so the same support works before choosing i. -/
theorem construct_B (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F S mul top s A X ci : Fin k)
    {i : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hS : ForcingConjugationGraph.Subgroup (env I) (env G) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hFixS : Supported (fun j => env (rho j)) (env S) (env s))
    (hFixA : Supported (fun j => env (rho j)) (env S) (env A))
    (hFixX : Supported (fun j => env (rho j)) (env S) (env X))
    (hCi : ForcingCheckName.Checked (env top) i (env ci)) :
    ∃ name, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
      Supported (fun j => env (rho j)) (env S) name ∧
      ForcingSliceSelection.Selected (orderFormula (rho 0) mul) (BPredicate rho G F mul s A X ci)
        env (env (rho 6)) (env X) name := by
  have hFixCi : Supported (fun j => env (rho j)) (env S) (env ci) := by
    intro pi _hpi act hAct
    exact ForcingLabelNames.checked_fixed hM (fun j => env (rho j)) hPres ht
      ((mapRel_action _ _ _).mp hAct) hCi
  apply construct_formula_selection hM env rho I K B w G F S mul X (four s A X ci) bFormula
    hPres hG hF hS hSF hX hFixX
  intro j
  exact Fin.cases hFixS (Fin.cases hFixA (Fin.cases hFixX (Fin.cases hFixCi (fun t => Fin.elim0 t)))) j

/-- Source mem_select for a forcing-defined predicate. Monotonicity,
regularity and equality invariance are discharged by the existing front end. -/
theorem mem_formula_selection (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul X : Fin k)
    (names : Fin n → Fin k) (phi : Formula (n+1)) {name nu p : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hNu : Predicate (domain rho G F) env nu)
    (hName : ForcingSliceSelection.Selected (orderFormula (rho 0) mul) (unaryOf rho G F mul names phi)
      env (env (rho 6)) (env X) name)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu name p ↔
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu (env X) p ∧
        Force (orderFormula (rho 0) mul) (domain rho G F) env
          (Fin.lastCases nu (fun j => env (names j))) (env (rho 6)) p phi := by
  rw [ForcingSliceSelection.mem_selected hM hpre hName
    (fun child c he => (domain_semantics env rho G F child).mpr (ForcingHS.child hX he)) hNu
    (by
      intro a b x ha hb hba _hx hh
      exact (unaryOf_semantics env rho G F mul names phi b x).mpr
        (ForcingFormula.mono hM hpre phi _ ha hb hba ((unaryOf_semantics env rho G F mul names phi a x).mp hh)))
    (by
      intro a x y _hx _hy he
      rw [unaryOf_semantics,unaryOf_semantics]
      apply ForcingFormula.tuple_congr hM hpre phi _ _ a (ForcingAtomicBasic.condition hM he)
      intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa only [Fin.lastCases_last] using he
      · simpa only [Fin.lastCases_castSucc] using ForcingAtomicBasic.eq_refl hM hpre
          (env (names i)) a (ForcingAtomicBasic.condition hM he))
    (by
      intro a x ha _hx hd
      apply (unaryOf_semantics env rho G F mul names phi a x).mpr
      apply ForcingFormula.of_dense hM hpre phi _ ha
      intro b hb hba
      obtain ⟨c,hc,hcb,hQ⟩ := hd b hb hba
      exact ⟨c,hc,hcb,(unaryOf_semantics env rho G F mul names phi c x).mp hQ⟩) hp,
    unaryOf_semantics]

theorem slice_mem_X {k : Nat} {R : Formula (k+2)} {H : Formula (k+1)}
    {env : Fin k → M.Carrier .set} {P p s A X ci a x : M.Carrier .set}
    (h : Force R H env (Fin.lastCases x (Fin.lastCases a (four s A X ci))) P p sliceFormula) :
    Forces false R env P x X p := by
  change _ ∧ Forces false R env P x X p ∧ _ at h
  exact h.2.1

/-- Exact source mem_B: the image already implies membership in X, so no
extra membership restriction survives in the result. -/
theorem mem_B (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul s A X ci : Fin k)
    {name nu p : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hNu : Predicate (domain rho G F) env nu)
    (hName : ForcingSliceSelection.Selected (orderFormula (rho 0) mul) (BPredicate rho G F mul s A X ci)
      env (env (rho 6)) (env X) name)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu name p ↔
      Force (orderFormula (rho 0) mul) (domain rho G F) env
        (Fin.lastCases nu (four (env s) (env A) (env X) (env ci))) (env (rho 6)) p bFormula := by
  rw [mem_formula_selection hM env rho G F mul X (four s A X ci) bFormula hpre hX hNu hName hp,four_map]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨ForcingAtomicBasic.mem_of_dense hM hpre hp ?_,h⟩
    intro q hq hqp
    obtain ⟨r,hr,hrq,a,_ha,hSlice⟩ := (b_force_dense hM hpre).mp h q hq hqp
    exact ⟨r,hr,hrq,slice_mem_X hSlice⟩

private def bOccurrenceSlots : Fin 5 → Fin 8 :=
  Fin.cases 1 (Fin.cases 2 (Fin.cases 3 (Fin.cases 5 (Fin.cases 7 (fun t => Fin.elim0 t)))))

/-- Fixed parents [f,s,A,X,Y], then check(i),y. B-membership is expanded
by the proved mem_B equation; this selects no auxiliary family of B names. -/
def occurrenceFormula : Formula 7 :=
  .ex ((bFormula.rename bOccurrenceSlots).conj
    ((Formula.mem 6 4).conj (Source.SetLanguage.edge 0 7 6)))

def occurrence {k : Nat} (rho : Fin 7 → Fin k) (G F mul top f s A X Y : Fin k) : Formula (k+3) :=
  ForcingLeastRelation.occurrence rho G F mul top (ForcingMapCalculus.five f s A X Y) occurrenceFormula

private theorem b_occurrence_values (f s A X Y ci y x : M.Carrier .set) :
    (fun j => Fin.lastCases x (Fin.lastCases y (Fin.lastCases ci (ForcingMapCalculus.five f s A X Y)))
      (bOccurrenceSlots j)) = Fin.lastCases x (four s A X ci) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t))))) j

theorem occurrence_force_dense (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p f s A X Y ci y : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P) :
    Force R H env (Fin.lastCases y (Fin.lastCases ci (ForcingMapCalculus.five f s A X Y))) P p occurrenceFormula ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p → ∃ r,
        (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧ ∃ x,
          Predicate H env x ∧ Force R H env (Fin.lastCases x (four s A X ci)) P r bFormula ∧
            Forces false R env P y Y r ∧ Force R H env (args3 f x y) P r (Source.SetLanguage.edge 0 1 2) := by
  let values : Fin 7 → M.Carrier .set := Fin.lastCases y (Fin.lastCases ci (ForcingMapCalculus.five f s A X Y))
  change (∀ q, _ → _ → ∃ r, _ ∧ _ ∧ ∃ x, _ ∧
    Force R H env (Fin.lastCases x values) P r (bFormula.rename bOccurrenceSlots) ∧
    Forces false R env P y Y r ∧
    Force R H env (Fin.lastCases x values) P r (Source.SetLanguage.edge 0 7 6)) ↔ _
  have hB (x r : M.Carrier .set) (hr : (Project.FirstOrderSemantics.reduct M).mem r P) :
      Force R H env (Fin.lastCases x values) P r (bFormula.rename bOccurrenceSlots) ↔
        Force R H env (Fin.lastCases x (four s A X ci)) P r bFormula := by
    rw [ForcingSound.rename hM hpre _ _ _ _ hr,b_occurrence_values]
  have hApp (x r : M.Carrier .set) (hr : (Project.FirstOrderSemantics.reduct M).mem r P) :
      Force R H env (Fin.lastCases x values) P r (Source.SetLanguage.edge 0 7 6) ↔
        Force R H env (args3 f x y) P r (Source.SetLanguage.edge 0 1 2) := by
    let vv : Fin 8 → M.Carrier .set := Fin.lastCases x values
    have e0 : vv 0 = f := by rfl
    have e7 : vv 7 = x := by simp only [vv,show (7 : Fin 8) = Fin.last 7 from rfl,Fin.lastCases_last]
    have e6 : vv 6 = y := by simp only [vv,values,show (6 : Fin 8) = (Fin.last 6).castSucc from rfl,Fin.lastCases_last,Fin.lastCases_castSucc]
    simpa only [e0,e7,e6] using ForcingRelationClass.edge_formula (H := H) (n := 8) hM hpre hr vv (0 : Fin 8) 7 6
  constructor
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,x,hx,hB',hy,hApp'⟩ := h q hq hqp
    exact ⟨r,hr,hrq,x,hx,(hB x r hr).mp hB',hy,(hApp x r hr).mp hApp'⟩
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,x,hx,hB',hy,hApp'⟩ := h q hq hqp
    exact ⟨r,hr,hrq,x,hx,(hB x r hr).mpr hB',hy,(hApp x r hr).mpr hApp'⟩

/-- Actual source occurrence = image of boundedApp f B_i Y. Only the
existing exact B constructor equation is consumed; no occurrence oracle. -/
theorem occurrence_iff_B (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top f s A X Y ci : Fin k)
    {i name p y : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hCi : ForcingCheckName.Checked (env top) i (env ci))
    (hName : ForcingSliceSelection.Selected (orderFormula (rho 0) mul) (BPredicate rho G F mul s A X ci)
      env (env (rho 6)) (env X) name) :
    ForcingRelationGraphForcing.Holds (occurrence rho G F mul top f s A X Y) env p y i ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
        MapRel (orderFormula (rho 0) mul) env q p → ∃ r,
          (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) ∧
          MapRel (orderFormula (rho 0) mul) env r q ∧ ∃ x, Predicate (domain rho G F) env x ∧
            Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x name r ∧
            Forces false (orderFormula (rho 0) mul) env (env (rho 6)) y (env Y) r ∧
            Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) x y)
              (env (rho 6)) r (Source.SetLanguage.edge 0 1 2) := by
  rw [occurrence,ForcingLeastRelation.occurrence_semantics]
  have hValues : ForcingLeastRelation.values env (ForcingMapCalculus.five f s A X Y) (env ci) y =
      Fin.lastCases y (Fin.lastCases (env ci) (ForcingMapCalculus.five (env f) (env s) (env A) (env X) (env Y))) := by
    unfold ForcingLeastRelation.values
    rw [five_map]
  constructor
  · rintro ⟨checked,hChecked,hForce⟩
    have heq := ForcingCheckName.unique hM hChecked hCi
    subst checked
    rw [hValues] at hForce
    intro q hq hqp
    obtain ⟨r,hr,hrq,x,hx,hB,hy,hApp⟩ := (occurrence_force_dense hM hpre).mp hForce q hq hqp
    exact ⟨r,hr,hrq,x,hx,(mem_B hM env rho G F mul s A X ci hpre hX hx hName hr).mpr hB,hy,hApp⟩
  · intro h
    refine ⟨env ci,hCi,?_⟩
    rw [hValues]
    apply (occurrence_force_dense hM hpre).mpr
    intro q hq hqp
    obtain ⟨r,hr,hrq,x,hx,hB,hy,hApp⟩ := h q hq hqp
    exact ⟨r,hr,hrq,x,hx,(mem_B hM env rho G F mul s A X ci hpre hX hx hName hr).mp hB,hy,hApp⟩

/-- The genuine source least-occurrence predicate on an INTERNAL index i. -/
def YPredicate {k : Nat} (rho : Fin 7 → Fin k) (G F mul top O f s A X Y i : Fin k) : Formula (k+2) :=
  ForcingLeastOccurrence.atFormula (orderFormula (rho 0) mul) (occurrence rho G F mul top f s A X Y)
    (fun j => j.castSucc.castSucc) (rho 6).castSucc.castSucc O.castSucc.castSucc
    (Fin.last k).castSucc (Fin.last (k+1)) i.castSucc.castSucc

theorem yPredicate_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul top O f s A X Y i : Fin k) (p y : M.Carrier .set) :
    MapRel (YPredicate rho G F mul top O f s A X Y i) env p y ↔
      ForcingLeastOccurrence.At (orderFormula (rho 0) mul) (occurrence rho G F mul top f s A X Y)
        env (env (rho 6)) (env O) p y (env i) := by
  simp only [MapRel,YPredicate,ForcingLeastOccurrence.at_semantics,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem construct_Ypart (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F S mul top O f s A X Y i : Fin k)
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hS : ForcingConjugationGraph.Subgroup (env I) (env G) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
    (hFixY : Supported (fun j => env (rho j)) (env S) (env Y))
    (hFixed : ∀ j, Supported (fun j => env (rho j)) (env S) (env (ForcingMapCalculus.five f s A X Y j))) :
    ∃ name, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
      Supported (fun j => env (rho j)) (env S) name ∧
      ForcingSliceSelection.Selected (orderFormula (rho 0) mul) (YPredicate rho G F mul top O f s A X Y i)
        env (env (rho 6)) (env Y) name := by
  apply ForcingSliceSelection.construct hM (YPredicate rho G F mul top O f s A X Y i)
    env rho I K B w G F S mul Y hPres hG hF hS hSF hY hFixY
  intro pi hpi act hAct p q x x' hp hpq _hx hxx hAt
  apply (yPredicate_semantics env rho G F mul top O f s A X Y i q x').mpr
  exact ForcingLeastRelation.at_move hM env rho G F mul top O (ForcingMapCalculus.five f s A X Y)
    occurrenceFormula hPres hG hF ht ((hG pi).mp (hS.1 pi hpi)) hAct
    (fun j => hFixed j pi hpi act hAct) hp hpq hxx
    ((yPredicate_semantics env rho G F mul top O f s A X Y i p x).mp hAt)

private theorem occ_mono (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top f s A X Y : Fin k)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    {p q x i : M.Carrier .set} (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hq : (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)))
    (hqp : MapRel (orderFormula (rho 0) mul) env q p)
    (h : ForcingRelationGraphForcing.Holds (occurrence rho G F mul top f s A X Y) env p x i) :
    ForcingRelationGraphForcing.Holds (occurrence rho G F mul top f s A X Y) env q x i := by
  simp only [occurrence,ForcingLeastRelation.occurrence_semantics] at h ⊢
  exact ForcingLeastRelation.occurrence_mono hM env rho G F mul top (ForcingMapCalculus.five f s A X Y)
    occurrenceFormula hpre hp hq hqp h

private theorem occ_congr (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top f s A X Y : Fin k)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    {p x x' i : M.Carrier .set} (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (he : Forces true (orderFormula (rho 0) mul) env (env (rho 6)) x x' p) :
    ForcingRelationGraphForcing.Holds (occurrence rho G F mul top f s A X Y) env p x i ↔
      ForcingRelationGraphForcing.Holds (occurrence rho G F mul top f s A X Y) env p x' i := by
  simp only [occurrence,ForcingLeastRelation.occurrence_semantics]
  exact ForcingLeastRelation.occurrence_congr hM env rho G F mul top (ForcingMapCalculus.five f s A X Y)
    occurrenceFormula hpre hp he

private theorem occ_regular (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top f s A X Y : Fin k)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    {p x i : M.Carrier .set} (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (h : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
      MapRel (orderFormula (rho 0) mul) env q p → ∃ r,
        (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) ∧
        MapRel (orderFormula (rho 0) mul) env r q ∧
        ForcingRelationGraphForcing.Holds (occurrence rho G F mul top f s A X Y) env r x i) :
    ForcingRelationGraphForcing.Holds (occurrence rho G F mul top f s A X Y) env p x i := by
  rw [occurrence,ForcingLeastRelation.occurrence_semantics]
  apply ForcingLeastRelation.occurrence_regular hM env rho G F mul top (ForcingMapCalculus.five f s A X Y)
    occurrenceFormula hpre hp
  intro q hq hqp
  obtain ⟨r,hr,hrq,hh⟩ := h q hq hqp
  exact ⟨r,hr,hrq,(ForcingLeastRelation.occurrence_semantics env rho G F mul top
    (ForcingMapCalculus.five f s A X Y) occurrenceFormula r x i).mp hh⟩

theorem mem_Ypart (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top O f s A X Y i : Fin k)
    {name nu p : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
    (hNu : Predicate (domain rho G F) env nu)
    (hName : ForcingSliceSelection.Selected (orderFormula (rho 0) mul) (YPredicate rho G F mul top O f s A X Y i)
      env (env (rho 6)) (env Y) name)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) :
    Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu name p ↔
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu (env Y) p ∧
        ForcingLeastOccurrence.At (orderFormula (rho 0) mul) (occurrence rho G F mul top f s A X Y)
          env (env (rho 6)) (env O) p nu (env i) := by
  have hMono : ∀ j, (Project.FirstOrderSemantics.reduct M).mem j (env O) → ∀ a b,
      (Project.FirstOrderSemantics.reduct M).mem a (env (rho 6)) →
      (Project.FirstOrderSemantics.reduct M).mem b (env (rho 6)) →
      MapRel (orderFormula (rho 0) mul) env b a → ∀ x, Predicate (domain rho G F) env x →
      ForcingRelationGraphForcing.Holds (occurrence rho G F mul top f s A X Y) env a x j →
      ForcingRelationGraphForcing.Holds (occurrence rho G F mul top f s A X Y) env b x j := by
    intro j _hj a b ha hb hba x _hx hh
    exact occ_mono hM env rho G F mul top f s A X Y hpre ha hb hba hh
  rw [ForcingSliceSelection.mem_selected hM hpre hName
    (fun child c he => (domain_semantics env rho G F child).mpr (ForcingHS.child hY he)) hNu
    (by
      intro a b x ha hb hba hx hAt
      rw [yPredicate_semantics] at hAt ⊢
      exact ForcingLeastOccurrence.mono hpre hMono hx ha hb hba hAt)
    (by
      intro a x x' hx hx' he
      rw [yPredicate_semantics,yPredicate_semantics]
      exact ForcingLeastOccurrence.congr hM hpre
        (fun j _hj b hb y z _hy _hz heq => occ_congr hM env rho G F mul top f s A X Y hpre hb heq)
        hx hx' (ForcingAtomicBasic.condition hM he) he)
    (by
      intro a x ha hx hd
      rw [yPredicate_semantics]
      apply ForcingLeastOccurrence.regular hpre hMono
        (fun j _hj b hb y _hy hh => occ_regular hM env rho G F mul top f s A X Y hpre hb hh) hx ha
      intro b hb hba
      obtain ⟨c,hc,hcb,hAt⟩ := hd b hb hba
      exact ⟨c,hc,hcb,(yPredicate_semantics env rho G F mul top O f s A X Y i c x).mp hAt⟩) hp,
    yPredicate_semantics]

/-- Parameters f,B_i,Y_i, then x. Exact inverse-image of boundedApp. -/
def preimageFormula : Formula 4 :=
  .ex ((Formula.mem 3 1).conj ((Formula.mem 4 2).conj (Source.SetLanguage.edge 0 3 4)))

theorem preimage_force_dense (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p f B Y x : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P) :
    Force R H env (Fin.lastCases x (args3 f B Y)) P p preimageFormula ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p → ∃ r,
        (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧ ∃ y, Predicate H env y ∧
          Forces false R env P x B r ∧ Forces false R env P y Y r ∧
            Force R H env (args3 f x y) P r (Source.SetLanguage.edge 0 1 2) := by
  let values : Fin 4 → M.Carrier .set := Fin.lastCases x (args3 f B Y)
  change (∀ q, _ → _ → ∃ r, _ ∧ _ ∧ ∃ y, _ ∧ Forces false R env P x B r ∧
    Forces false R env P y Y r ∧
    Force R H env (Fin.lastCases y values) P r (Source.SetLanguage.edge 0 3 4)) ↔ _
  have hApp (y r : M.Carrier .set) (hr : (Project.FirstOrderSemantics.reduct M).mem r P) :
      Force R H env (Fin.lastCases y values) P r (Source.SetLanguage.edge 0 3 4) ↔
        Force R H env (args3 f x y) P r (Source.SetLanguage.edge 0 1 2) := by
    let vv : Fin 5 → M.Carrier .set := Fin.lastCases y values
    have e0 : vv 0 = f := by rfl
    have e3 : vv 3 = x := by simp only [vv,values,show (3 : Fin 5) = (Fin.last 3).castSucc from rfl,Fin.lastCases_last,Fin.lastCases_castSucc]
    have e4 : vv 4 = y := by simp only [vv,show (4 : Fin 5) = Fin.last 4 from rfl,Fin.lastCases_last]
    simpa only [e0,e3,e4] using ForcingRelationClass.edge_formula (H := H) (n := 5) hM hpre hr vv (0 : Fin 5) 3 4
  constructor
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,y,hy,hB,hY,hApp'⟩ := h q hq hqp
    exact ⟨r,hr,hrq,y,hy,hB,hY,(hApp y r hr).mp hApp'⟩
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,y,hy,hB,hY,hApp'⟩ := h q hq hqp
    exact ⟨r,hr,hrq,y,hy,hB,hY,(hApp y r hr).mpr hApp'⟩

/-- Directly reuse the already accepted parameter-value Separation and its
literal movement theorem. This gives the SAME support, without a new collector. -/
theorem construct_Spart (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w S f Bi Yi : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hS : ForcingConjugationGraph.Subgroup I (env G) S)
    (hf : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) f)
    (hBi : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) Bi)
    (hYi : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) Yi)
    (hFixf : Supported (fun j => env (rho j)) S f)
    (hFixBi : Supported (fun j => env (rho j)) S Bi)
    (hFixYi : Supported (fun j => env (rho j)) S Yi) :
    ∃ name, HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
      Supported (fun j => env (rho j)) S name ∧
      ForcingSeparation.Separated (orderFormula (rho 0) mul) (domain rho G F) env
        (args3 f Bi Yi) (env (rho 6)) Bi name preimageFormula := by
  obtain ⟨name,hName,hSep⟩ := ForcingSeparationAxiom.exists_at_values hM env rho G F mul hPres hG hF hBi
    (args3 f Bi Yi) (fun j => Fin.cases hf (Fin.cases hBi (Fin.cases hYi (fun t => Fin.elim0 t))) j) preimageFormula
  refine ⟨name,hName,?_,hSep⟩
  intro pi hpi act hAct
  exact ForcingRelationClassMove.separated_move hM env rho G F mul hPres hG hF
    ((hG pi).mp (hS.1 pi hpi)) hAct (ForcingHS.isName hBi) (ForcingHS.isName hName)
    (hFixBi pi hpi act hAct) (args3 f Bi Yi) (args3 f Bi Yi)
    (fun j => Fin.cases (hFixf pi hpi act hAct) (Fin.cases (hFixBi pi hpi act hAct)
      (Fin.cases (hFixYi pi hpi act hAct) (fun t => Fin.elim0 t))) j) preimageFormula hSep hSep

theorem mem_Spart (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P f Bi Yi name nu p : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hName : ForcingSeparation.Separated R H env (args3 f Bi Yi) P Bi name preimageFormula)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) :
    Forces false R env P nu name p ↔ Forces false R env P nu Bi p ∧
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p → ∃ r,
        (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧ ∃ y, Predicate H env y ∧
          Forces false R env P nu Bi r ∧ Forces false R env P y Yi r ∧
            Force R H env (args3 f nu y) P r (Source.SetLanguage.edge 0 1 2) := by
  rw [ForcingSeparationAxiom.mem_separate hM hpre hName hp,preimage_force_dense hM hpre]

theorem Ypart_disjoint (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top O f s A X Y i j : Fin k)
    {left right nu p : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hO : ForcingRawRank.Ordinal (env O))
    (hY : HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F) (env Y))
    (hNu : Predicate (domain rho G F) env nu)
    (hLeft : ForcingSliceSelection.Selected (orderFormula (rho 0) mul) (YPredicate rho G F mul top O f s A X Y i)
      env (env (rho 6)) (env Y) left)
    (hRight : ForcingSliceSelection.Selected (orderFormula (rho 0) mul) (YPredicate rho G F mul top O f s A X Y j)
      env (env (rho 6)) (env Y) right)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hl : Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu left p)
    (hr : Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu right p) : env i = env j :=
  ForcingLeastOccurrence.unique hM hO hpre hp
    ((mem_Ypart hM env rho G F mul top O f s A X Y i hpre hY hNu hLeft hp).mp hl).2
    ((mem_Ypart hM env rho G F mul top O f s A X Y j hpre hY hNu hRight hp).mp hr).2

/-- Three ACTUAL names, all fixed by the SAME support. The raw constructor
equations retain every internal child and condition, not only named instances. -/
def Pieces {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F S mul top O f s A X Y i ci : Fin k) : Prop :=
  ∃ Bi Yi Si,
    HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) Bi ∧
    Supported (fun j => env (rho j)) (env S) Bi ∧
    ForcingSliceSelection.Selected (orderFormula (rho 0) mul) (BPredicate rho G F mul s A X ci) env (env (rho 6)) (env X) Bi ∧
    HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) Yi ∧
    Supported (fun j => env (rho j)) (env S) Yi ∧
    ForcingSliceSelection.Selected (orderFormula (rho 0) mul) (YPredicate rho G F mul top O f s A X Y i) env (env (rho 6)) (env Y) Yi ∧
    HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) Si ∧
    Supported (fun j => env (rho j)) (env S) Si ∧
    ForcingSeparation.Separated (orderFormula (rho 0) mul) (domain rho G F) env
      (args3 (env f) Bi Yi) (env (rho 6)) Bi Si preimageFormula

theorem construct_pieces (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F S mul top O f s A X Y i ci : Fin k)
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hS : ForcingConjugationGraph.Subgroup (env I) (env G) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hf : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env f))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
    (hFixed : ∀ j, Supported (fun j => env (rho j)) (env S) (env (ForcingMapCalculus.five f s A X Y j)))
    (hCi : ForcingCheckName.Checked (env top) (env i) (env ci)) :
    Pieces env rho G F S mul top O f s A X Y i ci := by
  have hFixf : Supported (fun j => env (rho j)) (env S) (env f) := by
    simpa only [ForcingMapCalculus.five,Fin.cases_zero] using hFixed 0
  have hFixs : Supported (fun j => env (rho j)) (env S) (env s) := by
    simpa only [ForcingMapCalculus.five,Fin.cases_zero,Fin.cases_succ] using hFixed (Fin.succ 0)
  have hFixA : Supported (fun j => env (rho j)) (env S) (env A) := by
    simpa only [ForcingMapCalculus.five,args3,Fin.cases_zero,Fin.cases_succ] using hFixed (Fin.succ (Fin.succ 0))
  have hFixX : Supported (fun j => env (rho j)) (env S) (env X) := by
    simpa only [ForcingMapCalculus.five,args3,args2,Fin.cases_zero,Fin.cases_succ] using hFixed (Fin.succ (Fin.succ (Fin.succ 0)))
  have hFixY : Supported (fun j => env (rho j)) (env S) (env Y) := by
    simpa only [ForcingMapCalculus.five,args3,args2,args1,Fin.cases_zero,Fin.cases_succ] using hFixed (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))
  obtain ⟨Bi,hBi,hFixBi,hB⟩ := construct_B hM env rho I K B w G F S mul top s A X ci
    hPres hG hF hS hSF ht hX hFixs hFixA hFixX hCi
  obtain ⟨Yi,hYi,hFixYi,hYPart⟩ := construct_Ypart hM env rho I K B w G F S mul top O f s A X Y i
    hPres hG hF hS hSF ht hY hFixY hFixed
  obtain ⟨Si,hSi,hFixSi,hSPart⟩ := construct_Spart hM env rho G F mul hPres hG hF hS hf hBi hYi hFixf hFixBi hFixYi
  exact ⟨Bi,Yi,Si,hBi,hFixBi,hB,hYi,hFixYi,hYPart,hSi,hFixSi,hSPart⟩

def piecesFormula {k : Nat} (rho : Fin 7 → Fin k) (G F S mul top O f s A X Y i ci : Fin k) : Formula k :=
  let b : Fin k → Fin (k+3) := fun j => j.castSucc.castSucc.castSucc
  let rr : Fin 7 → Fin (k+3) := fun j => b (rho j)
  let Bi := (Fin.last k).castSucc.castSucc
  let Yi := (Fin.last (k+1)).castSucc
  let Si := Fin.last (k+2)
  .ex (.ex (.ex ((ForcingHS.hs actionFormula rr (b G) (b (rho 6)) (b F) Bi).conj
    ((ForcingEquivariantMix.fixedAll rr (b S) Bi).conj
      ((ForcingSliceSelection.selected (orderFormula (rho 0) mul) (BPredicate rho G F mul s A X ci) b (b (rho 6)) (b X) Bi).conj
        ((ForcingHS.hs actionFormula rr (b G) (b (rho 6)) (b F) Yi).conj
          ((ForcingEquivariantMix.fixedAll rr (b S) Yi).conj
            ((ForcingSliceSelection.selected (orderFormula (rho 0) mul) (YPredicate rho G F mul top O f s A X Y i) b (b (rho 6)) (b Y) Yi).conj
              ((ForcingHS.hs actionFormula rr (b G) (b (rho 6)) (b F) Si).conj
                ((ForcingEquivariantMix.fixedAll rr (b S) Si).conj
                  (ForcingSeparation.separated (orderFormula (rho 0) mul) (domain rho G F) b
                    (args3 (b f) Bi Yi) (b (rho 6)) Bi Si preimageFormula)))))))))))

theorem piecesFormula_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F S mul top O f s A X Y i ci : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (piecesFormula rho G F S mul top O f s A X Y i ci) ↔
      Pieces env rho G F S mul top O f s A X Y i ci := by
  simp only [piecesFormula,Pieces,Formula.Realize,ForcingHS.hs_semantics,ForcingEquivariantMix.fixedAll_semantics,
    ForcingSliceSelection.selected_semantics,ForcingSeparation.separated_semantics,
    Fin.lastCases_last,Fin.lastCases_castSucc,args3_map]
  rfl

def sentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F S mul top O f s A X Y i ci : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
      ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
      ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
      ProjectSyntax.encode id (ForcingConjugationGraph.subgroup I G S),
      .mem (.bound S) (.bound F),
      ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F f),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F X),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F Y),
      ProjectSyntax.encode id (ForcingSupportingRoot.tupleSupported rho S (ForcingMapCalculus.five f s A X Y)),
      ProjectSyntax.encode id (ForcingCheckName.checkName top i ci)].foldr Definitional.Formula.imp
        (ProjectSyntax.encode id (piecesFormula rho G F S mul top O f s A X Y i ci)))
  freeClosed := by
    simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F S mul top O f s A X Y i ci : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sentence rho I K B w G F S mul top O f s A X Y i ci)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingNormalFilter.normal_semantics,ForcingConjugationGraph.subgroup_semantics,
    ForcingWithTopCarrier.empty_semantics,ForcingHS.hs_semantics,ForcingSupportingRoot.tupleSupported_semantics,
    ForcingCheckName.checkName_semantics,piecesFormula_semantics,id_eq]
  exact construct_pieces hM env rho I K B w G F S mul top O f s A X Y i ci

theorem kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F S mul top O f s A X Y i ci : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sentence rho I K B w G F S mul top O f s A X Y i ci)) :=
  ModelTransfer.derives (fun _ hM => models rho I K B w G F S mul top O f s A X Y i ci hM)

/-- One support is constructed BEFORE quantifying over the WHOLE internal
index set. Check names and all three piece names are actual existential outputs. -/
def Family {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul top O f s A X Y : Fin k) : Prop :=
  ∃ S, ForcingConjugationGraph.Subgroup (env I) (env G) S ∧
    (Project.FirstOrderSemantics.reduct M).mem S (env F) ∧
    (∀ j, Supported (fun a => env (rho a)) S (env (ForcingMapCalculus.five f s A X Y j))) ∧
    ∀ i, (Project.FirstOrderSemantics.reduct M).mem i (env O) → ∃ ci,
      ForcingCheckName.Checked (env top) i ci ∧
      Pieces (Fin.lastCases ci (Fin.lastCases i (Fin.lastCases S env)))
        (fun j => (rho j).castSucc.castSucc.castSucc)
        G.castSucc.castSucc.castSucc F.castSucc.castSucc.castSucc (Fin.last k).castSucc.castSucc
        mul.castSucc.castSucc.castSucc top.castSucc.castSucc.castSucc O.castSucc.castSucc.castSucc
        f.castSucc.castSucc.castSucc s.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc
        X.castSucc.castSucc.castSucc Y.castSucc.castSucc.castSucc (Fin.last (k+1)).castSucc (Fin.last (k+2))

theorem construct_family (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w G F mul top O f s A X Y : Fin k)
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hNames : ∀ j, HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F)
      (env (ForcingMapCalculus.five f s A X Y j))) :
    Family env rho I G F mul top O f s A X Y := by
  obtain ⟨S,hS,hSF,hTuple⟩ := ForcingTupleStabilizer.exists_tuple hM (fun a => env (rho a)) hPres hG hF
    (fun j => env (ForcingMapCalculus.five f s A X Y j)) hNames
  have hFixed (j : Fin 5) : Supported (fun a => env (rho a)) S (env (ForcingMapCalculus.five f s A X Y j)) :=
    fun pi hpi act hAct => ForcingTupleStabilizer.fixed_action hM hTuple hpi hAct j
  refine ⟨S,hS,hSF,hFixed,?_⟩
  intro i _hi
  obtain ⟨ci,hCi⟩ := ForcingCheckName.exists_checked hM (env top) i
  refine ⟨ci,hCi,?_⟩
  let ext : Fin (k+3) → M.Carrier .set := Fin.lastCases ci (Fin.lastCases i (Fin.lastCases S env))
  let up (a : Fin k) : Fin (k+3) := a.castSucc.castSucc.castSucc
  let rr : Fin 7 → Fin (k+3) := fun a => up (rho a)
  let ss : Fin (k+3) := (Fin.last k).castSucc.castSucc
  let ii : Fin (k+3) := (Fin.last (k+1)).castSucc
  let cc : Fin (k+3) := Fin.last (k+2)
  have eu (a : Fin k) : ext (up a) = env a := by simp only [ext,up,Fin.lastCases_castSucc]
  have es : ext ss = S := by simp only [ext,ss,Fin.lastCases_last,Fin.lastCases_castSucc]
  have ei : ext ii = i := by simp only [ext,ii,Fin.lastCases_last,Fin.lastCases_castSucc]
  have ec : ext cc = ci := by simp only [ext,cc,Fin.lastCases_last]
  have hv : (fun j => ext (ForcingMapCalculus.five (up f) (up s) (up A) (up X) (up Y) j)) =
      (fun j => env (ForcingMapCalculus.five f s A X Y j)) := by simp only [five_map,eu]
  apply construct_pieces hM ext rr (up I) (up K) (up B) (up w) (up G) (up F) ss (up mul) (up top)
    (up O) (up f) (up s) (up A) (up X) (up Y) ii cc
  · simpa only [rr,eu] using hPres
  · simpa only [eu] using hG
  · simpa only [eu] using hF
  · simpa only [eu,es] using hS
  · simpa only [eu,es] using hSF
  · simpa only [eu] using ht
  · simpa only [rr,eu,ForcingMapCalculus.five,Fin.cases_zero] using hNames 0
  · simpa only [rr,eu,ForcingMapCalculus.five,args3,args2,Fin.cases_succ,Fin.cases_zero]
      using hNames (Fin.succ (Fin.succ (Fin.succ 0)))
  · simpa only [rr,eu,ForcingMapCalculus.five,args3,args2,args1,Fin.cases_succ,Fin.cases_zero]
      using hNames (Fin.succ (Fin.succ (Fin.succ (Fin.succ 0))))
  · intro j
    have hvj := congrFun hv j
    simpa only [rr,eu,es,hvj] using hFixed j
  · simpa only [eu,ei,ec] using hCi

def familyFormula {k : Nat} (rho : Fin 7 → Fin k) (I G F mul top O f s A X Y : Fin k) : Formula k :=
  let up : Fin k → Fin (k+3) := fun j => j.castSucc.castSucc.castSucc
  let rr : Fin 7 → Fin (k+3) := fun j => up (rho j)
  .ex ((ForcingConjugationGraph.subgroup I.castSucc G.castSucc (Fin.last k)).conj
    ((Formula.mem (Fin.last k) F.castSucc).conj
      ((ForcingSupportingRoot.tupleSupported (fun j => (rho j).castSucc) (Fin.last k)
        (ForcingMapCalculus.five f.castSucc s.castSucc A.castSucc X.castSucc Y.castSucc)).conj
        (.all ((Formula.mem (Fin.last (k+1)) O.castSucc.castSucc).imp
          (.ex ((ForcingCheckName.checkName (up top) (Fin.last (k+1)).castSucc (Fin.last (k+2))).conj
            (piecesFormula rr (up G) (up F) (Fin.last k).castSucc.castSucc (up mul) (up top)
              (up O) (up f) (up s) (up A) (up X) (up Y) (Fin.last (k+1)).castSucc (Fin.last (k+2))))))))))

theorem familyFormula_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul top O f s A X Y : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (familyFormula rho I G F mul top O f s A X Y) ↔
      Family env rho I G F mul top O f s A X Y := by
  have hParam (S : M.Carrier .set) (j : Fin 5) :
      Fin.lastCases S env (ForcingMapCalculus.five f.castSucc s.castSucc A.castSucc X.castSucc Y.castSucc j) =
      env (ForcingMapCalculus.five f s A X Y j) := by
    calc
      _ = ForcingMapCalculus.five (Fin.lastCases S env f.castSucc) (Fin.lastCases S env s.castSucc)
          (Fin.lastCases S env A.castSucc) (Fin.lastCases S env X.castSucc) (Fin.lastCases S env Y.castSucc) j :=
        congrFun (five_map (Fin.lastCases S env) f.castSucc s.castSucc A.castSucc X.castSucc Y.castSucc) j
      _ = ForcingMapCalculus.five (env f) (env s) (env A) (env X) (env Y) j := by simp only [Fin.lastCases_castSucc]
      _ = _ := (congrFun (five_map env f s A X Y) j).symm
  simp only [familyFormula,Family,Formula.Realize,ForcingConjugationGraph.subgroup_semantics,
    ForcingSupportingRoot.tupleSupported_semantics,ForcingCheckName.checkName_semantics,piecesFormula_semantics,
    Fin.lastCases_last,Fin.lastCases_castSucc,hParam]
  rfl

def familySentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top O f s A X Y : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
      ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
      ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
      ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F f),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F s),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F A),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F X),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F Y)].foldr Definitional.Formula.imp
        (ProjectSyntax.encode id (familyFormula rho I G F mul top O f s A X Y)))
  freeClosed := by simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem family_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top O f s A X Y : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (familySentence rho I K B w G F mul top O f s A X Y)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingNormalFilter.normal_semantics,ForcingWithTopCarrier.empty_semantics,
    ForcingHS.hs_semantics,familyFormula_semantics,id_eq]
  intro hPres hG hF ht hf hs hA hX hY
  apply construct_family hM env rho I K B w G F mul top O f s A X Y hPres hG hF ht
  intro j
  exact Fin.cases hf (Fin.cases hs (Fin.cases hA (Fin.cases hX (Fin.cases hY (fun a => Fin.elim0 a))))) j

theorem family_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top O f s A X Y : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (familySentence rho I K B w G F mul top O f s A X Y)) :=
  ModelTransfer.derives (fun _ hM => family_models rho I K B w G F mul top O f s A X Y hM)

end PPAC.Migration.ForcingSliceGeometry
