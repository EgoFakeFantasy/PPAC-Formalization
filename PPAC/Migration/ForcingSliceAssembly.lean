/- Pinned SliceAssembly.assemble:61-105. The source familyUnion of the
ACTUAL bounded candidate graphs; internal indices and parameter names remain
set-coded. Existing graph collection/function constructors will be reused. -/
import PPAC.Migration.ForcingSliceCandidate
import PPAC.Migration.ForcingSectionInjection

namespace PPAC.Migration.ForcingSliceAssembly
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
open ForcingRelationGraphForcing (Holds)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
universe u v
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private def five {α : Type v} (c a b x y : α) : Fin 5 → α :=
  Fin.lastCases y (Fin.lastCases x (args3 c a b))

private theorem five_map {α : Type v} {β : Type u} (f : α → β) (c a b x y : α) :
    (fun j => f (five c a b x y j)) = five (f c) (f a) (f b) (f x) (f y) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rfl
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · rfl
    · exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t))) j

/-- Exactly source boundedApp c Ypart Spart. -/
def Part {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (P c a b p x y : M.Carrier .set) : Prop :=
  Force R H env (five c a b x y) P p ForcingSliceGraphs.boundedFormula

private theorem part_iff (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P c a b p x y : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) :
    Part R H env P c a b p x y ↔ Forces false R env P x a p ∧ Forces false R env P y b p ∧
      Force R H env (args3 c x y) P p (Source.SetLanguage.edge 0 1 2) := by
  change (_ ∧ _ ∧ Force R H env (five c a b x y) P p (Source.SetLanguage.edge 0 3 4)) ↔ _
  have e0 : five c a b x y 0 = c := rfl
  have e3 : five c a b x y 3 = x := by
    simp only [five,show (3 : Fin 5) = (Fin.last 3).castSucc from rfl,Fin.lastCases_castSucc,Fin.lastCases_last]
  have e4 : five c a b x y 4 = y := by
    simp only [five,show (4 : Fin 5) = Fin.last 4 from rfl,Fin.lastCases_last]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  simpa only [e0,e3,e4] using ForcingRelationClass.edge_formula (H := H) (n := 5) hM hpre hp
    (five c a b x y) (0 : Fin 5) 3 4

private theorem part_congr (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P c a b p x y x' y' : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hx : Forces true R env P x x' p) (hy : Forces true R env P y y' p) :
    Part R H env P c a b p x y ↔ Part R H env P c a b p x' y' := by
  apply ForcingFormula.tuple_congr hM hpre ForcingSliceGraphs.boundedFormula _ _ p hp
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simpa only [five,Fin.lastCases_last] using hy
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [five,Fin.lastCases_castSucc,Fin.lastCases_last] using hx
    · simpa only [five,Fin.lastCases_castSucc] using ForcingAtomicBasic.eq_refl hM hpre (args3 c a b j) p hp

/-- Exact source regularized familyUnion over an INTERNAL candidate function.
Q is the actual two-name parameter relation; no parameter function is needed. -/
def Union {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (Q : Formula (k+3))
    (env : Fin k → M.Carrier .set) (P O choices p x y : M.Carrier .set) : Prop :=
  ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p → ∃ r,
    (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧ ∃ i,
      (Project.FirstOrderSemantics.reduct M).mem i O ∧ ∃ c, PureKuratowski.PairMember M i c choices ∧
        ∃ a b, Holds Q env i a b ∧ Part R H env P c a b r x y

def unionFormula {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (Q : Formula (k+3))
    (base : Fin k → Fin m) (P O choices p x y : Fin m) : Formula m :=
  let up : Fin m → Fin (m+6) := fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let b : Fin k → Fin (m+6) := fun j => up (base j)
  let q := (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc
  let r := (Fin.last (m+1)).castSucc.castSucc.castSucc.castSucc
  let i := (Fin.last (m+2)).castSucc.castSucc.castSucc
  let c := (Fin.last (m+3)).castSucc.castSucc
  let a := (Fin.last (m+4)).castSucc
  let d := Fin.last (m+5)
  .all ((Formula.mem (Fin.last m) P.castSucc).imp
    ((ReplacementPredicates.rel R (fun j => (base j).castSucc) (Fin.last m) p.castSucc).imp
      (.ex (.ex (.ex (.ex (.ex ((Formula.mem r (up P)).conj
        ((ReplacementPredicates.rel R b r q).conj ((Formula.mem i (up O)).conj
          ((Source.SetLanguage.edge (up choices) i c).conj
            ((ForcingRelationGraphSupport.relation Q b i a d).conj
              (ForcingFormula.formula R H b (five c a d (up x) (up y)) (up P) r ForcingSliceGraphs.boundedFormula)))))))))))))

theorem unionFormula_semantics {k m : Nat} (v : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (Q : Formula (k+3))
    (base : Fin k → Fin m) (P O choices p x y : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v (unionFormula R H Q base P O choices p x y) ↔
      Union R H Q (fun j => v (base j)) (v P) (v O) (v choices) (v p) (v x) (v y) := by
  simp only [unionFormula,Union,Part,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    KuratowskiZF.source_edge,ForcingRelationGraphSupport.relation_semantics (M := M),
    ForcingFormula.formula_semantics,five_map,Fin.lastCases_last,Fin.lastCases_castSucc]
  constructor
  · intro h q hq hqp
    obtain ⟨r,i,c,a,b,hr,hrq,hi,hc,hQ,hPart⟩ := h q hq hqp
    exact ⟨r,hr,hrq,i,hi,c,hc,a,b,hQ,hPart⟩
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,i,hi,c,hc,a,b,hQ,hPart⟩ := h q hq hqp
    exact ⟨r,i,c,a,b,hr,hrq,hi,hc,hQ,hPart⟩

def relation {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (Q : Formula (k+3))
    (P O choices : Fin k) : Formula (k+3) :=
  unionFormula R H Q (fun j => j.castSucc.castSucc.castSucc)
    P.castSucc.castSucc.castSucc O.castSucc.castSucc.castSucc choices.castSucc.castSucc.castSucc
    (Fin.last k).castSucc.castSucc (Fin.last (k+1)).castSucc (Fin.last (k+2))

theorem relation_semantics {k : Nat} (env : Fin k → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (Q : Formula (k+3)) (P O choices : Fin k) (p x y : M.Carrier .set) :
    Holds (relation R H Q P O choices) env p x y ↔ Union R H Q env (env P) (env O) (env choices) p x y := by
  simp only [relation,Holds,unionFormula_semantics,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem mono {k : Nat} {R : Formula (k+2)} {H : Formula (k+1)} {Q : Formula (k+3)}
    {env : Fin k → M.Carrier .set} {P O choices p q x y : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hqp : MapRel R env q p) (h : Union R H Q env P O choices p x y) : Union R H Q env P O choices q x y := by
  intro r hr hrq
  exact h r hr (hpre.2 r q p hr hq hp hrq hqp)

theorem regular {k : Nat} {R : Formula (k+2)} {H : Formula (k+1)} {Q : Formula (k+3)}
    {env : Fin k → M.Carrier .set} {P O choices p x y : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (h : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p → ∃ r,
      (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧ Union R H Q env P O choices r x y) :
    Union R H Q env P O choices p x y := by
  intro q hq hqp
  obtain ⟨r,hr,hrq,hRel⟩ := h q hq hqp
  obtain ⟨s,hs,hsr,i,hi,c,hc,a,b,hQ,hPart⟩ := hRel r hr (hpre.1 r hr)
  exact ⟨s,hs,hpre.2 s r q hs hr hq hsr hrq,i,hi,c,hc,a,b,hQ,hPart⟩

theorem congruent (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {Q : Formula (k+3)}
    {env : Fin k → M.Carrier .set} {P O choices p x y x' y' : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hx : Forces true R env P x x' p) (hy : Forces true R env P y y' p) :
    Union R H Q env P O choices p x y ↔ Union R H Q env P O choices p x' y' := by
  have hp := ForcingAtomicBasic.condition hM hx
  have one {x y x' y' : M.Carrier .set} (hx : Forces true R env P x x' p) (hy : Forces true R env P y y' p)
      (h : Union R H Q env P O choices p x y) : Union R H Q env P O choices p x' y' := by
    intro q hq hqp
    obtain ⟨r,hr,hrq,i,hi,c,hc,a,b,hQ,hPart⟩ := h q hq hqp
    have hrp := hpre.2 r q p hr hq hp hrq hqp
    exact ⟨r,hr,hrq,i,hi,c,hc,a,b,hQ,(part_congr hM hpre hr
      (ForcingAtomicBasic.eq_mono hM hpre hr hrp hx) (ForcingAtomicBasic.eq_mono hM hpre hr hrp hy)).mp hPart⟩
  exact ⟨one hx hy,one (ForcingAtomicBasic.eq_symm hM hx) (ForcingAtomicBasic.eq_symm hM hy)⟩

theorem move (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k) (Q : Formula (k+3))
    {I K B w O choices pi act p q x y x' y' : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpi : ForcingConditionGraphs.Permutation I pi) (hAct : MapRel actionFormula (fun j => env (rho j)) pi act)
    (hFixC : ∀ i c, (Project.FirstOrderSemantics.reduct M).mem i O → PureKuratowski.PairMember M i c choices →
      ForcingStabilizer.Action (env (rho 6)) act c c)
    (hFixAB : ∀ i a b, (Project.FirstOrderSemantics.reduct M).mem i O → Holds Q env i a b →
      ForcingStabilizer.Action (env (rho 6)) act a a ∧ ForcingStabilizer.Action (env (rho 6)) act b b)
    (hpq : PureKuratowski.PairMember M p q act)
    (hxx : ForcingStabilizer.Action (env (rho 6)) act x x') (hyy : ForcingStabilizer.Action (env (rho 6)) act y y')
    (h : Union (orderFormula (rho 0) mul) (domain rho G F) Q env (env (rho 6)) O choices p x y) :
    Union (orderFormula (rho 0) mul) (domain rho G F) Q env (env (rho 6)) O choices q x' y' := by
  have ha := (mapRel_action (fun j => env (rho j)) pi act).mp hAct
  have hPerm := ForcingProductFamily.action_permutation ha
  have hOrder := ForcingProductFamily.order hM (env mul) hPres hpi ha
  intro t htP htq
  obtain ⟨t0,ht0,ht0t⟩ := hPerm.2.2 t htP
  have ht0p := (orderFormula_semantics env (rho 0) mul t0 p).mpr
    ((hOrder t0 p t q ht0t hpq).mpr ((orderFormula_semantics env (rho 0) mul t q).mp htq))
  obtain ⟨r,hr,hrt0,i,hi,c,hc,a,b,hQ,hPart⟩ := h t0 ht0 ht0p
  obtain ⟨r',hrr',_⟩ := hPerm.1.1.2 r hr
  have hr' := hPerm.1.2 r r' hrr'
  have hr't := (orderFormula_semantics env (rho 0) mul r' t).mpr
    ((hOrder r t0 r' t hrr' ht0t).mp ((orderFormula_semantics env (rho 0) mul r t0).mp hrt0))
  refine ⟨r',hr',hr't,i,hi,c,hc,a,b,hQ,?_⟩
  apply (ForcingSeparation.symmetry hM env rho G F mul hPres hG hF hpi hAct ForcingSliceGraphs.boundedFormula
    (five c a b x y) (five c a b x' y') ?_ hr hrr').mp hPart
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simpa only [five,Fin.lastCases_last] using hyy
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [five,Fin.lastCases_castSucc,Fin.lastCases_last] using hxx
    · simpa only [five,Fin.lastCases_castSucc] using
        Fin.cases (hFixC i c hi hc) (Fin.cases (hFixAB i a b hi hQ).1
          (Fin.cases (hFixAB i a b hi hQ).2 (fun t => Fin.elim0 t))) j


private theorem parameter_pair {k : Nat} (env : Fin k → M.Carrier .set) (Q : Formula (k+3)) (i a b : M.Carrier .set) :
    Holds Q env i a b ↔ ForcingUniformMaximum.ParameterSpec env Q i (args2 a b) := by
  change Formula.Realize _ (Fin.lastCases b (Fin.lastCases a (Fin.lastCases i env))) Q ↔ _
  rfl

/-- Eliminate the ACTUAL constructor equations of Q. This is not a slice
correctness assumption: both member laws are proved from parameter_spec_iff. -/
private theorem parameter_facts (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F S mul top O f s A X Y : Fin k)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
    {i a b : M.Carrier .set}
    (hQ : Holds (ForcingSliceParameters.parameterFormula rho G F S mul top O f s A X Y) env i a b) :
    ∀ nu, Predicate (domain rho G F) env nu → ∀ p,
      (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) →
      (Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu a p ↔
        Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu (env Y) p ∧
        ForcingLeastOccurrence.At (orderFormula (rho 0) mul) (ForcingSliceGeometry.occurrence rho G F mul top f s A X Y)
          env (env (rho 6)) (env O) p nu i) ∧
      (Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu b p →
        Forces false (orderFormula (rho 0) mul) env (env (rho 6)) nu (env X) p ∧
        ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
          MapRel (orderFormula (rho 0) mul) env q p → ∃ r,
          (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) ∧
          MapRel (orderFormula (rho 0) mul) env r q ∧ ∃ y, Predicate (domain rho G F) env y ∧
            Forces false (orderFormula (rho 0) mul) env (env (rho 6)) y a r ∧
            Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) nu y) (env (rho 6)) r (Source.SetLanguage.edge 0 1 2)) := by
  have hParam := (parameter_pair env _ i a b).mp hQ
  obtain ⟨ci,_hCi,Bi,_hBi,_hFixBi,hB,_hYi,_hFixYi,hYP,_hSi,_hFixSi,hSP⟩ :=
    (ForcingSliceParameters.parameter_spec_iff env rho G F S mul top O f s A X Y i (args2 a b)).mp hParam
  let e : Fin (k+2) → M.Carrier .set := Fin.lastCases ci (Fin.lastCases i env)
  let up : Fin k → Fin (k+2) := fun j => j.castSucc.castSucc
  let rr : Fin 7 → Fin (k+2) := fun j => up (rho j)
  let ii : Fin (k+2) := (Fin.last k).castSucc
  let cc : Fin (k+2) := Fin.last (k+1)
  have he (j : Fin k) : e (up j) = env j := by simp only [e,up,Fin.lastCases_castSucc]
  have ei : e ii = i := by simp only [e,ii,Fin.lastCases_castSucc,Fin.lastCases_last]
  have hR (x y : M.Carrier .set) : MapRel (orderFormula (rho 0) mul) env x y ↔
      MapRel (orderFormula (rr 0) (up mul)) e x y := by simp only [orderFormula_semantics,rr,he]
  have hpre' := ForcingNonwellorderableImage.pre_reindex env e up he rho mul hpre
  have hX' : HS actionFormula (fun j => e (rr j)) (e (up G)) (e (rr 6)) (e (up F)) (e (up X)) := by
    simpa only [rr,he] using hX
  have hY' : HS actionFormula (fun j => e (rr j)) (e (up G)) (e (rr 6)) (e (up F)) (e (up Y)) := by
    simpa only [rr,he] using hY
  have hYP' : ForcingSliceSelection.Selected (orderFormula (rr 0) (up mul))
      (ForcingSliceGeometry.YPredicate rr (up G) (up F) (up mul) (up top) (up O) (up f) (up s) (up A) (up X) (up Y) ii)
      e (e (rr 6)) (e (up Y)) a := by
    simpa only [rr,he,args2,Fin.cases_zero] using hYP
  have hB' : ForcingSliceSelection.Selected (orderFormula (rr 0) (up mul))
      (ForcingSliceGeometry.BPredicate rr (up G) (up F) (up mul) (up s) (up A) (up X) cc)
      e (e (rr 6)) (e (up X)) Bi := by
    simpa only [rr,he] using hB
  have hSP' : ForcingSeparation.Separated (orderFormula (rr 0) (up mul)) (domain rr (up G) (up F))
      e (args3 (env f) Bi a) (e (rr 6)) Bi b ForcingSliceGeometry.preimageFormula := by
    simpa only [rr,he,args2,args1,show (1 : Fin 2) = Fin.succ (0 : Fin 1) from rfl,Fin.cases_zero,Fin.cases_succ] using hSP
  intro nu hNu p hp
  have hNu' : Predicate (domain rr (up G) (up F)) e nu := by simpa only [domain_semantics,rr,he] using hNu
  have hp' : (Project.FirstOrderSemantics.reduct M).mem p (e (rr 6)) := by simpa only [rr,he] using hp
  have hYMem := ForcingSliceGeometry.mem_Ypart hM e rr (up G) (up F) (up mul) (up top) (up O)
    (up f) (up s) (up A) (up X) (up Y) ii hpre' hY' hNu' hYP' hp'
  refine ⟨?_,?_⟩
  · constructor
    · intro hh
      have hh' := (ForcingSeparation.atomic_congr hR false (env (rho 6)) nu a p).mp hh
      have hPair := hYMem.mp (by simpa only [rr,he,args2,Fin.cases_zero] using hh')
      refine ⟨?_,?_⟩
      · apply (ForcingSeparation.atomic_congr hR false (env (rho 6)) nu (env Y) p).mpr
        simpa only [rr,he] using hPair.1
      · apply (ForcingSliceCoverage.at_reindex env e up he rho G F mul top O f s A X Y p nu i).mpr
        simpa only [ei] using hPair.2
    · rintro ⟨hh,hAt⟩
      apply (ForcingSeparation.atomic_congr hR false (env (rho 6)) nu a p).mpr
      have hm := (ForcingSeparation.atomic_congr hR false (env (rho 6)) nu (env Y) p).mp hh
      have ha := (ForcingSliceCoverage.at_reindex env e up he rho G F mul top O f s A X Y p nu i).mp hAt
      have hOut := hYMem.mpr ⟨by simpa only [rr,he] using hm,by simpa only [ei] using ha⟩
      simpa only [rr,he,args2,Fin.cases_zero] using hOut
  · intro hh
    have hh' := (ForcingSeparation.atomic_congr hR false (env (rho 6)) nu b p).mp hh
    have hSPMem := (ForcingSliceGeometry.mem_Spart hM hpre' hSP' hp').mp (by simpa only [rr,he] using hh')
    have hBMem := (ForcingSliceGeometry.mem_formula_selection hM e rr (up G) (up F) (up mul) (up X)
      (ForcingSliceGeometry.four (up s) (up A) (up X) cc) ForcingSliceGeometry.bFormula hpre' hX' hNu' hB' hp').mp hSPMem.1
    refine ⟨?_,?_⟩
    · apply (ForcingSeparation.atomic_congr hR false (env (rho 6)) nu (env X) p).mpr
      simpa only [rr,he] using hBMem.1
    · intro q hq hqp
      obtain ⟨r,hr,hrq,y,hy,_hBi,hyA,hApp⟩ := hSPMem.2 q (by simpa only [rr,he] using hq) ((hR q p).mp hqp)
      refine ⟨r,?_,(hR r q).mpr hrq,y,?_,?_,?_⟩
      · simpa only [rr,he] using hr
      · simpa only [domain_semantics,rr,he] using hy
      · apply (ForcingSeparation.atomic_congr hR false (env (rho 6)) y a r).mpr
        simpa only [rr,he] using hyA
      · apply (ForcingNonwellorderableImage.force_reindex env e up he rho G F mul (Source.SetLanguage.edge 0 1 2)
          (args3 (env f) nu y) r).mpr
        simpa only [rr,he] using hApp


private theorem parameter_eq (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F S mul top O f s A X Y : Fin k)
    {i a b a' b' : M.Carrier .set}
    (h : Holds (ForcingSliceParameters.parameterFormula rho G F S mul top O f s A X Y) env i a b)
    (h' : Holds (ForcingSliceParameters.parameterFormula rho G F S mul top O f s A X Y) env i a' b') : a = a' ∧ b = b' := by
  have he := ForcingSliceParameters.parameter_unique hM env rho G F S mul top O f s A X Y
    ((parameter_pair env _ i a b).mp h) ((parameter_pair env _ i a' b').mp h')
  exact ⟨congrFun he 0,congrFun he 1⟩

private theorem injection_pair (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p c a b : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) :
    Force R H env (Fin.lastCases c (args2 a b)) P p (Source.SetLanguage.injection 2 0 1) ↔
      Force R H env (args3 c a b) P p (Source.SetLanguage.injection 0 1 2) := by
  rw [Source.SetLanguage.injection,Source.SetLanguage.injection,
    ForcingSound.rename hM hpre _ _ _ _ hp,ForcingSound.rename hM hpre _ _ _ _ hp]
  have hv : (fun j => Fin.lastCases c (args2 a b) (args3 (2 : Fin 3) 0 1 j)) =
      (fun j => args3 c a b (args3 (0 : Fin 3) 1 2 j)) := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t))) j
  rw [hv]

section ActualPieces
variable {k : Nat} (hM : FirstOrder.Theory.Models M nativeZF)
variable (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F S mul top O f s A X Y : Fin k)
variable (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
variable (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
variable (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
variable (hO : ForcingRawRank.Ordinal (env O))
include hM hpre hX hY hO

/-- Exact source Spart_disjoint at the ACTUAL Q names. Reuse the existing
Spart/member, parent function-uniqueness and least-occurrence rules. -/
private theorem spart_index_unique {i j a b a' b' x p q : M.Carrier .set}
    (hQi : Holds (ForcingSliceParameters.parameterFormula rho G F S mul top O f s A X Y) env i a b)
    (hQj : Holds (ForcingSliceParameters.parameterFormula rho G F S mul top O f s A X Y) env j a' b')
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y))
      (env (rho 6)) p (Source.SetLanguage.mapsTo 0 1 2))
    (hx : Predicate (domain rho G F) env x)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)))
    (hqp : MapRel (orderFormula (rho 0) mul) env q p)
    (hi : Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x b q)
    (hj : Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x b' q) : i = j := by
  have hFi := parameter_facts hM env rho G F S mul top O f s A X Y hpre hX hY hQi
  have hFj := parameter_facts hM env rho G F S mul top O f s A X Y hpre hX hY hQj
  obtain ⟨r,hr,hrq,y,hy,hyA,hAppY⟩ := ((hFi x hx q hq).2 hi).2 q hq (hpre.1 q hq)
  obtain ⟨t,ht,htr,z,hz,hzA',hAppZ⟩ := ((hFj x hx q hq).2 hj).2 r hr hrq
  have htq := hpre.2 t r q ht hr hq htr hrq
  have htp := hpre.2 t q p ht hq hp htq hqp
  have hxX := ForcingAtomicBasic.mem_mono hM hpre ht htq ((hFi x hx q hq).2 hi).1
  have heq := ForcingKernelImage.mapsTo_unique_reuse hM hpre hp ht htp hf hx hy hz hxX
    (ForcingFormula.mono hM hpre _ _ hr ht htr hAppY) hAppZ
  have hzA := (ForcingAtomicLaws.mem_congr_left hM hpre heq).mp (ForcingAtomicBasic.mem_mono hM hpre ht htr hyA)
  exact ForcingLeastOccurrence.unique hM hO hpre ht ((hFi z hz t ht).1.mp hzA).2 ((hFj z hz t ht).1.mp hzA').2

/-- The source function uniqueness case: target partition determines the
same internal index; literal parameter/function uniqueness then identifies
all three actual bounded-graph parents. -/
private theorem union_one {choices p q x y z : M.Carrier .set}
    (hChoices : ForcingConditionGraphs.FunctionOn (env O) choices)
    (hFamily : ∀ i c, (Project.FirstOrderSemantics.reduct M).mem i (env O) → PureKuratowski.PairMember M i c choices →
      ∀ a b, Holds (ForcingSliceParameters.parameterFormula rho G F S mul top O f s A X Y) env i a b →
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 c a b) (env (rho 6)) p (Source.SetLanguage.injection 0 1 2))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hx : Predicate (domain rho G F) env x) (hy : Predicate (domain rho G F) env y) (hz : Predicate (domain rho G F) env z)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6))) (hqp : MapRel (orderFormula (rho 0) mul) env q p)
    (hU : Union (orderFormula (rho 0) mul) (domain rho G F) (ForcingSliceParameters.parameterFormula rho G F S mul top O f s A X Y)
      env (env (rho 6)) (env O) choices q x y)
    (hU' : Union (orderFormula (rho 0) mul) (domain rho G F) (ForcingSliceParameters.parameterFormula rho G F S mul top O f s A X Y)
      env (env (rho 6)) (env O) choices q x z) :
    Forces true (orderFormula (rho 0) mul) env (env (rho 6)) y z q := by
  apply ForcingAtomicBasic.eq_of_dense hM hpre hq
  intro r hr hrq
  obtain ⟨stage,hs,hsr,i,hi,c,hc,a,b,hQ,hPart⟩ := hU r hr hrq
  have hsq := hpre.2 stage r q hs hr hq hsr hrq
  obtain ⟨t,ht,hts,j,_hj,c',hc',a',b',hQ',hPart'⟩ := hU' stage hs hsq
  have htq := hpre.2 t stage q ht hs hq hts hsq
  have htp := hpre.2 t q p ht hq hp htq hqp
  have hPart := (part_iff hM hpre hs).mp hPart
  have hPart' := (part_iff hM hpre ht).mp hPart'
  have hxA := ForcingAtomicBasic.mem_mono hM hpre ht hts hPart.1
  have hAt := ((parameter_facts hM env rho G F S mul top O f s A X Y hpre hX hY hQ x hx t ht).1.mp hxA).2
  have hAt' := ((parameter_facts hM env rho G F S mul top O f s A X Y hpre hX hY hQ' x hx t ht).1.mp hPart'.1).2
  have hij := ForcingLeastOccurrence.unique hM hO hpre ht hAt hAt'
  cases hij
  obtain ⟨haa,hbb⟩ := parameter_eq hM env rho G F S mul top O f s A X Y hQ hQ'
  cases haa
  cases hbb
  obtain ⟨chosen,_hChosen,hUnique⟩ := hChoices.2 i hi
  have hcc := (hUnique c hc).trans (hUnique c' hc').symm
  cases hcc
  have hMap := ForcingIndexedImage.injection_mapsTo hM hpre hp (hFamily i c hi hc a b hQ)
  exact ⟨t,ht,hpre.2 t stage r ht hs hr hts hsr,ForcingKernelImage.mapsTo_unique_reuse hM hpre hp ht htp hMap hx hy hz hxA
    (ForcingFormula.mono hM hpre _ _ hs ht hts hPart.2.2) hPart'.2.2⟩

/-- The source injectivity case uses disjoint source pieces, without claiming
that those pieces cover X and without requiring candidates to section f. -/
private theorem union_injective {choices p q x y z : M.Carrier .set}
    (hChoices : ForcingConditionGraphs.FunctionOn (env O) choices)
    (hFamily : ∀ i c, (Project.FirstOrderSemantics.reduct M).mem i (env O) → PureKuratowski.PairMember M i c choices →
      ∀ a b, Holds (ForcingSliceParameters.parameterFormula rho G F S mul top O f s A X Y) env i a b →
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 c a b) (env (rho 6)) p (Source.SetLanguage.injection 0 1 2))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y))
      (env (rho 6)) p (Source.SetLanguage.mapsTo 0 1 2))
    (hx : Predicate (domain rho G F) env x) (hy : Predicate (domain rho G F) env y) (hz : Predicate (domain rho G F) env z)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6))) (hqp : MapRel (orderFormula (rho 0) mul) env q p)
    (hU : Union (orderFormula (rho 0) mul) (domain rho G F) (ForcingSliceParameters.parameterFormula rho G F S mul top O f s A X Y)
      env (env (rho 6)) (env O) choices q x z)
    (hU' : Union (orderFormula (rho 0) mul) (domain rho G F) (ForcingSliceParameters.parameterFormula rho G F S mul top O f s A X Y)
      env (env (rho 6)) (env O) choices q y z) :
    Forces true (orderFormula (rho 0) mul) env (env (rho 6)) x y q := by
  apply ForcingAtomicBasic.eq_of_dense hM hpre hq
  intro r hr hrq
  obtain ⟨stage,hs,hsr,i,hi,c,hc,a,b,hQ,hPart⟩ := hU r hr hrq
  have hsq := hpre.2 stage r q hs hr hq hsr hrq
  obtain ⟨t,ht,hts,j,_hj,c',hc',a',b',hQ',hPart'⟩ := hU' stage hs hsq
  have htq := hpre.2 t stage q ht hs hq hts hsq
  have htp := hpre.2 t q p ht hq hp htq hqp
  have hPart := (part_iff hM hpre hs).mp hPart
  have hPart' := (part_iff hM hpre ht).mp hPart'
  have hzB := ForcingAtomicBasic.mem_mono hM hpre ht hts hPart.2.1
  have hij := spart_index_unique hM env rho G F S mul top O f s A X Y hpre hX hY hO hQ hQ' hp hf hz ht htp hzB hPart'.2.1
  cases hij
  obtain ⟨haa,hbb⟩ := parameter_eq hM env rho G F S mul top O f s A X Y hQ hQ'
  cases haa
  cases hbb
  obtain ⟨chosen,_hChosen,hUnique⟩ := hChoices.2 i hi
  have hcc := (hUnique c hc).trans (hUnique c' hc').symm
  cases hcc
  exact ⟨t,ht,hpre.2 t stage r ht hs hr hts hsr,ForcingIndexedImage.injection_one hM hpre hp (hFamily i c hi hc a b hQ)
    hx hy hz ht htp (ForcingAtomicBasic.mem_mono hM hpre ht hts hPart.1) hPart'.1
    (ForcingFormula.mono hM hpre _ _ hs ht hts hPart.2.2) hPart'.2.2⟩


/-- Source totality uses the ALREADY accepted dense occurrence cover and
internal ordinal least index, then the actual Q selector. No source-piece
cover of X, external index selection, or simultaneous default family. -/
private theorem union_total (I K B w checkedO Cart p : Fin k) {choices : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (htop : ForcingWithTopCarrier.Empty (env top))
    (hA : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env A))
    (hCheckedO : ForcingCheckName.Checked (env top) (env O) (env checkedO))
    (hCart : ForcingRelationGraph.Graph (orderFormula (rho 0) mul) ForcingCompletionGraph.trueRelation
      env (rho 6) top A checkedO (env Cart))
    (hChoices : ForcingConditionGraphs.FunctionOn (env O) choices)
    (hParameters : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i (env O) → ∃ a b,
      Holds (ForcingSliceParameters.parameterFormula rho G F S mul top O f s A X Y) env i a b)
    (hFamily : ∀ i c, (Project.FirstOrderSemantics.reduct M).mem i (env O) → PureKuratowski.PairMember M i c choices →
      ∀ a b, Holds (ForcingSliceParameters.parameterFormula rho G F S mul top O f s A X Y) env i a b →
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 c a b) (env (rho 6)) (env p) (Source.SetLanguage.injection 0 1 2))
    (hp : (Project.FirstOrderSemantics.reduct M).mem (env p) (env (rho 6)))
    (hs : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env s) (env Cart) (env X))
      (env (rho 6)) (env p) (Source.SetLanguage.surjection 0 1 2))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y))
      (env (rho 6)) (env p) (Source.SetLanguage.surjection 0 1 2)) :
    ∀ x, Predicate (domain rho G F) env x → ∀ q,
      (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
      MapRel (orderFormula (rho 0) mul) env q (env p) →
      Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env Y) q → ∀ r,
      (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) →
      MapRel (orderFormula (rho 0) mul) env r q → ∃ t,
      (Project.FirstOrderSemantics.reduct M).mem t (env (rho 6)) ∧
      MapRel (orderFormula (rho 0) mul) env t r ∧ ∃ y, Predicate (domain rho G F) env y ∧
        Forces false (orderFormula (rho 0) mul) env (env (rho 6)) y (env X) t ∧
        Union (orderFormula (rho 0) mul) (domain rho G F) (ForcingSliceParameters.parameterFormula rho G F S mul top O f s A X Y)
          env (env (rho 6)) (env O) choices t x y := by
  have hCover := ForcingSliceCoverage.occurrence_cover hM env rho I K B w G F mul top s f A X Y O checkedO Cart p
    hPres hG hF htop hpre hA hCheckedO hCart hp hs hf
  intro x hx q hq hqp hxY r hr hrq
  obtain ⟨stage,hstage,hstageR,i,hAt⟩ := ForcingLeastOccurrence.dense hM (orderFormula (rho 0) mul)
    (ForcingSliceGeometry.occurrence rho G F mul top f s A X Y) env (env (rho 6)) (env O) q x hO hpre
    (hCover x hx q hq hqp hxY) r hr hrq
  obtain ⟨a,b,hQ⟩ := hParameters i hAt.1
  obtain ⟨c,hc,_hUnique⟩ := hChoices.2 i hAt.1
  have hstageQ := hpre.2 stage r q hstage hr hq hstageR hrq
  have hstageP := hpre.2 stage q (env p) hstage hq hp hstageQ hqp
  have hxA := (parameter_facts hM env rho G F S mul top O f s A X Y hpre hX hY hQ x hx stage hstage).1.mpr
    ⟨ForcingAtomicBasic.mem_mono hM hpre hstage hstageQ hxY,hAt⟩
  have hMap := ForcingIndexedImage.injection_mapsTo hM hpre hp (hFamily i c hAt.1 hc a b hQ)
  obtain ⟨t,ht,htStage,y,hy,hyB,hApp⟩ := ForcingImageQuotient.mapsTo_total_reuse hM hpre hp hMap hx hstage hstageP hxA hstage (hpre.1 stage hstage)
  have hyX := ((parameter_facts hM env rho G F S mul top O f s A X Y hpre hX hY hQ y hy t ht).2 hyB).1
  refine ⟨t,ht,hpre.2 t stage r ht hstage hr htStage hstageR,y,hy,hyX,?_⟩
  intro cond hCond hCondT
  have hCondStage := hpre.2 cond t stage hCond ht hstage hCondT htStage
  refine ⟨cond,hCond,hpre.1 cond hCond,i,hAt.1,c,hc,a,b,hQ,(part_iff hM hpre hCond).mpr ?_⟩
  exact ⟨ForcingAtomicBasic.mem_mono hM hpre hCond hCondStage hxA,
    ForcingAtomicBasic.mem_mono hM hpre hCond hCondT hyB,ForcingFormula.mono hM hpre _ _ ht hCond hCondT hApp⟩

end ActualPieces


/-- Pinned SliceAssembly.assemble:61–105. The candidate function and its
support are exactly the source inputs. The ACTUAL Q equations discharge the
partition/subset/disjointness consumers; the EXISTING collector constructs
the one graph and full source injection, including functionOn and no junk. -/
theorem assemble (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F S H mul top O f s A X Y checkedO Cart choices p : Fin k)
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hS : ForcingConjugationGraph.Subgroup (env I) (env G) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env F))
    (hH : ForcingConjugationGraph.Subgroup (env I) (env G) (env H))
    (hHF : (Project.FirstOrderSemantics.reduct M).mem (env H) (env F))
    (hHD : ∀ pi, (Project.FirstOrderSemantics.reduct M).mem pi (env H) → (Project.FirstOrderSemantics.reduct M).mem pi (env S))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hNames : ∀ j, HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F)
      (env (ForcingMapCalculus.five f s A X Y j)))
    (hFixed : ∀ j, Supported (fun a => env (rho a)) (env S) (env (ForcingMapCalculus.five f s A X Y j)))
    (hOrd : ForcingRawRank.Ordinal (env O))
    (hCheckedO : ForcingCheckName.Checked (env top) (env O) (env checkedO))
    (hCart : ForcingRelationGraph.Graph (orderFormula (rho 0) mul) ForcingCompletionGraph.trueRelation
      env (rho 6) top A checkedO (env Cart))
    (hChoices : ForcingConditionGraphs.FunctionOn (env O) (env choices))
    (hCandidates : ∀ i c, (Project.FirstOrderSemantics.reduct M).mem i (env O) → PureKuratowski.PairMember M i c (env choices) →
      ForcingUniformMaximum.Selected env rho G F mul (env H) (env p)
        (ForcingSliceParameters.parameterFormula rho G F S mul top O f s A X Y) (Source.SetLanguage.injection 2 0 1) i c)
    (hp : (Project.FirstOrderSemantics.reduct M).mem (env p) (env (rho 6)))
    (hs : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env s) (env Cart) (env X))
      (env (rho 6)) (env p) (Source.SetLanguage.surjection 0 1 2))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y))
      (env (rho 6)) (env p) (Source.SetLanguage.surjection 0 1 2)) :
    ∃ graph, ForcingRelationGraph.Graph (orderFormula (rho 0) mul)
        (relation (orderFormula (rho 0) mul) (domain rho G F)
          (ForcingSliceParameters.parameterFormula rho G F S mul top O f s A X Y) (rho 6) O choices)
        env (rho 6) top Y X graph ∧
      HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F) graph ∧
      Supported (fun a => env (rho a)) (env H) graph ∧
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph (env Y) (env X))
        (env (rho 6)) (env p) (Source.SetLanguage.injection 0 1 2) := by
  let R := orderFormula (rho 0) mul
  let HC := domain rho G F
  let Q := ForcingSliceParameters.parameterFormula rho G F S mul top O f s A X Y
  let U := relation R HC Q (rho 6) O choices
  let W := env (rho 6)
  have hA := hNames (Fin.succ (Fin.succ (0 : Fin 3)))
  have hX := hNames (Fin.succ (Fin.succ (Fin.succ (0 : Fin 2))))
  have hY := hNames (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1)))))
  simp only [ForcingMapCalculus.five,args3,args2,args1,Fin.cases_zero,Fin.cases_succ] at hA hX hY
  have hFixX := hFixed (Fin.succ (Fin.succ (Fin.succ (0 : Fin 2))))
  have hFixY := hFixed (Fin.succ (Fin.succ (Fin.succ (Fin.succ (0 : Fin 1)))))
  simp only [ForcingMapCalculus.five,args3,args2,args1,Fin.cases_zero,Fin.cases_succ] at hFixX hFixY
  have hParameters : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i (env O) → ∃ a b, Holds Q env i a b := by
    intro i _hi
    obtain ⟨v,hv⟩ := ForcingSliceParameters.parameter_exists hM env rho I K B w G F S mul top O f s A X Y
      hPres hG hF hS hSF ht hNames hFixed i
    have he : args2 (v 0) (v 1) = v := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t)) j
    exact ⟨v 0,v 1,(parameter_pair env Q i (v 0) (v 1)).mpr (by rw [he]; exact hv)⟩
  have hFamily : ∀ i c, (Project.FirstOrderSemantics.reduct M).mem i (env O) → PureKuratowski.PairMember M i c (env choices) →
      ∀ a b, Holds Q env i a b → Force R HC env (args3 c a b) W (env p) (Source.SetLanguage.injection 0 1 2) := by
    intro i c hi hc a b hQ
    exact (injection_pair hM hpre hp).mp ((hCandidates i c hi hc).2.2 (args2 a b) ((parameter_pair env Q i a b).mp hQ))
  have hMove : ForcingRelationGraphSupport.Moves U env rho G F H := by
    intro pi hpi act hAct p' q x y x' y' hpW hpq _hx _hy hxx hyy hRel
    apply (relation_semantics env R HC Q (rho 6) O choices q x' y').mpr
    apply move hM env rho G F mul Q hPres hG hF ((hG pi).mp (hH.1 pi hpi)) hAct ?_ ?_ hpq hxx hyy
      ((relation_semantics env R HC Q (rho 6) O choices p' x y).mp hRel)
    · intro i c hi hc
      exact (hCandidates i c hi hc).2.1 pi hpi act hAct
    · intro i a b _hi hQ
      have hFix := ForcingSliceParameters.parameter_fixed env rho G F S mul top O f s A X Y ((parameter_pair env Q i a b).mp hQ)
      exact ⟨hFix 0 pi (hHD pi hpi) act hAct,hFix 1 pi (hHD pi hpi) act hAct⟩
  obtain ⟨graph,hGraph,hGraphHS,hGraphFix⟩ := ForcingRelationGraphSupport.construct hM U env rho I K B w G F H mul top Y X
    hPres hG hF hH ht hY hX (fun pi hpi act hAct => hFixY pi (hHD pi hpi) act hAct)
    (fun pi hpi act hAct => hFixX pi (hHD pi hpi) act hAct) hMove hHF
  have hMono : ForcingRelationGraphForcing.Monotone R (ForcingRelationGraphApplication.actionAt rho) U env W (env G) (env F) := by
    intro p' q x y hpW hq hqp _hx _hy hRel
    exact (relation_semantics env R HC Q (rho 6) O choices q x y).mpr
      (mono hpre hq hpW hqp ((relation_semantics env R HC Q (rho 6) O choices p' x y).mp hRel))
  have hCongr : ForcingRelationGraphForcing.Congruent R (ForcingRelationGraphApplication.actionAt rho) U env W (env G) (env F) := by
    intro p' x y x' y' _hx _hy _hx' _hy' hxx hyy
    rw [relation_semantics,relation_semantics]
    exact congruent hM hpre hxx hyy
  have hRegular : ForcingRelationGraphForcing.Regular R (ForcingRelationGraphApplication.actionAt rho) U env W (env G) (env F) := by
    intro p' x y _hpW _hx _hy hDense
    apply (relation_semantics env R HC Q (rho 6) O choices p' x y).mpr
    apply regular hpre
    intro q hq hqp
    obtain ⟨r,hr,hrq,hRel⟩ := hDense q hq hqp
    exact ⟨r,hr,hrq,(relation_semantics env R HC Q (rho 6) O choices r x y).mp hRel⟩
  have hTotal : ForcingRelationGraphFunctions.Total R (ForcingRelationGraphApplication.actionAt rho) U env W (env G) (env F) (env Y) (env X) (env p) := by
    intro x hx q hq hqp hxY r hr hrq
    have hx' := (domain_semantics env rho G F x).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hx)
    obtain ⟨t,ht,htr,y,hy,hyX,hRel⟩ := union_total hM env rho G F S mul top O f s A X Y hpre hX hY hOrd
      I K B w checkedO Cart p hPres hG hF ht hA hCheckedO hCart hChoices hParameters hFamily hp hs hf x hx' q hq hqp hxY r hr hrq
    exact ⟨t,ht,htr,y,(ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mpr ((domain_semantics env rho G F y).mp hy),hyX,
      (relation_semantics env R HC Q (rho 6) O choices t x y).mpr hRel⟩
  have hOne : ForcingRelationGraphFunctions.One R (ForcingRelationGraphApplication.actionAt rho) U env W (env G) (env F) (env p) := by
    intro q hq hqp x y z hx hy hz hRel hRel'
    exact union_one hM env rho G F S mul top O f s A X Y hpre hX hY hOrd hChoices hFamily hp
      ((domain_semantics env rho G F x).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hx))
      ((domain_semantics env rho G F y).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hy))
      ((domain_semantics env rho G F z).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hz)) hq hqp
      ((relation_semantics env R HC Q (rho 6) O choices q x y).mp hRel) ((relation_semantics env R HC Q (rho 6) O choices q x z).mp hRel')
  have hInj : ForcingRelationGraphFunctions.Injective R (ForcingRelationGraphApplication.actionAt rho) U env W (env G) (env F) (env p) := by
    intro q hq hqp x y z hx hy hz hRel hRel'
    exact union_injective hM env rho G F S mul top O f s A X Y hpre hX hY hOrd hChoices hFamily hp
      (ForcingImageQuotient.surjection_mapsTo_reuse hM hpre hp hf)
      ((domain_semantics env rho G F x).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hx))
      ((domain_semantics env rho G F y).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hy))
      ((domain_semantics env rho G F z).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hz)) hq hqp
      ((relation_semantics env R HC Q (rho 6) O choices q x z).mp hRel) ((relation_semantics env R HC Q (rho 6) O choices q y z).mp hRel')
  refine ⟨graph,hGraph,hGraphHS,hGraphFix,?_⟩
  exact ForcingRelationGraphFunctions.graph_injection hM env rho G F mul top Y X U (args3 graph (env Y) (env X)) 0 1 2
    hPres hG hF ht hpre hY hX hMono hCongr hRegular hGraph rfl rfl hTotal hOne hInj hp


/-- Source uniformly supported candidate function input, not a target oracle. -/
def candidates {k : Nat} (rho : Fin 7 → Fin k) (G F mul H p O choices : Fin k) (Q : Formula (k+3)) : Formula k :=
  .all (.all ((Formula.mem (Fin.last k).castSucc O.castSucc.castSucc).imp
    ((Source.SetLanguage.edge choices.castSucc.castSucc (Fin.last k).castSucc (Fin.last (k+1))).imp
      (ForcingUniformMaximum.selected (n := 2) id rho G F mul H p Q (Source.SetLanguage.injection 2 0 1)))))

theorem candidates_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul H p O choices : Fin k) (Q : Formula (k+3)) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (candidates rho G F mul H p O choices Q) ↔
      ∀ i c, (Project.FirstOrderSemantics.reduct M).mem i (env O) → PureKuratowski.PairMember M i c (env choices) →
        ForcingUniformMaximum.Selected (n := 2) env rho G F mul (env H) (env p) Q (Source.SetLanguage.injection 2 0 1) i c := by
  simp only [candidates,Formula.Realize,KuratowskiZF.source_edge,ForcingUniformMaximum.selected_semantics,
    Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  rfl

private theorem args3_map {α : Type v} {β : Type u} (f : α → β) (a b c : α) :
    (fun j => f (args3 a b c j)) = args3 (f a) (f b) (f c) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t))) j

/-- The actual collected HS graph and its support are retained in the object
conclusion, in addition to the FULL source injection formula. -/
def resultFormula {k : Nat} (rho : Fin 7 → Fin k) (G F S H mul top O f s A X Y choices p : Fin k) : Formula k :=
  let R := orderFormula (rho 0) mul
  let HC := domain rho G F
  let Q := ForcingSliceParameters.parameterFormula rho G F S mul top O f s A X Y
  let U := relation R HC Q (rho 6) O choices
  let rr : Fin 7 → Fin (k+1) := fun j => (rho j).castSucc
  let J := Fin.last k
  .ex ((ForcingRelationGraph.graph R U Fin.castSucc (rho 6) top Y X J).conj
    ((ForcingHS.hs actionFormula rr G.castSucc (rho 6).castSucc F.castSucc J).conj
      ((ForcingEquivariantMix.fixedAll rr H.castSucc J).conj
        (ForcingFormula.formula R HC Fin.castSucc (args3 J Y.castSucc X.castSucc) (rho 6).castSucc p.castSucc
          (Source.SetLanguage.injection 0 1 2)))))

theorem resultFormula_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F S H mul top O f s A X Y choices p : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (resultFormula rho G F S H mul top O f s A X Y choices p) ↔
      ∃ graph, ForcingRelationGraph.Graph (orderFormula (rho 0) mul)
          (relation (orderFormula (rho 0) mul) (domain rho G F)
            (ForcingSliceParameters.parameterFormula rho G F S mul top O f s A X Y) (rho 6) O choices)
          env (rho 6) top Y X graph ∧
        HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F) graph ∧
        Supported (fun a => env (rho a)) (env H) graph ∧
        Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph (env Y) (env X))
          (env (rho 6)) (env p) (Source.SetLanguage.injection 0 1 2) := by
  simp only [resultFormula,Formula.Realize,ForcingRelationGraph.graph_semantics,ForcingHS.hs_semantics,
    ForcingEquivariantMix.fixedAll_semantics,ForcingFormula.formula_semantics,args3_map,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def sentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F S H mul top O f s A X Y checkedO Cart choices p : Fin k) : Project.Sentence where
  formula :=
    let R := orderFormula (rho 0) mul
    let HC := domain rho G F
    let Q := ForcingSliceParameters.parameterFormula rho G F S mul top O f s A X Y
    Project.Formula.forallClosure k
      ([ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
        ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
        ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
        ProjectSyntax.encode id (ForcingConjugationGraph.subgroup I G S),
        .mem (.bound S) (.bound F),
        ProjectSyntax.encode id (ForcingConjugationGraph.subgroup I G H),
        .mem (.bound H) (.bound F),
        Project.Formula.subset (.bound H) (.bound S),
        ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
        ProjectSyntax.encode id (ForcingAtomicBasic.preorder R id (rho 6)),
        ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F f),
        ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F s),
        ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F A),
        ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F X),
        ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F Y),
        ProjectSyntax.encode id (ForcingSupportingRoot.tupleSupported rho S (ForcingMapCalculus.five f s A X Y)),
        ProjectSyntax.encode id (OrdinalSyntax.ordinal O),
        ProjectSyntax.encode id (ForcingCheckName.checkName top O checkedO),
        ProjectSyntax.encode id (ForcingRelationGraph.graph R ForcingCompletionGraph.trueRelation id (rho 6) top A checkedO Cart),
        ProjectSyntax.encode id (Source.SetLanguage.functionOn choices O),
        ProjectSyntax.encode id (candidates rho G F mul H p O choices Q),
        .mem (.bound p) (.bound (rho 6)),
        ProjectSyntax.encode id (ForcingFormula.formula R HC id (args3 s Cart X) (rho 6) p (Source.SetLanguage.surjection 0 1 2)),
        ProjectSyntax.encode id (ForcingFormula.formula R HC id (args3 f X Y) (rho 6) p (Source.SetLanguage.surjection 0 1 2))].foldr Definitional.Formula.imp
          (ProjectSyntax.encode id (resultFormula rho G F S H mul top O f s A X Y choices p)))
  freeClosed := by
    simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.subset]

theorem models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F S H mul top O f s A X Y checkedO Cart choices p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sentence rho I K B w G F S H mul top O f s A X Y checkedO Cart choices p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingNormalFilter.normal_semantics,ForcingConjugationGraph.subgroup_semantics,
    ForcingWithTopCarrier.empty_semantics,ForcingAtomicBasic.preorder_semantics,ForcingHS.hs_semantics,
    ForcingSupportingRoot.tupleSupported_semantics,ForcingRawRank.ordinal_semantics,ForcingCheckName.checkName_semantics,
    ForcingRelationGraph.graph_semantics,ForcingConditionGraphs.functionOn_semantics (M := M),
    candidates_semantics,ForcingFormula.formula_semantics,resultFormula_semantics,id_eq,args3_map]
  intro hPres hG hF hS hSF hH hHF hHD ht hpre hfHS hsHS hA hX hY hFixed hOrd hO hCart hChoices hCandidates hp hs hf
  have hNames : ∀ j, HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F)
      (env (ForcingMapCalculus.five f s A X Y j)) := by
    intro j
    exact Fin.cases hfHS (Fin.cases hsHS (Fin.cases hA (Fin.cases hX (Fin.cases hY (fun t => Fin.elim0 t))))) j
  exact assemble hM env rho I K B w G F S H mul top O f s A X Y checkedO Cart choices p
    hPres hG hF hS hSF hH hHF hHD ht hpre hNames hFixed hOrd hO hCart hChoices hCandidates hp hs hf

/-- Ordinary nativeZF original proof-kernel theorem for the complete source
assemble consumer. Actual candidate construction is the separate, completed
previous adapter; presentation_reverse_injection still must compose them. -/
theorem kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w G F S H mul top O f s A X Y checkedO Cart choices p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence
      (sentence rho I K B w G F S H mul top O f s A X Y checkedO Cart choices p)) :=
  ModelTransfer.derives (fun _ hM => models rho I K B w G F S H mul top O f s A X Y checkedO Cart choices p hM)

end PPAC.Migration.ForcingSliceAssembly
