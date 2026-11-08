/- Pinned OrderedSections.sectionPart/familyUnion/section_injection_of_uniform.
Use an ACTUAL INTERNAL graph of section names and the existing HS collector;
retain every source functionOn/no-junk/injectivity clause. -/
import PPAC.Migration.ForcingUniformMaximum
import PPAC.Migration.ForcingIndexedImage

namespace PPAC.Migration.ForcingSectionInjection
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args2 args3)
open ForcingMapConditions (MapRel)
open ForcingFormula (Force)
open ForcingAtomicRelations (Forces)
open ForcingClassEvaluation (Predicate)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingPairUnion (domain domain_semantics)
open ForcingRelationGraphForcing (Holds)
open ForcingCheckName (Checked)
open ForcingHS (HS)
open ForcingSupportedNames (Supported)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000
universe u v
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

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


def Part {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (P J Y ci nu p y z : M.Carrier .set) : Prop :=
  Forces false R env P y Y p ∧ Force R H env (args3 J y ci) P p (Source.SetLanguage.edge 0 1 2) ∧
    Forces true R env P z nu p

private def values (J Y ci nu y z : M.Carrier .set) : Fin 6 → M.Carrier .set :=
  Fin.lastCases z (Fin.lastCases y (Fin.cases J (args3 Y ci nu)))

private def partAtom : Formula 6 :=
  (Formula.mem 4 1).conj ((Source.SetLanguage.edge 0 4 2).conj (Formula.equal 5 3))

private theorem part_force_iff (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P J Y ci nu p y z : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) :
    Force R H env (values J Y ci nu y z) P p partAtom ↔ Part R H env P J Y ci nu p y z := by
  change (Forces false R env P y Y p ∧ Force R H env (values J Y ci nu y z) P p
    (Source.SetLanguage.edge 0 4 2) ∧ Forces true R env P z nu p) ↔ _
  rw [ForcingRelationClass.edge_formula hM hpre hp _ (0 : Fin 6) 4 2]
  rfl

def partFormula {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (P J Y ci nu p y z : Fin m) : Formula m :=
  (ForcingAtomicRelations.forces false R base P y Y p).conj
    ((ForcingFormula.formula R H base (args3 J y ci) P p (Source.SetLanguage.edge 0 1 2)).conj
      (ForcingAtomicRelations.forces true R base P z nu p))

theorem partFormula_semantics {k m : Nat} (v : Fin m → M.Carrier .set) (R : Formula (k+2)) (H : Formula (k+1))
    (base : Fin k → Fin m) (P J Y ci nu p y z : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v (partFormula R H base P J Y ci nu p y z) ↔
      Part R H (fun j => v (base j)) (v P) (v J) (v Y) (v ci) (v nu) (v p) (v y) (v z) := by
  simp only [partFormula,Part,Formula.Realize,ForcingAtomicRelations.forces_semantics (M := M),ForcingFormula.formula_semantics]
  rfl

/-- Source regularized familyUnion, all ground indices and actual family edges. -/
def Union {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (P A choices top J Y p y z : M.Carrier .set) : Prop :=
  ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p → ∃ r,
    (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧ ∃ i,
      (Project.FirstOrderSemantics.reduct M).mem i A ∧ ∃ nu, PureKuratowski.PairMember M i nu choices ∧
        ∃ ci, Checked top i ci ∧ Part R H env P J Y ci nu r y z

def unionFormula {k m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (P A choices top J Y p y z : Fin m) : Formula m :=
  let up : Fin m → Fin (m+5) := fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc
  let b : Fin k → Fin (m+5) := fun j => up (base j)
  let q := (Fin.last m).castSucc.castSucc.castSucc.castSucc
  let r := (Fin.last (m+1)).castSucc.castSucc.castSucc
  let i := (Fin.last (m+2)).castSucc.castSucc
  let nu := (Fin.last (m+3)).castSucc
  let ci := Fin.last (m+4)
  .all ((Formula.mem (Fin.last m) P.castSucc).imp
    ((ReplacementPredicates.rel R (fun j => (base j).castSucc) (Fin.last m) p.castSucc).imp
      (.ex (.ex (.ex (.ex ((Formula.mem r (up P)).conj
        ((ReplacementPredicates.rel R b r q).conj ((Formula.mem i (up A)).conj
          ((Source.SetLanguage.edge (up choices) i nu).conj ((ForcingCheckName.checkName (up top) i ci).conj
            (partFormula R H b (up P) (up J) (up Y) ci nu r (up y) (up z)))))))))))))

theorem unionFormula_semantics {k m : Nat} (v : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m) (P A choices top J Y p y z : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem v (unionFormula R H base P A choices top J Y p y z) ↔
      Union R H (fun j => v (base j)) (v P) (v A) (v choices) (v top) (v J) (v Y) (v p) (v y) (v z) := by
  simp only [unionFormula,Union,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    KuratowskiZF.source_edge,ForcingCheckName.checkName_semantics (M := M),partFormula_semantics,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  constructor
  · intro h q hq hqp
    obtain ⟨r,i,nu,ci,hr,hrq,hi,hNu,hCi,hPart⟩ := h q hq hqp
    exact ⟨r,hr,hrq,i,hi,nu,hNu,ci,hCi,hPart⟩
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,i,hi,nu,hNu,ci,hCi,hPart⟩ := h q hq hqp
    exact ⟨r,i,nu,ci,hr,hrq,hi,hNu,hCi,hPart⟩

def relation {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (P A choices top J Y : Fin k) : Formula (k+3) :=
  unionFormula R H (fun j => j.castSucc.castSucc.castSucc) P.castSucc.castSucc.castSucc A.castSucc.castSucc.castSucc
    choices.castSucc.castSucc.castSucc top.castSucc.castSucc.castSucc J.castSucc.castSucc.castSucc Y.castSucc.castSucc.castSucc
    (Fin.last k).castSucc.castSucc (Fin.last (k+1)).castSucc (Fin.last (k+2))

theorem relation_semantics {k : Nat} (env : Fin k → M.Carrier .set) (R : Formula (k+2)) (H : Formula (k+1))
    (P A choices top J Y : Fin k) (p y z : M.Carrier .set) :
    Holds (relation R H P A choices top J Y) env p y z ↔ Union R H env (env P) (env A) (env choices) (env top) (env J) (env Y) p y z := by
  simp only [relation,Holds,unionFormula_semantics,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem mono {k : Nat} {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P A choices top J Y p q y z : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) (hq : (Project.FirstOrderSemantics.reduct M).mem q P)
    (hqp : MapRel R env q p) (h : Union R H env P A choices top J Y p y z) : Union R H env P A choices top J Y q y z := by
  intro r hr hrq
  exact h r hr (hpre.2 r q p hr hq hp hrq hqp)

theorem regular {k : Nat} {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P A choices top J Y p y z : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (h : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p → ∃ r,
      (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧ Union R H env P A choices top J Y r y z) :
    Union R H env P A choices top J Y p y z := by
  intro q hq hqp
  obtain ⟨r,hr,hrq,hRel⟩ := h q hq hqp
  obtain ⟨s,hs,hsr,i,hi,nu,hNu,ci,hCi,hPart⟩ := hRel r hr (hpre.1 r hr)
  exact ⟨s,hs,hpre.2 s r q hs hr hq hsr hrq,i,hi,nu,hNu,ci,hCi,hPart⟩

theorem congruent (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P A choices top J Y p y z y' z' : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hyy : Forces true R env P y y' p) (hzz : Forces true R env P z z' p) :
    Union R H env P A choices top J Y p y z ↔ Union R H env P A choices top J Y p y' z' := by
  have step {y z y' z'} (hyy : Forces true R env P y y' p) (hzz : Forces true R env P z z' p)
      (h : Union R H env P A choices top J Y p y z) : Union R H env P A choices top J Y p y' z' := by
    intro q hq hqp
    obtain ⟨r,hr,hrq,i,hi,nu,hNu,ci,hCi,hPart⟩ := h q hq hqp
    have hrp := hpre.2 r q p hr hq hp hrq hqp
    refine ⟨r,hr,hrq,i,hi,nu,hNu,ci,hCi,(part_force_iff hM hpre hr).mp ?_⟩
    apply (ForcingFormula.tuple_congr hM hpre partAtom (values J Y ci nu y z) (values J Y ci nu y' z') r hr ?_).mp
      ((part_force_iff hM hpre hr).mpr hPart)
    intro j
    exact Fin.cases (ForcingAtomicBasic.eq_refl hM hpre J r hr)
      (Fin.cases (ForcingAtomicBasic.eq_refl hM hpre Y r hr) (Fin.cases (ForcingAtomicBasic.eq_refl hM hpre ci r hr)
        (Fin.cases (ForcingAtomicBasic.eq_refl hM hpre nu r hr) (Fin.cases
          (ForcingAtomicBasic.eq_mono hM hpre hr hrp hyy) (Fin.cases
            (ForcingAtomicBasic.eq_mono hM hpre hr hrp hzz) (fun a => Fin.elim0 a)))))) j
  exact ⟨step hyy hzz,step (ForcingAtomicBasic.eq_symm hM hyy) (ForcingAtomicBasic.eq_symm hM hzz)⟩


/-- The exact forced indexedSection form of source hs. The equivalence
with its original pointwise clause is proved below under the same preorder. -/
def Sections {k : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (P A choices top f X Y J p : M.Carrier .set) : Prop :=
  ∀ i, (Project.FirstOrderSemantics.reduct M).mem i A → ∀ nu, PureKuratowski.PairMember M i nu choices →
    ∀ ci, Checked top i ci → Force R H env (Fin.lastCases nu (ForcingMapCalculus.five f X Y J ci)) P p ForcingOrderedSections.indexedSection

theorem sections_iff (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P A choices top f X Y J p : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P) :
    Sections R H env P A choices top f X Y J p ↔
      ∀ i, (Project.FirstOrderSemantics.reduct M).mem i A → ∀ nu, PureKuratowski.PairMember M i nu choices →
        ∀ ci, Checked top i ci → ∀ y, Predicate H env y → ∀ q,
          (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p → Forces false R env P y Y q →
            Force R H env (args3 J y ci) P q (Source.SetLanguage.edge 0 1 2) →
              Forces false R env P nu X q ∧ Force R H env (args3 f nu y) P q (Source.SetLanguage.edge 0 1 2) := by
  constructor
  · intro h i hi nu hNu ci hCi y hy q hq hqp hyY hJ
    exact (ForcingOrderedSections.forces_indexedSection hM hpre hp f X Y J ci nu).mp
      (h i hi nu hNu ci hCi) y hy q hq hqp hyY q hq (hpre.1 q hq) hJ
  · intro h i hi nu hNu ci hCi
    apply (ForcingOrderedSections.forces_indexedSection hM hpre hp f X Y J ci nu).mpr
    intro y hy q hq hqp hyY r hr hrq hJ
    exact h i hi nu hNu ci hCi y hy r hr (hpre.2 r q p hr hq hp hrq hqp)
      (ForcingAtomicBasic.mem_mono hM hpre hr hrq hyY) hJ

/-- Source one-to-one-ness of J is NOT assumed here: its mapsTo uniqueness
already identifies the actual check indices, then FunctionOn identifies choices. -/
theorem one (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P A choices top J Y checkedA p q y z w : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hChoices : ForcingConditionGraphs.FunctionOn A choices)
    (hCheck : ∀ i ci, Checked top i ci → Predicate H env ci)
    (ht : (Project.FirstOrderSemantics.reduct M).mem top P)
    (hTop : ∀ a, (Project.FirstOrderSemantics.reduct M).mem a P → MapRel R env a top)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hJ : Force R H env (args3 J Y checkedA) P p (Source.SetLanguage.mapsTo 0 1 2))
    (hy : Predicate H env y) (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel R env q p)
    (hz : Union R H env P A choices top J Y q y z) (hw : Union R H env P A choices top J Y q y w) :
    Forces true R env P z w q := by
  apply ForcingAtomicBasic.eq_of_dense hM hpre hq
  intro r hr hrq
  obtain ⟨s,hs,hsr,i,hi,nu,hNu,ci,hCi,hPart⟩ := hz r hr hrq
  have hsq := hpre.2 s r q hs hr hq hsr hrq
  obtain ⟨t,htP,hts,j,_hj,mu,hMu,cj,hCj,hPart'⟩ := hw s hs hsq
  have htq := hpre.2 t s q htP hs hq hts hsq
  have htp := hpre.2 t q p htP hq hp htq hqp
  have hcEq := ForcingKernelImage.mapsTo_unique_reuse hM hpre hp htP htp hJ hy (hCheck i ci hCi) (hCheck j cj hCj)
    (ForcingAtomicBasic.mem_mono hM hpre htP hts hPart.1)
    (ForcingFormula.mono hM hpre _ _ hs htP hts hPart.2.1) hPart'.2.1
  have hij := (ForcingCheckReflection.eq_check_iff hM hpre ht hTop htP hCi hCj).mp hcEq
  cases hij
  obtain ⟨chosen,_hChosen,hUnique⟩ := hChoices.2 i hi
  have hnuMu := (hUnique nu hNu).trans (hUnique mu hMu).symm
  cases hnuMu
  exact ⟨t,htP,hpre.2 t s r htP hs hr hts hsr,ForcingAtomicLaws.eq_trans hM hpre
    (ForcingAtomicBasic.eq_mono hM hpre htP hts hPart.2.2) (ForcingAtomicBasic.eq_symm hM hPart'.2.2)⟩

theorem injective (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P A choices top f X Y J p q y z x : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hf : Force R H env (args3 f X Y) P p (Source.SetLanguage.mapsTo 0 1 2))
    (hSections : Sections R H env P A choices top f X Y J p)
    (hy : Predicate H env y) (hz : Predicate H env z) (hx : Predicate H env x)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel R env q p)
    (hY : Union R H env P A choices top J Y q y x) (hZ : Union R H env P A choices top J Y q z x) :
    Forces true R env P y z q := by
  have hValue := (sections_iff hM hpre hp).mp hSections
  apply ForcingAtomicBasic.eq_of_dense hM hpre hq
  intro r hr hrq
  obtain ⟨s,hs,hsr,i,hi,nu,hNu,ci,hCi,hPart⟩ := hY r hr hrq
  have hsq := hpre.2 s r q hs hr hq hsr hrq
  obtain ⟨t,ht,hts,j,hj,mu,hMu,cj,hCj,hPart'⟩ := hZ s hs hsq
  have htq := hpre.2 t s q ht hs hq hts hsq
  have htp := hpre.2 t q p ht hq hp htq hqp
  have hys := hValue i hi nu hNu ci hCi y hy t ht htp
    (ForcingAtomicBasic.mem_mono hM hpre ht hts hPart.1)
    (ForcingFormula.mono hM hpre _ _ hs ht hts hPart.2.1)
  have hzs := hValue j hj mu hMu cj hCj z hz t ht htp hPart'.1 hPart'.2.1
  have hEqXNu := ForcingAtomicBasic.eq_mono hM hpre ht hts hPart.2.2
  have hxy := app_congr hM hpre ht (ForcingAtomicBasic.eq_refl hM hpre f t ht)
    (ForcingAtomicBasic.eq_symm hM hEqXNu) (ForcingAtomicBasic.eq_refl hM hpre y t ht) hys.2
  have hxz := app_congr hM hpre ht (ForcingAtomicBasic.eq_refl hM hpre f t ht)
    (ForcingAtomicBasic.eq_symm hM hPart'.2.2) (ForcingAtomicBasic.eq_refl hM hpre z t ht) hzs.2
  have hxX : Forces false R env P x X t :=
    (ForcingFormula.tuple_congr (H := H) hM hpre (.mem (0 : Fin 2) 1) (args2 x X) (args2 mu X) t ht
      (fun a => Fin.cases hPart'.2.2 (Fin.cases (ForcingAtomicBasic.eq_refl hM hpre X t ht) (fun b => Fin.elim0 b)) a)).mpr hzs.1
  exact ⟨t,ht,hpre.2 t s r ht hs hr hts hsr,ForcingKernelImage.mapsTo_unique_reuse hM hpre hp ht htp hf hx hy hz hxX hxy hxz⟩

theorem total (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P A choices top f X Y J checkedA p q y r : M.Carrier .set}
    (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hChoices : ForcingConditionGraphs.FunctionOn A choices)
    (hFamily : ∀ i nu, (Project.FirstOrderSemantics.reduct M).mem i A → PureKuratowski.PairMember M i nu choices → Predicate H env nu)
    (ht : (Project.FirstOrderSemantics.reduct M).mem top P)
    (hTop : ∀ a, (Project.FirstOrderSemantics.reduct M).mem a P → MapRel R env a top)
    (hCheckedA : Checked top A checkedA)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hJ : Force R H env (args3 J Y checkedA) P p (Source.SetLanguage.mapsTo 0 1 2))
    (hSections : Sections R H env P A choices top f X Y J p)
    (hy : Predicate H env y) (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel R env q p)
    (hyY : Forces false R env P y Y q) (hr : (Project.FirstOrderSemantics.reduct M).mem r P) (hrq : MapRel R env r q) :
    ∃ t, (Project.FirstOrderSemantics.reduct M).mem t P ∧ MapRel R env t r ∧ ∃ nu,
      Predicate H env nu ∧ Forces false R env P nu X t ∧ Union R H env P A choices top J Y t y nu := by
  obtain ⟨s,hs,hsr,j,_hj,hjA,hyj⟩ := ForcingImageQuotient.mapsTo_total_reuse hM hpre hp hJ hy hq hqp hyY hr hrq
  obtain ⟨t,htP,hts,i,hi,ci,hCi,hEq⟩ := (ForcingInfinity.mem_check hM hCheckedA ht hTop hs).mp hjA s hs (hpre.1 s hs)
  obtain ⟨nu,hNu,_hUnique⟩ := hChoices.2 i hi
  have htr := hpre.2 t s r htP hs hr hts hsr
  have htq := hpre.2 t r q htP hr hq htr hrq
  have htp := hpre.2 t q p htP hq hp htq hqp
  have htyY := ForcingAtomicBasic.mem_mono hM hpre htP htq hyY
  have htyi := app_congr hM hpre htP (ForcingAtomicBasic.eq_refl hM hpre J t htP)
    (ForcingAtomicBasic.eq_refl hM hpre y t htP) hEq (ForcingFormula.mono hM hpre _ _ hs htP hts hyj)
  have hValue := (sections_iff hM hpre hp).mp hSections i hi nu hNu ci hCi y hy t htP htp htyY htyi
  refine ⟨t,htP,htr,nu,hFamily i nu hi hNu,hValue.1,?_⟩
  intro b hb hbt
  exact ⟨b,hb,hpre.1 b hb,i,hi,nu,hNu,ci,hCi,ForcingAtomicBasic.mem_mono hM hpre hb hbt htyY,
    ForcingFormula.mono hM hpre _ _ htP hb hbt htyi,ForcingAtomicBasic.eq_refl hM hpre nu b hb⟩

/-- Source sectionPart_move, via actual existing formula symmetry. -/
theorem part_move (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul J Y : Fin k)
    {I K B w pi act p q y z y' z' ci nu : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hpi : ForcingConditionGraphs.Permutation I pi) (hAct : MapRel actionFormula (fun j => env (rho j)) pi act)
    (hJ : ForcingStabilizer.Action (env (rho 6)) act (env J) (env J))
    (hY : ForcingStabilizer.Action (env (rho 6)) act (env Y) (env Y))
    (hCi : ForcingStabilizer.Action (env (rho 6)) act ci ci) (hNu : ForcingStabilizer.Action (env (rho 6)) act nu nu)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6))) (hpq : PureKuratowski.PairMember M p q act)
    (hyy : ForcingStabilizer.Action (env (rho 6)) act y y') (hzz : ForcingStabilizer.Action (env (rho 6)) act z z')
    (h : Part (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) (env J) (env Y) ci nu p y z) :
    Part (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) (env J) (env Y) ci nu q y' z' := by
  have hq := (ForcingProductFamily.action_permutation ((mapRel_action _ _ _).mp hAct)).1.2 p q hpq
  apply (part_force_iff hM hpre hq).mp
  apply (ForcingSeparation.symmetry hM env rho G F mul hPres hG hF hpi hAct partAtom
    (values (env J) (env Y) ci nu y z) (values (env J) (env Y) ci nu y' z')
    (fun j => Fin.cases hJ (Fin.cases hY (Fin.cases hCi (Fin.cases hNu (Fin.cases hyy
      (Fin.cases hzz (fun a => Fin.elim0 a)))))) j) hp hpq).mp
  exact (part_force_iff hM hpre hp).mpr h

theorem move (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top A choices J Y : Fin k)
    {I K B w pi act p q y z y' z' : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingNormalFilter.Normal I (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hpi : ForcingConditionGraphs.Permutation I pi) (hAct : MapRel actionFormula (fun j => env (rho j)) pi act)
    (hFixJ : ForcingStabilizer.Action (env (rho 6)) act (env J) (env J))
    (hFixY : ForcingStabilizer.Action (env (rho 6)) act (env Y) (env Y))
    (hFix : ∀ i nu, (Project.FirstOrderSemantics.reduct M).mem i (env A) → PureKuratowski.PairMember M i nu (env choices) →
      ForcingStabilizer.Action (env (rho 6)) act nu nu)
    (hpq : PureKuratowski.PairMember M p q act)
    (hyy : ForcingStabilizer.Action (env (rho 6)) act y y') (hzz : ForcingStabilizer.Action (env (rho 6)) act z z')
    (h : Union (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) (env A) (env choices) (env top) (env J) (env Y) p y z) :
    Union (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) (env A) (env choices) (env top) (env J) (env Y) q y' z' := by
  have ha := (mapRel_action (fun j => env (rho j)) pi act).mp hAct
  have hPerm := ForcingProductFamily.action_permutation ha
  have hOrder := ForcingProductFamily.order hM (env mul) hPres hpi ha
  intro t htP htq
  obtain ⟨t0,ht0,ht0t⟩ := hPerm.2.2 t htP
  have ht0p := (orderFormula_semantics env (rho 0) mul t0 p).mpr
    ((hOrder t0 p t q ht0t hpq).mpr ((orderFormula_semantics env (rho 0) mul t q).mp htq))
  obtain ⟨r,hr,hrt0,i,hi,nu,hNu,ci,hCi,hPart⟩ := h t0 ht0 ht0p
  obtain ⟨r',hrr',_⟩ := hPerm.1.1.2 r hr
  have hr' := hPerm.1.2 r r' hrr'
  have hr't := (orderFormula_semantics env (rho 0) mul r' t).mpr
    ((hOrder r t0 r' t hrr' ht0t).mp ((orderFormula_semantics env (rho 0) mul r t0).mp hrt0))
  have hCiFix := ForcingLabelNames.checked_fixed hM (fun j => env (rho j)) hPres ht ha hCi
  exact ⟨r',hr',hr't,i,hi,nu,hNu,ci,hCi,
    part_move hM env rho G F mul J Y hPres hG hF hpre hpi hAct hFixJ hFixY hCiFix (hFix i nu hi hNu) hr hrr' hyy hzz hPart⟩

theorem checked_hs (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w G F t x checked : M.Carrier .set}
    (hp : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G) (hF : ForcingNormalFilter.Normal I G F)
    (ht : ForcingWithTopCarrier.Empty t) (hc : Checked t x checked) : HS actionFormula v G (v 6) F checked := by
  have htW := (hp.2.2.2.2.2 t).mpr (Or.inl ht)
  apply ForcingHSCheck.check_hs hM actionFormula v G (v 6) F t hF.1 htW ?_ x checked hc
  intro pi hpi
  obtain ⟨act,ha⟩ := ForcingProductFamily.exists_action hM hp ((hG pi).mp hpi)
  exact ⟨act,(mapRel_action v pi act).mpr ha,(ForcingProductFamily.action_permutation ha).1,
    Or.inl ⟨htW,ForcingProductFamily.top_fixed hp ht ha⟩⟩


/-- Source section_injection_of_uniform. The exact original family input
is an INTERNAL FunctionOn graph, with source hs equivalent to Sections. -/
theorem construct (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F S mul top f X Y J A checkedA choices p : Fin k)
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hS : ForcingConjugationGraph.Subgroup (env I) (env G) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hX : HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F) (env X))
    (hY : HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F) (env Y))
    (hFixX : Supported (fun a => env (rho a)) (env S) (env X))
    (hFixY : Supported (fun a => env (rho a)) (env S) (env Y))
    (hFixJ : Supported (fun a => env (rho a)) (env S) (env J))
    (hChoices : ForcingConditionGraphs.FunctionOn (env A) (env choices))
    (hFamily : ForcingCollectedHS.FamilyHS (fun a => env (rho a)) (env G) (env (rho 6)) (env F) (env A) (env choices))
    (hFixed : ∀ i nu, (Project.FirstOrderSemantics.reduct M).mem i (env A) → PureKuratowski.PairMember M i nu (env choices) →
      Supported (fun a => env (rho a)) (env S) nu)
    (hCheckedA : Checked (env top) (env A) (env checkedA))
    (hp : (Project.FirstOrderSemantics.reduct M).mem (env p) (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y))
      (env (rho 6)) (env p) (Source.SetLanguage.mapsTo 0 1 2))
    (hJ : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env J) (env Y) (env checkedA))
      (env (rho 6)) (env p) (Source.SetLanguage.mapsTo 0 1 2))
    (hSections : Sections (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) (env A) (env choices)
      (env top) (env f) (env X) (env Y) (env J) (env p)) :
    ∃ graph, ForcingRelationGraph.Graph (orderFormula (rho 0) mul)
      (relation (orderFormula (rho 0) mul) (domain rho G F) (rho 6) A choices top J Y) env (rho 6) top Y X graph ∧
      HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F) graph ∧
      Supported (fun a => env (rho a)) (env S) graph ∧
      Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph (env Y) (env X))
        (env (rho 6)) (env p) (Source.SetLanguage.injection 0 1 2) := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  let Q := relation R H (rho 6) A choices top J Y
  have htW := (hPres.2.2.2.2.2 (env top)).mpr (Or.inl ht)
  have hTop : ∀ a, (Project.FirstOrderSemantics.reduct M).mem a W → MapRel R env a (env top) :=
    fun a _ => (orderFormula_semantics env (rho 0) mul a (env top)).mpr (Or.inl ht)
  have hCheck : ∀ i ci, Checked (env top) i ci → Predicate H env ci :=
    fun _ _ hc => (domain_semantics env rho G F _).mpr (checked_hs hM (fun a => env (rho a)) hPres hG hF ht hc)
  have hMove : ForcingRelationGraphSupport.Moves Q env rho G F S := by
    intro pi hpi act hAct a b y z y' z' _ha hab _hy _hz hyy hzz hRel
    apply (relation_semantics env R H (rho 6) A choices top J Y b y' z').mpr
    exact move hM env rho G F mul top A choices J Y hPres hG hF ht hpre
      ((hG pi).mp (hS.1 pi hpi)) hAct (hFixJ pi hpi act hAct) (hFixY pi hpi act hAct)
      (fun i nu hi hNu => hFixed i nu hi hNu pi hpi act hAct) hab hyy hzz
      ((relation_semantics env R H (rho 6) A choices top J Y a y z).mp hRel)
  obtain ⟨graph,hGraph,hGraphHS,hGraphFixed⟩ := ForcingRelationGraphSupport.construct hM Q env rho
    I K B w G F S mul top Y X hPres hG hF hS ht hY hX hFixY hFixX hMove hSF
  have hMono : ForcingRelationGraphForcing.Monotone R (ForcingRelationGraphApplication.actionAt rho) Q env W (env G) (env F) := by
    intro a b y z ha hb hba _hy _hz hRel
    exact (relation_semantics env R H (rho 6) A choices top J Y b y z).mpr
      (mono hpre ha hb hba ((relation_semantics env R H (rho 6) A choices top J Y a y z).mp hRel))
  have hCongr : ForcingRelationGraphForcing.Congruent R (ForcingRelationGraphApplication.actionAt rho) Q env W (env G) (env F) := by
    intro a y z y' z' _hy _hz _hy' _hz' hyy hzz
    rw [relation_semantics,relation_semantics]
    exact congruent hM hpre (ForcingAtomicBasic.condition hM hyy) hyy hzz
  have hRegular : ForcingRelationGraphForcing.Regular R (ForcingRelationGraphApplication.actionAt rho) Q env W (env G) (env F) := by
    intro a y z _ha _hy _hz hDense
    apply (relation_semantics env R H (rho 6) A choices top J Y a y z).mpr
    apply regular hpre
    intro b hb hba
    obtain ⟨c,hc,hcb,hRel⟩ := hDense b hb hba
    exact ⟨c,hc,hcb,(relation_semantics env R H (rho 6) A choices top J Y c y z).mp hRel⟩
  have hDomain (nu : M.Carrier .set)
      (hNu : HS (ForcingRelationGraphApplication.actionAt rho) env (env G) W (env F) nu) : Predicate H env nu :=
    (domain_semantics env rho G F nu).mpr ((ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mp hNu)
  refine ⟨graph,hGraph,hGraphHS,hGraphFixed,?_⟩
  apply ForcingRelationGraphFunctions.graph_injection hM env rho G F mul top Y X Q (args3 graph (env Y) (env X)) 0 1 2
    hPres hG hF ht hpre hY hX hMono hCongr hRegular hGraph rfl rfl ?_ ?_ ?_ hp
  · intro y hy q hq hqp hyY r hr hrq
    obtain ⟨t,htP,htr,nu,hNu,hNuX,hRel⟩ := total hM hpre hChoices
      (fun i nu hi hNu => (domain_semantics env rho G F nu).mpr (hFamily i nu hi hNu)) htW hTop hCheckedA hp hJ hSections
      (hDomain y hy) hq hqp hyY hr hrq
    exact ⟨t,htP,htr,nu,(ForcingRelationGraphApplication.hs_actionAt env rho _ _ _ _).mpr
      ((domain_semantics env rho G F nu).mp hNu),hNuX,(relation_semantics env R H (rho 6) A choices top J Y t y nu).mpr hRel⟩
  · intro q hq hqp y z w hy _hz _hw hRel hRel'
    exact one hM hpre hChoices hCheck htW hTop hp hJ (hDomain y hy) hq hqp
      ((relation_semantics env R H (rho 6) A choices top J Y q y z).mp hRel)
      ((relation_semantics env R H (rho 6) A choices top J Y q y w).mp hRel')
  · intro q hq hqp y z x hy hz hx hRel hRel'
    exact injective hM hpre hp hf hSections (hDomain y hy) (hDomain z hz) (hDomain x hx) hq hqp
      ((relation_semantics env R H (rho 6) A choices top J Y q y x).mp hRel)
      ((relation_semantics env R H (rho 6) A choices top J Y q z x).mp hRel')


private def sectionValues {a : Type v} (f X Y J ci nu : a) : Fin 6 → a :=
  Fin.lastCases nu (ForcingMapCalculus.five f X Y J ci)

private theorem sectionValues_map {a : Type v} {b : Type u} (g : a → b) (f X Y J ci nu : a) :
    (fun j => g (sectionValues f X Y J ci nu j)) = sectionValues (g f) (g X) (g Y) (g J) (g ci) (g nu) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))))) j

def sections {k : Nat} (R : Formula (k+2)) (H : Formula (k+1))
    (P A choices top f X Y J p : Fin k) : Formula k :=
  let up : Fin k → Fin (k+3) := fun j => j.castSucc.castSucc.castSucc
  let i := (Fin.last k).castSucc.castSucc
  let nu := (Fin.last (k+1)).castSucc
  let ci := Fin.last (k+2)
  .all ((Formula.mem (Fin.last k) A.castSucc).imp (.all
    ((Source.SetLanguage.edge choices.castSucc.castSucc (Fin.last k).castSucc (Fin.last (k+1))).imp (.all
      ((ForcingCheckName.checkName (up top) i ci).imp
        (ForcingFormula.formula R H up (sectionValues (up f) (up X) (up Y) (up J) ci nu)
          (up P) (up p) ForcingOrderedSections.indexedSection))))))

theorem sections_semantics {k : Nat} (env : Fin k → M.Carrier .set) (R : Formula (k+2)) (H : Formula (k+1))
    (P A choices top f X Y J p : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (sections R H P A choices top f X Y J p) ↔
      Sections R H env (env P) (env A) (env choices) (env top) (env f) (env X) (env Y) (env J) (env p) := by
  simp only [sections,Sections,Formula.Realize,KuratowskiZF.source_edge,ForcingCheckName.checkName_semantics (M := M),
    ForcingFormula.formula_semantics,sectionValues_map,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def Built {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F S mul top X Y J A choices p : Fin k) : Prop :=
  ∃ graph, ForcingRelationGraph.Graph (orderFormula (rho 0) mul)
    (relation (orderFormula (rho 0) mul) (domain rho G F) (rho 6) A choices top J Y) env (rho 6) top Y X graph ∧
    HS actionFormula (fun a => env (rho a)) (env G) (env (rho 6)) (env F) graph ∧
    Supported (fun a => env (rho a)) (env S) graph ∧
    Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 graph (env Y) (env X))
      (env (rho 6)) (env p) (Source.SetLanguage.injection 0 1 2)

def construction {k : Nat} (rho : Fin 7 → Fin k) (G F S mul top X Y J A choices p : Fin k) : Formula k :=
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let Q := relation R H (rho 6) A choices top J Y
  let up : Fin k → Fin (k+1) := Fin.castSucc
  let rr : Fin 7 → Fin (k+1) := fun j => up (rho j)
  let graph := Fin.last k
  .ex ((ForcingRelationGraph.graph R Q up (rho 6) top Y X graph).conj
    ((ForcingHS.hs actionFormula rr (up G) (up (rho 6)) (up F) graph).conj
      ((ForcingEquivariantMix.fixedAll rr (up S) graph).conj
        (ForcingFormula.formula R H up (args3 graph (up Y) (up X)) (up (rho 6)) (up p)
          (Source.SetLanguage.injection 0 1 2)))))

theorem construction_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F S mul top X Y J A choices p : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (construction rho G F S mul top X Y J A choices p) ↔
      Built env rho G F S mul top X Y J A choices p := by
  simp only [construction,Built,Formula.Realize,ForcingRelationGraph.graph_semantics (M := M),
    ForcingHS.hs_semantics (M := M),ForcingEquivariantMix.fixedAll_semantics,ForcingFormula.formula_semantics,
    Supported,Fin.lastCases_last,Fin.lastCases_castSucc]
  have hV (graph : M.Carrier .set) :
      (fun j => Fin.lastCases graph env (args3 (Fin.last k) Y.castSucc X.castSucc j)) = args3 graph (env Y) (env X) := by
    funext j
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))) j
    · change Fin.lastCases graph env (Fin.last k) = graph
      rw [Fin.lastCases_last]
    · change Fin.lastCases graph env Y.castSucc = env Y
      rw [Fin.lastCases_castSucc]
    · change Fin.lastCases graph env X.castSucc = env X
      rw [Fin.lastCases_castSucc]
  constructor
  · rintro ⟨graph,hGraph,hHS,hFix,hForce⟩
    rw [hV] at hForce
    exact ⟨graph,hGraph,hHS,hFix,hForce⟩
  · rintro ⟨graph,hGraph,hHS,hFix,hForce⟩
    refine ⟨graph,hGraph,hHS,hFix,?_⟩
    rw [hV]
    exact hForce

def sentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F S mul top f X Y J A checkedA choices p : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
      ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
      ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
      ProjectSyntax.encode id (ForcingConjugationGraph.subgroup I G S),
      .mem (.bound S) (.bound F),
      ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
      ProjectSyntax.encode id (ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F X),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F Y),
      ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho S X),
      ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho S Y),
      ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho S J),
      ProjectSyntax.encode id (Source.SetLanguage.functionOn choices A),
      ProjectSyntax.encode id (ForcingCollectedHS.familyHS rho G (rho 6) F A choices),
      ForcingIndexedGraph.fixedFamily rho S A choices,
      ProjectSyntax.encode id (ForcingCheckName.checkName top A checkedA),
      .mem (.bound p) (.bound (rho 6)),
      ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id
        (args3 f X Y) (rho 6) p (Source.SetLanguage.mapsTo 0 1 2)),
      ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id
        (args3 J Y checkedA) (rho 6) p (Source.SetLanguage.mapsTo 0 1 2)),
      ProjectSyntax.encode id (sections (orderFormula (rho 0) mul) (domain rho G F) (rho 6) A choices top f X Y J p)].foldr Definitional.Formula.imp
        (ProjectSyntax.encode id (construction rho G F S mul top X Y J A choices p)))
  freeClosed := by
    simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ForcingIndexedGraph.fixedFamily_freeClosed]

theorem models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F S mul top f X Y J A checkedA choices p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sentence rho I K B w G F S mul top f X Y J A checkedA choices p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingNormalFilter.normal_semantics,ForcingConjugationGraph.subgroup_semantics,
    ForcingWithTopCarrier.empty_semantics,ForcingAtomicBasic.preorder_semantics,ForcingHS.hs_semantics,
    ForcingEquivariantMix.fixedAll_semantics,ForcingConditionGraphs.functionOn_semantics (M := M),ForcingCollectedHS.familyHS_semantics,
    ForcingIndexedGraph.fixedFamily_semantics hM,ForcingCheckName.checkName_semantics,ForcingFormula.formula_semantics,
    sections_semantics,construction_semantics,id_eq]
  exact construct hM env rho I K B w G F S mul top f X Y J A checkedA choices p

theorem kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F S mul top f X Y J A checkedA choices p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sentence rho I K B w G F S mul top f X Y J A checkedA choices p)) :=
  ModelTransfer.derives (fun _ hM => models rho I K B w G F S mul top f X Y J A checkedA choices p hM)

end PPAC.Migration.ForcingSectionInjection
