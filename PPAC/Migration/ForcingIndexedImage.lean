/- Pinned OrderedSections.indexedImage/one/cover. The regular dense
inverse-bounded-app/composition is quoted as one source formula. -/
import PPAC.Migration.ForcingLeastRelation

namespace PPAC.Migration.ForcingIndexedImage
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
open ForcingLeastOccurrence (At)
open ForcingRawRank (Ordinal)
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

theorem injection_mapsTo (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p f X Y : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hf : Force R H env (args3 f X Y) P p (Source.SetLanguage.injection 0 1 2)) :
    Force R H env (args3 f X Y) P p (Source.SetLanguage.mapsTo 0 1 2) := by
  rw [Source.SetLanguage.injection,ForcingSound.rename hM hpre _ _ _ _ hp,ForcingFormula.force_conj] at hf
  exact hf.1

theorem injection_one (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p q f X Y x y z : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p P)
    (hf : Force R H env (args3 f X Y) P p (Source.SetLanguage.injection 0 1 2))
    (hx : ForcingClassEvaluation.Predicate H env x) (hy : ForcingClassEvaluation.Predicate H env y)
    (hz : ForcingClassEvaluation.Predicate H env z)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q P) (hqp : MapRel R env q p)
    (hxX : Forces false R env P x X q) (hyX : Forces false R env P y X q)
    (hxz : Force R H env (args3 f x z) P q (Source.SetLanguage.edge 0 1 2))
    (hyz : Force R H env (args3 f y z) P q (Source.SetLanguage.edge 0 1 2)) :
    Forces true R env P x y q := by
  rw [Source.SetLanguage.injection,ForcingSound.rename hM hpre _ _ _ _ hp,ForcingFormula.force_conj] at hf
  have hh := (ForcingFormula.force_all hM hpre hp _ _).mp hf.2 x hx
  have hh := (ForcingFormula.force_all hM hpre hp _ _).mp hh y hy
  have hh := (ForcingFormula.force_all hM hpre hp _ _).mp hh z hz
  have hh := (ForcingFormula.force_imp hM hpre hp _ _ _).mp hh q hq hqp hxX
  have hh := (ForcingFormula.force_imp hM hpre hq _ _ _).mp hh q hq (hpre.1 q hq) hyX
  have hh := (ForcingFormula.force_imp hM hpre hq _ _ _).mp hh q hq (hpre.1 q hq)
    ⟨(ForcingRelationClass.edge_formula hM hpre hq _ (0 : Fin 6) 3 5).mpr hxz,
      (ForcingRelationClass.edge_formula hM hpre hq _ (0 : Fin 6) 4 5).mpr hyz⟩
  exact hh


/-- Parameters f,J,X,Y,check(O), then check(i),y, with bound x. -/
def imageFormula : Formula 7 :=
  .ex ((Formula.mem 7 2).conj ((Formula.mem 5 4).conj ((Formula.mem 6 3).conj
    ((Source.SetLanguage.edge 1 7 5).conj (Source.SetLanguage.edge 0 7 6)))))

private theorem five_map {α : Type v} {β : Type u} (g : α → β) (f J X Y O : α) :
    (fun j => g (ForcingMapCalculus.five f J X Y O j)) =
      ForcingMapCalculus.five (g f) (g J) (g X) (g Y) (g O) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (fun i => Fin.elim0 i))))) j

/-- Exact regularized composition, with both bounded-app membership guards. -/
theorem image_force_dense (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {H : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {P p f J X Y checkedO ci y : M.Carrier .set} (hpre : ForcingAtomicBasic.PreorderOn R env P) :
    Force R H env (Fin.lastCases y (Fin.lastCases ci (ForcingMapCalculus.five f J X Y checkedO)))
      P p imageFormula ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q P → MapRel R env q p → ∃ r,
        (Project.FirstOrderSemantics.reduct M).mem r P ∧ MapRel R env r q ∧ ∃ x,
          Predicate H env x ∧ Forces false R env P x X r ∧ Forces false R env P ci checkedO r ∧
          Forces false R env P y Y r ∧
          Force R H env (args3 J x ci) P r (Source.SetLanguage.edge 0 1 2) ∧
          Force R H env (args3 f x y) P r (Source.SetLanguage.edge 0 1 2) := by
  change (∀ q, _ → _ → ∃ r, _ ∧ _ ∧ ∃ x, _ ∧ _ ∧ _ ∧ _ ∧
    Force R H env (Fin.lastCases x (Fin.lastCases y (Fin.lastCases ci (ForcingMapCalculus.five f J X Y checkedO))))
      P r (Source.SetLanguage.edge 1 7 5) ∧
    Force R H env (Fin.lastCases x (Fin.lastCases y (Fin.lastCases ci (ForcingMapCalculus.five f J X Y checkedO))))
      P r (Source.SetLanguage.edge 0 7 6)) ↔ _
  constructor
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,x,hx,hxX,hci,hY,hJ,hf⟩ := h q hq hqp
    exact ⟨r,hr,hrq,x,hx,hxX,hci,hY,
      (ForcingRelationClass.edge_formula hM hpre hr _ (1 : Fin 8) 7 5).mp hJ,
      (ForcingRelationClass.edge_formula hM hpre hr _ (0 : Fin 8) 7 6).mp hf⟩
  · intro h q hq hqp
    obtain ⟨r,hr,hrq,x,hx,hxX,hci,hY,hJ,hf⟩ := h q hq hqp
    exact ⟨r,hr,hrq,x,hx,hxX,hci,hY,
      (ForcingRelationClass.edge_formula hM hpre hr _ (1 : Fin 8) 7 5).mpr hJ,
      (ForcingRelationClass.edge_formula hM hpre hr _ (0 : Fin 8) 7 6).mpr hf⟩

def indexedImage {k : Nat} (rho : Fin 7 → Fin k) (G F mul top f J X Y checkedO : Fin k) : Formula (k+3) :=
  ForcingLeastRelation.occurrence rho G F mul top (ForcingMapCalculus.five f J X Y checkedO) imageFormula

theorem indexedImage_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top f J X Y checkedO : Fin k)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (p y i : M.Carrier .set) :
    ForcingRelationGraphForcing.Holds (indexedImage rho G F mul top f J X Y checkedO) env p y i ↔
      ∃ ci, Checked (env top) i ci ∧
        ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
          MapRel (orderFormula (rho 0) mul) env q p → ∃ r,
            (Project.FirstOrderSemantics.reduct M).mem r (env (rho 6)) ∧ MapRel (orderFormula (rho 0) mul) env r q ∧
            ∃ x, Predicate (domain rho G F) env x ∧
              Forces false (orderFormula (rho 0) mul) env (env (rho 6)) x (env X) r ∧
              Forces false (orderFormula (rho 0) mul) env (env (rho 6)) ci (env checkedO) r ∧
              Forces false (orderFormula (rho 0) mul) env (env (rho 6)) y (env Y) r ∧
              Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env J) x ci) (env (rho 6)) r (Source.SetLanguage.edge 0 1 2) ∧
              Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) x y) (env (rho 6)) r (Source.SetLanguage.edge 0 1 2) := by
  rw [indexedImage,ForcingLeastRelation.occurrence_semantics]
  unfold ForcingLeastRelation.Occurrence
  have hV (ci : M.Carrier .set) :
      ForcingLeastRelation.values env (ForcingMapCalculus.five f J X Y checkedO) ci y =
        Fin.lastCases y (Fin.lastCases ci (ForcingMapCalculus.five (env f) (env J) (env X) (env Y) (env checkedO))) := by
    unfold ForcingLeastRelation.values
    rw [five_map]
  simp only [hV,image_force_dense hM hpre]

/-- Pinned indexedImage_one. Function uniqueness is only required ON X. -/
theorem indexedImage_one (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top f J X Y O checkedO p : Fin k)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hCheck : ∀ i ci, Checked (env top) i ci → Predicate (domain rho G F) env ci)
    (hp : (Project.FirstOrderSemantics.reduct M).mem (env p) (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y))
      (env (rho 6)) (env p) (Source.SetLanguage.mapsTo 0 1 2))
    (hJ : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env J) (env X) (env checkedO))
      (env (rho 6)) (env p) (Source.SetLanguage.injection 0 1 2)) :
    ForcingLeastRelation.OneAt (orderFormula (rho 0) mul)
      (indexedImage rho G F mul top f J X Y checkedO) (domain rho G F) env
      (env (rho 6)) (env O) (env p) := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  intro i _hi q hq hqp y z hy hz hIy hIz
  obtain ⟨ci,hci,hY⟩ := (indexedImage_semantics hM env rho G F mul top f J X Y checkedO hpre q y i).mp hIy
  obtain ⟨cj,hcj,hZ⟩ := (indexedImage_semantics hM env rho G F mul top f J X Y checkedO hpre q z i).mp hIz
  have hc := ForcingCheckName.unique hM hci hcj
  cases hc
  apply ForcingAtomicBasic.eq_of_dense hM hpre hq
  intro r hr hrq
  obtain ⟨s,hs,hsr,x,hx,hxX,_hci,_hyY,hxci,hxy⟩ := hY r hr hrq
  have hsq := hpre.2 s r q hs hr hq hsr hrq
  obtain ⟨t,ht,hts,a,ha,haX,_hci,_hzY,haci,haz⟩ := hZ s hs hsq
  have htq := hpre.2 t s q ht hs hq hts hsq
  have htp := hpre.2 t q (env p) ht hq hp htq hqp
  have hxa := injection_one hM hpre hp hJ hx ha (hCheck i ci hci) ht htp
    (ForcingAtomicBasic.mem_mono hM hpre ht hts hxX) haX
    (ForcingFormula.mono hM hpre _ _ hs ht hts hxci) haci
  have hay := app_congr hM hpre ht (ForcingAtomicBasic.eq_refl hM hpre (env f) t ht)
    hxa (ForcingAtomicBasic.eq_refl hM hpre y t ht) (ForcingFormula.mono hM hpre _ _ hs ht hts hxy)
  exact ⟨t,ht,hpre.2 t s r ht hs hr hts hsr,
    ForcingKernelImage.mapsTo_unique_reuse hM hpre hp ht htp hf ha hy hz haX hay haz⟩

/-- Pinned indexedImage_cover: use actual onto/total witnesses and then
actual mem_check; no chosen family of preimages or ground indices. -/
theorem indexedImage_cover (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul top f J X Y O checkedO p : Fin k)
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (ht : (Project.FirstOrderSemantics.reduct M).mem (env top) (env (rho 6)))
    (hTop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
      MapRel (orderFormula (rho 0) mul) env q (env top))
    (hCheckedO : Checked (env top) (env O) (env checkedO))
    (hp : (Project.FirstOrderSemantics.reduct M).mem (env p) (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y))
      (env (rho 6)) (env p) (Source.SetLanguage.surjection 0 1 2))
    (hJ : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env J) (env X) (env checkedO))
      (env (rho 6)) (env p) (Source.SetLanguage.mapsTo 0 1 2)) :
    ForcingLeastRelation.Cover (orderFormula (rho 0) mul)
      (indexedImage rho G F mul top f J X Y checkedO) (domain rho G F) env
      (env (rho 6)) (env O) (env Y) (env p) := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  intro y hy q hq hqp hyY r hr hrq
  obtain ⟨s,hs,hsr,x,hx,hxX,hxy⟩ := ForcingImageQuotient.surjection_onto_reuse hM hpre hp hf hy hq hqp hyY hr hrq
  have hsq := hpre.2 s r q hs hr hq hsr hrq
  have hsp := hpre.2 s q (env p) hs hq hp hsq hqp
  obtain ⟨t,htW,hts,j,hj,hjCO,hxj⟩ := ForcingImageQuotient.mapsTo_total_reuse hM hpre hp hJ hx hs hsp hxX hs (hpre.1 s hs)
  obtain ⟨a,ha,hat,i,hi,ci,hci,hEq⟩ := (ForcingInfinity.mem_check hM hCheckedO ht hTop htW).mp hjCO t htW (hpre.1 t htW)
  refine ⟨a,ha,hpre.2 a s r ha hs hr (hpre.2 a t s ha htW hs hat hts) hsr,i,hi,?_⟩
  apply (indexedImage_semantics hM env rho G F mul top f J X Y checkedO hpre a y i).mpr
  refine ⟨ci,hci,?_⟩
  intro b hb hba
  have hbs := hpre.2 b t s hb htW hs (hpre.2 b a t hb ha htW hba hat) hts
  have hbq := hpre.2 b s q hb hs hq hbs hsq
  refine ⟨b,hb,hpre.1 b hb,x,hx,ForcingAtomicBasic.mem_mono hM hpre hb hbs hxX,
    ForcingInfinity.check_mem_of_mem hM hpre hCheckedO hci hi ht hTop hb,
    ForcingAtomicBasic.mem_mono hM hpre hb hbq hyY,?_,ForcingFormula.mono hM hpre _ _ hs hb hbs hxy⟩
  exact app_congr hM hpre hb (ForcingAtomicBasic.eq_refl hM hpre (env J) b hb)
    (ForcingAtomicBasic.eq_refl hM hpre x b hb) (ForcingAtomicBasic.eq_mono hM hpre hb hba hEq)
      (ForcingFormula.mono hM hpre _ _ htW hb (hpre.2 b a t hb ha htW hba hat) hxj)


/-- The four original source name parameters. The checked ordinal is fixed
by EVERY actual permutation and is not an additional support hypothesis. -/
def parameters {k : Nat} (f J X Y : Fin k) : Fin 4 → Fin k :=
  Fin.cases f (args3 J X Y)

/-- Actual source indexedImage produces an injection. Neither Cover nor
OneAt is an input: both are discharged above from the full source formulas. -/
theorem construct (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F S mul top f J X Y O checkedO p : Fin k)
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hS : ForcingConjugationGraph.Subgroup (env I) (env G) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hO : Ordinal (env O)) (hCheckedO : Checked (env top) (env O) (env checkedO))
    (hY : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
    (hParams : ∀ j, Supported (fun j => env (rho j)) (env S) (env (parameters f J X Y j)))
    (hp : (Project.FirstOrderSemantics.reduct M).mem (env p) (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y))
      (env (rho 6)) (env p) (Source.SetLanguage.surjection 0 1 2))
    (hJ : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env J) (env X) (env checkedO))
      (env (rho 6)) (env p) (Source.SetLanguage.injection 0 1 2)) :
    ForcingLeastRelation.Built env rho G F S mul top O Y checkedO p
      (ForcingMapCalculus.five f J X Y checkedO) imageFormula := by
  let v7 : Fin 7 → M.Carrier .set := fun j => env (rho j)
  have htW := (hPres.2.2.2.2.2 (env top)).mpr (Or.inl ht)
  have hTop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
      MapRel (orderFormula (rho 0) mul) env q (env top) :=
    fun q _ => (orderFormula_semantics env (rho 0) mul q (env top)).mpr (Or.inl ht)
  have hCheck : ∀ i ci, Checked (env top) i ci → Predicate (domain rho G F) env ci := by
    intro i ci hc
    apply (domain_semantics env rho G F ci).mpr
    apply ForcingHSCheck.check_hs hM actionFormula v7 (env G) (env (rho 6)) (env F) (env top) hF.1 htW ?_ i ci hc
    intro pi hpi
    obtain ⟨act,ha⟩ := ForcingProductFamily.exists_action hM hPres ((hG pi).mp hpi)
    exact ⟨act,(mapRel_action v7 pi act).mpr ha,(ForcingProductFamily.action_permutation ha).1,
      Or.inl ⟨htW,ForcingProductFamily.top_fixed hPres ht ha⟩⟩
  have hFixCO : Supported v7 (env S) (env checkedO) := by
    intro pi _hpi act hAct
    exact ForcingLabelNames.checked_fixed hM v7 hPres ht ((mapRel_action v7 pi act).mp hAct) hCheckedO
  have hParams5 : ∀ j, Supported v7 (env S) (env (ForcingMapCalculus.five f J X Y checkedO j)) := by
    intro j
    exact Fin.cases (hParams 0) (Fin.cases (hParams 1) (Fin.cases (hParams 2)
      (Fin.cases (hParams 3) (Fin.cases hFixCO (fun i => Fin.elim0 i))))) j
  exact ForcingLeastRelation.construct hM env rho I K B w G F S mul top O Y checkedO p
    (ForcingMapCalculus.five f J X Y checkedO) imageFormula hPres hG hF hS hSF ht hpre hO hCheckedO hY
    (hParams 3) hParams5
    (indexedImage_cover hM env rho G F mul top f J X Y O checkedO p hpre htW hTop hCheckedO hp hf
      (injection_mapsTo hM hpre hp hJ))
    (indexedImage_one hM env rho G F mul top f J X Y O checkedO p hpre hCheck hp
      (ForcingImageQuotient.surjection_mapsTo_reuse hM hpre hp hf) hJ) hp

def sentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F S mul top f J X Y O checkedO p : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
      ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
      ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
      ProjectSyntax.encode id (ForcingConjugationGraph.subgroup I G S),
      .mem (.bound S) (.bound F),
      ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
      ProjectSyntax.encode id (ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)),
      ProjectSyntax.encode id (OrdinalSyntax.ordinal O),
      ProjectSyntax.encode id (ForcingCheckName.checkName top O checkedO),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F Y),
      ProjectSyntax.encode id (ForcingLeastRelation.fixedParams rho S (parameters f J X Y)),
      .mem (.bound p) (.bound (rho 6)),
      ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id
        (args3 f X Y) (rho 6) p (Source.SetLanguage.surjection 0 1 2)),
      ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id
        (args3 J X checkedO) (rho 6) p (Source.SetLanguage.injection 0 1 2))].foldr Definitional.Formula.imp
        (ProjectSyntax.encode id (ForcingLeastRelation.construction rho G F S mul top O Y checkedO p
          (ForcingMapCalculus.five f J X Y checkedO) imageFormula)))
  freeClosed := by
    simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F S mul top f J X Y O checkedO p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sentence rho I K B w G F S mul top f J X Y O checkedO p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingNormalFilter.normal_semantics,ForcingConjugationGraph.subgroup_semantics,
    ForcingWithTopCarrier.empty_semantics,ForcingAtomicBasic.preorder_semantics,ForcingRawRank.ordinal_semantics,
    ForcingCheckName.checkName_semantics,ForcingHS.hs_semantics,
    ForcingLeastRelation.fixedParams_semantics,ForcingFormula.formula_semantics,ForcingLeastRelation.construction_semantics,id_eq]
  exact construct hM env rho I K B w G F S mul top f J X Y O checkedO p

theorem kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F S mul top f J X Y O checkedO p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sentence rho I K B w G F S mul top f J X Y O checkedO p)) :=
  ModelTransfer.derives (fun _ hM => models rho I K B w G F S mul top f J X Y O checkedO p hM)



/-- Pinned wellorderable_image: actual dense ordinal presentation, the source
tuple stabilizer and the constructed least-index graph discharge all witnesses. -/
theorem wellorderable_image (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul top f X Y p : Fin k)
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (ht : ForcingWithTopCarrier.Empty (env top))
    (hpre : ForcingAtomicBasic.PreorderOn (orderFormula (rho 0) mul) env (env (rho 6)))
    (hfHS : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env f))
    (hXHS : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hYHS : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env Y))
    (hp : (Project.FirstOrderSemantics.reduct M).mem (env p) (env (rho 6)))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 (env f) (env X) (env Y))
      (env (rho 6)) (env p) (Source.SetLanguage.surjection 0 1 2))
    (hWo : Force (orderFormula (rho 0) mul) (domain rho G F) env (Source.SetLanguage.args1 (env X))
      (env (rho 6)) (env p) (ForcingCheckOrdinal.wellorderable 0)) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env (Source.SetLanguage.args1 (env Y))
      (env (rho 6)) (env p) (ForcingCheckOrdinal.wellorderable 0) := by
  let R := orderFormula (rho 0) mul
  let H := domain rho G F
  let W := env (rho 6)
  let v7 : Fin 7 → M.Carrier .set := fun j => env (rho j)
  have htW := (hPres.2.2.2.2.2 (env top)).mpr (Or.inl ht)
  have hTop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q W → MapRel R env q (env top) :=
    fun q _ => (orderFormula_semantics env (rho 0) mul q (env top)).mpr (Or.inl ht)
  have hCheck : ∀ i ci, Checked (env top) i ci → Predicate H env ci := by
    intro i ci hc
    apply (domain_semantics env rho G F ci).mpr
    apply ForcingHSCheck.check_hs hM actionFormula v7 (env G) W (env F) (env top) hF.1 htW ?_ i ci hc
    intro pi hpi
    obtain ⟨act,ha⟩ := ForcingProductFamily.exists_action hM hPres ((hG pi).mp hpi)
    exact ⟨act,(mapRel_action v7 pi act).mpr ha,(ForcingProductFamily.action_permutation ha).1,
      Or.inl ⟨htW,ForcingProductFamily.top_fixed hPres ht ha⟩⟩
  apply ForcingFormula.of_dense hM hpre (ForcingCheckOrdinal.wellorderable 0) (Source.SetLanguage.args1 (env Y)) hp
  intro q hq hqp
  obtain ⟨r,hr,hrq,beta,hBeta,checked,hChecked,J,hJHS,hJ⟩ :=
    ForcingOrderedSections.wellorderable_check_dense hM env rho I K B w G F mul top hPres hG hF ht hpre hp hWo q hq hqp
  have hJHS' := (domain_semantics env rho G F J).mp hJHS
  have hNames : ∀ j, HS actionFormula v7 (env G) W (env F) (args3 (env f) J (env X) j) := by
    intro j
    exact Fin.cases hfHS (Fin.cases hJHS' (Fin.cases hXHS (fun i => Fin.elim0 i))) j
  obtain ⟨S,hS,hSF,hFixed⟩ := ForcingTupleStabilizer.separation_support hM v7 hPres hG hF hYHS
    (args3 (env f) J (env X)) hNames
  have hParamsRaw : ∀ j, Supported v7 S (Fin.cases (env f) (args3 J (env X) (env Y)) j) := by
    intro j pi hpi act hAct
    have hh := hFixed pi hpi act hAct
    exact Fin.cases (hh.2 0) (Fin.cases (hh.2 1) (Fin.cases (hh.2 2) (Fin.cases hh.1 (fun i => Fin.elim0 i)))) j
  let ext : Fin (k+5) → M.Carrier .set :=
    Fin.lastCases S (Fin.lastCases r (Fin.lastCases J (Fin.lastCases checked (Fin.lastCases beta env))))
  let up : Fin k → Fin (k+5) := fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc
  let rr : Fin 7 → Fin (k+5) := fun j => up (rho j)
  let o : Fin (k+5) := (Fin.last k).castSucc.castSucc.castSucc.castSucc
  let co : Fin (k+5) := (Fin.last (k+1)).castSucc.castSucc.castSucc
  let ji : Fin (k+5) := (Fin.last (k+2)).castSucc.castSucc
  let pr : Fin (k+5) := (Fin.last (k+3)).castSucc
  let si : Fin (k+5) := Fin.last (k+4)
  let R' := orderFormula (rr 0) (up mul)
  let H' := domain rr (up G) (up F)
  have hR : ∀ a b, MapRel R env a b ↔ MapRel R' ext a b := by
    intro a b
    simp only [R,R',rr,up,orderFormula_semantics,ext,Fin.lastCases_castSucc]
  have hH : ∀ x, Predicate H env x ↔ Predicate H' ext x := by
    intro x
    simp only [H,H',rr,up,domain_semantics,ext,Fin.lastCases_castSucc]
  have hpre' : ForcingAtomicBasic.PreorderOn R' ext W := by
    constructor
    · intro a ha
      exact (hR a a).mp (hpre.1 a ha)
    · intro a b c ha hb hc hab hbc
      exact (hR a c).mp (hpre.2 a b c ha hb hc ((hR a b).mpr hab) ((hR b c).mpr hbc))
  have hrp := hpre.2 r q (env p) hr hq hp hrq hqp
  have hfr := ForcingFormula.mono hM hpre (Source.SetLanguage.surjection 0 1 2) (args3 (env f) (env X) (env Y)) hp hr hrp hf
  have hfr' := (ForcingSeparation.force_congr hR hH (Source.SetLanguage.surjection 0 1 2)
    (args3 (env f) (env X) (env Y)) W r).mp hfr
  have hJ' := (ForcingSeparation.force_congr hR hH (Source.SetLanguage.injection 0 1 2)
    (args3 J (env X) checked) W r).mp hJ
  have hParams : ∀ j, Supported (fun a => ext (rr a)) (ext si)
      (ext (parameters (up f) ji (up X) (up Y) j)) := by
    intro j
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)))) j
    · change Supported (fun a => ext (rr a)) (ext si) (ext (up f))
      simpa only [v7,Source.SetLanguage.args3,Source.SetLanguage.args2,Source.SetLanguage.args1,Fin.cases_zero,Fin.cases_succ,si,rr,up,ext,Fin.lastCases_last,Fin.lastCases_castSucc] using hParamsRaw 0
    · change Supported (fun a => ext (rr a)) (ext si) (ext (ji))
      simpa only [v7,Source.SetLanguage.args3,Source.SetLanguage.args2,Source.SetLanguage.args1,Fin.cases_zero,Fin.cases_succ,ji,si,rr,up,ext,Fin.lastCases_last,Fin.lastCases_castSucc] using hParamsRaw (Fin.succ 0)
    · change Supported (fun a => ext (rr a)) (ext si) (ext (up X))
      simpa only [v7,Source.SetLanguage.args3,Source.SetLanguage.args2,Source.SetLanguage.args1,Fin.cases_zero,Fin.cases_succ,si,rr,up,ext,Fin.lastCases_last,Fin.lastCases_castSucc] using hParamsRaw (Fin.succ (Fin.succ 0))
    · change Supported (fun a => ext (rr a)) (ext si) (ext (up Y))
      simpa only [v7,Source.SetLanguage.args3,Source.SetLanguage.args2,Source.SetLanguage.args1,Fin.cases_zero,Fin.cases_succ,si,rr,up,ext,Fin.lastCases_last,Fin.lastCases_castSucc] using hParamsRaw (Fin.succ (Fin.succ (Fin.succ 0)))
  obtain ⟨graph,_hGraph,hGraphHS,_hFixedGraph,hGraphInj⟩ := construct hM ext rr
    (up I) (up K) (up B) (up w) (up G) (up F) si (up mul) (up top) (up f) ji (up X) (up Y) o co pr
    (by simpa only [rr,up,ext,Fin.lastCases_castSucc] using hPres)
    (by simpa only [up,ext,Fin.lastCases_castSucc] using hG)
    (by simpa only [up,ext,Fin.lastCases_castSucc] using hF)
    (by simpa only [si,up,ext,Fin.lastCases_last,Fin.lastCases_castSucc] using hS)
    (by simpa only [si,up,ext,Fin.lastCases_last,Fin.lastCases_castSucc] using hSF)
    (by simpa only [up,ext,Fin.lastCases_castSucc] using ht)
    (by simpa only [rr,up,ext,Fin.lastCases_castSucc] using hpre')
    (by simpa only [o,ext,Fin.lastCases_last,Fin.lastCases_castSucc] using hBeta)
    (by simpa only [o,co,up,ext,Fin.lastCases_last,Fin.lastCases_castSucc] using hChecked)
    (by simpa only [rr,up,ext,Fin.lastCases_castSucc] using hYHS)
    hParams
    (by simpa only [pr,rr,up,ext,Fin.lastCases_last,Fin.lastCases_castSucc] using hr)
    (by simpa only [rr,up,ext,pr,Fin.lastCases_last,Fin.lastCases_castSucc] using hfr')
    (by simpa only [ji,co,rr,up,ext,pr,Fin.lastCases_last,Fin.lastCases_castSucc] using hJ')
  have hInj : Force R H env (args3 graph (env Y) checked) W r (Source.SetLanguage.injection 0 1 2) := by
    apply (ForcingSeparation.force_congr hR hH (Source.SetLanguage.injection 0 1 2) (args3 graph (env Y) checked) W r).mpr
    simpa only [rr,up,ext,co,pr,Fin.lastCases_last,Fin.lastCases_castSucc] using hGraphInj
  have hGraphDom : Predicate H env graph := by
    apply (domain_semantics env rho G F graph).mpr
    simpa only [rr,up,ext,Fin.lastCases_castSucc] using hGraphHS
  refine ⟨r,hr,hrq,ForcingCheckOrdinal.wellorderable_of_check_injection hM hpre htW hTop ?_ hr hBeta hChecked
    (hCheck beta checked hChecked) hGraphDom hInj⟩
  intro nu hnu chi c hedge
  exact (domain_semantics env rho G F chi).mpr (ForcingHS.child ((domain_semantics env rho G F nu).mp hnu) hedge)


/-- Full source image-of-wellorderable theorem, with all actual ordinal,
check-name, injection and common-support witnesses eliminated. -/
def imageSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top f X Y p : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    ([ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)),
      ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G),
      ProjectSyntax.encode id (ForcingNormalFilter.normal I G F),
      ProjectSyntax.encode id (ForcingWithTopCarrier.empty top),
      ProjectSyntax.encode id (ForcingAtomicBasic.preorder (orderFormula (rho 0) mul) id (rho 6)),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F f),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F X),
      ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F Y),
      .mem (.bound p) (.bound (rho 6)),
      ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id
        (args3 f X Y) (rho 6) p (Source.SetLanguage.surjection 0 1 2)),
      ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id
        (Source.SetLanguage.args1 X) (rho 6) p (ForcingCheckOrdinal.wellorderable 0))].foldr Definitional.Formula.imp
      (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id
        (Source.SetLanguage.args1 Y) (rho 6) p (ForcingCheckOrdinal.wellorderable 0))))
  freeClosed := by
    simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem image_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top f X Y p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (imageSentence rho I K B w G F mul top f X Y p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingProductFamily.presentation_semantics,
    ForcingLabelPermutations.carrier_semantics,ForcingNormalFilter.normal_semantics,ForcingWithTopCarrier.empty_semantics,
    ForcingAtomicBasic.preorder_semantics,ForcingHS.hs_semantics,ForcingFormula.formula_semantics,id_eq]
  intro hPres hG hF ht hpre hfHS hXHS hYHS hp hf hWo
  have hV (Z : Fin k) : (fun j => env (Source.SetLanguage.args1 Z j)) = Source.SetLanguage.args1 (env Z) := by
    funext j
    exact Fin.cases rfl (fun i => Fin.elim0 i) j
  rw [hV] at hWo
  rw [hV]
  exact wellorderable_image hM env rho I K B w G F mul top f X Y p hPres hG hF ht hpre hfHS hXHS hYHS hp hf hWo

theorem image_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top f X Y p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (imageSentence rho I K B w G F mul top f X Y p)) :=
  ModelTransfer.derives (fun _ hM => image_models rho I K B w G F mul top f X Y p hM)

end PPAC.Migration.ForcingIndexedImage
