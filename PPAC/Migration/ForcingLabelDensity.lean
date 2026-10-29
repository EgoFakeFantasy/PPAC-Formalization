/- Pinned ProductNames.mem_labelSet and ChoiceFailure.exists_condition_below.
Consumer: AvailableRecords.classRepresentationSet_denseBelow, through its
actual label-class witness at a genuine Cohen/diagram condition. Reuse the
original name recursion, label edges, class congruence and WithTop coding. -/
import PPAC.Migration.ForcingRelationClass
import PPAC.Migration.ForcingCohenCodes

namespace PPAC.Migration.ForcingLabelDensity
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingMapConditions (MapRel)
open ForcingProductFamily (Presentation actionFormula)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingAtomicRelations (Forces)
open ForcingSupportingRoot (Code code_mem)
open ForcingSupportSize (Injection)
open ReplacementPredicates (paramsUp)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem mem_labelSet (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (R : Formula (k+2)) (env : Fin k → M.Carrier .set)
    {W I K c t b labels nu p : M.Carrier .set}
    (hA : ForcingLabelSet.LabelSet W I K c t b labels)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p W)
    (ht : (Project.FirstOrderSemantics.reduct M).mem t W)
    (hTop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q W → MapRel R env q t) :
    Forces false R env W nu labels p ↔
      ∀ q, (Project.FirstOrderSemantics.reduct M).mem q W → MapRel R env q p →
        ∃ r j name, (Project.FirstOrderSemantics.reduct M).mem r W ∧ MapRel R env r q ∧
          (Project.FirstOrderSemantics.reduct M).mem j I ∧ ForcingLabelNames.Label W K c t j b name ∧
            Forces true R env W nu name r := by
  constructor
  · intro hm q hq hqp
    obtain ⟨r,name,d,hr,hrq,_,he,_,heq⟩ :=
      ((ForcingAtomicRelations.mem_iff hM R env W nu labels p).mp hm).2 q hq hqp
    obtain ⟨_,j,hj,hn⟩ := (ForcingLabelSet.edge_labelSet hM hA name d).mp he
    exact ⟨r,j,name,hr,hrq,hj,hn,heq⟩
  · intro hd
    apply (ForcingAtomicRelations.mem_iff hM R env W nu labels p).mpr
    refine ⟨hp,?_⟩
    intro q hq hqp
    obtain ⟨r,j,name,hr,hrq,hj,hn,heq⟩ := hd q hq hqp
    exact ⟨r,name,t,hr,hrq,ht,(ForcingLabelSet.edge_labelSet hM hA name t).mpr ⟨rfl,j,hj,hn⟩,
      hTop r hr,heq⟩

/-- Eliminate the added top using an existing internal diagram, without
extracting a new object choice function. -/
theorem exists_condition_below (hM : FirstOrder.Theory.Models M nativeZF)
    {D I K B w C S X Y P W mul e root p : M.Carrier .set}
    (hpres : Presentation D I K B w C S X Y P W)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hroot : Injection D I root)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p W) :
    ∃ d s z, ForcingCohenConditions.Condition S w d ∧ Injection D I s ∧ Code z d s ∧
      ForcingWithTopAction.Le D mul z p := by
  rcases (hpres.2.2.2.2.2 p).mp hp with he | ⟨a,ha,hpa⟩
  · obtain ⟨d,hd⟩ := ForcingWithTopCarrier.exists_empty hM
    obtain ⟨z,hz⟩ := ForcingSupportingRoot.exists_code hM d root
    exact ⟨d,root,z,ForcingCohenCodes.empty_condition hM hd,hroot,hz,Or.inl he⟩
  · obtain ⟨d,hd,s,hs,hds⟩ := (hpres.2.2.2.2.1 a).mp ha
    have hcode : Code p d s := ⟨a,hds,hpa⟩
    have hinj := (hpres.2.2.2.1 s).mp hs
    exact ⟨d,s,p,(hpres.2.2.1 d).mp hd,hinj,hcode,
      (ForcingSupportingRoot.code_le hcode hcode).mpr ⟨fun _ hx => hx,ForcingDiagramPoset.le_refl hm hinj⟩⟩

/-- The first part of source classRepresentationSet_denseBelow: below every
condition there is a genuine pair forcing equality to an actual label class.
The later diagram extension must additionally put the label and support in
its range; this theorem does not assume or claim that coverage. -/
theorem class_label_dense (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w mu e root c t b labels E tau p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hpres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hroot : Injection (env (rho 0)) I root)
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hc : ForcingConditionGraphs.FunctionOn K c) (ht : ForcingWithTopCarrier.Empty t)
    (hA : ForcingLabelSet.LabelSet (env (rho 6)) I K c t b labels)
    (hE : ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) E)
    (hTau : ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) tau)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)))
    (hf : ForcingFormula.Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
      (Source.SetLanguage.args3 tau labels E) (env (rho 6)) p (ForcingEligibility.isClass 0 1 2)) :
    ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
      MapRel (orderFormula (rho 0) mul) env q p →
      ∃ z d s j x name, (Project.FirstOrderSemantics.reduct M).mem z (env (rho 6)) ∧
        MapRel (orderFormula (rho 0) mul) env z q ∧ ForcingCohenConditions.Condition (env (rho 2)) w d ∧
        Injection (env (rho 0)) I s ∧ Code z d s ∧ (Project.FirstOrderSemantics.reduct M).mem j I ∧
        ForcingLabelNames.Label (env (rho 6)) K c t j b x ∧
        ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
        ForcingRelationClass.Class (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
          (env (rho 6)) labels E x name ∧ Forces true (orderFormula (rho 0) mul) env (env (rho 6)) tau name z := by
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hpres.2.2.2.2.1 hpres.2.2.2.1 hpres.2.2.2.2.2
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hSmall := (ForcingSupportSize.native_small hM w mu).mpr hMu.2
  have hAHS := (ForcingLabelSet.HS_and_fixed hM (fun j => env (rho j))
    hpres hG hNormal hF hw hSmall hc ht hA).1
  have htW := (hpres.2.2.2.2.2 t).mpr (Or.inl ht)
  have hTop : ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
      MapRel (orderFormula (rho 0) mul) env q t :=
    fun q _ => (orderFormula_semantics env (rho 0) mul q t).mpr (Or.inl ht)
  intro q hq hqp
  obtain ⟨r,hr,hrq,y,old,_,hold,hClass,hy,heq⟩ :=
    (ForcingRelationClass.forces_isClass hM env rho G F mul hpres hG hNormal hpre hp
      (Source.SetLanguage.args3 tau labels E) 0 1 2 hTau hAHS hE).mp hf q hq hqp
  obtain ⟨v,j,x,hv,hvr,hj,hx,hyx⟩ :=
    (mem_labelSet hM (orderFormula (rho 0) mul) env hA hr htW hTop).mp hy r hr (hpre.1 r hr)
  obtain ⟨d,s,z,hd,hs,hz,hzv⟩ := exists_condition_below hM hpres hm hroot hv
  have hzW := code_mem hpres hd hs hz
  have hzv' := (orderFormula_semantics env (rho 0) mul z v).mpr hzv
  have hzr := hpre.2 z v r hzW hv hr hzv' hvr
  have hxHS := ForcingLabelNames.label_HS hM (fun j => env (rho j)) hpres hG hNormal hF hw hSmall hc ht hj hx
  obtain ⟨name,hn,hnClass⟩ := ForcingRelationClass.exists_class hM env rho G F mul hpres hG hNormal hAHS hE hxHS
  have hClassEq := ForcingRelationClass.congr hM hpre hold hn hClass hnClass hzW
    (ForcingAtomicBasic.eq_refl hM hpre labels z hzW) (ForcingAtomicBasic.eq_refl hM hpre E z hzW)
    (ForcingAtomicBasic.eq_mono hM hpre hzW hzv' hyx)
  exact ⟨z,d,s,j,x,name,hzW,hpre.2 z r q hzW hr hq hzr hrq,hd,hs,hz,hj,hx,hn,hnClass,
    ForcingAtomicLaws.eq_trans hM hpre (ForcingAtomicBasic.eq_mono hM hpre hzW hzr heq) hClassEq⟩

/-- Internal quantifiers over the actual Cohen/diagram and label-class witnesses. -/
def result {k : Nat} (rho : Fin 7 → Fin k) (I K w G F mul c t b labels E tau p : Fin k) : Formula k :=
  let R := orderFormula (rho 0) mul
  let H := ForcingPairUnion.domain rho G F
  let up := fun i : Fin k => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let q := (Fin.last k).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let z := (Fin.last (k+1)).castSucc.castSucc.castSucc.castSucc.castSucc
  let d := (Fin.last (k+2)).castSucc.castSucc.castSucc.castSucc
  let s := (Fin.last (k+3)).castSucc.castSucc.castSucc
  let j := (Fin.last (k+4)).castSucc.castSucc
  let x := (Fin.last (k+5)).castSucc
  let name := Fin.last (k+6)
  let body := (Formula.mem z (up (rho 6))).conj
    ((ReplacementPredicates.rel R up z q).conj
    ((ForcingCohenConditions.condition (up (rho 2)) (up w) d).conj
    ((Source.SetLanguage.injection s (up (rho 0)) (up I)).conj
    ((ForcingSupportingRoot.code z d s).conj
    ((Formula.mem j (up I)).conj
    ((ForcingLabelNames.label (up (rho 6)) (up K) (up c) (up t) j (up b) x).conj
    ((ForcingHS.hs actionFormula (fun j => up (rho j)) (up G) (up (rho 6)) (up F) name).conj
    ((ForcingRelationClass.relationClass R H up (up (rho 6)) (up labels) (up E) x name).conj
    (ForcingAtomicRelations.forces true R up (up (rho 6)) (up tau) name z)))))))))
  .all ((Formula.mem (Fin.last k) (rho 6).castSucc).imp
    ((ReplacementPredicates.rel R Fin.castSucc (Fin.last k) p.castSucc).imp
      (.ex (.ex (.ex (.ex (.ex (.ex body))))))))

theorem result_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K w G F mul c t b labels E tau p : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env
      (result rho I K w G F mul c t b labels E tau p) ↔
    ∀ q, (Project.FirstOrderSemantics.reduct M).mem q (env (rho 6)) →
      MapRel (orderFormula (rho 0) mul) env q (env p) →
      ∃ z d s j x name, (Project.FirstOrderSemantics.reduct M).mem z (env (rho 6)) ∧
        MapRel (orderFormula (rho 0) mul) env z q ∧ ForcingCohenConditions.Condition (env (rho 2)) (env w) d ∧
        Injection (env (rho 0)) (env I) s ∧ Code z d s ∧ (Project.FirstOrderSemantics.reduct M).mem j (env I) ∧
        ForcingLabelNames.Label (env (rho 6)) (env K) (env c) (env t) j (env b) x ∧
        ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
        ForcingRelationClass.Class (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
          (env (rho 6)) (env labels) (env E) x name ∧
        Forces true (orderFormula (rho 0) mul) env (env (rho 6)) (env tau) name z := by
  simp only [result,Formula.Realize,ForcingMapConditions.rel_semantics (M := M),
    ForcingCohenConditions.condition_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportingRoot.code_semantics (M := M),ForcingLabelNames.label_semantics (M := M),
    ForcingHS.hs_semantics (M := M),ForcingRelationClass.relationClass_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def densitySentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu e root G F mul c t b labels E tau p : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection root (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn c K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty t))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K c t b labels))
    (.imp (ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F E))
    (.imp (ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F tau))
    (.imp (.mem (.bound p) (.bound (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F)
      id (Source.SetLanguage.args3 tau labels E) (rho 6) p (ForcingEligibility.isClass 0 1 2)))
    (ProjectSyntax.encode id (result rho I K w G F mul c t b labels E tau p))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,ProjectSyntax.freeClosed]

theorem density_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu e root G F mul c t b labels E tau p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (densitySentence rho I K B w mu e root G F mul c t b labels E tau p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (densitySentence rho I K B w mu e root G F mul c t b labels E tau p)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingProductFamily.presentation_semantics (M := M),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingHS.hs_semantics (M := M),Project.Formula.satisfies_mem_iff,
    ForcingFormula.formula_semantics (M := M),result_semantics (M := M)]
  intro hw hMu hpres hm hroot hG hF hc ht hA hE hTau hp hf
  have hv : (fun i => env (Source.SetLanguage.args3 tau labels E i)) =
      Source.SetLanguage.args3 (env tau) (env labels) (env E) := by
    funext i
    refine Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun j => Fin.elim0 j) i) i) i
  simp only [id_eq] at hf
  rw [hv] at hf
  exact class_label_dense hM env rho G F mul hw hMu hpres hm hroot hG hF hc ht hA hE hTau hp hf

theorem density_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu e root G F mul c t b labels E tau p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence
      (densitySentence rho I K B w mu e root G F mul c t b labels E tau p)) :=
  ModelTransfer.derives (fun _ hM => density_models rho I K B w mu e root G F mul c t b labels E tau p hM)

end PPAC.Migration.ForcingLabelDensity
