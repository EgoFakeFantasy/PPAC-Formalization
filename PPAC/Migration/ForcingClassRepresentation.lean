/- Pinned AvailableRecords.classRepresentationSet_denseBelow:125-156.
All stronger Cohen conditions, actual diagram order, support coverage and the
specified label in the SAME diagram are retained. Consume the preceding
label-class density and the source extend_through; no generic filter oracle. -/
import PPAC.Migration.ForcingLabelDensity
import PPAC.Migration.ConstructionDiagramCoverage

namespace PPAC.Migration.ForcingClassRepresentation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingMapConditions (MapRel)
open ForcingProductFamily (Presentation actionFormula)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingAtomicRelations (Forces)
open ForcingSupportingRoot (Code code_mem)
open ForcingSupportSize (Injection Small)
open ForcingPowerName (Subset)
open ForcingPairUnion (domain)
open ConstructionDiagramCoverage (Covers)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem denseBelow (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w mu e mark root c t b labels E tau d0 z0 : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hLarge : ¬ Small I mu)
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) mark mu)
    (hmark : (Project.FirstOrderSemantics.reduct M).mem mark (env (rho 0)))
    (hpres : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) e)
    (hroot : Injection (env (rho 0)) I root)
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hc : ForcingConditionGraphs.FunctionOn K c) (ht : ForcingWithTopCarrier.Empty t)
    (hA : ForcingLabelSet.LabelSet (env (rho 6)) I K c t b labels)
    (hE : ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) E)
    (hTau : ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) tau)
    (hd0 : ForcingCohenConditions.Condition (env (rho 2)) w d0) (hz0 : Code z0 d0 root)
    (hf : ForcingFormula.Force (orderFormula (rho 0) mul) (domain rho G F) env
      (Source.SetLanguage.args3 tau labels E) (env (rho 6)) z0 (ForcingEligibility.isClass 0 1 2)) :
    ∀ d, ForcingCohenConditions.Condition (env (rho 2)) w d → Subset d0 d →
      ∃ a r H j x name z, ForcingCohenConditions.Condition (env (rho 2)) w a ∧ Subset d a ∧
        Injection (env (rho 0)) I r ∧ ForcingDiagramOrder.Le (env (rho 0)) (env mul) r root ∧
        ConstructionCohenCompatibility.Support a H ∧ Covers (env (rho 0)) H r ∧
        (Project.FirstOrderSemantics.reduct M).mem j I ∧ ConstructionPlacementTriple.ImageAt r (env (rho 0)) j ∧
        ForcingLabelNames.Label (env (rho 6)) K c t j b x ∧
        ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) name ∧
        ForcingRelationClass.Class (orderFormula (rho 0) mul) (domain rho G F) env (env (rho 6)) labels E x name ∧
        Code z a r ∧ Forces true (orderFormula (rho 0) mul) env (env (rho 6)) tau name z := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hpres.2.2.2.2.1 hpres.2.2.2.1 hpres.2.2.2.2.2
  have hz0W := code_mem hpres hd0 hroot hz0
  intro d hd hdd
  obtain ⟨zd,hzd⟩ := ForcingSupportingRoot.exists_code hM d root
  have hzdW := code_mem hpres hd hroot hzd
  have hzd0 := (orderFormula_semantics env (rho 0) mul zd z0).mpr
    ((ForcingSupportingRoot.code_le hzd hz0).mpr ⟨hdd,ForcingDiagramPoset.le_refl hm hroot⟩)
  obtain ⟨z,a,s,j,x,name,hzW,hzzd,ha,hs,hzas,hj,hx,hn,hClass,heq⟩ :=
    ForcingLabelDensity.class_label_dense hM env rho G F mul hw hMu hpres hm hroot hG hF hc ht hA hE hTau hz0W hf
      zd hzdW hzd0
  obtain ⟨hda,hsroot⟩ := (ForcingSupportingRoot.code_le hzas hzd).mp
    ((orderFormula_semantics env (rho 0) mul z zd).mp hzzd)
  obtain ⟨H,hH,hHI,hHw⟩ := ConstructionCohenCompatibility.exists_support hM hw hpres.1 hpres.2.1 ha
  obtain ⟨hToW,hhToW⟩ := (ForcingSupportSize.native_small hM H w).mp hHw
  obtain ⟨wToMu,hwToMu⟩ := hMu.2
  have hHmu : Small H mu := (ForcingSupportSize.native_small hM H mu).mpr
    (ZF.exists_compositionInjection hZF pair hhToW hwToMu)
  have hwmu : Small w mu := (ForcingSupportSize.native_small hM w mu).mpr hMu.2
  obtain ⟨single,hSingle⟩ := ForcingWithTopCarrier.exists_single hM j
  obtain ⟨J,hJ⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) H single
  have hJI : Subset J I := by
    intro y hy
    rcases (hJ y).mp hy with hy | hy
    · exact hHI y hy
    · exact ((hSingle y).mp hy).symm ▸ hj
  have hJmu := ForcingSupportIntersection.small_union hM hw hMu hHmu
    (ForcingLabelNames.singleton_small hM hw hwmu hSingle) hJ
  obtain ⟨r,hr,hSub,hCover⟩ := ConstructionDiagramCoverage.extend_through hM hChoice hw hMu hLarge hCard
    (hm.2.1 mark hmark) hs hJI hJmu
  have hrs : ForcingDiagramOrder.Le (env (rho 0)) (env mul) r s := ⟨mark,hmark,hSub⟩
  obtain ⟨zr,hzr⟩ := ForcingSupportingRoot.exists_code hM a r
  have hzrW := code_mem hpres ha hr hzr
  have hzrLe := (orderFormula_semantics env (rho 0) mul zr z).mpr
    ((ForcingSupportingRoot.code_le hzr hzas).mpr ⟨fun _ hy => hy,hrs⟩)
  exact ⟨a,r,H,j,x,name,zr,ha,hda,hr,ForcingDiagramPoset.le_trans hm hrs hsroot,hH,
    fun y hy => hCover y ((hJ y).mpr (Or.inl hy)),hj,
    hCover j ((hJ j).mpr (Or.inr ((hSingle j).mpr rfl))),hx,hn,hClass,hzr,
    ForcingAtomicBasic.eq_mono hM hpre hzrW hzrLe heq⟩

def witness {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (rr : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (w I K G F mul c t b labels E tau d root a r H j x name z : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w a))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.subset d a))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection r (rho 0) I))
    (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.le (rho 0) mul r root))
    (.conj (ConstructionCohenCompatibility.support a H)
    (.conj (ConstructionDiagramCoverage.covers (rho 0) H r)
    (.conj (.mem (.bound j) (.bound I))
    (.conj (ConstructionPlacementTriple.imageAt r (rho 0) j)
    (.conj (ProjectSyntax.encode id (ForcingLabelNames.label (rho 6) K c t j b x))
    (.conj (ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F name))
    (.conj (ProjectSyntax.encode id (ForcingRelationClass.relationClass R Hdom rr (rho 6) labels E x name))
    (.conj (ProjectSyntax.encode id (ForcingSupportingRoot.code z a r))
    (ProjectSyntax.encode id (ForcingAtomicRelations.forces true R rr (rho 6) tau name z))))))))))))))

theorem witness_freeClosed {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (rr : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (w I K G F mul c t b labels E tau d root a r H j x name z : Fin m) :
    (witness R Hdom rr rho w I K G F mul c t b labels E tau d root a r H j x name z).FreeClosed := by
  simp -implicitDefEqProofs [witness,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionCohenCompatibility.support_freeClosed,ConstructionDiagramCoverage.covers_freeClosed,
    ConstructionPlacementTriple.imageAt_freeClosed]

theorem witness_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) m)
    (R : Formula (k+2)) (Hdom : Formula (k+1)) (rr : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (w I K G F mul c t b labels E tau d root a r H j x name z : Fin m) :
    Project.Formula.satisfies env (witness R Hdom rr rho w I K G F mul c t b labels E tau d root a r H j x name z) ↔
      ForcingCohenConditions.Condition (env.bound (rho 2)) (env.bound w) (env.bound a) ∧
      Subset (env.bound d) (env.bound a) ∧ Injection (env.bound (rho 0)) (env.bound I) (env.bound r) ∧
      ForcingDiagramOrder.Le (env.bound (rho 0)) (env.bound mul) (env.bound r) (env.bound root) ∧
      ConstructionCohenCompatibility.Support (env.bound a) (env.bound H) ∧
      Covers (env.bound (rho 0)) (env.bound H) (env.bound r) ∧
      (Project.FirstOrderSemantics.reduct M).mem (env.bound j) (env.bound I) ∧
      ConstructionPlacementTriple.ImageAt (env.bound r) (env.bound (rho 0)) (env.bound j) ∧
      ForcingLabelNames.Label (env.bound (rho 6)) (env.bound K) (env.bound c) (env.bound t)
        (env.bound j) (env.bound b) (env.bound x) ∧
      ForcingHS.HS actionFormula (fun i => env.bound (rho i)) (env.bound G) (env.bound (rho 6)) (env.bound F) (env.bound name) ∧
      ForcingRelationClass.Class R Hdom (fun i => env.bound (rr i)) (env.bound (rho 6))
        (env.bound labels) (env.bound E) (env.bound x) (env.bound name) ∧
      Code (env.bound z) (env.bound a) (env.bound r) ∧
      Forces true R (fun i => env.bound (rr i)) (env.bound (rho 6)) (env.bound tau) (env.bound name) (env.bound z) := by
  simp only [witness,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenConditions.condition_semantics (M := M),ForcingLabelPermutations.subset_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.le_semantics (M := M),
    ConstructionCohenCompatibility.support_semantics hM,ConstructionDiagramCoverage.covers_semantics hM,
    Project.Formula.satisfies_mem_iff,ConstructionPlacementTriple.imageAt_semantics hM,
    ForcingLabelNames.label_semantics (M := M),ForcingHS.hs_semantics (M := M),
    ForcingRelationClass.relationClass_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M),
    ForcingAtomicRelations.forces_semantics (M := M)]
  rfl

def densityResult {k : Nat} (rho : Fin 7 → Fin k)
    (w I K G F mul c t b labels E tau d0 root : Fin k) : Project.Formula 1 k :=
  let up := fun i : Fin k => i.succ.succ.succ.succ.succ.succ.succ.succ
  .forallE (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2).succ w.succ 0))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.subset d0.succ 0))
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
      (witness (orderFormula (rho 0) mul) (domain rho G F) up (fun j => up (rho j))
        (up w) (up I) (up K) (up G) (up F) (up mul) (up c) (up t) (up b)
        (up labels) (up E) (up tau) 7 (up root) 6 5 4 3 2 1 0))))))))))

theorem densityResult_freeClosed {k : Nat} (rho : Fin 7 → Fin k)
    (w I K G F mul c t b labels E tau d0 root : Fin k) :
    (densityResult rho w I K G F mul c t b labels E tau d0 root).FreeClosed := by
  simp -implicitDefEqProofs [densityResult,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,witness_freeClosed]

def densitySentence {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu e mark root G F mul c t b labels E tau d0 z0 : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (.neg (ProjectSyntax.encode id (ForcingSupportSize.small I mu)))
    (.imp (ConstructionSaturationCardinals.cardinalsF (rho 0) mul mark mu)
    (.imp (.mem (.bound mark) (.bound (rho 0)))
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
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d0))
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z0 d0 root))
    (.imp (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id
      (Source.SetLanguage.args3 tau labels E) (rho 6) z0 (ForcingEligibility.isClass 0 1 2)))
    (densityResult rho w I K G F mul c t b labels E tau d0 root)))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,ProjectSyntax.freeClosed,
      ConstructionSaturationCardinals.cardinalsF_freeClosed,densityResult_freeClosed]

theorem density_models {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu e mark root G F mul c t b labels E tau d0 z0 : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (densitySentence rho I K B w mu e mark root G F mul c t b labels E tau d0 z0)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (densitySentence rho I K B w mu e mark root G F mul c t b labels E tau d0 z0)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_neg_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationCardinals.cardinalsF_semantics hM,
    Project.Formula.satisfies_mem_iff,ForcingProductFamily.presentation_semantics (M := M),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportFilter.filter_semantics (M := M),
    ForcingConditionGraphs.functionOn_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingLabelSet.labelSet_semantics (M := M),ForcingHS.hs_semantics (M := M),
    ForcingCohenConditions.condition_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M),
    ForcingFormula.formula_semantics (M := M)]
  intro hw hMu hLarge hCard hmark hpres hm hroot hG hF hc ht hA hE hTau hd0 hz0 hf
  have hv : (fun i => env (Source.SetLanguage.args3 tau labels E i)) =
      Source.SetLanguage.args3 (env tau) (env labels) (env E) := by
    funext i
    refine Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun j => Fin.elim0 j) i) i) i
  simp only [id_eq] at hf
  rw [hv] at hf
  simp only [densityResult,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenConditions.condition_semantics (M := M),ForcingLabelPermutations.subset_semantics (M := M),
    witness_semantics hM]
  exact denseBelow hM hChoice env rho G F mul hw hMu hLarge hCard hmark hpres hm hroot hG hF hc ht hA hE hTau hd0 hz0 hf

theorem density_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I K B w mu e mark root G F mul c t b labels E tau d0 z0 : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (densitySentence rho I K B w mu e mark root G F mul c t b labels E tau d0 z0))) := by
  apply ModelTransfer.derives
  intro N hN
  have hL := ConstructibleSource.model_zf hN
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hN)
  let zero := Classical.choice ((ConstructibleSource.model hN).nonempty .set)
  let env : Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hN)) 0 := ⟨Fin.elim0,fun _ => zero⟩
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hN
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hL) _).mp
    (density_models rho I K B w mu e mark root G F mul c t b labels E tau d0 z0 hL hChoice)

end PPAC.Migration.ForcingClassRepresentation
