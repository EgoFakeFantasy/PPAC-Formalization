/- Pinned StableSelectors.good_dense:199-206: choose all separating bits,
place them below one strict countable bound, and fill the bounded detector
rows. Reuse existing internal uniformization, Hartogs/regular range bounds,
and the actual Complete extension. Pattern injectivity is the next consumer. -/
import PPAC.Migration.ConstructionCohenPairSeparation
import PPAC.Migration.ConstructionSaturationBoundedness

namespace PPAC.Migration.ConstructionGermBoundedRows
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingCohenCoordinates (Cartesian)
open ForcingCohenConditions (Condition)
open ConstructionCohenCompatibility (Entry)
open ConstructionCohenPairSeparation (Pairs Requirement)
open ConstructionGermCosets (Carrier)
open ConstructionGermDetectors (Detectors)
open ConstructionGermDetectorSites (Covers)
open ConstructionGermComplete (Complete)
open ForcingSupportSize (Small)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Bit (lo hi z p b : M.Carrier .set) : Prop := ∃ j k,
  PureKuratowski.Code M z j k ∧ Entry p j b lo ∧ Entry p k b hi

def bit {m : Nat} (lo hi z p b : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (PureKuratowskiProject.code (.bound z.succ.succ) (.bound 1) (.bound 0))
    (.conj (ConstructionCohenCompatibility.entry p.succ.succ 1 b.succ.succ lo.succ.succ)
      (ConstructionCohenCompatibility.entry p.succ.succ 0 b.succ.succ hi.succ.succ))))

theorem bit_freeClosed {m : Nat} (lo hi z p b : Fin m) : (bit lo hi z p b).FreeClosed := by
  simp -implicitDefEqProofs [bit,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,ConstructionCohenCompatibility.entry_freeClosed]

theorem bit_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (lo hi z p b : Fin m) :
    Project.Formula.satisfies env (bit lo hi z p b) ↔
      Bit (env.bound lo) (env.bound hi) (env.bound z) (env.bound p) (env.bound b) := by
  simp only [bit,Bit,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    KuratowskiZF.code_correct hM,Project.Term.eval_bound,ConstructionCohenCompatibility.entry_semantics hM]
  rfl

theorem bounded_bits (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w K A p lo hi : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hHartogs : ConstructionSaturationIndex.Hartogs hM w K)
    (hReg : (Project.FirstOrderSemantics.reduct M).IsRegularCardinal (KuratowskiZF.interpretation hM) K)
    (hSmall : Small A w) (hReq : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z A → Requirement K lo hi z p) :
    ∃ alpha, (Project.FirstOrderSemantics.reduct M).mem alpha K ∧ Small alpha w ∧
      ∀ z, (Project.FirstOrderSemantics.reduct M).mem z A → Requirement alpha lo hi z p := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let P := KuratowskiZF.interpretation hM
  let schema : Project.BinarySchema 3 := { body := bit 3 4 1 2 0, freeClosed := bit_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases p (Fin.cases lo (fun _ => hi)), free := fun _ => p }
  have he z b : schema.denote env z b ↔ Bit lo hi z p b := bit_semantics hM ((env.push z).push b) 3 4 1 2 0
  obtain ⟨f,hf,hBits⟩ := ExistingSmallUnion.uniformize_formula_l P
    (ConstructionDirectedCardinality.models_zfc hM hChoice) schema env (X := A) (Y := K) (by
      intro z hz
      obtain ⟨j,k,b,hzjk,hb,hlo,hhi⟩ := hReq z hz
      exact ⟨b,hb,(he z b).mpr ⟨j,k,hzjk,hlo,hhi⟩⟩)
  obtain ⟨bound,hbound,hBelow⟩ := ConstructionSaturationBoundedness.countable_bounded hM hw hHartogs hReg hSmall hf
  obtain ⟨alpha,hAlpha,hBoundAlpha⟩ := hReg.isLimitOrdinal.2.2 bound hbound
  have hAlphaOrd := hHartogs.1.mem hAlpha
  have hAlphaSmall := (ForcingSupportSize.native_small hM alpha w).mpr ((hHartogs.2 alpha hAlphaOrd).mp hAlpha)
  refine ⟨alpha,hAlpha,hAlphaSmall,?_⟩
  intro z hz
  obtain ⟨b,_,hzb⟩ := hf.2.2 z hz
  have hbAlpha := (hBelow z b hzb).elim (fun he => he.symm ▸ hBoundAlpha)
    (fun hb => hAlphaOrd.transitive bound hBoundAlpha b hb)
  obtain ⟨j,k,hzjk,hlo,hhi⟩ := (he z b).mp (hBits z b hzb)
  exact ⟨j,k,b,hzjk,hbAlpha,hlo,hhi⟩

/-- The same extending condition has both completely assigned bounded
patterns and separating bits below that one strict bound for every unequal
pair of actual detector sites. No density/choice-of-bits premise remains. -/
theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w D I mul q root chain H N X reps det J K C B S lo hi p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hHartogs : ConstructionSaturationIndex.Hartogs hM w K)
    (hReg : (Project.FirstOrderSemantics.reduct M).IsRegularCardinal (KuratowskiZF.interpretation hM) K)
    (hH : Carrier D I mul q root H) (hDet : Detectors D I chain X reps det)
    (hX : Cartesian N w X) (hCovers : Covers w H det J)
    (hJ : Small J w) (hJI : (Project.FirstOrderSemantics.reduct M).MemberSubset J I)
    (hC : Cartesian I K C) (hS : Cartesian C B S)
    (hlo : (Project.FirstOrderSemantics.reduct M).mem lo B) (hhi : (Project.FirstOrderSemantics.reduct M).mem hi B)
    (hp : Condition S w p) :
    ∃ A alpha r, Pairs J A ∧ Small A w ∧ (Project.FirstOrderSemantics.reduct M).mem alpha K ∧ Small alpha w ∧
      Condition S w r ∧ (Project.FirstOrderSemantics.reduct M).MemberSubset p r ∧
        Complete w H N det alpha r ∧ ∀ z, (Project.FirstOrderSemantics.reduct M).mem z A → Requirement alpha lo hi z r := by
  have hNotSmall : ¬ Small K w := fun h => hHartogs.not_cardinalLessOrEqual
    (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) ((ForcingSupportSize.native_small hM K w).mp h)
  obtain ⟨A,r,hPairs,hASmall,hr,hpr,hReq⟩ := ConstructionCohenPairSeparation.construction hM hChoice
    hw hC hS hp hNotSmall hJ hJI hlo hhi
  obtain ⟨alpha,hAlpha,hAlphaSmall,hBounded⟩ := bounded_bits hM hChoice hw hHartogs hReg hASmall hReq
  obtain ⟨W,s,_,_,hs,_,hrs,hComplete⟩ := ConstructionGermComplete.construction hM hw hH hDet hX hCovers
    hJ hJI hAlphaSmall (hHartogs.1.transitive alpha hAlpha) hC hS hlo hr
  exact ⟨A,alpha,s,hPairs,hASmall,hAlpha,hAlphaSmall,hs,fun z hz => hrs z (hpr z hz),hComplete,
    fun z hz => ConstructionCohenPairSeparation.requirement_mono hrs (hBounded z hz)⟩

def constructionSentence {m : Nat} (w D I mul q root chain H N X reps det J K C B S lo hi p : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (ConstructionSaturationIndex.hartogs w K) (.imp (ConstructionSaturationIndex.regular K) (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ConstructionGermDetectors.detectors D I chain X reps det) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian N w X)) (.imp (ConstructionGermDetectorSites.coversFormula w H det J) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small J w)) (.imp (Project.Formula.subset (.bound J) (.bound I)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K C)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian C B S)) (.imp (.mem (.bound lo) (.bound B)) (.imp (.mem (.bound hi) (.bound B)) (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S w p)) (.existsE (.existsE (.existsE (.conj (ConstructionCohenPairSeparation.pairs J.succ.succ.succ 2) (.conj (ProjectSyntax.encode id (ForcingSupportSize.small 2 w.succ.succ.succ)) (.conj (.mem (.bound 1) (.bound K.succ.succ.succ)) (.conj (ProjectSyntax.encode id (ForcingSupportSize.small 1 w.succ.succ.succ)) (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ.succ.succ w.succ.succ.succ 0)) (.conj (Project.Formula.subset (.bound p.succ.succ.succ) (.bound 0)) (.conj (ConstructionGermComplete.complete w.succ.succ.succ H.succ.succ.succ N.succ.succ.succ det.succ.succ.succ 1 0) (.forallE (.imp (.mem (.bound 0) (.bound 3)) (ConstructionCohenPairSeparation.requirement 2 lo.succ.succ.succ.succ hi.succ.succ.succ.succ 0 1)))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,Project.Formula.subset,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationIndex.regular_freeClosed,
      ConstructionGermCosets.carrier_freeClosed,ConstructionGermDetectors.detectors_freeClosed,
      ConstructionGermDetectorSites.coversFormula_freeClosed,ConstructionCohenPairSeparation.pairs_freeClosed,
      ConstructionCohenPairSeparation.requirement_freeClosed,ConstructionGermComplete.complete_freeClosed]

theorem construction_models {m : Nat} (w D I mul q root chain H N X reps det J K C B S lo hi p : Fin m) (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence w D I mul q root chain H N X reps det J K C B S lo hi p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w D I mul q root chain H N X reps det J K C B S lo hi p)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationIndex.hartogs_semantics hM,
    ConstructionSaturationIndex.regular_semantics hM,ConstructionGermCosets.carrier_semantics hM,
    ConstructionGermDetectors.detectors_semantics hM,ConstructionGermDetectorSites.coversFormula_semantics hM,
    ConstructionCohenPairSeparation.pairs_semantics hM,ConstructionCohenPairSeparation.requirement_semantics hM,
    ConstructionGermComplete.complete_semantics hM]
  exact construction hM hChoice

theorem construction_kernel_certificate {m : Nat} (w D I mul q root chain H N X reps det J K C B S lo hi p : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (constructionSentence w D I mul q root chain H N X reps det J K C B S lo hi p))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let z := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => z }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (constructionSentence w D I mul q root chain H N X reps det J K C B S lo hi p)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence w D I mul q root chain H N X reps det J K C B S lo hi p)).mp (construction_models w D I mul q root chain H N X reps det J K C B S lo hi p hL hChoice)




end PPAC.Migration.ConstructionGermBoundedRows
