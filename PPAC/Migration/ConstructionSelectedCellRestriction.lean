/- Pinned CellCuts.restrict_selected: the retained old-stage subobject and
its simulation range. Reuse existing conservative-hull and generated/comap
proofs. Full cell simulation and pushout assembly remain separate consumers. -/
import PPAC.Migration.ConstructionSelectedCellWords

namespace PPAC.Migration.ConstructionSelectedCellRestriction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionConservativeHull (Closure ProductGraph)
open ConstructionCellGeneration (Submonoid Generated ClosureMember)
open ConstructionProbePushout (Hom)
open ConstructionProbeConservative (Conservative)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionAttachmentCoefficients (OldFixed)
open ForcingSupportSize (MapsTo)
open ForcingSupportedNames (Range)
open ForcingConditionGraphs (IdentityGraph function_input function_unique)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Restrict the SAME ambient conservative subobject to the SAME stage.
Join preservation is consumed from the existing conservative-hull theorem. -/
theorem cut_closed {V GV e D mul retained cut : M.Carrier .set}
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hD : Closure V GV e D) (hmul : ProductGraph D GV mul)
    (hRet : Closure V GV e retained)
    (hCut : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z cut ↔
      (Project.FirstOrderSemantics.reduct M).mem z retained ∧ (Project.FirstOrderSemantics.reduct M).mem z D) :
    Closure D mul e cut := by
  refine ⟨fun z hz => ((hCut z).mp hz).2,(hCut e).mpr ⟨hRet.2.1,hD.2.1⟩,?_,?_,?_⟩
  · intro x y z hx hy hp
    have hx' := (hCut x).mp hx
    have hy' := (hCut y).mp hy
    have hp' := ((hmul x y z).mp hp).2.2
    exact (hCut z).mpr ⟨hRet.2.2.1 x y z hx'.1 hy'.1 hp',hD.2.2.1 x y z hx'.2 hy'.2 hp'⟩
  · intro x y z hx hy hz hp
    exact (hCut z).mpr ⟨hRet.2.2.2.1 x y z ((hCut x).mp hx).1 ((hCut y).mp hy).1
      (hD.1 z hz) ((hmul x z y).mp hp).2.2,hz⟩
  · intro x y j hx hy hj hJoin
    have hx' := (hCut x).mp hx
    have hy' := (hCut y).mp hy
    exact (hCut j).mpr ⟨hRet.2.2.2.2 x y j hx'.1 hy'.1 (hD.1 j hj)
      (ConstructionConservativeHull.join_preserve hv hc hJ hD hmul hx'.2 hy'.2 hj hJoin),hj⟩

/-- Existing submonoid producer at the supplied literal intersection.
The inclusion used by Cell.exists_preimage is internal and conservative. -/
def Base (D mul e cut pairs cutMul inc : M.Carrier .set) : Prop :=
  Closure D mul e cut ∧ ConstructionProbeLetters.Representatives cut cut pairs ∧ MapsTo pairs cut cutMul ∧
    ProductGraph cut mul cutMul ∧ LeftCancelMonoid cut cutMul e ∧ Conical cut cutMul e ∧
    IdentityGraph cut inc ∧ Hom cut D cutMul mul e e inc ∧ Conservative cut D cutMul mul inc ∧
    ConditionalJoins cut cutMul

theorem base (hM : FirstOrder.Theory.Models M nativeZF)
    {V GV e D mul retained cut : M.Carrier .set}
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hD : Closure V GV e D) (hmul : ProductGraph D GV mul)
    (hRet : Closure V GV e retained)
    (hCut : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z cut ↔
      (Project.FirstOrderSemantics.reduct M).mem z retained ∧ (Project.FirstOrderSemantics.reduct M).mem z D) :
    ∃ pairs cutMul inc, Base D mul e cut pairs cutMul inc := by
  have hClosed := cut_closed hv hc hJ hD hmul hRet hCut
  obtain ⟨pairs,cutMul,inc,h⟩ := ConstructionConservativeHull.exists_submonoid hM
    (ConstructionConservativeHull.monoid hv hD hmul)
    (ConstructionConservativeHull.conical hc hD.1 hmul)
    (ConstructionConservativeHull.conditional_joins hJ hD hmul) hClosed
  exact ⟨pairs,cutMul,inc,hClosed,h⟩

/-- Source restrict_selected's sm and hm: all simulation images are retained,
and every retained next-stage element is in that SAME image. New words are
read from selected_word; old words use the literal fixed inclusion. -/
theorem exact_range (hM : FirstOrder.Theory.Models M nativeZF)
    {D T retained cut next I W G unit V GV e O P F old generators : M.Carrier .set}
    (hm : LeftCancelMonoid W G unit) (hv : LeftCancelMonoid V GV e)
    (hO : MapsTo cut W O) (hP : MapsTo I W P)
    (hF : Hom W V G GV unit e F) (hFT : MapsTo W T F)
    (hGenerated : Generated cut I W G unit O P) (hFixed : OldFixed O F)
    (hGen : NodeMap P F generators) (hGenerators : MapsTo I retained generators)
    (hRet : Submonoid V GV e retained) (hOld : IdentityGraph D old)
    (hCut : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z cut ↔
      (Project.FirstOrderSemantics.reduct M).mem z retained ∧ (Project.FirstOrderSemantics.reduct M).mem z D)
    (hNext : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z next ↔
      (Project.FirstOrderSemantics.reduct M).mem z retained ∧ (Project.FirstOrderSemantics.reduct M).mem z T)
    (hWords : ∀ y, (Project.FirstOrderSemantics.reduct M).mem y retained →
      (Project.FirstOrderSemantics.reduct M).mem y T → ¬ (Project.FirstOrderSemantics.reduct M).mem y D →
      ClosureMember I V GV e old generators cut y) : Range W F next := by
  have hWhole : Submonoid W G unit W := by
    refine ⟨fun _ h => h,hm.1.1,?_⟩
    intro x y z hx hy hp
    obtain ⟨t,ht,hpt⟩ := (hm.2.1 x hx).1 y hy
    exact ((hm.2.1 x hx).2.1 y t z hy hpt hp) ▸ ht
  obtain ⟨Q,hQ,hq⟩ := ConstructionAttachmentCoefficients.exists_comap hM hWhole hF hRet
  have hOldQ : MapsTo cut Q O := by
    refine ⟨hO.1,?_⟩
    intro a u hau
    refine (hq u).mpr ⟨hO.2 a u hau,?_⟩
    intro v huv
    have ev := function_unique hF.1.1 huv (hFixed a u hau)
    exact ev.symm ▸ ((hCut a).mp (function_input hO.1 hau)).1
  have hNewQ : MapsTo I Q P := ⟨hP.1,fun i u hiu =>
    (hq u).mpr ⟨hP.2 i u hiu,fun v huv => hGenerators.2 i v ((hGen i v).mpr ⟨u,hiu,huv⟩)⟩⟩
  have hQW := hGenerated Q hQ hOldQ hNewQ
  have hRangeRet x y (hxy : PureKuratowski.PairMember M x y F) :
      (Project.FirstOrderSemantics.reduct M).mem y retained :=
    ((hq x).mp (hQW.symm ▸ function_input hF.1.1 hxy)).2 y hxy
  obtain ⟨image,hImage⟩ := ConstructionBlockStages.range_exists hM hF.1
  have hImageMonoid := ConstructionCellSimulationEquiv.range_submonoid hm hv hF hImage
  have hOldImage a (ha : (Project.FirstOrderSemantics.reduct M).mem a cut) :
      (Project.FirstOrderSemantics.reduct M).mem a image := by
    obtain ⟨u,hau,_⟩ := hO.1.2 a ha
    exact (hImage a).mpr ⟨u,hO.2 a u hau,hFixed a u hau⟩
  have hNewImage : MapsTo I image generators := by
    refine ⟨hGenerators.1,?_⟩
    intro i v hiv
    obtain ⟨u,hiu,huv⟩ := (hGen i v).mp hiv
    exact (hImage v).mpr ⟨u,hP.2 i u hiu,huv⟩
  intro y
  constructor
  · intro hy
    obtain ⟨hyRet,hyT⟩ := (hNext y).mp hy
    have hyImage : (Project.FirstOrderSemantics.reduct M).mem y image := by
      by_cases hyD : (Project.FirstOrderSemantics.reduct M).mem y D
      · exact hOldImage y ((hCut y).mpr ⟨hyRet,hyD⟩)
      · apply (hWords y hyRet hyT hyD).2 image hImageMonoid
        · intro a z ha haz
          obtain ⟨_,rfl⟩ := (hOld a z).mp haz
          exact hOldImage a ha
        · exact hNewImage
    exact (hImage y).mp hyImage
  · rintro ⟨x,_,hxy⟩
    exact (hNext y).mpr ⟨hRangeRet x y hxy,hFT.2 x y hxy⟩

def baseFormula {m : Nat} (D mul e cut pairs cutMul inc : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionConservativeHull.closure D mul e cut) (.conj (ConstructionProbeLetters.representatives cut cut pairs) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo cutMul pairs cut)) (.conj (ConstructionConservativeHull.productGraph cut mul cutMul) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid cut cutMul e)) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.conical cut cutMul e)) (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph cut inc)) (.conj (ConstructionProbePushoutSyntax.hom cut D cutMul mul e e inc) (.conj (ConstructionProbeConservativeSyntax.conservative cut D cutMul mul inc) (ConstructionProbeSharedIntersections.conditionalJoins cut cutMul))))))))))

theorem baseFormula_freeClosed {m : Nat} (D mul e cut pairs cutMul inc : Fin m) :
    (baseFormula D mul e cut pairs cutMul inc).FreeClosed := by
  simp -implicitDefEqProofs [baseFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionConservativeHull.closure_freeClosed,ConstructionProbeLetters.representatives_freeClosed,ConstructionConservativeHull.productGraph_freeClosed,ConstructionProbePushoutSyntax.hom_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed]

theorem baseFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul e cut pairs cutMul inc : Fin m) :
    Project.Formula.satisfies env (baseFormula D mul e cut pairs cutMul inc) ↔ Base (env.bound D) (env.bound mul) (env.bound e) (env.bound cut) (env.bound pairs) (env.bound cutMul) (env.bound inc) := by
  simp only [baseFormula,Base,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionConservativeHull.closure_semantics hM,ConstructionProbeLetters.representatives_semantics hM,ConstructionConservativeHull.productGraph_semantics hM,ConstructionProbePushoutSyntax.hom_semantics hM,ConstructionProbeConservativeSyntax.conservative_semantics hM,ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ForcingConditionGraphs.identityGraph_semantics (M := M)]

  rfl

def baseSentence {m : Nat} (V GV e D mul retained cut : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV) (.imp (ConstructionConservativeHull.closure V GV e D) (.imp (ConstructionConservativeHull.productGraph D GV mul) (.imp (ConstructionConservativeHull.closure V GV e retained) (.imp (ConstructionAttachmentCoefficients.intersection cut retained D) (.existsE (.existsE (.existsE (baseFormula D.succ.succ.succ mul.succ.succ.succ e.succ.succ.succ cut.succ.succ.succ 2 1 0)))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionConservativeHull.closure_freeClosed,ConstructionConservativeHull.productGraph_freeClosed,ConstructionAttachmentCoefficients.intersection_freeClosed,baseFormula_freeClosed]

theorem base_models {m : Nat} (V GV e D mul retained cut : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (baseSentence V GV e D mul retained cut)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (baseSentence V GV e D mul retained cut)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,


    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionConservativeHull.closure_semantics hM,ConstructionConservativeHull.productGraph_semantics hM,ConstructionAttachmentCoefficients.intersection_semantics (M := M),baseFormula_semantics hM]
  exact base hM

theorem base_kernel_certificate {m : Nat} (V GV e D mul retained cut : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (baseSentence V GV e D mul retained cut)) :=
  ModelTransfer.derives (fun _ hM => base_models V GV e D mul retained cut hM)

def rangeSentence {m : Nat} (D T retained cut next I W G unit V GV e O P F old generators : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid W G unit)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo O cut W)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo P I W)) (.imp (ConstructionProbePushoutSyntax.hom W V G GV unit e F) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo F W T)) (.imp (ConstructionCellGeneration.generated cut I W G unit O P) (.imp (ConstructionAttachmentCoefficients.oldFixed O F) (.imp (ConstructionProbeMappedPathSyntax.nodeMap P F generators) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo generators I retained)) (.imp (ConstructionCellGeneration.submonoid V GV e retained) (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph D old)) (.imp (ConstructionAttachmentCoefficients.intersection cut retained D) (.imp (ConstructionAttachmentCoefficients.intersection next retained T) (.imp (.forallE (.imp (.mem (.bound 0) (.bound retained.succ)) (.imp (.mem (.bound 0) (.bound T.succ)) (.imp (.neg (.mem (.bound 0) (.bound D.succ))) (ConstructionCellGeneration.closureMember I.succ V.succ GV.succ e.succ old.succ generators.succ cut.succ 0))))) (ProjectSyntax.encode id (ForcingSupportedNames.range W F next)))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbePushoutSyntax.hom_freeClosed,ConstructionCellGeneration.generated_freeClosed,ConstructionAttachmentCoefficients.oldFixed_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,ConstructionCellGeneration.submonoid_freeClosed,ConstructionAttachmentCoefficients.intersection_freeClosed,ConstructionCellGeneration.closureMember_freeClosed]

theorem range_models {m : Nat} (D T retained cut next I W G unit V GV e O P F old generators : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (rangeSentence D T retained cut next I W G unit V GV e O P F old generators)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (rangeSentence D T retained cut next I W G unit V GV e O P F old generators)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbePushoutSyntax.hom_semantics hM,ConstructionCellGeneration.generated_semantics hM,ConstructionAttachmentCoefficients.oldFixed_semantics hM,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,ConstructionCellGeneration.submonoid_semantics hM,ForcingConditionGraphs.identityGraph_semantics (M := M),ConstructionAttachmentCoefficients.intersection_semantics (M := M),ConstructionCellGeneration.closureMember_semantics hM,ForcingSupportedNames.range_semantics (M := M)]
  exact exact_range hM

theorem range_kernel_certificate {m : Nat} (D T retained cut next I W G unit V GV e O P F old generators : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (rangeSentence D T retained cut next I W G unit V GV e O P F old generators)) :=
  ModelTransfer.derives (fun _ hM => range_models D T retained cut next I W G unit V GV e O P F old generators hM)

end PPAC.Migration.ConstructionSelectedCellRestriction
