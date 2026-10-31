/- Pinned BlockTowers.Cell.rangeAttachment, Merger branch.
Keep the original executed presentation fixed. Construct only its mapped
presentation, then reuse the actual conservative simulation, its inverse and
literal terminal-range identification. No replacement source cell is chosen. -/
import PPAC.Migration.ConstructionRangeObject
import PPAC.Migration.ConstructionMergerWordCancellation
import PPAC.Migration.ConstructionMergerWordTransport

namespace PPAC.Migration.ConstructionMappedMerger
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionMergerPushout (Presentation)
open ConstructionProbePushout (Hom SquareComm)
open ConstructionProbeConservative (Conservative)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ForcingSupportSize (Injection)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ForcingSupportedNames (Range)
open ForcingConditionGraphs (InverseGraph)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Retain the monoid and conicality already proved by the existing word
producer while packaging its SAME word, product, old map and roots. -/
theorem exists_conical_presentation (hM : FirstOrder.Theory.Models M nativeZF)
    {w n zero D mul e P : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e)
    (hP : ConstructionMergerRelations.Prescription n D P)
    (hValid : ConstructionMergerRelations.Valid n D mul P) :
    ∃ C L projection A W T B G unit O roots,
      Presentation w n zero D mul e P C L projection A W T B G unit O roots ∧
      LeftCancelMonoid W G unit ∧ Conical W G unit := by
  obtain ⟨C,L,projection,K,A,W,I,T,B,G,unit,hParent,hUnit,hmW,hcW⟩ :=
    ConstructionMergerWordCancellation.exists_system hM hw hz hzw hm hc hP hValid
  obtain ⟨hC,hp,hL,hProjection,hEq,_,_,hAction,_,hCopy,hW,_,_,hWordAction,_,hB,hG,hProduct⟩ := hParent
  obtain ⟨O,hO,hOG⟩ := ConstructionMergerOldEmbedding.exists_old_graph hM hz hzw hW
  have hOH : Hom D W mul G e unit O := ⟨hO.1,(hOG e unit).mpr hUnit,
    ConstructionMergerOldEmbedding.preserves_products hOG hWordAction hProduct⟩
  obtain ⟨roots,hRootsMap,hRoots⟩ := ConstructionMergerRoots.exists_root_graph hM hw hz hzw hm hW hC hp hUnit
  exact ⟨C,L,projection,A,W,T,B,G,unit,O,roots,
    ⟨hm,hP,hC,hL,hp,hProjection,hEq,hAction,hCopy,hW,hWordAction,hProduct,hUnit,
      hmW.1,hmW.2.2,hB,hG,hOG,hOH,hRootsMap,hRoots⟩,hmW,hcW⟩

/-- The mapped cell and its actual simulation/identification. The original
source W/G/unit/O/roots and literal ranges N/R are parameters, not rebuilt. -/
def Data (w n zero P W G unit O roots N mulN eN f V GV unitV g R
    PN CN LN projectionN AN WN TN BN GN unitN ON rootsN H inv embedding : M.Carrier .set) : Prop :=
  ConstructionMergerPrescriptionMap.Graph P f PN ∧
    ConstructionMergerRelations.Valid n N mulN PN ∧
    Presentation w n zero N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN ∧
    LeftCancelMonoid WN GN unitN ∧ Conical WN GN unitN ∧
    Hom W WN G GN unit unitN H ∧ Conservative W WN G GN H ∧
    SquareComm O f H ON ∧ NodeMap roots H rootsN ∧ Range W H WN ∧
    Hom WN W GN G unitN unit inv ∧ InverseGraph H inv ∧
    Hom WN V GN GV unitN unitV embedding ∧ Injection WN V embedding ∧
    NodeMap inv g embedding ∧ ConstructionAttachmentCoefficients.OldFixed ON embedding ∧
    Range WN embedding R

/-- Source d.map e / simulationEquiv / s.symm.trans g.rangeEquiv, with all
mapped data constructed and the actual source presentation held fixed. -/
theorem range_attachment (hM : FirstOrder.Theory.Models M nativeZF)
    {w n zero D mul e P C L projection A W T B G unit O roots N mulN eN f V GV unitV g R : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hA : Presentation w n zero D mul e P C L projection A W T B G unit O roots)
    (hValid : ConstructionMergerRelations.Valid n D mul P)
    (hmW : LeftCancelMonoid W G unit) (hJ : ConditionalJoins D mul)
    (hmN : LeftCancelMonoid N mulN eN) (hcN : Conical N mulN eN)
    (hf : Hom D N mul mulN e eN f) (hCons : Conservative D N mul mulN f)
    (hRange : Range D f N)
    (hg : Hom W V G GV unit unitV g) (hInj : Injection W V g)
    (hOld : NodeMap O g f) (hTerminalRange : Range W g R) :
    ∃ PN CN LN projectionN AN WN TN BN GN unitN ON rootsN H inv embedding,
      Data w n zero P W G unit O roots N mulN eN f V GV unitV g R
        PN CN LN projectionN AN WN TN BN GN unitN ON rootsN H inv embedding := by
  obtain ⟨PN,hPNGraph,hMap,hPN,hValidIff,_,_⟩ :=
    ConstructionMergerPrescriptionMap.exists_system hM hA.monoid hmN hA.prescription hCons hf.2.2 hJ
  have hValidN := hValidIff.mpr hValid
  obtain ⟨CN,LN,projectionN,AN,WN,TN,BN,GN,unitN,ON,rootsN,hB,hmWN,hcWN⟩ :=
    exists_conical_presentation hM hw hz hzw hmN hcN hPN hValidN
  obtain ⟨H,hH,hComm,hRoots⟩ :=
    ConstructionMergerPushout.exists_simulation hM hA hB hw hz hzw hf hMap
  have hConH := ConstructionMergerWordTransport.simulation_conservative hA hB hM hw hz hzw
    hCons hf.2.2 hf.2.1 hMap hJ hH hComm hRoots
  obtain ⟨hOnto,inv,hInv,hInverse⟩ := ConstructionCellSimulationEquiv.merger_equiv hM
    hw hz hzw hA hB hmW hmWN hH hConH.1 hRange hComm hRoots
  obtain ⟨embedding,hEmb,hEmbInj,hComp,hFixed,hExactRange⟩ :=
    ConstructionCellSimulationEquiv.range_identification hM hA.old_hom.1 hB.old_hom.1
      hH hInv hInverse hg hInj hRange hOld hComm hTerminalRange
  exact ⟨PN,CN,LN,projectionN,AN,WN,TN,BN,GN,unitN,ON,rootsN,H,inv,embedding,
    hPNGraph,hValidN,hB,hmWN,hcWN,hH,hConH,hComm,hRoots,hOnto,hInv,hInverse,
    hEmb,hEmbInj,hComp,hFixed,hExactRange⟩

/-- Discharge the target-range object and its conservative base change with
ConstructionRangeObject. The original presentation and both literal ranges
remain fixed throughout the entire source rangeAttachment construction. -/
theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    {w n zero D mul e P C L projection A W T B G unit O roots V GV unitV f g N R : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hA : Presentation w n zero D mul e P C L projection A W T B G unit O roots)
    (hValid : ConstructionMergerRelations.Valid n D mul P)
    (hmW : LeftCancelMonoid W G unit) (hJ : ConditionalJoins D mul)
    (hv : LeftCancelMonoid V GV unitV) (hc : Conical V GV unitV) (hJV : ConditionalJoins V GV)
    (hf : Hom D V mul GV e unitV f) (hCons : Conservative D V mul GV f)
    (hRange : Range D f N)
    (hg : Hom W V G GV unit unitV g) (hInj : Injection W V g)
    (hOld : NodeMap O g f) (hTerminalRange : Range W g R) :
    ∃ basePairs mulN inc baseInv PN CN LN projectionN AN WN TN BN GN unitN ON rootsN H inv embedding,
      ConstructionRangeObject.Data w zero D V mul GV e unitV f N basePairs mulN inc baseInv ∧
      Data w n zero P W G unit O roots N mulN unitV f V GV unitV g R
        PN CN LN projectionN AN WN TN BN GN unitN ON rootsN H inv embedding := by
  obtain ⟨basePairs,mulN,inc,baseInv,hBase⟩ :=
    ConstructionRangeObject.construction hM hA.monoid hJ hv hc hJV hf hCons hRange
  have hKeep := hBase
  obtain ⟨_,_,_,_,hmN,hcN,_,_,_,_,hfN,hConsN,_,_,_,_,_⟩ := hBase
  obtain ⟨PN,CN,LN,projectionN,AN,WN,TN,BN,GN,unitN,ON,rootsN,H,inv,embedding,hData⟩ :=
    range_attachment hM hw hz hzw hA hValid hmW hJ hmN hcN hfN hConsN hRange hg hInj hOld hTerminalRange
  exact ⟨basePairs,mulN,inc,baseInv,PN,CN,LN,projectionN,AN,WN,TN,BN,GN,unitN,ON,rootsN,H,inv,embedding,hKeep,hData⟩

/-- Object formula retaining the same mapped prescription, simulation,
inverse and terminal-range embedding, including every old/root equation. -/
def data {m : Nat} (w n zero P W G unit O roots N mulN eN f V GV unitV g R PN CN LN projectionN AN WN TN BN GN unitN ON rootsN H inv embedding : Fin m) : Project.Formula 1 m :=
  .conj (ConstructionMergerPrescriptionMapSyntax.graph P f PN)
    (.conj (ConstructionMergerRelations.valid n N mulN PN)
    (.conj (ConstructionMergerPushout.presentation w n zero N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN)
    (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid WN GN unitN))
    (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.conical WN GN unitN))
    (.conj (ConstructionProbePushoutSyntax.hom W WN G GN unit unitN H)
    (.conj (ConstructionProbeConservativeSyntax.conservative W WN G GN H)
    (.conj (ConstructionProbePushoutSyntax.squareComm O f H ON)
    (.conj (ConstructionProbeMappedPathSyntax.nodeMap roots H rootsN)
    (.conj (ProjectSyntax.encode id (ForcingSupportedNames.range W H WN))
    (.conj (ConstructionProbePushoutSyntax.hom WN W GN G unitN unit inv)
    (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.inverseGraph H inv))
    (.conj (ConstructionProbePushoutSyntax.hom WN V GN GV unitN unitV embedding)
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection embedding WN V))
    (.conj (ConstructionProbeMappedPathSyntax.nodeMap inv g embedding)
    (.conj (ConstructionAttachmentCoefficients.oldFixed ON embedding)
    (ProjectSyntax.encode id (ForcingSupportedNames.range WN embedding R)))))))))))))))))

theorem data_freeClosed {m : Nat} (w n zero P W G unit O roots N mulN eN f V GV unitV g R PN CN LN projectionN AN WN TN BN GN unitN ON rootsN H inv embedding : Fin m) :
    (data w n zero P W G unit O roots N mulN eN f V GV unitV g R PN CN LN projectionN AN WN TN BN GN unitN ON rootsN H inv embedding).FreeClosed := by
  simp -implicitDefEqProofs [data,Definitional.Formula.FreeClosed,
    ProjectSyntax.freeClosed,
    ConstructionMergerPrescriptionMapSyntax.graph_freeClosed,
    ConstructionMergerRelations.valid_freeClosed,
    ConstructionMergerPushout.presentation_freeClosed,
    ConstructionProbePushoutSyntax.hom_freeClosed,
    ConstructionProbeConservativeSyntax.conservative_freeClosed,
    ConstructionProbePushoutSyntax.squareComm_freeClosed,
    ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,
    ConstructionAttachmentCoefficients.oldFixed_freeClosed]

theorem data_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w n zero P W G unit O roots N mulN eN f V GV unitV g R PN CN LN projectionN AN WN TN BN GN unitN ON rootsN H inv embedding : Fin m) :
    Project.Formula.satisfies env (data w n zero P W G unit O roots N mulN eN f V GV unitV g R PN CN LN projectionN AN WN TN BN GN unitN ON rootsN H inv embedding) ↔
      Data (env.bound w) (env.bound n) (env.bound zero) (env.bound P) (env.bound W) (env.bound G) (env.bound unit) (env.bound O) (env.bound roots) (env.bound N) (env.bound mulN) (env.bound eN) (env.bound f) (env.bound V) (env.bound GV) (env.bound unitV) (env.bound g) (env.bound R) (env.bound PN) (env.bound CN) (env.bound LN) (env.bound projectionN) (env.bound AN) (env.bound WN) (env.bound TN) (env.bound BN) (env.bound GN) (env.bound unitN) (env.bound ON) (env.bound rootsN) (env.bound H) (env.bound inv) (env.bound embedding) := by
  simp only [data,Data,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionMergerPrescriptionMapSyntax.graph_semantics hM,
    ConstructionMergerRelations.valid_semantics hM,
    ConstructionMergerPushout.presentation_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingDiagramPoset.conical_semantics (M := M),
    ConstructionProbePushoutSyntax.hom_semantics hM,
    ConstructionProbeConservativeSyntax.conservative_semantics hM,
    ConstructionProbePushoutSyntax.squareComm_semantics hM,
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,
    ForcingSupportedNames.range_semantics (M := M),
    ForcingConditionGraphs.inverseGraph_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),
    ConstructionAttachmentCoefficients.oldFixed_semantics hM]
  rfl

/-- The Merger branch of rangeAttachment with the complete range-object
construction discharged. All nineteen output sets/graphs are internal. -/
def constructionSentence {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots V GV unitV f g N R : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isEmpty (.bound zero))
    (.imp (.mem (.bound zero) (.bound w))
    (.imp (ConstructionMergerPushout.presentation w n zero D mul e P C L projection A W T B G unit O roots)
    (.imp (ConstructionMergerRelations.valid n D mul P)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid W G unit))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul)
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV unitV))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV unitV))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV)
    (.imp (ConstructionProbePushoutSyntax.hom D V mul GV e unitV f)
    (.imp (ConstructionProbeConservativeSyntax.conservative D V mul GV f)
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range D f N))
    (.imp (ConstructionProbePushoutSyntax.hom W V G GV unit unitV g)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection g W V))
    (.imp (ConstructionProbeMappedPathSyntax.nodeMap O g f)
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range W g R))
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionRangeObject.data w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 18 17 16 15)
      (data w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ n.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ P.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ unit.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ O.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ roots.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 17 unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ unitV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ g.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 14 13 12 11 10 9 8 7 6 5 4 3 2 1 0))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isInductive,Project.Formula.isSuccessor,Project.Formula.isEmpty,
      data_freeClosed,ConstructionRangeObject.data_freeClosed,
      ConstructionMergerPushout.presentation_freeClosed,ConstructionMergerRelations.valid_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionProbePushoutSyntax.hom_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,
      ConstructionProbeMappedPathSyntax.nodeMap_freeClosed]

theorem construction_models {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots V GV unitV f g N R : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence w n zero D mul e P C L projection A W T B G unit O roots V GV unitV f g N R)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w n zero D mul e P C L projection A W T B G unit O roots V GV unitV f g N R)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionMergerPushout.presentation_semantics hM,ConstructionMergerRelations.valid_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ConstructionProbePushoutSyntax.hom_semantics hM,ConstructionProbeConservativeSyntax.conservative_semantics hM,
    ForcingSupportedNames.range_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,ConstructionRangeObject.data_semantics hM,data_semantics hM]
  exact construction hM

theorem construction_kernel_certificate {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots V GV unitV f g N R : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence w n zero D mul e P C L projection A W T B G unit O roots V GV unitV f g N R)) :=
  ModelTransfer.derives (fun _ hM => construction_models w n zero D mul e P C L projection A W T B G unit O roots V GV unitV f g N R hM)

end PPAC.Migration.ConstructionMappedMerger
