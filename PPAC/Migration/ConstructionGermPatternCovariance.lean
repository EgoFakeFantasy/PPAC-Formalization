/- Pinned GermSelectors.pattern_covariance/distinguishes_moveRows_iff and
StableSelectors.Good.permute. Exact equality of actual pattern values on the
whole quotient, followed by preservation of the same Complete bound. -/
import PPAC.Migration.ConstructionGermLeftAction

namespace PPAC.Migration.ConstructionGermPatternCovariance
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (Permutation CompositionGraph function_input function_unique)
open ConstructionGermCosets (Carrier Classes)
open ConstructionGermPattern (Pattern)
open ConstructionGermLeftAction (Action)
open ConstructionCohenCompatibility (Moved)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem rawPattern_moved {w N X I alpha B A E det pi g product R U pr P : M.Carrier .set}
    (hDet : MapsTo X I det) (hpi : Permutation I pi) (hg : MapsTo I I g)
    (hComp : CompositionGraph I pi g product) (hMove : Moved pi R U)
    (hP : ConstructionGermRawPattern.RawPattern w N alpha B A E det g R pr P) :
    ConstructionGermRawPattern.RawPattern w N alpha B A E det product U pr P := by
  refine ⟨hP.1,fun delta e => (hP.2 delta e).trans (and_congr Iff.rfl ?_)⟩
  exact exists_congr (fun s => and_congr (ConstructionGermRowCovariance.sequence_moved hDet hpi hg hComp hMove) Iff.rfl)

theorem pattern_moved_edge (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act C V P : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul unit)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul) (hq : Injection D I q)
    (hH : Carrier D I mul q root H) (hG : Classes w D chain H G) (hDet : MapsTo X I det)
    (hpi : (Project.FirstOrderSemantics.reduct M).mem pi H) (hMove : Moved pi R U)
    (hAct : Action w D I chain H G pi act)
    (hF : Pattern w D chain H G N alpha B A E T det R pr F)
    (hQ : Pattern w D chain H G N alpha B A E T det U pr Q)
    (hCV : PureKuratowski.PairMember M C V act) (hCP : PureKuratowski.PairMember M C P F) :
    PureKuratowski.PairMember M V P Q := by
  obtain ⟨hCG,g,hg,hClass,hRaw⟩ := (hF.2 C P).mp hCP
  have hp := (hH pi).mp hpi
  have hg' := (hH g).mp hg
  obtain ⟨pg,hpg,hComp⟩ := ForcingConditionGraphs.exists_composition hM hp.1 hg'.1
  have hpgH := (hH pg).mpr (ConstructionGermSeparation.stabilizes_composition hM hm hJ hq hp hg' hpg hComp)
  obtain ⟨V',hV'⟩ := ConstructionGermCosets.exists_class hM w D chain H pg
  have hCV' := (hAct.2 C V').mpr ⟨hCG,g,pg,hg,hpgH,hClass,hV',hComp⟩
  have e := function_unique hAct.1.1.1 hCV' hCV
  subst V'
  exact ConstructionGermPattern.pattern_mk hG hQ pg V P hpgH hV'
    (rawPattern_moved hDet hp.1 hg'.1.1 hComp hMove hRaw)

theorem pattern_covariance (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul unit)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul) (hq : Injection D I q)
    (hH : Carrier D I mul q root H) (hG : Classes w D chain H G) (hDet : MapsTo X I det)
    (hpi : (Project.FirstOrderSemantics.reduct M).mem pi H) (hMove : Moved pi R U)
    (hAct : Action w D I chain H G pi act)
    (hF : Pattern w D chain H G N alpha B A E T det R pr F)
    (hQ : Pattern w D chain H G N alpha B A E T det U pr Q) : CompositionGraph G Q act F := by
  intro C P
  constructor
  · intro hCP
    have hCG := function_input hF.1.1 hCP
    obtain ⟨V,hCV,_⟩ := hAct.1.1.1.2 C hCG
    exact ⟨hCG,V,hCV,pattern_moved_edge hM hm hJ hq hH hG hDet hpi hMove hAct hF hQ hCV hCP⟩
  · rintro ⟨hCG,V,hCV,hVP⟩
    obtain ⟨P',hCP',_⟩ := hF.1.1.2 C hCG
    have hVP' := pattern_moved_edge hM hm hJ hq hH hG hDet hpi hMove hAct hF hQ hCV hCP'
    have e := function_unique hQ.1.1 hVP' hVP
    exact e ▸ hCP'

theorem injection_iff {G T F Q act : M.Carrier .set}
    (hF : MapsTo G T F) (hQ : MapsTo G T Q) (hAct : Permutation G act)
    (hComp : CompositionGraph G Q act F) : Injection G T Q ↔ Injection G T F := by
  constructor
  · intro hInj
    refine ⟨hF,?_⟩
    intro C E P hCP hEP
    obtain ⟨_,V,hCV,hVP⟩ := (hComp C P).mp hCP
    obtain ⟨_,W,hEW,hWP⟩ := (hComp E P).mp hEP
    have e := hInj.2 V W P hVP hWP
    subst W
    exact hAct.2.1 C E V hCV hEW
  · intro hInj
    refine ⟨hQ,?_⟩
    intro C E P hCP hEP
    obtain ⟨V,hVG,hVC⟩ := hAct.2.2 C (function_input hQ.1 hCP)
    obtain ⟨W,hWG,hWE⟩ := hAct.2.2 E (function_input hQ.1 hEP)
    have e := hInj.2 V W P ((hComp V P).mpr ⟨hVG,C,hVC,hCP⟩) ((hComp W P).mpr ⟨hWG,E,hWE,hEP⟩)
    subst W
    exact function_unique hAct.1.1 hVC hWE

theorem distinguishes_moveRows_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul unit)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul) (hq : Injection D I q)
    (hH : Carrier D I mul q root H) (hG : Classes w D chain H G) (hDet : MapsTo X I det)
    (hpi : (Project.FirstOrderSemantics.reduct M).mem pi H) (hMove : Moved pi R U)
    (hAct : Action w D I chain H G pi act)
    (hF : Pattern w D chain H G N alpha B A E T det R pr F)
    (hQ : Pattern w D chain H G N alpha B A E T det U pr Q) : Injection G T Q ↔ Injection G T F :=
  injection_iff hF.1 hQ.1 hAct.1 (pattern_covariance hM hm hJ hq hH hG hDet hpi hMove hAct hF hQ)

theorem good_permute (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi p r : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul unit)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul) (hq : Injection D I q)
    (hChain : ConstructionComponentCofinal.Chain w D I mul q zero root vertices chain)
    (hH : Carrier D I mul q root H) (hG : Classes w D chain H G)
    (hDet : ConstructionGermDetectors.Detectors D I chain X reps det)
    (hX : ForcingCohenCoordinates.Cartesian N w X) (hC : ForcingCohenCoordinates.Cartesian I K C)
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal K)
    (hlo : (Project.FirstOrderSemantics.reduct M).mem lo B) (hhi : (Project.FirstOrderSemantics.reduct M).mem hi B)
    (hpi : (Project.FirstOrderSemantics.reduct M).mem pi H) (hMove : Moved pi p r)
    (hGood : ConstructionGermGoodDense.Good w D chain H G N K C B lo hi det p) :
    ConstructionGermGoodDense.Good w D chain H G N K C B lo hi det r := by
  obtain ⟨alpha,R,A,Seq,E,pr,T,F,hAlpha,hRows,hA,hSeq,hpr,hE,hProj,hExact,hT,hF,hInj,hComplete⟩ := hGood
  obtain ⟨U,hRowsU⟩ := ConstructionCohenRows.exists_rows (p := r) hM hlo hhi
  obtain ⟨Q,hQ⟩ := ConstructionGermPattern.exists_pattern hM hw hChain hDet hH hG hX hC hRowsU.1
    (hK.transitive alpha hAlpha) hA hSeq hT hpr hExact
  obtain ⟨act,hAct⟩ := ConstructionGermLeftAction.construction hM hw hm hJ hq hChain hH hG hpi
  have hMovedRows := ConstructionGermRowCovariance.rows_permute hM hC ((hH pi).mp hpi).1 hMove hRows hRowsU
  have hInjQ := (distinguishes_moveRows_iff hM hm hJ hq hH hG hDet.1 hpi hMovedRows hAct hF hQ).mpr hInj
  exact ⟨alpha,U,A,Seq,E,pr,T,Q,hAlpha,hRowsU,hA,hSeq,hpr,hE,hProj,hExact,hT,hQ,hInjQ,
    ConstructionGermRowCovariance.complete_permute hM hm hJ hq hH hpi hMove hComplete⟩

def covarianceSentence {m : Nat} (w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul unit)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q D I)) (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ConstructionGermCosets.classes w D chain H G) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo det X I)) (.imp (.mem (.bound pi) (.bound H)) (.imp (ConstructionCohenCompatibility.moved pi R U) (.imp (ConstructionGermLeftAction.action w D I chain H G pi act) (.imp (ConstructionGermPattern.pattern w D chain H G N alpha B A E T det R pr F) (.imp (ConstructionGermPattern.pattern w D chain H G N alpha B A E T det U pr Q) (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph G Q act F)))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionGermCosets.carrier_freeClosed,ConstructionGermCosets.classes_freeClosed,ConstructionCohenCompatibility.moved_freeClosed,ConstructionGermLeftAction.action_freeClosed,ConstructionGermPattern.pattern_freeClosed]

theorem covariance_models {m : Nat} (w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (covarianceSentence w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (covarianceSentence w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ForcingSupportSize.injection_semantics (M := M),ConstructionGermCosets.carrier_semantics hM,ConstructionGermCosets.classes_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ConstructionCohenCompatibility.moved_semantics hM,ConstructionGermLeftAction.action_semantics hM,ConstructionGermPattern.pattern_semantics hM,ForcingConditionGraphs.compositionGraph_semantics (M := M)]
  exact pattern_covariance hM

theorem covariance_kernel_certificate {m : Nat} (w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (covarianceSentence w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act)) :=
  ModelTransfer.derives (fun _ hM => covariance_models w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act hM)

def injectionSentence {m : Nat} (w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul unit)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q D I)) (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ConstructionGermCosets.classes w D chain H G) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo det X I)) (.imp (.mem (.bound pi) (.bound H)) (.imp (ConstructionCohenCompatibility.moved pi R U) (.imp (ConstructionGermLeftAction.action w D I chain H G pi act) (.imp (ConstructionGermPattern.pattern w D chain H G N alpha B A E T det R pr F) (.imp (ConstructionGermPattern.pattern w D chain H G N alpha B A E T det U pr Q) (.iff (ProjectSyntax.encode id (Source.SetLanguage.injection Q G T)) (ProjectSyntax.encode id (Source.SetLanguage.injection F G T))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionGermCosets.carrier_freeClosed,ConstructionGermCosets.classes_freeClosed,ConstructionCohenCompatibility.moved_freeClosed,ConstructionGermLeftAction.action_freeClosed,ConstructionGermPattern.pattern_freeClosed]

theorem injection_models {m : Nat} (w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (injectionSentence w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (injectionSentence w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ForcingSupportSize.injection_semantics (M := M),ConstructionGermCosets.carrier_semantics hM,ConstructionGermCosets.classes_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ConstructionCohenCompatibility.moved_semantics hM,ConstructionGermLeftAction.action_semantics hM,ConstructionGermPattern.pattern_semantics hM]
  exact distinguishes_moveRows_iff hM

theorem injection_kernel_certificate {m : Nat} (w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (injectionSentence w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act)) :=
  ModelTransfer.derives (fun _ hM => injection_models w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act hM)

def goodSentence {m : Nat} (w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi p r : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul unit)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q D I)) (.imp (ConstructionComponentCofinal.chain w D I mul q zero root vertices chain) (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ConstructionGermCosets.classes w D chain H G) (.imp (ConstructionGermDetectors.detectors D I chain X reps det) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian N w X)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K C)) (.imp (Project.Formula.isOrdinal (.bound K)) (.imp (.mem (.bound lo) (.bound B)) (.imp (.mem (.bound hi) (.bound B)) (.imp (.mem (.bound pi) (.bound H)) (.imp (ConstructionCohenCompatibility.moved pi p r) (.imp (ConstructionGermGoodDense.good w D chain H G N K C B lo hi det p) (ConstructionGermGoodDense.good w D chain H G N K C B lo hi det r)))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionGermCosets.carrier_freeClosed,ConstructionGermCosets.classes_freeClosed,ConstructionCohenCompatibility.moved_freeClosed,Project.Formula.isOmega,Project.Formula.isOrdinal,ConstructionComponentCofinal.chain_freeClosed,ConstructionGermDetectors.detectors_freeClosed,ConstructionGermGoodDense.good_freeClosed]

theorem good_models {m : Nat} (w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi p r : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (goodSentence w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi p r)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (goodSentence w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi p r)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ForcingSupportSize.injection_semantics (M := M),ConstructionGermCosets.carrier_semantics hM,ConstructionGermCosets.classes_semantics hM,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ConstructionCohenCompatibility.moved_semantics hM,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isOrdinal_iff,ConstructionComponentCofinal.chain_semantics hM,ConstructionGermDetectors.detectors_semantics hM,ForcingCohenCoordinates.cartesian_semantics (M := M),ConstructionGermGoodDense.good_semantics hM]
  exact good_permute hM

theorem good_kernel_certificate {m : Nat} (w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi p r : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (goodSentence w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi p r)) :=
  ModelTransfer.derives (fun _ hM => good_models w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi p r hM)

end PPAC.Migration.ConstructionGermPatternCovariance
