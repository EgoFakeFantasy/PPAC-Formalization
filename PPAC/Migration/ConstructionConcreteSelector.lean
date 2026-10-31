/- Pinned ConcreteQuotients.component_selector_dense:249 and
component_selected_covariant:259. Consume the SAME actual saturated row,
countable germ quotient, detectors, regular Hartogs bound and Selected graph.
No abstract countability, separation, shared-order or nonempty-quotient oracle. -/
import PPAC.Migration.ConstructionGermConditionSelector
import PPAC.Migration.ConstructionCountableGerms

namespace PPAC.Migration.ConstructionConcreteSelector
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection Small)
open ConstructionTowerHistory (Row)
open ForcingConditionGraphs (CompositionGraph function_input)
open ForcingCohenCoordinates (Cartesian)
open ForcingCohenConditions (Condition)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The identity in the actual component stabilizer supplies a germ class. -/
theorem quotient_nonempty (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain H G : M.Carrier .set}
    (hChain : ConstructionComponentCofinal.Chain w D I mul q zero root vertices chain)
    (hq : Injection D I q) (hH : ConstructionGermCosets.Carrier D I mul q root H)
    (hG : ConstructionGermCosets.Classes w D chain H G) :
    ∃ c, (Project.FirstOrderSemantics.reduct M).mem c G := by
  obtain ⟨id,hId,hIdentity⟩ := ForcingConditionGraphs.exists_identity hM I
  have hComp (r : M.Carrier .set) (hr : MapsTo D I r) : CompositionGraph D id r r := by
    intro x y
    constructor
    · intro hxy
      exact ⟨function_input hr.1 hxy,y,hxy,(hIdentity y y).mpr ⟨hr.2 x y hxy,rfl⟩⟩
    · rintro ⟨_,z,hxz,hzy⟩
      exact ((hIdentity z y).mp hzy).2 ▸ hxz
  have hCommon := hChain.2.2.2.1 zero root hChain.2.1
  obtain ⟨r,a,U,s,b,V,hCode,_,hVertex,_,_⟩ := hCommon
  have hStab : ConstructionCountableAlignments.Stabilizes D I mul q root id :=
    ⟨hId,hComp q hq.1,root,⟨r,a,U,r,hCode,hCode,hVertex,hVertex,hComp r hVertex.1.1⟩,
      hChain.2.2.2.1 zero root hChain.2.1⟩
  obtain ⟨c,hClass⟩ := ConstructionGermCosets.exists_class hM w D chain H id
  exact ⟨c,(hG c).mpr ⟨id,(hH id).mpr hStab,hClass⟩⟩

/-- Dense domain of the actual selector, with an actual value at each extension. -/
def Dense (w S f : M.Carrier .set) : Prop := ∀ p, Condition S w p →
  ∃ r c, Condition S w r ∧ (Project.FirstOrderSemantics.reduct M).MemberSubset p r ∧
    PureKuratowski.PairMember M r c f

def dense {m : Nat} (w S f : Fin m) : Project.Formula 1 m :=
  .forallE (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ w.succ 0))
    (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ.succ.succ w.succ.succ.succ 1))
      (.conj (Project.Formula.subset (.bound 2) (.bound 1))
        (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ 1 0)))))))

theorem dense_freeClosed {m : Nat} (w S f : Fin m) : (dense w S f).FreeClosed := by
  simp -implicitDefEqProofs [dense,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.subset]

theorem dense_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w S f : Fin m) :
    Project.Formula.satisfies env (dense w S f) ↔ Dense (env.bound w) (env.bound S) (env.bound f) := by
  simp only [dense,Dense,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingCohenConditions.condition_semantics (M := M),KuratowskiZF.source_edge]
  rfl

/-- All witnesses are internal sets and belong to this SAME concrete component. -/
def Result (hM : FirstOrder.Theory.Models M nativeZF) (w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f : M.Carrier .set) : Prop :=
  ConstructionGermCosets.Result w D I mul q root chain group quotient projection ∧
  ConstructionGermDetectors.Representatives group quotient reps ∧
  ConstructionGermDetectors.Nonidentity w D chain quotient reps N ∧
  Cartesian N w X ∧ ConstructionGermDetectors.Detectors D I chain X reps det ∧
  ConstructionGermDetectorSites.Covers w group det J ∧ Small J w ∧ (Project.FirstOrderSemantics.reduct M).MemberSubset J I ∧
  ConstructionGermSeparation.Separation w D chain group N det ∧
  ForcingWithTopCarrier.Empty zero ∧ (Project.FirstOrderSemantics.reduct M).SuccessorOf hi zero ∧
  (Project.FirstOrderSemantics.reduct M).SuccessorOf bits hi ∧ Cartesian I kappa coords ∧ Cartesian coords bits S ∧
  ConstructionGermPatternOrder.Covers w N bits kappa O ∧
  (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) order O ∧
  ConstructionGermConditionSelector.Selector w D chain group quotient N kappa coords bits zero hi det order S Psel f ∧ Dense w S f

theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain : M.Carrier .set}
    (hctx : ConstructionSaturationIterationCases.Context hM w Q values top w mul unit mark H C zero one u K mu B)
    (hrec : ConstructionSaturationIteration.Recursive hM w Q values top w mul unit mark H C zero one K mu B B history)
    (hindex : ConstructionSaturationIndex.Data hM w mu kappa B)
    (hf : ConstructionTowerTransitions.Matrix B history zero P outerF)
    (hr : Row history kappa V GV e markV HV CV terminalLegs baseV kappa)
    (hX : ConstructionComponentCarrier.Carrier V labels GV q vertices)
    (hC : ConstructionComponentCofinal.Chain w V labels GV q zero root vertices chain)
    (hq : Injection V labels q) :
    ∃ group quotient projection reps N X det J hi bits coords S O order Psel f,
      Result hM w V labels GV q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f := by
  obtain ⟨group,quotient,projection,hGerm⟩ := ConstructionCountableGerms.construction hM hOrder hChoice hctx hrec hindex hf hr hX hC hq
  have hctxCopy := hctx
  obtain ⟨hw,_,_,_,_,_,_,hz,hzw,_⟩ := hctxCopy
  have hv := (ConstructionSaturationIterationValidity.recursive_valid_small hM hOrder hChoice hctx hrec (fun _ h => h)).1
  have hV := (hv.2.1 kappa hindex.2.2.2.1.predecessor_mem V GV e markV HV CV terminalLegs baseV hr).1
  obtain ⟨reps,N,X,det,J,hReps,hN,hProd,hDet,_,_,hSmall,hJI,hSites⟩ :=
    ConstructionGermDetectorSites.construction hM hChoice hw hzw hC hGerm.1 hGerm.2.2.1 hGerm.2.2.2.2.1
  have hNX : Cartesian N w X := hProd
  have hSep : ConstructionGermSeparation.Separation w V chain group N det := by
    intro g h c d
    exact ConstructionGermSeparation.detector_separates hM hw hV.1 hV.2.2.1 hq hC hGerm.1 hGerm.2.2.1 hReps hN hDet hProd
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨hi,hhi⟩ := KP.exists_successor (ZF.modelsKP hZF) zero
  obtain ⟨bits,hbits⟩ := KP.exists_successor (ZF.modelsKP hZF) hi
  obtain ⟨coords,hCoords⟩ := ForcingCohenCoordinates.exists_cartesian hM labels kappa
  obtain ⟨S,hS⟩ := ForcingCohenCoordinates.exists_cartesian hM coords bits
  have hNonempty := quotient_nonempty hM hC hq hGerm.1 hGerm.2.2.1
  obtain ⟨O,order,Psel,f,hCover,hOrder',hSelector⟩ := ConstructionGermConditionSelector.construction
    (D := V) (chain := chain) (H := group) (N := N) (B := bits) (C := coords) (lo := zero) (hi := hi) (det := det) (S := S) hM hChoice hw hindex.1.1 hNonempty
  refine ⟨group,quotient,projection,reps,N,X,det,J,hi,bits,coords,S,O,order,Psel,f,
    hGerm,hReps,hN,hNX,hDet,hSites,hSmall,hJI,hSep,hz,hhi,hbits,hCoords,hS,hCover,hOrder',hSelector,?_⟩
  intro p hp
  obtain ⟨r,hr',hpr,hGood⟩ := ConstructionGermGoodDense.good_dense hM hChoice hw hindex.1 hindex.2.1 hC hGerm.1 hGerm.2.2.1
    hDet hSep hNX hSites hSmall hJI hCoords hS hz hhi hbits hp
  obtain ⟨c,hc⟩ := hSelector.2.1.1.2 r ((hSelector.1 r).mpr ⟨hr',hGood⟩)
  exact ⟨r,c,hr',hpr,hc.1⟩

def resultFormula {m : Nat} (w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionGermCosets.resultFormula w D I mul q root chain group quotient projection) (.conj (ConstructionGermDetectors.representatives group quotient reps) (.conj (ConstructionGermDetectors.nonidentity w D chain quotient reps N) (.conj (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian N w X)) (.conj (ConstructionGermDetectors.detectors D I chain X reps det) (.conj (ConstructionGermDetectorSites.coversFormula w group det J) (.conj (ProjectSyntax.encode id (ForcingSupportSize.small J w)) (.conj (Project.Formula.subset (.bound J) (.bound I)) (.conj (ConstructionGermSeparation.separation w D chain group N det) (.conj (Project.Formula.isEmpty (.bound zero)) (.conj (Project.Formula.isSuccessor (.bound hi) (.bound zero)) (.conj (Project.Formula.isSuccessor (.bound bits) (.bound hi)) (.conj (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I kappa coords)) (.conj (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian coords bits S)) (.conj (ConstructionGermPatternOrder.covers w N bits kappa O) (.conj (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound O)) (.conj (ConstructionGermConditionSelector.selector w D chain group quotient N kappa coords bits zero hi det order S Psel f) (dense w S f))))))))))))))))))

theorem resultFormula_freeClosed {m : Nat} (w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f : Fin m) :
    (resultFormula w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f).FreeClosed := by
  simp -implicitDefEqProofs [resultFormula,Definitional.Formula.FreeClosed,ConstructionGermCosets.resultFormula_freeClosed,ConstructionGermDetectors.representatives_freeClosed,ConstructionGermDetectors.nonidentity_freeClosed,ProjectSyntax.freeClosed,ConstructionGermDetectors.detectors_freeClosed,ConstructionGermDetectorSites.coversFormula_freeClosed,Project.Formula.subset,ConstructionGermSeparation.separation_freeClosed,Project.Formula.isEmpty,Project.Formula.isSuccessor,ConstructionGermPatternOrder.covers_freeClosed,ConstructionGermConditionSelector.selector_freeClosed,dense_freeClosed]

theorem resultFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f : Fin m) :
    Project.Formula.satisfies env (resultFormula w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f) ↔ Result hM (env.bound w) (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound root) (env.bound chain) (env.bound kappa) (env.bound zero) (env.bound group) (env.bound quotient) (env.bound projection) (env.bound reps) (env.bound N) (env.bound X) (env.bound det) (env.bound J) (env.bound hi) (env.bound bits) (env.bound coords) (env.bound S) (env.bound O) (env.bound order) (env.bound Psel) (env.bound f) := by
  simp only [resultFormula,Result,Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,ConstructionGermCosets.resultFormula_semantics hM,ConstructionGermDetectors.representatives_semantics hM,ConstructionGermDetectors.nonidentity_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingCohenCoordinates.cartesian_semantics (M := M),ConstructionGermDetectors.detectors_semantics hM,ConstructionGermDetectorSites.coversFormula_semantics hM,ForcingSupportSize.small_semantics (M := M),Project.Formula.satisfies_subset_iff,ConstructionGermSeparation.separation_semantics hM,Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_isSuccessor_iff,ConstructionGermPatternOrder.covers_semantics hM,Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),ConstructionGermConditionSelector.selector_semantics hM,dense_semantics hM]
  rfl

/-- Source OrbitAssignments.selected_exists, using actual membership in the full
quotient. This is existential elimination, not a representative choice function. -/
theorem selected_exists (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f p : M.Carrier .set}
    (hR : Result hM w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f) (hp : Condition S w p)
    (hGood : ConstructionGermGoodDense.Good w D chain group quotient N kappa coords bits zero hi det p) :
    ∃ g c, (Project.FirstOrderSemantics.reduct M).mem g group ∧ ConstructionGermCosets.Class w D chain group g c ∧
      ConstructionGermSelected.Selected w D chain group quotient N kappa coords bits zero hi det order p c := by
  obtain ⟨hGerm,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hSelector,_⟩ := hR
  obtain ⟨c,hc,_⟩ := hSelector.2.1.1.2 p ((hSelector.1 p).mpr ⟨hp,hGood⟩)
  obtain ⟨g,hg,hClass⟩ := (hGerm.2.2.1 c).mp (hSelector.2.1.2 p c hc)
  exact ⟨g,c,hg,hClass,((hSelector.2.2 p c).mp hc).2⟩

/-- Exact Good-density consumer for the fixed concrete output, without a new
countability or regularity hypothesis. -/
theorem good_dense (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f p : M.Carrier .set}
    (hR : Result hM w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f) (hp : Condition S w p) :
    ∃ r, Condition S w r ∧ (Project.FirstOrderSemantics.reduct M).MemberSubset p r ∧
      ConstructionGermGoodDense.Good w D chain group quotient N kappa coords bits zero hi det r := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hSelector,hDense⟩ := hR
  obtain ⟨r,c,hr,hpr,hc⟩ := hDense p hp
  exact ⟨r,hr,hpr,((hSelector.2.2 r c).mp hc).2.1⟩

/-- Source component_selected_covariant, constructing BOTH the moved condition
and the actual left-action graph, and returning an edge of the SAME selector. -/
theorem permutation (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f unit vertices pi p c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul unit)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hq : Injection D I q)
    (hChain : ConstructionComponentCofinal.Chain w D I mul q zero root vertices chain)
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal kappa)
    (hR : Result hM w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f)
    (hpi : (Project.FirstOrderSemantics.reduct M).mem pi group)
    (hpc : PureKuratowski.PairMember M p c f) :
    ∃ r act e, Condition S w r ∧ ConstructionCohenCompatibility.Moved pi p r ∧
      ConstructionGermLeftAction.Action w D I chain group quotient pi act ∧
      PureKuratowski.PairMember M c e act ∧ PureKuratowski.PairMember M r e f := by
  obtain ⟨hGerm,_,_,hNX,hDet,_,_,_,_,_,hhi,hbits,hCoords,hS,hCover,hOrder,hSelector,_⟩ := hR
  obtain ⟨hp,hSelected⟩ := (hSelector.2.2 p c).mp hpc
  obtain ⟨_,_,r,_,_,_,_,hr,_,hMove⟩ := ConstructionCohenCompatibility.exists_moved hM hCoords hS ((hGerm.1 pi).mp hpi).1 hp
  obtain ⟨act,hAct⟩ := ConstructionGermLeftAction.construction hM hw hm hJ hq hChain hGerm.1 hGerm.2.2.1 hpi
  obtain ⟨e,hce,_⟩ := hAct.1.1.1.2 c (ConstructionGermSelected.selected_mem hSelected)
  have hSelectedR := ConstructionGermSelected.selected_permute hM hw hm hJ hq hChain hGerm.1 hGerm.2.2.1 hDet hNX hCoords hK
    hCover hOrder ((hbits zero).mpr (Or.inl hhi.predecessor_mem)) hbits.predecessor_mem hpi hMove hAct hSelected hce
  exact ⟨r,act,e,hr,hMove,hAct,hce,(hSelector.2.2 r e).mpr ⟨hr,hSelectedR⟩⟩

def constructionSentence {m : Nat} (w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionSaturationIterationCases.context w Q values top w mul unit mark H C zero one u K mu B) (.imp (ConstructionSaturationIteration.recursive w Q values top w mul unit mark H C zero one K mu B B history) (.imp (ConstructionSaturationIndex.data w mu kappa B) (.imp (ConstructionTowerTransitions.matrix B history zero P outerF) (.imp (ConstructionTowerHistory.row history kappa V GV e markV HV CV terminalLegs baseV kappa) (.imp (ConstructionComponentCarrier.carrier V labels GV q vertices) (.imp (ConstructionComponentCofinal.chain w V labels GV q zero root vertices chain) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q V labels)) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (resultFormula w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ labels.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ root.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ chain.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1 0)))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,resultFormula_freeClosed,
      ConstructionSaturationIterationCases.context_freeClosed,
      ConstructionSaturationIteration.recursive_freeClosed,
      ConstructionSaturationIndex.data_freeClosed,
      ConstructionTowerTransitions.matrix_freeClosed,
      ConstructionTowerHistory.row_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed]

theorem construction_models {m : Nat} (w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.injection_semantics (M := M),resultFormula_semantics hM,
    ConstructionSaturationIterationCases.context_semantics hM,
    ConstructionSaturationIteration.recursive_semantics hM,
    ConstructionSaturationIndex.data_semantics hM,
    ConstructionTowerTransitions.matrix_semantics hM,
    ConstructionTowerHistory.row_semantics hM,
    ConstructionComponentCarrier.carrier_semantics hM,
    ConstructionComponentCofinal.chain_semantics hM]
  exact construction hM hOrder hChoice

def representativeSentence {m : Nat} (w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f p : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (resultFormula w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f) (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S w p)) (.imp (ConstructionGermGoodDense.good w D chain group quotient N kappa coords bits zero hi det p) (.existsE (.existsE (.conj (.mem (.bound 1) (.bound group.succ.succ)) (.conj (ConstructionGermCosets.eqClass w.succ.succ D.succ.succ chain.succ.succ group.succ.succ 1 0) (ConstructionGermSelected.selected w.succ.succ D.succ.succ chain.succ.succ group.succ.succ quotient.succ.succ N.succ.succ kappa.succ.succ coords.succ.succ bits.succ.succ zero.succ.succ hi.succ.succ det.succ.succ order.succ.succ p.succ.succ 0))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,resultFormula_freeClosed,ProjectSyntax.freeClosed,ConstructionGermGoodDense.good_freeClosed,ConstructionGermCosets.eqClass_freeClosed,ConstructionGermSelected.selected_freeClosed]

theorem representative_models {m : Nat} (w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f p : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (representativeSentence w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (representativeSentence w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f p)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Term.eval_bound,Project.Formula.satisfies_imp_iff,resultFormula_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingCohenConditions.condition_semantics (M := M),ConstructionGermGoodDense.good_semantics hM,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,ConstructionGermCosets.eqClass_semantics hM,ConstructionGermSelected.selected_semantics hM]
  exact selected_exists hM

theorem representative_kernel_certificate {m : Nat} (w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f p : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (representativeSentence w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f p)) :=
  ModelTransfer.derives (fun _ hM => representative_models w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f p hM)

def permutationSentence {m : Nat} (w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f unit vertices pi p c : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul unit)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q D I)) (.imp (ConstructionComponentCofinal.chain w D I mul q zero root vertices chain) (.imp (Project.Formula.isOrdinal (.bound kappa)) (.imp (resultFormula w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f) (.imp (.mem (.bound pi) (.bound group)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge f p c)) (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ.succ.succ w.succ.succ.succ 2)) (.conj (ConstructionCohenCompatibility.moved pi.succ.succ.succ p.succ.succ.succ 2) (.conj (ConstructionGermLeftAction.action w.succ.succ.succ D.succ.succ.succ I.succ.succ.succ chain.succ.succ.succ group.succ.succ.succ quotient.succ.succ.succ pi.succ.succ.succ 1) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 1 c.succ.succ.succ 0)) (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ 2 0))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,ProjectSyntax.freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionComponentCofinal.chain_freeClosed,Project.Formula.isOrdinal,resultFormula_freeClosed,ConstructionCohenCompatibility.moved_freeClosed,ConstructionGermLeftAction.action_freeClosed]

theorem permutation_models {m : Nat} (w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f unit vertices pi p c : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (permutationSentence w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f unit vertices pi p c)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (permutationSentence w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f unit vertices pi p c)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Term.eval_bound,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ForcingSupportSize.injection_semantics (M := M),ConstructionComponentCofinal.chain_semantics hM,Project.Formula.satisfies_isOrdinal_iff,resultFormula_semantics hM,Project.Formula.satisfies_mem_iff,KuratowskiZF.source_edge,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,ForcingCohenConditions.condition_semantics (M := M),ConstructionCohenCompatibility.moved_semantics hM,ConstructionGermLeftAction.action_semantics hM]
  exact permutation hM

theorem permutation_kernel_certificate {m : Nat} (w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f unit vertices pi p c : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (permutationSentence w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f unit vertices pi p c)) :=
  ModelTransfer.derives (fun _ hM => permutation_models w D I mul q root chain kappa zero group quotient projection reps N X det J hi bits coords S O order Psel f unit vertices pi p c hM)

theorem construction_kernel_certificate {m : Nat} (w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (constructionSentence w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain)).mp (construction_models w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain hL (ConstructionRoundSelection.l_order hM) hChoice)

end PPAC.Migration.ConstructionConcreteSelector
