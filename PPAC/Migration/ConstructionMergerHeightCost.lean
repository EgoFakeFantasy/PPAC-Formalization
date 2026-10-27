/- Pinned MergerCones.copiesHeightCost:351, complete SAME producer assembly.
Reuse actual coordinate/weight constructors and every already proved field.
Construct both literal weight graphs, all four bounds and the ACTUAL strict
missed-cost supremum; preserve the SAME parent Word/inclusion/profile/roots.
No supplied new weights/margins or new arithmetic/recursion/Choice backend. -/
import PPAC.Migration.ConstructionMergerUniformMargin

namespace PPAC.Migration.ConstructionMergerHeightCost
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts (Subset Cut CutCarrier)
open ConstructionCutAddition (SumCut)
open ConstructionProbeIntervals (Strict)
open ConstructionProbeLetters (Representatives)
open ConstructionMergerCopyCones (Reaches)
open ConstructionMergerFiniteWeights (HeightValue CostValue)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
open ConstructionProbeLetterIntervals (UniformMargins)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Full source copies HeightCost on the actual two function graphs. -/
def CopiesHeightCost (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R D L A top FH FC : M.Carrier .set) : Prop :=
  MapsTo L R FH ∧ MapsTo L R FC ∧ ConstructionCutWeights.RangeBound top FH ∧
    ConstructionProbeGateCap.Bounds top FC ∧ ∀ z t a b,
    PureKuratowski.PairMember M z a FH → PureKuratowski.PairMember M t b FH →
    Reaches D A z t → z ≠ t → ∃ cap total, Cut hM w Q cap ∧
      ConstructionMergerUniformMargin.Cap D L A FC z t cap ∧ SumCut hM w Q a cap total ∧
      Strict total b ∧ ConstructionMergerUniformMargin.MissedBound D L A FC z t cap

def copiesHeightCost {m : Nat} (w Q R D L A top FH FC : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo FH L R)) (.conj (ProjectSyntax.encode
  id (Source.SetLanguage.mapsTo FC L R)) (.conj (ConstructionCutWeights.rangeBound top FH) (.conj
  (ConstructionProbeGateCap.bounds top FC) (.forallE (.forallE (.forallE (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge (FH).succ.succ.succ.succ 3 1)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge (FH).succ.succ.succ.succ 2 0)) (.imp
  (ConstructionMergerCopyCones.reaches (D).succ.succ.succ.succ (A).succ.succ.succ.succ 3 2) (.imp
  (.neg (Project.Formula.extensionalEq (.bound 3) (.bound 2))) (.existsE (.existsE (.conj
  (ConstructionRealCuts.cut ((w).succ.succ.succ.succ).succ.succ ((Q).succ.succ.succ.succ).succ.succ
  1) (.conj (.existsE (.conj (.forallE (.iff (.mem (.bound 0) (.bound 1))
  (ConstructionMergerUniformMargin.costMember ((((D).succ.succ.succ.succ).succ.succ).succ).succ
  ((((L).succ.succ.succ.succ).succ.succ).succ).succ
  ((((A).succ.succ.succ.succ).succ.succ).succ).succ
  ((((FC).succ.succ.succ.succ).succ.succ).succ).succ 7
  6 0))) (ConstructionRealCuts.supremum 0 2))) (.conj
  (ConstructionCutAddition.sumCut ((w).succ.succ.succ.succ).succ.succ
  ((Q).succ.succ.succ.succ).succ.succ 3 1 0) (.conj (.conj (Project.Formula.subset
  (.bound 0) (.bound 2)) (.neg (Project.Formula.subset (.bound 2) (.bound
  0)))) (.forallE (.forallE (.imp (.mem (.bound 1) (.bound
  (((L).succ.succ.succ.succ).succ.succ).succ.succ)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge (((FC).succ.succ.succ.succ).succ.succ).succ.succ 1 0)) (.imp
  (ConstructionMergerCopyCones.reaches (((D).succ.succ.succ.succ).succ.succ).succ.succ
  (((A).succ.succ.succ.succ).succ.succ).succ.succ 1 6) (.imp (.neg
  (ConstructionMergerCopyCones.reaches (((D).succ.succ.succ.succ).succ.succ).succ.succ
  (((A).succ.succ.succ.succ).succ.succ).succ.succ 1 7))
  (Project.Formula.subset (.bound 0) (.bound 3))))))))))))))))))))))))))

theorem copiesHeightCost_freeClosed {m : Nat} (w Q R D L A top FH FC : Fin m) :
    (copiesHeightCost w Q R D L A top FH FC).FreeClosed := by
  simp -implicitDefEqProofs [copiesHeightCost,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.extensionalEq,ConstructionCutWeights.rangeBound_freeClosed,
    ConstructionProbeGateCap.bounds_freeClosed,ConstructionMergerCopyCones.reaches_freeClosed,
    ConstructionRealCuts.cut_freeClosed,ConstructionRealCuts.supremum_freeClosed,
    ConstructionMergerUniformMargin.costMember_freeClosed,ConstructionCutAddition.sumCut_freeClosed]

theorem copiesHeightCost_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R D L A top FH FC : Fin m) :
    Project.Formula.satisfies env (copiesHeightCost w Q R D L A top FH FC) ↔
      CopiesHeightCost hM (env.bound w) (env.bound Q) (env.bound R) (env.bound D) (env.bound L)
        (env.bound A) (env.bound top) (env.bound FH) (env.bound FC) := by
  simp only [copiesHeightCost,CopiesHeightCost,ConstructionMergerUniformMargin.Cap,
    ConstructionMergerUniformMargin.Family,ConstructionMergerUniformMargin.MissedBound,
    ConstructionProbeIntervals.Strict,ConstructionRealCuts.Subset,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingSupportSize.mapsTo_semantics (M := M),ConstructionCutWeights.rangeBound_semantics hM,
    ConstructionProbeGateCap.bounds_semantics hM,ConstructionMergerCopyCones.reaches_semantics hM,
    ConstructionRealCuts.cut_semantics hM,ConstructionRealCuts.supremum_semantics,
    ConstructionMergerUniformMargin.costMember_semantics hM,ConstructionCutAddition.sumCut_semantics hM]
  rfl

theorem exists_weights (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q n D mul e P C L projection A R Height Cost top J CH CC zero one u : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : CutCarrier hM w Q R)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hnp : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i n)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : ConstructionRealCuts.Principal hM w Q u top)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hc : ForcingDiagramPoset.Conical D mul e)
    (hC : Representatives n D C) (hL : ConstructionMergerCopies.Copies n D mul P C L)
    (hp : MapsTo C L projection) (hProj : ConstructionMergerCopies.Projection n D mul P C projection)
    (hEq : ConstructionMergerCopies.EqualityLaw n D mul P projection)
    (hCopy : ConstructionMergerAction.CopyLaw D mul projection A)
    (hJ : Representatives n L J) (hCH : MapsTo J R CH) (hCC : MapsTo J R CC)
    (hHeight : MapsTo D R Height) (hHB : ConstructionCutWeights.RangeBound top Height)
    (hCost : MapsTo D R Cost) (hCB : ConstructionProbeGateCap.Bounds top Cost)
    (hUniform : ConstructionProbeLetterIntervals.UniformMargins hM w Q D mul Height Cost)
    (hCoordH : ConstructionMergerCoordinates.Graph n L projection Height zero CH)
    (hCoordC : ConstructionMergerCoordinates.Graph n L projection Cost top CC) :
    ∃ unitHeight Ka add Km mulCut Id two cap FH FC, (
      PureKuratowski.PairMember M e unitHeight Height ∧
      Representatives R R Ka ∧ MapsTo Ka R add ∧ ConstructionCutArithmetic.Graph hM w Q R add ∧
      Representatives R R Km ∧ MapsTo Km R mulCut ∧ ConstructionCutProduct.Graph hM w Q R mulCut ∧
      MapsTo R R Id ∧ ForcingConditionGraphs.IdentityGraph R Id ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf two one ∧ (Project.FirstOrderSemantics.reduct M).mem two w ∧
      (Project.FirstOrderSemantics.reduct M).mem cap R ∧ ConstructionCutDivision.Value hM w Q two unitHeight cap ∧
      MapsTo L R FH ∧ (∀ z a, PureKuratowski.PairMember M z a FH ↔
        (Project.FirstOrderSemantics.reduct M).mem z L ∧ HeightValue hM w Q n R add Id zero CH z a) ∧
      MapsTo L R FC ∧ (∀ z a, PureKuratowski.PairMember M z a FC ↔
        (Project.FirstOrderSemantics.reduct M).mem z L ∧ CostValue hM w Q n R mulCut Id top cap CC z a) ∧
      (∀ a, (Project.FirstOrderSemantics.reduct M).mem a R → Product mulCut a top a) ∧
      (∀ a, (Project.FirstOrderSemantics.reduct M).mem a R → Product add zero a a)) ∧
      CopiesHeightCost hM w Q R D L A top FH FC := by
  obtain ⟨unitHeight,Ka,add,Km,mulCut,Id,two,cap,FH,FC,hWeightFields⟩ :=
    ConstructionMergerFiniteWeights.exists_system hM hw hQ hn hnp hR hJ hCH hCC hz hu hone hunit hHeight hm.1.1
  have hRetained := hWeightFields
  obtain ⟨hEdge,hKa,hadd,hAdd,hKm,hmul,hMul,hId,hIdGraph,htwo,htwow,hcapR,hCap,hFH,hGraphH,hFC,hGraphC,hMulUnit,hAddZero⟩ := hWeightFields
  have hEst := ConstructionMergerWeightEstimates.copies_estimates hM hw hz hzw hQ hR hn hnp hu hone hunit hIdGraph hAdd hMul hC hL hp hProj hEq hHeight hHB hCB hCoordH hCoordC hJ hCC hEdge htwo htwow hCap
  have hUpper := ConstructionMergerHeightUpper.copiesHeight_lt_one hM hw hz hzw hQ hR hu hone hunit hn hnp hKa hadd hId hIdGraph hAdd hHB hCB hCoordH hCoordC hEdge
  refine ⟨unitHeight,Ka,add,Km,mulCut,Id,two,cap,FH,FC,hRetained,hFH,hFC,?_,?_,?_⟩
  · intro z a hza
    obtain ⟨hzL,hValue⟩ := (hGraphH z a).mp hza
    exact ⟨(hEst z a hzL).1 hValue,hUpper z a hValue⟩
  · intro z a hza
    obtain ⟨hzL,hValue⟩ := (hGraphC z a).mp hza
    exact ⟨((hEst z a hzL).2 hValue).1,
      (ConstructionMergerHeightComparison.copiesCost_unit_bound hM hw hQ hR hu.1 hone hn hnp htwo htwow hHeight hHB hEdge hCap hValue).1⟩
  · intro z t a b hza htb hReach hne
    obtain ⟨hzL,ha⟩ := (hGraphH z a).mp hza
    obtain ⟨htL,hb⟩ := (hGraphH t b).mp htb
    have hMargin := ConstructionMergerUniformMargin.copies_uniform_margin hM hw hz hzw hQ hR hIdGraph hAdd hMul hn hnp hu.1 hone hu hunit htwo htwow hm hc hC hL hp hProj hEq hCopy hJ hCH hCC hHeight hHB hCost hCB hUniform hCoordH hCoordC hEdge hCap hGraphC hzL htL ha hb hReach hne
    exact ConstructionMergerUniformMargin.canonical_uniform hM hw hQ hR hFC ((hR a).mp (hFH.2 z a hza)) hMargin

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    {w n D mul e P zero Q R Height Cost top one u : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hc : ForcingDiagramPoset.Conical D mul e)
    (hJoins : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hP : ConstructionMergerRelations.Prescription n D P) (hValid : ConstructionMergerRelations.Valid n D mul P)
    (hQ : ConstructionFractionOrder.Carrier w Q)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hnp : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i n)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hunit : ConstructionRealCuts.Principal hM w Q u top)
    (hR : CutCarrier hM w Q R) (hHeight : MapsTo D R Height)
    (hHB : ConstructionCutWeights.RangeBound top Height) (hCost : MapsTo D R Cost)
    (hCB : ConstructionProbeGateCap.Bounds top Cost)
    (hUniform : UniformMargins hM w Q D mul Height Cost) :
    ∃ C L projection K A W I T B H unit, (Representatives n D C ∧ MapsTo C L projection ∧
      ConstructionMergerCopies.Copies n D mul P C L ∧ ConstructionMergerCopies.Projection n D mul P C projection ∧
      ConstructionMergerCopies.EqualityLaw n D mul P projection ∧ Representatives L D K ∧ MapsTo K L A ∧
      ConstructionMergerAction.ActionTable D mul projection A ∧ ConstructionMergerAction.RightFreeAction mul e L A ∧
      ConstructionMergerAction.CopyLaw D mul projection A ∧ ConstructionProbeRaw.Carrier w D L W ∧
      Representatives W D I ∧ MapsTo I W T ∧ ConstructionMergerWordAction.ActionTable w D L zero mul A T ∧
      ConstructionMergerAction.RightFreeAction mul e W T ∧ Representatives W W B ∧ MapsTo B W H ∧ ConstructionMergerWordProduct.Laws w D L zero T H) ∧
      ConstructionProbeRaw.Old zero D e unit ∧ LeftCancelMonoid W H unit ∧ ForcingDiagramPoset.Conical W H unit ∧ ConstructionMergerCopyCones.HasConeJoins D L A ∧ ConstructionProbeSharedIntersections.ConditionalJoins W H ∧ ∃ O, ConstructionProbeOldEmbedding.OldGraph zero D O ∧ ConstructionProbeConservative.Conservative D W mul H O ∧
      ConstructionProbeLiftHom.PreservesProducts mul H O ∧ ConstructionPersistentProfiles.HasOldGates D W mul H O ∧ PureKuratowski.PairMember M e unit O ∧
      (∀ a b d p node, ConstructionPersistentProfiles.ProbeProfile w D mul a b d p node →
        ∃ mapped fa fb fd fp, ConstructionProbeMappedPath.NodeMap node O mapped ∧
          PureKuratowski.PairMember M a fa O ∧ PureKuratowski.PairMember M b fb O ∧
          PureKuratowski.PairMember M d fd O ∧ PureKuratowski.PairMember M p fp O ∧
          ConstructionPersistentProfiles.ProbeProfile w W H fa fb fd fp mapped) ∧ ∃ F, MapsTo n W F ∧ ConstructionMergerRoots.RootGraph w D L e projection unit F ∧ ConstructionMergerRoots.RootLaws w D L n mul P projection unit H O F ∧ ∃ J CH CC, Representatives n L J ∧ MapsTo J R CH ∧ MapsTo J R CC ∧
      ConstructionMergerCoordinates.Graph n L projection Height zero CH ∧ ConstructionMergerCoordinates.Graph n L projection Cost top CC ∧
      ConstructionMergerCoordinateLaws.Laws n D L A projection Height Cost zero top CH CC ∧
      ∃ unitHeight Ka add Km mulCut Id two cap FH FC, (
      PureKuratowski.PairMember M e unitHeight Height ∧
      Representatives R R Ka ∧ MapsTo Ka R add ∧ ConstructionCutArithmetic.Graph hM w Q R add ∧
      Representatives R R Km ∧ MapsTo Km R mulCut ∧ ConstructionCutProduct.Graph hM w Q R mulCut ∧
      MapsTo R R Id ∧ ForcingConditionGraphs.IdentityGraph R Id ∧
      (Project.FirstOrderSemantics.reduct M).SuccessorOf two one ∧ (Project.FirstOrderSemantics.reduct M).mem two w ∧
      (Project.FirstOrderSemantics.reduct M).mem cap R ∧ ConstructionCutDivision.Value hM w Q two unitHeight cap ∧
      MapsTo L R FH ∧ (∀ z a, PureKuratowski.PairMember M z a FH ↔
        (Project.FirstOrderSemantics.reduct M).mem z L ∧ HeightValue hM w Q n R add Id zero CH z a) ∧
      MapsTo L R FC ∧ (∀ z a, PureKuratowski.PairMember M z a FC ↔
        (Project.FirstOrderSemantics.reduct M).mem z L ∧ CostValue hM w Q n R mulCut Id top cap CC z a) ∧
      (∀ a, (Project.FirstOrderSemantics.reduct M).mem a R → Product mulCut a top a) ∧
      (∀ a, (Project.FirstOrderSemantics.reduct M).mem a R → Product add zero a a)) ∧
      CopiesHeightCost hM w Q R D L A top FH FC := by
  have htop := (hR top).mpr (ConstructionRealCuts.principal_cut hM hw hQ
    ((hQ u).mpr ⟨one,one,hu⟩) hunit)
  obtain ⟨C,L,projection,K,A,W,I,T,B,H,unit,hParent,hUnit,hMonoid,hCon,hCone,hJoinsW,O,hO,hCons,hPres,hGates,hEdge,hProfiles,F,hF,hRoots,hRootLaws,J,CH,CC,hJ,hCH,hCC,hCoordH,hCoordC,hCoordLaws⟩ :=
    ConstructionMergerCoordinateLaws.exists_system hM hw hz hzw hm hc hJoins hP hValid hR hHeight hHB hCost hCB htop hUniform
  have hRetained := hParent
  obtain ⟨hC,hp,hL,hProjection,hEq,_,_,_,_,hCopy,_⟩ := hParent
  obtain ⟨unitHeight,Ka,add,Km,mulCut,Id,two,cap,FH,FC,hWeights,hHeightCost⟩ :=
    exists_weights hM hw hz hzw hQ hR hn hnp hu hone hunit hm hc hC hL hp hProjection hEq hCopy hJ hCH hCC hHeight hHB hCost hCB hUniform hCoordH hCoordC
  exact ⟨C,L,projection,K,A,W,I,T,B,H,unit,hRetained,hUnit,hMonoid,hCon,hCone,hJoinsW,O,hO,hCons,hPres,hGates,hEdge,hProfiles,F,hF,hRoots,hRootLaws,J,CH,CC,hJ,hCH,hCC,hCoordH,hCoordC,hCoordLaws,
    unitHeight,Ka,add,Km,mulCut,Id,two,cap,FH,FC,hWeights,hHeightCost⟩

end PPAC.Migration.ConstructionMergerHeightCost
