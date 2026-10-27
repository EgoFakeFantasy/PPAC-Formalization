/- Pinned CompleteRounds.RootSystem.map and Round.probe_independent/creates_merger.
Use existing Conservative.Intersections/Common and actual native composition.
The target cone quantifier covers the entire new carrier. -/
import PPAC.Migration.ConstructionProbeIndependent
import PPAC.Migration.ConstructionMergerRootSystem

namespace PPAC.Migration.ConstructionConeTransport
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeConservative (Conservative)
open ConstructionProbeLiftHom (PreservesProducts)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionProbeCones (JoinProperty)
open ConstructionProbeIndependent (Independent)
open ConstructionMergerRootSystem (RootSystem)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Transport the SAME probe and old inclusion along an actual conservative leg. -/
theorem probe_map {D mul a ex W G O gen N GN f ON fgen : M.Carrier .set}
    (hf : Conservative W N G GN f) (hO : NodeMap O f ON)
    (hgen : PureKuratowski.PairMember M gen fgen f)
    (hInd : Independent D mul a ex W G O gen) :
    Independent D mul a ex N GN ON fgen := by
  intro x fx fex z hx hfx hfex hz hxex hxa
  obtain ⟨ox,hox,hofx⟩ := (hO x fx).mp hfx
  obtain ⟨oex,hoex,hofex⟩ := (hO ex fex).mp hfex
  have hJoin : JoinProperty W G ox gen oex :=
    fun q hq => hInd x ox oex q hx hox hoex hq hxex hxa
  exact hf.2.2.1 ox gen oex fx fgen fex hofx hgen hofex hJoin z hz

/-- Original RootSystem.map, with original P fixed and its factor inclusion
composed literally. Both absence and full intersections persist to ALL N. -/
theorem merger_map {n D P W G unit O roots N GN f ON rootsN : M.Carrier .set}
    (hm : LeftCancelMonoid W G unit) (hO : MapsTo D W O)
    (hf : Conservative W N G GN f) (hPres : PreservesProducts G GN f)
    (hOC : NodeMap O f ON) (hRC : NodeMap roots f rootsN)
    (hRoots : RootSystem n P W G O roots) : RootSystem n P N GN ON rootsN := by
  intro i j riN rjN hi hj hij hriN hrjN
  obtain ⟨ri,hri,hfRi⟩ := (hRC i riN).mp hriN
  obtain ⟨rj,hrj,hfRj⟩ := (hRC j rjN).mp hrjN
  have hOld := hRoots i j ri rj hi hj hij hri hrj
  constructor
  · intro hNone z hz hBoth
    obtain ⟨q,hq,hiQ,hjQ⟩ := hf.2.2.2 ri rj riN rjN hfRi hfRj ⟨z,hz,hBoth.1,hBoth.2⟩
    exact hOld.1 hNone q hq ⟨hiQ,hjQ⟩
  · intro a b hStart
    obtain ⟨oa,ob,q,hOa,hOb,hProdI,hProdJ,hJoin⟩ := hOld.2 a b hStart
    obtain ⟨fa,hfa,_⟩ := hf.1.1.1.2 oa (hO.2 a oa hOa)
    obtain ⟨fb,hfb,_⟩ := hf.1.1.1.2 ob (hO.2 b ob hOb)
    have hRiW := ForcingConditionGraphs.function_input hf.1.1.1 hfRi
    have hqW := ConstructionMergerRelations.product_range hm hRiW (hO.2 a oa hOa) hProdI
    obtain ⟨fq,hfq,_⟩ := hf.1.1.1.2 q hqW
    exact ⟨fa,fb,fq,(hOC a fa).mpr ⟨oa,hOa,hfa⟩,(hOC b fb).mpr ⟨ob,hOb,hfb⟩,
      hPres ri oa q riN fa fq hProdI hfRi hfa hfq,
      hPres rj ob q rjN fb fq hProdJ hfRj hfb hfq,
      hf.2.2.1 ri rj q riN rjN fq hfRi hfRj hfq hJoin⟩

/-- Actually construct the composed inclusion and image of the SAME probe. -/
theorem exists_probe_map (hM : FirstOrder.Theory.Models M nativeZF)
    {D mul a ex W G O gen N GN f : M.Carrier .set}
    (hO : MapsTo D W O) (hf : Conservative W N G GN f)
    (hgen : (Project.FirstOrderSemantics.reduct M).mem gen W)
    (hInd : Independent D mul a ex W G O gen) :
    ∃ ON fgen, MapsTo D N ON ∧ NodeMap O f ON ∧
      PureKuratowski.PairMember M gen fgen f ∧ Independent D mul a ex N GN ON fgen := by
  obtain ⟨ON,hON,hComp⟩ := ConstructionProbeMappedPath.exists_node_map hM hO hf.1.1
  obtain ⟨fgen,hfgen,_⟩ := hf.1.1.1.2 gen hgen
  exact ⟨ON,fgen,hON,hComp,hfgen,probe_map hf hComp hfgen hInd⟩

/-- Actually construct both composed graphs, without an image-family input. -/
theorem exists_merger_map (hM : FirstOrder.Theory.Models M nativeZF)
    {n D P W G unit O roots N GN f : M.Carrier .set}
    (hm : LeftCancelMonoid W G unit) (hO : MapsTo D W O) (hR : MapsTo n W roots)
    (hf : Conservative W N G GN f) (hPres : PreservesProducts G GN f)
    (hRoots : RootSystem n P W G O roots) :
    ∃ ON rootsN, MapsTo D N ON ∧ MapsTo n N rootsN ∧ NodeMap O f ON ∧
      NodeMap roots f rootsN ∧ RootSystem n P N GN ON rootsN := by
  obtain ⟨ON,hON,hOC⟩ := ConstructionProbeMappedPath.exists_node_map hM hO hf.1.1
  obtain ⟨rootsN,hRN,hRC⟩ := ConstructionProbeMappedPath.exists_node_map hM hR hf.1.1
  exact ⟨ON,rootsN,hON,hRN,hOC,hRC,merger_map hm hO hf hPres hOC hRC hRoots⟩

/-- Reassociate the exact mapped prescription with its actual base inclusion.
This is the native encoding of the source (P.map f).map g = P.map (g*f). -/
theorem merger_pullback (hM : FirstOrder.Theory.Models M nativeZF)
    {n D P A f PA N GN O base roots : M.Carrier .set}
    (hP : ConstructionMergerRelations.Prescription n D P) (hf : MapsTo D A f)
    (hMap : ConstructionMergerPrescriptionMap.Graph P f PA) (hBase : NodeMap f O base)
    (hRoots : RootSystem n PA N GN O roots) : RootSystem n P N GN base roots := by
  have hMapped := ConstructionMergerPrescriptionMap.mapped hM hMap
  intro i j ri rj hi hj hij hri hrj
  have hR := hRoots i j ri rj hi hj hij hri hrj
  constructor
  · intro hNone
    apply hR.1
    rintro ⟨a,b,hS⟩
    obtain ⟨x,y,hxy,_,_⟩ := (hMapped i j a b).mp hS
    exact hNone ⟨x,y,hxy⟩
  · intro a b hStart
    have hSpec := hP.1 i j a b hStart
    obtain ⟨fa,hfa,_⟩ := hf.1.2 a hSpec.2.2.1
    obtain ⟨fb,hfb,_⟩ := hf.1.2 b hSpec.2.2.2
    have hStart' := (hMapped i j fa fb).mpr ⟨a,b,hStart,hfa,hfb⟩
    obtain ⟨oa,ob,q,hoa,hob,hI,hJ,hJoin⟩ := hR.2 fa fb hStart'
    exact ⟨oa,ob,q,(hBase a oa).mpr ⟨fa,hfa,hoa⟩,(hBase b ob).mpr ⟨fb,hfb,hob⟩,hI,hJ,hJoin⟩


/-- Consume the SAME selected Probe source and construct its actual images
along the later conservative leg; no supplied image or composed graph. -/
theorem probe_after (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one request N mulN eN markN f W G unit O gen a b node V GV leg : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid N mulN eN) (hc : ForcingDiagramPoset.Conical N mulN eN)
    (hmark : (Project.FirstOrderSemantics.reduct M).mem markN N)
    (hne : zero ≠ one) (hCode : ConstructionRequestSchedule.ProbeCode zero a b node request)
    (hSource : ConstructionRoundSource.Provenance hM w zero one request N mulN eN markN f W G unit O gen)
    (hO : MapsTo N W O) (hLeg : Conservative W V G GV leg) :
    ∃ ON genV, MapsTo N V ON ∧ NodeMap O leg ON ∧
      PureKuratowski.PairMember M gen genV leg ∧
      ConstructionProbeIndependent.Realized N mulN markN f V GV ON genV a b node := by
  rcases hSource with ⟨a',b',node',fa,fb,mapped,hCode',hfa,hfb,hMap,hProbe⟩ | ⟨n,P,PN,hCode',_⟩
  · obtain ⟨ea,eb,en⟩ := ConstructionRequestSchedule.probe_code_injective hCode hCode'
    subst a'; subst b'; subst node'
    have hKeep := hProbe
    obtain ⟨_,_,_,S,A,E,projection,KG,P,_,_,_,_,_,_,_,hP,_,hgen⟩ := hProbe
    obtain ⟨ON,hON,hOC⟩ := ConstructionProbeMappedPath.exists_node_map hM hO hLeg.1.1
    obtain ⟨genV,hGenV,_⟩ := hLeg.1.1.1.2 gen (hP.2 zero gen hgen)
    refine ⟨ON,genV,hON,hOC,hGenV,fa,fb,mapped,hfa,hfb,hMap,?_⟩
    intro ex hEx
    apply probe_map hLeg hOC hGenV
    exact fun x ox oex z hx hox hoex hzW hxex hxa =>
      ConstructionProbeIndependent.independent hM hw hz hzw hm hc hmark hKeep hx hEx hox hoex hzW hxex hxa
  · exact False.elim (ConstructionRequestSchedule.code_disjoint hne hCode hCode')

/-- Consume the SAME selected Merger, construct the two image graphs and the
actual base inclusion, then reassociate P.map f with that base. -/
theorem merger_after (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one request D N mulN eN markN f W G unit O roots n P V GV leg : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid N mulN eN) (hmW : LeftCancelMonoid W G unit)
    (hne : zero ≠ one) (hCode : ConstructionRequestSchedule.MergerCode one n P request)
    (hSource : ConstructionRoundSource.Provenance hM w zero one request N mulN eN markN f W G unit O roots)
    (hP : ConstructionMergerRelations.Prescription n D P) (hOrigin : MapsTo D N f)
    (hO : MapsTo N W O) (hR : MapsTo n W roots)
    (hLeg : Conservative W V G GV leg) (hPres : PreservesProducts G GV leg) :
    ∃ ON baseV rootsV, MapsTo N V ON ∧ MapsTo D V baseV ∧ MapsTo n V rootsV ∧
      NodeMap O leg ON ∧ NodeMap roots leg rootsV ∧ NodeMap f ON baseV ∧
      RootSystem n P V GV baseV rootsV := by
  obtain ⟨PN,hGraph,hRoot⟩ := ConstructionMergerRootSystem.of_provenance hM hw hz hzw hm hne hCode hSource
  obtain ⟨ON,rootsV,hON,hRV,hOC,hRC,hRootV⟩ := exists_merger_map hM hmW hO hR hLeg hPres hRoot
  obtain ⟨baseV,hBase,hBaseC⟩ := ConstructionProbeMappedPath.exists_node_map hM hOrigin hON
  exact ⟨ON,baseV,rootsV,hON,hBase,hRV,hOC,hRC,hBaseC,
    merger_pullback hM hP hOrigin hGraph hBaseC hRootV⟩


def probeAfterSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 20 (.imp (Project.Formula.isOmega (.bound (0 : Fin 20))) (.imp
    (Project.Formula.isEmpty (.bound (1 : Fin 20))) (.imp (.mem (.bound (1 : Fin 20)) (.bound (0 : Fin 20)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (4 : Fin 20) (5 : Fin 20) (6 : Fin
    20))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical (4 : Fin 20) (5 : Fin 20) (6 : Fin
    20))) (.imp (.mem (.bound (7 : Fin 20)) (.bound (4 : Fin 20))) (.imp (.neg
    (Project.Formula.extensionalEq (.bound (1 : Fin 20)) (.bound (2 : Fin 20)))) (.imp
    (ConstructionRequestSchedule.probeCode (1 : Fin 20) (14 : Fin 20) (15 : Fin 20) (16 : Fin 20) (3 : Fin
    20)) (.imp (ConstructionRoundSource.provenance (0 : Fin 20) (1 : Fin 20) (2 : Fin 20) (3 : Fin 20) (4 :
    Fin 20) (5 : Fin 20) (6 : Fin 20) (7 : Fin 20) (8 : Fin 20) (9 : Fin 20) (10 : Fin 20) (11 : Fin 20) (12
    : Fin 20) (13 : Fin 20)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (12 : Fin 20) (4 :
    Fin 20) (9 : Fin 20))) (.imp (ConstructionProbeConservativeSyntax.conservative (9 : Fin 20) (17 : Fin
    20) (10 : Fin 20) (18 : Fin 20) (19 : Fin 20)) (.existsE (.existsE (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (1 : Fin 22) (4 : Fin 20).succ.succ (17 : Fin 20).succ.succ)) (.conj
    (ConstructionProbeMappedPathSyntax.nodeMap (12 : Fin 20).succ.succ (19 : Fin 20).succ.succ (1 : Fin 22))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (19 : Fin 20).succ.succ (13 : Fin 20).succ.succ
    (0 : Fin 22))) (ConstructionProbeIndependent.realized (4 : Fin 20).succ.succ (5 : Fin 20).succ.succ (7 :
    Fin 20).succ.succ (8 : Fin 20).succ.succ (17 : Fin 20).succ.succ (18 : Fin 20).succ.succ (1 : Fin 22) (0
    : Fin 22) (14 : Fin 20).succ.succ (15 : Fin 20).succ.succ (16 : Fin 20).succ.succ))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isEmpty,Project.Formula.extensionalEq,
      ConstructionRoundSource.provenance_freeClosed,
      ConstructionProbeConservativeSyntax.conservative_freeClosed,ConstructionRequestSchedule.probeCode_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,ConstructionProbeIndependent.realized_freeClosed]

theorem probeAfter_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence probeAfterSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) probeAfterSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionRoundSource.provenance_semantics hM,
    ConstructionProbeConservativeSyntax.conservative_semantics hM,
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,ForcingDiagramPoset.conical_semantics (M := M),ConstructionRequestSchedule.probeCode_semantics hM,ConstructionProbeIndependent.realized_semantics hM]
  exact fun hw hz hzw hm hc hmark hne hCode hSource hO hLeg =>
    probe_after hM hw hz hzw hm hc hmark hne hCode hSource hO hLeg

theorem probeAfter_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence probeAfterSentence) := ModelTransfer.derives (fun _ hM => probeAfter_models hM)

def mergerAfterSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 20 (.imp (Project.Formula.isOmega (.bound (0 : Fin 20))) (.imp
    (Project.Formula.isEmpty (.bound (1 : Fin 20))) (.imp (.mem (.bound (1 : Fin 20)) (.bound (0 : Fin 20)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (5 : Fin 20) (6 : Fin 20) (7 : Fin
    20))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (10 : Fin 20) (11 : Fin 20)
    (12 : Fin 20))) (.imp (.neg (Project.Formula.extensionalEq (.bound (1 : Fin 20)) (.bound (2 : Fin 20))))
    (.imp (ConstructionRequestSchedule.mergerCode (2 : Fin 20) (15 : Fin 20) (16 : Fin 20) (3 : Fin 20))
    (.imp (ConstructionRoundSource.provenance (0 : Fin 20) (1 : Fin 20) (2 : Fin 20) (3 : Fin 20) (5 : Fin
    20) (6 : Fin 20) (7 : Fin 20) (8 : Fin 20) (9 : Fin 20) (10 : Fin 20) (11 : Fin 20) (12 : Fin 20) (13 :
    Fin 20) (14 : Fin 20)) (.imp (ConstructionMergerRelations.prescription (15 : Fin 20) (4 : Fin 20) (16 :
    Fin 20)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (9 : Fin 20) (4 : Fin 20) (5 : Fin
    20))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (13 : Fin 20) (5 : Fin 20) (10 : Fin
    20))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (14 : Fin 20) (15 : Fin 20) (10 : Fin
    20))) (.imp (ConstructionProbeConservativeSyntax.conservative (10 : Fin 20) (17 : Fin 20) (11 : Fin 20)
    (18 : Fin 20) (19 : Fin 20)) (.imp (ConstructionProbeLiftHomSyntax.preservesProducts (11 : Fin 20) (18 :
    Fin 20) (19 : Fin 20)) (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (2 : Fin 23) (5 : Fin 20).succ.succ.succ (17 : Fin 20).succ.succ.succ))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (1 : Fin 23) (4 : Fin 20).succ.succ.succ (17
    : Fin 20).succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 23) (15 :
    Fin 20).succ.succ.succ (17 : Fin 20).succ.succ.succ)) (.conj (ConstructionProbeMappedPathSyntax.nodeMap
    (13 : Fin 20).succ.succ.succ (19 : Fin 20).succ.succ.succ (2 : Fin 23)) (.conj
    (ConstructionProbeMappedPathSyntax.nodeMap (14 : Fin 20).succ.succ.succ (19 : Fin 20).succ.succ.succ (0
    : Fin 23)) (.conj (ConstructionProbeMappedPathSyntax.nodeMap (9 : Fin 20).succ.succ.succ (2 : Fin 23) (1
    : Fin 23)) (ConstructionMergerRootSystem.rootSystem (15 : Fin 20).succ.succ.succ (16 : Fin
    20).succ.succ.succ (17 : Fin 20).succ.succ.succ (18 : Fin 20).succ.succ.succ (1 : Fin 23) (0 : Fin
    23))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isEmpty,Project.Formula.extensionalEq,
      ConstructionRoundSource.provenance_freeClosed,
      ConstructionProbeConservativeSyntax.conservative_freeClosed,ConstructionRequestSchedule.mergerCode_freeClosed,ConstructionMergerRelations.prescription_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,ConstructionProbeLiftHomSyntax.preservesProducts_freeClosed,ConstructionMergerRootSystem.rootSystem_freeClosed]

theorem mergerAfter_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence mergerAfterSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) mergerAfterSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionRoundSource.provenance_semantics hM,
    ConstructionProbeConservativeSyntax.conservative_semantics hM,
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,ConstructionRequestSchedule.mergerCode_semantics hM,ConstructionMergerRelations.prescription_semantics hM,ConstructionProbeLiftHomSyntax.preservesProducts_semantics hM,ConstructionMergerRootSystem.rootSystem_semantics hM]
  exact fun hw hz hzw hm hmW hne hCode hSource hP hOrigin hO hR hLeg hPres =>
    merger_after hM hw hz hzw hm hmW hne hCode hSource hP hOrigin hO hR hLeg hPres

theorem mergerAfter_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence mergerAfterSentence) := ModelTransfer.derives (fun _ hM => mergerAfter_models hM)

end PPAC.Migration.ConstructionConeTransport
