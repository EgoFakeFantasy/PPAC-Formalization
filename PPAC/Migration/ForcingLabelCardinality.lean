/- Pinned ConcreteSystem.labelFiberEmbedding/labelFiber_cardinal/
gluedLabel_cardinal:185-267. Use the existing actual IdealProbes and cardinal
bounds, literal label diagrams, native composition/inverse/Cantor-Bernstein,
and the actual component quotient. No symbolic fiber size is postulated. -/
import PPAC.Migration.ForcingLabelSystem
import YesMetaZFC.SetTheory.Card.CantorBernstein

namespace PPAC.Migration.ForcingLabelCardinality
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection Small)
open ForcingSystemFibers (Fiber)
open ForcingLabelSystem (Objects Maps Centers)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem profile_mem {D mul objects maps r Or a U X p j : M.Carrier .set}
    (hCenters : Centers D mul objects maps) (hr : PureKuratowski.PairMember M r Or objects)
    (hRange : ForcingSupportedNames.Range D r Or) (hF : Fiber D mul objects maps r Or a U X)
    (hU : ConstructionIdealProbes.ConeIdeal D mul a U)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p D) (hpj : PureKuratowski.PairMember M p j r)
    (hProfile : ∀ n, (Project.FirstOrderSemantics.reduct M).mem n D →
      ((ConstructionBaseMonoid.Divides D mul n a ∧ ConstructionBaseMonoid.Divides D mul n p) ↔
        (Project.FirstOrderSemantics.reduct M).mem n U)) : (Project.FirstOrderSemantics.reduct M).mem j X := by
  refine (hF j).mpr ⟨(hRange j).mpr ⟨p,hp,hpj⟩,?_⟩
  intro n
  constructor
  · intro hnU
    have hn := hU.1 n hnU
    obtain ⟨hna,hnp⟩ := (hProfile n hn).mpr hnU
    exact ⟨hn,hna,(hCenters r Or p j n hr hpj hn).mpr hnp⟩
  · rintro ⟨hn,hna,hnj⟩
    exact (hProfile n hn).mp ⟨hna,(hCenters r Or p j n hr hpj hn).mp hnj⟩

theorem fiber_embedding (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul diagrams objects maps K mark a b U r Or X : M.Carrier .set}
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObjects : Objects D diagrams objects)
    (hCenters : Centers D mul objects maps) (hr : PureKuratowski.PairMember M r Or objects)
    (hU : ConstructionIdealProbes.ConeIdeal D mul a U)
    (hProbes : ConstructionIdealProbes.IdealProbes K D mul mark a b U)
    (hF : Fiber D mul objects maps r Or a U X) :
    ∃ f, Injection K X f ∧ ∃ family, Injection K D family ∧
      ForcingConditionGraphs.CompositionGraph K r family f := by
  have hR := (hObjects r Or).mp hr
  have hrI := (hDiagrams r).mp hR.1
  obtain ⟨family,hFamily,hProfiles,_⟩ := hProbes
  obtain ⟨f,hf,hEdges⟩ := ZF.exists_compositionFunction (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) ((ForcingSupportSize.native_mapsTo hM K D family).mp hFamily.1)
    ((ForcingSupportSize.native_mapsTo hM D I r).mp hrI.1)
  have hComp : ForcingConditionGraphs.CompositionGraph K r family f := hEdges
  have hFMap : MapsTo K X f := by
    refine ⟨((ForcingSupportSize.native_mapsTo hM K I f).mpr hf).1,?_⟩
    intro k j hkj
    obtain ⟨_,p,hkp,hpj⟩ := (hComp k j).mp hkj
    obtain ⟨_,_,_,_,_,hProfile,_⟩ := hProfiles k p hkp
    exact profile_mem hCenters hr hR.2 hF hU (hFamily.1.2 k p hkp) hpj hProfile
  refine ⟨f,⟨hFMap,?_⟩,family,hFamily,hComp⟩
  intro k l j hkj hlj
  obtain ⟨_,p,hkp,hpj⟩ := (hComp k j).mp hkj
  obtain ⟨_,t,hlt,htj⟩ := (hComp l j).mp hlj
  have he := hrI.2 p t j hpj htj
  subst t
  exact hFamily.2 k l p hkp hlt

theorem fiber_small (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul diagrams objects maps mu a U r Or X : M.Carrier .set}
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObjects : Objects D diagrams objects)
    (hr : PureKuratowski.PairMember M r Or objects) (hF : Fiber D mul objects maps r Or a U X)
    (hD : Small D mu) : Small X mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  have hR := (hObjects r Or).mp hr
  have hrI := (hDiagrams r).mp hR.1
  have hRMap : MapsTo D Or r := ⟨hrI.1.1,fun x y hxy =>
    (hR.2 y).mpr ⟨x,ForcingConditionGraphs.function_input hrI.1.1 hxy,hxy⟩⟩
  have hBij : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo pair r D Or :=
    ⟨⟨(ForcingSupportSize.native_mapsTo hM D Or r).mp hRMap,hrI.2⟩,fun y hy => (hR.2 y).mp hy⟩
  obtain ⟨inverse,hInverse⟩ := ZF.exists_inverseBijection hZF pair hBij
  obtain ⟨inclusion,hInclusion⟩ := ZF.exists_inclusionInjection hZF pair (fun x hx => ((hF x).mp hx).1)
  obtain ⟨toD,hToD⟩ := ZF.exists_compositionInjection hZF pair hInclusion hInverse.1
  obtain ⟨toMu,hToMu⟩ := (ForcingSupportSize.native_small hM D mu).mp hD
  exact (ForcingSupportSize.native_small hM X mu).mpr (ZF.exists_compositionInjection hZF pair hToD hToMu)

theorem fiber_equinumerous (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul diagrams objects maps K mu mark a b U r Or X : M.Carrier .set}
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObjects : Objects D diagrams objects)
    (hCenters : Centers D mul objects maps) (hr : PureKuratowski.PairMember M r Or objects)
    (hU : ConstructionIdealProbes.ConeIdeal D mul a U)
    (hProbes : ConstructionIdealProbes.IdealProbes K D mul mark a b U)
    (hF : Fiber D mul objects maps r Or a U X) (hD : Small D mu)
    (hK : (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) K mu) :
    (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) X mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨f,hf,_⟩ := fiber_embedding hM hDiagrams hObjects hCenters hr hU hProbes hF
  obtain ⟨kToMu,hKtoMu⟩ := hK
  obtain ⟨muToK,hMuToK⟩ := ZF.exists_inverseBijection hZF pair hKtoMu
  obtain ⟨lower,hLower⟩ := ZF.exists_compositionInjection hZF pair hMuToK.1
    ((ForcingSupportSize.native_injection hM K X f).mp hf)
  obtain ⟨upper,hUpper⟩ := (ForcingSupportSize.native_small hM X mu).mp (fiber_small hM hDiagrams hObjects hr hF hD)
  exact ZF.equinumerous_of_injections hZF pair hUpper hLower

theorem glued_equinumerous (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul q objects maps root Q pr v X mu : M.Carrier .set}
    (hAll : ForcingComponentGluing.AllFiberMaps D I mul q objects maps root Q pr)
    (hv : ConstructionComponentCofinal.EncodedCommon D I mul q root v)
    (hX : ForcingComponentFibers.VertexFiber D mul objects maps v X)
    (hEq : (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) X mu) :
    (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) Q mu := by
  obtain ⟨b,_,hb,hOnto⟩ := hAll v X hv hX
  have hBij : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo (KuratowskiZF.interpretation hM) b X Q :=
    ⟨(ForcingSupportSize.native_injection hM X Q b).mp hb,hOnto⟩
  obtain ⟨inverse,hInverse⟩ := ZF.exists_inverseBijection (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) hBij
  obtain ⟨f,hf⟩ := hEq
  exact ZF.exists_compositionBijection (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) hInverse hf

/-- Joint construction: the literal label System, specified exact fiber,
whole actual glued component and both cardinal equalities use the same data. -/
theorem construct (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q r a U K mu mark b : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hVertex : ConstructionComponentVertices.Vertex D I mul q r a U)
    (hProbes : ConstructionIdealProbes.IdealProbes K D mul mark a b U)
    (hD : Small D mu)
    (hK : (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) K mu) :
    ∃ diagrams objImage objects S mapImage maps Or X v P Q pr,
      ForcingDiagramCarrier.Carrier D I diagrams ∧ MapsTo diagrams objImage objects ∧ Objects D diagrams objects ∧
      ForcingEligibleMapFamily.Arrows D mul diagrams S ∧ MapsTo S mapImage maps ∧ Maps objects S maps ∧
      ForcingEligibleSystem.System D objects maps ∧ Centers D mul objects maps ∧
      PureKuratowski.PairMember M r Or objects ∧ Fiber D mul objects maps r Or a U X ∧
      ConstructionComponentCarrier.Code v r a U ∧ ForcingComponentGluing.Component D I mul q objects maps v P ∧
      MapsTo P Q pr ∧ ForcingComponentGluing.Classes D I mul q objects maps P Q ∧
      ForcingComponentGluing.Projection D I mul q objects maps P pr ∧
      ForcingComponentGluing.AllFiberMaps D I mul q objects maps v Q pr ∧
      ForcingComponentGluing.Commuting D I mul q objects maps Q pr ∧
      (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) X mu ∧
      (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) Q mu := by
  obtain ⟨diagrams,objImage,objects,S,mapImage,maps,hDiagrams,hObj,hObjects,hS,hMaps,hFamily,hSys⟩ :=
    ForcingLabelSystem.exists_system hM D I mul
  have hCenters := ForcingLabelSystem.centers_of_families hM hm hDiagrams hObj hObjects hS hMaps hFamily
  obtain ⟨Or,hr,_⟩ := hObj.1.2 r ((hDiagrams r).mpr hVertex.1)
  obtain ⟨X,hX⟩ := ForcingSystemFibers.exists_fiber hM D mul objects maps r Or a U
  have hEqX := fiber_equinumerous hM hDiagrams hObjects hCenters hr hVertex.2.2 hProbes hX hD hK
  obtain ⟨v,hv⟩ := ConstructionComponentCarrier.code_total hM r a U
  have hV : ConstructionComponentCarrier.EncodedVertex D I mul q v := ⟨r,a,U,hv,hVertex⟩
  have hVX : ForcingComponentFibers.VertexFiber D mul objects maps v X := ⟨r,a,U,Or,hv,hr,hX⟩
  have hId := ForcingComponentMatches.arrow_id hm hV
  have hCommon := ForcingComponentMatches.arrow_common hId hId
  obtain ⟨vertices,hVertices⟩ := ConstructionComponentCarrier.exists_carrier hM D I mul q
  obtain ⟨image,fibers,hFibers,hFiberFamily⟩ := ForcingComponentFibers.exists_family hM hDiagrams hObj hVertices
  obtain ⟨A,hA⟩ := ForcingComponentMatches.exists_carrier hM hVertices hFibers hFiberFamily
  obtain ⟨P,hP⟩ := ForcingComponentGluing.exists_component hM hA (root := v)
  obtain ⟨Q,pr,hpr,hQ,hProjection⟩ := ForcingComponentGluing.exists_quotient hM D I mul q objects maps P
  obtain ⟨hAll,hCommute⟩ := ForcingComponentGluing.gluing_laws hM hm hJ hDiagrams hObj hS hMaps hSys hP hpr hQ hProjection
  have hEqQ := glued_equinumerous hM hAll hCommon hVX hEqX
  exact ⟨diagrams,objImage,objects,S,mapImage,maps,Or,X,v,P,Q,pr,hDiagrams,hObj,hObjects,hS,hMaps,hFamily,hSys,hCenters,hr,hX,hv,hP,hpr,hQ,hProjection,hAll,hCommute,hEqX,hEqQ⟩

def constructionSentence {k : Nat} (D I mul e q r a U K mu mark b : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.imp (ConstructionComponentVertices.vertex D I mul q r a U) (.imp (ConstructionIdealProbes.idealProbesF K D mul mark a b U) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small D mu)) (.imp (Project.Formula.equinumerous PureKuratowskiProject.convention (.bound K) (.bound mu)) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 9 11 10)) (.conj (ForcingLabelSystem.objectFamily D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 9) (.conj (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 8)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 6 8 7)) (.conj (ForcingLabelSystem.mapFamily 9 8 6) (.conj (ForcingEligibleSystem.system D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 6) (.conj (ForcingLabelSystem.centers D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 6) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 9 r.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 5)) (.conj (ProjectSyntax.encode id (ForcingSystemFibers.fiber D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 6 r.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 5 a.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ U.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 4)) (.conj (ConstructionComponentCarrier.code 3 r.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ a.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ U.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj (ForcingComponentGluing.component D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 6 3 2) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 0 2 1)) (.conj (ForcingComponentGluing.classes D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 6 2 1) (.conj (ForcingComponentGluing.projection D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 6 2 0) (.conj (ForcingComponentGluing.allFiberMaps D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 6 3 1 0) (.conj (ForcingComponentGluing.commuting D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 6 1 0) (.conj (Project.Formula.equinumerous PureKuratowskiProject.convention (.bound 4) (.bound mu.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (Project.Formula.equinumerous PureKuratowskiProject.convention (.bound 1) (.bound mu.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionComponentVertices.vertex_freeClosed,
      ConstructionIdealProbes.idealProbesF_freeClosed,ForcingLabelSystem.objectFamily_freeClosed,
      ForcingLabelSystem.mapFamily_freeClosed,ForcingEligibleSystem.system_freeClosed,ForcingLabelSystem.centers_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,ForcingComponentGluing.component_freeClosed,
      ForcingComponentGluing.classes_freeClosed,ForcingComponentGluing.projection_freeClosed,
      ForcingComponentGluing.allFiberMaps_freeClosed,ForcingComponentGluing.commuting_freeClosed]

theorem construction_models {k : Nat} (D I mul e q r a U K mu mark b : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence D I mul e q r a U K mu mark b)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence D I mul e q r a U K mu mark b)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ConstructionComponentVertices.vertex_semantics hM,ConstructionIdealProbes.idealProbesF_semantics hM,
    ForcingSupportSize.small_semantics (M := M),
    Project.Formula.satisfies_equinumerous_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingLabelSystem.objectFamily_semantics hM,ForcingEligibleMapFamily.arrows_semantics (M := M),
    ForcingLabelSystem.mapFamily_semantics hM,ForcingEligibleSystem.system_semantics hM,ForcingLabelSystem.centers_semantics hM,
    ForcingSystemFibers.fiber_semantics (M := M),ConstructionComponentCarrier.code_semantics hM,
    ForcingComponentGluing.component_semantics hM,ForcingComponentGluing.classes_semantics hM,
    ForcingComponentGluing.projection_semantics hM,ForcingComponentGluing.allFiberMaps_semantics hM,
    ForcingComponentGluing.commuting_semantics hM]
  exact fun hm hJ hv hProbes hD hK => construct hM hm hJ hv hProbes hD hK

theorem construction_kernel_certificate {k : Nat} (D I mul e q r a U K mu mark b : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence D I mul e q r a U K mu mark b)) :=
  ModelTransfer.derives (fun _ hM => construction_models D I mul e q r a U K mu mark b hM)

end PPAC.Migration.ForcingLabelCardinality
