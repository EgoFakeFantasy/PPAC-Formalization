/- Pinned ConcreteSystem.label_arrowMap_val/labelFiberSet_common and
Saturation.labelFiber_cardinal/gluedLabel_cardinal:213-267.
Consume the completed SAME ConstructionConcreteBase.Target; no new saturation,
ideal-probe, cardinal, function or quotient backend. -/
import PPAC.Migration.ForcingLabelCardinality
import PPAC.Migration.ConstructionConcreteBase

namespace PPAC.Migration.ForcingConcreteLabels
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Small)
open ForcingComponentFibers (VertexFiber ArrowMap)
open ConstructionComponentCarrier (EncodedVertex)
open ConstructionComponentCofinal (EncodedCommon)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem arrow_value {objects S maps v w X Y b x y : M.Carrier .set}
    (hMaps : ForcingLabelSystem.Maps objects S maps) (hb : ArrowMap maps v w X Y b)
    (hxy : PureKuratowski.PairMember M x y b) : x = y := by
  obtain ⟨r,a,U,s,c,V,z,f,_,_,_,hf,hR,_,_⟩ := hb
  obtain ⟨r',s',Or,Os,_,_,_,_,hId⟩ := ((hMaps z f).mp hf).2
  exact ((hId x y).mp (((hR x y).mp hxy).1)).2

theorem related_value {D I mul q objects S maps v X x w Y y : M.Carrier .set}
    (hMaps : ForcingLabelSystem.Maps objects S maps)
    (h : ForcingComponentMatches.Related D I mul q objects maps v X x w Y y) : x = y := by
  obtain ⟨t,Z,n,m,b,c,z,_,_,_,hb,hc,_,hzx,hzy⟩ := h
  exact (arrow_value hMaps hb hzx).symm.trans (arrow_value hMaps hc hzy)

def CommonFibers (D I mul objects maps : M.Carrier .set) : Prop :=
  ∀ q v w X Y, EncodedCommon D I mul q v w →
    VertexFiber D mul objects maps v X → VertexFiber D mul objects maps w Y → X = Y

theorem common_fibers (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e diagrams objImage objects S mapImage maps : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObj : MapsTo diagrams objImage objects)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S) (hMaps : MapsTo S mapImage maps)
    (hFamily : ForcingLabelSystem.Maps objects S maps)
    (hSys : ForcingEligibleSystem.System D objects maps) : CommonFibers D I mul objects maps := by
  intro q v w X Y hCommon hX hY
  have hC := ForcingComponentFibers.coherent_of_system hM hm hJ hDiagrams hObj hS hMaps hSys (q := q)
  have hReverse : EncodedCommon D I mul q w v := by
    obtain ⟨r,a,U,s,b,V,hv,hw,hr,hs,h⟩ := hCommon
    exact ⟨s,b,V,r,a,U,hw,hv,hs,hr,ConstructionComponentVertices.common_symm h⟩
  apply (ModelTransfer.extensionality hM).eq_of_same_members
  intro x
  constructor
  · intro hx
    obtain ⟨y,hy,h⟩ := ForcingComponentMatches.related_onto_common hM hDiagrams hObj hC hReverse hY hX hx
    exact related_value hFamily h ▸ hy
  · intro hx
    obtain ⟨y,hy,h⟩ := ForcingComponentMatches.related_onto_common hM hDiagrams hObj hC hCommon hX hY hx
    exact related_value hFamily h ▸ hy

/-- Every actual whole fiber, with an actual entire glued quotient, in one System. -/
def FiberCardinals (hM : FirstOrder.Theory.Models M nativeZF)
    (D I mul objects maps mu : M.Carrier .set) : Prop :=
  ∀ q v X, EncodedVertex D I mul q v → VertexFiber D mul objects maps v X →
    (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) X mu ∧
    ∃ P Q pr, ForcingComponentGluing.Component D I mul q objects maps v P ∧ MapsTo P Q pr ∧
      ForcingComponentGluing.Classes D I mul q objects maps P Q ∧
      ForcingComponentGluing.Projection D I mul q objects maps P pr ∧
      ForcingComponentGluing.AllFiberMaps D I mul q objects maps v Q pr ∧
      ForcingComponentGluing.Commuting D I mul q objects maps Q pr ∧
      (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) Q mu

theorem target_fiber_cardinals (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top zero mu history kappa D mul e mark H C incoming base I
      diagrams objImage objects S mapImage maps : M.Carrier .set}
    (hT : ConstructionConcreteBase.Target hM w Q R top zero mu history kappa D mul e mark H C incoming base)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObj : MapsTo diagrams objImage objects)
    (hObjects : ForcingLabelSystem.Objects D diagrams objects)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S) (hMaps : MapsTo S mapImage maps)
    (hCenters : ForcingLabelSystem.Centers D mul objects maps)
    (hSys : ForcingEligibleSystem.System D objects maps) : FiberCardinals hM D I mul objects maps mu := by
  obtain ⟨hRow,hFields,_,_,hIdeals,_,hCard⟩ := hT
  have hm := hFields.1
  have hJ := hFields.2.2.1
  obtain ⟨dToMu,hDToMu⟩ := hCard.1
  have hD : Small D mu := (ForcingSupportSize.native_small hM D mu).mpr ⟨dToMu,hDToMu.1⟩
  obtain ⟨id,hId⟩ := ZF.exists_identityBijection (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) mu
  intro q v X hv hX
  obtain ⟨r,a,U,hvCode,hr⟩ := hv
  obtain ⟨r',a',U',Or,hvCode',hOr,hFiber⟩ := hX
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hvCode hvCode'
  have hProbes := hIdeals D mul e mark H C incoming base a mark U hRow hFields.2.2.2.1 hFields.2.2.2.2.1 hr.2.2
  have hEq := ForcingLabelCardinality.fiber_equinumerous hM hDiagrams hObjects hCenters hOr hr.2.2 hProbes hFiber hD ⟨id,hId⟩
  have hVertex : EncodedVertex D I mul q v := ⟨r,a,U,hvCode,hr⟩
  have hVX : VertexFiber D mul objects maps v X := ⟨r,a,U,Or,hvCode,hOr,hFiber⟩
  have hArrow := ForcingComponentMatches.arrow_id hm hVertex
  have hCommon := ForcingComponentMatches.arrow_common hArrow hArrow
  obtain ⟨vertices,hVertices⟩ := ConstructionComponentCarrier.exists_carrier hM D I mul q
  obtain ⟨image,fibers,hFibers,hFamily⟩ := ForcingComponentFibers.exists_family hM hDiagrams hObj hVertices
  obtain ⟨A,hA⟩ := ForcingComponentMatches.exists_carrier hM hVertices hFibers hFamily
  obtain ⟨P,hP⟩ := ForcingComponentGluing.exists_component hM hA (root := v)
  obtain ⟨Z,pr,hpr,hZ,hProjection⟩ := ForcingComponentGluing.exists_quotient hM D I mul q objects maps P
  obtain ⟨hAll,hCommute⟩ := ForcingComponentGluing.gluing_laws hM hm hJ hDiagrams hObj hS hMaps hSys hP hpr hZ hProjection
  exact ⟨hEq,P,Z,pr,hP,hpr,hZ,hProjection,hAll,hCommute,
    ForcingLabelCardinality.glued_equinumerous hM hAll hCommon hVX hEq⟩

def Labels (hM : FirstOrder.Theory.Models M nativeZF) (D I mul mu : M.Carrier .set) : Prop :=
  ∃ diagrams objImage objects S mapImage maps,
    ForcingDiagramCarrier.Carrier D I diagrams ∧ MapsTo diagrams objImage objects ∧
    ForcingLabelSystem.Objects D diagrams objects ∧ ForcingEligibleMapFamily.Arrows D mul diagrams S ∧
    MapsTo S mapImage maps ∧ ForcingLabelSystem.Maps objects S maps ∧
    ForcingEligibleSystem.System D objects maps ∧ ForcingLabelSystem.Centers D mul objects maps ∧
    CommonFibers D I mul objects maps ∧ FiberCardinals hM D I mul objects maps mu

theorem target_labels (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top zero mu history kappa D mul e mark H C incoming base : M.Carrier .set}
    (hT : ConstructionConcreteBase.Target hM w Q R top zero mu history kappa D mul e mark H C incoming base)
    (I : M.Carrier .set) : Labels hM D I mul mu := by
  obtain ⟨diagrams,objImage,objects,S,mapImage,maps,hDiagrams,hObj,hObjects,hS,hMaps,hFamily,hSys⟩ :=
    ForcingLabelSystem.exists_system hM D I mul
  have hCenters := ForcingLabelSystem.centers_of_families hM hT.2.1.1 hDiagrams hObj hObjects hS hMaps hFamily
  exact ⟨diagrams,objImage,objects,S,mapImage,maps,hDiagrams,hObj,hObjects,hS,hMaps,hFamily,hSys,hCenters,
    common_fibers hM hT.2.1.1 hT.2.1.2.2.1 hDiagrams hObj hS hMaps hFamily hSys,
    target_fiber_cardinals hM hT hDiagrams hObj hObjects hS hMaps hCenters hSys⟩


def commonFibers {m : Nat} (D I mul objects maps : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ConstructionComponentCofinal.encodedCommon D.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ 4 3 2) (.imp (ForcingComponentFibers.vertexFiber D.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ 3 1) (.imp (ForcingComponentFibers.vertexFiber D.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ 2 0) (Project.Formula.extensionalEq (.bound 1) (.bound 0))))))))))

theorem commonFibers_freeClosed {m : Nat} (D I mul objects maps : Fin m) :
    (commonFibers D I mul objects maps).FreeClosed := by
  simp -implicitDefEqProofs [commonFibers,Definitional.Formula.FreeClosed,ConstructionComponentCofinal.encodedCommon_freeClosed,ForcingComponentFibers.vertexFiber_freeClosed,Project.Formula.extensionalEq]

theorem commonFibers_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul objects maps : Fin m) :
    Project.Formula.satisfies env (commonFibers D I mul objects maps) ↔ CommonFibers (env.bound D) (env.bound I) (env.bound mul) (env.bound objects) (env.bound maps) := by
  simp only [commonFibers,CommonFibers,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    ConstructionComponentCofinal.encodedCommon_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  rfl

def fiberCardinals {m : Nat} (D I mul objects maps mu : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.imp (ConstructionComponentCarrier.encodedVertex D.succ.succ.succ I.succ.succ.succ mul.succ.succ.succ 2 1) (.imp (ForcingComponentFibers.vertexFiber D.succ.succ.succ mul.succ.succ.succ objects.succ.succ.succ maps.succ.succ.succ 1 0) (.conj (Project.Formula.equinumerous PureKuratowskiProject.convention (.bound 0) (.bound mu.succ.succ.succ)) (.existsE (.existsE (.existsE (.conj (ForcingComponentGluing.component D.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ 5 objects.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ 4 2) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 0 2 1)) (.conj (ForcingComponentGluing.classes D.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ 5 objects.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ 2 1) (.conj (ForcingComponentGluing.projection D.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ 5 objects.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ 2 0) (.conj (ForcingComponentGluing.allFiberMaps D.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ 5 objects.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ 4 1 0) (.conj (ForcingComponentGluing.commuting D.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ 5 objects.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ 1 0) (Project.Formula.equinumerous PureKuratowskiProject.convention (.bound 1) (.bound mu.succ.succ.succ.succ.succ.succ)))))))))))))))))

theorem fiberCardinals_freeClosed {m : Nat} (D I mul objects maps mu : Fin m) :
    (fiberCardinals D I mul objects maps mu).FreeClosed := by
  simp -implicitDefEqProofs [fiberCardinals,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionComponentCarrier.encodedVertex_freeClosed,ForcingComponentFibers.vertexFiber_freeClosed,
    ForcingComponentGluing.component_freeClosed,ForcingComponentGluing.classes_freeClosed,ForcingComponentGluing.projection_freeClosed,
    ForcingComponentGluing.allFiberMaps_freeClosed,ForcingComponentGluing.commuting_freeClosed,Project.Formula.equinumerous]

theorem fiberCardinals_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul objects maps mu : Fin m) :
    Project.Formula.satisfies env (fiberCardinals D I mul objects maps mu) ↔ FiberCardinals hM (env.bound D) (env.bound I) (env.bound mul) (env.bound objects) (env.bound maps) (env.bound mu) := by
  simp only [fiberCardinals,FiberCardinals,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    ConstructionComponentCarrier.encodedVertex_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM,
    ForcingComponentGluing.component_semantics hM,ForcingComponentGluing.classes_semantics hM,ForcingComponentGluing.projection_semantics hM,
    ForcingComponentGluing.allFiberMaps_semantics hM,ForcingComponentGluing.commuting_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),
    Project.Formula.satisfies_equinumerous_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  rfl

def labels {m : Nat} (D I mul mu : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier D.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ 5)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 3 5 4)) (.conj (ForcingLabelSystem.objectFamily D.succ.succ.succ.succ.succ.succ 5 3) (.conj (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ 5 2)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 0 2 1)) (.conj (ForcingLabelSystem.mapFamily 3 2 0) (.conj (ForcingEligibleSystem.system D.succ.succ.succ.succ.succ.succ 3 0) (.conj (ForcingLabelSystem.centers D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ 3 0) (.conj (commonFibers D.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ 3 0) (fiberCardinals D.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ 3 0 mu.succ.succ.succ.succ.succ.succ))))))))))))))))

theorem labels_freeClosed {m : Nat} (D I mul mu : Fin m) :
    (labels D I mul mu).FreeClosed := by
  simp -implicitDefEqProofs [labels,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ForcingLabelSystem.objectFamily_freeClosed,ForcingLabelSystem.mapFamily_freeClosed,ForcingEligibleSystem.system_freeClosed,
    ForcingLabelSystem.centers_freeClosed,commonFibers_freeClosed,fiberCardinals_freeClosed]

theorem labels_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul mu : Fin m) :
    Project.Formula.satisfies env (labels D I mul mu) ↔ Labels hM (env.bound D) (env.bound I) (env.bound mul) (env.bound mu) := by
  simp only [labels,Labels,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramCarrier.carrier_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingLabelSystem.objectFamily_semantics hM,
    ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingLabelSystem.mapFamily_semantics hM,
    ForcingEligibleSystem.system_semantics hM,ForcingLabelSystem.centers_semantics hM,commonFibers_semantics hM,fiberCardinals_semantics hM]
  rfl

def targetSentence {k : Nat} (w Q R top zero mu history kappa D I mul e mark H C incoming base : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ConstructionConcreteBase.target w Q R top zero mu history kappa D mul e mark H C incoming base) (labels D I mul mu))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionConcreteBase.target_freeClosed,labels_freeClosed]

theorem target_models {k : Nat} (w Q R top zero mu history kappa D I mul e mark H C incoming base : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (targetSentence w Q R top zero mu history kappa D I mul e mark H C incoming base)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (targetSentence w Q R top zero mu history kappa D I mul e mark H C incoming base)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,ConstructionConcreteBase.target_semantics hM,labels_semantics hM]
  exact fun hT => target_labels hM hT (bound I)

theorem target_kernel_certificate {k : Nat} (w Q R top zero mu history kappa D I mul e mark H C incoming base : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (targetSentence w Q R top zero mu history kappa D I mul e mark H C incoming base)) :=
  ModelTransfer.derives (fun _ hM => target_models w Q R top zero mu history kappa D I mul e mark H C incoming base hM)

def Actual (hM : FirstOrder.Theory.Models M nativeZF)
    (w mul0 zero one two three Q R H0 C0 u top P c mu kappa B history D mul e mark H C incoming base : M.Carrier .set) : Prop :=
  ConstructionConcreteBase.TowerData hM w mul0 zero one two three Q R H0 C0 u top P c mu kappa B ∧
  ConstructionConcreteBase.Target hM w Q R top zero mu history kappa D mul e mark H C incoming base ∧
  ∀ I, Labels hM D I mul mu

theorem exists_actual (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) :
    ∃ mul0 zero one two three Q R H0 C0 u top P c mu kappa B history D mul e mark H C incoming base, Actual hM w mul0 zero one two three Q R H0 C0 u top P c mu kappa B history D mul e mark H C incoming base := by
  obtain ⟨mul0,zero,one,two,three,Q,R,H0,C0,u,top,P,c,mu,kappa,B,hData⟩ :=
    ConstructionConcreteBase.exists_tower_data hM hOrder hChoice hw
  obtain ⟨history,D,mul,e,mark,H,C,incoming,base,hT⟩ := ConstructionConcreteBase.target_of_tower_data hM hData
  exact ⟨mul0,zero,one,two,three,Q,R,H0,C0,u,top,P,c,mu,kappa,B,history,D,mul,e,mark,H,C,incoming,base,
    hData,hT,fun I => target_labels hM hT I⟩

def actual {m : Nat} (w mul0 zero one two three Q R H0 C0 u top P c mu kappa B history D mul e mark H C incoming base : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionConcreteBase.towerData w mul0 zero one two three Q R H0 C0 u top P c mu kappa B) (.conj (ConstructionConcreteBase.target w Q R top zero mu history kappa D mul e mark H C incoming base) (.forallE (labels D.succ 0 mul.succ mu.succ))))

theorem actual_freeClosed {m : Nat} (w mul0 zero one two three Q R H0 C0 u top P c mu kappa B history D mul e mark H C incoming base : Fin m) :
    (actual w mul0 zero one two three Q R H0 C0 u top P c mu kappa B history D mul e mark H C incoming base).FreeClosed := by
  simp -implicitDefEqProofs [actual,Definitional.Formula.FreeClosed,ConstructionConcreteBase.towerData_freeClosed,ConstructionConcreteBase.target_freeClosed,labels_freeClosed]

theorem actual_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w mul0 zero one two three Q R H0 C0 u top P c mu kappa B history D mul e mark H C incoming base : Fin m) :
    Project.Formula.satisfies env (actual w mul0 zero one two three Q R H0 C0 u top P c mu kappa B history D mul e mark H C incoming base) ↔ Actual hM (env.bound w) (env.bound mul0) (env.bound zero) (env.bound one) (env.bound two) (env.bound three) (env.bound Q) (env.bound R) (env.bound H0) (env.bound C0) (env.bound u) (env.bound top) (env.bound P) (env.bound c) (env.bound mu) (env.bound kappa) (env.bound B) (env.bound history) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound incoming) (env.bound base) := by
  simp only [actual,Actual,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,
    ConstructionConcreteBase.towerData_semantics hM,ConstructionConcreteBase.target_semantics hM,labels_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 1
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 1)))
      (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (actual 25 24 23 22 21 20 19 18 17 16 15 14 13 12 11 10 9 8 7 6 5 4 3 2 1 0)))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,actual_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_exists_iff,actual_semantics hM,Project.Term.eval_bound]
  exact exists_actual hM hOrder hChoice

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative constructionSentence)) := by
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
  apply ConstructibleGround.relative_models hM constructionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) constructionSentence).mp
    (construction_models hL (ConstructionRoundSelection.l_order hM) hChoice)

end PPAC.Migration.ForcingConcreteLabels
