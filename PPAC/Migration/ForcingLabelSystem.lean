/- Pinned LocalRecords.labelSystem:606-619. Actual label ranges and literal
inclusion maps, collected over every internal diagram and comparable pair.
Consumers: ConcreteSystem.label_available_center/labelFiberEmbedding and the
already migrated actual ComponentGluing, not a second quotient backend. -/
import PPAC.Migration.ForcingComponentGluing

namespace PPAC.Migration.ForcingLabelSystem
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection)
open ForcingSupportedNames (Range)
open ForcingConditionGraphs (IdentityGraph)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Objects (D diagrams objects : M.Carrier .set) : Prop := ∀ r O,
  PureKuratowski.PairMember M r O objects ↔ (Project.FirstOrderSemantics.reduct M).mem r diagrams ∧ Range D r O

def MapRow (objects z f : M.Carrier .set) : Prop := ∃ r s Or Os,
  PureKuratowski.Code M z r s ∧ PureKuratowski.PairMember M r Or objects ∧
  PureKuratowski.PairMember M s Os objects ∧ MapsTo Or Os f ∧ IdentityGraph Or f

def Maps (objects S maps : M.Carrier .set) : Prop := ∀ z f,
  PureKuratowski.PairMember M z f maps ↔ (Project.FirstOrderSemantics.reduct M).mem z S ∧ MapRow objects z f

theorem exists_range (hM : FirstOrder.Theory.Models M nativeZF)
    {D I r : M.Carrier .set} (hr : Injection D I r) : ∃ O, Range D r O := by
  have hn := (ForcingSupportSize.native_injection hM D I r).mp hr
  obtain ⟨O,hO⟩ := ZF.exists_range_of_setFunction (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) hn.1.1 hn.1.2.1
  exact ⟨O,fun y => ⟨fun hy => by
    obtain ⟨x,hxy⟩ := (hO y).mp hy
    exact ⟨x,ForcingConditionGraphs.function_input hr.1.1 hxy,hxy⟩,
    fun ⟨x,_,hxy⟩ => (hO y).mpr ⟨x,hxy⟩⟩⟩

theorem range_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {D r O P : M.Carrier .set} (hO : Range D r O) (hP : Range D r P) : O = P :=
  (ModelTransfer.extensionality hM).eq_of_same_members O P (fun x => (hO x).trans (hP x).symm)

theorem exists_map_row (hM : FirstOrder.Theory.Models M nativeZF)
    {D mul objects r s Or Os z : M.Carrier .set}
    (hr : PureKuratowski.PairMember M r Or objects) (hs : PureKuratowski.PairMember M s Os objects)
    (hOr : Range D r Or) (hOs : Range D s Os) (hz : PureKuratowski.Code M z r s)
    (hle : ForcingDiagramOrder.Le D mul s r) : ∃ f, MapRow objects z f := by
  obtain ⟨f,hf,hId⟩ := ForcingConditionGraphs.exists_identity hM Or
  refine ⟨f,r,s,Or,Os,hz,hr,hs,⟨hf.1.1,?_⟩,hId⟩
  intro x y hxy
  obtain ⟨hx,rfl⟩ := (hId x y).mp hxy
  obtain ⟨t,_,htx⟩ := (hOr x).mp hx
  obtain ⟨n,_,hSub⟩ := hle
  obtain ⟨_,u,hu,_,hux⟩ := (hSub t x).mp htx
  exact (hOs x).mpr ⟨u,hu,hux⟩

theorem map_row_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {diagrams image objects z f g : M.Carrier .set} (hObj : MapsTo diagrams image objects)
    (hf : MapRow objects z f) (hg : MapRow objects z g) : f = g := by
  obtain ⟨r,s,Or,Os,hz,hr,_,hf,hId⟩ := hf
  obtain ⟨r',s',Or',Os',hz',hr',_,hg,hId'⟩ := hg
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
  have he := ForcingConditionGraphs.function_unique hObj.1 hr hr'
  subst Or'
  exact SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM Or Os f).mp hf).1.1
    ((ForcingSupportSize.native_mapsTo hM Or Os' g).mp hg).1.1
    (fun x y => (hId x y).trans (hId' x y).symm)

theorem map_data {diagrams image objects S maps r s Or Os z f : M.Carrier .set}
    (hObj : MapsTo diagrams image objects) (hMaps : Maps objects S maps)
    (hr : PureKuratowski.PairMember M r Or objects) (hs : PureKuratowski.PairMember M s Os objects)
    (hz : PureKuratowski.Code M z r s) (hf : PureKuratowski.PairMember M z f maps) :
    MapsTo Or Os f ∧ IdentityGraph Or f := by
  obtain ⟨r',s',Or',Os',hz',hr',hs',hf,hId⟩ := ((hMaps z f).mp hf).2
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
  have er := ForcingConditionGraphs.function_unique hObj.1 hr hr'
  have es := ForcingConditionGraphs.function_unique hObj.1 hs hs'
  subst Or'; subst Os'
  exact ⟨hf,hId⟩

theorem system_of_families {D diagrams image objects S maps : M.Carrier .set}
    (hObj : MapsTo diagrams image objects) (hObjects : Objects D diagrams objects)
    (hMaps : Maps objects S maps) : ForcingEligibleSystem.System D objects maps := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro r s Or Os z f hr hs hz hf
    exact (map_data hObj hMaps hr hs hz hf).1
  · intro r Or z f hr hz hf
    exact (map_data hObj hMaps hr hr hz hf).2
  · intro r s t Or Os Ot z01 z12 z02 f g h hr hs ht hz01 hz12 hz02 hf hg hh
    have hF := map_data hObj hMaps hr hs hz01 hf
    have hG := map_data hObj hMaps hs ht hz12 hg
    have hH := map_data hObj hMaps hr ht hz02 hh
    intro x z
    constructor
    · intro hxz
      obtain ⟨hx,rfl⟩ := (hH.2 x z).mp hxz
      have hxx := (hF.2 x x).mpr ⟨hx,rfl⟩
      exact ⟨hx,x,hxx,(hG.2 x x).mpr ⟨hF.1.2 x x hxx,rfl⟩⟩
    · rintro ⟨hx,y,hxy,hyz⟩
      exact (hH.2 x z).mpr ⟨hx,((hF.2 x y).mp hxy).2.trans ((hG.2 y z).mp hyz).2⟩
  · intro r s Or Os z f hr hs hz hf
    have hF := map_data hObj hMaps hr hs hz hf
    exact ⟨hF.1,fun x y z hx hy => ((hF.2 x z).mp hx).2.trans ((hF.2 y z).mp hy).2.symm⟩
  · intro p s0 s1 v OP O0 O1 OV z0 z1 zk0 zk1 a0 a1 b0 b1 x0 x1 y hp hs0 hs1 hv hz0 hz1 hzk0 hzk1 ha0 ha1 hb0 hb1 hInt hx0 hx1
    have hA0 := map_data hObj hMaps hs0 hv hz0 ha0
    have hA1 := map_data hObj hMaps hs1 hv hz1 ha1
    have hB0 := map_data hObj hMaps hp hs0 hzk0 hb0
    have hB1 := map_data hObj hMaps hp hs1 hzk1 hb1
    obtain ⟨hxO0,rfl⟩ := (hA0.2 x0 y).mp hx0
    obtain ⟨hxO1,he⟩ := (hA1.2 x1 x0).mp hx1
    subst x1
    have hxP := (((hObjects p OP).mp hp).2 x0).mpr ((hInt x0).mp
      ⟨(((hObjects s0 O0).mp hs0).2 x0).mp hxO0,(((hObjects s1 O1).mp hs1).2 x0).mp hxO1⟩)
    exact ⟨x0,hxP,(hB0.2 x0 x0).mpr ⟨hxP,rfl⟩,(hB1.2 x0 x0).mpr ⟨hxP,rfl⟩⟩

def objectFamily {m : Nat} (D diagrams objects : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge objects.succ.succ 1 0))
    (.conj (.mem (.bound 1) (.bound diagrams.succ.succ))
      (ProjectSyntax.encode id (ForcingSupportedNames.range D.succ.succ 1 0)))))

theorem objectFamily_freeClosed {m : Nat} (D diagrams objects : Fin m) :
    (objectFamily D diagrams objects).FreeClosed := by
  simp -implicitDefEqProofs [objectFamily,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem objectFamily_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D diagrams objects : Fin m) :
    Project.Formula.satisfies env (objectFamily D diagrams objects) ↔ Objects (env.bound D) (env.bound diagrams) (env.bound objects) := by
  simp only [objectFamily,Objects,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingSupportedNames.range_semantics (M := M)]
  rfl

def mapRow {m : Nat} (objects z f : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.existsE
    (.conj (ProjectSyntax.encode id (PairSyntax.ordered z.succ.succ.succ.succ 3 2))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge objects.succ.succ.succ.succ 3 1))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge objects.succ.succ.succ.succ 2 0))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo f.succ.succ.succ.succ 1 0))
      (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph 1 f.succ.succ.succ.succ)))))))))

theorem mapRow_freeClosed {m : Nat} (objects z f : Fin m) : (mapRow objects z f).FreeClosed := by
  simp -implicitDefEqProofs [mapRow,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem mapRow_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (objects z f : Fin m) :
    Project.Formula.satisfies env (mapRow objects z f) ↔ MapRow (env.bound objects) (env.bound z) (env.bound f) := by
  simp only [mapRow,MapRow,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_code,KuratowskiZF.source_edge,
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingConditionGraphs.identityGraph_semantics (M := M)]
  rfl

def mapFamily {m : Nat} (objects S maps : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge maps.succ.succ 1 0))
    (.conj (.mem (.bound 1) (.bound S.succ.succ)) (mapRow objects.succ.succ 1 0))))

theorem mapFamily_freeClosed {m : Nat} (objects S maps : Fin m) : (mapFamily objects S maps).FreeClosed := by
  simp -implicitDefEqProofs [mapFamily,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,mapRow_freeClosed]

theorem mapFamily_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (objects S maps : Fin m) :
    Project.Formula.satisfies env (mapFamily objects S maps) ↔ Maps (env.bound objects) (env.bound S) (env.bound maps) := by
  simp only [mapFamily,Maps,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,mapRow_semantics hM]
  rfl

theorem exists_objects (hM : FirstOrder.Theory.Models M nativeZF)
    {D I diagrams : M.Carrier .set} (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) :
    ∃ image objects, MapsTo diagrams image objects ∧ Objects D diagrams objects := by
  let schema : Project.BinarySchema 1 := {
    body := ProjectSyntax.encode id (ForcingSupportedNames.range (2 : Fin 3) 1 0)
    freeClosed := ProjectSyntax.freeClosed _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 := { bound := fun _ => D, free := fun _ => diagrams }
  have he r O : schema.denote env r O ↔ Range D r O := by
    simp only [schema,env,Project.BinarySchema.denote,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
      ForcingSupportedNames.range_semantics (M := M)]
    rfl
  have ht : ∀ r, (Project.FirstOrderSemantics.reduct M).mem r diagrams → ∃ O, schema.denote env r O := by
    intro r hr
    obtain ⟨O,hO⟩ := exists_range hM ((hDiagrams r).mp hr)
    exact ⟨O,(he r O).mpr hO⟩
  have hu : ∀ r O P, schema.denote env r O → schema.denote env r P → O = P :=
    fun r O P hO hP => range_unique hM ((he r O).mp hO) ((he r P).mp hP)
  obtain ⟨image,hImage⟩ := ZF.exists_functionalImage (ModelTransfer.project_models_iff.mp hM) schema env diagrams ht hu
  obtain ⟨objects,hObj,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env ht (fun r _ O P hO hP => hu r O P hO hP)
    (fun r O hr hO => (hImage O).mpr ⟨r,hr,hO⟩)
  exact ⟨image,objects,(ForcingSupportSize.native_mapsTo hM diagrams image objects).mpr hObj,
    fun r O => (hEdge r O).trans (and_congr Iff.rfl (he r O))⟩

theorem exists_maps (hM : FirstOrder.Theory.Models M nativeZF)
    {D mul diagrams image objects S : M.Carrier .set}
    (hObj : MapsTo diagrams image objects) (hObjects : Objects D diagrams objects)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S) :
    ∃ mapImage maps, MapsTo S mapImage maps ∧ Maps objects S maps := by
  let schema : Project.BinarySchema 1 := { body := mapRow 2 1 0, freeClosed := mapRow_freeClosed _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 := { bound := fun _ => objects, free := fun _ => S }
  have he z f : schema.denote env z f ↔ MapRow objects z f := mapRow_semantics hM ((env.push z).push f) 2 1 0
  have ht : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z S → ∃ f, schema.denote env z f := by
    intro z hz
    obtain ⟨r,s,hr,hs,hle,hz⟩ := (hS z).mp hz
    obtain ⟨Or,hr,_⟩ := hObj.1.2 r hr
    obtain ⟨Os,hs,_⟩ := hObj.1.2 s hs
    obtain ⟨f,hf⟩ := exists_map_row hM hr hs ((hObjects r Or).mp hr).2 ((hObjects s Os).mp hs).2 hz hle
    exact ⟨f,(he z f).mpr hf⟩
  have hu : ∀ z f g, schema.denote env z f → schema.denote env z g → f = g :=
    fun z f g hf hg => map_row_unique hM hObj ((he z f).mp hf) ((he z g).mp hg)
  obtain ⟨mapImage,hImage⟩ := ZF.exists_functionalImage (ModelTransfer.project_models_iff.mp hM) schema env S ht hu
  obtain ⟨maps,hMaps,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env ht (fun z _ f g hf hg => hu z f g hf hg)
    (fun z f hz hf => (hImage f).mpr ⟨z,hz,hf⟩)
  exact ⟨mapImage,maps,(ForcingSupportSize.native_mapsTo hM S mapImage maps).mpr hMaps,
    fun z f => (hEdge z f).trans (and_congr Iff.rfl (he z f))⟩

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF) (D I mul : M.Carrier .set) :
    ∃ diagrams objImage objects S mapImage maps,
      ForcingDiagramCarrier.Carrier D I diagrams ∧ MapsTo diagrams objImage objects ∧ Objects D diagrams objects ∧
      ForcingEligibleMapFamily.Arrows D mul diagrams S ∧ MapsTo S mapImage maps ∧ Maps objects S maps ∧
      ForcingEligibleSystem.System D objects maps := by
  obtain ⟨diagrams,hDiagrams⟩ := ForcingDiagramCarrier.exists_carrier hM D I
  obtain ⟨objImage,objects,hObj,hObjects⟩ := exists_objects hM hDiagrams
  let env : Fin 3 → M.Carrier .set := Fin.cases D (Fin.cases mul (fun _ => diagrams))
  obtain ⟨S,hS⟩ := ForcingEligibleMapFamily.exists_arrows hM env 0 1 2
  obtain ⟨mapImage,maps,hMaps,hFamily⟩ := exists_maps hM hObj hObjects hS
  exact ⟨diagrams,objImage,objects,S,mapImage,maps,hDiagrams,hObj,hObjects,hS,hMaps,hFamily,system_of_families hObj hObjects hFamily⟩

theorem available_center (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e diagrams objImage objects S mapImage maps r Or k j n : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObj : MapsTo diagrams objImage objects)
    (hObjects : Objects D diagrams objects) (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S)
    (hMaps : MapsTo S mapImage maps) (hFamily : Maps objects S maps)
    (hr : PureKuratowski.PairMember M r Or objects) (hkj : PureKuratowski.PairMember M k j r)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n D) :
    ForcingSystemAvailability.Available D mul objects maps r j n ↔ ConstructionBaseMonoid.Divides D mul n k := by
  have hrI := (hDiagrams r).mp (ForcingConditionGraphs.function_input hObj.1 hr)
  have hk := ForcingConditionGraphs.function_input hrI.1.1 hkj
  obtain ⟨s,hsI,hSub⟩ := ForcingDiagramOrder.exists_sub hM (hm.2.1 n hn) hrI
  obtain ⟨Os,hs,_⟩ := hObj.1.2 s ((hDiagrams s).mpr hsI)
  obtain ⟨z,f,hz,hf,_⟩ := ForcingSystemAvailability.exists_map hM hObj hS hMaps
    (system_of_families hObj hObjects hFamily) hr hs ⟨n,hn,hSub⟩
  have hId := (map_data hObj hFamily hs hr hz hf).2
  rw [ForcingSystemFibers.available_iff_at_sub hM hDiagrams hObj hMaps hs hSub hz hf]
  have hOs := ((hObjects s Os).mp hs).2
  constructor
  · rintro ⟨y,hy,hyj⟩
    have he := ((hId y j).mp hyj).2
    subst y
    obtain ⟨k',_,hnk',hk'j⟩ := (ConstructionDiagramPlacements.sub_range hSub).mp ((hOs j).mp hy)
    have he := hrI.2 k' k j hk'j hkj
    exact he ▸ hnk'
  · intro hnk
    have hj := (hOs j).mpr ((ConstructionDiagramPlacements.sub_range hSub).mpr ⟨k,hk,hnk,hkj⟩)
    exact ⟨j,hj,(hId j j).mpr ⟨hj,rfl⟩⟩

def Centers (D mul objects maps : M.Carrier .set) : Prop := ∀ r Or k j n,
  PureKuratowski.PairMember M r Or objects → PureKuratowski.PairMember M k j r →
  (Project.FirstOrderSemantics.reduct M).mem n D →
    (ForcingSystemAvailability.Available D mul objects maps r j n ↔ ConstructionBaseMonoid.Divides D mul n k)

theorem centers_of_families (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e diagrams objImage objects S mapImage maps : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObj : MapsTo diagrams objImage objects)
    (hObjects : Objects D diagrams objects) (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S)
    (hMaps : MapsTo S mapImage maps) (hFamily : Maps objects S maps) : Centers D mul objects maps :=
  fun _ _ _ _ _ hr hkj hn => available_center hM hm hDiagrams hObj hObjects hS hMaps hFamily hr hkj hn

def centers {m : Nat} (D mul objects maps : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge objects.succ.succ.succ.succ.succ 4 3)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 4 2 1)) (.imp (.mem (.bound 0) (.bound D.succ.succ.succ.succ.succ)) (.iff (ProjectSyntax.encode id (ForcingSystemAvailability.available D.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ 4 1 0)) (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ 0 2)))))))))))

theorem centers_freeClosed {m : Nat} (D mul objects maps : Fin m) :
    (centers D mul objects maps).FreeClosed := by
  simp -implicitDefEqProofs [centers,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem centers_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul objects maps : Fin m) :
    Project.Formula.satisfies env (centers D mul objects maps) ↔ Centers (env.bound D) (env.bound mul) (env.bound objects) (env.bound maps) := by
  simp only [centers,Centers,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingSystemAvailability.available_semantics (M := M),ConstructionBaseMonoid.divides_semantics (M := M)]
  rfl

def constructionSentence {k : Nat} (D I mul e : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e)) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier D.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ 5)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 3 5 4)) (.conj (objectFamily D.succ.succ.succ.succ.succ.succ 5 3) (.conj (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ 5 2)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 0 2 1)) (.conj (mapFamily 3 2 0) (.conj (ForcingEligibleSystem.system D.succ.succ.succ.succ.succ.succ 3 0) (centers D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ 3 0)))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      objectFamily_freeClosed,mapFamily_freeClosed,ForcingEligibleSystem.system_freeClosed,centers_freeClosed]

theorem construction_models {k : Nat} (D I mul e : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence D I mul e)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence D I mul e)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingEligibleMapFamily.arrows_semantics (M := M),objectFamily_semantics hM,mapFamily_semantics hM,
    ForcingEligibleSystem.system_semantics hM,centers_semantics hM]
  intro hm
  obtain ⟨diagrams,objImage,objects,S,mapImage,maps,hDiagrams,hObj,hObjects,hS,hMaps,hFamily,hSys⟩ :=
    exists_system hM (bound D) (bound I) (bound mul)
  exact ⟨diagrams,objImage,objects,S,mapImage,maps,hDiagrams,hObj,hObjects,hS,hMaps,hFamily,hSys,
    centers_of_families hM hm hDiagrams hObj hObjects hS hMaps hFamily⟩

theorem construction_kernel_certificate {k : Nat} (D I mul e : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence D I mul e)) :=
  ModelTransfer.derives (fun _ hM => construction_models D I mul e hM)

end PPAC.Migration.ForcingLabelSystem
