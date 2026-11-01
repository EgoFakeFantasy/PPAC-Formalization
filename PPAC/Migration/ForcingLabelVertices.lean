/- Fixed OrbitAssignments.labelVertex/labelVertex_mem/labelVertex_arrow:523-552.
Use the actual label-system availability ideal and literal label at the same
root extension. Reuse native ideal/fiber constructors and availability_sub. -/
import PPAC.Migration.ForcingLabelSystem
import PPAC.Migration.ForcingComponentFibers

namespace PPAC.Migration.ForcingLabelVertices
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Sub Le Product)
open ForcingDiagramPoset (LeftCancelMonoid)
open ConstructionComponentVertices (Vertex Arrow)
open ConstructionComponentCarrier (Code)
open ForcingSystemAvailability (Carrier)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def LabelVertex (D I mul q objects maps r a j v : M.Carrier .set) : Prop :=
  ∃ U, Code v r a U ∧ Vertex D I mul q r a U ∧ Carrier D mul objects maps r j a U

def labelVertex {m : Nat} (D I mul q objects maps r a j v : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (ConstructionComponentCarrier.code v.succ r.succ a.succ 0)
    (.conj (ConstructionComponentVertices.vertex D.succ I.succ mul.succ q.succ r.succ a.succ 0)
      (ProjectSyntax.encode id (ForcingSystemAvailability.carrier D.succ mul.succ objects.succ maps.succ r.succ j.succ a.succ 0))))

theorem labelVertex_freeClosed {m : Nat} (D I mul q objects maps r a j v : Fin m) :
    (labelVertex D I mul q objects maps r a j v).FreeClosed := by
  simp -implicitDefEqProofs [labelVertex,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionComponentCarrier.code_freeClosed,ConstructionComponentVertices.vertex_freeClosed]

theorem labelVertex_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q objects maps r a j v : Fin m) :
    Project.Formula.satisfies env (labelVertex D I mul q objects maps r a j v) ↔
      LabelVertex (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound objects) (env.bound maps)
        (env.bound r) (env.bound a) (env.bound j) (env.bound v) := by
  simp only [labelVertex,LabelVertex,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionComponentCarrier.code_semantics hM,ConstructionComponentVertices.vertex_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSystemAvailability.carrier_semantics (M := M)]
  rfl

theorem labelVertex_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul q objects maps r a j v w : M.Carrier .set}
    (hv : LabelVertex D I mul q objects maps r a j v) (hw : LabelVertex D I mul q objects maps r a j w) : v = w := by
  obtain ⟨U,hv,_,hU⟩ := hv
  obtain ⟨V,hw,_,hV⟩ := hw
  have e := (ModelTransfer.extensionality hM).eq_of_same_members U V (fun n => (hU n).trans (hV n).symm)
  exact ConstructionComponentCarrier.code_unique hM (e ▸ hv) hw

theorem construct (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul one q diagrams objImage objects S mapImage maps r Or a label : M.Carrier .set}
    (hm : LeftCancelMonoid D mul one)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams)
    (hObj : MapsTo diagrams objImage objects)
    (hObjects : ForcingLabelSystem.Objects D diagrams objects)
    (hArrows : ForcingEligibleMapFamily.Arrows D mul diagrams S)
    (hMaps : MapsTo S mapImage maps) (hMapFamily : ForcingLabelSystem.Maps objects S maps)
    (hr : PureKuratowski.PairMember M r Or objects)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a D)
    (hRoot : Sub D mul r a q)
    (hj : (Project.FirstOrderSemantics.reduct M).mem label Or) :
    ∃ v X, LabelVertex D I mul q objects maps r a label v ∧
      ForcingComponentFibers.VertexFiber D mul objects maps v X ∧ (Project.FirstOrderSemantics.reduct M).mem label X := by
  have hSys := ForcingLabelSystem.system_of_families hObj hObjects hMapFamily
  obtain ⟨U,hU,hIdeal⟩ := ForcingSystemAvailability.all_ideals hM hm hDiagrams hObj hArrows hMaps hSys r Or a label hr hj ha
  obtain ⟨v,hCode⟩ := ConstructionComponentCarrier.code_total hM r a U
  obtain ⟨X,hX⟩ := ForcingSystemFibers.exists_fiber hM D mul objects maps r Or a U
  have hrI := (hDiagrams r).mp (ForcingConditionGraphs.function_input hObj.1 hr)
  exact ⟨v,X,⟨U,hCode,⟨hrI,hRoot,hIdeal⟩,hU⟩,⟨r,a,U,Or,hCode,hr,hX⟩,(hX label).mpr ⟨hj,hU⟩⟩

/-- Actual label-system contraction. The ideal equality is the existing availability_sub. -/
theorem arrow_at (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul one q diagrams objImage objects S mapImage maps r Or a label s Os b U V : M.Carrier .set}
    (hm : LeftCancelMonoid D mul one)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams)
    (hObj : MapsTo diagrams objImage objects)
    (hObjects : ForcingLabelSystem.Objects D diagrams objects)
    (hArrows : ForcingEligibleMapFamily.Arrows D mul diagrams S)
    (hMaps : MapsTo S mapImage maps) (hMapFamily : ForcingLabelSystem.Maps objects S maps)
    (hr : PureKuratowski.PairMember M r Or objects) (hs : PureKuratowski.PairMember M s Os objects)
    (hv : Vertex D I mul q r a U) (hw : Vertex D I mul q s b V)
    (hU : Carrier D mul objects maps r label a U) (hV : Carrier D mul objects maps s label b V)
    (hj : (Project.FirstOrderSemantics.reduct M).mem label Os) (hrs : Le D mul r s) :
    ∃ n, Arrow D mul r U s V n := by
  obtain ⟨n,hn,hSub⟩ := hrs
  have hSys := ForcingLabelSystem.system_of_families hObj hObjects hMapFamily
  obtain ⟨z,f,hz,hf,_⟩ := ForcingSystemAvailability.exists_map hM hObj hArrows hMaps hSys hr hs ⟨n,hn,hSub⟩
  have hId := (ForcingLabelSystem.map_data hObj hMapFamily hs hr hz hf).2
  have hLabelEdge := (hId label label).mpr ⟨hj,rfl⟩
  obtain ⟨c,hc,hprod⟩ := (hm.2.1 n hn).1 b hw.2.2.2.1
  have hSubRoot := ForcingDiagramPoset.sub_sub hm hn hw.2.2.2.1 hprod hSub hw.2.1
  have e := ForcingDiagramPoset.index_unique hm hv.1 hc hv.2.2.2.1 hSubRoot hv.2.1
  have hna : Product mul n b a := e ▸ hprod
  have hAvail := (ForcingSystemFibers.available_iff_at_sub hM hDiagrams hObj hMaps hs hSub hz hf).mpr ⟨label,hj,hLabelEdge⟩
  have hnU := (hU n).mpr ⟨hn,⟨b,hw.2.2.2.1,hna⟩,hAvail⟩
  exact ⟨n,hnU,hSub,ForcingSystemFibers.availability_sub hM hm hDiagrams hObj hArrows hMaps hSys
    hr hs hn hw.2.2.2.1 hna hSub hz hf hLabelEdge hU hV⟩

theorem labelVertex_arrow (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul one q diagrams objImage objects S mapImage maps r Or a label v old s b V X : M.Carrier .set}
    (hm : LeftCancelMonoid D mul one)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams)
    (hObj : MapsTo diagrams objImage objects)
    (hObjects : ForcingLabelSystem.Objects D diagrams objects)
    (hArrows : ForcingEligibleMapFamily.Arrows D mul diagrams S)
    (hMaps : MapsTo S mapImage maps) (hMapFamily : ForcingLabelSystem.Maps objects S maps)
    (hr : PureKuratowski.PairMember M r Or objects)
    (hv : LabelVertex D I mul q objects maps r a label v)
    (hOldCode : Code old s b V) (hOldVertex : Vertex D I mul q s b V)
    (hFiber : ForcingComponentFibers.VertexFiber D mul objects maps old X)
    (hj : (Project.FirstOrderSemantics.reduct M).mem label X) (hrs : Le D mul r s) :
    ∃ n, ConstructionComponentCofinal.EncodedArrow D I mul q v old n := by
  obtain ⟨U,hCode,hVertex,hU⟩ := hv
  obtain ⟨t,c,W,Os,hCode',ht,hX⟩ := hFiber
  obtain ⟨es,eb,eV⟩ := ConstructionComponentCarrier.code_injective hCode' hOldCode
  have hs : PureKuratowski.PairMember M s Os objects := es ▸ ht
  have hjOs := ((hX label).mp hj).1
  have hV : Carrier D mul objects maps s label b V := by simpa only [es,eb,eV] using ((hX label).mp hj).2
  obtain ⟨n,hArrow⟩ := arrow_at hM hm hDiagrams hObj hObjects hArrows hMaps hMapFamily hr hs hVertex hOldVertex hU hV hjOs hrs
  exact ⟨n,r,a,U,s,b,V,hCode,hOldCode,hVertex,hOldVertex,hArrow⟩

def constructionSentence {k : Nat} (D I mul one q diagrams objImage objects S mapImage maps r Or a label : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul one))
    (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier D I diagrams))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage))
    (.imp (ForcingLabelSystem.objectFamily D diagrams objects)
    (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows D mul diagrams S))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps S mapImage))
    (.imp (ForcingLabelSystem.mapFamily objects S maps)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge objects r Or))
    (.imp (.mem (.bound a) (.bound D))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub D mul r a q))
    (.imp (.mem (.bound label) (.bound Or))
    (.existsE (.existsE (.conj (labelVertex D.succ.succ I.succ.succ mul.succ.succ q.succ.succ objects.succ.succ maps.succ.succ r.succ.succ a.succ.succ label.succ.succ 1) (.conj (ForcingComponentFibers.vertexFiber D.succ.succ mul.succ.succ objects.succ.succ maps.succ.succ 1 0) (.mem (.bound label.succ.succ) (.bound 0)))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ForcingLabelSystem.objectFamily_freeClosed,ForcingLabelSystem.mapFamily_freeClosed,labelVertex_freeClosed,ForcingComponentFibers.vertexFiber_freeClosed]

theorem construction_models {k : Nat} (D I mul one q diagrams objImage objects S mapImage maps r Or a label : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence D I mul one q diagrams objImage objects S mapImage maps r Or a label)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramCarrier.carrier_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingLabelSystem.objectFamily_semantics hM,
    ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingLabelSystem.mapFamily_semantics hM,
    KuratowskiZF.source_edge,labelVertex_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM,ForcingDiagramOrder.sub_semantics (M := M)]
  exact construct hM

theorem construction_kernel_certificate {k : Nat} (D I mul one q diagrams objImage objects S mapImage maps r Or a label : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence D I mul one q diagrams objImage objects S mapImage maps r Or a label)) := by
  apply ModelTransfer.derives
  intro M hM
  exact construction_models D I mul one q diagrams objImage objects S mapImage maps r Or a label hM

def arrowSentence {k : Nat} (D I mul one q diagrams objImage objects S mapImage maps r Or a label v old s b V X : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul one))
    (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier D I diagrams))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage))
    (.imp (ForcingLabelSystem.objectFamily D diagrams objects)
    (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows D mul diagrams S))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps S mapImage))
    (.imp (ForcingLabelSystem.mapFamily objects S maps)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge objects r Or))
    (.imp (labelVertex D I mul q objects maps r a label v)
    (.imp (ConstructionComponentCarrier.code old s b V)
    (.imp (ConstructionComponentVertices.vertex D I mul q s b V)
    (.imp (ForcingComponentFibers.vertexFiber D mul objects maps old X)
    (.imp (.mem (.bound label) (.bound X))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.le D mul r s))
    (.existsE (ConstructionComponentCofinal.encodedArrow D.succ I.succ mul.succ q.succ v.succ old.succ 0))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ForcingLabelSystem.objectFamily_freeClosed,ForcingLabelSystem.mapFamily_freeClosed,labelVertex_freeClosed,ConstructionComponentCarrier.code_freeClosed,ConstructionComponentVertices.vertex_freeClosed,ForcingComponentFibers.vertexFiber_freeClosed,ConstructionComponentCofinal.encodedArrow_freeClosed]

theorem arrow_models {k : Nat} (D I mul one q diagrams objImage objects S mapImage maps r Or a label v old s b V X : Fin k) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (arrowSentence D I mul one q diagrams objImage objects S mapImage maps r Or a label v old s b V X)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramCarrier.carrier_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingLabelSystem.objectFamily_semantics hM,
    ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingLabelSystem.mapFamily_semantics hM,
    KuratowskiZF.source_edge,labelVertex_semantics hM,ConstructionComponentCarrier.code_semantics hM,ConstructionComponentVertices.vertex_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM,ConstructionComponentCofinal.encodedArrow_semantics hM,ForcingDiagramOrder.le_semantics (M := M)]
  exact labelVertex_arrow hM

theorem arrow_kernel_certificate {k : Nat} (D I mul one q diagrams objImage objects S mapImage maps r Or a label v old s b V X : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (arrowSentence D I mul one q diagrams objImage objects S mapImage maps r Or a label v old s b V X)) := by
  apply ModelTransfer.derives
  intro M hM
  exact arrow_models D I mul one q diagrams objImage objects S mapImage maps r Or a label v old s b V X hM

end PPAC.Migration.ForcingLabelVertices
