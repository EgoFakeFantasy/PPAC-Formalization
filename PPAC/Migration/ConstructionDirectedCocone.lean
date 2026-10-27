/- Pinned MonoidTowers.DirectedColimit.cocone:84. Collect the unique
canonical stage graphs using existing Replacement and function construction.
Naturality and all original weighted/pointed/conservative leg fields follow
for this SAME actual internal family. No object Choice premise. -/
import PPAC.Migration.ConstructionDirectedLiftSyntax

namespace PPAC.Migration.ConstructionDirectedCocone
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionDirectedSystem
open ConstructionDirectedMonoidData (Family)
open ConstructionDirectedLimitCarrier (Representatives EqualityLaw)
open ConstructionDirectedWeightData (WeightFamily Stable)
open ConstructionDirectedLift (Legs WeightedLegs MarkLegs)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def StageMap (Domains L projection i f : M.Carrier .set) : Prop :=
  ∃ D, PureKuratowski.PairMember M i D Domains ∧ MapsTo D L f ∧
    ∀ x z, PureKuratowski.PairMember M x z f ↔
      (Project.FirstOrderSemantics.reduct M).mem x D ∧ Product projection i x z

def Cocone (J E Domains F L projection K : M.Carrier .set) : Prop :=
  WeightFamily J Domains L K ∧ Stable J E Domains F K ∧
    ∀ i D ki, (Project.FirstOrderSemantics.reduct M).mem i J →
      PureKuratowski.PairMember M i D Domains → PureKuratowski.PairMember M i ki K →
      ∀ x z, PureKuratowski.PairMember M x z ki ↔
        (Project.FirstOrderSemantics.reduct M).mem x D ∧ Product projection i x z

def stageMap {m : Nat} (Domains L projection i f : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge Domains.succ i.succ (0 : Fin (m+1))))
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo f.succ (0 : Fin (m+1)) L.succ)) (.forallE
  (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ (1 : Fin (m+3)) (0 :
  Fin (m+3)))) (.conj (.mem (.bound (1 : Fin (m+3))) (.bound (0 : Fin (m+1)).succ.succ))
  (ProjectSyntax.encode id (ForcingDiagramOrder.product projection.succ.succ.succ i.succ.succ.succ (1 : Fin
  (m+3)) (0 : Fin (m+3)))))))))))

theorem stageMap_freeClosed {m : Nat} (Domains L projection i f : Fin m) :
    (stageMap Domains L projection i f).FreeClosed := by
  simp -implicitDefEqProofs [stageMap,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem stageMap_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (Domains L projection i f : Fin m) :
    Project.Formula.satisfies env (stageMap Domains L projection i f) ↔ StageMap (env.bound Domains) (env.bound L) (env.bound projection) (env.bound i) (env.bound f) := by
  simp only [stageMap,StageMap,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingSupportSize.mapsTo_semantics (M := M),ForcingDiagramOrder.product_semantics (M := M)]
  rfl


def cocone {m : Nat} (J E Domains F L projection K : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionDirectedWeightData.weightFamily J Domains L K) (.conj
  (ConstructionDirectedWeightData.stable J E Domains F K) (.forallE (.forallE (.forallE (.imp (.mem (.bound
  (2 : Fin (m+3))) (.bound J.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Domains.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge K.succ.succ.succ (2 : Fin (m+3)) (0 : Fin (m+3)))) (.forallE (.forallE (.iff
  (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin (m+3)).succ.succ (1 : Fin (m+5)) (0 : Fin
  (m+5)))) (.conj (.mem (.bound (1 : Fin (m+5))) (.bound (1 : Fin (m+3)).succ.succ)) (ProjectSyntax.encode
  id (ForcingDiagramOrder.product projection.succ.succ.succ.succ.succ (2 : Fin (m+3)).succ.succ (1 : Fin
  (m+5)) (0 : Fin (m+5))))))))))))))))

theorem cocone_freeClosed {m : Nat} (J E Domains F L projection K : Fin m) :
    (cocone J E Domains F L projection K).FreeClosed := by
  simp -implicitDefEqProofs [cocone,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionDirectedWeightData.weightFamily_freeClosed,ConstructionDirectedWeightData.stable_freeClosed]

theorem cocone_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Domains F L projection K : Fin m) :
    Project.Formula.satisfies env (cocone J E Domains F L projection K) ↔ Cocone (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound L) (env.bound projection) (env.bound K) := by
  simp only [cocone,Cocone,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionDirectedWeightData.weightFamily_semantics hM,ConstructionDirectedWeightData.stable_semantics hM,ForcingDiagramOrder.product_semantics (M := M)]
  rfl


theorem stage_map_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {J Domains L projection i f g : M.Carrier .set}
    (hFn : ForcingConditionGraphs.FunctionOn J Domains)
    (hf : StageMap Domains L projection i f) (hg : StageMap Domains L projection i g) : f = g := by
  obtain ⟨D,hD,hf,hFG⟩ := hf
  obtain ⟨D',hD',hg,hGG⟩ := hg
  have heq := ForcingConditionGraphs.function_unique hFn hD hD'
  subst D'
  exact SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM D L f).mp hf).1.1
    ((ForcingSupportSize.native_mapsTo hM D L g).mp hg).1.1
    (fun x z => (hFG x z).trans (hGG x z).symm)

theorem exists_cocone (hM : FirstOrder.Theory.Models M nativeZF)
    {J E Domains F C L projection : M.Carrier .set}
    (hFn : ForcingConditionGraphs.FunctionOn J Domains)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hEq : EqualityLaw J E Domains F projection) :
    ∃ K, Cocone J E Domains F L projection K := by
  let schema : Project.BinarySchema 3 := {
    body := stageMap 2 3 4 1 0
    freeClosed := stageMap_freeClosed _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases Domains (Fin.cases L (fun _ => projection)), free := fun _ => J }
  have he (i f) : schema.denote env i f ↔ StageMap Domains L projection i f :=
    stageMap_semantics hM ((env.push i).push f) 2 3 4 1 0
  have ht : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i J → ∃ f, schema.denote env i f := by
    intro i hi
    obtain ⟨D,hD,_⟩ := hFn.2 i hi
    obtain ⟨f,hf,hFG,_⟩ := ConstructionDirectedLimitCarrier.exists_stage_map hM hC hp hE hT hEq hi hD
    exact ⟨f,(he i f).mpr ⟨D,hD,hf,hFG⟩⟩
  have hu : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i J → ∀ f g,
      schema.denote env i f → schema.denote env i g → f = g :=
    fun _ _ _ _ hf hg => stage_map_unique hM hFn ((he _ _).mp hf) ((he _ _).mp hg)
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨A,hA⟩ := ZF.exists_functionalImageOn hZF schema env J ht hu
  obtain ⟨K,hK,hKG⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (KuratowskiZF.interpretation hM)
    schema env ht hu (fun i f hi hf => (hA f).mpr ⟨i,hi,hf⟩)
  have hk := (ForcingSupportSize.native_mapsTo hM J A K).mpr hK
  have hStage : ∀ i D ki, (Project.FirstOrderSemantics.reduct M).mem i J →
      PureKuratowski.PairMember M i D Domains → PureKuratowski.PairMember M i ki K →
      MapsTo D L ki ∧ (∀ x z, PureKuratowski.PairMember M x z ki ↔
        (Project.FirstOrderSemantics.reduct M).mem x D ∧ Product projection i x z) := by
    intro i D ki _ hD hki
    obtain ⟨D',hD',hki',hFG⟩ := (he i ki).mp ((hKG i ki).mp hki).2
    have hd := ForcingConditionGraphs.function_unique hFn hD' hD
    subst D'
    exact ⟨hki',hFG⟩
  refine ⟨K,⟨hk.1,fun i D ki hi hD hki => (hStage i D ki hi hD hki).1⟩,?_,
    fun i D ki hi hD hki => (hStage i D ki hi hD hki).2⟩
  intro i j x y r ki kj hij hTrans hki hkj hxr
  obtain ⟨Di,hDi,_⟩ := hFn.2 i hTrans.1.1
  obtain ⟨Dj,hDj,_⟩ := hFn.2 j hTrans.2.1.1
  have hPX := ((hStage i Di ki hTrans.1.1 hDi hki).2 x r).mp hxr |>.2
  obtain ⟨s,_,hPY⟩ := ConstructionDirectedLimitCarrier.projected_total hM hC hp hTrans.2.1
  have hrs := ConstructionDirectedLimitCarrier.of_map hE hT hEq hij hTrans hPX hPY
  obtain ⟨D0,hD0,hy0⟩ := hTrans.2.1.2
  have hdd := ForcingConditionGraphs.function_unique hFn hD0 hDj
  subst D0
  exact ((hStage j Dj kj hTrans.2.1.1 hDj hkj).2 y r).mpr ⟨hy0,hrs.symm ▸ hPY⟩

theorem hom_fields (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top J E Domains F Muls Units Heights Costs Marks C L projection B G unit mark HL LC K : M.Carrier .set}
    (hFam : Family J Domains Muls Units) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hCons : ConstructionDirectedConservativeData.ConservativeTransitions J E Domains F Muls)
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hL : ConstructionDirectedLimitCarrier.Carrier J E Domains F C L)
    (hP : ConstructionDirectedLimitCarrier.Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection) (hG : MapsTo B L G)
    (hGraph : ConstructionDirectedProduct.Graph J Domains Muls projection G)
    (hMon : ForcingDiagramPoset.LeftCancelMonoid L G unit)
    (hImage : ConstructionDirectedMonoid.UnitImage J Domains Units projection unit)
    (hMarks : ConstructionDirectedMarks.MarkFamily J Domains Units Marks)
    (hMarkImage : ConstructionDirectedMarks.MarkImage J Marks projection mark)
    (hWeights : ConstructionDirectedHeightCost.Laws hM w Q R top J Domains Muls Heights Costs L projection G HL LC)
    (hK : Cocone J E Domains F L projection K) :
    Legs J Domains Muls Units K L G unit ∧ MarkLegs J Marks K mark ∧
      WeightedLegs J Domains Muls Heights Costs K HL LC L G := by
  refine ⟨?_,?_,?_⟩
  · intro i D mul e ki hi hD hm he hki
    have hFG := hK.2.2 i D ki hi hD hki
    have hHom := ConstructionDirectedMonoid.stage_hom hFam hGraph hImage hi hD hm he hFG
    exact ⟨hHom.1,hHom.2,ConstructionDirectedConservative.stage_conservative hM hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hi hD hm he (hK.1.2 i D ki hi hD hki) hFG⟩
  · intro i a ki hi ha hki
    obtain ⟨D,mul,e,hD,_,he,_⟩ := ConstructionDirectedMonoidData.family_at hFam hi
    exact (hK.2.2 i D ki hi hD hki a mark).mpr ⟨(hMarks.2 i D e a hi hD he ha).1,hMarkImage i a hi ha⟩
  · intro i D mul Hi Ci ki hi hD hm hHi hCi hki
    obtain ⟨_,_,_,_,_,_,_,_,hOld⟩ := hWeights
    have hFields := hOld i D mul Hi Ci ki hi hD hm hHi hCi (hK.1.2 i D ki hi hD hki) (hK.2.2 i D ki hi hD hki)
    refine ⟨fun x fx r hx => (hFields.1 x fx r hx).symm,
      fun x fx r hx => (hFields.2.1 x fx r hx).symm,?_⟩
    intro x y fx fy cap hfx hfy hCap
    obtain ⟨_,_,cap0,_,_,_,hCap0,hCapL,_⟩ := hFields.2.2 x y fx fy hfx hfy
    have heq := ConstructionProbeCostSupremum.cap_unique hM hCap hCap0
    subst cap
    exact hCapL

end PPAC.Migration.ConstructionDirectedCocone
