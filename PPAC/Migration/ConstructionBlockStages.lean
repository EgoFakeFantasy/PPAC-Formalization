/- Pinned BlockTowers.blockMap/blockStage/naturality/mono/limit and
Hom.range_comp_of_surjective. Reuse ConstructionTowerSuccessor.exists_family
and stable_comp for ALL actual composites; construct their exact range graph
inside the SAME terminal carrier. No replacement terminal object or new
recursor. Consumers: literal block stages and the flattened Timeline. -/
import PPAC.Migration.ConstructionTowerSuccessor
import PPAC.Migration.ConstructionFirstAppearance

namespace PPAC.Migration.ConstructionBlockStages
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingConditionGraphs (FunctionOn function_input function_unique)
open ForcingSupportSize (MapsTo)
open ForcingSupportedNames (Range)
open ConstructionRealCuts (Subset)
open ConstructionDirectedWeightData (WeightFamily Stable)
open ConstructionDirectedSystem (Transition TransitionLaws)
open ConstructionProbeMappedPath (NodeMap)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def StageRange (Domains Legs i R : M.Carrier .set) : Prop :=
  ∃ D f, PureKuratowski.PairMember M i D Domains ∧ PureKuratowski.PairMember M i f Legs ∧ Range D f R

def Ranges (J Domains Legs Images : M.Carrier .set) : Prop :=
  FunctionOn J Images ∧ ∀ i R, PureKuratowski.PairMember M i R Images ↔
    (Project.FirstOrderSemantics.reduct M).mem i J ∧ StageRange Domains Legs i R

def MonotoneImages (J E Images : M.Carrier .set) : Prop := ∀ i j A B,
  (Project.FirstOrderSemantics.reduct M).mem i J → (Project.FirstOrderSemantics.reduct M).mem j J →
  PureKuratowski.PairMember M i j E → PureKuratowski.PairMember M i A Images →
    PureKuratowski.PairMember M j B Images → Subset A B

def Bounded (V Images : M.Carrier .set) : Prop := ∀ i R,
  PureKuratowski.PairMember M i R Images → Subset R V

/-- The actual preimage/transition witnesses supplied by continuous histories. -/
def Prior (J r Domains F j : M.Carrier .set) : Prop := ∀ D x,
  PureKuratowski.PairMember M j D Domains → (Project.FirstOrderSemantics.reduct M).mem x D →
    ∃ i y, (Project.FirstOrderSemantics.reduct M).mem i J ∧ PureKuratowski.PairMember M i j r ∧
      Transition J Domains F i j y x

def Earlier (J r Images j : M.Carrier .set) : Prop := ∀ x,
  ConstructionFirstAppearance.At Images j x → ∃ i,
    (Project.FirstOrderSemantics.reduct M).mem i J ∧ PureKuratowski.PairMember M i j r ∧
      ConstructionFirstAppearance.At Images i x

def Covers (J Domains K N : M.Carrier .set) : Prop := ∀ y,
  (Project.FirstOrderSemantics.reduct M).mem y N → ∃ i D f x,
    (Project.FirstOrderSemantics.reduct M).mem i J ∧ PureKuratowski.PairMember M i D Domains ∧
    PureKuratowski.PairMember M i f K ∧ (Project.FirstOrderSemantics.reduct M).mem x D ∧
    PureKuratowski.PairMember M x y f

def ImageCover (J Images R : M.Carrier .set) : Prop := ∀ z,
  (Project.FirstOrderSemantics.reduct M).mem z R → ∃ i,
    (Project.FirstOrderSemantics.reduct M).mem i J ∧ ConstructionFirstAppearance.At Images i z

def Result (J E Domains F K O V Out Images : M.Carrier .set) : Prop :=
  ConstructionTowerSuccessor.Graph J Domains K O V Out ∧ WeightFamily J Domains V Out ∧
    ConstructionTowerSuccessor.CompositeFamily J K O Out ∧ Stable J E Domains F Out ∧
    Ranges J Domains Out Images ∧ Bounded V Images ∧ MonotoneImages J E Images

theorem range_exists (hM : FirstOrder.Theory.Models M nativeZF)
    {D V f : M.Carrier .set} (hf : MapsTo D V f) : ∃ R, Range D f R := by
  have hn := (ForcingSupportSize.native_mapsTo hM D V f).mp hf
  obtain ⟨R,hR⟩ := ZF.exists_range_of_setFunction (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) hn.1 hn.2.1
  exact ⟨R,fun z => ⟨fun hz => by
      obtain ⟨x,hxz⟩ := (hR z).mp hz
      exact ⟨x,hn.input_mem_of_pairMember hxz,hxz⟩,
    fun ⟨x,_,hxz⟩ => (hR z).mpr ⟨x,hxz⟩⟩⟩

theorem range_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {D f R S : M.Carrier .set} (hR : Range D f R) (hS : Range D f S) : R = S :=
  (ModelTransfer.extensionality hM).eq_of_same_members R S (fun z => (hR z).trans (hS z).symm)

theorem stageRange_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {J Domains Legs i R S : M.Carrier .set} (hD : FunctionOn J Domains) (hK : FunctionOn J Legs)
    (hR : StageRange Domains Legs i R) (hS : StageRange Domains Legs i S) : R = S := by
  obtain ⟨D,f,hDi,hfi,hR⟩ := hR
  obtain ⟨D',f',hDi',hfi',hS⟩ := hS
  have ed := function_unique hD hDi' hDi
  have ef := function_unique hK hfi' hfi
  subst D'; subst f'
  exact range_unique hM hR hS

def stageRange {m : Nat} (Domains Legs i R : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge Domains.succ.succ i.succ.succ
  1)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge Legs.succ.succ i.succ.succ 0))
  (ProjectSyntax.encode id (ForcingSupportedNames.range 1 0 R.succ.succ))))))

theorem stageRange_freeClosed {m : Nat} (Domains Legs i R : Fin m) :
    (stageRange Domains Legs i R).FreeClosed := by
  simp -implicitDefEqProofs [stageRange,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem stageRange_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (Domains Legs i R : Fin m) :
    Project.Formula.satisfies env (stageRange Domains Legs i R) ↔ StageRange (env.bound Domains) (env.bound Legs) (env.bound i) (env.bound R) := by
  simp only [stageRange,StageRange,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingSupportedNames.range_semantics (M := M)]
  rfl

def ranges {m : Nat} (J Domains Legs Images : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn Images J)) (.forallE (.forallE (.iff
  (ProjectSyntax.encode id (Source.SetLanguage.edge Images.succ.succ 1 0)) (.conj (.mem (.bound 1) (.bound
  J.succ.succ)) (stageRange Domains.succ.succ Legs.succ.succ 1 0))))))

theorem ranges_freeClosed {m : Nat} (J Domains Legs Images : Fin m) :
    (ranges J Domains Legs Images).FreeClosed := by
  simp -implicitDefEqProofs [ranges,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,stageRange_freeClosed]

theorem ranges_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains Legs Images : Fin m) :
    Project.Formula.satisfies env (ranges J Domains Legs Images) ↔ Ranges (env.bound J) (env.bound Domains) (env.bound Legs) (env.bound Images) := by
  simp only [ranges,Ranges,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,stageRange_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M)]
  rfl

def monotoneImages {m : Nat} (J E Images : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 3) (.bound J.succ.succ.succ.succ)) (.imp (.mem
  (.bound 2) (.bound J.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  E.succ.succ.succ.succ 3 2)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Images.succ.succ.succ.succ 3 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Images.succ.succ.succ.succ 2 0)) (Project.Formula.subset (.bound 1) (.bound 0)))))))))))

theorem monotoneImages_freeClosed {m : Nat} (J E Images : Fin m) :
    (monotoneImages J E Images).FreeClosed := by
  simp -implicitDefEqProofs [monotoneImages,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem monotoneImages_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Images : Fin m) :
    Project.Formula.satisfies env (monotoneImages J E Images) ↔ MonotoneImages (env.bound J) (env.bound E) (env.bound Images) := by
  simp only [monotoneImages,MonotoneImages,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def bounded {m : Nat} (V Images : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Images.succ.succ 1 0))
  (Project.Formula.subset (.bound 0) (.bound V.succ.succ)))))

theorem bounded_freeClosed {m : Nat} (V Images : Fin m) :
    (bounded V Images).FreeClosed := by
  simp -implicitDefEqProofs [bounded,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem bounded_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (V Images : Fin m) :
    Project.Formula.satisfies env (bounded V Images) ↔ Bounded (env.bound V) (env.bound Images) := by
  simp only [bounded,Bounded,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def prior {m : Nat} (J r Domains F j : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Domains.succ.succ j.succ.succ
  1)) (.imp (.mem (.bound 0) (.bound 1)) (.existsE (.existsE (.conj (.mem (.bound 1) (.bound
  J.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge r.succ.succ.succ.succ 1
  j.succ.succ.succ.succ)) (ConstructionDirectedSystem.transition J.succ.succ.succ.succ
  Domains.succ.succ.succ.succ F.succ.succ.succ.succ 1 j.succ.succ.succ.succ 0 2)))))))))

theorem prior_freeClosed {m : Nat} (J r Domains F j : Fin m) :
    (prior J r Domains F j).FreeClosed := by
  simp -implicitDefEqProofs [prior,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionDirectedSystem.transition_freeClosed]

theorem prior_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J r Domains F j : Fin m) :
    Project.Formula.satisfies env (prior J r Domains F j) ↔ Prior (env.bound J) (env.bound r) (env.bound Domains) (env.bound F) (env.bound j) := by
  simp only [prior,Prior,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionDirectedSystem.transition_semantics hM]
  rfl

def earlier {m : Nat} (J r Images j : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (ConstructionFirstAppearance.atStage Images.succ j.succ 0) (.existsE (.conj (.mem (.bound 0)
  (.bound J.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge r.succ.succ 0 j.succ.succ))
  (ConstructionFirstAppearance.atStage Images.succ.succ 0 1))))))

theorem earlier_freeClosed {m : Nat} (J r Images j : Fin m) :
    (earlier J r Images j).FreeClosed := by
  simp -implicitDefEqProofs [earlier,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionFirstAppearance.atStage_freeClosed]

theorem earlier_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J r Images j : Fin m) :
    Project.Formula.satisfies env (earlier J r Images j) ↔ Earlier (env.bound J) (env.bound r) (env.bound Images) (env.bound j) := by
  simp only [earlier,Earlier,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionFirstAppearance.atStage_semantics hM]
  rfl

def covers {m : Nat} (J Domains K N : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (.mem (.bound 0) (.bound N.succ)) (.existsE (.existsE (.existsE (.existsE (.conj (.mem
  (.bound 3) (.bound J.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  Domains.succ.succ.succ.succ.succ 3 2)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  K.succ.succ.succ.succ.succ 3 1)) (.conj (.mem (.bound 0) (.bound 2)) (ProjectSyntax.encode id
  (Source.SetLanguage.edge 1 0 4))))))))))))

theorem covers_freeClosed {m : Nat} (J Domains K N : Fin m) :
    (covers J Domains K N).FreeClosed := by
  simp -implicitDefEqProofs [covers,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem covers_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains K N : Fin m) :
    Project.Formula.satisfies env (covers J Domains K N) ↔ Covers (env.bound J) (env.bound Domains) (env.bound K) (env.bound N) := by
  simp only [covers,Covers,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def imageCover {m : Nat} (J Images R : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (.mem (.bound 0) (.bound R.succ)) (.existsE (.conj (.mem (.bound 0) (.bound J.succ.succ))
  (ConstructionFirstAppearance.atStage Images.succ.succ 0 1)))))

theorem imageCover_freeClosed {m : Nat} (J Images R : Fin m) :
    (imageCover J Images R).FreeClosed := by
  simp -implicitDefEqProofs [imageCover,Definitional.Formula.FreeClosed,ConstructionFirstAppearance.atStage_freeClosed]

theorem imageCover_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Images R : Fin m) :
    Project.Formula.satisfies env (imageCover J Images R) ↔ ImageCover (env.bound J) (env.bound Images) (env.bound R) := by
  simp only [imageCover,ImageCover,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ConstructionFirstAppearance.atStage_semantics hM]
  rfl

def result {m : Nat} (J E Domains F K O V Out Images : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionTowerSuccessor.graph J Domains K O V Out) (.conj
  (ConstructionDirectedWeightData.weightFamily J Domains V Out) (.conj
  (ConstructionTowerSuccessor.compositeFamily J K O Out) (.conj (ConstructionDirectedWeightData.stable J E
  Domains F Out) (.conj (ranges J Domains Out Images) (.conj (bounded V Images) (monotoneImages J E
  Images)))))))

theorem result_freeClosed {m : Nat} (J E Domains F K O V Out Images : Fin m) :
    (result J E Domains F K O V Out Images).FreeClosed := by
  simp -implicitDefEqProofs [result,Definitional.Formula.FreeClosed,ConstructionTowerSuccessor.graph_freeClosed,ConstructionDirectedWeightData.weightFamily_freeClosed,ConstructionTowerSuccessor.compositeFamily_freeClosed,ConstructionDirectedWeightData.stable_freeClosed,ranges_freeClosed,bounded_freeClosed,monotoneImages_freeClosed]

theorem result_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Domains F K O V Out Images : Fin m) :
    Project.Formula.satisfies env (result J E Domains F K O V Out Images) ↔ Result (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound K) (env.bound O) (env.bound V) (env.bound Out) (env.bound Images) := by
  simp only [result,Result,
    Project.Formula.satisfies_conj_iff,ConstructionTowerSuccessor.graph_semantics hM,ConstructionDirectedWeightData.weightFamily_semantics hM,ConstructionTowerSuccessor.compositeFamily_semantics hM,ConstructionDirectedWeightData.stable_semantics hM,ranges_semantics hM,bounded_semantics hM,monotoneImages_semantics hM]

theorem exists_ranges (hM : FirstOrder.Theory.Models M nativeZF)
    {J Domains V Legs : M.Carrier .set} (hD : FunctionOn J Domains) (hL : WeightFamily J Domains V Legs) :
    ∃ Images, Ranges J Domains Legs Images := by
  let schema : Project.BinarySchema 2 := {
    body := stageRange 2 3 1 0
    freeClosed := stageRange_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases Domains (fun _ => Legs), free := fun _ => J }
  have he i R : schema.denote env i R ↔ StageRange Domains Legs i R :=
    stageRange_semantics hM ((env.push i).push R) 2 3 1 0
  have ht : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i J → ∃ R, schema.denote env i R := by
    intro i hi
    obtain ⟨D,hDi,_⟩ := hD.2 i hi
    obtain ⟨f,hfi,_⟩ := hL.1.2 i hi
    obtain ⟨R,hR⟩ := range_exists hM (hL.2 i D f hi hDi hfi)
    exact ⟨R,(he i R).mpr ⟨D,f,hDi,hfi,hR⟩⟩
  have hu : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i J → ∀ R S,
      schema.denote env i R → schema.denote env i S → R = S :=
    fun _ _ _ _ hr hs => stageRange_unique hM hD hL.1 ((he _ _).mp hr) ((he _ _).mp hs)
  obtain ⟨A,hA⟩ := ZF.exists_functionalImageOn (ModelTransfer.project_models_iff.mp hM) schema env J ht hu
  obtain ⟨Images,hImages,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) schema env ht hu
    (fun i R hi hR => (hA R).mpr ⟨i,hi,hR⟩)
  exact ⟨Images,((ForcingSupportSize.native_mapsTo hM J A Images).mpr hImages).1,
    fun i R => (hGraph i R).trans (and_congr_right fun _ => he i R)⟩

theorem range_at {J Domains Legs Images i D f R : M.Carrier .set}
    (hD : FunctionOn J Domains) (hL : FunctionOn J Legs) (hR : Ranges J Domains Legs Images)
    (hDi : PureKuratowski.PairMember M i D Domains) (hfi : PureKuratowski.PairMember M i f Legs)
    (hRi : PureKuratowski.PairMember M i R Images) : Range D f R := by
  obtain ⟨_,D',f',hDi',hfi',hr⟩ := (hR.2 i R).mp hRi
  have ed := function_unique hD hDi' hDi
  have ef := function_unique hL hfi' hfi
  subst D'; subst f'
  exact hr

theorem ranges_bounded {J Domains V Legs Images : M.Carrier .set}
    (hL : WeightFamily J Domains V Legs) (hR : Ranges J Domains Legs Images) : Bounded V Images := by
  intro i R hRi z hz
  obtain ⟨hi,D,f,hDi,hfi,hr⟩ := (hR.2 i R).mp hRi
  obtain ⟨x,_,hxz⟩ := (hr z).mp hz
  exact (hL.2 i D f hi hDi hfi).2 x z hxz

theorem ranges_mono {J E Domains F Legs Images : M.Carrier .set}
    (hD : FunctionOn J Domains)
    (hT : TransitionLaws J E Domains F) (hs : Stable J E Domains F Legs)
    (hR : Ranges J Domains Legs Images) : MonotoneImages J E Images := by
  intro i j A B hi hj hij hAi hBj z hz
  obtain ⟨_,Di,fi,hDi,hfi,hA⟩ := (hR.2 i A).mp hAi
  obtain ⟨_,Dj,fj,hDj,hfj,hB⟩ := (hR.2 j B).mp hBj
  obtain ⟨x,hx,hxz⟩ := (hA z).mp hz
  obtain ⟨y,hxy⟩ := hT.1 i j x ⟨hi,Di,hDi,hx⟩ hj hij
  obtain ⟨Dj',hDj',hy⟩ := hxy.2.1.2
  have ed := function_unique hD hDj' hDj
  subst Dj'
  exact (hB z).mpr ⟨y,hy,hs i j x y z fi fj hij hxy hfi hfj hxz⟩

/-- Source blockMap is the already constructed whole composite family. -/
theorem exists_block (hM : FirstOrder.Theory.Models M nativeZF)
    {J E Domains F K N O V : M.Carrier .set} (hD : FunctionOn J Domains)
    (hK : WeightFamily J Domains N K) (hs : Stable J E Domains F K)
    (hT : TransitionLaws J E Domains F) (hO : MapsTo N V O) :
    ∃ Out Images, Result J E Domains F K O V Out Images := by
  obtain ⟨Out,hG,hOut,hComp,_⟩ := ConstructionTowerSuccessor.exists_family hM hD hK hO
  have hStable := ConstructionTowerSuccessor.stable_comp hK hs hComp
  obtain ⟨Images,hR⟩ := exists_ranges hM hD hOut
  exact ⟨Out,Images,hG,hOut,hComp,hStable,hR,ranges_bounded hOut hR,
    ranges_mono hD hT hStable hR⟩

/-- The image of a surjective initial/top map is the SAME literal range,
not merely an isomorphic carrier. Used by blockStage_base/top/boundary. -/
theorem range_comp_surjective (hM : FirstOrder.Theory.Models M nativeZF)
    {D N f O out A B : M.Carrier .set} (hf : MapsTo D N f)
    (hOnto : ∀ y, (Project.FirstOrderSemantics.reduct M).mem y N →
      ∃ x, (Project.FirstOrderSemantics.reduct M).mem x D ∧ PureKuratowski.PairMember M x y f)
    (hComp : NodeMap f O out) (hA : Range D out A) (hB : Range N O B) : A = B := by
  apply (ModelTransfer.extensionality hM).eq_of_same_members
  intro z
  constructor
  · intro hz
    obtain ⟨x,_,hxz⟩ := (hA z).mp hz
    obtain ⟨y,hxy,hyz⟩ := (hComp x z).mp hxz
    exact (hB z).mpr ⟨y,hf.2 x y hxy,hyz⟩
  · intro hz
    obtain ⟨y,hy,hyz⟩ := (hB z).mp hz
    obtain ⟨x,hx,hxy⟩ := hOnto y hy
    exact (hA z).mpr ⟨x,hx,(hComp x z).mpr ⟨y,hxy,hyz⟩⟩

/-- Source blockStage_limit: actual earlier representatives and naturality
transport to the precise earlier literal range, with the SAME element z. -/
theorem ranges_earlier {J E r Domains F V Legs Images j : M.Carrier .set}
    (hD : FunctionOn J Domains) (hL : WeightFamily J Domains V Legs)
    (hs : Stable J E Domains F Legs) (hR : Ranges J Domains Legs Images)
    (hLE : ∀ i k, PureKuratowski.PairMember M i k r → PureKuratowski.PairMember M i k E)
    (hp : Prior J r Domains F j) : Earlier J r Images j := by
  intro z hz
  obtain ⟨R,hRj,hz⟩ := hz
  obtain ⟨hj,D,f,hDj,hfj,hr⟩ := (hR.2 j R).mp hRj
  obtain ⟨x,hx,hxz⟩ := (hr z).mp hz
  obtain ⟨i,y,hi,hij,hyx⟩ := hp D x hDj hx
  obtain ⟨Di,hDi,hy⟩ := hyx.1.2
  obtain ⟨fi,hfi,_⟩ := hL.1.2 i hi
  obtain ⟨z',hyz',_⟩ := (hL.2 i Di fi hi hDi hfi).1.2 y hy
  have hxz' := hs i j y x z' fi f (hLE i j hij) hyx hfi hfj hyz'
  have eq := function_unique (hL.2 j D f hj hDj hfj).1 hxz' hxz
  subst z'
  obtain ⟨A,hAi,_⟩ := hR.1.2 i hi
  exact ⟨i,hi,hij,A,hAi,(range_at hD hL.1 hR hDi hfi hAi z).mpr ⟨y,hy,hyz'⟩⟩

theorem ranges_cover {J Domains K N O V Out Images R : M.Carrier .set}
    (hD : FunctionOn J Domains) (hOut : WeightFamily J Domains V Out)
    (hComp : ConstructionTowerSuccessor.CompositeFamily J K O Out)
    (hR : Ranges J Domains Out Images) (hCover : Covers J Domains K N) (hRange : Range N O R) :
    ImageCover J Images R := by
  intro z hz
  obtain ⟨y,hy,hyz⟩ := (hRange z).mp hz
  obtain ⟨i,D,f,x,hi,hDi,hfi,hx,hxy⟩ := hCover y hy
  obtain ⟨out,hout,_⟩ := hOut.1.2 i hi
  obtain ⟨A,hAi,_⟩ := hR.1.2 i hi
  exact ⟨i,hi,A,hAi,(range_at hD hOut.1 hR hDi hout hAi z).mpr
    ⟨x,hx,((hComp i f out hi hfi hout) x z).mpr ⟨y,hxy,hyz⟩⟩⟩

/-- Source Subobject.range: multiplication, factors and actual conditional
joins are closed in the exact range of a conservative homomorphism. -/
theorem range_closed
    {D V mul G e unit f R : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hv : ForcingDiagramPoset.LeftCancelMonoid V G unit) (hc : ForcingDiagramPoset.Conical V G unit)
    (hf : ConstructionProbePushout.Hom D V mul G e unit f)
    (hCons : ConstructionProbeConservative.Conservative D V mul G f) (hR : Range D f R) :
    ConstructionConservativeHull.Closure V G unit R := by
  have hSub : Subset R V := by
    intro z hz
    obtain ⟨x,_,hxz⟩ := (hR z).mp hz
    exact hf.1.2 x z hxz
  refine ⟨hSub,(hR unit).mpr ⟨e,hm.1.1,hf.2.1⟩,?_,?_,?_⟩
  · intro x y z hx hy hxyz
    obtain ⟨a,ha,hax⟩ := (hR x).mp hx
    obtain ⟨b,hb,hby⟩ := (hR y).mp hy
    obtain ⟨c,hcD,habc⟩ := (hm.2.1 a ha).1 b hb
    obtain ⟨fc,hcfc,_⟩ := hf.1.1.2 c hcD
    have hxyfc := hf.2.2 a b c x y fc habc hax hby hcfc
    have eq := (hv.2.1 x (hSub x hx)).2.1 y fc z (hSub y hy) hxyfc hxyz
    exact (hR z).mpr ⟨c,hcD,eq ▸ hcfc⟩
  · intro x y z hx hy hz hxzy
    obtain ⟨a,_,hax⟩ := (hR x).mp hx
    obtain ⟨b,_,hby⟩ := (hR y).mp hy
    obtain ⟨c,hcz⟩ := hCons.2.1 a b z x y hax hby hz hxzy
    exact (hR z).mpr ⟨c,function_input hf.1.1 hcz,hcz⟩
  · intro x y z hx hy hz hJoin
    obtain ⟨a,ha,hax⟩ := (hR x).mp hx
    obtain ⟨b,hb,hby⟩ := (hR y).mp hy
    have hzz : ConstructionBaseMonoid.Divides V G z z :=
      ⟨unit,hv.1.1,(hv.1.2 z hz z).2.mpr rfl⟩
    have hxyz := (hJoin z hz).mpr hzz
    obtain ⟨c,hcD,hac,hbc⟩ := hCons.2.2.2 a b x y hax hby ⟨z,hz,hxyz⟩
    obtain ⟨j,hj,hJoinD⟩ := hJ a b c ha hb hcD hac hbc
    obtain ⟨fj,hjfj,_⟩ := hf.1.1.2 j hj
    have hJoinV := hCons.2.2.1 a b j x y fj hax hby hjfj hJoinD
    have eq := ConstructionCountableConservativeHull.join_unique hv hc
      (Or.inl ⟨hf.1.2 j fj hjfj,hJoinV⟩) (Or.inl ⟨hz,hJoin⟩)
    exact (hR z).mpr ⟨j,hj,eq ▸ hjfj⟩

def constructionSentence {m : Nat} (J E Domains F K N O V : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn Domains J)) (.imp
    (ConstructionDirectedWeightData.weightFamily J Domains N K) (.imp (ConstructionDirectedWeightData.stable J
    E Domains F K) (.imp (ConstructionDirectedSystem.transitionLaws J E Domains F) (.imp (ProjectSyntax.encode
    id (Source.SetLanguage.mapsTo O N V)) (.existsE (.existsE (result J.succ.succ E.succ.succ
    Domains.succ.succ F.succ.succ K.succ.succ O.succ.succ V.succ.succ 1 0))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionDirectedWeightData.weightFamily_freeClosed,ConstructionDirectedWeightData.stable_freeClosed,ConstructionDirectedSystem.transitionLaws_freeClosed,result_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (J E Domains F K N O V : Fin m) : (Project.fo_sentence (constructionSentence J E Domains F K N O V)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence J E Domains F K N O V)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionDirectedWeightData.weightFamily_semantics hM,ConstructionDirectedWeightData.stable_semantics hM,ConstructionDirectedSystem.transitionLaws_semantics hM,result_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M)]
  exact exists_block hM

theorem construction_kernel_certificate {m : Nat} (J E Domains F K N O V : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence J E Domains F K N O V)) := by
  apply ModelTransfer.derives
  intro M hM
  exact construction_models hM J E Domains F K N O V

def boundarySentence {m : Nat} (D N f O out A B : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo f D N)) (.imp (.forallE (.imp (.mem (.bound 0)
    (.bound N.succ)) (.existsE (.conj (.mem (.bound 0) (.bound D.succ.succ)) (ProjectSyntax.encode id
    (Source.SetLanguage.edge f.succ.succ 0 1)))))) (.imp (ConstructionProbeMappedPathSyntax.nodeMap f O out)
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range D out A)) (.imp (ProjectSyntax.encode id
    (ForcingSupportedNames.range N O B)) (Project.Formula.extensionalEq (.bound A) (.bound B)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed]

theorem boundary_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (D N f O out A B : Fin m) : (Project.fo_sentence (boundarySentence D N f O out A B)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (boundarySentence D N f O out A B)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),ForcingSupportedNames.range_semantics (M := M)]
  exact range_comp_surjective hM

theorem boundary_kernel_certificate {m : Nat} (D N f O out A B : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (boundarySentence D N f O out A B)) := by
  apply ModelTransfer.derives
  intro M hM
  exact boundary_models hM D N f O out A B

def limitSentence {m : Nat} (J E r Domains F V Legs Images j : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn Domains J)) (.imp
    (ConstructionDirectedWeightData.weightFamily J Domains V Legs) (.imp
    (ConstructionDirectedWeightData.stable J E Domains F Legs) (.imp (ranges J Domains Legs Images) (.imp
    (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge r.succ.succ 1 0))
    (ProjectSyntax.encode id (Source.SetLanguage.edge E.succ.succ 1 0))))) (.imp (prior J r Domains F j)
    (earlier J r Images j)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionDirectedWeightData.weightFamily_freeClosed,ConstructionDirectedWeightData.stable_freeClosed,ranges_freeClosed,prior_freeClosed,earlier_freeClosed]

theorem limit_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (J E r Domains F V Legs Images j : Fin m) : (Project.fo_sentence (limitSentence J E r Domains F V Legs Images j)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (limitSentence J E r Domains F V Legs Images j)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionDirectedWeightData.weightFamily_semantics hM,ConstructionDirectedWeightData.stable_semantics hM,ranges_semantics hM,prior_semantics hM,earlier_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M)]
  exact ranges_earlier

theorem limit_kernel_certificate {m : Nat} (J E r Domains F V Legs Images j : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (limitSentence J E r Domains F V Legs Images j)) := by
  apply ModelTransfer.derives
  intro M hM
  exact limit_models hM J E r Domains F V Legs Images j

def coverageSentence {m : Nat} (J Domains K N O V Out Images R : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn Domains J)) (.imp
    (ConstructionDirectedWeightData.weightFamily J Domains V Out) (.imp
    (ConstructionTowerSuccessor.compositeFamily J K O Out) (.imp (ranges J Domains Out Images) (.imp (covers J
    Domains K N) (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range N O R)) (imageCover J Images
    R)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionDirectedWeightData.weightFamily_freeClosed,ConstructionTowerSuccessor.compositeFamily_freeClosed,ranges_freeClosed,covers_freeClosed,imageCover_freeClosed]

theorem coverage_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (J Domains K N O V Out Images R : Fin m) : (Project.fo_sentence (coverageSentence J Domains K N O V Out Images R)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (coverageSentence J Domains K N O V Out Images R)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionDirectedWeightData.weightFamily_semantics hM,ConstructionTowerSuccessor.compositeFamily_semantics hM,ranges_semantics hM,covers_semantics hM,imageCover_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),ForcingSupportedNames.range_semantics (M := M)]
  exact ranges_cover

theorem coverage_kernel_certificate {m : Nat} (J Domains K N O V Out Images R : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (coverageSentence J Domains K N O V Out Images R)) := by
  apply ModelTransfer.derives
  intro M hM
  exact coverage_models hM J Domains K N O V Out Images R

def subobjectSentence {m : Nat} (D V mul G e unit f R : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e)) (.imp
    (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid V G unit)) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.conical V G unit)) (.imp (ConstructionProbePushoutSyntax.hom D V mul G e unit f)
    (.imp (ConstructionProbeConservativeSyntax.conservative D V mul G f) (.imp (ProjectSyntax.encode id
    (ForcingSupportedNames.range D f R)) (ConstructionConservativeHull.closure V G unit R))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionProbePushoutSyntax.hom_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,ConstructionConservativeHull.closure_freeClosed]

theorem subobject_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (D V mul G e unit f R : Fin m) : (Project.fo_sentence (subobjectSentence D V mul G e unit f R)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (subobjectSentence D V mul G e unit f R)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionProbePushoutSyntax.hom_semantics hM,ConstructionProbeConservativeSyntax.conservative_semantics hM,ConstructionConservativeHull.closure_semantics hM,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ForcingSupportedNames.range_semantics (M := M)]
  exact range_closed

theorem subobject_kernel_certificate {m : Nat} (D V mul G e unit f R : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (subobjectSentence D V mul G e unit f R)) := by
  apply ModelTransfer.derives
  intro M hM
  exact subobject_models hM D V mul G e unit f R

end PPAC.Migration.ConstructionBlockStages
