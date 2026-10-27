/- Pinned MonoidRounds.Round.fromBase_naturality/map_succ and the actual
successor case of ConstructionIteration. Keep EVERY old stage, its varying
carrier and full weighted conservative map. Consume the SAME chosen round
successor; collect the entire family of composites as an internal function.
This is the actual successor-map update, not the completed ordinal tower. -/
import PPAC.Migration.ConstructionRoundSelection
import PPAC.Migration.ConstructionDirectedCocone

namespace PPAC.Migration.ConstructionTowerSuccessor
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (FunctionOn function_unique)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionRoundFields
open ConstructionDirectedWeightData (WeightFamily Stable)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (Domains K O W i out : M.Carrier .set) : Prop :=
  ∃ D ki, PureKuratowski.PairMember M i D Domains ∧ PureKuratowski.PairMember M i ki K ∧
    MapsTo D W out ∧ NodeMap ki O out

def Graph (J Domains K O W Out : M.Carrier .set) : Prop := ∀ i out,
  PureKuratowski.PairMember M i out Out ↔
    (Project.FirstOrderSemantics.reduct M).mem i J ∧ Value Domains K O W i out

def CompositeFamily (J K O Out : M.Carrier .set) : Prop := ∀ i ki out,
  (Project.FirstOrderSemantics.reduct M).mem i J →
    PureKuratowski.PairMember M i ki K → PureKuratowski.PairMember M i out Out → NodeMap ki O out

/-- Full original Object.Hom fields at EVERY displayed old stage. -/
def FullLegs (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q J Domains Muls Units Marks Heights Costs K N mulN eN markN HN CN : M.Carrier .set) : Prop :=
  FunctionOn J Domains ∧ FunctionOn J Muls ∧ FunctionOn J Units ∧ FunctionOn J Marks ∧
    FunctionOn J Heights ∧ FunctionOn J Costs ∧
    ∀ i D mul e mark H C ki, (Project.FirstOrderSemantics.reduct M).mem i J →
      PureKuratowski.PairMember M i D Domains → PureKuratowski.PairMember M i mul Muls →
      PureKuratowski.PairMember M i e Units → PureKuratowski.PairMember M i mark Marks →
      PureKuratowski.PairMember M i H Heights → PureKuratowski.PairMember M i C Costs →
      PureKuratowski.PairMember M i ki K → MapFields hM w Q D N mul mulN e eN mark markN H C HN CN ki

def ProfileLegs (w J Domains Muls K N mulN : M.Carrier .set) : Prop := ∀ i D mul ki,
  (Project.FirstOrderSemantics.reduct M).mem i J → PureKuratowski.PairMember M i D Domains →
    PureKuratowski.PairMember M i mul Muls → PureKuratowski.PairMember M i ki K →
      Profiles w D N mul mulN ki

def BaseNatural (J Origins K f : M.Carrier .set) : Prop := ∀ i fi ki,
  (Project.FirstOrderSemantics.reduct M).mem i J → PureKuratowski.PairMember M i fi Origins →
    PureKuratowski.PairMember M i ki K → NodeMap fi ki f

/-- If an old leg is the actual identity at the current stage, the new
transition is the SAME inclusion O, not an unspecified isomorphic map. -/
def SuccessorEquation (J K N O Out : M.Carrier .set) : Prop := ∀ i ki out,
  (Project.FirstOrderSemantics.reduct M).mem i J → PureKuratowski.PairMember M i ki K →
    ForcingConditionGraphs.IdentityGraph N ki → PureKuratowski.PairMember M i out Out → out = O

def value {m : Nat} (Domains K O W i out : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge Domains.succ.succ i.succ.succ
  (1 : Fin (m+2)))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge K.succ.succ i.succ.succ (0 :
  Fin (m+2)))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo out.succ.succ (1 : Fin (m+2))
  W.succ.succ)) (ConstructionProbeMappedPathSyntax.nodeMap (0 : Fin (m+2)) O.succ.succ out.succ.succ))))))

theorem value_freeClosed {m : Nat} (Domains K O W i out : Fin m) :
    (value Domains K O W i out).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (Domains K O W i out : Fin m) :
    Project.Formula.satisfies env (value Domains K O W i out) ↔ Value (env.bound Domains) (env.bound K) (env.bound O) (env.bound W) (env.bound i) (env.bound out) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbeMappedPathSyntax.nodeMap_semantics hM]
  rfl


def graph {m : Nat} (J Domains K O W Out : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge Out.succ.succ (1 : Fin (m+2)) (0
  : Fin (m+2)))) (.conj (.mem (.bound (1 : Fin (m+2))) (.bound J.succ.succ)) (value Domains.succ.succ
  K.succ.succ O.succ.succ W.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))))))

theorem graph_freeClosed {m : Nat} (J Domains K O W Out : Fin m) :
    (graph J Domains K O W Out).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,value_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains K O W Out : Fin m) :
    Project.Formula.satisfies env (graph J Domains K O W Out) ↔ Graph (env.bound J) (env.bound Domains) (env.bound K) (env.bound O) (env.bound W) (env.bound Out) := by
  simp only [graph,Graph,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,value_semantics hM]
  rfl


def compositeFamily {m : Nat} (J K O Out : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.imp (.mem (.bound (2 : Fin (m+3))) (.bound J.succ.succ.succ)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge K.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Out.succ.succ.succ (2 : Fin (m+3)) (0 : Fin (m+3))))
  (ConstructionProbeMappedPathSyntax.nodeMap (1 : Fin (m+3)) O.succ.succ.succ (0 : Fin (m+3)))))))))

theorem compositeFamily_freeClosed {m : Nat} (J K O Out : Fin m) :
    (compositeFamily J K O Out).FreeClosed := by
  simp -implicitDefEqProofs [compositeFamily,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed]

theorem compositeFamily_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J K O Out : Fin m) :
    Project.Formula.satisfies env (compositeFamily J K O Out) ↔ CompositeFamily (env.bound J) (env.bound K) (env.bound O) (env.bound Out) := by
  simp only [compositeFamily,CompositeFamily,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM]
  rfl


def fullLegs {m : Nat} (w Q J Domains Muls Units Marks Heights Costs K N mulN eN markN HN CN : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn Domains J)) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.functionOn Muls J)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn
  Units J)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn Marks J)) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.functionOn Heights J)) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.functionOn Costs J)) (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE
  (.forallE (.forallE (.imp (.mem (.bound (7 : Fin (m+8))) (.bound
  J.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Domains.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)) (6 : Fin (m+8)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Muls.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin
  (m+8)) (5 : Fin (m+8)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Units.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)) (4 : Fin (m+8)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Marks.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin
  (m+8)) (3 : Fin (m+8)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Heights.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)) (2 : Fin (m+8)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Costs.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin
  (m+8)) (1 : Fin (m+8)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  K.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)) (0 : Fin (m+8))))
  (ConstructionRoundStepSyntax.mapFields w.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+8)) N.succ.succ.succ.succ.succ.succ.succ.succ (5 :
  Fin (m+8)) mulN.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin (m+8))
  eN.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin (m+8)) markN.succ.succ.succ.succ.succ.succ.succ.succ
  (2 : Fin (m+8)) (1 : Fin (m+8)) HN.succ.succ.succ.succ.succ.succ.succ.succ
  CN.succ.succ.succ.succ.succ.succ.succ.succ (0 : Fin (m+8)))))))))))))))))))))))))

theorem fullLegs_freeClosed {m : Nat} (w Q J Domains Muls Units Marks Heights Costs K N mulN eN markN HN CN : Fin m) :
    (fullLegs w Q J Domains Muls Units Marks Heights Costs K N mulN eN markN HN CN).FreeClosed := by
  simp -implicitDefEqProofs [fullLegs,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionRoundStepSyntax.mapFields_freeClosed]

theorem fullLegs_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q J Domains Muls Units Marks Heights Costs K N mulN eN markN HN CN : Fin m) :
    Project.Formula.satisfies env (fullLegs w Q J Domains Muls Units Marks Heights Costs K N mulN eN markN HN CN) ↔ FullLegs hM (env.bound w) (env.bound Q) (env.bound J) (env.bound Domains) (env.bound Muls) (env.bound Units) (env.bound Marks) (env.bound Heights) (env.bound Costs) (env.bound K) (env.bound N) (env.bound mulN) (env.bound eN) (env.bound markN) (env.bound HN) (env.bound CN) := by
  simp only [fullLegs,FullLegs,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingConditionGraphs.functionOn_semantics (M := M),ConstructionRoundStepSyntax.mapFields_semantics hM]
  rfl


def profileLegs {m : Nat} (w J Domains Muls K N mulN : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (3 : Fin (m+4))) (.bound J.succ.succ.succ.succ))
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Domains.succ.succ.succ.succ (3 : Fin (m+4)) (2 :
  Fin (m+4)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Muls.succ.succ.succ.succ (3 : Fin
  (m+4)) (1 : Fin (m+4)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge K.succ.succ.succ.succ (3
  : Fin (m+4)) (0 : Fin (m+4)))) (ConstructionRoundStepSyntax.profiles w.succ.succ.succ.succ (2 : Fin (m+4))
  N.succ.succ.succ.succ (1 : Fin (m+4)) mulN.succ.succ.succ.succ (0 : Fin (m+4)))))))))))

theorem profileLegs_freeClosed {m : Nat} (w J Domains Muls K N mulN : Fin m) :
    (profileLegs w J Domains Muls K N mulN).FreeClosed := by
  simp -implicitDefEqProofs [profileLegs,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionRoundStepSyntax.profiles_freeClosed]

theorem profileLegs_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w J Domains Muls K N mulN : Fin m) :
    Project.Formula.satisfies env (profileLegs w J Domains Muls K N mulN) ↔ ProfileLegs (env.bound w) (env.bound J) (env.bound Domains) (env.bound Muls) (env.bound K) (env.bound N) (env.bound mulN) := by
  simp only [profileLegs,ProfileLegs,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionRoundStepSyntax.profiles_semantics hM]
  rfl


def baseNatural {m : Nat} (J Origins K f : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.imp (.mem (.bound (2 : Fin (m+3))) (.bound J.succ.succ.succ)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Origins.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3))))
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge K.succ.succ.succ (2 : Fin (m+3)) (0 : Fin (m+3))))
  (ConstructionProbeMappedPathSyntax.nodeMap (1 : Fin (m+3)) (0 : Fin (m+3)) f.succ.succ.succ)))))))

theorem baseNatural_freeClosed {m : Nat} (J Origins K f : Fin m) :
    (baseNatural J Origins K f).FreeClosed := by
  simp -implicitDefEqProofs [baseNatural,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed]

theorem baseNatural_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Origins K f : Fin m) :
    Project.Formula.satisfies env (baseNatural J Origins K f) ↔ BaseNatural (env.bound J) (env.bound Origins) (env.bound K) (env.bound f) := by
  simp only [baseNatural,BaseNatural,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM]
  rfl


def successorEquation {m : Nat} (J K N O Out : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.imp (.mem (.bound (2 : Fin (m+3))) (.bound J.succ.succ.succ)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge K.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3)))) (.imp
  (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph N.succ.succ.succ (1 : Fin (m+3)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Out.succ.succ.succ (2 : Fin (m+3)) (0 : Fin (m+3))))
  (Project.Formula.extensionalEq (.bound (0 : Fin (m+3))) (.bound O.succ.succ.succ)))))))))

theorem successorEquation_freeClosed {m : Nat} (J K N O Out : Fin m) :
    (successorEquation J K N O Out).FreeClosed := by
  simp -implicitDefEqProofs [successorEquation,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq]

theorem successorEquation_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J K N O Out : Fin m) :
    Project.Formula.satisfies env (successorEquation J K N O Out) ↔ SuccessorEquation (env.bound J) (env.bound K) (env.bound N) (env.bound O) (env.bound Out) := by
  simp only [successorEquation,SuccessorEquation,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingConditionGraphs.identityGraph_semantics (M := M),Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl


theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {J Domains K O W i x y : M.Carrier .set}
    (hD : FunctionOn J Domains) (hK : FunctionOn J K)
    (hx : Value Domains K O W i x) (hy : Value Domains K O W i y) : x = y := by
  obtain ⟨D,ki,hD0,hk,hx,hcx⟩ := hx
  obtain ⟨D',ki',hD1,hk',hy,hcy⟩ := hy
  have hd := function_unique hD hD0 hD1
  have hkEq := function_unique hK hk hk'
  subst D'; subst ki'
  exact SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM D W x).mp hx).1.1
    ((ForcingSupportSize.native_mapsTo hM D W y).mp hy).1.1
    (fun a b => (hcx a b).trans (hcy a b).symm)

theorem exists_family (hM : FirstOrder.Theory.Models M nativeZF)
    {J Domains K N O W : M.Carrier .set}
    (hD : FunctionOn J Domains) (hK : WeightFamily J Domains N K) (hO : MapsTo N W O) :
    ∃ Out, Graph J Domains K O W Out ∧ WeightFamily J Domains W Out ∧ CompositeFamily J K O Out ∧
      ∀ other, FunctionOn J other → Graph J Domains K O W other → other = Out := by
  let schema : Project.BinarySchema 4 := {
    body := value 2 3 4 5 1 0
    freeClosed := value_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 := {
    bound := Fin.cases Domains (Fin.cases K (Fin.cases O (fun _ => W)))
    free := fun _ => J }
  have he (i out) : schema.denote env i out ↔ Value Domains K O W i out :=
    value_semantics hM ((env.push i).push out) 2 3 4 5 1 0
  have ht : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i J → ∃ out, schema.denote env i out := by
    intro i hi
    obtain ⟨D,hDi,_⟩ := hD.2 i hi
    obtain ⟨ki,hki,_⟩ := hK.1.2 i hi
    obtain ⟨out,hm,hc⟩ := ConstructionProbeMappedPath.exists_node_map hM (hK.2 i D ki hi hDi hki) hO
    exact ⟨out,(he i out).mpr ⟨D,ki,hDi,hki,hm,hc⟩⟩
  have hu : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i J → ∀ x y,
      schema.denote env i x → schema.denote env i y → x = y :=
    fun _ _ _ _ hx hy => value_unique hM hD hK.1 ((he _ _).mp hx) ((he _ _).mp hy)
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨A,hA⟩ := ZF.exists_functionalImageOn hZF schema env J ht hu
  obtain ⟨Out,hOut,hG⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (KuratowskiZF.interpretation hM)
    schema env ht hu (fun i out hi hv => (hA out).mpr ⟨i,hi,hv⟩)
  have hFn := ((ForcingSupportSize.native_mapsTo hM J A Out).mpr hOut).1
  have hGraph : Graph J Domains K O W Out :=
    fun i out => (hG i out).trans (and_congr_right fun _ => he i out)
  refine ⟨Out,hGraph,⟨hFn,?_⟩,?_,?_⟩
  · intro i D out _ hDi hout
    obtain ⟨_,D',ki,hDi',_,hMaps,_⟩ := (hGraph i out).mp hout
    exact (function_unique hD hDi' hDi) ▸ hMaps
  · intro i ki out _ hki hout
    obtain ⟨_,D,ki',_,hki',_,hc⟩ := (hGraph i out).mp hout
    exact (function_unique hK.1 hki' hki) ▸ hc
  · intro other hOther hGraphOther
    have hmOther : MapsTo J A other := ⟨hOther,fun i out hout => (hA out).mpr
      ⟨i,((hGraphOther i out).mp hout).1,(he i out).mpr ((hGraphOther i out).mp hout).2⟩⟩
    exact SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
      ((ForcingSupportSize.native_mapsTo hM J A other).mp hmOther).1.1 hOut.1.1
      (fun i out => (hGraphOther i out).trans (hGraph i out).symm)

theorem stable_comp {J E Domains F K N O Out : M.Carrier .set}
    (hK : WeightFamily J Domains N K) (hs : Stable J E Domains F K)
    (hc : CompositeFamily J K O Out) : Stable J E Domains F Out := by
  intro i j x y r outi outj hij hxy hi hj hxr
  obtain ⟨ki,hki,_⟩ := hK.1.2 i hxy.1.1
  obtain ⟨kj,hkj,_⟩ := hK.1.2 j hxy.2.1.1
  obtain ⟨mid,hxm,hmr⟩ := ((hc i ki outi hxy.1.1 hki hi) x r).mp hxr
  exact ((hc j kj outj hxy.2.1.1 hkj hj) y r).mpr
    ⟨mid,hs i j x y mid ki kj hij hxy hki hkj hxm,hmr⟩

theorem full_legs_comp (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q J Domains Muls Units Marks Heights Costs K N mulN eN markN HN CN
      O W G unitW markW HL LC Out : M.Carrier .set}
    (hN : ForcingDiagramPoset.LeftCancelMonoid N mulN eN)
    (hW : ForcingDiagramPoset.LeftCancelMonoid W G unitW)
    (hK : WeightFamily J Domains N K) (hOut : WeightFamily J Domains W Out)
    (hc : CompositeFamily J K O Out)
    (hFull : FullLegs hM w Q J Domains Muls Units Marks Heights Costs K N mulN eN markN HN CN)
    (hO : MapFields hM w Q N W mulN G eN unitW markN markW HN CN HL LC O) :
    FullLegs hM w Q J Domains Muls Units Marks Heights Costs Out W G unitW markW HL LC := by
  obtain ⟨hD,hm,hu,ha,hh,hhc,hLegs⟩ := hFull
  refine ⟨hD,hm,hu,ha,hh,hhc,?_⟩
  intro i D mul e mark H C out hi hDi hMul hUnit hMark hH hC hout
  obtain ⟨ki,hki,_⟩ := hK.1.2 i hi
  exact map_comp hM hN hW (hLegs i D mul e mark H C ki hi hDi hMul hUnit hMark hH hC hki)
    hO (hOut.2 i D out hi hDi hout) (hc i ki out hi hki hout)

theorem profile_legs_comp {w J Domains Muls K N mulN O W G Out : M.Carrier .set}
    (hK : WeightFamily J Domains N K) (hc : CompositeFamily J K O Out)
    (hOld : ProfileLegs w J Domains Muls K N mulN) (hO : Profiles w N W mulN G O) :
    ProfileLegs w J Domains Muls Out W G := by
  intro i D mul out hi hD hm hout
  obtain ⟨ki,hki,_⟩ := hK.1.2 i hi
  exact profiles_comp (hc i ki out hi hki hout) (hOld i D mul ki hi hD hm hki) hO

theorem base_natural_comp {J Origins K O f baseW Out : M.Carrier .set}
    (hK : FunctionOn J K)
    (hc : CompositeFamily J K O Out) (hOld : BaseNatural J Origins K f)
    (hBase : NodeMap f O baseW) : BaseNatural J Origins Out baseW := by
  intro i fi out hi hfi hout
  obtain ⟨ki,hki,_⟩ := hK.2 i hi
  exact node_comp (hc i ki out hi hki hout) (hOld i fi ki hi hfi hki) hBase

theorem successor_equation (hM : FirstOrder.Theory.Models M nativeZF)
    {J Domains K N O W Out : M.Carrier .set}
    (hD : FunctionOn J Domains) (hOut : WeightFamily J Domains W Out)
    (hc : CompositeFamily J K O Out) (hO : MapsTo N W O) :
    SuccessorEquation J K N O Out := by
  intro i ki out hi hki hId hout
  obtain ⟨D,hDi,_⟩ := hD.2 i hi
  have hm := hOut.2 i D out hi hDi hout
  have hComp := hc i ki out hi hki hout
  apply SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM D W out).mp hm).1.1
    ((ForcingSupportSize.native_mapsTo hM N W O).mp hO).1.1
  intro x y
  constructor
  · intro hxy
    obtain ⟨z,hxz,hzy⟩ := (hComp x y).mp hxy
    exact ((hId x z).mp hxz).2.symm ▸ hzy
  · intro hxy
    exact (hComp x y).mpr ⟨x,(hId x x).mpr ⟨ForcingConditionGraphs.function_input hO.1 hxy,rfl⟩,hxy⟩


/-- SAME selected successor plus the ACTUAL new family of ALL old legs.
The final graph-uniqueness clause rules out an arbitrary supplied family. -/
def Extended (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request
      J E Domains F Muls Units Marks Heights Costs K Origins output : M.Carrier .set) : Prop :=
  ConstructionRoundSelection.Picked hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request output ∧
    ∃ W G unitW markW HL LC O baseW roots Out,
      ConstructionRoundSelection.Pack W G unitW markW HL LC O baseW roots output ∧
      ConstructionRoundStep.Step hM w Q R top zero D mul e mark H C N mulN eN markN HN CN f W G unitW markW HL LC O baseW ∧
      ConstructionRoundSelection.Done w D mul zero one request W G markW baseW roots ∧
      Graph J Domains K O W Out ∧ WeightFamily J Domains W Out ∧ CompositeFamily J K O Out ∧
      Stable J E Domains F Out ∧
      FullLegs hM w Q J Domains Muls Units Marks Heights Costs Out W G unitW markW HL LC ∧
      ProfileLegs w J Domains Muls Out W G ∧ BaseNatural J Origins Out baseW ∧
      SuccessorEquation J K N O Out ∧
      ∀ other, FunctionOn J other → Graph J Domains K O W other → other = Out

theorem extended_unique (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request
      J E Domains F Muls Units Marks Heights Costs K Origins x y : M.Carrier .set}
    (hx : Extended hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request J E Domains F Muls Units Marks Heights Costs K Origins x)
    (hy : Extended hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request J E Domains F Muls Units Marks Heights Costs K Origins y) : x = y :=
  ConstructionRoundSelection.picked_unique hM hOrder hx.1 hy.1

theorem exists_extended (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w Q R top zero one u D mul e mark H C N mulN eN markN HN CN f request
      J E Domains F Muls Units Marks Heights Costs K Origins : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hQ : ConstructionFractionOrder.Carrier w Q) (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hu : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (htop : ConstructionRealCuts.Principal hM w Q u top)
    (hObjD : ObjectFields hM w Q R top D mul e mark H C)
    (hObjN : ObjectFields hM w Q R top N mulN eN markN HN CN)
    (hf : MapFields hM w Q D N mul mulN e eN mark markN H C HN CN f)
    (hq : ConstructionRequestSchedule.Request w D mul e zero one request)
    (hK : WeightFamily J Domains N K) (hStable : Stable J E Domains F K)
    (hFull : FullLegs hM w Q J Domains Muls Units Marks Heights Costs K N mulN eN markN HN CN)
    (hProfiles : ProfileLegs w J Domains Muls K N mulN)
    (hNatural : BaseNatural J Origins K f) :
    ∃ output, Extended hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request
      J E Domains F Muls Units Marks Heights Costs K Origins output ∧
      ∀ other, Extended hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request
        J E Domains F Muls Units Marks Heights Costs K Origins other → other = output := by
  obtain ⟨output,hPick,_⟩ := ConstructionRoundSelection.picked_total hM hOrder
    w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request
  obtain ⟨W,G,unitW,markW,HL,LC,O,baseW,roots,hPack,hStep,hDone⟩ :=
    ConstructionRoundSelection.picked_is_candidate hM
      (ConstructionRoundSelection.candidate_exists hM hw hz hzw hQ hR hu hone htop hObjD hObjN hf hq) hPick
  have hMapO := hStep.1.2.1
  have hObjW := hStep.1.1
  obtain ⟨Out,hGraph,hOut,hComp,hUnique⟩ := exists_family hM hFull.1 hK hMapO.1.1.1
  have hExtended : Extended hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request
      J E Domains F Muls Units Marks Heights Costs K Origins output :=
    ⟨hPick,W,G,unitW,markW,HL,LC,O,baseW,roots,Out,hPack,hStep,hDone,hGraph,hOut,hComp,
      stable_comp hK hStable hComp,
      full_legs_comp hM hObjN.1 hObjW.1 hK hOut hComp hFull hMapO,
      profile_legs_comp hK hComp hProfiles hStep.1.2.2.2.2.1,
      base_natural_comp hK.1 hComp hNatural hStep.2.1,
      successor_equation hM hFull.1 hOut hComp hMapO.1.1.1,hUnique⟩
  exact ⟨output,hExtended,fun other hOther => extended_unique hM hOrder hOther hExtended⟩


def extended {m : Nat} (w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request J E Domains F Muls Units Marks Heights Costs K Origins output : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionRoundSelection.picked w Q R top zero one D mul e mark H C N mulN eN markN HN CN f
  request output) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.conj (ConstructionRoundSelection.pack (9 : Fin (m+10)) (8 : Fin (m+10)) (7 : Fin (m+10)) (6 :
  Fin (m+10)) (5 : Fin (m+10)) (4 : Fin (m+10)) (3 : Fin (m+10)) (2 : Fin (m+10)) (1 : Fin (m+10))
  output.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj (ConstructionRoundStepSyntax.step
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mulN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  eN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  markN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  HN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ CN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin (m+10)) (8 : Fin (m+10)) (7 : Fin (m+10)) (6
  : Fin (m+10)) (5 : Fin (m+10)) (4 : Fin (m+10)) (3 : Fin (m+10)) (2 : Fin (m+10))) (.conj
  (ConstructionRoundSelection.done w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  one.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  request.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin (m+10)) (8 : Fin (m+10)) (6 : Fin
  (m+10)) (2 : Fin (m+10)) (1 : Fin (m+10))) (.conj (graph
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Domains.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin (m+10)) (9 : Fin (m+10)) (0 : Fin (m+10)))
  (.conj (ConstructionDirectedWeightData.weightFamily J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Domains.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin (m+10)) (0 : Fin (m+10))) (.conj
  (compositeFamily J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin (m+10)) (0 : Fin (m+10))) (.conj
  (ConstructionDirectedWeightData.stable J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  E.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Domains.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  F.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (0 : Fin (m+10))) (.conj (fullLegs
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Domains.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Muls.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Units.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Marks.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Heights.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Costs.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (0 : Fin (m+10)) (9 : Fin (m+10)) (8 : Fin (m+10))
  (7 : Fin (m+10)) (6 : Fin (m+10)) (5 : Fin (m+10)) (4 : Fin (m+10))) (.conj (profileLegs
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Domains.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Muls.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (0 : Fin (m+10)) (9 : Fin (m+10)) (8 : Fin (m+10)))
  (.conj (baseNatural J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Origins.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (0 : Fin (m+10)) (2 : Fin (m+10))) (.conj
  (successorEquation J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3
  : Fin (m+10)) (0 : Fin (m+10))) (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn (0
  : Fin (m+11)) J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp (graph
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Domains.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin (m+10)).succ (9 : Fin (m+10)).succ (0 :
  Fin (m+11))) (Project.Formula.extensionalEq (.bound (0 : Fin (m+11))) (.bound (0 : Fin
  (m+10)).succ)))))))))))))))))))))))))))

theorem extended_freeClosed {m : Nat} (w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request J E Domains F Muls Units Marks Heights Costs K Origins output : Fin m) :
    (extended w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request J E Domains F Muls Units Marks Heights Costs K Origins output).FreeClosed := by
  simp -implicitDefEqProofs [extended,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionRoundSelection.picked_freeClosed,ConstructionRoundSelection.pack_freeClosed,ConstructionRoundStepSyntax.step_freeClosed,ConstructionRoundSelection.done_freeClosed,graph_freeClosed,ConstructionDirectedWeightData.weightFamily_freeClosed,compositeFamily_freeClosed,ConstructionDirectedWeightData.stable_freeClosed,fullLegs_freeClosed,profileLegs_freeClosed,baseNatural_freeClosed,successorEquation_freeClosed,Project.Formula.extensionalEq]

theorem extended_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request J E Domains F Muls Units Marks Heights Costs K Origins output : Fin m) :
    Project.Formula.satisfies env (extended w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request J E Domains F Muls Units Marks Heights Costs K Origins output) ↔ Extended hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound zero) (env.bound one) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound N) (env.bound mulN) (env.bound eN) (env.bound markN) (env.bound HN) (env.bound CN) (env.bound f) (env.bound request) (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound Muls) (env.bound Units) (env.bound Marks) (env.bound Heights) (env.bound Costs) (env.bound K) (env.bound Origins) (env.bound output) := by
  simp only [extended,Extended,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionRoundSelection.picked_semantics hM,ConstructionRoundSelection.pack_semantics hM,ConstructionRoundStepSyntax.step_semantics hM,ConstructionRoundSelection.done_semantics hM,graph_semantics hM,ConstructionDirectedWeightData.weightFamily_semantics hM,compositeFamily_semantics hM,ConstructionDirectedWeightData.stable_semantics hM,fullLegs_semantics hM,profileLegs_semantics hM,baseNatural_semantics hM,successorEquation_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl


def successorSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 32 (.imp (Project.Formula.isOmega (.bound (0 : Fin 32))) (.imp
    (Project.Formula.isEmpty (.bound (4 : Fin 32))) (.imp (.mem (.bound (4 : Fin 32)) (.bound (0 : Fin 32)))
    (.imp (ConstructionFractionOrder.carrier (0 : Fin 32) (1 : Fin 32)) (.imp
    (ConstructionRealCuts.cutCarrier (0 : Fin 32) (1 : Fin 32) (2 : Fin 32)) (.imp
    (ConstructionFractionOrder.coordinates (0 : Fin 32) (31 : Fin 32) (5 : Fin 32) (5 : Fin 32)) (.imp
    (Project.Formula.isOrdinalOne (.bound (5 : Fin 32))) (.imp (ConstructionRealCuts.principal (0 : Fin 32)
    (1 : Fin 32) (31 : Fin 32) (3 : Fin 32)) (.imp (ConstructionRoundStepSyntax.objectFields (0 : Fin 32) (1
    : Fin 32) (2 : Fin 32) (3 : Fin 32) (6 : Fin 32) (7 : Fin 32) (8 : Fin 32) (9 : Fin 32) (10 : Fin 32)
    (11 : Fin 32)) (.imp (ConstructionRoundStepSyntax.objectFields (0 : Fin 32) (1 : Fin 32) (2 : Fin 32) (3
    : Fin 32) (12 : Fin 32) (13 : Fin 32) (14 : Fin 32) (15 : Fin 32) (16 : Fin 32) (17 : Fin 32)) (.imp
    (ConstructionRoundStepSyntax.mapFields (0 : Fin 32) (1 : Fin 32) (6 : Fin 32) (12 : Fin 32) (7 : Fin 32)
    (13 : Fin 32) (8 : Fin 32) (14 : Fin 32) (9 : Fin 32) (15 : Fin 32) (10 : Fin 32) (11 : Fin 32) (16 :
    Fin 32) (17 : Fin 32) (18 : Fin 32)) (.imp (ConstructionRequestSchedule.request (0 : Fin 32) (6 : Fin
    32) (7 : Fin 32) (8 : Fin 32) (4 : Fin 32) (5 : Fin 32) (19 : Fin 32)) (.imp
    (ConstructionDirectedWeightData.weightFamily (20 : Fin 32) (22 : Fin 32) (12 : Fin 32) (29 : Fin 32))
    (.imp (ConstructionDirectedWeightData.stable (20 : Fin 32) (21 : Fin 32) (22 : Fin 32) (23 : Fin 32) (29
    : Fin 32)) (.imp (fullLegs (0 : Fin 32) (1 : Fin 32) (20 : Fin 32) (22 : Fin 32) (24 : Fin 32) (25 : Fin
    32) (26 : Fin 32) (27 : Fin 32) (28 : Fin 32) (29 : Fin 32) (12 : Fin 32) (13 : Fin 32) (14 : Fin 32)
    (15 : Fin 32) (16 : Fin 32) (17 : Fin 32)) (.imp (profileLegs (0 : Fin 32) (20 : Fin 32) (22 : Fin 32)
    (24 : Fin 32) (29 : Fin 32) (12 : Fin 32) (13 : Fin 32)) (.imp (baseNatural (20 : Fin 32) (30 : Fin 32)
    (29 : Fin 32) (18 : Fin 32)) (.existsE (.conj (extended (0 : Fin 32).succ (1 : Fin 32).succ (2 : Fin
    32).succ (3 : Fin 32).succ (4 : Fin 32).succ (5 : Fin 32).succ (6 : Fin 32).succ (7 : Fin 32).succ (8 :
    Fin 32).succ (9 : Fin 32).succ (10 : Fin 32).succ (11 : Fin 32).succ (12 : Fin 32).succ (13 : Fin
    32).succ (14 : Fin 32).succ (15 : Fin 32).succ (16 : Fin 32).succ (17 : Fin 32).succ (18 : Fin 32).succ
    (19 : Fin 32).succ (20 : Fin 32).succ (21 : Fin 32).succ (22 : Fin 32).succ (23 : Fin 32).succ (24 : Fin
    32).succ (25 : Fin 32).succ (26 : Fin 32).succ (27 : Fin 32).succ (28 : Fin 32).succ (29 : Fin 32).succ
    (30 : Fin 32).succ (0 : Fin 33)) (.forallE (.imp (extended (0 : Fin 32).succ.succ (1 : Fin 32).succ.succ
    (2 : Fin 32).succ.succ (3 : Fin 32).succ.succ (4 : Fin 32).succ.succ (5 : Fin 32).succ.succ (6 : Fin
    32).succ.succ (7 : Fin 32).succ.succ (8 : Fin 32).succ.succ (9 : Fin 32).succ.succ (10 : Fin
    32).succ.succ (11 : Fin 32).succ.succ (12 : Fin 32).succ.succ (13 : Fin 32).succ.succ (14 : Fin
    32).succ.succ (15 : Fin 32).succ.succ (16 : Fin 32).succ.succ (17 : Fin 32).succ.succ (18 : Fin
    32).succ.succ (19 : Fin 32).succ.succ (20 : Fin 32).succ.succ (21 : Fin 32).succ.succ (22 : Fin
    32).succ.succ (23 : Fin 32).succ.succ (24 : Fin 32).succ.succ (25 : Fin 32).succ.succ (26 : Fin
    32).succ.succ (27 : Fin 32).succ.succ (28 : Fin 32).succ.succ (29 : Fin 32).succ.succ (30 : Fin
    32).succ.succ (0 : Fin 34)) (Project.Formula.extensionalEq (.bound (0 : Fin 34)) (.bound (0 : Fin
    33).succ))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      Project.Formula.isOmega,Project.Formula.isEmpty,Project.Formula.isOrdinalOne,Project.Formula.extensionalEq,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionFractionOrder.coordinates_freeClosed,ConstructionRealCuts.principal_freeClosed,
      ConstructionRoundStepSyntax.objectFields_freeClosed,ConstructionRoundStepSyntax.mapFields_freeClosed,
      ConstructionRequestSchedule.request_freeClosed,ConstructionDirectedWeightData.weightFamily_freeClosed,
      ConstructionDirectedWeightData.stable_freeClosed,fullLegs_freeClosed,profileLegs_freeClosed,
      baseNatural_freeClosed,extended_freeClosed]

theorem successor_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M))) :
    (Project.fo_sentence successorSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) successorSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    ConstructionFractionOrder.coordinates_semantics hM,Project.Formula.satisfies_isOrdinalOne_iff,
    ConstructionRealCuts.principal_semantics hM,ConstructionRoundStepSyntax.objectFields_semantics hM,
    ConstructionRoundStepSyntax.mapFields_semantics hM,ConstructionRequestSchedule.request_semantics hM,
    ConstructionDirectedWeightData.weightFamily_semantics hM,ConstructionDirectedWeightData.stable_semantics hM,
    fullLegs_semantics hM,profileLegs_semantics hM,baseNatural_semantics hM,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    extended_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  exact fun hw hz hzw hQ hR hu hone htop hObjD hObjN hf hq hK hStable hFull hProfiles hNatural =>
    exists_extended hM hOrder hw hz hzw hQ hR hu hone htop hObjD hObjN hf hq hK hStable hFull hProfiles hNatural

theorem successor_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative successorSentence)) := by
  apply ModelTransfer.derives
  intro M hM
  apply ConstructibleGround.relative_models hM successorSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality (ConstructibleSource.model_zf hM)) successorSentence).mp
    (successor_models (ConstructibleSource.model_zf hM) (ConstructionRoundSelection.l_order hM))


/-- Add exactly the new internal ordinal index and its OWN identity leg.
The original native IsSequenceOfLength.exists_append is reused unchanged. -/
def SelfExtension (J next Domains Out W identity NewDomains NewOut : M.Carrier .set) : Prop :=
  FunctionOn next NewDomains ∧ FunctionOn next NewOut ∧ MapsTo W W identity ∧
    ForcingConditionGraphs.IdentityGraph W identity ∧
    (∀ i D, PureKuratowski.PairMember M i D NewDomains ↔
      PureKuratowski.PairMember M i D Domains ∨ (i = J ∧ D = W)) ∧
    (∀ i ki, PureKuratowski.PairMember M i ki NewOut ↔
      PureKuratowski.PairMember M i ki Out ∨ (i = J ∧ ki = identity)) ∧
    WeightFamily next NewDomains W NewOut

theorem exists_self_extension (hM : FirstOrder.Theory.Models M nativeZF)
    {J next Domains Out W : M.Carrier .set}
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hNext : (Project.FirstOrderSemantics.reduct M).IsOrdinal next)
    (hSucc : (Project.FirstOrderSemantics.reduct M).SuccessorOf next J)
    (hD : FunctionOn J Domains) (hOut : WeightFamily J Domains W Out) :
    ∃ identity NewDomains NewOut, SelfExtension J next Domains Out W identity NewDomains NewOut := by
  let rawM := Project.FirstOrderSemantics.reduct M
  let I := KuratowskiZF.interpretation hM
  have toSeq (f) (hf : FunctionOn J f) : rawM.IsSequenceOfLength I f J := by
    refine ⟨hJ,⟨?_,?_⟩,?_⟩
    · intro row hrow
      obtain ⟨x,y,_,hc⟩ := hf.1 row hrow
      exact ⟨x,y,hc⟩
    · intro x y z hy hz
      exact function_unique hf hy hz
    · intro x
      constructor
      · intro hx
        obtain ⟨y,hy,_⟩ := hf.2 x hx
        exact ⟨y,hy⟩
      · rintro ⟨y,hy⟩
        exact ForcingConditionGraphs.function_input hf hy
  have fromSeq {S V} (h : rawM.IsSequenceOfLength I V S) : FunctionOn S V := by
    constructor
    · intro row hrow
      obtain ⟨x,y,hc⟩ := h.2.1.1 row hrow
      exact ⟨x,y,(h.2.2 x).mpr ⟨y,row,hc,hrow⟩,hc⟩
    · intro x hx
      obtain ⟨y,hy⟩ := (h.2.2 x).mp hx
      exact ⟨y,hy,fun z hz => h.2.1.2 x z y hz hy⟩
  obtain ⟨identity,hId,hIdGraph⟩ := ForcingConditionGraphs.exists_identity hM W
  obtain ⟨NewDomains,hDomains,hDG⟩ := Structure.IsSequenceOfLength.exists_append
    (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) I (value := W) (toSeq Domains hD) hNext hSucc
  obtain ⟨NewOut,hNewOut,hOG⟩ := Structure.IsSequenceOfLength.exists_append
    (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) I (value := identity) (toSeq Out hOut.1) hNext hSucc
  refine ⟨identity,NewDomains,NewOut,fromSeq hDomains,fromSeq hNewOut,hId.1,hIdGraph,hDG,hOG,
    ⟨fromSeq hNewOut,?_⟩⟩
  intro i D ki _ hDi hki
  rcases (hDG i D).mp hDi with hOldD | ⟨rfl,rfl⟩
  · rcases (hOG i ki).mp hki with hOldK | ⟨rfl,rfl⟩
    · exact hOut.2 i D ki (ForcingConditionGraphs.function_input hD hOldD) hOldD hOldK
    · have hSelf := ForcingConditionGraphs.function_input hD hOldD
      exact False.elim (hJ.wellOrder.linear.irrefl i hSelf hSelf)
  · rcases (hOG i ki).mp hki with hOldK | ⟨_,rfl⟩
    · have hSelf := ForcingConditionGraphs.function_input hOut.1 hOldK
      exact False.elim (hJ.wellOrder.linear.irrefl i hSelf hSelf)
    · exact hId.1


def selfExtension {m : Nat} (J next Domains Out W identity NewDomains NewOut : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn NewDomains next)) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.functionOn NewOut next)) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.mapsTo identity W W)) (.conj (ProjectSyntax.encode id
  (ForcingConditionGraphs.identityGraph W identity)) (.conj (.forallE (.forallE (.iff (ProjectSyntax.encode
  id (Source.SetLanguage.edge NewDomains.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))) (.disj
  (ProjectSyntax.encode id (Source.SetLanguage.edge Domains.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2))))
  (.conj (Project.Formula.extensionalEq (.bound (1 : Fin (m+2))) (.bound J.succ.succ))
  (Project.Formula.extensionalEq (.bound (0 : Fin (m+2))) (.bound W.succ.succ))))))) (.conj (.forallE
  (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge NewOut.succ.succ (1 : Fin (m+2)) (0 :
  Fin (m+2)))) (.disj (ProjectSyntax.encode id (Source.SetLanguage.edge Out.succ.succ (1 : Fin (m+2)) (0 :
  Fin (m+2)))) (.conj (Project.Formula.extensionalEq (.bound (1 : Fin (m+2))) (.bound J.succ.succ))
  (Project.Formula.extensionalEq (.bound (0 : Fin (m+2))) (.bound identity.succ.succ)))))))
  (ConstructionDirectedWeightData.weightFamily next NewDomains W NewOut)))))))

theorem selfExtension_freeClosed {m : Nat} (J next Domains Out W identity NewDomains NewOut : Fin m) :
    (selfExtension J next Domains Out W identity NewDomains NewOut).FreeClosed := by
  simp -implicitDefEqProofs [selfExtension,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq,ConstructionDirectedWeightData.weightFamily_freeClosed]

theorem selfExtension_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J next Domains Out W identity NewDomains NewOut : Fin m) :
    Project.Formula.satisfies env (selfExtension J next Domains Out W identity NewDomains NewOut) ↔ SelfExtension (env.bound J) (env.bound next) (env.bound Domains) (env.bound Out) (env.bound W) (env.bound identity) (env.bound NewDomains) (env.bound NewOut) := by
  simp only [selfExtension,SelfExtension,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ForcingConditionGraphs.functionOn_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),ForcingConditionGraphs.identityGraph_semantics (M := M),ConstructionDirectedWeightData.weightFamily_semantics hM]
  rfl


def appendSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 5 (.imp (Project.Formula.isOrdinal (.bound (0 : Fin 5))) (.imp
    (Project.Formula.isOrdinal (.bound (1 : Fin 5))) (.imp (.forallE (.iff (.mem (.bound (0 : Fin 6))
    (.bound (1 : Fin 5).succ)) (.disj (.mem (.bound (0 : Fin 6)) (.bound (0 : Fin 5).succ))
    (Project.Formula.extensionalEq (.bound (0 : Fin 6)) (.bound (0 : Fin 5).succ))))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.functionOn (2 : Fin 5) (0 : Fin 5))) (.imp
    (ConstructionDirectedWeightData.weightFamily (0 : Fin 5) (2 : Fin 5) (4 : Fin 5) (3 : Fin 5)) (.existsE
    (.existsE (.existsE (selfExtension (0 : Fin 5).succ.succ.succ (1 : Fin 5).succ.succ.succ (2 : Fin
    5).succ.succ.succ (3 : Fin 5).succ.succ.succ (4 : Fin 5).succ.succ.succ (2 : Fin 8) (1 : Fin 8) (0 : Fin
    8)))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOrdinal,
      Project.Formula.extensionalEq,ProjectSyntax.freeClosed,
      ConstructionDirectedWeightData.weightFamily_freeClosed,selfExtension_freeClosed]

theorem append_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence appendSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) appendSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOrdinal_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.functionOn_semantics (M := M),ConstructionDirectedWeightData.weightFamily_semantics hM,
    Project.Formula.satisfies_exists_iff,selfExtension_semantics hM]
  intro hJ hNext hSucc hD hOut
  have hs : (Project.FirstOrderSemantics.reduct M).SuccessorOf (bound 1) (bound 0) := by
    intro x
    exact (hSucc x).trans (or_congr Iff.rfl ⟨(fun h => by
      change x = bound 0 at h
      subst x
      exact fun _ => Iff.rfl),
      fun h => (ModelTransfer.extensionality hM).eq_of_same_members x (bound 0) h⟩)
  exact exists_self_extension hM hJ hNext hs hD hOut

theorem append_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence appendSentence) := ModelTransfer.derives (fun _ hM => append_models hM)


/-- Consume the actual selected output and its NEW leg family immediately;
append the same new carrier and its identity, preserving every old row. -/
theorem close_extended (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request
      J E Domains F Muls Units Marks Heights Costs K Origins output next : M.Carrier .set}
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hNext : (Project.FirstOrderSemantics.reduct M).IsOrdinal next)
    (hSucc : (Project.FirstOrderSemantics.reduct M).SuccessorOf next J)
    (hExt : Extended hM w Q R top zero one D mul e mark H C N mulN eN markN HN CN f request
      J E Domains F Muls Units Marks Heights Costs K Origins output) :
    ∃ W G unitW markW HL LC O baseW roots Out identity NewDomains NewOut,
      ConstructionRoundSelection.Pack W G unitW markW HL LC O baseW roots output ∧
      Graph J Domains K O W Out ∧ SelfExtension J next Domains Out W identity NewDomains NewOut := by
  obtain ⟨_,W,G,unitW,markW,HL,LC,O,baseW,roots,Out,hPack,_,_,hGraph,hOut,_,_,hFull,_,_,_,_⟩ := hExt
  obtain ⟨identity,NewDomains,NewOut,hSelf⟩ := exists_self_extension hM hJ hNext hSucc hFull.1 hOut
  exact ⟨W,G,unitW,markW,HL,LC,O,baseW,roots,Out,identity,NewDomains,NewOut,hPack,hGraph,hSelf⟩

end PPAC.Migration.ConstructionTowerSuccessor
