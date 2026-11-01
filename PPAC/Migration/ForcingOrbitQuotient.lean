/- Fixed OrbitAssignments.OrbitRel/ComponentOrbit/orbit:136-182.
Reuse the actual native separation, functional image and graph constructors
already used by ForcingComponentGluing. No host quotient is the object quotient. -/
import PPAC.Migration.ForcingOrbitAssignment
import PPAC.Migration.ConstructionGermDetectors

namespace PPAC.Migration.ForcingOrbitQuotient
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingOrbitAssignment (OrbitRel orbitRel)
open ForcingConditionGraphs (Permutation IdentityGraph CompositionGraph function_input function_unique)
open ForcingSupportSize (MapsTo Injection)
open ConstructionComponentCarrier (EncodedVertex)
open ConstructionComponentCofinal (EncodedCommon)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem identity_comp {D I idGraph r : M.Carrier .set}
    (hi : IdentityGraph I idGraph) (hr : Injection D I r) :
    CompositionGraph D idGraph r r := by
  intro x y
  constructor
  · intro hxy
    exact ⟨function_input hr.1.1 hxy,y,hxy,(hi y y).mpr ⟨hr.1.2 x y hxy,rfl⟩⟩
  · rintro ⟨_,z,hxz,hzy⟩
    exact ((hi z y).mp hzy).2 ▸ hxz

theorem common_refl {D I mul one q v : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul one)
    (hv : EncodedVertex D I mul q v) : EncodedCommon D I mul q v v := by
  obtain ⟨r,a,U,hCode,hVertex⟩ := hv
  exact ⟨r,a,U,r,a,U,hCode,hCode,hVertex,hVertex,ConstructionComponentVertices.common_refl hm hVertex⟩

theorem orbit_common (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul q v w : M.Carrier .set} (hq : Injection D I q)
    (h : EncodedCommon D I mul q v w) : OrbitRel D I mul q v w := by
  obtain ⟨idGraph,hi,hId⟩ := ForcingConditionGraphs.exists_identity hM I
  obtain ⟨r,a,U,s,b,V,hv,hw,hr,hs,hCommon⟩ := h
  exact ⟨idGraph,w,hi,identity_comp hId hq,
    ⟨s,b,V,s,hw,hw,hs,hs,identity_comp hId hs.1⟩,⟨r,a,U,s,b,V,hv,hw,hr,hs,hCommon⟩⟩

theorem orbit_refl (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul one q v : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul one)
    (hq : Injection D I q) (hv : EncodedVertex D I mul q v) : OrbitRel D I mul q v v :=
  orbit_common hM hq (common_refl hm hv)

theorem orbit_symm (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul q v w : M.Carrier .set} (hq : Injection D I q)
    (h : OrbitRel D I mul q v w) : OrbitRel D I mul q w v := by
  obtain ⟨pi,target,hPi,hFix,hMove,hCommon⟩ := h
  obtain ⟨inv,hInv,hInverse⟩ := ForcingConditionGraphs.exists_inverse hM hPi
  have hInvFix := ForcingDiagramCarrier.reverse hPi hq hInverse hFix
  have hv : EncodedVertex D I mul q v := by
    obtain ⟨r,a,U,s,b,V,hv,_,hr,_,_⟩ := hCommon
    exact ⟨r,a,U,hv,hr⟩
  obtain ⟨source,hSource⟩ := ForcingComponentMove.exists_move hM hInv hInvFix hv
  have hBack := ForcingComponentMove.move_inverse hPi hInverse hMove
  exact ⟨inv,source,hInv,hInvFix,hSource,ForcingComponentRebase.common_symm
    (ForcingComponentMove.move_common hM hInv hInvFix hSource hBack hCommon)⟩

theorem orbit_trans (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul one q v w z : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul one)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul) (hq : Injection D I q)
    (h : OrbitRel D I mul q v w) (h' : OrbitRel D I mul q w z) : OrbitRel D I mul q v z := by
  obtain ⟨pi,target,hPi,hFix,hMove,hCommon⟩ := h
  obtain ⟨s,other,hs,hsFix,hsMove,hsCommon⟩ := h'
  obtain ⟨product,hProduct,hProductGraph⟩ := ForcingConditionGraphs.exists_composition hM hPi hs
  have hProductFix := ConstructionGermSeparation.compose_diagrams hq hProductGraph hsFix hFix
  obtain ⟨movedOther,hMovedOther⟩ := ForcingComponentMove.exists_move hM hPi hFix (ForcingComponentMove.target_vertex hsMove)
  have hMovedCommon := ForcingComponentMove.move_common hM hPi hFix hMove hMovedOther hsCommon
  exact ⟨product,movedOther,hProduct,hProductFix,ConstructionGermSeparation.move_composition hProductGraph hsMove hMovedOther,
    ForcingComponentGluing.common_between hM hm hJ (ForcingComponentRebase.common_symm hCommon) hMovedCommon⟩

theorem orbit_move
    {D I mul one q pi v w : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul one)
    (hPi : Permutation I pi) (hFix : CompositionGraph D pi q q)
    (hMove : ForcingComponentMove.Move D I mul q pi v w) : OrbitRel D I mul q w v :=
  ⟨pi,w,hPi,hFix,hMove,common_refl hm (ForcingComponentMove.target_vertex hMove)⟩

def Class (D I mul q V v C : M.Carrier .set) : Prop := ∀ w,
  (Project.FirstOrderSemantics.reduct M).mem w C ↔
    (Project.FirstOrderSemantics.reduct M).mem w V ∧ OrbitRel D I mul q v w

def Classes (D I mul q V Q : M.Carrier .set) : Prop := ∀ C,
  (Project.FirstOrderSemantics.reduct M).mem C Q ↔
    ∃ v, (Project.FirstOrderSemantics.reduct M).mem v V ∧ Class D I mul q V v C

def Projection (D I mul q V pr : M.Carrier .set) : Prop := ∀ v C,
  PureKuratowski.PairMember M v C pr ↔ (Project.FirstOrderSemantics.reduct M).mem v V ∧ Class D I mul q V v C

theorem class_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul q V v C E : M.Carrier .set}
    (hC : Class D I mul q V v C) (hE : Class D I mul q V v E) : C = E :=
  (ModelTransfer.extensionality hM).eq_of_same_members C E (fun w => (hC w).trans (hE w).symm)

theorem class_eq_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul one q V v w C E : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul one)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul) (hq : Injection D I q)
    (hV : ConstructionComponentCarrier.Carrier D I mul q V)
    (hw : (Project.FirstOrderSemantics.reduct M).mem w V)
    (hC : Class D I mul q V v C) (hE : Class D I mul q V w E) :
    C = E ↔ OrbitRel D I mul q v w := by
  constructor
  · intro he
    have hself := (hE w).mpr ⟨hw,orbit_refl hM hm hq ((hV w).mp hw)⟩
    exact ((hC w).mp (he.symm ▸ hself)).2
  · intro h
    apply (ModelTransfer.extensionality hM).eq_of_same_members
    intro z
    rw [hC z,hE z]
    exact and_congr_right fun _ => ⟨
      fun hz => orbit_trans hM hm hJ hq (orbit_symm hM hq h) hz,
      fun hz => orbit_trans hM hm hJ hq h hz⟩

def eqClass {m : Nat} (D I mul q V v C : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound C.succ))
    (.conj (.mem (.bound 0) (.bound V.succ)) (orbitRel D.succ I.succ mul.succ q.succ v.succ 0)))

theorem eqClass_freeClosed {m : Nat} (D I mul q V v C : Fin m) : (eqClass D I mul q V v C).FreeClosed := by
  simp -implicitDefEqProofs [eqClass,Definitional.Formula.FreeClosed,ForcingOrbitAssignment.orbitRel_freeClosed]

theorem eqClass_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q V v C : Fin m) :
    Project.Formula.satisfies env (eqClass D I mul q V v C) ↔
      Class (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound V) (env.bound v) (env.bound C) := by
  simp only [eqClass,Class,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,
    ForcingOrbitAssignment.orbitRel_semantics hM]
  rfl

def classes {m : Nat} (D I mul q V Q : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound Q.succ)) (.existsE (.conj
    (.mem (.bound 0) (.bound V.succ.succ)) (eqClass D.succ.succ I.succ.succ mul.succ.succ q.succ.succ V.succ.succ 0 1))))

theorem classes_freeClosed {m : Nat} (D I mul q V Q : Fin m) : (classes D I mul q V Q).FreeClosed := by
  simp -implicitDefEqProofs [classes,Definitional.Formula.FreeClosed,eqClass_freeClosed]

theorem classes_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q V Q : Fin m) :
    Project.Formula.satisfies env (classes D I mul q V Q) ↔
      Classes (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound V) (env.bound Q) := by
  simp only [classes,Classes,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Term.eval_bound,eqClass_semantics hM]
  rfl

def projection {m : Nat} (D I mul q V pr : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge pr.succ.succ 1 0))
    (.conj (.mem (.bound 1) (.bound V.succ.succ)) (eqClass D.succ.succ I.succ.succ mul.succ.succ q.succ.succ V.succ.succ 1 0))))

theorem projection_freeClosed {m : Nat} (D I mul q V pr : Fin m) : (projection D I mul q V pr).FreeClosed := by
  simp -implicitDefEqProofs [projection,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,eqClass_freeClosed]

theorem projection_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q V pr : Fin m) :
    Project.Formula.satisfies env (projection D I mul q V pr) ↔
      Projection (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound V) (env.bound pr) := by
  simp only [projection,Projection,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,eqClass_semantics hM]
  rfl

theorem exists_class (hM : FirstOrder.Theory.Models M nativeZF)
    (D I mul q V v : M.Carrier .set) : ∃ C, Class D I mul q V v C := by
  let schema : Project.UnarySchema 5 := {
    body := orbitRel 1 2 3 4 5 0
    freeClosed := ForcingOrbitAssignment.orbitRel_freeClosed _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 := {
    bound := Fin.cases D (Fin.cases I (Fin.cases mul (Fin.cases q (fun _ => v)))), free := fun _ => V }
  have he w : schema.denote env w ↔ OrbitRel D I mul q v w := ForcingOrbitAssignment.orbitRel_semantics hM (env.push w) 1 2 3 4 5 0
  obtain ⟨C,hC⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env V
  exact ⟨C,fun w => (hC w).trans (and_congr Iff.rfl (he w))⟩

theorem exists_quotient (hM : FirstOrder.Theory.Models M nativeZF)
    (D I mul q V : M.Carrier .set) :
    ∃ Q pr, MapsTo V Q pr ∧ Classes D I mul q V Q ∧ Projection D I mul q V pr := by
  let schema : Project.BinarySchema 5 := { body := eqClass 2 3 4 5 6 1 0, freeClosed := eqClass_freeClosed _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 := {
    bound := Fin.cases D (Fin.cases I (Fin.cases mul (Fin.cases q (fun _ => V)))), free := fun _ => V }
  have he v C : schema.denote env v C ↔ Class D I mul q V v C := eqClass_semantics hM ((env.push v).push C) 2 3 4 5 6 1 0
  have ht : ∀ v, (Project.FirstOrderSemantics.reduct M).mem v V → ∃ C, schema.denote env v C := by
    intro v _
    obtain ⟨C,hC⟩ := exists_class hM D I mul q V v
    exact ⟨C,(he v C).mpr hC⟩
  have hu : ∀ v C E, schema.denote env v C → schema.denote env v E → C = E :=
    fun v C E hC hE => class_unique hM ((he v C).mp hC) ((he v E).mp hE)
  obtain ⟨Q,hQ⟩ := ZF.exists_functionalImage (ModelTransfer.project_models_iff.mp hM) schema env V ht hu
  obtain ⟨pr,hpr,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env ht (fun v _ C E hC hE => hu v C E hC hE)
    (fun v C hv hC => (hQ C).mpr ⟨v,hv,hC⟩)
  refine ⟨Q,pr,(ForcingSupportSize.native_mapsTo hM V Q pr).mpr hpr,?_,?_⟩
  · intro C
    exact (hQ C).trans ⟨fun ⟨v,hv,hC⟩ => ⟨v,hv,(he v C).mp hC⟩,
      fun ⟨v,hv,hC⟩ => ⟨v,hv,(he v C).mpr hC⟩⟩
  · exact fun v C => (hEdge v C).trans (and_congr Iff.rfl (he v C))

def Laws (D I mul q pr : M.Carrier .set) : Prop := ∀ v w C E,
  PureKuratowski.PairMember M v C pr → PureKuratowski.PairMember M w E pr →
    (C = E ↔ OrbitRel D I mul q v w) ∧
    (EncodedCommon D I mul q v w → C = E) ∧
    ∀ pi, Permutation I pi → CompositionGraph D pi q q →
      ForcingComponentMove.Move D I mul q pi v w → C = E

theorem quotient_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul one q V pr : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul one)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul) (hq : Injection D I q)
    (hV : ConstructionComponentCarrier.Carrier D I mul q V) (hPr : Projection D I mul q V pr) : Laws D I mul q pr := by
  intro v w C E hv hw
  obtain ⟨_,hC⟩ := (hPr v C).mp hv
  obtain ⟨hwV,hE⟩ := (hPr w E).mp hw
  have hEq := class_eq_iff hM hm hJ hq hV hwV hC hE
  exact ⟨hEq,fun h => hEq.mpr (orbit_common hM hq h),
    fun pi hPi hFix hMove => hEq.mpr (orbit_symm hM hq (orbit_move hm hPi hFix hMove))⟩

def laws {m : Nat} (D I mul q pr : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge pr.succ.succ.succ.succ 3 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge pr.succ.succ.succ.succ 2 0)) (.conj (.iff (Project.Formula.extensionalEq (.bound 1) (.bound 0)) (orbitRel D.succ.succ.succ.succ I.succ.succ.succ.succ mul.succ.succ.succ.succ q.succ.succ.succ.succ 3 2)) (.conj (.imp (ConstructionComponentCofinal.encodedCommon D.succ.succ.succ.succ I.succ.succ.succ.succ mul.succ.succ.succ.succ q.succ.succ.succ.succ 3 2) (Project.Formula.extensionalEq (.bound 1) (.bound 0))) (.forallE (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I.succ.succ.succ.succ.succ 0)) (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph D.succ.succ.succ.succ.succ 0 q.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ)) (.imp (ForcingComponentMove.move D.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ 0 4 3) (Project.Formula.extensionalEq (.bound 2) (.bound 1))))))))))))))

theorem laws_freeClosed {m : Nat} (D I mul q pr : Fin m) : (laws D I mul q pr).FreeClosed := by
  simp -implicitDefEqProofs [laws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.extensionalEq,ForcingOrbitAssignment.orbitRel_freeClosed,
    ConstructionComponentCofinal.encodedCommon_freeClosed,ForcingComponentMove.move_freeClosed]

theorem laws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q pr : Fin m) :
    Project.Formula.satisfies env (laws D I mul q pr) ↔
      Laws (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound pr) := by
  simp only [laws,Laws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ForcingOrbitAssignment.orbitRel_semantics hM,ConstructionComponentCofinal.encodedCommon_semantics hM,
    ForcingComponentMove.move_semantics hM]
  rfl

def constructionSentence {k : Nat} (D I mul one q : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul one)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q D I)) (.existsE (.existsE (.existsE (.conj (ConstructionComponentCarrier.carrier D.succ.succ.succ I.succ.succ.succ mul.succ.succ.succ q.succ.succ.succ 2) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 0 2 1)) (.conj (classes D.succ.succ.succ I.succ.succ.succ mul.succ.succ.succ q.succ.succ.succ 2 1) (.conj (projection D.succ.succ.succ I.succ.succ.succ mul.succ.succ.succ q.succ.succ.succ 2 0) (laws D.succ.succ.succ I.succ.succ.succ mul.succ.succ.succ q.succ.succ.succ 0)))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionComponentCarrier.carrier_freeClosed,
      classes_freeClosed,projection_freeClosed,laws_freeClosed]

theorem construction_models {k : Nat} (D I mul one q : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence D I mul one q)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingSupportSize.injection_semantics (M := M),ConstructionComponentCarrier.carrier_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),classes_semantics hM,projection_semantics hM,laws_semantics hM]
  intro hm hJ hq
  obtain ⟨V,hV⟩ := ConstructionComponentCarrier.exists_carrier hM (bound D) (bound I) (bound mul) (bound q)
  obtain ⟨Q,pr,hpr,hQ,hPr⟩ := exists_quotient hM (bound D) (bound I) (bound mul) (bound q) V
  exact ⟨V,Q,pr,hV,hpr,hQ,hPr,quotient_laws hM hm hJ hq hV hPr⟩

theorem construction_kernel_certificate {k : Nat} (D I mul one q : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence D I mul one q)) :=
  ModelTransfer.derives (fun _ hM => construction_models D I mul one q hM)

end PPAC.Migration.ForcingOrbitQuotient
