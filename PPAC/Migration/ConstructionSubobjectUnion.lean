/- Pinned CellReorder.Subobject.directedSup and unionLift/unionLift_comp.
The union is the actual union inside the SAME terminal carrier. Glued maps
have arbitrary internal targets; no injectivity/conservativity/Choice premise
is imposed on the target or cocone. Consumer: Square.union -> future_cut. -/
import PPAC.Migration.ConstructionCellRestriction

namespace PPAC.Migration.ConstructionSubobjectUnion
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionDirectedSystem (IndexLaws)
open ConstructionBlockStages (MonotoneImages)
open ConstructionCellRestriction (Stages)
open ConstructionConservativeHull (Closure ProductGraph)
open ConstructionRealCuts (Subset)
open ConstructionProbePushout (Hom)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionDirectedWeightData (WeightFamily)
open ForcingConditionGraphs (FunctionOn IdentityGraph function_input function_unique)
open ForcingSupportSize (MapsTo)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Union (K Domains U : M.Carrier .set) : Prop := ∀ x,
  (Project.FirstOrderSemantics.reduct M).mem x U ↔ ∃ i D,
    (Project.FirstOrderSemantics.reduct M).mem i K ∧ PureKuratowski.PairMember M i D Domains ∧
    (Project.FirstOrderSemantics.reduct M).mem x D

/-- Directly reuse native function range and set union, also for families
whose values are graphs. No new image/recursion constructor. -/
theorem exists_union (hM : FirstOrder.Theory.Models M nativeZF)
    {K Domains : M.Carrier .set} (hD : FunctionOn K Domains) : ∃ U, Union K Domains U := by
  have hFun : (Project.FirstOrderSemantics.reduct M).IsSetFunction (KuratowskiZF.interpretation hM) Domains :=
    ⟨fun z hz => by obtain ⟨x,y,_,hxy⟩ := hD.1 z hz; exact ⟨x,y,hxy⟩,
      fun x y z hy hz => function_unique hD hy hz⟩
  have hDom : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i K ↔
      ∃ D, PureKuratowski.PairMember M i D Domains :=
    fun i => ⟨fun hi => by obtain ⟨D,hD,_⟩ := hD.2 i hi; exact ⟨D,hD⟩,
      fun ⟨D,hi⟩ => function_input hD hi⟩
  obtain ⟨R,hR⟩ := ZF.exists_range_of_setFunction (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) hFun hDom
  obtain ⟨U,hU⟩ := KP.exists_union (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) R
  refine ⟨U,fun x => ?_⟩
  constructor
  · intro hx
    obtain ⟨D,hDR,hxD⟩ := (hU x).mp hx
    obtain ⟨i,hiD⟩ := (hR D).mp hDR
    exact ⟨i,D,function_input hD hiD,hiD,hxD⟩
  · rintro ⟨i,D,_,hiD,hxD⟩
    exact (hU x).mpr ⟨D,(hR D).mpr ⟨i,hiD⟩,hxD⟩

theorem common {K E Domains U x y : M.Carrier .set}
    (hE : IndexLaws K E) (hD : FunctionOn K Domains) (hMono : MonotoneImages K E Domains)
    (hU : Union K Domains U) (hx : (Project.FirstOrderSemantics.reduct M).mem x U)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y U) :
    ∃ k D, (Project.FirstOrderSemantics.reduct M).mem k K ∧ PureKuratowski.PairMember M k D Domains ∧
      (Project.FirstOrderSemantics.reduct M).mem x D ∧ (Project.FirstOrderSemantics.reduct M).mem y D := by
  obtain ⟨i,Di,hi,hDi,hx⟩ := (hU x).mp hx
  obtain ⟨j,Dj,hj,hDj,hy⟩ := (hU y).mp hy
  obtain ⟨k,hk,hik,hjk⟩ := hE.2.2 i j hi hj
  obtain ⟨D,hDk,_⟩ := hD.2 k hk
  exact ⟨k,D,hk,hDk,hMono i k Di D hi hk hik hDi hDk x hx,hMono j k Dj D hj hk hjk hDj hDk y hy⟩

theorem closed {V GV e K E Domains U : M.Carrier .set}
    (hE : IndexLaws K E) (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i K)
    (hD : FunctionOn K Domains) (hMono : MonotoneImages K E Domains)
    (hStages : Stages V GV e Domains) (hU : Union K Domains U) : Closure V GV e U := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro x hx
    obtain ⟨i,D,_,hiD,hxD⟩ := (hU x).mp hx
    exact (hStages i D hiD).1 x hxD
  · obtain ⟨i,hi⟩ := hne
    obtain ⟨D,hiD,_⟩ := hD.2 i hi
    exact (hU e).mpr ⟨i,D,hi,hiD,(hStages i D hiD).2.1⟩
  · intro x y z hx hy hp
    obtain ⟨i,D,hi,hiD,hxD,hyD⟩ := common hE hD hMono hU hx hy
    exact (hU z).mpr ⟨i,D,hi,hiD,(hStages i D hiD).2.2.1 x y z hxD hyD hp⟩
  · intro x y z hx hy hz hp
    obtain ⟨i,D,hi,hiD,hxD,hyD⟩ := common hE hD hMono hU hx hy
    exact (hU z).mpr ⟨i,D,hi,hiD,(hStages i D hiD).2.2.2.1 x y z hxD hyD hz hp⟩
  · intro x y z hx hy hz hp
    obtain ⟨i,D,hi,hiD,hxD,hyD⟩ := common hE hD hMono hU hx hy
    exact (hU z).mpr ⟨i,D,hi,hiD,(hStages i D hiD).2.2.2.2 x y z hxD hyD hz hp⟩

theorem directedSup (hM : FirstOrder.Theory.Models M nativeZF)
    {V GV e K E Domains : M.Carrier .set}
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins V GV)
    (hE : IndexLaws K E) (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i K)
    (hD : FunctionOn K Domains) (hMono : MonotoneImages K E Domains)
    (hStages : Stages V GV e Domains) :
    ∃ U pairs GU inc, Union K Domains U ∧ ConstructionSelectedCellRestriction.Base V GV e U pairs GU inc := by
  obtain ⟨U,hU⟩ := exists_union hM hD
  have hClosed := closed hE hne hD hMono hStages hU
  obtain ⟨pairs,GU,inc,h⟩ := ConstructionConservativeHull.exists_submonoid hM hv hc hJ hClosed
  exact ⟨U,pairs,GU,inc,hU,hClosed,h⟩

/-- Source cocone uses the actual restricted multiplication at each stage.
No target algebraic property beyond these Hom laws is assumed. -/
def Cocone (K Domains Muls Legs GV e N GN unitN : M.Carrier .set) : Prop :=
  FunctionOn K Muls ∧ WeightFamily K Domains N Legs ∧ ∀ i D G f,
    (Project.FirstOrderSemantics.reduct M).mem i K → PureKuratowski.PairMember M i D Domains →
    PureKuratowski.PairMember M i G Muls → PureKuratowski.PairMember M i f Legs →
    ProductGraph D GV G ∧ Hom D N G GN e unitN f

def Compatible (K E Domains Legs : M.Carrier .set) : Prop := ∀ i j D f g x y,
  (Project.FirstOrderSemantics.reduct M).mem i K → (Project.FirstOrderSemantics.reduct M).mem j K →
  PureKuratowski.PairMember M i j E → PureKuratowski.PairMember M i D Domains →
  PureKuratowski.PairMember M i f Legs → PureKuratowski.PairMember M j g Legs →
  (Project.FirstOrderSemantics.reduct M).mem x D → PureKuratowski.PairMember M x y f →
  PureKuratowski.PairMember M x y g

def Graph (K Legs lift : M.Carrier .set) : Prop := ∀ x y,
  PureKuratowski.PairMember M x y lift ↔ ∃ i f,
    (Project.FirstOrderSemantics.reduct M).mem i K ∧ PureKuratowski.PairMember M i f Legs ∧
    PureKuratowski.PairMember M x y f

def Restricts (K Domains Legs lift : M.Carrier .set) : Prop := ∀ i D f x y,
  (Project.FirstOrderSemantics.reduct M).mem i K → PureKuratowski.PairMember M i D Domains →
  PureKuratowski.PairMember M i f Legs → (Project.FirstOrderSemantics.reduct M).mem x D →
  (PureKuratowski.PairMember M x y lift ↔ PureKuratowski.PairMember M x y f)

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {K Legs : M.Carrier .set} (hf : FunctionOn K Legs) : ∃ lift,
      Union K Legs lift ∧ Graph K Legs lift := by
  obtain ⟨lift,hU⟩ := exists_union hM hf
  refine ⟨lift,hU,fun x y => ?_⟩
  constructor
  · rintro ⟨z,hxy,hz⟩
    obtain ⟨i,f,hi,hif,hzf⟩ := (hU z).mp hz
    exact ⟨i,f,hi,hif,z,hxy,hzf⟩
  · rintro ⟨i,f,hi,hif,z,hxy,hzf⟩
    exact ⟨z,hxy,(hU z).mpr ⟨i,f,hi,hif,hzf⟩⟩

theorem value_unique {K E Domains Legs N x y z : M.Carrier .set}
    (hE : IndexLaws K E) (hD : FunctionOn K Domains) (hLegs : WeightFamily K Domains N Legs)
    (hStable : Compatible K E Domains Legs)
    (hy : ∃ i f, (Project.FirstOrderSemantics.reduct M).mem i K ∧ PureKuratowski.PairMember M i f Legs ∧ PureKuratowski.PairMember M x y f)
    (hz : ∃ i f, (Project.FirstOrderSemantics.reduct M).mem i K ∧ PureKuratowski.PairMember M i f Legs ∧ PureKuratowski.PairMember M x z f) : y = z := by
  obtain ⟨i,f,hi,hif,hxy⟩ := hy
  obtain ⟨j,g,hj,hjg,hxz⟩ := hz
  obtain ⟨Di,hDi,_⟩ := hD.2 i hi
  obtain ⟨Dj,hDj,_⟩ := hD.2 j hj
  obtain ⟨k,hk,hik,hjk⟩ := hE.2.2 i j hi hj
  obtain ⟨Dk,hDk,_⟩ := hD.2 k hk
  obtain ⟨t,hkt,_⟩ := hLegs.1.2 k hk
  exact function_unique (hLegs.2 k Dk t hk hDk hkt).1
    (hStable i k Di f t x y hi hk hik hDi hif hkt (function_input (hLegs.2 i Di f hi hDi hif).1 hxy) hxy)
    (hStable j k Dj g t x z hj hk hjk hDj hjg hkt (function_input (hLegs.2 j Dj g hj hDj hjg).1 hxz) hxz)

theorem graph_maps {K E Domains Legs U N lift : M.Carrier .set}
    (hE : IndexLaws K E) (hD : FunctionOn K Domains) (hLegs : WeightFamily K Domains N Legs)
    (hStable : Compatible K E Domains Legs) (hU : Union K Domains U)
    (hUnion : Union K Legs lift) (hGraph : Graph K Legs lift) : MapsTo U N lift := by
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro z hz
    obtain ⟨i,f,hi,hif,hzf⟩ := (hUnion z).mp hz
    obtain ⟨D,hDi,_⟩ := hD.2 i hi
    obtain ⟨x,y,hx,hcode⟩ := (hLegs.2 i D f hi hDi hif).1.1 z hzf
    exact ⟨x,y,(hU x).mpr ⟨i,D,hi,hDi,hx⟩,hcode⟩
  · intro x hx
    obtain ⟨i,D,hi,hDi,hxD⟩ := (hU x).mp hx
    obtain ⟨f,hif,_⟩ := hLegs.1.2 i hi
    obtain ⟨y,hxy,_⟩ := (hLegs.2 i D f hi hDi hif).1.2 x hxD
    refine ⟨y,(hGraph x y).mpr ⟨i,f,hi,hif,hxy⟩,?_⟩
    intro z hxz
    exact value_unique hE hD hLegs hStable ((hGraph x z).mp hxz) ⟨i,f,hi,hif,hxy⟩
  · intro x y hxy
    obtain ⟨i,f,hi,hif,hxy⟩ := (hGraph x y).mp hxy
    obtain ⟨D,hDi,_⟩ := hD.2 i hi
    exact (hLegs.2 i D f hi hDi hif).2 x y hxy

theorem restricts {K Domains Legs U N lift : M.Carrier .set}
    (hLegs : WeightFamily K Domains N Legs) (hMap : MapsTo U N lift) (hGraph : Graph K Legs lift) :
    Restricts K Domains Legs lift := by
  intro i D f x y hi hDi hif hxD
  constructor
  · intro hxy
    obtain ⟨z,hxz,_⟩ := (hLegs.2 i D f hi hDi hif).1.2 x hxD
    exact (function_unique hMap.1 ((hGraph x z).mpr ⟨i,f,hi,hif,hxz⟩) hxy) ▸ hxz
  · intro hxy
    exact (hGraph x y).mpr ⟨i,f,hi,hif,hxy⟩

theorem exists_lift (hM : FirstOrder.Theory.Models M nativeZF)
    {V GV e K E Domains Muls Legs U GU N GN unitN : M.Carrier .set}
    (hE : IndexLaws K E) (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i K)
    (hD : FunctionOn K Domains) (hMono : MonotoneImages K E Domains)
    (hStages : Stages V GV e Domains) (hC : Cocone K Domains Muls Legs GV e N GN unitN)
    (hStable : Compatible K E Domains Legs) (hU : Union K Domains U) (hGU : ProductGraph U GV GU) :
    ∃ lift, Hom U N GU GN e unitN lift ∧ Graph K Legs lift ∧ Restricts K Domains Legs lift := by
  obtain ⟨lift,hUnion,hGraph⟩ := exists_graph hM hC.2.1.1
  have hMap := graph_maps hE hD hC.2.1 hStable hU hUnion hGraph
  have hRestrict := restricts hC.2.1 hMap hGraph
  refine ⟨lift,⟨hMap,?_,?_⟩,hGraph,hRestrict⟩
  · obtain ⟨i,hi⟩ := hne
    obtain ⟨D,hDi,_⟩ := hD.2 i hi
    obtain ⟨G,hGi,_⟩ := hC.1.2 i hi
    obtain ⟨f,hif,_⟩ := hC.2.1.1.2 i hi
    exact (hGraph e unitN).mpr ⟨i,f,hi,hif,(hC.2.2 i D G f hi hDi hGi hif).2.2.1⟩
  · intro x y z fx fy fz hp hx hy hz
    obtain ⟨hxU,hyU,hpV⟩ := (hGU x y z).mp hp
    obtain ⟨i,D,hi,hDi,hxD,hyD⟩ := common hE hD hMono hU hxU hyU
    have hzD := (hStages i D hDi).2.2.1 x y z hxD hyD hpV
    obtain ⟨G,hGi,_⟩ := hC.1.2 i hi
    obtain ⟨f,hif,_⟩ := hC.2.1.1.2 i hi
    have hLocal := hC.2.2 i D G f hi hDi hGi hif
    exact hLocal.2.2.2 x y z fx fy fz ((hLocal.1 x y z).mpr ⟨hxD,hyD,hpV⟩)
      ((hRestrict i D f x fx hi hDi hif hxD).mp hx)
      ((hRestrict i D f y fy hi hDi hif hyD).mp hy)
      ((hRestrict i D f z fz hi hDi hif hzD).mp hz)

theorem unique (hM : FirstOrder.Theory.Models M nativeZF)
    {K Domains Legs U N lift other : M.Carrier .set}
    (hLegs : WeightFamily K Domains N Legs) (hU : Union K Domains U)
    (hMap : MapsTo U N lift) (hOther : MapsTo U N other)
    (hR : Restricts K Domains Legs lift) (hS : Restricts K Domains Legs other) : other = lift := by
  apply SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM U N other).mp hOther).1.1
    ((ForcingSupportSize.native_mapsTo hM U N lift).mp hMap).1.1
  intro x y
  constructor
  · intro hxy
    obtain ⟨i,D,hi,hDi,hxD⟩ := (hU x).mp (function_input hOther.1 hxy)
    obtain ⟨f,hif,_⟩ := hLegs.1.2 i hi
    exact (hR i D f x y hi hDi hif hxD).mpr ((hS i D f x y hi hDi hif hxD).mp hxy)
  · intro hxy
    obtain ⟨i,D,hi,hDi,hxD⟩ := (hU x).mp (function_input hMap.1 hxy)
    obtain ⟨f,hif,_⟩ := hLegs.1.2 i hi
    exact (hS i D f x y hi hDi hif hxD).mpr ((hR i D f x y hi hDi hif hxD).mp hxy)

theorem universal_lift (hM : FirstOrder.Theory.Models M nativeZF)
    {V GV e K E Domains Muls Legs U GU N GN unitN : M.Carrier .set}
    (hE : IndexLaws K E) (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i K)
    (hD : FunctionOn K Domains) (hMono : MonotoneImages K E Domains)
    (hStages : Stages V GV e Domains) (hC : Cocone K Domains Muls Legs GV e N GN unitN)
    (hStable : Compatible K E Domains Legs) (hU : Union K Domains U) (hGU : ProductGraph U GV GU) :
    ∃ lift, Hom U N GU GN e unitN lift ∧ Graph K Legs lift ∧ Restricts K Domains Legs lift ∧
      ∀ other, Hom U N GU GN e unitN other → Restricts K Domains Legs other → other = lift := by
  obtain ⟨lift,hL,hGraph,hR⟩ := exists_lift hM hE hne hD hMono hStages hC hStable hU hGU
  exact ⟨lift,hL,hGraph,hR,fun other hOther hS => unique hM hC.2.1 hU hL.1 hOther.1 hR hS⟩

theorem factorization {K Domains Legs N lift i D f inc : M.Carrier .set}
    (hLegs : WeightFamily K Domains N Legs)
    (hR : Restricts K Domains Legs lift) (hi : (Project.FirstOrderSemantics.reduct M).mem i K)
    (hDi : PureKuratowski.PairMember M i D Domains) (hif : PureKuratowski.PairMember M i f Legs)
    (hInc : IdentityGraph D inc) : NodeMap inc lift f := by
  intro x y
  constructor
  · intro hxy
    have hxD := function_input (hLegs.2 i D f hi hDi hif).1 hxy
    exact ⟨x,(hInc x x).mpr ⟨hxD,rfl⟩,(hR i D f x y hi hDi hif hxD).mpr hxy⟩
  · rintro ⟨z,hxz,hzy⟩
    obtain ⟨hxD,rfl⟩ := (hInc x z).mp hxz
    exact (hR i D f x y hi hDi hif hxD).mp hzy



def unionFormula {m : Nat} (K Domains U : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound 0) (.bound U.succ)) (.existsE (.existsE (.conj (.mem (.bound 1) (.bound K.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge Domains.succ.succ.succ 1 0)) (.mem (.bound 2) (.bound 0))))))))

theorem unionFormula_freeClosed {m : Nat} (K Domains U : Fin m) :
    (unionFormula K Domains U).FreeClosed := by
  simp -implicitDefEqProofs [unionFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem unionFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (K Domains U : Fin m) :
    Project.Formula.satisfies env (unionFormula K Domains U) ↔ Union (env.bound K) (env.bound Domains) (env.bound U) := by
  simp only [unionFormula,Union,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def cocone {m : Nat} (K Domains Muls Legs GV e N GN unitN : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn Muls K)) (.conj (ConstructionDirectedWeightData.weightFamily K Domains N Legs) (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 3) (.bound K.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Domains.succ.succ.succ.succ 3 2)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Muls.succ.succ.succ.succ 3 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Legs.succ.succ.succ.succ 3 0)) (.conj (ConstructionConservativeHull.productGraph 2 GV.succ.succ.succ.succ 1) (ConstructionProbePushoutSyntax.hom 2 N.succ.succ.succ.succ 1 GN.succ.succ.succ.succ e.succ.succ.succ.succ unitN.succ.succ.succ.succ 0))))))))))))

theorem cocone_freeClosed {m : Nat} (K Domains Muls Legs GV e N GN unitN : Fin m) :
    (cocone K Domains Muls Legs GV e N GN unitN).FreeClosed := by
  simp -implicitDefEqProofs [cocone,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionDirectedWeightData.weightFamily_freeClosed,ConstructionConservativeHull.productGraph_freeClosed,ConstructionProbePushoutSyntax.hom_freeClosed]

theorem cocone_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (K Domains Muls Legs GV e N GN unitN : Fin m) :
    Project.Formula.satisfies env (cocone K Domains Muls Legs GV e N GN unitN) ↔ Cocone (env.bound K) (env.bound Domains) (env.bound Muls) (env.bound Legs) (env.bound GV) (env.bound e) (env.bound N) (env.bound GN) (env.bound unitN) := by
  simp only [cocone,Cocone,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConditionGraphs.functionOn_semantics (M := M),KuratowskiZF.source_edge,ConstructionDirectedWeightData.weightFamily_semantics hM,ConstructionConservativeHull.productGraph_semantics hM,ConstructionProbePushoutSyntax.hom_semantics hM]
  rfl

def compatible {m : Nat} (K E Domains Legs : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 6) (.bound K.succ.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound 5) (.bound K.succ.succ.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge E.succ.succ.succ.succ.succ.succ.succ 6 5)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Domains.succ.succ.succ.succ.succ.succ.succ 6 4)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Legs.succ.succ.succ.succ.succ.succ.succ 6 3)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Legs.succ.succ.succ.succ.succ.succ.succ 5 2)) (.imp (.mem (.bound 1) (.bound 4)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 3 1 0)) (ProjectSyntax.encode id (Source.SetLanguage.edge 2 1 0)))))))))))))))))

theorem compatible_freeClosed {m : Nat} (K E Domains Legs : Fin m) :
    (compatible K E Domains Legs).FreeClosed := by
  simp -implicitDefEqProofs [compatible,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem compatible_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (K E Domains Legs : Fin m) :
    Project.Formula.satisfies env (compatible K E Domains Legs) ↔ Compatible (env.bound K) (env.bound E) (env.bound Domains) (env.bound Legs) := by
  simp only [compatible,Compatible,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def graph {m : Nat} (K Legs lift : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge lift.succ.succ 1 0)) (.existsE (.existsE (.conj (.mem (.bound 1) (.bound K.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge Legs.succ.succ.succ.succ 1 0)) (ProjectSyntax.encode id (Source.SetLanguage.edge 0 3 2)))))))))

theorem graph_freeClosed {m : Nat} (K Legs lift : Fin m) :
    (graph K Legs lift).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (K Legs lift : Fin m) :
    Project.Formula.satisfies env (graph K Legs lift) ↔ Graph (env.bound K) (env.bound Legs) (env.bound lift) := by
  simp only [graph,Graph,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def restrictsFormula {m : Nat} (K Domains Legs lift : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 4) (.bound K.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Domains.succ.succ.succ.succ.succ 4 3)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Legs.succ.succ.succ.succ.succ 4 2)) (.imp (.mem (.bound 1) (.bound 3)) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge lift.succ.succ.succ.succ.succ 1 0)) (ProjectSyntax.encode id (Source.SetLanguage.edge 2 1 0))))))))))))

theorem restrictsFormula_freeClosed {m : Nat} (K Domains Legs lift : Fin m) :
    (restrictsFormula K Domains Legs lift).FreeClosed := by
  simp -implicitDefEqProofs [restrictsFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem restrictsFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (K Domains Legs lift : Fin m) :
    Project.Formula.satisfies env (restrictsFormula K Domains Legs lift) ↔ Restricts (env.bound K) (env.bound Domains) (env.bound Legs) (env.bound lift) := by
  simp only [restrictsFormula,Restricts,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def directedSupSentence {m : Nat} (V GV e K E Domains : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV) (.imp (ConstructionDirectedSystem.indexLaws K E) (.imp (.existsE (.mem (.bound 0) (.bound K.succ))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn Domains K)) (.imp (ConstructionBlockStages.monotoneImages K E Domains) (.imp (ConstructionCellRestriction.stages V GV e Domains) (.existsE (.existsE (.existsE (.existsE (.conj (unionFormula K.succ.succ.succ.succ Domains.succ.succ.succ.succ 3) (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ GV.succ.succ.succ.succ e.succ.succ.succ.succ 3 2 1 0))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionDirectedSystem.indexLaws_freeClosed,ConstructionBlockStages.monotoneImages_freeClosed,ConstructionCellRestriction.stages_freeClosed,unionFormula_freeClosed,ConstructionSelectedCellRestriction.baseFormula_freeClosed]

theorem directedSup_models {m : Nat} (V GV e K E Domains : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (directedSupSentence V GV e K E Domains)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (directedSupSentence V GV e K E Domains)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ForcingConditionGraphs.functionOn_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionDirectedSystem.indexLaws_semantics hM,ConstructionBlockStages.monotoneImages_semantics hM,ConstructionCellRestriction.stages_semantics hM,unionFormula_semantics hM,ConstructionSelectedCellRestriction.baseFormula_semantics hM]
  exact directedSup hM

theorem directedSup_kernel_certificate {m : Nat} (V GV e K E Domains : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (directedSupSentence V GV e K E Domains)) :=
  ModelTransfer.derives (fun _ hM => directedSup_models V GV e K E Domains hM)

def liftSentence {m : Nat} (V GV e K E Domains Muls Legs U GU N GN unitN : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionDirectedSystem.indexLaws K E) (.imp (.existsE (.mem (.bound 0) (.bound K.succ))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn Domains K)) (.imp (ConstructionBlockStages.monotoneImages K E Domains) (.imp (ConstructionCellRestriction.stages V GV e Domains) (.imp (cocone K Domains Muls Legs GV e N GN unitN) (.imp (compatible K E Domains Legs) (.imp (unionFormula K Domains U) (.imp (ConstructionConservativeHull.productGraph U GV GU) (.existsE (.conj (ConstructionProbePushoutSyntax.hom U.succ N.succ GU.succ GN.succ e.succ unitN.succ 0) (.conj (graph K.succ Legs.succ 0) (.conj (restrictsFormula K.succ Domains.succ Legs.succ 0) (.forallE (.imp (ConstructionProbePushoutSyntax.hom U.succ.succ N.succ.succ GU.succ.succ GN.succ.succ e.succ.succ unitN.succ.succ 0) (.imp (restrictsFormula K.succ.succ Domains.succ.succ Legs.succ.succ 0) (Project.Formula.extensionalEq (.bound 0) (.bound 1))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionDirectedSystem.indexLaws_freeClosed,ConstructionBlockStages.monotoneImages_freeClosed,ConstructionCellRestriction.stages_freeClosed,cocone_freeClosed,compatible_freeClosed,unionFormula_freeClosed,ConstructionConservativeHull.productGraph_freeClosed,ConstructionProbePushoutSyntax.hom_freeClosed,graph_freeClosed,restrictsFormula_freeClosed,Project.Formula.extensionalEq]

theorem lift_models {m : Nat} (V GV e K E Domains Muls Legs U GU N GN unitN : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (liftSentence V GV e K E Domains Muls Legs U GU N GN unitN)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (liftSentence V GV e K E Domains Muls Legs U GU N GN unitN)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConditionGraphs.functionOn_semantics (M := M),ConstructionDirectedSystem.indexLaws_semantics hM,ConstructionBlockStages.monotoneImages_semantics hM,ConstructionCellRestriction.stages_semantics hM,cocone_semantics hM,compatible_semantics hM,unionFormula_semantics hM,ConstructionConservativeHull.productGraph_semantics hM,ConstructionProbePushoutSyntax.hom_semantics hM,graph_semantics hM,restrictsFormula_semantics hM]
  exact universal_lift hM

theorem lift_kernel_certificate {m : Nat} (V GV e K E Domains Muls Legs U GU N GN unitN : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (liftSentence V GV e K E Domains Muls Legs U GU N GN unitN)) :=
  ModelTransfer.derives (fun _ hM => lift_models V GV e K E Domains Muls Legs U GU N GN unitN hM)

def factorizationSentence {m : Nat} (K Domains Legs N lift i D f inc : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionDirectedWeightData.weightFamily K Domains N Legs) (.imp (restrictsFormula K Domains Legs lift) (.imp (.mem (.bound i) (.bound K)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Domains i D)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Legs i f)) (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph D inc)) (ConstructionProbeMappedPathSyntax.nodeMap inc lift f)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionDirectedWeightData.weightFamily_freeClosed,restrictsFormula_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed]

theorem factorization_models {m : Nat} (K Domains Legs N lift i D f inc : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (factorizationSentence K Domains Legs N lift i D f inc)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (factorizationSentence K Domains Legs N lift i D f inc)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingConditionGraphs.identityGraph_semantics (M := M),ConstructionDirectedWeightData.weightFamily_semantics hM,restrictsFormula_semantics hM,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM]
  exact factorization

theorem factorization_kernel_certificate {m : Nat} (K Domains Legs N lift i D f inc : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (factorizationSentence K Domains Legs N lift i D f inc)) :=
  ModelTransfer.derives (fun _ hM => factorization_models K Domains Legs N lift i D f inc hM)

end PPAC.Migration.ConstructionSubobjectUnion
