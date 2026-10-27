/- Pinned DirectLimits.height/cost:181/184. Construct the actual two
quotient-descended function graphs by the accepted native function constructor.
No new quotient or representative choice; source hρ/hε give well-definedness. -/
import PPAC.Migration.ConstructionDirectedWeightData

namespace PPAC.Migration.ConstructionDirectedWeights
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionDirectedSystem
open ConstructionDirectedWeightData
open ConstructionDirectedLimitCarrier (Representatives Carrier Projection EqualityLaw)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}
variable {J E Domains F Weights R C L projection W : M.Carrier .set}

def Value (J Domains Weights projection a r : M.Carrier .set) : Prop :=
  ∃ i x Wi, At J Domains i x ∧ PureKuratowski.PairMember M i Wi Weights ∧
    PureKuratowski.PairMember M x r Wi ∧ Product projection i x a

def Graph (J Domains Weights projection W : M.Carrier .set) : Prop :=
  ∀ a r, PureKuratowski.PairMember M a r W ↔ Value J Domains Weights projection a r

theorem value_range (hWF : WeightFamily J Domains R Weights) {a r : M.Carrier .set}
    (hv : Value J Domains Weights projection a r) : (Project.FirstOrderSemantics.reduct M).mem r R := by
  obtain ⟨i,x,Wi,hx,hWi,hxr,_⟩ := hv
  obtain ⟨D,hD,hxD⟩ := hx.2
  exact (hWF.2 i D Wi hx.1 hD hWi).2 x r hxr

theorem value_total (hWF : WeightFamily J Domains R Weights)
    (hC : Representatives J Domains C) (hL : Carrier J E Domains F C L)
    (hP : Projection J E Domains F C projection) {a : M.Carrier .set}
    (ha : (Project.FirstOrderSemantics.reduct M).mem a L) : ∃ r, Value J Domains Weights projection a r := by
  obtain ⟨i,x,hx,hpx⟩ := ConstructionDirectedLimitCarrier.representative hC hL hP ha
  obtain ⟨D,hD,hxD⟩ := hx.2
  obtain ⟨Wi,hWi,_⟩ := hWF.1.2 i hx.1
  obtain ⟨r,hxr,_⟩ := (hWF.2 i D Wi hx.1 hD hWi).1.2 x hxD
  exact ⟨r,i,x,Wi,hx,hWi,hxr,hpx⟩

theorem value_unique (hWF : WeightFamily J Domains R Weights)
    (hStable : Stable J E Domains F Weights) (hEq : EqualityLaw J E Domains F projection)
    {a r s : M.Carrier .set} (hr : Value J Domains Weights projection a r)
    (hs : Value J Domains Weights projection a s) : r = s := by
  obtain ⟨i,x,Wi,hx,hWi,hxr,hpx⟩ := hr
  obtain ⟨j,y,Wj,hy,hWj,hys,hpy⟩ := hs
  obtain ⟨_,_,k,z,hk,hik,hjk,hxz,hyz⟩ := (ConstructionDirectedLimitCarrier.projected_eq_iff hEq hpx hpy).mp rfl
  obtain ⟨Dk,hDk,_⟩ := hxz.2.1.2
  obtain ⟨Wk,hWk,_⟩ := hWF.1.2 k hk
  exact ForcingConditionGraphs.function_unique (hWF.2 k Dk Wk hk hDk hWk).1
    (hStable i k x z r Wi Wk hik hxz hWi hWk hxr)
    (hStable j k y z s Wj Wk hjk hyz hWj hWk hys)


def value {m : Nat} (J Domains Weights projection a r : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.conj (ConstructionDirectedSystem.atStage J.succ.succ.succ
  Domains.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3))) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge Weights.succ.succ.succ (2 : Fin (m+3)) (0 : Fin (m+3)))) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin (m+3)) (1 : Fin (m+3)) r.succ.succ.succ))
  (ProjectSyntax.encode id (ForcingDiagramOrder.product projection.succ.succ.succ (2 : Fin (m+3)) (1 : Fin
  (m+3)) a.succ.succ.succ))))))))

theorem value_freeClosed {m : Nat} (J Domains Weights projection a r : Fin m) :
    (value J Domains Weights projection a r).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionDirectedSystem.atStage_freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains Weights projection a r : Fin m) :
    Project.Formula.satisfies env (value J Domains Weights projection a r) ↔ Value (env.bound J) (env.bound Domains) (env.bound Weights) (env.bound projection) (env.bound a) (env.bound r) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionDirectedSystem.atStage_semantics hM,ForcingDiagramOrder.product_semantics (M := M)]
  rfl

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF)
    (hWF : WeightFamily J Domains R Weights) (hStable : Stable J E Domains F Weights)
    (hC : Representatives J Domains C) (hL : Carrier J E Domains F C L)
    (hP : Projection J E Domains F C projection) (hEq : EqualityLaw J E Domains F projection) :
    ∃ W, MapsTo L R W ∧ Graph J Domains Weights projection W := by
  let schema : Project.BinarySchema 4 := {
    body := value 2 3 4 5 1 0
    freeClosed := value_freeClosed _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 := {
    bound := Fin.cases J (Fin.cases Domains (Fin.cases Weights (fun _ => projection))), free := fun _ => J }
  have he (a r) : schema.denote env a r ↔ Value J Domains Weights projection a r :=
    value_semantics hM ((env.push a).push r) 2 3 4 5 1 0
  obtain ⟨W,hW,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := L) (target := R) (by
      intro a ha
      obtain ⟨r,hr⟩ := value_total hWF hC hL hP ha
      exact ⟨r,(he a r).mpr hr⟩) (by
      intro a _ r s hr hs
      exact value_unique hWF hStable hEq ((he a r).mp hr) ((he a s).mp hs)) (by
      intro a r _ hr
      exact value_range hWF ((he a r).mp hr))
  refine ⟨W,(ForcingSupportSize.native_mapsTo hM L R W).mpr hW,fun a r => ?_⟩
  constructor
  · exact fun har => (he a r).mp ((hGraph a r).mp har).2
  · intro hv
    obtain ⟨i,x,Wi,hx,hWi,hxr,hpx⟩ := hv
    have hpL := (hL a).mpr (by
      obtain ⟨p,hcode,hpa⟩ := hpx
      exact ⟨p,(hC p).mpr ⟨i,x,hx,hcode⟩,(hP p a).mp hpa |>.2⟩)
    exact (hGraph a r).mpr ⟨hpL,(he a r).mpr ⟨i,x,Wi,hx,hWi,hxr,hpx⟩⟩

theorem projection_equation (hWF : WeightFamily J Domains R Weights)
    (hW : MapsTo L R W) (hGraph : Graph J Domains Weights projection W)
    {i D Wi x a r : M.Carrier .set} (hi : (Project.FirstOrderSemantics.reduct M).mem i J)
    (hD : PureKuratowski.PairMember M i D Domains) (hWi : PureKuratowski.PairMember M i Wi Weights)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D) (hpx : Product projection i x a) :
    PureKuratowski.PairMember M a r W ↔ PureKuratowski.PairMember M x r Wi := by
  constructor
  · intro har
    obtain ⟨r0,hxr0,_⟩ := (hWF.2 i D Wi hi hD hWi).1.2 x hx
    have h0 := (hGraph a r0).mpr ⟨i,x,Wi,⟨hi,D,hD,hx⟩,hWi,hxr0,hpx⟩
    exact (ForcingConditionGraphs.function_unique hW.1 h0 har) ▸ hxr0
  · exact fun hxr => (hGraph a r).mpr ⟨i,x,Wi,⟨hi,D,hD,hx⟩,hWi,hxr,hpx⟩

theorem height_bounds {top : M.Carrier .set}
    (hBounds : HeightBounds J Weights top) (hGraph : Graph J Domains Weights projection W) :
    ConstructionCutWeights.RangeBound top W := by
  intro a r har
  obtain ⟨i,x,Wi,hx,hWi,hxr,_⟩ := (hGraph a r).mp har
  exact hBounds i Wi hx.1 hWi x r hxr

theorem cost_bounds {top : M.Carrier .set}
    (hBounds : CostBounds J Weights top) (hGraph : Graph J Domains Weights projection W) :
    ConstructionProbeGateCap.Bounds top W := by
  intro a r har
  obtain ⟨i,x,Wi,hx,hWi,hxr,_⟩ := (hGraph a r).mp har
  exact hBounds i Wi hx.1 hWi x r hxr


def graph {m : Nat} (J Domains Weights projection W : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge W.succ.succ (1 : Fin (m+2)) (0 :
  Fin (m+2)))) (value J.succ.succ Domains.succ.succ Weights.succ.succ projection.succ.succ (1 : Fin (m+2))
  (0 : Fin (m+2))))))

theorem graph_freeClosed {m : Nat} (J Domains Weights projection W : Fin m) :
    (graph J Domains Weights projection W).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,value_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains Weights projection W : Fin m) :
    Project.Formula.satisfies env (graph J Domains Weights projection W) ↔ Graph (env.bound J) (env.bound Domains) (env.bound Weights) (env.bound projection) (env.bound W) := by
  simp only [graph,Graph,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,value_semantics hM]
  rfl

end PPAC.Migration.ConstructionDirectedWeights
