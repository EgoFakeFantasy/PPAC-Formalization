/- Pinned HeightCost.directed_cofinal_sequence, with the source's internal
1/(n+1) approximation and directed-upper recursion. The initial entry is
parameterized so ConeIdeal can prepend the unit without external Nat recursion.
All induction uses an actual Separation instance in the original ZF model. -/
import PPAC.Migration.ConstructionIdealApproximation
import PPAC.Migration.ExistingIndexedChoice

namespace PPAC.Migration.ConstructionIdealCofinal
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts
open ConstructionBaseMonoid (Divides)
open ConstructionProbeGates (divides_trans)
open ConstructionFractionOrder (NatLe)
open ConstructionIdealApproximation
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (function_input function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Directed (D mul U : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).MemberSubset U D ∧
    (∃ x, (Project.FirstOrderSemantics.reduct M).mem x U) ∧
    ∀ x y, (Project.FirstOrderSemantics.reduct M).mem x U →
      (Project.FirstOrderSemantics.reduct M).mem y U → ∃ z,
        (Project.FirstOrderSemantics.reduct M).mem z U ∧ Divides D mul x z ∧ Divides D mul y z

def MonotoneAt (D mul node j : M.Carrier .set) : Prop :=
  ∀ i x y, NatLe i j → PureKuratowski.PairMember M i x node →
    PureKuratowski.PairMember M j y node → Divides D mul x y


def monotoneAt {m : Nat} (D mul node j : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.imp (ConstructionBaseCostBound.natLeF (2 : Fin (m+3)) j.succ.succ.succ)
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge node.succ.succ.succ (2 : Fin (m+3)) (1 : Fin
  (m+3)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge node.succ.succ.succ j.succ.succ.succ (0 :
  Fin (m+3)))) (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ.succ mul.succ.succ.succ
  (1 : Fin (m+3)) (0 : Fin (m+3))))))))))

theorem monotoneAt_freeClosed {m : Nat} (D mul node j : Fin m) :
    (monotoneAt D mul node j).FreeClosed := by
  simp -implicitDefEqProofs [monotoneAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionBaseCostBound.natLeF_freeClosed]

theorem monotoneAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul node j : Fin m) :
    Project.Formula.satisfies env (monotoneAt D mul node j) ↔ MonotoneAt (env.bound D) (env.bound mul) (env.bound node) (env.bound j) := by
  simp only [monotoneAt,MonotoneAt,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionBaseCostBound.natLeF_semantics hM,ConstructionBaseMonoid.divides_semantics (M := M)]
  rfl


def Cofinal (w D mul U node : M.Carrier .set) : Prop := ∀ d,
  (Project.FirstOrderSemantics.reduct M).mem d U → ∃ i y,
    (Project.FirstOrderSemantics.reduct M).mem i w ∧
      PureKuratowski.PairMember M i y node ∧ Divides D mul d y

def Sequence (w D mul U zero a node : M.Carrier .set) : Prop :=
  MapsTo w U node ∧ PureKuratowski.PairMember M zero a node ∧
    (∀ j, (Project.FirstOrderSemantics.reduct M).mem j w → MonotoneAt D mul node j) ∧
    Cofinal w D mul U node

theorem directed_cofinal_sequence (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C U zero a : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hTop : Cut hM w Q top)
    (hObj : ConstructionRoundFields.ObjectFields hM w Q R top D mul e mark H C)
    (hU : Directed D mul U)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a U) :
    ∃ node, Sequence w D mul U zero a node := by
  classical
  obtain ⟨hm,hCon,_,_,_,hH,hBound,hC,hCost,hMargin,_,_⟩ := hObj
  obtain ⟨r,hr,hSup⟩ := supremum_exists hM hR hTop hH hBound
  have hRNonempty : ∃ q, (Project.FirstOrderSemantics.reduct M).mem q r := by
    obtain ⟨x,hx⟩ := hU.2.1
    obtain ⟨height,hxh,_⟩ := hH.1.2 x (hU.1 x hx)
    obtain ⟨q,hq⟩ := (hBound x height hxh).1
    exact ⟨q,(hSup q).mpr ⟨x,height,hx,hxh,hq⟩⟩
  let schema : Project.UnarySchema 8 := {
    body := .conj (ProjectSyntax.encode id
      (ConstructionBaseMonoid.divides (7 : Fin 9) (8 : Fin 9) (1 : Fin 9) (0 : Fin 9)))
      (approximates (3 : Fin 9) (4 : Fin 9) (5 : Fin 9) (6 : Fin 9) (2 : Fin 9) (0 : Fin 9))
    freeClosed := by simp [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,approximates_freeClosed] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 6 :=
    { bound := Fin.cases w (Fin.cases Q (Fin.cases H (Fin.cases r (Fin.cases D (fun _ => mul))))),
      free := fun _ => D }
  have hSchema i x y : schema.denote ((env.push i).push x) y ↔
      Divides D mul x y ∧ Approximates hM w Q H r i y := by
    simp only [schema,Project.UnarySchema.denote,Project.Formula.satisfies_conj_iff,
      GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
      ConstructionBaseMonoid.divides_semantics (M := M),approximates_semantics hM]
    rfl
  obtain ⟨node,hNative,hZero,hNext⟩ := ExistingIndexedChoice.indexed_choice_l
    (KuratowskiZF.interpretation hM) (ConstructionDirectedCardinality.models_zfc hM hChoice)
    schema env hw ha (by
      intro i x hi hx
      obtain ⟨u,hu,hApprox⟩ := approximate hM hw hQ hR hH hr hSup hRNonempty hi
      obtain ⟨y,hy,hxy,huy⟩ := hU.2.2 x u hx hu
      exact ⟨y,hy,(hSchema i x y).mpr ⟨hxy,approximate_mono hM hw hQ hR hm hCon hH hMargin
        (hU.1 y hy) huy hApprox⟩⟩)
  have hNode := (ForcingSupportSize.native_mapsTo hM w U node).mpr hNative
  have hNext' i j x y (hij : (Project.FirstOrderSemantics.reduct M).SuccessorOf j i)
      (hix : PureKuratowski.PairMember M i x node) (hjy : PureKuratowski.PairMember M j y node) :
      Divides D mul x y ∧ Approximates hM w Q H r i y :=
    (hSchema i x y).mp (hNext i j x y hij hix hjy)
  have hSelf x (hx : (Project.FirstOrderSemantics.reduct M).mem x D) : Divides D mul x x :=
    ⟨e,hm.1.1,(hm.1.2 x hx x).2.mpr rfl⟩
  have hMono : ∀ j, (Project.FirstOrderSemantics.reduct M).mem j w → MonotoneAt D mul node j := by
    apply hw.induction (fun j => MonotoneAt D mul node j)
    · let φ : Project.UnarySchema 3 := {
        body := monotoneAt (3 : Fin 4) (2 : Fin 4) (1 : Fin 4) (0 : Fin 4)
        freeClosed := monotoneAt_freeClosed _ _ _ _ }
      let ρ : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 :=
        { bound := Fin.cases node (Fin.cases mul (fun _ => D)), free := fun _ => D }
      obtain ⟨S,hS⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) φ ρ w
      exact ⟨S,fun j => (hS j).trans (and_congr_right (fun _ => monotoneAt_semantics hM (ρ.push j) 3 2 1 0))⟩
    · intro z hz i x y hij hix hzy
      rcases hij with rfl | hmem
      · have he := function_unique hNode.1 hix hzy
        subst y
        exact hSelf x (hU.1 x (hNode.2 i x hix))
      · exact False.elim (hz i hmem)
    · intro i hi ih j hij k x y hkj hkx hjy
      rcases hkj with rfl | hmem
      · have he := function_unique hNode.1 hkx hjy
        subst y
        exact hSelf x (hU.1 x (hNode.2 k x hkx))
      · have hki : NatLe k i := ((hij k).mp hmem).elim Or.inr
          (fun he => Or.inl ((ModelTransfer.extensionality hM).eq_of_same_members k i he))
        obtain ⟨prev,hip,_⟩ := hNode.1.2 i hi
        exact divides_trans hm (hU.1 x (hNode.2 k x hkx))
          (ih k x prev hki hkx hip) (hNext' i j prev y hij hip hjy).1
  refine ⟨node,hNode,hZero zero hz,hMono,?_⟩
  intro d hd
  obtain ⟨cost,hdc,_⟩ := hC.1.2 d (hU.1 d hd)
  have hCostCut := (hR cost).mp (hC.2 d cost hdc)
  obtain ⟨i,n,one,step,eps,hi,hni,hone,hstep,hEps,hEpsCost⟩ :=
    small_cost_step hM hw hQ hCostCut (hCost d cost hdc).1
  obtain ⟨j,hji,hjw⟩ := hw.1.2 i hi
  obtain ⟨x,hix,_⟩ := hNode.1.2 i hi
  obtain ⟨y,hjy,_⟩ := hNode.1.2 j hjw
  refine ⟨j,y,hjw,hjy,?_⟩
  apply Classical.byContradiction
  intro hnot
  have hApprox := (hNext' i j x y hji hix hjy).2
  obtain ⟨nA,oneA,stepA,epsA,hy,total,hSucA,hOneA,hStepA,hEpsA,hyH,hTotal,hApproxBound⟩ := hApprox
  have en := Structure.SuccessorOf.eq (ModelTransfer.extensionality hM) hSucA hni
  subst nA
  have eo := Structure.IsOrdinalOne.eq (ModelTransfer.extensionality hM) hOneA hone
  subst oneA
  have es := KuratowskiZF.code_unique hM hStepA.2.2.2 hstep.2.2.2
  subst stepA
  have ee := principal_unique hM hEpsA hEps
  subst epsA
  obtain ⟨z,hzU,hyz,hdz⟩ := hU.2.2 y d (hNode.2 j y hjy) hd
  obtain ⟨hz,hzH,_⟩ := hH.1.2 z (hU.1 z hzU)
  have hnotBack : ¬ Divides D mul z y :=
    fun h => hnot (divides_trans hm (hU.1 d hd) hdz h)
  obtain ⟨cap,out,_,hOut,hStrict,hMissed⟩ := hMargin y z hy hz hyH hzH hyz hnotBack
  have hEpsCap : Subset eps cap := fun p hp => hMissed d cost (hU.1 d hd) hdc hdz hnot p (hEpsCost p hp)
  have hMonoSum := ConstructionCutArithmetic.sum_mono hTotal hOut (fun _ h => h) hEpsCap
  exact hStrict.2 (fun q hq => hMonoSum q (hApproxBound q ((hSup q).mpr ⟨z,hz,hzU,hzH,hq⟩)))
end PPAC.Migration.ConstructionIdealCofinal
