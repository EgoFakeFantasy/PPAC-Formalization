/- Pinned DiagramOrder.ConeIdeal.countable_cofinal_sequence:169 and
SaturatedMonoids.Saturation.ideal_probes:153. Arbitrary internal ideals,
all internal omega indices and ALL final divisors/elements are retained.
The SAME final Probe family is used; no rescheduling or new monoid backend. -/
import PPAC.Migration.ConstructionIdealCofinal

namespace PPAC.Migration.ConstructionIdealProbes
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionRealCuts
open ConstructionBaseMonoid (Divides)
open ConstructionProbeCones (JoinProperty)
open ForcingDiagramOrder (Product)
open ForcingSupportSize (MapsTo Injection)
open ConstructionTowerHistory (Row)
open ConstructionIdealCofinal (Directed Sequence Cofinal)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def ConeIdeal (D mul a U : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).MemberSubset U D ∧
  (Project.FirstOrderSemantics.reduct M).mem a D ∧
  (∃ x, (Project.FirstOrderSemantics.reduct M).mem x U) ∧
  (∀ x, (Project.FirstOrderSemantics.reduct M).mem x U → Divides D mul x a) ∧
  (∀ x y, (Project.FirstOrderSemantics.reduct M).mem x D →
    (Project.FirstOrderSemantics.reduct M).mem y U → Divides D mul x y →
      (Project.FirstOrderSemantics.reduct M).mem x U) ∧
  (∀ x y j, (Project.FirstOrderSemantics.reduct M).mem x U →
    (Project.FirstOrderSemantics.reduct M).mem y U →
    (Project.FirstOrderSemantics.reduct M).mem j D → JoinProperty D mul x y j →
      (Project.FirstOrderSemantics.reduct M).mem j U)

theorem directed {D mul e a U : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hU : ConeIdeal D mul a U) : Directed D mul U := by
  refine ⟨hU.1,hU.2.2.1,?_⟩
  intro x y hx hy
  obtain ⟨j,hj,hJoin⟩ := hJ x y a (hU.1 x hx) (hU.1 y hy) hU.2.1
    (hU.2.2.2.1 x hx) (hU.2.2.2.1 y hy)
  have hSelf : Divides D mul j j := ⟨e,hm.1.1,(hm.1.2 j hj j).2.mpr rfl⟩
  exact ⟨j,hU.2.2.2.2.2 x y j hx hy hj hJoin,(hJoin j hj).mpr hSelf⟩

def IdealPath (w D mul e zero a U node : M.Carrier .set) : Prop :=
  ConstructionProbePath.Path w D mul e zero a node ∧ MapsTo w U node ∧ Cofinal w D mul U node

theorem countable_cofinal_sequence (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C U zero a : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hTop : Cut hM w Q top)
    (hObj : ConstructionRoundFields.ObjectFields hM w Q R top D mul e mark H C)
    (hU : ConeIdeal D mul a U)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero) :
    ∃ node, IdealPath w D mul e zero a U node := by
  obtain ⟨x,hx⟩ := hU.2.2.1
  have heU := hU.2.2.2.2.1 e x hObj.1.1.1 hx
    ⟨x,hU.1 x hx,(hObj.1.1.2 x (hU.1 x hx) x).1.mpr rfl⟩
  obtain ⟨node,hNode,hZero,hMono,hCof⟩ := ConstructionIdealCofinal.directed_cofinal_sequence
    hM hChoice hw hQ hR hTop hObj (directed hObj.1 hObj.2.2.1 hU) hz heU
  have hToD : MapsTo w D node := ⟨hNode.1,fun i x hix => hU.1 x (hNode.2 i x hix)⟩
  refine ⟨node,⟨hToD,hU.2.1,hZero,?_,?_⟩,hNode,hCof⟩
  · intro i j hi hj hij
    obtain ⟨ni,hni,_⟩ := hNode.1.2 i hi
    obtain ⟨nj,hnj,_⟩ := hNode.1.2 j hj
    obtain ⟨f,hf,hprod⟩ := hMono j hj i ni nj hij hni hnj
    exact ⟨f,ni,nj,hni,hnj,hf,hprod⟩
  · intro i hi
    obtain ⟨ni,hni,_⟩ := hNode.1.2 i hi
    obtain ⟨t,ht,hprod⟩ := hU.2.2.2.1 ni (hNode.2 i ni hni)
    exact ⟨t,ni,hni,ht,hprod⟩

def IdealProbes (K D mul mark a b U : M.Carrier .set) : Prop :=
  ∃ Family, Injection K D Family ∧
    (∀ k p, PureKuratowski.PairMember M k p Family → ∃ exit,
      (Project.FirstOrderSemantics.reduct M).mem exit D ∧ Product mul a mark exit ∧
      Product mul p b exit ∧ ¬ Divides D mul p a ∧
      (∀ x, (Project.FirstOrderSemantics.reduct M).mem x D →
        ((Divides D mul x a ∧ Divides D mul x p) ↔ (Project.FirstOrderSemantics.reduct M).mem x U)) ∧
      (∀ x, (Project.FirstOrderSemantics.reduct M).mem x D → Divides D mul x a →
        ¬ (Project.FirstOrderSemantics.reduct M).mem x U → JoinProperty D mul x p exit)) ∧
    (∀ k l p q, PureKuratowski.PairMember M k p Family → PureKuratowski.PairMember M l q Family →
      k ≠ l → ∃ exit, Product mul a mark exit ∧ JoinProperty D mul p q exit)

theorem ideal_probes (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top K D mul e mark H C U zero a b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : CutCarrier hM w Q R) (hTop : Cut hM w Q top)
    (hObj : ConstructionRoundFields.ObjectFields hM w Q R top D mul e mark H C)
    (hU : ConeIdeal D mul a U)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hProbes : ∀ node, ConstructionProbePath.Path w D mul e zero a node →
      ConstructionSaturationProbes.Probes w K D mul mark a b node) :
    IdealProbes K D mul mark a b U := by
  obtain ⟨node,hPath,hNode,hCof⟩ := countable_cofinal_sequence hM hChoice hw hQ hR hTop hObj hU hz
  obtain ⟨Family,hInjection,hProfiles,hIndependent⟩ := hProbes node hPath
  refine ⟨Family,hInjection,?_,hIndependent⟩
  intro k p hkp
  obtain ⟨_,_,_,_,_,exit,hExitD,hExit,hProduct,hNot,hDiv,hJoin⟩ := hProfiles k p hkp
  have hProfile x (hx : (Project.FirstOrderSemantics.reduct M).mem x D) :
      (Divides D mul x a ∧ Divides D mul x p) ↔ (Project.FirstOrderSemantics.reduct M).mem x U := by
    constructor
    · intro h
      obtain ⟨i,n,_,hin,hxn⟩ := (hDiv x hx).mp h
      exact hU.2.2.2.2.1 x n hx (hNode.2 i n hin) hxn
    · intro hxU
      exact (hDiv x hx).mpr (hCof x hxU)
  exact ⟨exit,hExitD,hExit,hProduct,hNot,hProfile,fun x hx hxa hxU =>
    hJoin x hx hxa (fun hxp => hxU ((hProfile x hx).mp ⟨hxa,hxp⟩))⟩

def AllIdeals (K history kappa : M.Carrier .set) : Prop :=
  ∀ N mul e mark H C incoming base a b U,
    Row history kappa N mul e mark H C incoming base kappa →
    (Project.FirstOrderSemantics.reduct M).mem b N → b ≠ e →
    ConeIdeal N mul a U → IdealProbes K N mul mark a b U

def AllHistoriesIdeals (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one K mu kappa B : M.Carrier .set) : Prop :=
  ∀ history P F,
    ConstructionSaturationIteration.Recursive hM w Q R top D mul e mark H C zero one K mu B B history →
    ConstructionTowerTransitions.Matrix B history zero P F → AllIdeals K history kappa

def IdealTower (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one u K mu kappa B : M.Carrier .set) : Prop :=
  ConstructionSaturationCardinals.CardinalTower hM w Q R top D mul e mark H C zero one u K mu kappa B ∧
    AllHistoriesIdeals hM w Q R top D mul e mark H C zero one K mu kappa B

theorem tower_ideals (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C zero one u K mu kappa B : M.Carrier .set}
    (hTower : ConstructionSaturationCardinals.CardinalTower hM w Q R top D mul e mark H C zero one u K mu kappa B) :
    IdealTower hM w Q R top D mul e mark H C zero one u K mu kappa B := by
  refine ⟨hTower,?_⟩
  intro history P F hRec hF N m v a W V incoming base a' b U hRow hb hne hU
  have hProbe := hTower.1.1.1
  have hCtx := hProbe.1.1.2.1
  have hData := hProbe.1.1.1
  have hCtxCopy := hCtx
  obtain ⟨hw,hQ,hR,hCoordinates,_,hPrincipal,_,hz,_,_,_,_,_,_,_,_⟩ := hCtxCopy
  have hTop := principal_cut hM hw hQ ((hQ u).mpr ⟨one,one,hCoordinates⟩) hPrincipal
  have hV := (ConstructionSaturationIterationValidity.recursive_valid_small hM hOrder hChoice
    hCtx hRec (fun _ h => h)).1
  have hObj := (hV.2.1 kappa hData.2.2.2.1.predecessor_mem
    N m v a W V incoming base hRow).1
  exact ideal_probes hM hChoice hw hQ hR hTop hObj hU hz
    (fun node hPath => hProbe.2 history P F hRec hF N m v a W V incoming base a' b node hRow hb hne hPath)
theorem exists_ideal_tower (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C zero one u K mu : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hCoordinates : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hTop : ConstructionRealCuts.Principal hM w Q u top)
    (hObj : ConstructionRoundFields.ObjectFields hM w Q R top D mul e mark H C)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hK : ∃ k, (Project.FirstOrderSemantics.reduct M).mem k K)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hpow : (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation (KuratowskiZF.interpretation hM) mu mu w)
    (hD : ForcingSupportSize.Small D mu) (hKSmall : ForcingSupportSize.Small K mu) (hOmegaOne : ConstructionSaturationIndex.OmegaOneLe hM w mu) :
    ∃ kappa B, IdealTower hM w Q R top D mul e mark H C zero one u K mu kappa B := by
  obtain ⟨kappa,B,hTower⟩ := ConstructionSaturationCardinals.exists_cardinal_tower hM hOrder hChoice
    hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall hOmegaOne
  exact ⟨kappa,B,tower_ideals hM hOrder hChoice hTower⟩


def coneIdeal {m : Nat} (D mul a U : Fin m) : Project.Formula 1 m :=
  (.conj (Project.Formula.subset (.bound U) (.bound D)) (.conj (.mem (.bound a) (.bound D)) (.conj (.existsE
  (.mem (.bound (0 : Fin (m+1))) (.bound U.succ))) (.conj (.forallE (.imp (.mem (.bound (0 : Fin (m+1)))
  (.bound U.succ)) (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ mul.succ (0 : Fin (m+1))
  a.succ)))) (.conj (.forallE (.forallE (.imp (.mem (.bound (1 : Fin (m+2))) (.bound D.succ.succ)) (.imp
  (.mem (.bound (0 : Fin (m+2))) (.bound U.succ.succ)) (.imp (ProjectSyntax.encode id
  (ConstructionBaseMonoid.divides D.succ.succ mul.succ.succ (1 : Fin (m+2)) (0 : Fin (m+2)))) (.mem (.bound
  (1 : Fin (m+2))) (.bound U.succ.succ))))))) (.forallE (.forallE (.forallE (.imp (.mem (.bound (2 : Fin
  (m+3))) (.bound U.succ.succ.succ)) (.imp (.mem (.bound (1 : Fin (m+3))) (.bound U.succ.succ.succ)) (.imp
  (.mem (.bound (0 : Fin (m+3))) (.bound D.succ.succ.succ)) (.imp (ConstructionProbeCones.joinProperty
  D.succ.succ.succ mul.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3)) (0 : Fin (m+3))) (.mem (.bound (0 :
  Fin (m+3))) (.bound U.succ.succ.succ))))))))))))))

theorem coneIdeal_freeClosed {m : Nat} (D mul a U : Fin m) :
    (coneIdeal D mul a U).FreeClosed := by
  simp -implicitDefEqProofs [coneIdeal,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeCones.joinProperty_freeClosed]

theorem coneIdeal_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul a U : Fin m) :
    Project.Formula.satisfies env (coneIdeal D mul a U) ↔ ConeIdeal (env.bound D) (env.bound mul) (env.bound a) (env.bound U) := by
  simp only [coneIdeal,ConeIdeal,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Project.Formula.satisfies_subset_iff,ConstructionBaseMonoid.divides_semantics (M := M),ConstructionProbeCones.joinProperty_semantics hM]
  rfl


def idealProbesF {m : Nat} (K D mul mark a b U : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection (0 : Fin (m+1)) K.succ D.succ))
  (.conj (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin
  (m+1)).succ.succ (1 : Fin (m+3)) (0 : Fin (m+3)))) (.existsE (.conj (.mem (.bound (0 : Fin (m+4))) (.bound
  D.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product
  mul.succ.succ.succ.succ a.succ.succ.succ.succ mark.succ.succ.succ.succ (0 : Fin (m+4)))) (.conj
  (ProjectSyntax.encode id (ForcingDiagramOrder.product mul.succ.succ.succ.succ (1 : Fin (m+4))
  b.succ.succ.succ.succ (0 : Fin (m+4)))) (.conj (.neg (ProjectSyntax.encode id
  (ConstructionBaseMonoid.divides D.succ.succ.succ.succ mul.succ.succ.succ.succ (1 : Fin (m+4))
  a.succ.succ.succ.succ))) (.conj (.forallE (.imp (.mem (.bound (0 : Fin (m+5))) (.bound
  D.succ.succ.succ.succ.succ)) (.iff (.conj (ProjectSyntax.encode id (ConstructionBaseMonoid.divides
  D.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ (0 : Fin (m+5)) a.succ.succ.succ.succ.succ))
  (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ (0 : Fin (m+5)) (2 : Fin (m+5))))) (.mem (.bound (0 : Fin (m+5))) (.bound
  U.succ.succ.succ.succ.succ))))) (.forallE (.imp (.mem (.bound (0 : Fin (m+5))) (.bound
  D.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (ConstructionBaseMonoid.divides
  D.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ (0 : Fin (m+5)) a.succ.succ.succ.succ.succ)) (.imp
  (.neg (.mem (.bound (0 : Fin (m+5))) (.bound U.succ.succ.succ.succ.succ)))
  (ConstructionProbeCones.joinProperty D.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ (0 : Fin
  (m+5)) (2 : Fin (m+5)) (1 : Fin (m+5)))))))))))))))) (.forallE (.forallE (.forallE (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin (m+1)).succ.succ.succ.succ (3 : Fin (m+5)) (1 :
  Fin (m+5)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin (m+1)).succ.succ.succ.succ
  (2 : Fin (m+5)) (0 : Fin (m+5)))) (.imp (.neg (Project.Formula.extensionalEq (.bound (3 : Fin (m+5)))
  (.bound (2 : Fin (m+5))))) (.existsE (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product
  mul.succ.succ.succ.succ.succ.succ a.succ.succ.succ.succ.succ.succ mark.succ.succ.succ.succ.succ.succ (0 :
  Fin (m+6)))) (ConstructionProbeCones.joinProperty D.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ (2 : Fin (m+6)) (1 : Fin (m+6)) (0 : Fin (m+6)))))))))))))))

theorem idealProbesF_freeClosed {m : Nat} (K D mul mark a b U : Fin m) :
    (idealProbesF K D mul mark a b U).FreeClosed := by
  simp -implicitDefEqProofs [idealProbesF,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq,ConstructionProbeCones.joinProperty_freeClosed]

theorem idealProbesF_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (K D mul mark a b U : Fin m) :
    Project.Formula.satisfies env (idealProbesF K D mul mark a b U) ↔ IdealProbes (env.bound K) (env.bound D) (env.bound mul) (env.bound mark) (env.bound a) (env.bound b) (env.bound U) := by
  simp only [idealProbesF,IdealProbes,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.product_semantics (M := M),ConstructionBaseMonoid.divides_semantics (M := M),ConstructionProbeCones.joinProperty_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl


def allIdeals {m : Nat} (K history kappa : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE
  (.forallE (.imp (ConstructionTowerHistory.row
  history.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (10 : Fin (m+11)) (9 : Fin (m+11)) (8 : Fin
  (m+11)) (7 : Fin (m+11)) (6 : Fin (m+11)) (5 : Fin (m+11)) (4 : Fin (m+11)) (3 : Fin (m+11))
  kappa.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.imp (.mem (.bound (1 : Fin (m+11)))
  (.bound (10 : Fin (m+11)))) (.imp (.neg (Project.Formula.extensionalEq (.bound (1 : Fin (m+11))) (.bound
  (8 : Fin (m+11))))) (.imp (coneIdeal (10 : Fin (m+11)) (9 : Fin (m+11)) (2 : Fin (m+11)) (0 : Fin (m+11)))
  (idealProbesF K.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (10 : Fin (m+11)) (9 : Fin (m+11))
  (7 : Fin (m+11)) (2 : Fin (m+11)) (1 : Fin (m+11)) (0 : Fin (m+11))))))))))))))))))

theorem allIdeals_freeClosed {m : Nat} (K history kappa : Fin m) :
    (allIdeals K history kappa).FreeClosed := by
  simp -implicitDefEqProofs [allIdeals,Definitional.Formula.FreeClosed,ConstructionTowerHistory.row_freeClosed,Project.Formula.extensionalEq,coneIdeal_freeClosed,idealProbesF_freeClosed]

theorem allIdeals_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (K history kappa : Fin m) :
    Project.Formula.satisfies env (allIdeals K history kappa) ↔ AllIdeals (env.bound K) (env.bound history) (env.bound kappa) := by
  simp only [allIdeals,AllIdeals,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionTowerHistory.row_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),coneIdeal_semantics hM,idealProbesF_semantics hM]
  rfl

def allHistoriesIdeals {m : Nat} (w Q R top D mul e mark H C zero one K mu kappa B : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.imp (ConstructionSaturationIteration.recursive w.succ.succ.succ
  Q.succ.succ.succ R.succ.succ.succ top.succ.succ.succ D.succ.succ.succ mul.succ.succ.succ e.succ.succ.succ
  mark.succ.succ.succ H.succ.succ.succ C.succ.succ.succ zero.succ.succ.succ one.succ.succ.succ
  K.succ.succ.succ mu.succ.succ.succ B.succ.succ.succ B.succ.succ.succ (2 : Fin (m+3))) (.imp
  (ConstructionTowerTransitions.matrix B.succ.succ.succ (2 : Fin (m+3)) zero.succ.succ.succ (1 : Fin (m+3))
  (0 : Fin (m+3))) (allIdeals K.succ.succ.succ (2 : Fin (m+3)) kappa.succ.succ.succ))))))

theorem allHistoriesIdeals_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one K mu kappa B : Fin m) :
    (allHistoriesIdeals w Q R top D mul e mark H C zero one K mu kappa B).FreeClosed := by
  simp -implicitDefEqProofs [allHistoriesIdeals,Definitional.Formula.FreeClosed,ConstructionSaturationIteration.recursive_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,allIdeals_freeClosed]

theorem allHistoriesIdeals_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one K mu kappa B : Fin m) :
    Project.Formula.satisfies env (allHistoriesIdeals w Q R top D mul e mark H C zero one K mu kappa B) ↔ AllHistoriesIdeals hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound K) (env.bound mu) (env.bound kappa) (env.bound B) := by
  simp only [allHistoriesIdeals,AllHistoriesIdeals,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    
    ConstructionSaturationIteration.recursive_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,allIdeals_semantics hM]
  rfl


def idealTower {m : Nat} (w Q R top D mul e mark H C zero one u K mu kappa B : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionSaturationCardinals.cardinalTower w Q R top D mul e mark H C zero one u K mu kappa B)
  (allHistoriesIdeals w Q R top D mul e mark H C zero one K mu kappa B))

theorem idealTower_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one u K mu kappa B : Fin m) :
    (idealTower w Q R top D mul e mark H C zero one u K mu kappa B).FreeClosed := by
  simp -implicitDefEqProofs [idealTower,Definitional.Formula.FreeClosed,ConstructionSaturationCardinals.cardinalTower_freeClosed,allHistoriesIdeals_freeClosed]

theorem idealTower_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one u K mu kappa B : Fin m) :
    Project.Formula.satisfies env (idealTower w Q R top D mul e mark H C zero one u K mu kappa B) ↔ IdealTower hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound u) (env.bound K) (env.bound mu) (env.bound kappa) (env.bound B) := by
  simp only [idealTower,IdealTower,
    Project.Formula.satisfies_conj_iff,
    
    ConstructionSaturationCardinals.cardinalTower_semantics hM,allHistoriesIdeals_semantics hM]

def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 15 (.imp (Project.Formula.isOmega (.bound (0 : Fin 15))) (.imp
    (ConstructionFractionOrder.carrier (0 : Fin 15) (1 : Fin 15)) (.imp (ConstructionRealCuts.cutCarrier (0
    : Fin 15) (1 : Fin 15) (2 : Fin 15)) (.imp (ConstructionFractionOrder.coordinates (0 : Fin 15) (12 : Fin
    15) (11 : Fin 15) (11 : Fin 15)) (.imp (Project.Formula.isOrdinalOne (.bound (11 : Fin 15))) (.imp
    (ConstructionRealCuts.principal (0 : Fin 15) (1 : Fin 15) (12 : Fin 15) (3 : Fin 15)) (.imp
    (ConstructionRoundStepSyntax.objectFields (0 : Fin 15) (1 : Fin 15) (2 : Fin 15) (3 : Fin 15) (4 : Fin
    15) (5 : Fin 15) (6 : Fin 15) (7 : Fin 15) (8 : Fin 15) (9 : Fin 15)) (.imp (Project.Formula.isEmpty
    (.bound (10 : Fin 15))) (.imp (.mem (.bound (10 : Fin 15)) (.bound (0 : Fin 15))) (.imp (.existsE (.mem
    (.bound (0 : Fin 16)) (.bound (13 : Fin 15).succ))) (.imp (Project.Formula.isInfiniteCardinal
    PureKuratowskiProject.convention (.bound (0 : Fin 15)) (.bound (14 : Fin 15))) (.imp
    (Project.Formula.isCardinalExponentiation PureKuratowskiProject.convention (.bound (14 : Fin 15))
    (.bound (14 : Fin 15)) (.bound (0 : Fin 15))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small
    (4 : Fin 15) (14 : Fin 15))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (13 : Fin 15) (14
    : Fin 15))) (.imp (ConstructionSaturationIndex.omegaOneLe (0 : Fin 15) (14 : Fin 15)) (.existsE (.existsE (idealTower (0 : Fin
    15).succ.succ (1 : Fin 15).succ.succ (2 : Fin 15).succ.succ (3 : Fin 15).succ.succ (4 : Fin
    15).succ.succ (5 : Fin 15).succ.succ (6 : Fin 15).succ.succ (7 : Fin 15).succ.succ (8 : Fin
    15).succ.succ (9 : Fin 15).succ.succ (10 : Fin 15).succ.succ (11 : Fin 15).succ.succ (12 : Fin
    15).succ.succ (13 : Fin 15).succ.succ (14 : Fin 15).succ.succ (1 : Fin 17) (0 : Fin
    17))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,ConstructionFractionOrder.carrier_freeClosed,
      ConstructionRealCuts.cutCarrier_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,
      Project.Formula.isOrdinalOne,ConstructionRealCuts.principal_freeClosed,
      ConstructionRoundStepSyntax.objectFields_freeClosed,Project.Formula.isEmpty,
      Project.Formula.isInfiniteCardinal,Project.Formula.isCardinalExponentiation,Project.Formula.isFunctionSpace,
      ConstructionSaturationIndex.omegaOneLe_freeClosed,idealTower_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isOrdinalOne_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isCardinalExponentiation_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    ConstructionFractionOrder.coordinates_semantics hM,ConstructionRealCuts.principal_semantics hM,
    ConstructionRoundStepSyntax.objectFields_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationIndex.omegaOneLe_semantics hM,idealTower_semantics hM]
  exact fun hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall hOmegaOne =>
    exists_ideal_tower hM hOrder hChoice hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall hOmegaOne

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




end PPAC.Migration.ConstructionIdealProbes
