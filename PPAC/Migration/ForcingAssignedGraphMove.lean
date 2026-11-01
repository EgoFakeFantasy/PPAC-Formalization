/- Fixed AssignedGraphs.graphWitness_move:78 and graphRelation_move:90.
Consumer: assignmentGraph:100. Move the actual Cohen condition, vertex, label
and local name together; retain the same sixteen orbit parameter functions.
The bound-support premise is supplied by the existing literal label-bound
construction (ForcingLocalNameTransport.bound_supported), not a new law. -/
import PPAC.Migration.ForcingAssignedGraph
import PPAC.Migration.ForcingAssignedTransport
import PPAC.Migration.ForcingLocalNameTransport

namespace PPAC.Migration.ForcingAssignedGraphMove
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingAssignedGraph (Witness Holds witness holds)
open ForcingConditionGraphs (Permutation CompositionGraph)
open ForcingProductCovariance (SystemData)
open ForcingProductSymmetry (orderFormula)
open ForcingMapConditions (MapRel)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 500000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private theorem assigned_move_values (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E w top K B zero Q s sAct : Fin k) (families : Fin 16 → Fin k)
    {ac d e vertex movedVertex label movedLabel tau movedTau : M.Carrier .set}
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hs : Permutation (env I) (env s))
    (hsFix : CompositionGraph (env (rho 0)) (env s) (env q) (env q))
    (hsAct : ForcingProductFamily.Action (env (rho 0)) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)) (env s) (env sAct))
    (hsCohen : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) (env s) ac)
    (hsD : PureKuratowski.PairMember M d e ac)
    (hsVertex : ForcingComponentMove.Move (env (rho 0)) (env I) (env mul) (env q) (env s) vertex movedVertex)
    (hsLabel : PureKuratowski.PairMember M label movedLabel (env s))
    (hsTau : ForcingStabilizer.Action (env (rho 6)) (env sAct) tau movedTau)
    (h : ForcingAssigned.Assigned hM env rho I G F mul q bound labels E w top K B zero Q families d vertex label tau) :
    ForcingAssigned.Assigned hM env rho I G F mul q bound labels E w top K B zero Q families e movedVertex movedLabel movedTau := by
  let other : Fin (k+9) → M.Carrier .set := Fin.cases movedTau (Fin.cases tau (Fin.cases movedLabel (Fin.cases label (Fin.cases movedVertex (Fin.cases vertex (Fin.cases e (Fin.cases d (Fin.cases ac env))))))))
  let up : Fin k → Fin (k+9) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ
  have he (i : Fin k) : other (up i) = env i := rfl
  have hi := (ForcingAssigned.assigned_reindex hM env other up he rho I G F mul q bound labels E w top K B zero Q families d vertex label tau).mpr h
  have ho := ForcingAssignedTransport.assigned_permute hM other (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up w) (up top) (up K) (up B) (up zero) (up Q) (up s) (up sAct) 8 7 6 5 4 3 2 1 0 (fun j => up (families j)) hp hq hs hsFix hsAct hsCohen hsD hsVertex hsLabel hsTau hi
  exact (ForcingAssigned.assigned_reindex hM env other up he rho I G F mul q bound labels E w top K B zero Q families e movedVertex movedLabel movedTau).mp ho

private theorem entry_move (hM : FirstOrder.Theory.Models M nativeZF)
    {v : Fin 7 → M.Carrier .set} {I K B w G F mu pi inv c a ai bound mul q vertex movedVertex tau movedTau : M.Carrier .set}
    (hData : SystemData v I K B w G F mu pi inv c a ai)
    (hBound : ForcingSupportedNames.Supported v G bound)
    (hMove : ForcingComponentMove.Move (v 0) I mul q pi vertex movedVertex)
    (hEntry : ForcingTailCodes.Entry v G F bound vertex tau)
    (hTau : ForcingStabilizer.Action (v 6) a tau movedTau) :
    ForcingTailCodes.Entry v G F bound movedVertex movedTau := by
  obtain ⟨r,index,U,R,hCode,hMoved,hVertex,_,hComp⟩ := hMove
  obtain ⟨r0,index0,U0,J,H,hCode0,hRange,hFixing,hLocal⟩ := hEntry
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hCode0 hCode
  obtain ⟨JT,hImage,_⟩ := ForcingLabelConjugacy.exists_image hM (J := J) hData.2.2.1.1
  obtain ⟨HT,hHT⟩ := ForcingLabelPermutations.exists_fixing hM G JT
  exact ⟨R,index0,U0,JT,HT,hMoved,ForcingLocalNameTransport.range_image hRange hComp hImage,hHT,
    ForcingLocalNameTransport.local_name_move hM hData hBound (ForcingTailGroup.range_subset hVertex.1 hRange) hImage hFixing hHT hLocal hTau⟩

theorem witness_move (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E w top K B zero Q labelMap bit mu pi inv c a ai : Fin k) (families : Fin 16 → Fin k)
    {p p' x x' y y' : M.Carrier .set}
    (hData : SystemData (fun j => env (rho j)) (env I) (env K) (env B) (env w) (env G) (env F) (env mu) (env pi) (env inv) (env c) (env a) (env ai))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hFix : CompositionGraph (env (rho 0)) (env pi) (env q) (env q))
    (hBound : ForcingSupportedNames.Supported (fun j => env (rho j)) (env G) (env bound))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hpp : PureKuratowski.PairMember M p p' (env a))
    (hxx : ForcingStabilizer.Action (env (rho 6)) (env a) x x')
    (hyy : ForcingStabilizer.Action (env (rho 6)) (env a) y y')
    (h : Witness hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y) :
    Witness hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p' x' y' := by
  have hp := hData.1
  have hpi := hData.2.2.1
  have hA := hData.2.2.2.2.2.2.2.1
  have ha := ForcingProductFamily.action_permutation hA
  have hpW := ForcingAssignedGraph.witness_condition hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families h
  obtain ⟨d,vertex,j,tau,r,index,U,z,labelName,hd,hCode,hVertex,hj,hEntry,hz,hpz,hAssigned,hLabel,hx,hy⟩ := h
  obtain ⟨ac,hCohen⟩ := ForcingLocalTransport.part_of_action hA
  have hac := ForcingLocalTransport.part_permutation hCohen
  obtain ⟨d',hdd,_⟩ := hac.1.1.2 d hd
  obtain ⟨R,hR,hComp⟩ := ForcingDiagramAction.exists_permute hM hpi hVertex.1
  obtain ⟨vertex',hCode'⟩ := ConstructionComponentCarrier.code_total hM R index U
  have hVertex' : ConstructionComponentVertices.Vertex (env (rho 0)) (env I) (env mul) (env q) R index U :=
    ⟨hR,ForcingDiagramOrder.permute_sub hComp hFix hVertex.2.1,hVertex.2.2⟩
  have hMove : ForcingComponentMove.Move (env (rho 0)) (env I) (env mul) (env q) (env pi) vertex vertex' :=
    ⟨r,index,U,R,hCode,hCode',hVertex,hVertex',hComp⟩
  obtain ⟨j',hjj,_⟩ := hpi.1.1.2 j hj
  obtain ⟨tau',hTau⟩ := ForcingNameConjugacy.exists_action hM ha.1 tau
  obtain ⟨z',hz'⟩ := ForcingSupportingRoot.exists_code hM d' R
  have hzz := ForcingLocalTransport.moved_code hM hp hA hCohen hdd hVertex.1 hR hComp hz hz'
  obtain ⟨labelName',hLabel'⟩ := ForcingLabelNames.exists_label hM hLabelMap (env (rho 6)) (env top) j' (env bit)
  have hLabelMove := ForcingLabelNames.label_move hM (fun j => env (rho j)) hp hTop hpi hA hjj hLabel hLabel'
  have hOrder := ForcingProductFamily.order hM (env mul) hp hpi hA
  have hMoveOrder : MapRel (orderFormula (rho 0) mul) env p' z' := by
    rw [ForcingProductSymmetry.orderFormula_semantics] at hpz ⊢
    exact (hOrder p z p' z' hpp hzz).mp hpz
  have hSym := ForcingAtomicSymmetry.atomic_symmetry hM (ForcingConditionAction.actFormula (rho 6) a) (orderFormula (rho 0) mul) env (env (rho 6))
    (ForcingAtomicSymmetry.action_transport _ env (rho 6) a ha (ForcingProductSymmetry.order_on hM env rho mul a hData))
  have hppRel := (ForcingConditionAction.relation_semantics env (rho 6) a p p').mpr ((ForcingConditionAction.act_inside hpW).mpr hpp)
  refine ⟨d',vertex',j',tau',R,index,U,z',labelName',hac.1.2 d d' hdd,hCode',hVertex',hpi.1.2 j j' hjj,
    entry_move hM hData hBound hMove hEntry hTau,hz',hMoveOrder,
    assigned_move_values hM env rho I G F mul q bound labels E w top K B zero Q pi a families hp hq hpi hFix hA hCohen hdd hMove hjj hTau hAssigned,hLabel',?_,?_⟩
  · exact (hSym x labelName x' labelName' p p'
      ((ForcingNameConjugacy.action_iff env (rho 6) a x x').mpr hxx)
      ((ForcingNameConjugacy.action_iff env (rho 6) a labelName labelName').mpr hLabelMove) hpW hppRel).2.mp hx
  · exact (hSym y tau y' tau' p p'
      ((ForcingNameConjugacy.action_iff env (rho 6) a y y').mpr hyy)
      ((ForcingNameConjugacy.action_iff env (rho 6) a tau tau').mpr hTau) hpW hppRel).2.mp hy

theorem holds_move (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E w top K B zero Q labelMap bit mu pi inv c a ai : Fin k) (families : Fin 16 → Fin k)
    {p p' x x' y y' : M.Carrier .set}
    (hData : SystemData (fun j => env (rho j)) (env I) (env K) (env B) (env w) (env G) (env F) (env mu) (env pi) (env inv) (env c) (env a) (env ai))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hFix : CompositionGraph (env (rho 0)) (env pi) (env q) (env q))
    (hBound : ForcingSupportedNames.Supported (fun j => env (rho j)) (env G) (env bound))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hpp : PureKuratowski.PairMember M p p' (env a))
    (hxx : ForcingStabilizer.Action (env (rho 6)) (env a) x x')
    (hyy : ForcingStabilizer.Action (env (rho 6)) (env a) y y')
    (h : Holds hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y) :
    Holds hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p' x' y' := by
  have hA := hData.2.2.2.2.2.2.2.1
  have ha := ForcingProductFamily.action_permutation hA
  have ho := ForcingProductFamily.order hM (env mul) hData.1 hData.2.2.1 hA
  refine ⟨ha.1.2 p p' hpp,?_⟩
  intro r' hr' hrp
  obtain ⟨r,hr,hrr⟩ := ha.2.2 r' hr'
  have hrp0 : MapRel (orderFormula (rho 0) mul) env r p := by
    rw [ForcingProductSymmetry.orderFormula_semantics] at hrp ⊢
    exact (ho r p r' p' hrr hpp).mpr hrp
  obtain ⟨s,hs,hWitness⟩ := h.2 r hr hrp0
  have hsW := ForcingAssignedGraph.witness_condition hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families hWitness
  obtain ⟨s',hss,_⟩ := ha.1.1.2 s hsW
  refine ⟨s',?_,witness_move hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit mu pi inv c a ai families hData hq hFix hBound hLabelMap hTop hss hxx hyy hWitness⟩
  rw [ForcingProductSymmetry.orderFormula_semantics] at hs ⊢
  exact (ho s r s' r' hss hrr).mp hs

/-- Actual label-bound construction discharges bound support. All moved names
and all conditions remain quantified in the original pure-set language. -/
def moveSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E w top K B zero Q labelMap bit mu pi inv c a ai p p' x x' y y' : Fin k) (families : Fin 16 → Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small w mu))
    (.imp (ProjectSyntax.encode id (ForcingProductCovariance.systemData rho I K B w G F mu pi inv c a ai))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph (rho 0) pi q q))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels))
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K labelMap top bit bound))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge a p p'))
    (.imp (ProjectSyntax.encode id (ForcingStabilizer.action (rho 6) a x x'))
    (.imp (ProjectSyntax.encode id (ForcingStabilizer.action (rho 6) a y y'))
    (.conj (.imp (witness rho I G F mul q bound labels E w top K B zero Q labelMap bit families id p x y) (witness rho I G F mul q bound labels E w top K B zero Q labelMap bit families id p' x' y'))
      (.imp (holds rho I G F mul q bound labels E w top K B zero Q labelMap bit families id p x y) (holds rho I G F mul q bound labels E w top K B zero Q labelMap bit families id p' x' y'))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isInfiniteCardinal,
      ForcingAssignedGraph.witness_freeClosed,ForcingAssignedGraph.holds_freeClosed]

theorem move_models {k : Nat} (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E w top K B zero Q labelMap bit mu pi inv c a ai p p' x x' y y' : Fin k) (families : Fin 16 → Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (moveSentence rho I G F mul q bound labels E w top K B zero Q labelMap bit mu pi inv c a ai p p' x x' y y' families)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ForcingProductCovariance.systemData_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ForcingConditionGraphs.functionOn_semantics (M := M),ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingLabelSet.labelSet_semantics (M := M),ForcingLabelBound.labelBound_semantics (M := M),
    KuratowskiZF.source_edge,ForcingStabilizer.action_semantics (M := M),
    ForcingAssignedGraph.witness_semantics hM,ForcingAssignedGraph.holds_semantics hM]
  intro hw hMu hSmall hData hq hFix hLabelMap hTop hLabels hLabelBound hpp hxx hyy
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hData.2.1 hData.2.2.2.2.2.2.2.2.2
  obtain ⟨hHS,hFixed⟩ := ForcingLabelSet.HS_and_fixed hM (fun j => env (rho j)) hData.1 hData.2.1 hNormal hData.2.2.2.2.2.2.2.2.2 hw hSmall hLabelMap hTop hLabels
  have hBound := ForcingLocalNameTransport.bound_supported hM hData.1 hData.2.1 hHS hFixed ((ForcingLabelBound.bound_iff hM hLabels).mpr hLabelBound)
  exact ⟨witness_move hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit mu pi inv c a ai families hData hq hFix hBound hLabelMap hTop hpp hxx hyy,
    holds_move hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit mu pi inv c a ai families hData hq hFix hBound hLabelMap hTop hpp hxx hyy⟩

theorem move_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E w top K B zero Q labelMap bit mu pi inv c a ai p p' x x' y y' : Fin k) (families : Fin 16 → Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (moveSentence rho I G F mul q bound labels E w top K B zero Q labelMap bit mu pi inv c a ai p p' x x' y y' families)) := by
  apply ModelTransfer.derives
  intro M hM
  exact move_models rho I G F mul q bound labels E w top K B zero Q labelMap bit mu pi inv c a ai p p' x x' y y' families hM

end PPAC.Migration.ForcingAssignedGraphMove
