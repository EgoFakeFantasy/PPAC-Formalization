/- Pinned OrbitAssignments.OrbitRel:136 and OrbitAssignment:202.
The full root-fixing permutation group acts on corrected component assignments.
All group elements and moves are actual internal graphs, in the original language. -/
import PPAC.Migration.ForcingGermCorrectedDensity
import PPAC.Migration.ForcingGermCorrectedStability

namespace PPAC.Migration.ForcingOrbitAssignment
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingConditionGraphs (Permutation CompositionGraph InverseGraph)
open ForcingSupportSize (MapsTo Injection)
open ForcingGermCorrected (Corrected corrected)
open ForcingComponentMove (Move)
open ConstructionComponentCofinal (EncodedCommon Chain)
open ForcingComponentFibers (VertexFiber)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem corrected_reindex (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (other : Fin n → M.Carrier .set)
    (base : Fin k → Fin n) (he : ∀ i, other (base i) = env i) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder : Fin k) (d vertex label tau : M.Carrier .set) :
    Corrected hM other (fun j => base (rho j)) (base I) (base G) (base F) (base mul) (base q) (base bound) (base labels) (base E) (base root) (base w) (base chain) (base codes) (base order) (base ranks) (base selection) (base top) (base rankBound) (base labelSet) (base tab) (base r) (base K) (base B) (base zero) (base germGroup) (base quotient) (base nonidentity) (base high) (base detector) (base patternOrder) d vertex label tau ↔
    Corrected hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder d vertex label tau := by
  simp only [Corrected,ForcingGermCorrected.Shift,
    ForcingAssignmentInvariant.preliminary_reindex hM env other base he,he]

def OrbitRel (D I mul q root vertex : M.Carrier .set) : Prop :=
  ∃ pi target, Permutation I pi ∧ CompositionGraph D pi q q ∧
    Move D I mul q pi vertex target ∧ EncodedCommon D I mul q root target

def orbitRel {m : Nat} (D I mul q root vertex : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I.succ.succ 1))
    (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph D.succ.succ 1 q.succ.succ q.succ.succ))
    (.conj (ForcingComponentMove.move D.succ.succ I.succ.succ mul.succ.succ q.succ.succ 1 vertex.succ.succ 0)
      (ConstructionComponentCofinal.encodedCommon D.succ.succ I.succ.succ mul.succ.succ q.succ.succ root.succ.succ 0)))))

theorem orbitRel_freeClosed {m : Nat} (D I mul q root vertex : Fin m) :
    (orbitRel D I mul q root vertex).FreeClosed := by
  simp -implicitDefEqProofs [orbitRel,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ForcingComponentMove.move_freeClosed,ConstructionComponentCofinal.encodedCommon_freeClosed]

theorem orbitRel_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q root vertex : Fin m) :
    Project.Formula.satisfies env (orbitRel D I mul q root vertex) ↔
      OrbitRel (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound root) (env.bound vertex) := by
  simp only [orbitRel,OrbitRel,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ForcingComponentMove.move_semantics hM,ConstructionComponentCofinal.encodedCommon_semantics hM]
  rfl

def OrbitAssignment (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder : Fin k) (d vertex label tau : M.Carrier .set) : Prop :=
  ∃ pi inv act ac movedD movedVertex movedTau oldLabel,
    Permutation (env I) pi ∧ CompositionGraph (env (rho 0)) pi (env q) (env q) ∧
    Permutation (env I) inv ∧ InverseGraph pi inv ∧
    ForcingProductFamily.Action (env (rho 0)) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)) inv act ∧
    ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) inv ac ∧
    PureKuratowski.PairMember M d movedD ac ∧ Move (env (rho 0)) (env I) (env mul) (env q) inv vertex movedVertex ∧
    ForcingStabilizer.Action (env (rho 6)) act tau movedTau ∧
    (Project.FirstOrderSemantics.reduct M).mem oldLabel (env labelSet) ∧ PureKuratowski.PairMember M oldLabel label pi ∧
    Corrected hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder movedD movedVertex oldLabel movedTau

def orbitAssignment {k m : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder : Fin k)
    (base : Fin k → Fin m) (d vertex label tau : Fin m) : Project.Formula 1 m :=
  let up : Fin m → Fin (m+8) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation (up (base I)) 7))
    (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph (up (base (rho 0))) 7 (up (base q)) (up (base q))))
    (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation (up (base I)) 6))
    (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.inverseGraph 7 6))
    (.conj (ProjectSyntax.encode id (ForcingProductFamily.action (up (base (rho 0))) (up (base (rho 1))) (up (base (rho 2))) (up (base (rho 3))) (up (base (rho 4))) (up (base (rho 5))) (up (base (rho 6))) 6 5))
    (.conj (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (up (base (rho 1))) (up (base (rho 2))) (up (base (rho 3))) 6 4))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 4 (up d) 3))
    (.conj (ForcingComponentMove.move (up (base (rho 0))) (up (base I)) (up (base mul)) (up (base q)) 6 (up vertex) 2)
    (.conj (ProjectSyntax.encode id (ForcingStabilizer.action (up (base (rho 6))) 5 (up tau) 1))
    (.conj (.mem (.bound 0) (.bound (up (base labelSet))))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 7 0 (up label)))
    (corrected rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (fun i => up (base i)) 3 2 0 1))))))))))))))))))))

theorem orbitAssignment_freeClosed {k m : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder : Fin k)
    (base : Fin k → Fin m) (d vertex label tau : Fin m) :
    (orbitAssignment rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder base d vertex label tau).FreeClosed := by
  simp -implicitDefEqProofs [orbitAssignment,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ForcingComponentMove.move_freeClosed,ForcingGermCorrected.corrected_freeClosed]

theorem orbitAssignment_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder : Fin k) (base : Fin k → Fin m) (d vertex label tau : Fin m) :
    Project.Formula.satisfies env (orbitAssignment rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder base d vertex label tau) ↔
      OrbitAssignment hM (fun j => env.bound (base j)) rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder
        (env.bound d) (env.bound vertex) (env.bound label) (env.bound tau) := by
  simp only [orbitAssignment,OrbitAssignment,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ForcingConditionGraphs.inverseGraph_semantics (M := M),ForcingProductFamily.action_semantics (M := M),
    ForcingLocalTransport.cohenPart_semantics (M := M),KuratowskiZF.source_edge,
    ForcingComponentMove.move_semantics hM,ForcingStabilizer.action_semantics (M := M),ForcingGermCorrected.corrected_semantics hM]
  rfl

theorem corrected_common_at (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices : Fin k) (d vertex label tau : M.Carrier .set)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hGerm : ConstructionGermCosets.Carrier (env (rho 0)) (env I) (env mul) (env q) (env root) (env germGroup))
    (h : Corrected hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder d vertex label tau) :
    ConstructionComponentCofinal.EncodedCommon (env (rho 0)) (env I) (env mul) (env q) (env root) vertex := by
  let other : Fin (k+4) → M.Carrier .set := Fin.cases d (Fin.cases vertex (Fin.cases label (Fin.cases tau env)))
  let up : Fin k → Fin (k+4) := fun i => i.succ.succ.succ.succ
  have henv (i : Fin k) : other (up i) = env i := rfl
  have hInput := (corrected_reindex hM env other up henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder d vertex label tau).mpr h
  exact ForcingGermCorrected.corrected_common hM other (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up root) (up w) (up chain) (up codes) (up order) (up ranks) (up selection) (up top) (up rankBound) (up labelSet) (up tab) (up r) (up K) (up B) (up zero) (up germGroup) (up quotient) (up nonidentity) (up high) (up detector) (up patternOrder) (up one) (up vertices) 0 1 2 3 hm hJ hw hChain hGerm hInput

theorem orbitAssignment_orbit (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices : Fin k) (d vertex label tau : M.Carrier .set)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hGerm : ConstructionGermCosets.Carrier (env (rho 0)) (env I) (env mul) (env q) (env root) (env germGroup))
    (h : OrbitAssignment hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder d vertex label tau) :
    OrbitRel (env (rho 0)) (env I) (env mul) (env q) (env root) vertex := by
  obtain ⟨pi,inv,act,ac,oldD,oldVertex,oldTau,oldLabel,hPi,hFix,hInv,hInverse,_,_,_,hMove,_,_,_,hCorrected⟩ := h
  exact ⟨inv,oldVertex,hInv,ForcingDiagramCarrier.reverse hPi hq hInverse hFix,hMove,
    corrected_common_at hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices oldD oldVertex oldLabel oldTau hm hJ hw hChain hGerm hCorrected⟩

theorem orbitAssignment_label (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices diagrams objImage objects arrows mapImage maps vertexLabels : Fin k) (d vertex label tau : M.Carrier .set)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hGerm : ConstructionGermCosets.Carrier (env (rho 0)) (env I) (env mul) (env q) (env root) (env germGroup))
    (hDiagrams : ForcingDiagramCarrier.Carrier (env (rho 0)) (env I) (env diagrams))
    (hObj : MapsTo (env diagrams) (env objImage) (env objects))
    (hObjects : ForcingLabelSystem.Objects (env (rho 0)) (env diagrams) (env objects))
    (hArrows : ForcingEligibleMapFamily.Arrows (env (rho 0)) (env mul) (env diagrams) (env arrows))
    (hMaps : MapsTo (env arrows) (env mapImage) (env maps))
    (hMapFamily : ForcingLabelSystem.Maps (env objects) (env arrows) (env maps))
    (hSys : ForcingEligibleSystem.System (env (rho 0)) (env objects) (env maps))
    (hFibers : ForcingConcreteLabels.CommonFibers (env (rho 0)) (env I) (env mul) (env objects) (env maps))
    (hRootFiber : VertexFiber (env (rho 0)) (env mul) (env objects) (env maps) (env root) (env labelSet))
    (hVertexFiber : VertexFiber (env (rho 0)) (env mul) (env objects) (env maps) vertex (env vertexLabels))
    (h : OrbitAssignment hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder d vertex label tau) :
    (Project.FirstOrderSemantics.reduct M).mem label (env vertexLabels) := by
  obtain ⟨pi,inv,act,ac,oldD,oldVertex,oldTau,oldLabel,hPi,_,hInv,hInverse,_,_,_,hMove,_,hk,hLabel,hCorrected⟩ := h
  have hCommon := corrected_common_at hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices oldD oldVertex oldLabel oldTau hm hJ hw hChain hGerm hCorrected
  obtain ⟨oldFiber,hOldFiber⟩ := ForcingComponentFibers.exists_vertexFiber hM hDiagrams hObj (ForcingComponentMove.target_vertex hMove)
  have hEqual := hFibers (env q) (env root) oldVertex (env labelSet) oldFiber hCommon hRootFiber hOldFiber
  have hkOld : (Project.FirstOrderSemantics.reduct M).mem oldLabel oldFiber := hEqual ▸ hk
  have hBack := ForcingComponentMove.move_inverse hInv (fun x y => (hInverse y x).symm) hMove
  exact ForcingGermCorrectedDensity.label_move hM hm hPi hDiagrams hObj hObjects hArrows hMaps hMapFamily hSys hBack hOldFiber hVertexFiber hkOld hLabel

theorem orbitAssignment_mono (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau : Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hRoot : ConstructionComponentCarrier.Code (env root) (env r) (env idx) (env U))
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal (env K))
    (hResult : ConstructionConcreteSelector.Result hM (env w) (env (rho 0)) (env I) (env mul) (env q) (env root) (env chain) (env K) (env zero) (env germGroup) (env quotient) (env projection) (env reps) (env nonidentity) (env detectorDomain) (env detector) (env detectorSites) (env high) (env B) (env (rho 1)) (env (rho 2)) (env patternCarrier) (env patternOrder) (env selectorDomain) (env selector))
    (he : (Project.FirstOrderSemantics.reduct M).mem (env e) (env (rho 3)))
    (hde : ForcingPowerName.Subset (env d) (env e))
    (h : OrbitAssignment hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env d) (env vertex) (env label) (env tau)) :
    OrbitAssignment hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env e) (env vertex) (env label) (env tau) := by
  obtain ⟨pi,inv,act,ac,oldD,oldVertex,oldTau,oldLabel,hPi,hFix,hInv,hInverse,hAct,hCohen,hdd,hMove,hTau,hk,hLabel,hCorrected⟩ := h
  have hac := ForcingLocalTransport.part_permutation hCohen
  obtain ⟨oldE,hee,_⟩ := hac.1.1.2 (env e) he
  have hOldE := hac.1.2 (env e) oldE hee
  have hOrder : ForcingCohenOrderAction.OrderPreserving ac := by
    obtain ⟨_,_,_,_,ht,_,_,hGraph⟩ := hCohen
    exact ForcingCohenOrderAction.graph_order hp.2.2.1 ht hGraph
  have hOldDE := (hOrder (env e) (env d) oldE oldD hee hdd).mpr hde
  let other : Fin (k+5) → M.Carrier .set := Fin.cases oldD (Fin.cases oldE (Fin.cases oldVertex (Fin.cases oldLabel (Fin.cases oldTau env))))
  let up : Fin k → Fin (k+5) := fun i => i.succ.succ.succ.succ.succ
  have henv (i : Fin k) : other (up i) = env i := rfl
  have hInput := (corrected_reindex hM env other up henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder oldD oldVertex oldLabel oldTau).mpr hCorrected
  have hOutput := ForcingGermCorrectedStability.corrected_mono hM other (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up root) (up w) (up chain) (up codes) (up order) (up ranks) (up selection) (up top) (up rankBound) (up labelSet) (up tab) (up r) (up K) (up B) (up zero) (up germGroup) (up quotient) (up nonidentity) (up high) (up detector) (up patternOrder) (up one) (up vertices) (up idx) (up U) (up projection) (up reps) (up detectorDomain) (up detectorSites) (up patternCarrier) (up selectorDomain) (up selector) 0 1 2 3 4
    hm hp hChain hRoot hK hResult hOldE hOldDE hInput
  exact ⟨pi,inv,act,ac,oldE,oldVertex,oldTau,oldLabel,hPi,hFix,hInv,hInverse,hAct,hCohen,hee,hMove,hTau,hk,hLabel,
    (corrected_reindex hM env other up henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder oldE oldVertex oldLabel oldTau).mp hOutput⟩

theorem orbitAssignment_restrict (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one d vertex vertexT n label tau : Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hGerm : ConstructionGermCosets.Carrier (env (rho 0)) (env I) (env mul) (env q) (env root) (env germGroup))
    (hf : ConstructionComponentCofinal.EncodedArrow (env (rho 0)) (env I) (env mul) (env q) (env vertexT) (env vertex) (env n))
    (h : OrbitAssignment hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env d) (env vertex) (env label) (env tau)) :
    OrbitAssignment hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env d) (env vertexT) (env label) (env tau) := by
  obtain ⟨pi,inv,act,ac,oldD,oldVertex,oldTau,oldLabel,hPi,hFix,hInv,hInverse,hAct,hCohen,hdd,hMove,hTau,hk,hLabel,hCorrected⟩ := h
  have hInvFix := ForcingDiagramCarrier.reverse hPi hq hInverse hFix
  have hVertexT : ConstructionComponentCarrier.EncodedVertex (env (rho 0)) (env I) (env mul) (env q) (env vertexT) := by
    obtain ⟨rt,a,U,rv,b,V,ht,_,hvt,_,_⟩ := hf
    exact ⟨rt,a,U,ht,hvt⟩
  obtain ⟨oldT,hMoveT⟩ := ForcingComponentMove.exists_move hM hInv hInvFix hVertexT
  have hArrow := ForcingComponentMove.move_arrow hMoveT hMove hf
  let other : Fin (k+5) → M.Carrier .set := Fin.cases oldD (Fin.cases oldVertex (Fin.cases oldT (Fin.cases oldLabel (Fin.cases oldTau env))))
  let up : Fin k → Fin (k+5) := fun i => i.succ.succ.succ.succ.succ
  have henv (i : Fin k) : other (up i) = env i := rfl
  have hInput := (corrected_reindex hM env other up henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder oldD oldVertex oldLabel oldTau).mpr hCorrected
  have hOutput := ForcingGermCorrectedStability.corrected_restrict hM other (fun j => up (rho j)) (up I) (up G) (up F) (up mul) (up q) (up bound) (up labels) (up E) (up root) (up w) (up chain) (up codes) (up order) (up ranks) (up selection) (up top) (up rankBound) (up labelSet) (up tab) (up r) (up K) (up B) (up zero) (up germGroup) (up quotient) (up nonidentity) (up high) (up detector) (up patternOrder) (up one) 0 1 2 (up n) 3 4
    hm hp hq hGerm hArrow hInput
  exact ⟨pi,inv,act,ac,oldD,oldT,oldTau,oldLabel,hPi,hFix,hInv,hInverse,hAct,hCohen,hdd,hMoveT,hTau,hk,hLabel,
    (corrected_reindex hM env other up henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder oldD oldT oldLabel oldTau).mp hOutput⟩

def orbitSentence {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices d vertex label tau : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ConstructionGermCosets.carrier (rho 0) I mul q root germGroup)
    (.imp (orbitAssignment rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id d vertex label tau)
    (orbitRel (rho 0) I mul q root vertex))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionComponentCofinal.chain_freeClosed,ConstructionGermCosets.carrier_freeClosed,orbitAssignment_freeClosed,orbitRel_freeClosed]

theorem orbit_models {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices d vertex label tau : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (orbitSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices d vertex label tau)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionComponentCofinal.chain_semantics hM,ConstructionGermCosets.carrier_semantics hM,orbitAssignment_semantics hM,ForcingSupportSize.injection_semantics (M := M),orbitRel_semantics hM]
  exact orbitAssignment_orbit hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices (env d) (env vertex) (env label) (env tau)

theorem orbit_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices d vertex label tau : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (orbitSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices d vertex label tau)) := by
  apply ModelTransfer.derives
  intro M hM
  exact orbit_models rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices d vertex label tau hM

def labelSentence {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices diagrams objImage objects arrows mapImage maps vertexLabels d vertex label tau : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ConstructionGermCosets.carrier (rho 0) I mul q root germGroup)
    (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier (rho 0) I diagrams))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage))
    (.imp (ForcingLabelSystem.objectFamily (rho 0) diagrams objects)
    (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows (rho 0) mul diagrams arrows))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps arrows mapImage))
    (.imp (ForcingLabelSystem.mapFamily objects arrows maps)
    (.imp (ForcingEligibleSystem.system (rho 0) objects maps)
    (.imp (ForcingConcreteLabels.commonFibers (rho 0) I mul objects maps)
    (.imp (ForcingComponentFibers.vertexFiber (rho 0) mul objects maps root labelSet)
    (.imp (ForcingComponentFibers.vertexFiber (rho 0) mul objects maps vertex vertexLabels)
    (.imp (orbitAssignment rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id d vertex label tau)
    (.mem (.bound label) (.bound vertexLabels))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionComponentCofinal.chain_freeClosed,ConstructionGermCosets.carrier_freeClosed,orbitAssignment_freeClosed,ForcingLabelSystem.objectFamily_freeClosed,ForcingLabelSystem.mapFamily_freeClosed,ForcingEligibleSystem.system_freeClosed,ForcingConcreteLabels.commonFibers_freeClosed,ForcingComponentFibers.vertexFiber_freeClosed]

theorem label_models {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices diagrams objImage objects arrows mapImage maps vertexLabels d vertex label tau : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (labelSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices diagrams objImage objects arrows mapImage maps vertexLabels d vertex label tau)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionComponentCofinal.chain_semantics hM,ConstructionGermCosets.carrier_semantics hM,orbitAssignment_semantics hM,ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),ForcingLabelSystem.objectFamily_semantics hM,ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingLabelSystem.mapFamily_semantics hM,ForcingEligibleSystem.system_semantics hM,ForcingConcreteLabels.commonFibers_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM]
  exact orbitAssignment_label hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices diagrams objImage objects arrows mapImage maps vertexLabels (env d) (env vertex) (env label) (env tau)

theorem label_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices diagrams objImage objects arrows mapImage maps vertexLabels d vertex label tau : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (labelSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices diagrams objImage objects arrows mapImage maps vertexLabels d vertex label tau)) := by
  apply ModelTransfer.derives
  intro M hM
  exact label_models rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices diagrams objImage objects arrows mapImage maps vertexLabels d vertex label tau hM

def monoSentence {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ConstructionComponentCarrier.code root r idx U)
    (.imp (Project.Formula.isOrdinal (.bound K))
    (.imp (ConstructionConcreteSelector.resultFormula w (rho 0) I mul q root chain K zero germGroup quotient projection reps nonidentity detectorDomain detector detectorSites high B (rho 1) (rho 2) patternCarrier patternOrder selectorDomain selector)
    (.imp ( .mem (.bound e) (.bound (rho 3)))
    (.imp (Project.Formula.subset (.bound d) (.bound e))
    (.imp (orbitAssignment rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id d vertex label tau)
    (orbitAssignment rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id e vertex label tau))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ConstructionComponentCarrier.code_freeClosed,
      Project.Formula.isOrdinal,ConstructionConcreteSelector.resultFormula_freeClosed,
      Project.Formula.subset,orbitAssignment_freeClosed]

theorem mono_models {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (monoSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingProductFamily.presentation_semantics (M := M),ConstructionComponentCofinal.chain_semantics hM,
    ConstructionComponentCarrier.code_semantics hM,Project.Formula.satisfies_isOrdinal_iff,
    ConstructionConcreteSelector.resultFormula_semantics hM,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_subset_iff,orbitAssignment_semantics hM]
  exact orbitAssignment_mono hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau

theorem mono_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (monoSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau)) := by
  apply ModelTransfer.derives
  intro M hM
  exact mono_models rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices idx U projection reps detectorDomain detectorSites patternCarrier selectorDomain selector d e vertex label tau hM

/-- Pullback retains the literal selected representative and name action. -/
def restrictSentence {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one d vertex vertexT n label tau : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ConstructionGermCosets.carrier (rho 0) I mul q root germGroup)
    (.imp (ConstructionComponentCofinal.encodedArrow (rho 0) I mul q vertexT vertex n)
    (.imp (orbitAssignment rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id d vertex label tau)
    (orbitAssignment rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id d vertexT label tau)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionGermCosets.carrier_freeClosed,ConstructionComponentCofinal.encodedArrow_freeClosed,
      orbitAssignment_freeClosed]

theorem restrict_models {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one d vertex vertexT n label tau : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (restrictSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one d vertex vertexT n label tau)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingProductFamily.presentation_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ConstructionGermCosets.carrier_semantics hM,ConstructionComponentCofinal.encodedArrow_semantics hM,
    orbitAssignment_semantics hM]
  exact orbitAssignment_restrict hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one d vertex vertexT n label tau

theorem restrict_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one d vertex vertexT n label tau : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (restrictSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one d vertex vertexT n label tau)) := by
  apply ModelTransfer.derives
  intro M hM
  exact restrict_models rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one d vertex vertexT n label tau hM

/-- Exact source RootGroup = Fix(range q), using the already constructed group. -/
theorem rootGroup_iff {D I q A G Hq pi : M.Carrier .set}
    (hG : ForcingLabelPermutations.Carrier I G) (hq : Injection D I q)
    (hA : ForcingSupportedNames.Range D q A) (hHq : ForcingLabelPermutations.Fixing G A Hq) :
    (Project.FirstOrderSemantics.reduct M).mem pi Hq ↔ Permutation I pi ∧ CompositionGraph D pi q q := by
  constructor
  · intro h
    obtain ⟨hp,hFix⟩ := (hHq pi).mp h
    exact ⟨(hG pi).mp hp,ForcingComponentMove.root_fixed ((hG pi).mp hp) hq hA hFix⟩
  · rintro ⟨hp,hFix⟩
    apply (hHq pi).mpr
    refine ⟨(hG pi).mpr hp,?_⟩
    intro x hx
    obtain ⟨j,_,hjx⟩ := (hA x).mp hx
    obtain ⟨_,y,hjy,hyx⟩ := (hFix j x).mp hjx
    have hy : y = x := ForcingConditionGraphs.function_unique hq.1.1 hjy hjx
    exact hy ▸ hyx

def rootGroupSentence {k : Nat} (D I q A G Hq pi : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q D I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range D q A))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A Hq))
    (.iff (.mem (.bound pi) (.bound Hq))
      (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I pi))
        (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph D pi q q))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem rootGroup_models {k : Nat} (D I q A G Hq pi : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (rootGroupSentence D I q A G Hq pi)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M)]
  exact rootGroup_iff

theorem rootGroup_kernel_certificate {k : Nat} (D I q A G Hq pi : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (rootGroupSentence D I q A G Hq pi)) := by
  apply ModelTransfer.derives
  intro M hM
  exact rootGroup_models D I q A G Hq pi hM

end PPAC.Migration.ForcingOrbitAssignment
