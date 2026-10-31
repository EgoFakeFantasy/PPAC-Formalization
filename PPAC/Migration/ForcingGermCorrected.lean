/- Pinned StableSelectors.Corrected:413 and corrected_selected:419.
The existential representative belongs to the actual component group and is
Selected by the existing concrete selector. All inverse action witnesses are
actual internal graphs; representative independence consumes proved shift_eq.
Consumer: corrected_mono/common/congr and OrbitAssignments, not an arbitrary
assignment or a second selector construction. -/
import PPAC.Migration.ForcingAssignmentCosets
import PPAC.Migration.ConstructionGermConditionSelector

namespace PPAC.Migration.ForcingGermCorrected
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingGermPreliminary (Preliminary preliminary)
open ForcingSupportSize (MapsTo)
open ForcingComponentFibers (VertexFiber)
open ForcingConditionGraphs (Permutation InverseGraph)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Literal inverse move of all four coordinates, with actual action graphs. -/
def Shift (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r : Fin k) (pi d vertex label tau : M.Carrier .set) : Prop :=
  ∃ inv act ac movedD movedVertex movedLabel movedTau,
    Permutation (env I) pi ∧ Permutation (env I) inv ∧ InverseGraph pi inv ∧
    ForcingProductFamily.Action (env (rho 0)) (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)) inv act ∧
    ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) inv ac ∧
    PureKuratowski.PairMember M d movedD ac ∧
    ForcingComponentMove.Move (env (rho 0)) (env I) (env mul) (env q) inv vertex movedVertex ∧
    PureKuratowski.PairMember M label movedLabel inv ∧
    ForcingStabilizer.Action (env (rho 6)) act tau movedTau ∧
    Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r movedD movedVertex movedLabel movedTau

/-- Original Selected-class definition; the existing selector graph is its producer. -/
def Corrected (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder : Fin k) (d vertex label tau : M.Carrier .set) : Prop :=
  ∃ pi cls, (Project.FirstOrderSemantics.reduct M).mem pi (env germGroup) ∧
    ConstructionGermCosets.Class (env w) (env (rho 0)) (env chain) (env germGroup) pi cls ∧
    ConstructionGermSelected.Selected (env w) (env (rho 0)) (env chain) (env germGroup) (env quotient) (env nonidentity) (env K) (env (rho 1)) (env B) (env zero) (env high) (env detector) (env patternOrder) d cls ∧
    Shift hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r pi d vertex label tau

def shift {k m : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r : Fin k)
    (base : Fin k → Fin m) (pi d vertex label tau : Fin m) : Project.Formula 1 m :=
  let up : Fin m → Fin (m+7) := fun i => i.succ.succ.succ.succ.succ.succ.succ
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation (up (base I)) (up pi)))
    (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation (up (base I)) 6))
    (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.inverseGraph (up pi) 6))
    (.conj (ProjectSyntax.encode id (ForcingProductFamily.action (up (base (rho 0))) (up (base (rho 1))) (up (base (rho 2))) (up (base (rho 3))) (up (base (rho 4))) (up (base (rho 5))) (up (base (rho 6))) 6 5))
    (.conj (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (up (base (rho 1))) (up (base (rho 2))) (up (base (rho 3))) 6 4))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 4 (up d) 3))
    (.conj (ForcingComponentMove.move (up (base (rho 0))) (up (base I)) (up (base mul)) (up (base q)) 6 (up vertex) 2)
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 6 (up label) 1))
    (.conj (ProjectSyntax.encode id (ForcingStabilizer.action (up (base (rho 6))) 5 (up tau) 0))
    (preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r (fun i => up (base i)) 3 2 1 0)))))))))))))))))

theorem shift_freeClosed {k m : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r : Fin k)
    (base : Fin k → Fin m) (pi d vertex label tau : Fin m) :
    (shift rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r base pi d vertex label tau).FreeClosed := by
  simp -implicitDefEqProofs [shift,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ForcingComponentMove.move_freeClosed,ForcingGermPreliminary.preliminary_freeClosed]

theorem shift_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r : Fin k) (base : Fin k → Fin m) (pi d vertex label tau : Fin m) :
    Project.Formula.satisfies env (shift rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r base pi d vertex label tau) ↔
    Shift hM (fun i => env.bound (base i)) rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r
      (env.bound pi) (env.bound d) (env.bound vertex) (env.bound label) (env.bound tau) := by
  simp only [shift,Shift,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingConditionGraphs.inverseGraph_semantics (M := M),
    ForcingProductFamily.action_semantics (M := M),ForcingLocalTransport.cohenPart_semantics (M := M),
    KuratowskiZF.source_edge,ForcingComponentMove.move_semantics hM,
    ForcingStabilizer.action_semantics (M := M),ForcingGermPreliminary.preliminary_semantics hM]
  rfl

def corrected {k m : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder : Fin k)
    (base : Fin k → Fin m) (d vertex label tau : Fin m) : Project.Formula 1 m :=
  let up : Fin m → Fin (m+2) := fun i => i.succ.succ
  (.existsE (.existsE (.conj (.mem (.bound 1) (.bound (up (base germGroup))))
    (.conj (ConstructionGermCosets.eqClass (up (base w)) (up (base (rho 0))) (up (base chain)) (up (base germGroup)) 1 0)
    (.conj (ConstructionGermSelected.selected (up (base w)) (up (base (rho 0))) (up (base chain)) (up (base germGroup)) (up (base quotient)) (up (base nonidentity)) (up (base K)) (up (base (rho 1))) (up (base B)) (up (base zero)) (up (base high)) (up (base detector)) (up (base patternOrder)) (up d) 0)
    (shift rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r (fun i => up (base i)) 1 (up d) (up vertex) (up label) (up tau)))))))

theorem corrected_freeClosed {k m : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder : Fin k)
    (base : Fin k → Fin m) (d vertex label tau : Fin m) :
    (corrected rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder base d vertex label tau).FreeClosed := by
  simp -implicitDefEqProofs [corrected,Definitional.Formula.FreeClosed,ConstructionGermCosets.eqClass_freeClosed,
    ConstructionGermSelected.selected_freeClosed,shift_freeClosed]

theorem corrected_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder : Fin k) (base : Fin k → Fin m) (d vertex label tau : Fin m) :
    Project.Formula.satisfies env (corrected rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder base d vertex label tau) ↔
    Corrected hM (fun i => env.bound (base i)) rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder
      (env.bound d) (env.bound vertex) (env.bound label) (env.bound tau) := by
  simp only [corrected,Corrected,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ConstructionGermCosets.eqClass_semantics hM,
    ConstructionGermSelected.selected_semantics hM,shift_semantics hM]
  rfl

theorem corrected_selected (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel germGroup quotient nonidentity high detector patternOrder selectorDomain selector coset : Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hData : ForcingProductCovariance.SystemData (fun j => env (rho j)) (env I) (env K) (env B) (env w) (env G) (env F) (env mu) (env pi) (env inv) (env c) (env act) (env ai))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hSmallD : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hSmall : ForcingSupportSize.Small (env w) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul) (env one) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hLabelMap : ForcingConditionGraphs.FunctionOn (env K) (env labelMap))
    (hTop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env labels))
    (hLabelBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env labelMap) (env top) (env bit) (env bound))
    (hBound : ForcingSupportedNames.Supported (fun j => env (rho j)) (env G) (env bound))
    (hq : ForcingSupportSize.Injection (env (rho 0)) (env I) (env q))
    (hA : ForcingSupportedNames.Range (env (rho 0)) (env q) (env A))
    (hHq : ForcingLabelPermutations.Fixing (env G) (env A) (env Hq))
    (hE : ForcingSupportedNames.Supported (fun j => env (rho j)) (env Hq) (env E))
    (hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hCarrier : ForcingTailCodes.Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) (env codes))
    (hGroup : ForcingTailGroup.TailGroup (env w) (env (rho 0)) (env G) (env chain) (env group))
    (hc : ForcingLocalTransport.CohenPart (env (rho 1)) (env (rho 2)) (env (rho 3)) (env inv) (env ac))
    (hdd : PureKuratowski.PairMember M (env d) (env movedD) (env ac))
    (hRoot : ConstructionComponentCarrier.Code (env root) (env r) (env idx) (env U))
    (hFamily : ForcingOrdinalFixed.FixedFamily (fun j => env (rho j)) (env G) (env F) (env group) (env codes) (env ranks))
    (hType : ForcingOrdinalFixed.Fixed (fun j => env (rho j)) (env G) (env F) (env group) (env selection))
    (hMove : ForcingComponentMove.Move (env (rho 0)) (env I) (env mul) (env q) (env inv) (env vertex) (env movedVertex))
    (hTau : ForcingStabilizer.Action (env (rho 6)) (env ai) (env tau) (env movedTau))
    (hDiagrams : ForcingDiagramCarrier.Carrier (env (rho 0)) (env I) (env diagrams))
    (hObj : MapsTo (env diagrams) (env objImage) (env objects))
    (hObjects : ForcingLabelSystem.Objects (env (rho 0)) (env diagrams) (env objects))
    (hCommon : ForcingConcreteLabels.CommonFibers (env (rho 0)) (env I) (env mul) (env objects) (env maps))
    (hRootFiber : VertexFiber (env (rho 0)) (env mul) (env objects) (env maps) (env root) (env labelSet))
    (hLabelMove : PureKuratowski.PairMember M (env label) (env movedLabel) (env inv))
    (hSelector : ConstructionGermConditionSelector.Selector (env w) (env (rho 0)) (env chain) (env germGroup) (env quotient) (env nonidentity) (env K) (env (rho 1)) (env B) (env zero) (env high) (env detector) (env patternOrder) (env (rho 2)) (env selectorDomain) (env selector))
    (hPiGerm : (Project.FirstOrderSemantics.reduct M).mem (env pi) (env germGroup))
    (hPiClass : ConstructionGermCosets.Class (env w) (env (rho 0)) (env chain) (env germGroup) (env pi) (env coset))
    (hSelected : ConstructionGermSelected.Selected (env w) (env (rho 0)) (env chain) (env germGroup) (env quotient) (env nonidentity) (env K) (env (rho 1)) (env B) (env zero) (env high) (env detector) (env patternOrder) (env d) (env coset))
    (hTauName : ForcingNames.IsName (env (rho 6)) (env tau)) :
    Corrected hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env d) (env vertex) (env label) (env tau) ↔
    Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r (env movedD) (env movedVertex) (env movedLabel) (env movedTau) := by
  constructor
  · rintro ⟨sigma,cls,hSigmaGerm,hClass,hSel,hShift⟩
    obtain ⟨sigmaInv,sigmaAct,sigmaAc,sigmaD,sigmaVertex,sigmaLabel,sigmaTau,
      hSigma,hSigmaInv,hSigmaInverse,hSigmaAction,hSigmaCohen,hSigmaD,hSigmaMove,hSigmaLabel,hSigmaTau,hPreliminary⟩ := hShift
    have hd := (hData.1.2.2.1 (env d)).mp
      (ForcingConditionGraphs.function_input (ForcingLocalTransport.part_permutation hc).1.1 hdd)
    have hEdge := (hSelector.2.2 (env d) cls).mpr ⟨hd,hSel⟩
    have hChosen := (hSelector.2.2 (env d) (env coset)).mpr ⟨hd,hSelected⟩
    have hClassEq := ForcingConditionGraphs.function_unique hSelector.2.1.1 hEdge hChosen
    have hSame := (ConstructionGermCosets.class_eq_iff hM hw
      (ForcingConditionGraphs.function_input hChain.1.1 hChain.2.1) hChain hPiGerm hClass hPiClass).mp hClassEq
    let other : Fin (k+8) → M.Carrier .set := Fin.cases sigma (Fin.cases sigmaInv
      (Fin.cases sigmaAct (Fin.cases sigmaAc (Fin.cases sigmaD (Fin.cases sigmaVertex
      (Fin.cases sigmaLabel (Fin.cases sigmaTau env)))))))
    let up : Fin k → Fin (k+8) := fun j => j.succ.succ.succ.succ.succ.succ.succ.succ
    have henv (j : Fin k) : other (up j) = env j := by
      simp only [other,up,Fin.cases_succ]
    have hShiftEq := ForcingAssignmentCosets.shift_eq hM hChoice other (fun j => up (rho j))
      (up I) (up K) (up B) (up w) (up G) (up F) (up mul) (up one) (up mu) (up history) (up kappa) (up mark) (up H) (up C) (up incoming) (up base) (up q) (up A) (up Hq) (up labelMap) (up top) (up bit) (up labels) (up E) (up bound) (up pi) (up inv) (up c) (up act) (up ai) (up zero) (up root) (up vertices) (up chain) (up names) (up codes) (up order) (up group) (up r) (up idx) (up U) (up ranks) (up selection) (up rankBound) (up labelSet) (up tab) (up ac) (up d) (up movedD) (up vertex) (up movedVertex) (up tau) (up movedTau) (up label) (up diagrams) (up objImage) (up objects) (up maps) (up movedLabel) 0 1 2 3 4 5 6 7
      hm hJ hData hw hMu hI hSmallD hSmall hMergers hRow hLabelMap hTop hLabels hLabelBound hBound
      hq hA hHq hE hChain hCarrier hGroup hSame hc hdd hRoot hFamily hType hMove hTau
      hDiagrams hObj hObjects hCommon hRootFiber hLabelMove
      hSigma hSigmaInv hSigmaInverse hSigmaAction hSigmaCohen hSigmaD hSigmaMove hSigmaTau hSigmaLabel hTauName
    have hInput := (ForcingAssignmentInvariant.preliminary_reindex hM env other up henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r
      sigmaD sigmaVertex sigmaLabel sigmaTau).mpr hPreliminary
    exact (ForcingAssignmentInvariant.preliminary_reindex hM env other up henv rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r
      (env movedD) (env movedVertex) (env movedLabel) (env movedTau)).mp (hShiftEq.mpr hInput)
  · intro hPreliminary
    obtain ⟨_,_,hPi,hInv,hInverse,_,_,_,hAI,_⟩ := hData
    exact ⟨env pi,env coset,hPiGerm,hPiClass,hSelected,env inv,env ai,env ac,
      env movedD,env movedVertex,env movedLabel,env movedTau,hPi,hInv,hInverse,hAI,hc,hdd,hMove,hLabelMove,hTau,hPreliminary⟩

/-- Pinned corrected_common: membership in the actual component stabilizer is used. -/
theorem corrected_common (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices d vertex label tau : Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins (env (rho 0)) (env mul))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) (env zero) (env root) (env vertices) (env chain))
    (hGerm : ConstructionGermCosets.Carrier (env (rho 0)) (env I) (env mul) (env q) (env root) (env germGroup))
    (h : Corrected hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder (env d) (env vertex) (env label) (env tau)) :
    ConstructionComponentCofinal.EncodedCommon (env (rho 0)) (env I) (env mul) (env q) (env root) (env vertex) := by
  obtain ⟨pi,cls,hpi,_,_,inv,act,ac,movedD,movedVertex,movedLabel,movedTau,
    _,hInv,hInverse,_,_,_,hMove,_,_,hPreliminary⟩ := h
  obtain ⟨hPi,hFix,rootT,hRootMove,hRootCommon⟩ := (hGerm pi).mp hpi
  have hCommon := ForcingGermPreliminary.preliminary_common hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r hw hChain hPreliminary
  have hBack := ForcingComponentMove.move_inverse hInv (fun x y => (hInverse y x).symm) hMove
  have hTransport := ForcingComponentMove.move_common hM hPi hFix hRootMove hBack hCommon
  exact (ForcingComponentRebase.common_iff hM hm hJ hRootCommon).mpr hTransport

def commonSentence {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices d vertex label tau : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ConstructionGermCosets.carrier (rho 0) I mul q root germGroup)
    (.imp (corrected rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id d vertex label tau)
    (ConstructionComponentCofinal.encodedCommon (rho 0) I mul q root vertex)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ConstructionGermCosets.carrier_freeClosed,corrected_freeClosed,ConstructionComponentCofinal.encodedCommon_freeClosed]

theorem common_models {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices d vertex label tau : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (commonSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices d vertex label tau)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionComponentCofinal.chain_semantics hM,
    ConstructionGermCosets.carrier_semantics hM,corrected_semantics hM,ConstructionComponentCofinal.encodedCommon_semantics hM]
  exact corrected_common hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices d vertex label tau

theorem common_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices d vertex label tau : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (commonSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices d vertex label tau)) := by
  apply ModelTransfer.derives
  intro M hM
  exact common_models rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder one vertices d vertex label tau hM

def selectedSentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel germGroup quotient nonidentity high detector patternOrder selectorDomain selector coset : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul)
    (.imp (ProjectSyntax.encode id (ForcingProductCovariance.systemData rho I K B w G F mu pi inv c act ai))
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (ConstructionSaturationIndex.hartogs mu I)
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small w mu))
    (.imp (ConstructionSaturationMergers.allMergers w history kappa)
    (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul one mark H C incoming base kappa)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn labelMap K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K labelMap top bit labels))
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K labelMap top bit bound))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho G bound))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q A))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G A Hq))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq E))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ForcingTailCodes.carrier rho G F bound w names chain codes)
    (.imp (ForcingTailGroup.tailGroup w (rho 0) G chain group)
    (.imp (ProjectSyntax.encode id (ForcingLocalTransport.cohenPart (rho 1) (rho 2) (rho 3) inv ac))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge ac d movedD))
    (.imp (ConstructionComponentCarrier.code root r idx U)
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixedFamily rho G F group codes ranks))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixed rho G F group selection))
    (.imp (ForcingComponentMove.move (rho 0) I mul q inv vertex movedVertex)
    (.imp (ProjectSyntax.encode id (ForcingStabilizer.action (rho 6) ai tau movedTau))
    (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier (rho 0) I diagrams))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage))
    (.imp (ForcingLabelSystem.objectFamily (rho 0) diagrams objects)
    (.imp (ForcingConcreteLabels.commonFibers (rho 0) I mul objects maps)
    (.imp (ForcingComponentFibers.vertexFiber (rho 0) mul objects maps root labelSet)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge inv label movedLabel))
    (.imp (ConstructionGermConditionSelector.selector w (rho 0) chain germGroup quotient nonidentity K (rho 1) B zero high detector patternOrder (rho 2) selectorDomain selector)
    (.imp (.mem (.bound pi) (.bound germGroup))
    (.imp (ConstructionGermCosets.eqClass w (rho 0) chain germGroup pi coset)
    (.imp (ConstructionGermSelected.selected w (rho 0) chain germGroup quotient nonidentity K (rho 1) B zero high detector patternOrder d coset)
    (.imp (ProjectSyntax.encode id (ForcingNames.isName (rho 6) tau))
    (.iff (corrected rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B zero germGroup quotient nonidentity high detector patternOrder id d vertex label tau)
    (preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r id movedD movedVertex movedLabel movedTau))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionSaturationIndex.hartogs_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ForcingTailCodes.carrier_freeClosed,ForcingTailGroup.tailGroup_freeClosed,
      ConstructionComponentCarrier.code_freeClosed,ForcingComponentMove.move_freeClosed,
      ForcingGermPreliminary.preliminary_freeClosed,ForcingLabelSystem.objectFamily_freeClosed,
      ForcingConcreteLabels.commonFibers_freeClosed,ForcingComponentFibers.vertexFiber_freeClosed,ConstructionGermConditionSelector.selector_freeClosed,
      ConstructionGermCosets.eqClass_freeClosed,ConstructionGermSelected.selected_freeClosed,corrected_freeClosed]

theorem selected_models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel germGroup quotient nonidentity high detector patternOrder selectorDomain selector coset : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (selectedSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel germGroup quotient nonidentity high detector patternOrder selectorDomain selector coset)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductCovariance.systemData_semantics (M := M),ConstructionSaturationIndex.hartogs_semantics hM,
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ConstructionComponentCofinal.chain_semantics hM,
    ForcingTailCodes.carrier_semantics hM,ForcingTailGroup.tailGroup_semantics hM,
    ForcingLocalTransport.cohenPart_semantics (M := M),KuratowskiZF.source_edge,
    ConstructionComponentCarrier.code_semantics hM,ForcingOrdinalFixed.fixedFamily_semantics (M := M),
    ForcingOrdinalFixed.fixed_semantics (M := M),ForcingComponentMove.move_semantics hM,
    ForcingStabilizer.action_semantics (M := M),ForcingGermPreliminary.preliminary_semantics hM,ForcingNames.isName_semantics (M := M),
    Project.Formula.satisfies_iff_iff,ForcingDiagramCarrier.carrier_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingLabelSystem.objectFamily_semantics hM,
    ForcingConcreteLabels.commonFibers_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM,ConstructionGermConditionSelector.selector_semantics hM,
    ConstructionGermCosets.eqClass_semantics hM,ConstructionGermSelected.selected_semantics hM,corrected_semantics hM,
    Project.Formula.satisfies_mem_iff]
  exact corrected_selected hM hChoice env rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel germGroup quotient nonidentity high detector patternOrder selectorDomain selector coset

theorem selected_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel germGroup quotient nonidentity high detector patternOrder selectorDomain selector coset : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (selectedSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel germGroup quotient nonidentity high detector patternOrder selectorDomain selector coset))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let witness := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    {bound := Fin.elim0,free := fun _ => witness}
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (selectedSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel germGroup quotient nonidentity high detector patternOrder selectorDomain selector coset)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (selectedSentence rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel germGroup quotient nonidentity high detector patternOrder selectorDomain selector coset)).mp
      (selected_models rho I K B w G F mul one mu history kappa mark H C incoming base q A Hq labelMap top bit labels E bound pi inv c act ai zero root vertices chain names codes order group r idx U ranks selection rankBound labelSet tab ac d movedD vertex movedVertex tau movedTau label diagrams objImage objects maps movedLabel germGroup quotient nonidentity high detector patternOrder selectorDomain selector coset hL hChoice)

end PPAC.Migration.ForcingGermCorrected
