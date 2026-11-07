/- Pinned OrdinalPresentation.PresentationIndex/presentationPartial:305-337.
The index is the full internal set of literal raw edges and supporting diagrams.
Ranges/fixing groups are existential properties, never extra index coordinates.
The source orbit graph is uniquely determined, so native functional image
constructs the internal family in ZF without a new choice premise. -/
import PPAC.Migration.ForcingPartialOrbitGraph

namespace PPAC.Migration.ForcingPresentationFamily
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args3)
open ForcingProductFamily (Presentation actionFormula)
open ForcingMapConditions (MapRel)
open ForcingConditionGraphs (FunctionOn)
open ForcingHS (HS)
open ForcingSupportedNames (Range Supported)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingPairUnion (domain domain_semantics)
open ForcingDefaultRelation (PartialUnique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Record (v : Fin 7 → M.Carrier .set) (I G X i sigma b root : M.Carrier .set) : Prop :=
  ∃ e, (Project.FirstOrderSemantics.reduct M).mem e X ∧ PureKuratowski.Code M i e root ∧
    PureKuratowski.Code M e sigma b ∧ ForcingSupportSize.Injection (v 0) I root ∧ ∃ J,
      Range (v 0) root J ∧ ∃ H, ForcingLabelPermutations.Fixing G J H ∧ Supported v H sigma

def Member (v : Fin 7 → M.Carrier .set) (I G X i : M.Carrier .set) : Prop :=
  ∃ sigma b root, Record v I G X i sigma b root

def Index (v : Fin 7 → M.Carrier .set) (I G X indices : M.Carrier .set) : Prop :=
  ∀ i, (Project.FirstOrderSemantics.reduct M).mem i indices ↔ Member v I G X i

/-- Every literal edge and every supporting diagram occurs, without any rank cutoff. -/
def record {k : Nat} (rho : Fin 7 → Fin k) (I G X i sigma b root : Fin k) : Formula k :=
  .ex ((Formula.mem (Fin.last k) X.castSucc).conj
    ((PairSyntax.ordered i.castSucc (Fin.last k) root.castSucc).conj
      ((PairSyntax.ordered (Fin.last k) sigma.castSucc b.castSucc).conj
        ((Source.SetLanguage.injection root.castSucc (rho 0).castSucc I.castSucc).conj
          (.ex ((ForcingSupportedNames.range (rho 0).castSucc.castSucc root.castSucc.castSucc (Fin.last (k+1))).conj
            (.ex ((ForcingLabelPermutations.fixing G.castSucc.castSucc.castSucc (Fin.last (k+1)).castSucc (Fin.last (k+2))).conj
              (ForcingEquivariantMix.fixedAll (fun j => (rho j).castSucc.castSucc.castSucc) (Fin.last (k+2)) sigma.castSucc.castSucc.castSucc)))))))))

theorem record_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G X i sigma b root : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (record rho I G X i sigma b root) ↔
      Record (fun j => env (rho j)) (env I) (env G) (env X) (env i) (env sigma) (env b) (env root) := by
  simp only [record,Record,Formula.Realize,KuratowskiZF.source_code,ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingEquivariantMix.fixedAll_semantics (M := M),Supported,Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def member {k : Nat} (rho : Fin 7 → Fin k) (I G X i : Fin k) : Formula k :=
  .ex (.ex (.ex (record (fun j => (rho j).castSucc.castSucc.castSucc)
    I.castSucc.castSucc.castSucc G.castSucc.castSucc.castSucc X.castSucc.castSucc.castSucc i.castSucc.castSucc.castSucc
    (Fin.last k).castSucc.castSucc (Fin.last (k+1)).castSucc (Fin.last (k+2)))))

theorem member_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G X i : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (member rho I G X i) ↔
      Member (fun j => env (rho j)) (env I) (env G) (env X) (env i) := by
  simp only [member,Member,Formula.Realize,record_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

def index {k : Nat} (rho : Fin 7 → Fin k) (I G X indices : Fin k) : Formula k :=
  .all ((Formula.mem (Fin.last k) indices.castSucc).iff
    (member (fun j => (rho j).castSucc) I.castSucc G.castSucc X.castSucc (Fin.last k)))

theorem index_semantics {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G X indices : Fin k) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (index rho I G X indices) ↔
      Index (fun j => env (rho j)) (env I) (env G) (env X) (env indices) := by
  simp only [index,Index,Source.Formula.iff,Formula.Realize,member_semantics (M := M),Fin.lastCases_last,Fin.lastCases_castSucc]
  exact forall_congr' (fun _ => ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.mp,h.mpr⟩⟩)

theorem construct_index (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G X : Fin k)
    (hDiagrams : ForcingDiagramCarrier.Carrier (env (rho 0)) (env I) (env (rho 4))) :
    ∃ indices, Index (fun j => env (rho j)) (env I) (env G) (env X) indices := by
  obtain ⟨bound,hBound⟩ := ForcingCohenCoordinates.exists_cartesian hM (env X) (env (rho 4))
  let query := member (fun j => (rho j).castSucc) I.castSucc G.castSucc X.castSucc (Fin.last k)
  have hq i : Formula.Realize (Project.FirstOrderSemantics.reduct M).mem (Fin.lastCases i env) query ↔
      Member (fun j => env (rho j)) (env I) (env G) (env X) i := by
    simpa only [query,Fin.lastCases_last,Fin.lastCases_castSucc] using
      member_semantics (M := M) (Fin.lastCases i env) (fun j => (rho j).castSucc) I.castSucc G.castSucc X.castSucc (Fin.last k)
  have hSep := (GodelDefOutput.separation_semantics (Project.FirstOrderSemantics.reduct M).mem query).mp
    ((Translation.realizes_sentence M _).mp ((SeparationSyntax.source_separation query).semantically_entails M hM))
  obtain ⟨indices,hIndices⟩ := hSep env bound
  refine ⟨indices,fun i => ?_⟩
  constructor
  · intro hi
    exact (hq i).mp ((hIndices i).mp hi).2
  · intro hi
    have hMember := hi
    obtain ⟨sigma,b,root,e,he,hCode,_hEdge,hRoot,_rest⟩ := hi
    exact (hIndices i).mpr ⟨(hBound i).mpr ⟨e,he,root,(hDiagrams root).mpr hRoot,hCode⟩,(hq i).mpr hMember⟩

theorem record_unique {v : Fin 7 → M.Carrier .set} {I G X i s b root s' b' root' : M.Carrier .set}
    (h : Record v I G X i s b root) (h' : Record v I G X i s' b' root') : s = s' ∧ b = b' ∧ root = root' := by
  obtain ⟨e,_he,hCode,hEdge,_⟩ := h
  obtain ⟨e',_he',hCode',hEdge',_⟩ := h'
  obtain ⟨ee,er⟩ := PureKuratowski.code_injective hCode hCode'
  have he' : PureKuratowski.Code M e s' b' := ee.symm ▸ hEdge'
  obtain ⟨es,eb⟩ := PureKuratowski.code_injective hEdge he'
  exact ⟨es,eb,er⟩

def Selected {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (v : Fin 7 → M.Carrier .set) (I K G F top one c hi X i graph : M.Carrier .set) : Prop :=
  ∃ sigma b root, Record v I G X i sigma b root ∧ ∃ j z left seed,
    PureKuratowski.PairMember M one j root ∧ ForcingSupportingRoot.Code z top root ∧
      ForcingLabelNames.Label (v 6) K c top j hi left ∧ ForcingOrderedPairName.OrderedPairName top left sigma seed ∧
        ForcingPartialOrbitGraph.Graph v G seed z graph ∧ HS actionFormula v G (v 6) F graph ∧ Supported v G graph ∧
          PartialUnique (R := R) (H := Hdom) (env := env) (P := v 6) graph

private theorem code_unique (hM : FirstOrder.Theory.Models M nativeZF) {z z' top root : M.Carrier .set}
    (hz : ForcingSupportingRoot.Code z top root) (hz' : ForcingSupportingRoot.Code z' top root) : z = z' := by
  obtain ⟨c,hc,hs⟩ := hz
  obtain ⟨c',hc',hs'⟩ := hz'
  have e := KuratowskiZF.code_unique hM hc' hc
  cases e
  exact ForcingWithTopCarrier.single_unique hM hs hs'

/-- The source presentationPartial is a canonical graph, not a chosen
representative. Its actual uniqueness allows a native ZF function image. -/
theorem selected_unique (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {v : Fin 7 → M.Carrier .set} {I K G F top one c hi X i graph graph' : M.Carrier .set}
    (h : Selected R Hdom env v I K G F top one c hi X i graph)
    (h' : Selected R Hdom env v I K G F top one c hi X i graph') : graph = graph' := by
  obtain ⟨sigma,b,root,hRec,j,z,left,seed,hCenter,hZ,hLabel,hPair,hGraph,_⟩ := h
  obtain ⟨sigma',b',root',hRec',j',z',left',seed',hCenter',hZ',hLabel',hPair',hGraph',_⟩ := h'
  obtain ⟨es,eb,er⟩ := record_unique hRec hRec'
  cases es
  cases eb
  cases er
  obtain ⟨_e,_he,_hc,_hedge,hRoot,_⟩ := hRec
  have ej := ForcingConditionGraphs.function_unique hRoot.1.1 hCenter hCenter'
  cases ej
  have ez := code_unique hM hZ hZ'
  cases ez
  have el := ForcingLabelNames.unique hM hLabel hLabel'
  cases el
  have ep := ForcingOrderedPairName.unique hM hPair hPair'
  cases ep
  exact (ModelTransfer.extensionality hM).eq_of_same_members graph graph' (fun e => (hGraph e).trans (hGraph' e).symm)

/-- Each actual index produces its source graph by the accepted constructor;
all source support/uniqueness witnesses are discharged, not supplied as a family. -/
theorem exists_selected (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul top one values c lo hi X labels : Fin k) {i : M.Carrier .set}
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w)) (hK : ¬ ForcingSupportSize.Small (env K) (env w))
    (hc : ForcingSupportSize.Injection (env K) (env values) (env c)) (ht : ForcingWithTopCarrier.Empty (env top))
    (hlo : (Project.FirstOrderSemantics.reduct M).mem (env lo) (env B)) (hhi : (Project.FirstOrderSemantics.reduct M).mem (env hi) (env B))
    (hBits : env lo ≠ env hi)
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env c) (env top) (env hi) (env labels))
    (hLabelsHS : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env labels))
    (hMember : Member (fun j => env (rho j)) (env I) (env G) (env X) i) :
    ∃ graph, Selected (orderFormula (rho 0) mul) (domain rho G F) env (fun j => env (rho j))
      (env I) (env K) (env G) (env F) (env top) (env one) (env c) (env hi) (env X) i graph := by
  obtain ⟨sigma,b,root,hRec⟩ := hMember
  obtain ⟨e,he,hCode,hEdge,hRoot,J,hRange,H,hFix,hSupport⟩ := hRec
  have hSigma := ForcingHS.child hX (show PureKuratowski.PairMember M sigma b (env X) from ⟨e,hEdge,he⟩)
  let other : Fin (k+4) → M.Carrier .set := Fin.cases H (Fin.cases J (Fin.cases root (Fin.cases sigma env)))
  let rr : Fin 7 → Fin (k+4) := fun j => (rho j).succ.succ.succ.succ
  obtain ⟨j,z,left,seed,graph,hCenter,hZ,hLabel,hPair,hGraph,hGraphHS,hFixed,_hApp,hUnique,_hMember⟩ :=
    ForcingPartialOrbitGraph.construct_partial hM other rr I.succ.succ.succ.succ K.succ.succ.succ.succ B.succ.succ.succ.succ
      w.succ.succ.succ.succ G.succ.succ.succ.succ F.succ.succ.succ.succ mul.succ.succ.succ.succ top.succ.succ.succ.succ
      one.succ.succ.succ.succ values.succ.succ.succ.succ c.succ.succ.succ.succ lo.succ.succ.succ.succ hi.succ.succ.succ.succ
      2 1 0 3 labels.succ.succ.succ.succ hPres hG hF hm hw hK hc ht hlo hhi hBits hRoot hRange hFix hSupport hSigma hLabels hLabelsHS
  have hR : ∀ a b, MapRel (orderFormula (rho 0) mul) env a b ↔ MapRel (orderFormula (rr 0) mul.succ.succ.succ.succ) other a b := by
    intro a b
    exact (orderFormula_semantics env (rho 0) mul a b).trans (orderFormula_semantics other (rr 0) mul.succ.succ.succ.succ a b).symm
  have hH : ∀ a, ForcingClassEvaluation.Predicate (domain rho G F) env a ↔
      ForcingClassEvaluation.Predicate (domain rr G.succ.succ.succ.succ F.succ.succ.succ.succ) other a := by
    intro a
    exact (domain_semantics env rho G F a).trans (domain_semantics other rr G.succ.succ.succ.succ F.succ.succ.succ.succ a).symm
  exact ⟨graph,sigma,b,root,⟨e,he,hCode,hEdge,hRoot,J,hRange,H,hFix,hSupport⟩,j,z,left,seed,hCenter,hZ,hLabel,hPair,hGraph,hGraphHS,hFixed,
    (ForcingCompletionGraph.partialUnique_congr hR hH (env (rho 6)) graph).mpr hUnique⟩


def selected {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin m)
    (rho : Fin 7 → Fin m) (I K G F top one c hi X i graph : Fin m) : Formula m :=
  let up3 : Fin m → Fin (m+3) := fun j => j.castSucc.castSucc.castSucc
  let up : Fin m → Fin (m+7) := fun j => j.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let rr : Fin 7 → Fin (m+7) := fun j => up (rho j)
  let sigma := (Fin.last m).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc
  let root := (Fin.last (m+2)).castSucc.castSucc.castSucc.castSucc
  let j := (Fin.last (m+3)).castSucc.castSucc.castSucc
  let z := (Fin.last (m+4)).castSucc.castSucc
  let left := (Fin.last (m+5)).castSucc
  let seed := Fin.last (m+6)
  .ex (.ex (.ex ((record (fun j => up3 (rho j)) (up3 I) (up3 G) (up3 X) (up3 i)
    (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))).conj
      (.ex (.ex (.ex (.ex ((Source.SetLanguage.edge root (up one) j).conj
    ((ForcingSupportingRoot.code z (up top) root).conj
    ((ForcingLabelNames.label (up (rho 6)) (up K) (up c) (up top) j (up hi) left).conj
    ((ForcingOrderedPairName.orderedPairName (up top) left sigma seed).conj
    ((ForcingPartialOrbitGraph.graph rr (up G) seed z (up graph)).conj
    ((ForcingHS.hs actionFormula rr (up G) (up (rho 6)) (up F) (up graph)).conj
    ((ForcingEquivariantMix.fixedAll rr (up G) (up graph)).conj
    ((ForcingDefaultRelation.uniqueFormula false R Hdom (fun j => up (base j)) (up (rho 6)) (up graph) (up graph) (up graph)))))))))))))))))

theorem selected_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin m)
    (rho : Fin 7 → Fin m) (I K G F top one c hi X i graph : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (selected R Hdom base rho I K G F top one c hi X i graph) ↔
      Selected R Hdom (fun j => env (base j)) (fun j => env (rho j)) (env I) (env K) (env G) (env F)
        (env top) (env one) (env c) (env hi) (env X) (env i) (env graph) := by
  simp only [selected,Selected,Formula.Realize,record_semantics (M := M),KuratowskiZF.source_edge,
    ForcingSupportingRoot.code_semantics (M := M),ForcingLabelNames.label_semantics (M := M),
    ForcingOrderedPairName.orderedPairName_semantics (M := M),ForcingPartialOrbitGraph.graph_semantics (M := M),
    ForcingHS.hs_semantics (M := M),ForcingEquivariantMix.fixedAll_semantics (M := M),
    ForcingDefaultRelation.uniqueFormula_semantics,Bool.false_eq_true,if_false,Supported,PartialUnique,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  rfl

/-- The actual source family is a full INTERNAL function graph, constructed
by the existing functional-image/function constructors because its values are
unique. No Choice, external family, rank bound or assumed function is used. -/
theorem construct_family (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K G F top one c hi X : Fin k) (indices : M.Carrier .set)
    (R : Formula (k+2)) (Hdom : Formula (k+1))
    (hEach : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i (indices) →
      ∃ graph, Selected R Hdom env (fun j => env (rho j)) (env I) (env K) (env G) (env F)
        (env top) (env one) (env c) (env hi) (env X) i graph) :
    ∃ f, FunctionOn (indices) f ∧ ∀ i graph, PureKuratowski.PairMember M i graph f ↔
      (Project.FirstOrderSemantics.reduct M).mem i (indices) ∧
        Selected R Hdom env (fun j => env (rho j)) (env I) (env K) (env G) (env F)
          (env top) (env one) (env c) (env hi) (env X) i graph := by
  let up : Fin k → Fin (k+2) := fun j => j.castSucc.castSucc
  let query := selected R Hdom up (fun j => up (rho j)) (up I) (up K) (up G) (up F) (up top)
    (up one) (up c) (up hi) (up X) (Fin.last k).castSucc (Fin.last (k+1))
  let schema := ProjectSyntax.binary query
  let penv : Env (Project.FirstOrderSemantics.reduct M) k := ⟨fun j => env j.rev,fun _ => indices⟩
  have he i graph : schema.denote penv i graph ↔
      Selected R Hdom env (fun j => env (rho j)) (env I) (env K) (env G) (env F)
        (env top) (env one) (env c) (env hi) (env X) i graph := by
    rw [ForcingMapConditions.binary_semantics hM query env (indices) i graph]
    simp only [MapRel,query,selected_semantics,up,Fin.lastCases_last,Fin.lastCases_castSucc]
  have hTotal : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i (indices) → ∃ graph, schema.denote penv i graph := by
    intro i hi
    obtain ⟨graph,hGraph⟩ := hEach i hi
    exact ⟨graph,(he i graph).mpr hGraph⟩
  have hUnique i a b (ha : schema.denote penv i a) (hb : schema.denote penv i b) : a = b :=
    selected_unique hM ((he i a).mp ha) ((he i b).mp hb)
  obtain ⟨bound,hBound⟩ := ZF.exists_functionalImage (ModelTransfer.project_models_iff.mp hM) schema penv (indices) hTotal hUnique
  obtain ⟨f,hf,hfEdges⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema penv (source := indices) (target := bound) hTotal
    (fun i _ a b ha hb => hUnique i a b ha hb) (fun i graph hi hGraph => (hBound graph).mpr ⟨i,hi,hGraph⟩)
  exact ⟨f,((ForcingSupportSize.native_mapsTo hM _ _ _).mpr hf).1,
    fun i graph => (hfEdges i graph).trans (and_congr Iff.rfl (he i graph))⟩


def Family {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (v : Fin 7 → M.Carrier .set) (I K G F top one c hi X indices f : M.Carrier .set) : Prop :=
  Index v I G X indices ∧ FunctionOn indices f ∧ ∀ i graph, PureKuratowski.PairMember M i graph f ↔
    (Project.FirstOrderSemantics.reduct M).mem i indices ∧ Selected R Hdom env v I K G F top one c hi X i graph

theorem family_laws {k : Nat} {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set}
    {v : Fin 7 → M.Carrier .set} {I K G F top one c hi X indices f : M.Carrier .set}
    (h : Family R Hdom env v I K G F top one c hi X indices f) :
    ForcingCollectedHS.FamilyHS v G (v 6) F indices f ∧
      (∀ i graph, (Project.FirstOrderSemantics.reduct M).mem i indices → PureKuratowski.PairMember M i graph f → Supported v G graph) ∧
      (∀ i graph, (Project.FirstOrderSemantics.reduct M).mem i indices → PureKuratowski.PairMember M i graph f →
        PartialUnique (R := R) (H := Hdom) (env := env) (P := v 6) graph) := by
  have hall i graph (he : PureKuratowski.PairMember M i graph f) :
      HS actionFormula v G (v 6) F graph ∧ Supported v G graph ∧ PartialUnique (R := R) (H := Hdom) (env := env) (P := v 6) graph := by
    obtain ⟨_,sigma,b,root,_hRecord,j,z,left,seed,_hCenter,_hZ,_hLabel,_hPair,_hGraph,hHS,hFixed,hUnique⟩ := (h.2.2 i graph).mp he
    exact ⟨hHS,hFixed,hUnique⟩
  exact ⟨fun i graph _hi he => (hall i graph he).1,
    fun i graph _hi he => (hall i graph he).2.1,fun i graph _hi he => (hall i graph he).2.2⟩

/-- Actual source PresentationIndex and presentationPartial family. Every
index and every function value is constructed; all three consumer laws follow
from the real graph constructor. The source ground Choice is unnecessary here. -/
theorem construct (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w G F mul top one values c lo hi X labels : Fin k)
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w)) (hK : ¬ ForcingSupportSize.Small (env K) (env w))
    (hc : ForcingSupportSize.Injection (env K) (env values) (env c)) (ht : ForcingWithTopCarrier.Empty (env top))
    (hlo : (Project.FirstOrderSemantics.reduct M).mem (env lo) (env B)) (hhi : (Project.FirstOrderSemantics.reduct M).mem (env hi) (env B))
    (hBits : env lo ≠ env hi)
    (hX : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env X))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env c) (env top) (env hi) (env labels))
    (hLabelsHS : HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) (env labels)) :
    ∃ indices f, Family (orderFormula (rho 0) mul) (domain rho G F) env (fun j => env (rho j))
      (env I) (env K) (env G) (env F) (env top) (env one) (env c) (env hi) (env X) indices f := by
  obtain ⟨indices,hIndex⟩ := construct_index hM env rho I G X hPres.2.2.2.1
  obtain ⟨f,hFunction,hEdges⟩ := construct_family hM env rho I K G F top one c hi X indices
    (orderFormula (rho 0) mul) (domain rho G F)
    (fun i hIndexMember => exists_selected hM env rho I K B w G F mul top one values c lo hi X labels
      hPres hG hF hm hw hK hc ht hlo hhi hBits hX hLabels hLabelsHS ((hIndex i).mp hIndexMember))
  exact ⟨indices,f,hIndex,hFunction,hEdges⟩


def family {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin m)
    (rho : Fin 7 → Fin m) (I K G F top one c hi X indices f : Fin m) : Formula m :=
  (index rho I G X indices).conj ((Source.SetLanguage.functionOn f indices).conj
    (.all (.all ((Source.SetLanguage.edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
      ((Formula.mem (Fin.last m).castSucc indices.castSucc.castSucc).conj
        (selected R Hdom (fun j => (base j).castSucc.castSucc) (fun j => (rho j).castSucc.castSucc)
          I.castSucc.castSucc K.castSucc.castSucc G.castSucc.castSucc F.castSucc.castSucc top.castSucc.castSucc
          one.castSucc.castSucc c.castSucc.castSucc hi.castSucc.castSucc X.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))))))))

theorem family_semantics {k m : Nat} (env : Fin m → M.Carrier .set)
    (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin m)
    (rho : Fin 7 → Fin m) (I K G F top one c hi X indices f : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (family R Hdom base rho I K G F top one c hi X indices f) ↔
      Family R Hdom (fun j => env (base j)) (fun j => env (rho j)) (env I) (env K) (env G) (env F)
        (env top) (env one) (env c) (env hi) (env X) (env indices) (env f) := by
  simp only [family,Family,Source.Formula.iff,Formula.Realize,index_semantics (M := M),
    ForcingConditionGraphs.functionOn_semantics (M := M),KuratowskiZF.source_edge,selected_semantics,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  exact and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun i => forall_congr' fun graph =>
    ⟨fun h => ⟨h.1,h.2⟩,fun h => ⟨h.mp,h.mpr⟩⟩))

/-- The constructed set/function and exactly the three original consumer
interfaces of completionGraph_surjection, with no given family or laws. -/
def construction {k : Nat} (rho : Fin 7 → Fin k) (I K G F mul top one c hi X : Fin k) : Formula k :=
  let R := orderFormula (rho 0) mul
  let Hdom := domain rho G F
  let up : Fin k → Fin (k+2) := fun j => j.castSucc.castSucc
  let rr : Fin 7 → Fin (k+2) := fun j => up (rho j)
  let indices := (Fin.last k).castSucc
  let f := Fin.last (k+1)
  .ex (.ex ((family R Hdom up rr (up I) (up K) (up G) (up F) (up top) (up one) (up c) (up hi) (up X) indices f).conj
    ((ForcingCollectedHS.familyHS rr (up G) (up (rho 6)) (up F) indices f).conj
      ((ForcingCompletionGraph.invariant rr (up G) indices f).conj
        (ForcingCompletionGraph.partialFamily R Hdom up (up (rho 6)) indices f f f)))))

def guards {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top one values c lo hi X labels : Fin k) : Formula k :=
  (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).conj
    ((ForcingLabelPermutations.carrier I G).conj
    ((ForcingNormalFilter.normal I G F).conj
    ((ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one).conj
    (((ForcingSupportSize.small K w).neg).conj
    ((Source.SetLanguage.injection c K values).conj
    ((ForcingWithTopCarrier.empty top).conj
    ((Formula.mem lo B).conj
    ((Formula.mem hi B).conj
    (((Formula.equal lo hi).neg).conj
    ((ForcingHS.hs actionFormula rho G (rho 6) F X).conj
    ((ForcingLabelSet.labelSet (rho 6) I K c top hi labels).conj
    ((ForcingHS.hs actionFormula rho G (rho 6) F labels)))))))))))))

def sentence {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top one values c lo hi X labels : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (Project.Formula.isOmega (.bound w))
    (.imp (ProjectSyntax.encode id (guards rho I K B w G F mul top one values c lo hi X labels))
      (ProjectSyntax.encode id (construction rho I K G F mul top one c hi X))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega]

theorem models {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top one values c lo hi X labels : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sentence rho I K B w G F mul top one values c lo hi X labels)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),guards,Formula.Realize,
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingNormalFilter.normal_semantics (M := M),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingSupportSize.small_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingHS.hs_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M)]
  intro hw h
  obtain ⟨hPres,hG,hF,hm,hK,hc,ht,hlo,hhi,hBits,hX,hLabels,hLabelsHS⟩ := h
  obtain ⟨indices,f,hFamily⟩ := construct hM env rho I K B w G F mul top one values c lo hi X labels
    hPres hG hF hm hw hK hc ht hlo hhi hBits hX hLabels hLabelsHS
  have hLaws := family_laws hFamily
  simp only [construction,Formula.Realize,family_semantics (M := M),ForcingCollectedHS.familyHS_semantics (M := M),
    ForcingCompletionGraph.invariant_semantics (M := M),ForcingCompletionGraph.partialFamily_semantics,
    Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨indices,f,hFamily,hLaws.1,(fun i hi graph he => hLaws.2.1 i graph hi he),hLaws.2.2⟩

/-- Original nativeZF object derivation of the actual full set-indexed
presentation family; Choice is NOT a background assumption of this theorem. -/
theorem kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I K B w G F mul top one values c lo hi X labels : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sentence rho I K B w G F mul top one values c lo hi X labels)) :=
  ModelTransfer.derives (fun _ hM => models rho I K B w G F mul top one values c lo hi X labels hM)

end PPAC.Migration.ForcingPresentationFamily
