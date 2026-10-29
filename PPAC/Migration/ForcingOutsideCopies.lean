/- Pinned ClassFibers.outsideClass_copies:508-557.
The actual condition and literal normalized label class move together, with
unchanged root restriction and exclusion at every stronger Product condition.
Consumer: classFiber_dense_lower / CodeCardinals.ordinalType_lower_count. -/
import PPAC.Migration.ForcingOutsideLocal
import PPAC.Migration.ForcingRelationClassMove

namespace PPAC.Migration.ForcingOutsideCopies
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args2 args3)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingMapConditions (MapRel)
open ForcingStabilizer (Action)
open ForcingConditionGraphs (Permutation CompositionGraph)
open ForcingSupportSize (Injection)
open ForcingCohenConditions (Condition)
open ConstructionCohenCompatibility (Entry Moved Restricted)
open ConstructionPlacementTriple (ImageAt)
open ForcingSupportingRoot (Code exists_code code_mem moved_code)
open ForcingOutsideLocal (Outside)
open ForcingRelationClassMove (Value)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Exact support transport along the supplied literal diagram composition. -/
theorem moved_supported {D pi s t d q : M.Carrier .set}
    (hcomp : CompositionGraph D pi s t)
    (hs : ForcingLocalRecordPullback.Supported D s d) (hm : Moved pi d q) :
    ForcingLocalRecordPullback.Supported D t q := by
  intro j k b he
  obtain ⟨i,hij,hi⟩ := (hm j k b).mp he
  obtain ⟨x,hx,hxi⟩ := hs i k b hi
  exact ⟨x,hx,(hcomp x j).mpr ⟨hx,i,hxi,hij⟩⟩

/-- Source restrict_permute_of_fixes, for the SAME internal restriction set. -/
theorem restrict_permute_of_fixes (hM : FirstOrder.Theory.Models M nativeZF)
    {I K C B S w J pi d q delta : M.Carrier .set}
    (hC : ForcingCohenCoordinates.Cartesian I K C) (hS : ForcingCohenCoordinates.Cartesian C B S)
    (hpi : Permutation I pi) (hd : Condition S w d) (hq : Condition S w q)
    (hfix : ForcingLabelPermutations.Fixes J pi) (hm : Moved pi d q)
    (hr : Restricted J d delta) : Restricted J q delta := by
  obtain ⟨r,hrC,hrr,_⟩ := ConstructionCohenCompatibility.exists_restrict hM hq J
  have he : r = delta := by
    apply ConstructionCohenCompatibility.entries_ext hM hC hS hrC
      (ForcingSupportingRoot.restricted_condition hM hd hr)
    intro j k b
    rw [ConstructionCohenCompatibility.restricted_entry hrr,
      ConstructionCohenCompatibility.restricted_entry hr]
    constructor
    · rintro ⟨he,hj⟩
      obtain ⟨i,hij,hi⟩ := (hm j k b).mp he
      have eq := hpi.2.1 i j j hij (hfix j hj)
      exact ⟨eq ▸ hi,hj⟩
    · rintro ⟨he,hj⟩
      exact ⟨(hm j k b).mpr ⟨j,hfix j hj,he⟩,hj⟩
  exact he ▸ hrr

/-- Pull every target extension back through the actual Product permutation.
No filter or supplied target exclusion is used. -/
theorem outside_move (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w pi a z z' sigma sigma' list : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G))
    (hF : ForcingNormalFilter.Normal I (env G) (env F)) (hpi : Permutation I pi)
    (ha : MapRel actionFormula (fun j => env (rho j)) pi a)
    (hzz : PureKuratowski.PairMember M z z' a)
    (hs : Action (env (rho 6)) a sigma sigma') (hl : Action (env (rho 6)) a list list)
    (hout : Outside (orderFormula (rho 0) mul) env (env (rho 6)) z sigma list) :
    Outside (orderFormula (rho 0) mul) env (env (rho 6)) z' sigma' list := by
  have hA := (mapRel_action _ _ _).mp ha
  have hPerm := ForcingProductFamily.action_permutation hA
  have hOrder := ForcingProductFamily.order hM (env mul) hp hpi hA
  intro q' hq' hq'z hmem
  obtain ⟨q,hq,hqq⟩ := hPerm.2.2 q' hq'
  have hqz := (orderFormula_semantics env (rho 0) mul q z).mpr
    ((hOrder q z q' z' hqq hzz).mpr
      ((orderFormula_semantics env (rho 0) mul q' z').mp hq'z))
  have hsym := ForcingSeparation.symmetry hM env rho G F mul hp hG hF hpi ha
    (Formula.mem (0 : Fin 2) 1) (args2 sigma list) (args2 sigma' list)
    (fun i => Fin.cases hs (fun j => Fin.cases hl (fun z => Fin.elim0 z) j) i) hq hqq
  exact hout q hq hqz (hsym.mpr hmem)

/-- A concrete labelClass value is already the normalized local name when its
label and E are supported in the stated local set. -/
theorem local_value (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w mu c top bit labels E j name bound J fixing : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hc : ForcingConditionGraphs.FunctionOn K c) (ht : ForcingWithTopCarrier.Empty top)
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) I K c top bit labels)
    (hBound : ForcingLabelBound.LabelBound (env (rho 6)) I K c top bit bound)
    (hFix : ForcingLabelPermutations.Fixing (env G) J fixing)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j J)
    (hEf : ForcingSupportedNames.Supported (fun i => env (rho i)) fixing E)
    (hn : Value (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun i => env (rho i))
      (env G) (env F) I K c top bit labels E j name) :
    ForcingLocalNames.LocalName (fun i => env (rho i)) (env G) (env F) bound fixing name := by
  refine ⟨⟨hn.2.1,?_⟩,?_⟩
  · obtain ⟨x,_,hClass⟩ := hn.2.2
    exact ForcingRelationClass.bounded ((ForcingLabelBound.bound_iff hM hLabels).mpr hBound) hn.2.1 hClass
  · intro pi hpi a ha
    obtain ⟨hpiG,hfixed⟩ := (hFix pi).mp hpi
    exact ForcingRelationClassMove.labelClass_move hM env rho G F mul hp hG hF hw hMu hc ht hLabels
      ((hG pi).mp hpiG) ha (hEf pi hpi a ha) (hfixed j hj) hn hn

/-- Actual labelClass values force the full source isClass formula at every condition. -/
theorem value_isClass (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w mu one c top bit labels E j name : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hc : ForcingConditionGraphs.FunctionOn K c) (ht : ForcingWithTopCarrier.Empty top)
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) I K c top bit labels)
    (hE : ForcingHS.HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) E)
    (hn : Value (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun i => env (rho i))
      (env G) (env F) I K c top bit labels E j name) :
    ∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) →
      ForcingFormula.Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
        (args3 name labels E) (env (rho 6)) p (ForcingEligibility.isClass 0 1 2) := by
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hF
  have hSmall := (ForcingSupportSize.native_small hM w mu).mpr hMu.2
  obtain ⟨hA,_⟩ := ForcingLabelSet.HS_and_fixed hM (fun i => env (rho i)) hp hG hNormal hF hw hSmall hc ht hLabels
  obtain ⟨hj,hName,x,hx,hClass⟩ := hn
  have hxHS := ForcingLabelNames.label_HS hM (fun i => env (rho i)) hp hG hNormal hF hw hSmall hc ht hj hx
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm hp.2.2.2.2.1 hp.2.2.2.1 hp.2.2.2.2.2
  intro p hcond
  apply (ForcingRelationClass.forces_isClass hM env rho G F mul hp hG hNormal hpre hcond
    (args3 name labels E) 0 1 2 hName hA hE).mpr
  intro q hq _
  have htW := (hp.2.2.2.2.2 top).mpr (Or.inl ht)
  have hqt := (orderFormula_semantics env (rho 0) mul q top).mpr (Or.inl ht)
  have hmem := ForcingAtomicBasic.mem_of_edge_eq hM hpre htW hqt
    ((ForcingLabelSet.edge_labelSet hM hLabels x top).mpr ⟨rfl,j,hj,hx⟩)
    (ForcingAtomicBasic.eq_refl hM hpre x q hq)
  exact ⟨q,hq,hpre.1 q hq,x,name,hxHS,hName,hClass,hmem,ForcingAtomicBasic.eq_refl hM hpre name q hq⟩

/-- One actual copy over the common root. The target name and Cohen condition
are constructed; only the source outside witness is an input. -/
theorem copy (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    {I K B w mu one c top bit labels E j sigma bound J H A HA list s t pi d delta z : M.Carrier .set}
    (hp : Presentation (env (rho 0)) I K B w (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier I (env G)) (hF : ForcingSupportFilter.Filter I (env G) mu (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hc : ForcingConditionGraphs.FunctionOn K c) (htop : ForcingWithTopCarrier.Empty top)
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) I K c top bit labels)
    (hBound : ForcingLabelBound.LabelBound (env (rho 6)) I K c top bit bound)
    (hE : ForcingHS.HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) E)
    (hRoot : ForcingLabelPermutations.Fixing (env G) J H)
    (hEf : ForcingSupportedNames.Supported (fun i => env (rho i)) H E)
    (hList : ForcingOrdinalFixed.Fixed (fun i => env (rho i)) (env G) (env F) H list)
    (hRange : ForcingSupportedNames.Range (env (rho 0)) t A)
    (hTarget : ForcingLabelPermutations.Fixing (env G) A HA)
    (hJA : ForcingPowerName.Subset J A)
    (hs : Injection (env (rho 0)) I s) (ht : Injection (env (rho 0)) I t)
    (hpi : Permutation I pi) (hComp : CompositionGraph (env (rho 0)) pi s t)
    (hFix : ForcingLabelPermutations.Fixes J pi)
    (hd : Condition (env (rho 2)) w d)
    (hSupp : ForcingLocalRecordPullback.Supported (env (rho 0)) s d)
    (hRestr : Restricted J d delta) (hz : Code z d s)
    (hj : ImageAt s (env (rho 0)) j)
    (hSigma : Value (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun i => env (rho i))
      (env G) (env F) I K c top bit labels E j sigma)
    (hOut : Outside (orderFormula (rho 0) mul) env (env (rho 6)) z sigma list) :
    ∃ d' z' j' name,
      ConstructionDescentPlacement.ActualMoved (env (rho 1)) (env (rho 2)) w pi d d' ∧
      ForcingLocalRecordPullback.Supported (env (rho 0)) t d' ∧ Restricted J d' delta ∧ Code z' d' t ∧
      (Project.FirstOrderSemantics.reduct M).mem j' A ∧ PureKuratowski.PairMember M j j' pi ∧
      Value (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun i => env (rho i))
        (env G) (env F) I K c top bit labels E j' name ∧
      ForcingLocalNames.LocalName (fun i => env (rho i)) (env G) (env F) bound HA name ∧
      (∀ p, (Project.FirstOrderSemantics.reduct M).mem p (env (rho 6)) →
        ForcingFormula.Force (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env
          (args3 name labels E) (env (rho 6)) p (ForcingEligibility.isClass 0 1 2)) ∧
      Outside (orderFormula (rho 0) mul) env (env (rho 6)) z' name list := by
  obtain ⟨f,g,d',hf,hfg,hg,hgg,hd',hImage,hMove⟩ :=
    ConstructionCohenCompatibility.exists_moved hM hp.1 hp.2.1 hpi hd
  have hMoved : ConstructionDescentPlacement.ActualMoved (env (rho 1)) (env (rho 2)) w pi d d' :=
    ⟨f,g,hf,hfg,hg,hgg,hd',hImage,hMove⟩
  have hpiH := (hRoot pi).mpr ⟨(hG pi).mpr hpi,hFix⟩
  obtain ⟨j',hjj,_⟩ := hpi.1.1.2 j hSigma.1
  have hjA : (Project.FirstOrderSemantics.reduct M).mem j' A := by
    obtain ⟨x,hx,hxj⟩ := hj
    exact (hRange j').mpr ⟨x,hx,(hComp x j').mpr ⟨hx,j,hxj,hjj⟩⟩
  obtain ⟨name,hName⟩ := ForcingRelationClassMove.value_exists hM env rho G F mul hp hG hF hw hMu hc htop hLabels hE
    (hpi.1.2 j j' hjj)
  have hLocal := local_value hM env rho G F mul hp hG hF hw hMu hc htop hLabels hBound hTarget hjA
    (ForcingSupportedNames.supported_mono hRoot hTarget hJA hEf) hName
  obtain ⟨action,hAction⟩ := ForcingProductFamily.exists_action hM hp hpi
  have hActionRel := (mapRel_action (fun i => env (rho i)) pi action).mpr hAction
  have hNameMove := ForcingRelationClassMove.labelClass_move hM env rho G F mul hp hG hF hw hMu hc htop hLabels
    hpi hActionRel (hEf pi hpiH action hActionRel) hjj hSigma hName
  obtain ⟨z',hz'⟩ := exists_code hM d' t
  refine ⟨d',z',j',name,hMoved,moved_supported hComp hSupp hMove,
    restrict_permute_of_fixes hM hp.1 hp.2.1 hpi hd hd' hFix hMove hRestr,hz',hjA,hjj,hName,hLocal,
    value_isClass hM env rho G F mul hp hG hF hw hMu hm hc htop hLabels hE hName,?_⟩
  exact outside_move hM env rho G F mul hp hG (ForcingNormalFilter.is_normal hM hw hMu hG hF) hpi hActionRel
    (moved_code hM hp hAction hd hs ht hMoved hComp hz hz') hNameMove (hList.2 pi hpiH action hActionRel) hOut

/-- The source pair of a Cohen condition and a normalized local name.
Its support, root restriction and all-condition assertions are internal. -/
def Copy {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (v : Fin 7 → M.Carrier .set) (G F w bound labels E J delta list target record : M.Carrier .set) : Prop :=
  ∃ d name A HA z, PureKuratowski.Code M record d name ∧ Condition (v 2) w d ∧
    ForcingLocalRecordPullback.Supported (v 0) target d ∧ Restricted J d delta ∧
    ForcingSupportedNames.Range (v 0) target A ∧ ForcingLabelPermutations.Fixing G A HA ∧
    ForcingLocalNames.LocalName v G F bound HA name ∧ Code z d target ∧
    (∀ p, (Project.FirstOrderSemantics.reduct M).mem p (v 6) →
      ForcingFormula.Force R Hdom env (args3 name labels E) (v 6) p (ForcingEligibility.isClass 0 1 2)) ∧
    Outside R env (v 6) z name list

def copyRecord {k n : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin n)
    (rho : Fin 7 → Fin n) (G F w bound labels E J delta list target record : Fin n) : Project.Formula 1 n :=
  let up : Fin n → Fin (n+5) := fun j => j.succ.succ.succ.succ.succ
  .existsE (.existsE (.existsE (.existsE (.existsE (
    .conj (ProjectSyntax.encode id (PairSyntax.ordered (up record) 4 3)) (
    .conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (up (rho 2)) (up w) 4)) (
    .conj (ForcingLocalRecordPullback.supported (up (rho 0)) (up target) 4) (
    .conj (ConstructionCohenCompatibility.restricted (up J) 4 (up delta)) (
    .conj (ProjectSyntax.encode id (ForcingSupportedNames.range (up (rho 0)) (up target) 2)) (
    .conj (ProjectSyntax.encode id (ForcingLabelPermutations.fixing (up G) 2 1)) (
    .conj (ProjectSyntax.encode id (ForcingLocalNames.localName (fun j => up (rho j)) (up G) (up F) (up bound) 1 3)) (
    .conj (ProjectSyntax.encode id (ForcingSupportingRoot.code 0 4 (up target))) (
    .conj (.forallE (.imp (.mem (.bound 0) (.bound (up (rho 6)).succ))
      (ProjectSyntax.encode id (ForcingFormula.formula R Hdom (fun j => (up (base j)).succ)
        (args3 4 (up labels).succ (up E).succ) (up (rho 6)).succ 0 (ForcingEligibility.isClass 0 1 2)))))
      (ProjectSyntax.encode id (ForcingOutsideLocal.outside R (fun j => up (base j)) (up (rho 6)) 0 3 (up list)))
    )))))))))))))

theorem copyRecord_freeClosed {k n : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin n)
    (rho : Fin 7 → Fin n) (G F w bound labels E J delta list target record : Fin n) :
    (copyRecord R Hdom base rho G F w bound labels E J delta list target record).FreeClosed := by
  simp -implicitDefEqProofs [copyRecord,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ForcingLocalRecordPullback.supported_freeClosed,ConstructionCohenCompatibility.restricted_freeClosed]

theorem copyRecord_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin n) (rho : Fin 7 → Fin n) (G F w bound labels E J delta list target record : Fin n) :
    Project.Formula.satisfies env (copyRecord R Hdom base rho G F w bound labels E J delta list target record) ↔
      Copy R Hdom (fun j => env.bound (base j)) (fun j => env.bound (rho j))
        (env.bound G) (env.bound F) (env.bound w) (env.bound bound) (env.bound labels) (env.bound E)
        (env.bound J) (env.bound delta) (env.bound list) (env.bound target) (env.bound record) := by
  simp only [copyRecord,Copy,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_code,ForcingCohenConditions.condition_semantics (M := M),
    ForcingLocalRecordPullback.supported_semantics hM,ConstructionCohenCompatibility.restricted_semantics hM,
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingLocalNames.localName_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M),
    ForcingFormula.formula_semantics (M := M),ForcingOutsideLocal.outside_semantics (M := M)]
  rfl

def Family {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (v : Fin 7 → M.Carrier .set) (G F w bound labels E J delta list indices targets family : M.Carrier .set) : Prop :=
  ForcingConditionGraphs.FunctionOn indices family ∧ ∀ i record,
    PureKuratowski.PairMember M i record family → ∃ t, PureKuratowski.PairMember M i t targets ∧
      Copy R Hdom env v G F w bound labels E J delta list t record

def family {k n : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin n)
    (rho : Fin 7 → Fin n) (G F w bound labels E J delta list indices targets output : Fin n) : Project.Formula 1 n :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn output indices))
    (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge output.succ.succ 1 0))
      (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge targets.succ.succ.succ 2 0))
        (copyRecord R Hdom (fun j => (base j).succ.succ.succ) (fun j => (rho j).succ.succ.succ)
          G.succ.succ.succ F.succ.succ.succ w.succ.succ.succ bound.succ.succ.succ
          labels.succ.succ.succ E.succ.succ.succ J.succ.succ.succ delta.succ.succ.succ list.succ.succ.succ 0 1))))))

theorem family_freeClosed {k n : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin n)
    (rho : Fin 7 → Fin n) (G F w bound labels E J delta list indices targets output : Fin n) :
    (family R Hdom base rho G F w bound labels E J delta list indices targets output).FreeClosed := by
  simp -implicitDefEqProofs [family,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,copyRecord_freeClosed]

theorem family_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin n) (rho : Fin 7 → Fin n) (G F w bound labels E J delta list indices targets output : Fin n) :
    Project.Formula.satisfies env (family R Hdom base rho G F w bound labels E J delta list indices targets output) ↔
      Family R Hdom (fun j => env.bound (base j)) (fun j => env.bound (rho j))
        (env.bound G) (env.bound F) (env.bound w) (env.bound bound) (env.bound labels) (env.bound E)
        (env.bound J) (env.bound delta) (env.bound list) (env.bound indices) (env.bound targets) (env.bound output) := by
  simp only [family,Family,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingConditionGraphs.functionOn_semantics (M := M),copyRecord_semantics hM]
  rfl

/-- Source choose, on all members of the actual internal index set. The
codomain is the already available product of conditions and bounded names. -/
theorem construct (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul I K B w mu one c top bit labels E j sigma bound J H list s p pos d delta z indices : Fin k) (targets : M.Carrier .set)
    (hp : Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hLarge : ¬ ForcingSupportSize.Small (env I) (env mu)) (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hc : ForcingConditionGraphs.FunctionOn (env K) (env c)) (htop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env c) (env top) (env bit) (env labels))
    (hBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env c) (env top) (env bit) (env bound))
    (hE : ForcingHS.HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) (env E))
    (hRootRange : ForcingSupportedNames.Range (env (rho 0)) (env p) (env J))
    (hRoot : ForcingLabelPermutations.Fixing (env G) (env J) (env H))
    (hEf : ForcingSupportedNames.Supported (fun i => env (rho i)) (env H) (env E))
    (hList : ForcingOrdinalFixed.Fixed (fun i => env (rho i)) (env G) (env F) (env H) (env list))
    (hs : Injection (env (rho 0)) (env I) (env s))
    (hpos : (Project.FirstOrderSemantics.reduct M).mem (env pos) (env (rho 0)))
    (hSub : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env s) (env pos) (env p))
    (hd : Condition (env (rho 2)) (env w) (env d))
    (hSupp : ForcingLocalRecordPullback.Supported (env (rho 0)) (env s) (env d))
    (hRestr : Restricted (env J) (env d) (env delta)) (hz : Code (env z) (env d) (env s))
    (hj : ImageAt (env s) (env (rho 0)) (env j))
    (hSigma : Value (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun i => env (rho i))
      (env G) (env F) (env I) (env K) (env c) (env top) (env bit) (env labels) (env E) (env j) (env sigma))
    (hOut : Outside (orderFormula (rho 0) mul) env (env (rho 6)) (env z) (env sigma) (env list))
    (hTargets : ForcingConditionGraphs.FunctionOn (env indices) targets)
    (hRoots : ∀ i t, PureKuratowski.PairMember M i t targets →
      Injection (env (rho 0)) (env I) t ∧ ForcingDiagramOrder.Sub (env (rho 0)) (env mul) t (env pos) (env p)) :
    ∃ output, Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun i => env (rho i))
      (env G) (env F) (env w) (env bound) (env labels) (env E) (env J) (env delta) (env list) (env indices) targets output := by
  obtain ⟨names,hNames⟩ := ForcingPowerName.exists_candidates hM (fun i => env (rho i)) (env G) (env F) (env bound)
  obtain ⟨values,hValues⟩ := ForcingCohenCoordinates.exists_cartesian hM (env (rho 3)) names
  let R := orderFormula (rho 0) mul
  let Hdom := ForcingPairUnion.domain rho G F
  let schema : Project.BinarySchema (k+1) := {
    body := .existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin (k+1)).succ.succ.succ 2 0))
      (copyRecord R Hdom (fun j => j.succ.succ.succ.succ) (fun j => (rho j).succ.succ.succ.succ)
        G.succ.succ.succ.succ F.succ.succ.succ.succ w.succ.succ.succ.succ bound.succ.succ.succ.succ labels.succ.succ.succ.succ
        E.succ.succ.succ.succ J.succ.succ.succ.succ delta.succ.succ.succ.succ list.succ.succ.succ.succ 0 1))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,copyRecord_freeClosed] }
  let penv : Env (Project.FirstOrderSemantics.reduct M) (k+1) := ⟨Fin.cases targets env,fun _ => env w⟩
  have he i record : schema.denote penv i record ↔ ∃ t, PureKuratowski.PairMember M i t targets ∧
      Copy R Hdom env (fun j => env (rho j)) (env G) (env F) (env w) (env bound) (env labels) (env E)
        (env J) (env delta) (env list) t record := by
    simp only [schema,Project.BinarySchema.denote,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
      GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,copyRecord_semantics hM]
    rfl
  obtain ⟨output,hOutput,hSelect⟩ := ExistingSmallUnion.uniformize_formula_l (KuratowskiZF.interpretation hM)
    (ConstructionDirectedCardinality.models_zfc hM hChoice) schema penv (X := env indices) (Y := values) (by
      intro i hi
      obtain ⟨t,hit,_⟩ := hTargets.2 i hi
      obtain ⟨ht,hSubT⟩ := hRoots i t hit
      obtain ⟨pi,hpi,hComp,hFix⟩ := ConstructionDiagramPlacements.permutation_over_root hM hChoice
        hw hMu hLarge hSmall hs ht (hm.2.1 (env pos) hpos) hSub hSubT
      obtain ⟨A,hA,_,_⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 ht hSmall
      obtain ⟨HA,hHA⟩ := ForcingLabelPermutations.exists_fixing hM (env G) A
      have hJA : ForcingPowerName.Subset (env J) A := fun x hx => (hA x).mpr
        (ConstructionDescentPlacement.range_antitone ⟨env pos,hpos,hSubT⟩ ((hRootRange x).mp hx))
      obtain ⟨d',z',j',name,hMoved,hSupport,hRestr',hCode,_,_,_,hLocal,hClass,hOutside⟩ :=
        copy hM env rho G F mul hp hG hF hw hMu hm hc htop hLabels hBound hE hRoot hEf hList
          hA hHA hJA hs ht hpi hComp (fun x hx => hFix x ((hRootRange x).mp hx)) hd hSupp hRestr hz hj hSigma hOut
      have hd' := (ConstructionDescentPlacement.actual_moved_condition hMoved).1
      obtain ⟨record,hRecord⟩ := KuratowskiZF.exists_code hM d' name
      exact ⟨record,(hValues record).mpr ⟨d',(hp.2.2.1 d').mpr hd',name,(hNames name).mpr hLocal.1,hRecord⟩,
        (he i record).mpr ⟨t,hit,d',name,A,HA,z',hRecord,hd',hSupport,hRestr',hA,hHA,hLocal,hCode,hClass,hOutside⟩⟩)
  exact ⟨output,((ForcingSupportSize.native_mapsTo hM _ _ _).mpr hOutput).1,
    fun i record hir => (he i record).mp (hSelect i record hir)⟩

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (G F mul I K B w mu one c top bit labels E j sigma bound J H list s p pos d delta z indices targets : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (.neg (ProjectSyntax.encode id (ForcingSupportSize.small I mu)))
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn c K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K c top bit labels))
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K c top bit bound))
    (.imp (ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F E))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) p J))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G J H))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho H E))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixed rho G F H list))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection s (rho 0) I))
    (.imp (.mem (.bound pos) (.bound (rho 0)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul s pos p))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d))
    (.imp (ForcingLocalRecordPullback.supported (rho 0) s d)
    (.imp (ConstructionCohenCompatibility.restricted J d delta)
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z d s))
    (.imp (ConstructionPlacementTriple.imageAt s (rho 0) j)
    (.imp (ProjectSyntax.encode id (ForcingRelationClassMove.value (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F I K c top bit labels E j sigma))
    (.imp (ProjectSyntax.encode id (ForcingOutsideLocal.outside (orderFormula (rho 0) mul) id (rho 6) z sigma list))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn targets indices))
    (.imp (.forallE (.forallE (.imp
      (ProjectSyntax.encode id (Source.SetLanguage.edge targets.succ.succ 1 0))
      (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection 0 (rho 0).succ.succ I.succ.succ))
        (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0).succ.succ mul.succ.succ 0 pos.succ.succ p.succ.succ))))))
      (.existsE (family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) Fin.succ
      (fun j => (rho j).succ) G.succ F.succ w.succ bound.succ labels.succ E.succ J.succ delta.succ list.succ indices.succ targets.succ 0)))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isInfiniteCardinal,ForcingLocalRecordPullback.supported_freeClosed,
      ConstructionCohenCompatibility.restricted_freeClosed,ConstructionPlacementTriple.imageAt_freeClosed,family_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k)
    (G F mul I K B w mu one c top bit labels E j sigma bound J H list s p pos d delta z indices targets : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho G F mul I K B w mu one c top bit labels E j sigma bound J H list s p pos d delta z indices targets)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingSupportSize.small_semantics (M := M),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),ForcingHS.hs_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ForcingOrdinalFixed.fixed_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    ForcingCohenConditions.condition_semantics (M := M),ForcingLocalRecordPullback.supported_semantics hM,
    ConstructionCohenCompatibility.restricted_semantics hM,ForcingSupportingRoot.code_semantics (M := M),
    ConstructionPlacementTriple.imageAt_semantics hM,ForcingRelationClassMove.value_semantics (M := M),
    ForcingOutsideLocal.outside_semantics (M := M),KuratowskiZF.source_edge]
  intro hp hG hF hw hMu hLarge hSmall hm hc htop hLabels hBound hE hRootRange hRoot hEf hList hs hpos hSub hd hSupp hRestr hz hj hSigma hOut hTargets hRoots
  simp only [Project.Formula.satisfies_exists_iff,family_semantics hM]
  exact construct hM hChoice env rho G F mul I K B w mu one c top bit labels E j sigma bound J H list s p pos d delta z indices (env targets)
    hp hG hF hw hMu hLarge hSmall hm hc htop hLabels hBound hE hRootRange hRoot hEf hList hs hpos hSub hd hSupp hRestr hz hj hSigma hOut hTargets hRoots

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (G F mul I K B w mu one c top bit labels E j sigma bound J H list s p pos d delta z indices targets : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (constructionSentence rho G F mul I K B w mu one c top bit labels E j sigma bound J H list s p pos d delta z indices targets))) := by
  apply ModelTransfer.derives
  intro N hN
  have hL := ConstructibleSource.model_zf hN
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hN)
  let inhabitant := Classical.choice ((ConstructibleSource.model hN).nonempty .set)
  let env : Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hN)) 0 := ⟨Fin.elim0,fun _ => inhabitant⟩
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hN
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hL) _).mp
    (construction_models rho G F mul I K B w mu one c top bit labels E j sigma bound J H list s p pos d delta z indices targets hL hChoice)

/-- Literal source family i ↦ r.sub(m i), together with its common root. -/
def Targets (D I mul r pos p indices multipliers output : M.Carrier .set) : Prop :=
  ForcingConditionGraphs.FunctionOn indices output ∧ ∀ i t, PureKuratowski.PairMember M i t output →
    Injection D I t ∧ ForcingDiagramOrder.Sub D mul t pos p ∧
      ∃ m, PureKuratowski.PairMember M i m multipliers ∧ ForcingDiagramOrder.Sub D mul r m t

def targets {n : Nat} (D I mul r pos p indices multipliers output : Fin n) : Project.Formula 1 n :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn output indices))
    (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge output.succ.succ 1 0))
      (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection 0 D.succ.succ I.succ.succ))
      (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.sub D.succ.succ mul.succ.succ 0 pos.succ.succ p.succ.succ))
      (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge multipliers.succ.succ.succ 2 0))
        (ProjectSyntax.encode id (ForcingDiagramOrder.sub D.succ.succ.succ mul.succ.succ.succ r.succ.succ.succ 0 1)))))))))

theorem targets_freeClosed {n : Nat} (D I mul r pos p indices multipliers output : Fin n) :
    (targets D I mul r pos p indices multipliers output).FreeClosed := by
  simp -implicitDefEqProofs [targets,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem targets_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (D I mul r pos p indices multipliers output : Fin n) :
    Project.Formula.satisfies env (targets D I mul r pos p indices multipliers output) ↔
      Targets (env.bound D) (env.bound I) (env.bound mul) (env.bound r) (env.bound pos) (env.bound p)
        (env.bound indices) (env.bound multipliers) (env.bound output) := by
  simp only [targets,Targets,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.functionOn_semantics (M := M),KuratowskiZF.source_edge,
    ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M)]
  rfl

theorem construct_targets_at (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (D I mul one r p pos product indices Y : Fin k)
    (multipliers : M.Carrier .set)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env D) (env mul) (env one))
    (hr : Injection (env D) (env I) (env r)) (hp : Injection (env D) (env I) (env p))
    (hpos : (Project.FirstOrderSemantics.reduct M).mem (env pos) (env D))
    (hSub : ForcingDiagramOrder.Sub (env D) (env mul) (env r) (env product) (env p))
    (hMuls : ForcingSupportSize.MapsTo (env indices) (env D) multipliers)
    (hProducts : ∀ i m, PureKuratowski.PairMember M i m multipliers →
      ForcingDiagramOrder.Product (env mul) m (env pos) (env product))
    (hY : ForcingDiagramCarrier.Carrier (env D) (env I) (env Y)) :
    ∃ output, Targets (env D) (env I) (env mul) (env r) (env pos) (env p) (env indices) multipliers output := by
  let schema : Project.BinarySchema (k+1) := {
    body := .conj (.mem (.bound 0) (.bound Y.succ.succ.succ))
      (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 3 2 0))
        (ProjectSyntax.encode id (ForcingDiagramOrder.sub D.succ.succ.succ.succ mul.succ.succ.succ.succ r.succ.succ.succ.succ 0 1))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed] }
  let penv : Env (Project.FirstOrderSemantics.reduct M) (k+1) := ⟨Fin.cases multipliers env,fun _ => env r⟩
  have he i t : schema.denote penv i t ↔ (Project.FirstOrderSemantics.reduct M).mem t (env Y) ∧
      ∃ m, PureKuratowski.PairMember M i m multipliers ∧ ForcingDiagramOrder.Sub (env D) (env mul) (env r) m t := by
    simp only [schema,Project.BinarySchema.denote,Project.Formula.satisfies_conj_iff,
      Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_exists_iff,Project.Term.eval_bound,
      GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
      ForcingDiagramOrder.sub_semantics (M := M)]
    rfl
  obtain ⟨output,hOutput,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) schema penv
    (source := env indices) (target := env Y) (by
      intro i hi
      obtain ⟨m,him,_⟩ := hMuls.1.2 i hi
      obtain ⟨t,ht,hst⟩ := ForcingDiagramOrder.exists_sub hM (hm.2.1 m (hMuls.2 i m him)) hr
      exact ⟨t,(he i t).mpr ⟨(hY t).mpr ht,m,him,hst⟩⟩) (by
      intro i _ t u ht hu
      obtain ⟨htY,m,him,hmt⟩ := (he i t).mp ht
      obtain ⟨huY,n,hin,hnu⟩ := (he i u).mp hu
      have eq := ForcingConditionGraphs.function_unique hMuls.1 him hin
      subst n
      exact ForcingDiagramPoset.injection_ext hM ((hY t).mp htY) ((hY u).mp huY)
        (fun x z => (hmt x z).trans (hnu x z).symm))
    (fun i t _ ht => ((he i t).mp ht).1)
  refine ⟨output,((ForcingSupportSize.native_mapsTo hM _ _ _).mpr hOutput).1,?_⟩
  intro i t hit
  obtain ⟨htY,m,him,hmt⟩ := (he i t).mp ((hEdge i t).mp hit).2
  have ht := (hY t).mp htY
  obtain ⟨v,hv,hsv⟩ := ForcingDiagramOrder.exists_sub hM (hm.2.1 (env pos) hpos) ht
  have hrv := ForcingDiagramPoset.sub_sub hm (hMuls.2 i m him) hpos (hProducts i m him) hmt hsv
  have eq := ForcingDiagramPoset.injection_ext hM hv hp (fun x z => (hrv x z).trans (hSub x z).symm)
  exact ⟨ht,eq ▸ hsv,m,him,hmt⟩

theorem construct_targets (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (D I mul one r p pos product indices multipliers Y : Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env D) (env mul) (env one))
    (hr : Injection (env D) (env I) (env r)) (hp : Injection (env D) (env I) (env p))
    (hpos : (Project.FirstOrderSemantics.reduct M).mem (env pos) (env D))
    (hSub : ForcingDiagramOrder.Sub (env D) (env mul) (env r) (env product) (env p))
    (hMuls : ForcingSupportSize.MapsTo (env indices) (env D) (env multipliers))
    (hProducts : ∀ i m, PureKuratowski.PairMember M i m (env multipliers) →
      ForcingDiagramOrder.Product (env mul) m (env pos) (env product))
    (hY : ForcingDiagramCarrier.Carrier (env D) (env I) (env Y)) :
    ∃ output, Targets (env D) (env I) (env mul) (env r) (env pos) (env p) (env indices) (env multipliers) output := by
  exact construct_targets_at hM env D I mul one r p pos product indices Y (env multipliers) hm hr hp hpos hSub hMuls hProducts hY

theorem source_family_at (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul I K B w mu one c top bit labels E j sigma bound J H list s p pos d delta z indices r product : Fin k)
    (multipliers : M.Carrier .set)
    (hp : Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hLarge : ¬ ForcingSupportSize.Small (env I) (env mu)) (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hc : ForcingConditionGraphs.FunctionOn (env K) (env c)) (htop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env c) (env top) (env bit) (env labels))
    (hBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env c) (env top) (env bit) (env bound))
    (hE : ForcingHS.HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) (env E))
    (hRootRange : ForcingSupportedNames.Range (env (rho 0)) (env p) (env J))
    (hRoot : ForcingLabelPermutations.Fixing (env G) (env J) (env H))
    (hEf : ForcingSupportedNames.Supported (fun i => env (rho i)) (env H) (env E))
    (hList : ForcingOrdinalFixed.Fixed (fun i => env (rho i)) (env G) (env F) (env H) (env list))
    (hs : Injection (env (rho 0)) (env I) (env s))
    (hpos : (Project.FirstOrderSemantics.reduct M).mem (env pos) (env (rho 0)))
    (hSub : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env s) (env pos) (env p))
    (hd : Condition (env (rho 2)) (env w) (env d))
    (hSupp : ForcingLocalRecordPullback.Supported (env (rho 0)) (env s) (env d))
    (hRestr : Restricted (env J) (env d) (env delta)) (hz : Code (env z) (env d) (env s))
    (hj : ImageAt (env s) (env (rho 0)) (env j))
    (hSigma : Value (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun i => env (rho i))
      (env G) (env F) (env I) (env K) (env c) (env top) (env bit) (env labels) (env E) (env j) (env sigma))
    (hOut : Outside (orderFormula (rho 0) mul) env (env (rho 6)) (env z) (env sigma) (env list))
    (hr : Injection (env (rho 0)) (env I) (env r)) (hpRoot : Injection (env (rho 0)) (env I) (env p))
    (hSubR : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env product) (env p))
    (hMuls : ForcingSupportSize.MapsTo (env indices) (env (rho 0)) multipliers)
    (hProducts : ∀ i m, PureKuratowski.PairMember M i m multipliers →
      ForcingDiagramOrder.Product (env mul) m (env pos) (env product)) :
    ∃ ts output, Targets (env (rho 0)) (env I) (env mul) (env r) (env pos) (env p) (env indices) multipliers ts ∧
      Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun i => env (rho i))
        (env G) (env F) (env w) (env bound) (env labels) (env E) (env J) (env delta) (env list) (env indices) ts output := by
  obtain ⟨ts,hTs⟩ := construct_targets_at hM env (rho 0) I mul one r p pos product indices (rho 4) multipliers hm hr hpRoot hpos hSubR hMuls hProducts hp.2.2.2.1
  obtain ⟨output,hOutput⟩ := construct hM hChoice env rho G F mul I K B w mu one c top bit labels E j sigma bound J H list s p pos d delta z indices ts
    hp hG hF hw hMu hLarge hSmall hm hc htop hLabels hBound hE hRootRange hRoot hEf hList hs hpos hSub hd hSupp hRestr hz hj hSigma hOut hTs.1
    (fun i t hit => ⟨(hTs.2 i t hit).1,(hTs.2 i t hit).2.1⟩)
  exact ⟨ts,output,hTs,hOutput⟩

theorem source_construct (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul I K B w mu one c top bit labels E j sigma bound J H list s p pos d delta z indices r product multipliers : Fin k)
    (hp : Presentation (env (rho 0)) (env I) (env K) (env B) (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G)) (hF : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hLarge : ¬ ForcingSupportSize.Small (env I) (env mu)) (hSmall : ForcingSupportSize.Small (env (rho 0)) (env mu))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hc : ForcingConditionGraphs.FunctionOn (env K) (env c)) (htop : ForcingWithTopCarrier.Empty (env top))
    (hLabels : ForcingLabelSet.LabelSet (env (rho 6)) (env I) (env K) (env c) (env top) (env bit) (env labels))
    (hBound : ForcingLabelBound.LabelBound (env (rho 6)) (env I) (env K) (env c) (env top) (env bit) (env bound))
    (hE : ForcingHS.HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) (env E))
    (hRootRange : ForcingSupportedNames.Range (env (rho 0)) (env p) (env J))
    (hRoot : ForcingLabelPermutations.Fixing (env G) (env J) (env H))
    (hEf : ForcingSupportedNames.Supported (fun i => env (rho i)) (env H) (env E))
    (hList : ForcingOrdinalFixed.Fixed (fun i => env (rho i)) (env G) (env F) (env H) (env list))
    (hs : Injection (env (rho 0)) (env I) (env s))
    (hpos : (Project.FirstOrderSemantics.reduct M).mem (env pos) (env (rho 0)))
    (hSub : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env s) (env pos) (env p))
    (hd : Condition (env (rho 2)) (env w) (env d))
    (hSupp : ForcingLocalRecordPullback.Supported (env (rho 0)) (env s) (env d))
    (hRestr : Restricted (env J) (env d) (env delta)) (hz : Code (env z) (env d) (env s))
    (hj : ImageAt (env s) (env (rho 0)) (env j))
    (hSigma : Value (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun i => env (rho i))
      (env G) (env F) (env I) (env K) (env c) (env top) (env bit) (env labels) (env E) (env j) (env sigma))
    (hOut : Outside (orderFormula (rho 0) mul) env (env (rho 6)) (env z) (env sigma) (env list))
    (hr : Injection (env (rho 0)) (env I) (env r)) (hpRoot : Injection (env (rho 0)) (env I) (env p))
    (hSubR : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env r) (env product) (env p))
    (hMuls : ForcingSupportSize.MapsTo (env indices) (env (rho 0)) (env multipliers))
    (hProducts : ∀ i m, PureKuratowski.PairMember M i m (env multipliers) →
      ForcingDiagramOrder.Product (env mul) m (env pos) (env product)) :
    ∃ ts output, Targets (env (rho 0)) (env I) (env mul) (env r) (env pos) (env p) (env indices) (env multipliers) ts ∧
      Family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env (fun i => env (rho i))
        (env G) (env F) (env w) (env bound) (env labels) (env E) (env J) (env delta) (env list) (env indices) ts output := by
  exact source_family_at hM hChoice env rho G F mul I K B w mu one c top bit labels E j sigma bound J H list s p pos d delta z indices r product (env multipliers) hp hG hF hw hMu hLarge hSmall hm hc htop hLabels hBound hE hRootRange hRoot hEf hList hs hpos hSub hd hSupp hRestr hz hj hSigma hOut hr hpRoot hSubR hMuls hProducts

def sourceSentence {k : Nat} (rho : Fin 7 → Fin k)
    (G F mul I K B w mu one c top bit labels E j sigma bound J H list s p pos d delta z indices r product multipliers : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
    (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
    (.imp (.neg (ProjectSyntax.encode id (ForcingSupportSize.small I mu)))
    (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn c K))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty top))
    (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K c top bit labels))
    (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K c top bit bound))
    (.imp (ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F E))
    (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) p J))
    (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G J H))
    (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho H E))
    (.imp (ProjectSyntax.encode id (ForcingOrdinalFixed.fixed rho G F H list))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection s (rho 0) I))
    (.imp (.mem (.bound pos) (.bound (rho 0)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul s pos p))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d))
    (.imp (ForcingLocalRecordPullback.supported (rho 0) s d)
    (.imp (ConstructionCohenCompatibility.restricted J d delta)
    (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z d s))
    (.imp (ConstructionPlacementTriple.imageAt s (rho 0) j)
    (.imp (ProjectSyntax.encode id (ForcingRelationClassMove.value (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F I K c top bit labels E j sigma))
    (.imp (ProjectSyntax.encode id (ForcingOutsideLocal.outside (orderFormula (rho 0) mul) id (rho 6) z sigma list))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection r (rho 0) I))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection p (rho 0) I))
    (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul r product p))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo multipliers indices (rho 0)))
    (.imp (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge multipliers.succ.succ 1 0))
      (ProjectSyntax.encode id (ForcingDiagramOrder.product mul.succ.succ 0 pos.succ.succ product.succ.succ)))))
      (.existsE (.existsE (.conj
      (targets (rho 0).succ.succ I.succ.succ mul.succ.succ r.succ.succ pos.succ.succ p.succ.succ indices.succ.succ multipliers.succ.succ 1)
      (family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) (fun j => j.succ.succ)
        (fun j => (rho j).succ.succ) G.succ.succ F.succ.succ w.succ.succ bound.succ.succ
        labels.succ.succ E.succ.succ J.succ.succ delta.succ.succ list.succ.succ indices.succ.succ 1 0))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isInfiniteCardinal,ForcingLocalRecordPullback.supported_freeClosed,
      ConstructionCohenCompatibility.restricted_freeClosed,ConstructionPlacementTriple.imageAt_freeClosed,
      targets_freeClosed,family_freeClosed]

theorem source_models {k : Nat} (rho : Fin 7 → Fin k)
    (G F mul I K B w mu one c top bit labels E j sigma bound J H list s p pos d delta z indices r product multipliers : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (sourceSentence rho G F mul I K B w mu one c top bit labels E j sigma bound J H list s p pos d delta z indices r product multipliers)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_forall_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),ForcingSupportSize.small_semantics (M := M),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),ForcingHS.hs_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ForcingOrdinalFixed.fixed_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingDiagramOrder.product_semantics (M := M),
    ForcingCohenConditions.condition_semantics (M := M),ForcingLocalRecordPullback.supported_semantics hM,
    ConstructionCohenCompatibility.restricted_semantics hM,ForcingSupportingRoot.code_semantics (M := M),
    ConstructionPlacementTriple.imageAt_semantics hM,ForcingRelationClassMove.value_semantics (M := M),
    ForcingOutsideLocal.outside_semantics (M := M),KuratowskiZF.source_edge]
  intro hp hG hF hw hMu hLarge hSmall hm hc htop hLabels hBound hE hRootRange hRoot hEf hList hs hpos hSub hd hSupp hRestr hz hj hSigma hOut hr hpRoot hSubR hMuls hProducts
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,targets_semantics hM,family_semantics hM]
  exact source_construct hM hChoice env rho G F mul I K B w mu one c top bit labels E j sigma bound J H list s p pos d delta z indices r product multipliers
    hp hG hF hw hMu hLarge hSmall hm hc htop hLabels hBound hE hRootRange hRoot hEf hList hs hpos hSub hd hSupp hRestr hz hj hSigma hOut hr hpRoot hSubR hMuls hProducts

theorem source_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (G F mul I K B w mu one c top bit labels E j sigma bound J H list s p pos d delta z indices r product multipliers : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (sourceSentence rho G F mul I K B w mu one c top bit labels E j sigma bound J H list s p pos d delta z indices r product multipliers))) := by
  apply ModelTransfer.derives
  intro N hN
  have hL := ConstructibleSource.model_zf hN
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hN)
  let inhabitant := Classical.choice ((ConstructibleSource.model hN).nonempty .set)
  let env : Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hN)) 0 := ⟨Fin.elim0,fun _ => inhabitant⟩
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hN
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hL) _).mp
    (source_models rho G F mul I K B w mu one c top bit labels E j sigma bound J H list s p pos d delta z indices r product multipliers hL hChoice)

end PPAC.Migration.ForcingOutsideCopies
