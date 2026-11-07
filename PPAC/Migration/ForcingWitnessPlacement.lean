/- Pinned Construction/DiagramPlacements.transported_name_supported and
witness_placement. Reuse the actual RootProbes, internal target diagrams,
native bounded uniformization and compatible-copy selection. All probe
families and moved Cohen conditions are internal sets. -/
import PPAC.Migration.ForcingRootProbes
import PPAC.Migration.ForcingOutsideCopies
import PPAC.Migration.ForcingProbeDensity

namespace PPAC.Migration.ForcingWitnessPlacement
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingConditionGraphs (Permutation CompositionGraph FunctionOn)
open ForcingSupportSize (Injection Small)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open Source (Formula)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingFormula (Force)
open ForcingPairUnion (domain)
open ForcingSupportingRoot (Code)
open ForcingSupportedNames (Range Supported)
open ForcingDiagramOrder (Sub Product)
open ConstructionDiagramPlacements (FixesRange)
open ConstructionDescentPlacement (ActualMoved)
open ForcingCohenConditions (Condition)
open ConstructionCohenCompatibility (Restricted Compatible)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000
universe u v1 v2
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Exact source transported_name_supported; the support is the target range,
not merely some member of the normal filter. -/
theorem transported_name_supported (hM : FirstOrder.Theory.Models M nativeZF)
    (v : Fin 7 → M.Carrier .set) {I K B w G s t Js Jt Hs Ht pi A tau nu : M.Carrier .set}
    (hPres : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hG : ForcingLabelPermutations.Carrier I G)
    (hs : Injection (v 0) I s) (hJs : Range (v 0) s Js) (hJt : Range (v 0) t Jt)
    (hHs : ForcingLabelPermutations.Fixing G Js Hs) (hHt : ForcingLabelPermutations.Fixing G Jt Ht)
    (hpi : Permutation I pi) (hComp : CompositionGraph (v 0) pi s t)
    (hA : ForcingMapConditions.MapRel actionFormula v pi A)
    (hn : ForcingNames.IsName (v 6) tau) (hTau : Supported v Hs tau)
    (hNu : ForcingStabilizer.Action (v 6) A tau nu) : Supported v Ht nu := by
  intro g hg Bact hB
  obtain ⟨hgG,hFix⟩ := (hHt g).mp hg
  have hgPerm := (hG g).mp hgG
  obtain ⟨product,hProduct,hMult⟩ := ForcingConditionGraphs.exists_composition hM hgPerm hpi
  obtain ⟨C,hC⟩ := ForcingProductFamily.exists_action hM hPres hProduct
  have hAC := ForcingProductFamily.multiplication hM hPres hpi hMult
    ((mapRel_action v g Bact).mp hB) ((mapRel_action v pi A).mp hA) hC
  obtain ⟨out,hOut⟩ := ForcingNameConjugacy.exists_action hM
    (ForcingProductFamily.action_permutation ((mapRel_action v g Bact).mp hB)).1 nu
  have hComposite := ForcingNameConjugacy.composition hM
    (ForcingProductFamily.action_permutation ((mapRel_action v g Bact).mp hB)).1
    (ForcingProductFamily.action_permutation ((mapRel_action v pi A).mp hA)).1 hAC hNu hOut
  have hSame : CompositionGraph (v 0) product s t := by
    intro x z
    constructor
    · intro hxz
      obtain ⟨hx,y,hxy,hyz⟩ := (hComp x z).mp hxz
      have hyI := hs.1.2 x y hxy
      have hzJ := (hJt z).mpr ⟨x,hx,hxz⟩
      exact ⟨hx,y,hxy,(hMult y z).mpr ⟨hyI,z,hyz,hFix z hzJ⟩⟩
    · rintro ⟨hx,y,hxy,hyz⟩
      obtain ⟨_,a,hya,haz⟩ := (hMult y z).mp hyz
      have hxa := (hComp x a).mpr ⟨hx,y,hxy,hya⟩
      have haJ := (hJt a).mpr ⟨x,hx,hxa⟩
      have eq := ForcingConditionGraphs.function_unique hgPerm.1.1 haz (hFix a haJ)
      exact eq.symm ▸ hxa
  have eq := ForcingSupportedNames.name_eq_of_same_diagram hM v hPres hG hHs hs hJs hn hTau
    hpi hProduct hComp hSame hA ((mapRel_action v product C).mpr hC) hNu hComposite
  exact eq.symm ▸ hOut

/-- A selected moved condition retains the actual permutation and its target
diagram as existential internal-set witnesses. -/
def Copy (D I CC S w p s targets d i moved : M.Carrier .set) : Prop :=
  ∃ t pi, PureKuratowski.PairMember M i t targets ∧ Permutation I pi ∧
    CompositionGraph D pi s t ∧ FixesRange D p pi ∧ ActualMoved CC S w pi d moved

def copy {n : Nat} (D I CC S w p s targets d i moved : Fin n) : Project.Formula 1 n :=
  let up : Fin n → Fin (n+2) := fun j => j.succ.succ
  .existsE (.existsE
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (up targets) (up i) 1))
      (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation (up I) 0))
        (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph (up D) 0 (up s) 1))
          (.conj (ConstructionDiagramPlacements.fixesRange (up D) (up p) 0)
            (ConstructionDescentPlacement.actualMoved (up CC) (up S) (up w) 0 (up d) (up moved)))))))

theorem copy_freeClosed {n : Nat} (D I CC S w p s targets d i moved : Fin n) :
    (copy D I CC S w p s targets d i moved).FreeClosed := by
  simp -implicitDefEqProofs [copy,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionDiagramPlacements.fixesRange_freeClosed,ConstructionDescentPlacement.actualMoved_freeClosed]

theorem copy_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (D I CC S w p s targets d i moved : Fin n) :
    Project.Formula.satisfies env (copy D I CC S w p s targets d i moved) ↔
      Copy (env.bound D) (env.bound I) (env.bound CC) (env.bound S) (env.bound w) (env.bound p)
        (env.bound s) (env.bound targets) (env.bound d) (env.bound i) (env.bound moved) := by
  simp only [copy,Copy,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ConstructionDiagramPlacements.fixesRange_semantics hM,ConstructionDescentPlacement.actualMoved_semantics hM]
  rfl

/-- Replace the source host choose by bounded native uniformization on the
existing Cohen carrier. No family of names or external choice is extracted. -/
theorem construct_copies (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (D I mul CC S w mu X p s b indices targets d : Fin k)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hLarge : ¬ Small (env I) (env mu)) (hSmall : Small (env D) (env mu))
    {K : M.Carrier .set} (hC : ForcingCohenCoordinates.Cartesian (env I) K (env CC))
    {bits : M.Carrier .set} (hS : ForcingCohenCoordinates.Cartesian (env CC) bits (env S))
    (hX : ForcingCohenConditions.Carrier (env S) (env w) (env X))
    (hs : Injection (env D) (env I) (env s)) (hLeft : ForcingDiagramOrder.LeftInjection (env D) (env mul) (env b))
    (hSubS : Sub (env D) (env mul) (env s) (env b) (env p))
    (hTargets : FunctionOn (env indices) (env targets))
    (hRoots : ∀ i t, PureKuratowski.PairMember M i t (env targets) →
      Injection (env D) (env I) t ∧ Sub (env D) (env mul) t (env b) (env p))
    (hd : Condition (env S) (env w) (env d)) :
    ∃ output, FunctionOn (env indices) output ∧ ∀ i moved, PureKuratowski.PairMember M i moved output →
      Copy (env D) (env I) (env CC) (env S) (env w) (env p) (env s) (env targets) (env d) i moved := by
  let schema : Project.BinarySchema k := {
    body := copy D.succ.succ I.succ.succ CC.succ.succ S.succ.succ w.succ.succ p.succ.succ s.succ.succ
      targets.succ.succ d.succ.succ 1 0
    freeClosed := copy_freeClosed .. }
  let penv : Env (Project.FirstOrderSemantics.reduct M) k := ⟨env,fun _ => env d⟩
  have he i moved : schema.denote penv i moved ↔
      Copy (env D) (env I) (env CC) (env S) (env w) (env p) (env s) (env targets) (env d) i moved := by
    exact copy_semantics hM _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨output,hOutput,hSelect⟩ := ExistingSmallUnion.uniformize_formula_l (KuratowskiZF.interpretation hM)
    (ConstructionDirectedCardinality.models_zfc hM hChoice) schema penv (X := env indices) (Y := env X) (by
      intro i hi
      obtain ⟨t,hit,_⟩ := hTargets.2 i hi
      obtain ⟨ht,hSubT⟩ := hRoots i t hit
      obtain ⟨pi,hpi,hComp,hFix⟩ := ConstructionDiagramPlacements.permutation_over_root hM hChoice
        hw hMu hLarge hSmall hs ht hLeft hSubS hSubT
      obtain ⟨f,g,moved,hf,hfg,hg,hgg,hm,hImage,hMoved⟩ :=
        ConstructionCohenCompatibility.exists_moved hM hC hS hpi hd
      exact ⟨moved,(hX moved).mpr hm,(he i moved).mpr
        ⟨t,pi,hit,hpi,hComp,hFix,f,g,hf,hfg,hg,hgg,hm,hImage,hMoved⟩⟩)
  exact ⟨output,((ForcingSupportSize.native_mapsTo hM _ _ _).mpr hOutput).1,
    fun i moved hi => (he i moved).mp (hSelect i moved hi)⟩

/-- Source witness_placement, nonunit case: choose the actual internal copy
whose nonroot support avoids c, then form the actual common extension. -/
theorem place_condition_nonunit (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (env : Fin k → M.Carrier .set) (D I K B CC S w mu X Y mul unit mark index p q s b d c J delta : Fin k)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hLarge : ¬ Small (env I) (env mu)) (hSmall : Small (env D) (env mu))
    (hC : ForcingCohenCoordinates.Cartesian (env I) (env K) (env CC))
    (hS : ForcingCohenCoordinates.Cartesian (env CC) (env B) (env S))
    (hX : ForcingCohenConditions.Carrier (env S) (env w) (env X))
    (hY : ForcingDiagramCarrier.Carrier (env D) (env I) (env Y))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env D) (env mul) (env unit))
    (hProbes : ForcingRootProbes.RootProbes (env index) (env D) (env mul) (env unit) (env mark))
    (hIndex : ¬ Small (env index) (env w))
    (hp : Injection (env D) (env I) (env p)) (hq : Injection (env D) (env I) (env q))
    (hs : Injection (env D) (env I) (env s))
    (hb : (Project.FirstOrderSemantics.reduct M).mem (env b) (env D)) (hne : env b ≠ env unit)
    (hSubQ : Sub (env D) (env mul) (env q) (env mark) (env p))
    (hSubS : Sub (env D) (env mul) (env s) (env b) (env p))
    (hJ : Range (env D) (env p) (env J))
    (hd : Condition (env S) (env w) (env d)) (hc : Condition (env S) (env w) (env c))
    (hSupp : ForcingLocalRecordPullback.Supported (env D) (env s) (env d))
    (hRestr : Restricted (env J) (env d) (env delta)) (hRoot : Compatible (env c) (env delta)) :
    ∃ a t pi moved, Condition (env S) (env w) a ∧
      (Project.FirstOrderSemantics.reduct M).MemberSubset (env c) a ∧
      Injection (env D) (env I) t ∧ ForcingDiagramOrder.Le (env D) (env mul) (env q) t ∧
      Permutation (env I) pi ∧ CompositionGraph (env D) pi (env s) t ∧ FixesRange (env D) (env p) pi ∧
      ActualMoved (env CC) (env S) (env w) pi (env d) moved ∧
      (Project.FirstOrderSemantics.reduct M).MemberSubset moved a := by
  obtain ⟨multipliers,hMuls,hProducts,hIndependent⟩ := hProbes (env b) hb hne
  obtain ⟨targets,hTargets,hTargetData⟩ := ForcingOutsideCopies.construct_targets_at hM env
    D I mul unit q p b mark index Y multipliers hm hq hp hb hSubQ hMuls.1 hProducts hY
  let env' : Fin (k+1) → M.Carrier .set := Fin.cases targets env
  obtain ⟨copies,hCopies,hCopy⟩ := construct_copies hM hChoice env'
    D.succ I.succ mul.succ CC.succ S.succ w.succ mu.succ X.succ p.succ s.succ b.succ index.succ 0 d.succ
    hw hMu hLarge hSmall hC hS hX hs (hm.2.1 (env b) hb) hSubS hTargets
    (fun i t hit => ⟨(hTargetData i t hit).1,(hTargetData i t hit).2.1⟩) hd
  have hFamily : ForcingProbeDensity.Copies (env index) copies (env S) (env w) (env J) (env delta) := by
    refine ⟨hCopies,?_⟩
    intro i moved hi
    obtain ⟨t,pi,_,hpi,_,hFix,hMoved⟩ := hCopy i moved hi
    have hMoved' := ConstructionDescentPlacement.actual_moved_condition hMoved
    exact ⟨hMoved'.1,ForcingOutsideCopies.restrict_permute_of_fixes hM hC hS hpi hd hMoved'.1
      (fun z hz => hFix z ((hJ z).mp hz)) hMoved'.2 hRestr⟩
  have hDisjoint : ForcingProbeDensity.DisjointOff (env index) copies (env J) := by
    intro i j moved moved' label _ _ hi hj hOff hOff'
    apply Classical.byContradiction
    intro hij
    obtain ⟨t,pi,hit,_,hComp,_,hMoved⟩ := hCopy i moved hi
    obtain ⟨t',pi',hjt,_,hComp',_,hMoved'⟩ := hCopy j moved' hj
    obtain ⟨_,_,m,him,hSub⟩ := hTargetData i t hit
    obtain ⟨_,_,m',hjm,hSub'⟩ := hTargetData j t' hjt
    have hInter := ConstructionDiagramPlacements.range_inter_sub hq hSub hSub' hSubQ
      (hIndependent i j m m' him hjm hij)
    obtain ⟨ki,bi,hEntry⟩ := hOff.1
    obtain ⟨kj,bj,hEntry'⟩ := hOff'.1
    have hLabel := ForcingOutsideCopies.moved_supported hComp hSupp
      (ConstructionDescentPlacement.actual_moved_condition hMoved).2 label ki bi hEntry
    have hLabel' := ForcingOutsideCopies.moved_supported hComp' hSupp
      (ConstructionDescentPlacement.actual_moved_condition hMoved').2 label kj bj hEntry'
    exact hOff.2 ((hJ label).mpr ((hInter label).mp ⟨hLabel,hLabel'⟩))
  obtain ⟨i,moved,_,hi,hCompatible⟩ := ForcingProbeDensity.compatible_copy hM hChoice hw hC hS
    hFamily hDisjoint hIndex hc hRoot
  obtain ⟨t,pi,hit,hpi,hComp,hFix,hMoved⟩ := hCopy i moved hi
  obtain ⟨ht,_,m,him,hSub⟩ := hTargetData i t hit
  obtain ⟨a,ha,_,hca,hma⟩ := ConstructionCohenCompatibility.exists_union hM hw hc
    (ConstructionDescentPlacement.actual_moved_condition hMoved).1 hCompatible
  exact ⟨a,t,pi,moved,ha,hca,ht,⟨m,hMuls.1.2 i m him,hSub⟩,hpi,hComp,hFix,hMoved,hma⟩

/-- Full pinned witness_placement, for arbitrary external finite formula and
arbitrary internal-rank HS witness. The chosen diagram q is unchanged. -/
theorem witness_placement (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I K B w mu G F mul unit mark index p q s b d c Jp Hp Js Hs Jq Hq delta tau z : Fin k)
    (phi : Formula (n+1)) (v : Fin n → M.Carrier .set)
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hF : ForcingNormalFilter.Normal (env I) (env G) (env F))
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hLarge : ¬ Small (env I) (env mu)) (hSmall : Small (env (rho 0)) (env mu))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env unit))
    (hMark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hProbes : ForcingRootProbes.RootProbes (env index) (env (rho 0)) (env mul) (env unit) (env mark))
    (hIndex : ¬ Small (env index) (env w))
    (hp : Injection (env (rho 0)) (env I) (env p)) (hq : Injection (env (rho 0)) (env I) (env q))
    (hs : Injection (env (rho 0)) (env I) (env s))
    (hb : (Project.FirstOrderSemantics.reduct M).mem (env b) (env (rho 0)))
    (hSubQ : Sub (env (rho 0)) (env mul) (env q) (env mark) (env p))
    (hSubS : Sub (env (rho 0)) (env mul) (env s) (env b) (env p))
    (hJp : Range (env (rho 0)) (env p) (env Jp)) (hHp : ForcingLabelPermutations.Fixing (env G) (env Jp) (env Hp))
    (hJs : Range (env (rho 0)) (env s) (env Js)) (hHs : ForcingLabelPermutations.Fixing (env G) (env Js) (env Hs))
    (hJq : Range (env (rho 0)) (env q) (env Jq)) (hHq : ForcingLabelPermutations.Fixing (env G) (env Jq) (env Hq))
    (hv : ∀ j, Supported (fun i => env (rho i)) (env Hp) (v j))
    (hTau : ForcingHS.HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) (env tau))
    (hTauSupport : Supported (fun i => env (rho i)) (env Hs) (env tau))
    (hd : Condition (env (rho 2)) (env w) (env d)) (hc : Condition (env (rho 2)) (env w) (env c))
    (hSupp : ForcingLocalRecordPullback.Supported (env (rho 0)) (env s) (env d))
    (hRestr : Restricted (env Jp) (env d) (env delta)) (hRoot : Compatible (env c) (env delta))
    (hz : Code (env z) (env d) (env s))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (Fin.lastCases (env tau) v) (env (rho 6)) (env z) phi) :
    ∃ a nu out, Condition (env (rho 2)) (env w) a ∧
      (Project.FirstOrderSemantics.reduct M).MemberSubset (env c) a ∧
      ForcingHS.HS actionFormula (fun i => env (rho i)) (env G) (env (rho 6)) (env F) nu ∧
      Supported (fun i => env (rho i)) (env Hq) nu ∧ Code out a (env q) ∧
      Force (orderFormula (rho 0) mul) (domain rho G F) env (Fin.lastCases nu v) (env (rho 6)) out phi := by
  classical
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hPres.2.2.2.2.1 hPres.2.2.2.1 hPres.2.2.2.2.2
  have hqp : ForcingDiagramOrder.Le (env (rho 0)) (env mul) (env q) (env p) := ⟨env mark,hMark,hSubQ⟩
  have hzW := ForcingSupportingRoot.code_mem hPres hd hs hz
  by_cases he : env b = env unit
  · have hsp : env s = env p := ForcingDiagramPoset.injection_ext hM hs hp (fun x y =>
      ((ForcingDiagramPoset.sub_one hm hs) x y).trans ((he ▸ hSubS) x y).symm)
    have hDelta : env delta = env d := by
      apply ConstructionCohenCompatibility.entries_ext hM hPres.1 hPres.2.1
        (ForcingSupportingRoot.restricted_condition hM hd hRestr) hd
      intro i j bit
      rw [ConstructionCohenCompatibility.restricted_entry hRestr]
      exact ⟨And.left,fun h => ⟨h,(hJp i).mpr (hsp ▸ hSupp i j bit h)⟩⟩
    obtain ⟨a,ha,_,hca,hda⟩ := ConstructionCohenCompatibility.exists_union hM hw hc hd (hDelta ▸ hRoot)
    obtain ⟨out,hout⟩ := ForcingSupportingRoot.exists_code hM a (env q)
    have houtW := ForcingSupportingRoot.code_mem hPres ha hq hout
    have hSupport := ForcingSupportedNames.supported_mono hHs hHq
      (fun x hx => (hJq x).mpr (ConstructionDescentPlacement.range_antitone hqp
        (hsp ▸ (hJs x).mp hx))) hTauSupport
    refine ⟨a,env tau,out,ha,hca,hTau,hSupport,hout,?_⟩
    exact ForcingFormula.mono hM hpre phi _ hzW houtW
      ((orderFormula_semantics env (rho 0) mul out (env z)).mpr
        ((ForcingSupportingRoot.code_le hout hz).mpr ⟨hda,hsp ▸ hqp⟩)) hf
  · obtain ⟨a,t,pi,moved,ha,hca,ht,hqt,hpi,hComp,hFix,hMoved,hma⟩ :=
      place_condition_nonunit hM hChoice env (rho 0) I K B (rho 1) (rho 2) w mu (rho 3) (rho 4)
        mul unit mark index p q s b d c Jp delta hw hMu hLarge hSmall hPres.1 hPres.2.1 hPres.2.2.1 hPres.2.2.2.1
        hm hProbes hIndex hp hq hs hb he hSubQ hSubS hJp hd hc hSupp hRestr hRoot
    obtain ⟨A,hA⟩ := ForcingProductFamily.exists_action hM hPres hpi
    have hAr := (mapRel_action (fun i => env (rho i)) pi A).mpr hA
    have hAPerm := ForcingProductFamily.action_permutation hA
    obtain ⟨nu,hNu⟩ := ForcingNameConjugacy.exists_action hM hAPerm.1 (env tau)
    obtain ⟨inv,hInv,hInverse⟩ := ForcingConditionGraphs.exists_inverse hM hpi
    obtain ⟨Bact,hB⟩ := ForcingProductFamily.exists_action hM hPres hInv
    obtain ⟨conj,hConj,hConjugate⟩ := ForcingConjugationGraph.exists_graph hM hG hpi hInv hInverse
    have hContext := ForcingSeparation.normal_context hM (fun i => env (rho i)) hPres hG hF hpi hInv hInverse
      hConj hConjugate hAr ((mapRel_action (fun i => env (rho i)) inv Bact).mpr hB)
    have hNuHS := ForcingHSAction.hs_action hM hContext (env tau) hTau nu hNu
    obtain ⟨Jt,hJt,_,_⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 ht hSmall
    obtain ⟨Ht,hHt⟩ := ForcingLabelPermutations.exists_fixing hM (env G) Jt
    have hNuSupport := transported_name_supported hM (fun i => env (rho i)) hPres hG hs hJs hJt
      hHs hHt hpi hComp hAr (ForcingHS.isName hTau) hTauSupport hNu
    have hSupport := ForcingSupportedNames.supported_mono hHt hHq
      (fun x hx => (hJq x).mpr (ConstructionDescentPlacement.range_antitone hqt ((hJt x).mp hx))) hNuSupport
    obtain ⟨mid,hMid⟩ := ForcingSupportingRoot.exists_code hM moved t
    obtain ⟨out,hOut⟩ := ForcingSupportingRoot.exists_code hM a (env q)
    have hMidW := ForcingSupportingRoot.code_mem hPres
      (ConstructionDescentPlacement.actual_moved_condition hMoved).1 ht hMid
    have hOutW := ForcingSupportingRoot.code_mem hPres ha hq hOut
    have hPiRoot := (hHp pi).mpr ⟨(hG pi).mpr hpi,fun x hx => hFix x ((hJp x).mp hx)⟩
    have hVec : ∀ j, ForcingStabilizer.Action (env (rho 6)) A
        (Fin.lastCases (env tau) v j) (Fin.lastCases nu v j) := by
      intro j
      refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [Fin.lastCases_last] using hNu
      · simpa only [Fin.lastCases_castSucc] using hv j pi hPiRoot A hAr
    have hSym := (ForcingSeparation.symmetry hM env rho G F mul hPres hG hF hpi hAr phi
      (Fin.lastCases (env tau) v) (Fin.lastCases nu v) hVec hzW
      (ForcingSupportingRoot.moved_code hM hPres hA hd hs ht hMoved hComp hz hMid)).mp hf
    exact ⟨a,nu,out,ha,hca,hNuHS,hSupport,hOut,ForcingFormula.mono hM hpre phi _ hMidW hOutW
      ((orderFormula_semantics env (rho 0) mul out mid).mpr
        ((ForcingSupportingRoot.code_le hOut hMid).mpr ⟨hma,hqt⟩)) hSym⟩

private theorem lastCases_map {a : Type v1} {b : Type v2} {n : Nat} (f : a → b) (x : a) (v : Fin n → a) :
    (fun j => f (Fin.lastCases x v j)) = Fin.lastCases (f x) (fun j => f (v j)) := by
  funext j
  refine Fin.lastCases ?_ (fun _ => ?_) j <;>
    simp only [Fin.lastCases_last,Fin.lastCases_castSucc]

/-- The exact output graph, HS witness, prescribed support and full formula. -/
def resultFormula {k n : Nat} (rho : Fin 7 → Fin k) (G F w q c Hq : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1)) (mul : Fin k) : Project.Formula 1 k :=
  let up : Fin k → Fin (k+3) := fun j => j.succ.succ.succ
  .existsE (.existsE (.existsE
    (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (up (rho 2)) (up w) 2))
      (.conj (ProjectSyntax.encode id (Source.SetLanguage.subset (up c) 2))
        (.conj (ProjectSyntax.encode id (ForcingHS.hs actionFormula (fun j => up (rho j)) (up G) (up (rho 6)) (up F) 1))
          (.conj (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll (fun j => up (rho j)) (up Hq) 1))
            (.conj (ProjectSyntax.encode id (ForcingSupportingRoot.code 0 2 (up q)))
              (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) up
                (Fin.lastCases 1 (fun j => up (v j))) (up (rho 6)) 0 phi)))))))))

theorem resultFormula_freeClosed {k n : Nat} (rho : Fin 7 → Fin k) (G F w q c Hq : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1)) (mul : Fin k) :
    (resultFormula rho G F w q c Hq v phi mul).FreeClosed := by
  simp -implicitDefEqProofs [resultFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem resultFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) k) (rho : Fin 7 → Fin k) (G F w q c Hq : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1)) (mul : Fin k) :
    Project.Formula.satisfies env (resultFormula rho G F w q c Hq v phi mul) ↔
      ∃ a nu out, Condition (env.bound (rho 2)) (env.bound w) a ∧
        (Project.FirstOrderSemantics.reduct M).MemberSubset (env.bound c) a ∧
        ForcingHS.HS actionFormula (fun j => env.bound (rho j)) (env.bound G) (env.bound (rho 6)) (env.bound F) nu ∧
        Supported (fun j => env.bound (rho j)) (env.bound Hq) nu ∧ Code out a (env.bound q) ∧
        Force (orderFormula (rho 0) mul) (domain rho G F) env.bound
          (Fin.lastCases nu (fun j => env.bound (v j))) (env.bound (rho 6)) out phi := by
  simp only [resultFormula,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenConditions.condition_semantics (M := M),ForcingLabelPermutations.subset_semantics (M := M),
    ForcingHS.hs_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    ForcingSupportingRoot.code_semantics (M := M),ForcingFormula.formula_semantics (M := M)]
  simp only [id_eq,SetTheory.Env.push,Fin.cases_succ,Fin.cases_zero,lastCases_map]
  rfl

/-- Source witness_placement as an object sentence scheme. Every background
guard is an original source hypothesis; actual RootProbes were proved from
the same saturation system in ForcingRootProbes.on_core. -/
def sentence {k n : Nat} (rho : Fin 7 → Fin k) (I K B w mu G F mul unit mark index p q s b d c Jp Hp Js Hs Jq Hq delta tau z : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1)) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
      (.imp (ProjectSyntax.encode id (ForcingNormalFilter.normal I G F))
      (.imp (Project.Formula.isOmega (.bound w))
      (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
      (.imp (.neg (ProjectSyntax.encode id (ForcingSupportSize.small I mu)))
      (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
      (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul unit))
      (.imp (.mem (.bound mark) (.bound (rho 0)))
      (.imp (ForcingRootProbes.rootProbes index (rho 0) mul unit mark)
      (.imp (.neg (ProjectSyntax.encode id (ForcingSupportSize.small index w)))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection p (rho 0) I))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection s (rho 0) I))
      (.imp (.mem (.bound b) (.bound (rho 0)))
      (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul q mark p))
      (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul s b p))
      (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) p Jp))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Jp Hp))
      (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) s Js))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Js Hs))
      (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q Jq))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Jq Hq))
      (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.tupleSupported rho Hp v))
      (.imp (ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F tau))
      (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hs tau))
      (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d))
      (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w c))
      (.imp (ForcingLocalRecordPullback.supported (rho 0) s d)
      (.imp (ConstructionCohenCompatibility.restricted Jp d delta)
      (.imp (ConstructionCompatiblePlacement.compatible c delta)
      (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z d s))
      (.imp (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id (Fin.lastCases tau v) (rho 6) z phi))
      (resultFormula rho G F w q c Hq v phi mul))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isInfiniteCardinal,ForcingRootProbes.rootProbes_freeClosed,
      ForcingLocalRecordPullback.supported_freeClosed,ConstructionCohenCompatibility.restricted_freeClosed,
      ConstructionCompatiblePlacement.compatible_freeClosed,resultFormula_freeClosed]

theorem models {k n : Nat} (rho : Fin 7 → Fin k) (I K B w mu G F mul unit mark index p q s b d c Jp Hp Js Hs Jq Hq delta tau z : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1))
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (sentence rho I K B w mu G F mul unit mark index p q s b d c Jp Hp Js Hs Jq Hq delta tau z v phi)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingProductFamily.presentation_semantics (M := M),ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingNormalFilter.normal_semantics (M := M),ForcingSupportSize.small_semantics (M := M),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingRootProbes.rootProbes_semantics hM,
    ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingSupportingRoot.tupleSupported_semantics (M := M),ForcingHS.hs_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    ForcingLocalRecordPullback.supported_semantics hM,ConstructionCohenCompatibility.restricted_semantics hM,
    ConstructionCompatiblePlacement.compatible_semantics hM,ForcingSupportingRoot.code_semantics (M := M),
    ForcingFormula.formula_semantics (M := M),resultFormula_semantics hM]
  intro hPres hG hF hw hMu hLarge hSmall hm hMark hProbes hIndex hp hq hs hb hSubQ hSubS
    hJp hHp hJs hHs hJq hHq hv hTau hTauSupport hd hc hSupp hRestr hRoot hz hf
  simp only [id_eq,lastCases_map] at hf
  exact witness_placement hM hChoice env rho I K B w mu G F mul unit mark index p q s b d c Jp Hp Js Hs Jq Hq delta tau z phi (fun j => env (v j))
    hPres hG hF hw hMu hLarge hSmall hm hMark hProbes hIndex hp hq hs hb hSubQ hSubS
    hJp hHp hJs hHs hJq hHq hv hTau hTauSupport hd hc hSupp hRestr hRoot hz hf

/-- Ordinary native ZF endpoint. The existing internal L discharges ground
Choice; no Choice premise or new proof kernel is added to this certificate. -/
theorem kernel_certificate {k n : Nat} (rho : Fin 7 → Fin k) (I K B w mu G F mul unit mark index p q s b d c Jp Hp Js Hs Jq Hq delta tau z : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (sentence rho I K B w mu G F mul unit mark index p q s b d c Jp Hp Js Hs Jq Hq delta tau z v phi))) := by
  apply ModelTransfer.derives
  intro N hN
  have hL := ConstructibleSource.model_zf hN
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hN)
  obtain ⟨witness,_⟩ := ZF.exists_omega (ModelTransfer.project_models_iff.mp hL)
  let env : Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hN)) 0 :=
    ⟨Fin.elim0,fun _ => witness⟩
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hN
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) _).mp
      (models rho I K B w mu G F mul unit mark index p q s b d c Jp Hp Js Hs Jq Hq delta tau z v phi hL hChoice)

end PPAC.Migration.ForcingWitnessPlacement

