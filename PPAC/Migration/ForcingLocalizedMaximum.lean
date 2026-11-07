/- Pinned Models/OrdinalChoice.localized_maximum:64-147. Consume actual
localized_existential and Cohen maximal_antichain, native Collection and
bounded uniformization, and the existing full mixing/HS/forcing laws.
All conditions, families, graphs and arbitrary-rank names are internal sets. -/
import PPAC.Migration.ForcingMaximalAntichain

namespace PPAC.Migration.ForcingLocalizedMaximum
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingFormula (Force)
open ForcingProductFamily (Presentation actionFormula mapRel_action)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingPairUnion (domain domain_semantics)
open ForcingSupportSize (Injection Small)
open ForcingSupportedNames (Supported Range)
open ForcingCohenConditions (Condition)
open ForcingConditionGraphs (FunctionOn)
open ForcingSupportingRoot (Code)
open ConstructionCohenCompatibility (Restricted Compatible)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1600000
universe u v1 v2
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private theorem lastCases_map {a : Type v1} {b : Type v2} {n : Nat} (f : a → b) (x : a) (v : Fin n → a) :
    (fun j => f (Fin.lastCases x v j)) = Fin.lastCases (f x) (fun j => f (v j)) := by
  funext j
  refine Fin.lastCases ?_ (fun _ => ?_) j <;> simp only [Fin.lastCases_last,Fin.lastCases_castSucc]

def ChoiceAt {k n : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (env : Fin k → M.Carrier .set)
    (rho : Fin 7 → M.Carrier .set) (G F q Hq : M.Carrier .set) (v : Fin n → M.Carrier .set)
    (phi : Formula (n+1)) (a nu : M.Carrier .set) : Prop :=
  ForcingHS.HS actionFormula rho G (rho 6) F nu ∧ Supported rho Hq nu ∧
    ∃ z, Code z a q ∧ Force R H env (Fin.lastCases nu v) (rho 6) z phi

def choiceAt {k n m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (rho : Fin 7 → Fin m) (G F q Hq a nu : Fin m) (v : Fin n → Fin m) (phi : Formula (n+1)) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (ForcingHS.hs actionFormula rho G (rho 6) F nu))
    (.conj (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho Hq nu))
      (.existsE (.conj (ProjectSyntax.encode id (ForcingSupportingRoot.code 0 a.succ q.succ))
        (ProjectSyntax.encode id (ForcingFormula.formula R H (fun j => (base j).succ)
          (Fin.lastCases nu.succ (fun j => (v j).succ)) (rho 6).succ 0 phi)))))

theorem choiceAt_freeClosed {k n m : Nat} (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (rho : Fin 7 → Fin m) (G F q Hq a nu : Fin m) (v : Fin n → Fin m) (phi : Formula (n+1)) :
    (choiceAt R H base rho G F q Hq a nu v phi).FreeClosed := by
  simp -implicitDefEqProofs [choiceAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem choiceAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k n m : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) m) (R : Formula (k+2)) (H : Formula (k+1)) (base : Fin k → Fin m)
    (rho : Fin 7 → Fin m) (G F q Hq a nu : Fin m) (v : Fin n → Fin m) (phi : Formula (n+1)) :
    Project.Formula.satisfies env (choiceAt R H base rho G F q Hq a nu v phi) ↔
      ChoiceAt R H (fun j => env.bound (base j)) (fun j => env.bound (rho j)) (env.bound G) (env.bound F)
        (env.bound q) (env.bound Hq) (fun j => env.bound (v j)) phi (env.bound a) (env.bound nu) := by
  simp only [choiceAt,ChoiceAt,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingHS.hs_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),ForcingSupportingRoot.code_semantics (M := M),
    ForcingFormula.formula_semantics (M := M)]
  simp only [id_eq,SetTheory.Env.push,Fin.cases_zero,Fin.cases_succ,lastCases_map]
  rfl

/-- Native Collection first bounds the arbitrary-rank witnesses; the already
accepted bounded uniformization then constructs the actual internal family. -/
theorem choose_family (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul q Hq : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1)) (A : M.Carrier .set)
    (hEach : ∀ a, (Project.FirstOrderSemantics.reduct M).mem a A →
      ∃ nu, ChoiceAt (orderFormula (rho 0) mul) (domain rho G F) env (fun j => env (rho j))
        (env G) (env F) (env q) (env Hq) (fun j => env (v j)) phi a nu) :
    ∃ f, FunctionOn A f ∧ ∀ a nu, PureKuratowski.PairMember M a nu f →
      ChoiceAt (orderFormula (rho 0) mul) (domain rho G F) env (fun j => env (rho j))
        (env G) (env F) (env q) (env Hq) (fun j => env (v j)) phi a nu := by
  let schema : Project.BinarySchema k := {
    body := choiceAt (orderFormula (rho 0) mul) (domain rho G F) (fun j => j.succ.succ)
      (fun j => (rho j).succ.succ) G.succ.succ F.succ.succ q.succ.succ Hq.succ.succ 1 0 (fun j => (v j).succ.succ) phi
    freeClosed := choiceAt_freeClosed .. }
  let penv : Env (Project.FirstOrderSemantics.reduct M) k := ⟨env,fun _ => env q⟩
  have he a nu : schema.denote penv a nu ↔
      ChoiceAt (orderFormula (rho 0) mul) (domain rho G F) env (fun j => env (rho j))
        (env G) (env F) (env q) (env Hq) (fun j => env (v j)) phi a nu :=
    choiceAt_semantics hM _ _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨names,hNames⟩ := ZF.collection_exists_d (ModelTransfer.project_models_iff.mp hM)
    schema penv A (fun a ha => by obtain ⟨nu,hnu⟩ := hEach a ha; exact ⟨nu,(he a nu).mpr hnu⟩)
  obtain ⟨f,hf,hSelect⟩ := ExistingSmallUnion.uniformize_formula_l (KuratowskiZF.interpretation hM)
    (ConstructionDirectedCardinality.models_zfc hM hChoice) schema penv (X := A) (Y := names) hNames
  exact ⟨f,((ForcingSupportSize.native_mapsTo hM _ _ _).mpr hf).1,
    fun a nu h => (he a nu).mp (hSelect a nu h)⟩

/-- The source dense family D as an actual separated subset of the SAME
Cohen carrier. No family or member witnesses are supplied. -/
theorem candidates (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F mul w q Hq d0 : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1))
    (hX : ForcingCohenConditions.Carrier (env (rho 2)) (env w) (env (rho 3))) :
    ∃ D, ∀ a, (Project.FirstOrderSemantics.reduct M).mem a D ↔
      Condition (env (rho 2)) (env w) a ∧ (Project.FirstOrderSemantics.reduct M).MemberSubset (env d0) a ∧
      ForcingLocalRecordPullback.Supported (env (rho 0)) (env q) a ∧
      ∃ nu, ChoiceAt (orderFormula (rho 0) mul) (domain rho G F) env (fun j => env (rho j))
        (env G) (env F) (env q) (env Hq) (fun j => env (v j)) phi a nu := by
  let schema : Project.UnarySchema k := {
    body := .conj (ProjectSyntax.encode id (Source.SetLanguage.subset d0.succ 0))
      (.conj (ForcingLocalRecordPullback.supported (rho 0).succ q.succ 0)
        (.existsE (choiceAt (orderFormula (rho 0) mul) (domain rho G F) (fun j => j.succ.succ)
          (fun j => (rho j).succ.succ) G.succ.succ F.succ.succ q.succ.succ Hq.succ.succ 1 0
          (fun j => (v j).succ.succ) phi)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ForcingLocalRecordPullback.supported_freeClosed,choiceAt_freeClosed] }
  let penv : Env (Project.FirstOrderSemantics.reduct M) k := ⟨env,fun _ => env w⟩
  have he a : schema.denote penv a ↔ (Project.FirstOrderSemantics.reduct M).MemberSubset (env d0) a ∧
      ForcingLocalRecordPullback.Supported (env (rho 0)) (env q) a ∧
      ∃ nu, ChoiceAt (orderFormula (rho 0) mul) (domain rho G F) env (fun j => env (rho j))
        (env G) (env F) (env q) (env Hq) (fun j => env (v j)) phi a nu := by
    simp only [schema,Project.UnarySchema.denote,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
      GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingLabelPermutations.subset_semantics (M := M),
      ForcingLocalRecordPullback.supported_semantics hM,choiceAt_semantics hM]
    rfl
  obtain ⟨D,hD⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema penv (env (rho 3))
  exact ⟨D,fun a => (hD a).trans (and_congr (hX a) (he a))⟩

private theorem code_unique (hM : FirstOrder.Theory.Models M nativeZF) {a q z z' : M.Carrier .set}
    (hz : Code z a q) (hz' : Code z' a q) : z = z' := by
  obtain ⟨p,hp,hz⟩ := hz
  obtain ⟨p',hp',hz'⟩ := hz'
  have eq := KuratowskiZF.code_unique hM hp hp'
  subst p'
  exact (ModelTransfer.extensionality hM).eq_of_same_members z z' (fun x => (hz x).trans (hz' x).symm)

/-- Actual activation function a |-> ((a,q):WithTop), on the chosen internal
antichain. Reuse native definable graph construction and literal code uniqueness. -/
theorem activations (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I K B w q : Fin k) (A : M.Carrier .set)
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hq : Injection (env (rho 0)) (env I) (env q))
    (hA : ∀ a, (Project.FirstOrderSemantics.reduct M).mem a A → Condition (env (rho 2)) (env w) a) :
    ∃ act, FunctionOn A act ∧ ∀ a z, PureKuratowski.PairMember M a z act → Code z a (env q) := by
  let schema : Project.BinarySchema k := {
    body := ProjectSyntax.encode id (ForcingSupportingRoot.code 0 1 q.succ.succ)
    freeClosed := ProjectSyntax.freeClosed .. }
  let penv : Env (Project.FirstOrderSemantics.reduct M) k := ⟨env,fun _ => env w⟩
  have he a z : schema.denote penv a z ↔ Code z a (env q) := by
    simp only [schema,Project.BinarySchema.denote,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
      ForcingSupportingRoot.code_semantics (M := M)]
    rfl
  obtain ⟨act,hAct,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema penv (source := A) (target := env (rho 6))
    (fun a ha => by obtain ⟨z,hz⟩ := ForcingSupportingRoot.exists_code hM a (env q); exact ⟨z,(he a z).mpr hz⟩)
    (fun _ _ _ _ hz hz' => code_unique hM ((he _ _).mp hz) ((he _ _).mp hz'))
    (fun a z ha hz => ForcingSupportingRoot.code_mem hPres (hA a ha) hq ((he a z).mp hz))
  exact ⟨act,((ForcingSupportSize.native_mapsTo hM _ _ _).mpr hAct).1,
    fun a z h => (he a z).mp ((hEdge a z).mp h).2⟩

private theorem code_fixed (hM : FirstOrder.Theory.Models M nativeZF) (v : Fin 7 → M.Carrier .set)
    {I K B w q J pi act d z : M.Carrier .set}
    (hPres : Presentation (v 0) I K B w (v 1) (v 2) (v 3) (v 4) (v 5) (v 6))
    (hq : Injection (v 0) I q) (hJ : Range (v 0) q J) (hpi : ForcingConditionGraphs.Permutation I pi)
    (hFix : ForcingLabelPermutations.Fixes J pi)
    (hAct : ForcingProductFamily.Action (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) pi act)
    (hd : Condition (v 2) w d) (hSupp : ForcingLocalRecordPullback.Supported (v 0) q d)
    (hz : Code z d q) : PureKuratowski.PairMember M z z act := by
  obtain ⟨f,g,moved,hf,hfg,hg,hgg,hm,hImage,hMoved⟩ :=
    ConstructionCohenCompatibility.exists_moved hM hPres.1 hPres.2.1 hpi hd
  have eq : moved = d := by
    apply ConstructionCohenCompatibility.entries_ext hM hPres.1 hPres.2.1 hm hd
    intro j k bit
    rw [hMoved j k bit]
    constructor
    · rintro ⟨i,hij,hi⟩
      have hii := hFix i ((hJ i).mpr (hSupp i k bit hi))
      have e := ForcingConditionGraphs.function_unique hpi.1.1 hij hii
      exact e.symm ▸ hi
    · intro hj
      exact ⟨j,hFix j ((hJ j).mpr (hSupp j k bit hj)),hj⟩
  subst moved
  have hComp : ForcingConditionGraphs.CompositionGraph (v 0) pi q q := by
    intro x z
    constructor
    · intro hxz
      have hx := ForcingConditionGraphs.function_input hq.1.1 hxz
      exact ⟨hx,z,hxz,hFix z ((hJ z).mpr ⟨x,hx,hxz⟩)⟩
    · rintro ⟨hx,y,hxy,hyz⟩
      have hyy := hFix y ((hJ y).mpr ⟨x,hx,hxy⟩)
      have e := ForcingConditionGraphs.function_unique hpi.1.1 hyz hyy
      exact e.symm ▸ hxy
  exact ForcingSupportingRoot.moved_code hM hPres hAct hd hq hq
    ⟨f,g,hf,hfg,hg,hgg,hm,hImage,hMoved⟩ hComp hz hz

private theorem subset_restrict
    {D I K B CC S w q J p d r : M.Carrier .set}
    (hC : ForcingCohenCoordinates.Cartesian I K CC) (hS : ForcingCohenCoordinates.Cartesian CC B S)
    (hJ : Range D q J) (hp : Condition S w p) (hSupport : ForcingLocalRecordPullback.Supported D q p)
    (hSub : (Project.FirstOrderSemantics.reduct M).MemberSubset p d) (hRestr : Restricted J d r) :
    (Project.FirstOrderSemantics.reduct M).MemberSubset p r := by
  intro z hz
  obtain ⟨coord,hCoord,bit,_,hCode⟩ := (hS z).mp (hp.1 z hz)
  obtain ⟨i,_,k,_,hCoordCode⟩ := (hC coord).mp hCoord
  exact (hRestr z).mpr ⟨hSub z hz,i,⟨coord,k,bit,hCode,hCoordCode⟩,
    (hJ i).mpr (hSupport i k bit ⟨coord,hCoordCode,z,hCode,hz⟩)⟩

private theorem compatible_root (hM : FirstOrder.Theory.Models M nativeZF)
    {I K B CC S w J d c b : M.Carrier .set}
    (hC : ForcingCohenCoordinates.Cartesian I K CC) (hS : ForcingCohenCoordinates.Cartesian CC B S)
    (hd : Condition S w d) (hb : Condition S w b) (hRestr : Restricted J d c)
    (hWithin : ConstructionCohenCompatibility.Within b J)
    (hcb : (Project.FirstOrderSemantics.reduct M).MemberSubset c b) : Compatible d b := by
  apply ConstructionCohenCompatibility.compatible_of_entries hC hS hd
  intro i k bit bit' hD hB
  have hCEntry := (ConstructionCohenCompatibility.restricted_entry hRestr).mpr ⟨hD,hWithin i k bit' hB⟩
  obtain ⟨coord,hCoord,z,hz,hzc⟩ := hCEntry
  obtain ⟨coord',hCoord',z',hz',hzb⟩ := hB
  have eq := KuratowskiZF.code_unique hM hCoord' hCoord
  subst coord'
  exact hb.2.1 coord bit bit' ⟨z,hz,hcb z hzc⟩ ⟨z',hz',hzb⟩

private theorem force_reindex {k l n : Nat} (env : Fin k → M.Carrier .set) (other : Fin l → M.Carrier .set)
    (up : Fin k → Fin l) (he : ∀ j, other (up j) = env j) (rho : Fin 7 → Fin k) (G F mul : Fin k)
    (phi : Formula n) (v : Fin n → M.Carrier .set) (p : M.Carrier .set) :
    Force (orderFormula (rho 0) mul) (domain rho G F) env v (env (rho 6)) p phi ↔
      Force (orderFormula (up (rho 0)) (up mul)) (domain (fun j => up (rho j)) (up G) (up F))
        other v (env (rho 6)) p phi := by
  apply ForcingSeparation.force_congr ?_ ?_ phi v _ p
  · intro x y
    simp only [orderFormula_semantics,he]
  · intro x
    simp only [domain_semantics,he]

/-- Full pinned localized_maximum: actual internal antichain, selected names,
activation graph and HS mixture. Cohen d0 and the predetermined q stay fixed. -/
theorem localized_maximum (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k n : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 Jp Hp Jq Hq z0 : Fin k)
    (phi : Formula (n+1)) (v : Fin n → Fin k)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) (env w) (env mu))
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) (env I) (env mu))
    (hD : Small (env (rho 0)) (env mu))
    (hCard : ConstructionSaturationCardinals.Cardinals hM (env (rho 0)) (env mul) (env mark) (env mu))
    (hMergers : ConstructionSaturationMergers.AllMergers (env w) (env history) (env kappa))
    (hRow : ConstructionTowerHistory.Row (env history) (env kappa) (env (rho 0)) (env mul)
      (env unit) (env mark) (env H) (env C) (env incoming) (env base) (env kappa))
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env unit))
    (hPres : Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hG : ForcingLabelPermutations.Carrier (env I) (env G))
    (hFilter : ForcingSupportFilter.Filter (env I) (env G) (env mu) (env F))
    (hMark : (Project.FirstOrderSemantics.reduct M).mem (env mark) (env (rho 0)))
    (hProbes : ForcingRootProbes.RootProbes (env index) (env (rho 0)) (env mul) (env unit) (env mark))
    (hIndex : ¬ Small (env index) (env w))
    (hp : Injection (env (rho 0)) (env I) (env p)) (hq : Injection (env (rho 0)) (env I) (env q))
    (hSubQ : ForcingDiagramOrder.Sub (env (rho 0)) (env mul) (env q) (env mark) (env p))
    (hJp : Range (env (rho 0)) (env p) (env Jp)) (hHp : ForcingLabelPermutations.Fixing (env G) (env Jp) (env Hp))
    (hJq : Range (env (rho 0)) (env q) (env Jq)) (hHq : ForcingLabelPermutations.Fixing (env G) (env Jq) (env Hq))
    (hv : ∀ j, Supported (fun i => env (rho i)) (env Hp) (env (v j)))
    (hd0 : Condition (env (rho 2)) (env w) (env d0))
    (hd0q : ForcingLocalRecordPullback.Supported (env (rho 0)) (env q) (env d0))
    (hz0 : Code (env z0) (env d0) (env p))
    (hf : Force (orderFormula (rho 0) mul) (domain rho G F) env (fun j => env (v j))
      (env (rho 6)) (env z0) (.ex phi)) :
    ∃ nu out, ForcingHS.HS actionFormula (fun j => env (rho j)) (env G) (env (rho 6)) (env F) nu ∧
      Supported (fun j => env (rho j)) (env Hq) nu ∧ Code out (env d0) (env q) ∧
      Force (orderFormula (rho 0) mul) (domain rho G F) env (Fin.lastCases nu (fun j => env (v j)))
        (env (rho 6)) out phi := by
  obtain ⟨D,hCandidates⟩ := candidates hM env rho G F mul w q Hq d0 v phi hPres.2.2.1
  obtain ⟨A,hAD,hAnti,hPred⟩ := ForcingMaximalAntichain.maximal_antichain hM hChoice hw
    (fun a ha => ((hCandidates a).mp ha).1)
  have hACond a ha := ((hCandidates a).mp (hAD a ha)).1
  obtain ⟨f,hFn,hSelected⟩ := choose_family hM hChoice env rho G F mul q Hq v phi A
    (fun a ha => ((hCandidates a).mp (hAD a ha)).2.2.2)
  obtain ⟨act,hActFn,hActCode⟩ := activations hM env rho I K B w q A hPres hq hACond
  have hpre := ForcingProductPoset.preorder env (rho 0) mul (rho 6) hm
    hPres.2.2.2.2.1 hPres.2.2.2.1 hPres.2.2.2.2.2
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hFilter
  obtain ⟨range,hRange,hRangeI,hRangeSmall⟩ := ConstructionDescentPlacement.diagram_range hM hMu.1.1 hq hD
  have hRangeEq : range = env Jq := (ModelTransfer.extensionality hM).eq_of_same_members range (env Jq)
    (fun x => (hRange x).trans (hJq x).symm)
  have hJI : (Project.FirstOrderSemantics.reduct M).MemberSubset (env Jq) (env I) := hRangeEq ▸ hRangeI
  have hJSmall : Small (env Jq) (env mu) := hRangeEq ▸ hRangeSmall
  have hGroup := ForcingConjugationGraph.fixing_subgroup hM hG hHq hJI
  have hHF : (Project.FirstOrderSemantics.reduct M).mem (env Hq) (env F) :=
    (hFilter (env Hq)).mpr ⟨hGroup,env Jq,env Hq,hJI,hJSmall,hHq,fun _ h => h⟩
  have hFamily : ForcingCollectedHS.FamilyHS (fun j => env (rho j)) (env G) (env (rho 6)) (env F) A f :=
    fun a nu _ ha => (hSelected a nu ha).1
  have hPerm : ForcingEquivariantMix.Permutes (fun j => env (rho j)) (env Hq) A f act := by
    intro pi hpi actPi hActPi a nu z ha hfa haz
    have hpip := (hG pi).mp ((hHq pi).mp hpi).1
    exact ⟨a,nu,z,ha,hfa,haz,(hSelected a nu hfa).2.1 pi hpi actPi hActPi,
      code_fixed hM (fun j => env (rho j)) hPres hq hJq hpip ((hHq pi).mp hpi).2
        ((mapRel_action _ _ _).mp hActPi) (hACond a ha)
        ((hCandidates a).mp (hAD a ha)).2.2.1 (hActCode a z haz)⟩
  obtain ⟨nu,hMix⟩ := ForcingMixName.exists_mix hM (orderFormula (rho 0) mul) env (env (rho 6)) A f act
  obtain ⟨hNuHS,hNuSupport⟩ := ForcingEquivariantMix.fixed_and_HS hM env rho mul hPres hG hNormal
    hGroup hHF hFamily hPerm hMix
  have hActivations : ForcingMixLaws.Activations (env (rho 6)) A act :=
    fun a z ha haz => ForcingSupportingRoot.code_mem hPres (hACond a ha) hq (hActCode a z haz)
  have hCoherent : ForcingMixLaws.Coherent (orderFormula (rho 0) mul) env (env (rho 6)) A f act := by
    intro a b sigma tau za zb t ha hb hfa hfb haz hbz ht hta htb
    obtain ⟨dr,r,zr,hdr,hr,hzr,hzrt⟩ := ForcingLabelDensity.exists_condition_below hM hPres hm hq ht
    have hzrW := ForcingSupportingRoot.code_mem hPres hdr hr hzr
    have hzrT := (orderFormula_semantics env (rho 0) mul zr t).mpr hzrt
    have hzrA := hpre.2 zr t za hzrW ht (hActivations a za ha haz) hzrT hta
    have hzrB := hpre.2 zr t zb hzrW ht (hActivations b zb hb hbz) hzrT htb
    have hab := hAnti a ha b hb dr hdr
      ((ForcingSupportingRoot.code_le hzr (hActCode a za haz)).mp
        ((orderFormula_semantics env (rho 0) mul zr za).mp hzrA)).1
      ((ForcingSupportingRoot.code_le hzr (hActCode b zb hbz)).mp
        ((orderFormula_semantics env (rho 0) mul zr zb).mp hzrB)).1
    subst b
    have heq := ForcingConditionGraphs.function_unique hFn hfa hfb
    subst tau
    exact ForcingAtomicBasic.eq_refl hM hpre sigma t ht
  obtain ⟨out,hOut⟩ := ForcingSupportingRoot.exists_code hM (env d0) (env q)
  have hOutW := ForcingSupportingRoot.code_mem hPres hd0 hq hOut
  refine ⟨nu,out,hNuHS,hNuSupport,hOut,?_⟩
  apply ForcingFormula.of_dense hM hpre phi (Fin.lastCases nu (fun j => env (v j))) hOutW
  intro t ht hto
  obtain ⟨dr,r,zr,hdr,hr,hzr,hzrt⟩ := ForcingLabelDensity.exists_condition_below hM hPres hm hq ht
  have hzrW := ForcingSupportingRoot.code_mem hPres hdr hr hzr
  have hzrT := (orderFormula_semantics env (rho 0) mul zr t).mpr hzrt
  have hzrOut := hpre.2 zr t out hzrW ht hOutW hzrT hto
  obtain ⟨hd0dr,hrq⟩ := (ForcingSupportingRoot.code_le hzr hOut).mp
    ((orderFormula_semantics env (rho 0) mul zr out).mp hzrOut)
  obtain ⟨c,hc,hRestrC,hWithinC⟩ := ConstructionCohenCompatibility.exists_restrict hM hdr (env Jq)
  have hc0 := subset_restrict hPres.1 hPres.2.1 hJq hd0 hd0q hd0dr hRestrC
  have hcq : ForcingLocalRecordPullback.Supported (env (rho 0)) (env q) c :=
    fun i j bit he => (hJq i).mp (hWithinC i j bit he)
  let other : Fin (k+1) → M.Carrier .set := Fin.cases c env
  have he j : other j.succ = env j := rfl
  have hf' := (force_reindex env other Fin.succ he rho G F mul (.ex phi) (fun j => env (v j)) (env z0)).mp hf
  obtain ⟨d,witness,zd,hd,hcd,hdq,hWHS,hWSupport,hzd,hWForce⟩ :=
    ForcingLocalizedExistential.localized_existential hM hChoice other (fun j => (rho j).succ)
      w.succ mu.succ history.succ kappa.succ unit.succ mark.succ H.succ C.succ incoming.succ base.succ
      I.succ K.succ B.succ G.succ F.succ mul.succ index.succ p.succ q.succ d0.succ 0 Jp.succ Hp.succ Jq.succ Hq.succ z0.succ
      phi (fun j => env (v j)) hw hMu hI hD hCard hMergers hRow hm hPres hG hFilter hMark hProbes hIndex hp hq hSubQ
      hJp hHp hJq hHq hv hd0 hc hc0 hcq hz0 hf'
  have hWForce' := (force_reindex env other Fin.succ he rho G F mul phi (Fin.lastCases witness (fun j => env (v j))) zd).mpr hWForce
  have hdD : (Project.FirstOrderSemantics.reduct M).mem d D := (hCandidates d).mpr
    ⟨hd,fun z hz => hcd z (hc0 z hz),hdq,witness,hWHS,hWSupport,zd,hzd,hWForce'⟩
  obtain ⟨a,b,ha,hb,hdb,hab⟩ := hPred d hdD
  obtain ⟨bR,hbR,hRestrB,hWithinB⟩ := ConstructionCohenCompatibility.exists_restrict hM hb (env Jq)
  have hcbR := subset_restrict hPres.1 hPres.2.1 hJq hc hcq (fun z hz => hdb z (hcd z hz)) hRestrB
  have habR := subset_restrict hPres.1 hPres.2.1 hJq (hACond a ha)
    ((hCandidates a).mp (hAD a ha)).2.2.1 hab hRestrB
  have hCompatible := compatible_root hM hPres.1 hPres.2.1 hdr hbR hRestrC hWithinB hcbR
  obtain ⟨s,hs,_,hdrs,hbRs⟩ := ConstructionCohenCompatibility.exists_union hM hw hdr hbR hCompatible
  obtain ⟨sigma,hfa,_⟩ := hFn.2 a ha
  obtain ⟨za,haza,_⟩ := hActFn.2 a ha
  have hZaW := hActivations a za ha haza
  have hZaCode := hActCode a za haza
  obtain ⟨zSelected,hZSelected,hForceSelected⟩ := (hSelected a sigma hfa).2.2
  have hCodeEq := code_unique hM hZSelected hZaCode
  have hForceSigma : Force (orderFormula (rho 0) mul) (domain rho G F) env
      (Fin.lastCases sigma (fun j => env (v j))) (env (rho 6)) za phi := hCodeEq ▸ hForceSelected
  obtain ⟨z,hz⟩ := ForcingSupportingRoot.exists_code hM s r
  have hzW := ForcingSupportingRoot.code_mem hPres hs hr hz
  have hzZa := (orderFormula_semantics env (rho 0) mul z za).mpr
    ((ForcingSupportingRoot.code_le hz hZaCode).mpr ⟨fun x hx => hbRs x (habR x hx),hrq⟩)
  have hzZr := (orderFormula_semantics env (rho 0) mul z zr).mpr
    ((ForcingSupportingRoot.code_le hz hzr).mpr ⟨hdrs,ForcingDiagramPoset.le_refl hm hr⟩)
  have hzT := hpre.2 z zr t hzW hzrW ht hzZr hzrT
  have hEq := ForcingAtomicBasic.eq_mono hM hpre hzW hzZa
    (ForcingMixLaws.eq_at hM hpre hActivations hMix hCoherent ha hfa haza)
  have hVec : ∀ j, ForcingAtomicRelations.Forces true (orderFormula (rho 0) mul) env (env (rho 6))
      (Fin.lastCases nu (fun j => env (v j)) j) (Fin.lastCases sigma (fun j => env (v j)) j) z := by
    intro j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [Fin.lastCases_last] using hEq
    · simpa only [Fin.lastCases_castSucc] using ForcingAtomicBasic.eq_refl hM hpre (env (v j)) z hzW
  exact ⟨z,hzW,hzT,(ForcingFormula.tuple_congr hM hpre phi _ _ z hzW hVec).mpr
    (ForcingFormula.mono hM hpre phi _ hZaW hzW hzZa hForceSigma)⟩

/-- Original conclusion at exactly d0 and q; no further Cohen strengthening
or bound on the quantified witness's rank is inserted. -/
def resultFormula {k n : Nat} (rho : Fin 7 → Fin k) (G F q Hq d0 mul : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1)) : Project.Formula 1 k :=
  let up : Fin k → Fin (k+2) := fun j => j.succ.succ
  .existsE (.existsE
    (.conj (ProjectSyntax.encode id (ForcingHS.hs actionFormula (fun j => up (rho j)) (up G) (up (rho 6)) (up F) 1))
      (.conj (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll (fun j => up (rho j)) (up Hq) 1))
        (.conj (ProjectSyntax.encode id (ForcingSupportingRoot.code 0 (up d0) (up q)))
          (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) up
            (Fin.lastCases 1 (fun j => up (v j))) (up (rho 6)) 0 phi))))))

theorem resultFormula_freeClosed {k n : Nat} (rho : Fin 7 → Fin k) (G F q Hq d0 mul : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1)) :
    (resultFormula rho G F q Hq d0 mul v phi).FreeClosed := by
  simp -implicitDefEqProofs [resultFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem resultFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) k) (rho : Fin 7 → Fin k) (G F q Hq d0 mul : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1)) :
    Project.Formula.satisfies env (resultFormula rho G F q Hq d0 mul v phi) ↔
      ∃ nu out, ForcingHS.HS actionFormula (fun j => env.bound (rho j)) (env.bound G) (env.bound (rho 6)) (env.bound F) nu ∧
        Supported (fun j => env.bound (rho j)) (env.bound Hq) nu ∧ Code out (env.bound d0) (env.bound q) ∧
        Force (orderFormula (rho 0) mul) (domain rho G F) env.bound
          (Fin.lastCases nu (fun j => env.bound (v j))) (env.bound (rho 6)) out phi := by
  simp only [resultFormula,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingHS.hs_semantics (M := M),ForcingSupportedNames.supported_semantics (M := M),
    ForcingSupportingRoot.code_semantics (M := M),ForcingFormula.formula_semantics (M := M)]
  simp only [id_eq,SetTheory.Env.push,Fin.cases_succ,Fin.cases_zero,lastCases_map]
  rfl

def sentence {k n : Nat} (rho : Fin 7 → Fin k) (w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 Jp Hp Jq Hq z0 : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1)) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
      (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu))
      (.imp (ConstructionSaturationIndex.hartogs mu I)
      (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu))
      (.imp (ConstructionSaturationCardinals.cardinalsF (rho 0) mul mark mu)
      (.imp (ConstructionSaturationMergers.allMergers w history kappa)
      (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul unit mark H C incoming base kappa)
      (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul unit))
      (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G))
      (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F))
      (.imp (.mem (.bound mark) (.bound (rho 0)))
      (.imp (ForcingRootProbes.rootProbes index (rho 0) mul unit mark)
      (.imp (.neg (ProjectSyntax.encode id (ForcingSupportSize.small index w)))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection p (rho 0) I))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I))
      (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (rho 0) mul q mark p))
      (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) p Jp))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Jp Hp))
      (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q Jq))
      (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Jq Hq))
      (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.tupleSupported rho Hp v))
      (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (rho 2) w d0))
      (.imp (ForcingLocalRecordPullback.supported (rho 0) q d0)
      (.imp (ProjectSyntax.encode id (ForcingSupportingRoot.code z0 d0 p))
      (.imp (ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) mul) (domain rho G F) id v (rho 6) z0 (.ex phi)))
      (resultFormula rho G F q Hq d0 mul v phi)))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isInfiniteCardinal,ConstructionSaturationIndex.hartogs_freeClosed,
      ConstructionSaturationCardinals.cardinalsF_freeClosed,ConstructionSaturationMergers.allMergers_freeClosed,
      ConstructionTowerHistory.row_freeClosed,ForcingRootProbes.rootProbes_freeClosed,
      ForcingLocalRecordPullback.supported_freeClosed,resultFormula_freeClosed]

theorem models {k n : Nat} (rho : Fin 7 → Fin k) (w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 Jp Hp Jq Hq z0 : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1))
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (sentence rho w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 Jp Hp Jq Hq z0 v phi)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionSaturationIndex.hartogs_semantics hM,ConstructionSaturationCardinals.cardinalsF_semantics hM,
    ConstructionSaturationMergers.allMergers_semantics hM,ConstructionTowerHistory.row_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.small_semantics (M := M),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),ForcingSupportFilter.filter_semantics (M := M),
    ForcingRootProbes.rootProbes_semantics hM,ForcingSupportSize.injection_semantics (M := M),
    ForcingDiagramOrder.sub_semantics (M := M),ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),ForcingSupportingRoot.tupleSupported_semantics (M := M),
    ForcingCohenConditions.condition_semantics (M := M),ForcingLocalRecordPullback.supported_semantics hM,
    ForcingSupportingRoot.code_semantics (M := M),ForcingFormula.formula_semantics (M := M),resultFormula_semantics hM]
  intro hw hMu hI hD hCard hMergers hRow hm hPres hG hFilter hMark hProbes hIndex hp hq hSubQ
    hJp hHp hJq hHq hv hd0 hd0q hz0 hf
  exact localized_maximum hM hChoice env rho w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 Jp Hp Jq Hq z0 phi v
    hw hMu hI hD hCard hMergers hRow hm hPres hG hFilter hMark hProbes hIndex hp hq hSubQ
    hJp hHp hJq hHq hv hd0 hd0q hz0 hf

/-- Ordinary native ZF's original proof kernel; existing internal L discharges
ground Choice. Actual ACwo and internal Con are subsequent source consumers. -/
theorem kernel_certificate {k n : Nat} (rho : Fin 7 → Fin k) (w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 Jp Hp Jq Hq z0 : Fin k)
    (v : Fin n → Fin k) (phi : Formula (n+1)) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (sentence rho w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 Jp Hp Jq Hq z0 v phi))) := by
  apply ModelTransfer.derives
  intro N hN
  have hL := ConstructibleSource.model_zf hN
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hN)
  obtain ⟨witness,_⟩ := ZF.exists_omega (ModelTransfer.project_models_iff.mp hL)
  let env : Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hN)) 0 := ⟨Fin.elim0,fun _ => witness⟩
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hN
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hL) _).mp
    (models rho w mu history kappa unit mark H C incoming base I K B G F mul index p q d0 Jp Hp Jq Hq z0 v phi hL hChoice)

end PPAC.Migration.ForcingLocalizedMaximum

