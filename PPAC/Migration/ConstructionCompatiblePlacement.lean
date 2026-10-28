/- Pinned ProductForcing.compatible_placement:149.
Actual consumer: ChoiceFailure.forces_at_supporting_root and
LocalQuotients.active_equal. Reuse native placement extension, existing
diagram amalgamation and Cohen union; no supplied output permutation/lower bound. -/
import PPAC.Migration.ConstructionDescentPlacement

namespace PPAC.Migration.ConstructionCompatiblePlacement
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (Injection Small)
open ForcingConditionGraphs (Permutation CompositionGraph)
open ForcingCohenCoordinates (Cartesian)
open ForcingCohenConditions (Condition)
open ForcingStabilizerTransport (Image)
open ConstructionPlacementTriple (ImageAt)
open ConstructionDiagramPlacements (FixesRange RangeIntersection)
open ConstructionCohenCompatibility (Restricted Compatible Entry)
open ConstructionDescentPlacement (ActualMoved diagram_range range_antitone range_permute)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def RootCompatible (D p d0 d1 : M.Carrier .set) : Prop :=
  ∃ A r0 r1, Image p D A ∧ Restricted A d0 r0 ∧ Restricted A d1 r1 ∧ Compatible r0 r1

def Inputs (I K CC B S w D mul p s0 s1 d0 d1 : M.Carrier .set) : Prop :=
  Cartesian I K CC ∧ Cartesian CC B S ∧ Injection D I p ∧ Injection D I s0 ∧
    Injection D I s1 ∧ ForcingDiagramOrder.Le D mul s0 p ∧ ForcingDiagramOrder.Le D mul s1 p ∧
    Condition S w d0 ∧ Condition S w d1 ∧ RootCompatible D p d0 d1

def Result (D I mul CC S w p s0 s1 d0 d1 pi q : M.Carrier .set) : Prop :=
  Permutation I pi ∧ FixesRange D p pi ∧
    ∃ s1P d1P a t c0 c1,
      Injection D I s1P ∧ CompositionGraph D pi s1 s1P ∧ RangeIntersection D s0 s1P p ∧
      ActualMoved CC S w pi d1 d1P ∧ Condition S w a ∧ Injection D I t ∧
      PureKuratowski.Code M q a t ∧ PureKuratowski.Code M c0 d0 s0 ∧ PureKuratowski.Code M c1 d1P s1P ∧
      ForcingProductAction.Le D mul q c0 ∧ ForcingProductAction.Le D mul q c1

theorem compatible_placement (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w mu history kappa D mul e mark H C incoming base I K B CC S p s0 s1 d0 d1 : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hD : Small D mu) (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa D mul e mark H C incoming base kappa)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (h : Inputs I K CC B S w D mul p s0 s1 d0 d1) :
    ∃ pi q, Result D I mul CC S w p s0 s1 d0 d1 pi q := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨hC,hS,hp,hs0,hs1,hs0p,hs1p,hd0,hd1,A,r0,r1,hA,hR0,hR1,hRoot⟩ := h
  obtain ⟨A',hA',hAI,hASmall⟩ := diagram_range hM hMu.1.1 hp hD
  have hEqA := ForcingCohenOrderAction.image_unique hM hA' hA
  subst A'
  obtain ⟨A0,hA0,hA0I,hA0Small⟩ := diagram_range hM hMu.1.1 hs0 hD
  obtain ⟨A1,hA1,hA1I,hA1Small⟩ := diagram_range hM hMu.1.1 hs1 hD
  obtain ⟨V0,hV0,hV0I,hV0Small⟩ := ConstructionCohenCompatibility.exists_support hM hw hC hS hd0
  obtain ⟨V1,hV1,hV1I,hV1Small⟩ := ConstructionCohenCompatibility.exists_support hM hw hC hS hd1
  have liftSmall {V : M.Carrier .set} (hV : Small V w) : Small V mu := by
    obtain ⟨toW,hToW⟩ := (ForcingSupportSize.native_small hM V w).mp hV
    obtain ⟨toMu,hToMu⟩ := hMu.2
    exact (ForcingSupportSize.native_small hM V mu).mpr
      (ZF.exists_compositionInjection hZF pair hToW hToMu)
  obtain ⟨source,hSource⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) A1 V1
  obtain ⟨avoid,hAvoid⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) A0 V0
  have hSourceI : (Project.FirstOrderSemantics.reduct M).MemberSubset source I :=
    fun z hz => ((hSource z).mp hz).elim (hA1I z) (hV1I z)
  have hAvoidI : (Project.FirstOrderSemantics.reduct M).MemberSubset avoid I :=
    fun z hz => ((hAvoid z).mp hz).elim (hA0I z) (hV0I z)
  have unionSmall {X Y Z : M.Carrier .set} (hX : Small X mu) (hY : Small Y mu)
      (hZ : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z Z ↔
        (Project.FirstOrderSemantics.reduct M).mem z X ∨ (Project.FirstOrderSemantics.reduct M).mem z Y) :
      Small Z mu :=
    (ForcingSupportSize.native_small hM Z mu).mpr
      (ExistingCardinalBounds.infinite_union_two_l pair hZF hw hMu
        ((ForcingSupportSize.native_small hM X mu).mp hX)
        ((ForcingSupportSize.native_small hM Y mu).mp hY) hZ)
  obtain ⟨identity,hId,hIdentity⟩ := ForcingConditionGraphs.exists_identity hM A
  have hIdAI : Injection A I identity :=
    ⟨⟨hId.1.1,fun x y hxy => hAI y (hId.1.2 x y hxy)⟩,hId.2.1⟩
  have hLarge : ¬ Small I mu := fun hi => hI.not_cardinalLessOrEqual (ZF.modelsKP hZF)
    ((ForcingSupportSize.native_small hM I mu).mp hi)
  obtain ⟨pi,hpi,hExtend,hOff⟩ := ConstructionPlacementExtensions.extend_permutation_off hM hChoice
    hw hMu hLarge hAI hSourceI hAvoidI hASmall
    (unionSmall hA1Small (liftSmall hV1Small) hSource)
    (unionSmall hA0Small (liftSmall hV0Small) hAvoid)
    ((ForcingSupportSize.native_injection hM A I identity).mp hIdAI)
  have hFix : ForcingLabelPermutations.Fixes A pi :=
    fun z hz => hExtend z z ((hIdentity z z).mpr ⟨hz,rfl⟩)
  have hFixRange : FixesRange D p pi := fun z hz => hFix z ((hA z).mpr hz)
  obtain ⟨s1P,hS1P,hPerm⟩ := ForcingDiagramAction.exists_permute hM hpi hs1
  have hPiP : CompositionGraph D pi p p := by
    intro x z
    constructor
    · intro hxz
      have hx := ForcingConditionGraphs.function_input hp.1.1 hxz
      exact ⟨hx,z,hxz,hFixRange z ⟨x,hx,hxz⟩⟩
    · rintro ⟨hx,y,hxy,hyz⟩
      have he := ForcingConditionGraphs.function_unique hpi.1.1 hyz (hFixRange y ⟨x,hx,hxy⟩)
      exact he.symm ▸ hxy
  have hS1Pp : ForcingDiagramOrder.Le D mul s1P p :=
    (ForcingDiagramOrder.le_iff hM hpi hs1 hp hPerm hPiP).mp hs1p
  have hInter : RangeIntersection D s0 s1P p := by
    intro z
    constructor
    · rintro ⟨hz0,hz1⟩
      obtain ⟨x,hx,hxz⟩ := (range_permute hA1 hPerm).mp hz1
      have hxA : (Project.FirstOrderSemantics.reduct M).mem x A := by
        apply Classical.byContradiction
        intro hnot
        exact hOff x z ((hSource x).mpr (Or.inl hx)) hnot hxz
          ((hAvoid z).mpr (Or.inl ((hA0 z).mpr hz0)))
      have he := ForcingConditionGraphs.function_unique hpi.1.1 hxz (hFix x hxA)
      exact he.symm ▸ (hA x).mp hxA
    · intro hz
      exact ⟨range_antitone hs0p hz,range_antitone hS1Pp hz⟩
  have hOverlap := ConstructionDiagramPlacements.exactOverlap_of_common hp hs0p hS1Pp hInter
  have hRefl := ForcingDiagramPoset.le_refl hm hS1P
  obtain ⟨t,ht,ht0,ht1,_⟩ := ConstructionDiagramThree.common_extension_three hM hChoice
    hw hMu hI hD hMergers hRow hm hs0 hS1P hS1P hOverlap hOverlap
    (ConstructionDiagramPlacements.exactOverlap_of_common hS1P hRefl hRefl
      (fun _ => ⟨fun h => h.1,fun h => ⟨h,h⟩⟩))
  obtain ⟨f,g,d1P,hf,hfg,hg,hgg,hd1P,hImage,hMoved⟩ :=
    ConstructionCohenCompatibility.exists_moved hM hC hS hpi hd1
  have hCompatible : Compatible d0 d1P := by
    apply ConstructionCohenCompatibility.compatible_of_entries hC hS hd0
    intro j k b c he0 heP
    obtain ⟨i,hij,he1⟩ := (hMoved j k c).mp heP
    have hiA : (Project.FirstOrderSemantics.reduct M).mem i A := by
      apply Classical.byContradiction
      intro hnot
      exact hOff i j ((hSource i).mpr (Or.inr ((hV1 i).mpr ⟨k,c,he1⟩))) hnot hij
        ((hAvoid j).mpr (Or.inr ((hV0 j).mpr ⟨k,b,he0⟩)))
    have hijEq := ForcingConditionGraphs.function_unique hpi.1.1 hij (hFix i hiA)
    subst j
    have er0 := ConstructionCohenCompatibility.restricted_entry hR0 |>.mpr ⟨he0,hiA⟩
    have er1 := ConstructionCohenCompatibility.restricted_entry hR1 |>.mpr ⟨he1,hiA⟩
    obtain ⟨a,ha,ea⟩ := er0
    obtain ⟨a',ha',ea'⟩ := er1
    have he := KuratowskiZF.code_unique hM ha' ha
    exact hRoot a b c ea (he ▸ ea')
  obtain ⟨a,ha,_,h0a,h1a⟩ := ConstructionCohenCompatibility.exists_union hM hw hd0 hd1P hCompatible
  obtain ⟨q,hq⟩ := KuratowskiZF.exists_code hM a t
  obtain ⟨c0,hc0⟩ := KuratowskiZF.exists_code hM d0 s0
  obtain ⟨c1,hc1⟩ := KuratowskiZF.exists_code hM d1P s1P
  exact ⟨pi,q,hpi,hFixRange,s1P,d1P,a,t,c0,c1,hS1P,hPerm,hInter,
    ⟨f,g,hf,hfg,hg,hgg,hd1P,hImage,hMoved⟩,ha,ht,hq,hc0,hc1,
    ⟨a,t,d0,s0,hq,hc0,h0a,ht0⟩,⟨a,t,d1P,s1P,hq,hc1,h1a,ht1⟩⟩


def compatible {m : Nat} (p q : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge p.succ.succ.succ 2 1))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge q.succ.succ.succ 2 0))
        (Project.Formula.extensionalEq (.bound 1) (.bound 0))))))

theorem compatible_freeClosed {m : Nat} (p q : Fin m) : (compatible p q).FreeClosed := by
  simp -implicitDefEqProofs [compatible,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq]

theorem compatible_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (p q : Fin m) :
    Project.Formula.satisfies env (compatible p q) ↔ Compatible (env.bound p) (env.bound q) := by
  simp only [compatible,Compatible,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  rfl

def rootCompatible {m : Nat} (D p d0 d1 : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE
    (.conj (ProjectSyntax.encode id (ForcingStabilizerTransport.image p.succ.succ.succ D.succ.succ.succ 2))
      (.conj (ConstructionCohenCompatibility.restricted 2 d0.succ.succ.succ 1)
        (.conj (ConstructionCohenCompatibility.restricted 2 d1.succ.succ.succ 0) (compatible 1 0))))))

theorem rootCompatible_freeClosed {m : Nat} (D p d0 d1 : Fin m) : (rootCompatible D p d0 d1).FreeClosed := by
  simp -implicitDefEqProofs [rootCompatible,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionCohenCompatibility.restricted_freeClosed,compatible_freeClosed]

theorem rootCompatible_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D p d0 d1 : Fin m) :
    Project.Formula.satisfies env (rootCompatible D p d0 d1) ↔
      RootCompatible (env.bound D) (env.bound p) (env.bound d0) (env.bound d1) := by
  simp only [rootCompatible,RootCompatible,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingStabilizerTransport.image_semantics (M := M),
    ConstructionCohenCompatibility.restricted_semantics hM,compatible_semantics hM]
  rfl

def inputs {m : Nat} (I K CC B S w D mul p s0 s1 d0 d1 : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K CC)) (.conj (ProjectSyntax.encode id
    (ForcingCohenCoordinates.cartesian CC B S)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection p D
    I)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection s0 D I)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.injection s1 D I)) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.le D mul s0 p))
    (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.le D mul s1 p)) (.conj (ProjectSyntax.encode id
    (ForcingCohenConditions.condition S w d0)) (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition S
    w d1)) (rootCompatible D p d0 d1))))))))))

theorem inputs_freeClosed {m : Nat} (I K CC B S w D mul p s0 s1 d0 d1 : Fin m) :
    (inputs I K CC B S w D mul p s0 s1 d0 d1).FreeClosed := by
  simp -implicitDefEqProofs [inputs,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,rootCompatible_freeClosed]

theorem inputs_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (I K CC B S w D mul p s0 s1 d0 d1 : Fin m) :
    Project.Formula.satisfies env (inputs I K CC B S w D mul p s0 s1 d0 d1) ↔
      Inputs (env.bound I) (env.bound K) (env.bound CC) (env.bound B) (env.bound S) (env.bound w)
        (env.bound D) (env.bound mul) (env.bound p) (env.bound s0) (env.bound s1) (env.bound d0) (env.bound d1) := by
  simp only [inputs,Inputs,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingDiagramOrder.le_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    rootCompatible_semantics hM]
  rfl

def result {m : Nat} (D I mul CC S w p s0 s1 d0 d1 pi q : Fin m) : Project.Formula 1 m :=
  let up : Fin m → Fin (m+6) := fun i => i.succ.succ.succ.succ.succ.succ
  (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I pi)) (.conj
    (ConstructionDiagramPlacements.fixesRange D p pi) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection 5 (up D) (up I))) (.conj (ProjectSyntax.encode id
    (ForcingConditionGraphs.compositionGraph (up D) (up pi) (up s1) 5)) (.conj
    (ConstructionDiagramPlacements.rangeIntersection (up D) (up s0) 5 (up p)) (.conj
    (ConstructionDescentPlacement.actualMoved (up CC) (up S) (up w) (up pi) (up d1) 4) (.conj (ProjectSyntax.encode
    id (ForcingCohenConditions.condition (up S) (up w) 3)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.injection 2 (up D) (up I))) (.conj (PureKuratowskiProject.code (.bound (up q)) (.bound 3)
    (.bound 2)) (.conj (PureKuratowskiProject.code (.bound 1) (.bound (up d0)) (.bound (up s0))) (.conj
    (PureKuratowskiProject.code (.bound 0) (.bound 4) (.bound 5)) (.conj (ProjectSyntax.encode id
    (ForcingProductAction.le (up D) (up mul) (up q) 1)) (ProjectSyntax.encode id (ForcingProductAction.le (up D)
    (up mul) (up q) 0))))))))))))))))))))

theorem result_freeClosed {m : Nat} (D I mul CC S w p s0 s1 d0 d1 pi q : Fin m) :
    (result D I mul CC S w p s0 s1 d0 d1 pi q).FreeClosed := by
  simp -implicitDefEqProofs [result,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionDiagramPlacements.fixesRange_freeClosed,ConstructionDiagramPlacements.rangeIntersection_freeClosed,
    ConstructionDescentPlacement.actualMoved_freeClosed,PureKuratowskiProject.code]

theorem result_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul CC S w p s0 s1 d0 d1 pi q : Fin m) :
    Project.Formula.satisfies env (result D I mul CC S w p s0 s1 d0 d1 pi q) ↔
      Result (env.bound D) (env.bound I) (env.bound mul) (env.bound CC) (env.bound S) (env.bound w)
        (env.bound p) (env.bound s0) (env.bound s1) (env.bound d0) (env.bound d1) (env.bound pi) (env.bound q) := by
  simp only [result,Result,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),ConstructionDescentPlacement.actualMoved_semantics hM,
    ConstructionDiagramPlacements.fixesRange_semantics hM,ConstructionDiagramPlacements.rangeIntersection_semantics hM,
    ForcingCohenConditions.condition_semantics (M := M),KuratowskiZF.code_correct hM,
    ForcingProductAction.le_semantics (M := M),Project.Term.eval_bound]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 22
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 22))) (.imp (Project.Formula.isInfiniteCardinal
    PureKuratowskiProject.convention (.bound (0 : Fin 22)) (.bound 1)) (.imp (ConstructionSaturationIndex.hartogs
    (1 : Fin 22) 12) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (4 : Fin 22) 1)) (.imp
    (ConstructionSaturationMergers.allMergers (0 : Fin 22) 2 3) (.imp (ConstructionTowerHistory.row (2 : Fin 22) 3
    4 5 6 7 8 9 10 11 3) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (4 : Fin 22) 5 6))
    (.imp (inputs (12 : Fin 22) 13 15 14 16 0 4 5 17 18 19 20 21) (.existsE (.existsE (result (4 : Fin
    22).succ.succ (12 : Fin 22).succ.succ (5 : Fin 22).succ.succ (15 : Fin 22).succ.succ (16 : Fin 22).succ.succ (0
    : Fin 22).succ.succ (17 : Fin 22).succ.succ (18 : Fin 22).succ.succ (19 : Fin 22).succ.succ (20 : Fin
    22).succ.succ (21 : Fin 22).succ.succ 1 0)))))))))))

  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,ConstructionSaturationIndex.hartogs_freeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,
      inputs_freeClosed,result_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    inputs_semantics hM,result_semantics hM,Project.Term.eval_bound]
  exact fun hw hMu hI hD hMergers hRow hm h =>
    compatible_placement hM hChoice hw hMu hI hD hMergers hRow hm h

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
    (ModelTransfer.extensionality hL) constructionSentence).mp (construction_models hL hChoice)

end PPAC.Migration.ConstructionCompatiblePlacement
