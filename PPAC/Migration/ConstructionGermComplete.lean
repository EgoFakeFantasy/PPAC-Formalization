/- Pinned StableSelectors.Complete.mono/downward and complete_of_covered.
Consume actual countable detector sites and the existing Cohen fill operation.
The bound and every sequence index lie in the model's internal omega. -/
import PPAC.Migration.ConstructionCohenFill
import PPAC.Migration.ConstructionGermDetectorSites

namespace PPAC.Migration.ConstructionGermComplete
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingCohenCoordinates (Cartesian)
open ForcingCohenConditions (Condition)
open ConstructionCohenCompatibility (Entry)
open ConstructionGermCosets (Carrier)
open ConstructionGermDetectors (Detectors)
open ConstructionGermDetectorSites (Covers)
open ConstructionCohenFill (Fill)
open ConstructionFractionOrder (NatLe)
open ForcingSupportSize (Small)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Complete (w H N det alpha p : M.Carrier .set) : Prop := ∀ g,
  (Project.FirstOrderSemantics.reduct M).mem g H → ∀ delta,
  (Project.FirstOrderSemantics.reduct M).mem delta N → ∃ bound,
  (Project.FirstOrderSemantics.reduct M).mem bound w ∧ ∀ n,
  (Project.FirstOrderSemantics.reduct M).mem n w → NatLe bound n → ∀ b,
  (Project.FirstOrderSemantics.reduct M).mem b alpha → ∃ t x y v,
    PureKuratowski.Code M t delta n ∧ PureKuratowski.PairMember M t x det ∧
      PureKuratowski.PairMember M x y g ∧ Entry p y b v

theorem mono {w H N det alpha p r : M.Carrier .set} (h : Complete w H N det alpha p)
    (hle : (Project.FirstOrderSemantics.reduct M).MemberSubset p r) : Complete w H N det alpha r := by
  intro g hg delta hd
  obtain ⟨bound,hbound,h⟩ := h g hg delta hd
  refine ⟨bound,hbound,?_⟩
  intro n hn hbn b hb
  obtain ⟨t,x,y,v,ht,hx,hxy,a,ha,z,hz,hzp⟩ := h n hn hbn b hb
  exact ⟨t,x,y,v,ht,hx,hxy,a,ha,z,hz,hle z hzp⟩

theorem downward {w H N det alpha beta p : M.Carrier .set} (h : Complete w H N det alpha p)
    (hle : (Project.FirstOrderSemantics.reduct M).MemberSubset beta alpha) : Complete w H N det beta p := by
  intro g hg delta hd
  obtain ⟨bound,hbound,h⟩ := h g hg delta hd
  exact ⟨bound,hbound,fun n hn hbn b hb => h n hn hbn b (hle b hb)⟩

theorem complete_of_covered (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q root chain H N X reps det J alpha p : M.Carrier .set}
    (hH : Carrier D I mul q root H) (hDet : Detectors D I chain X reps det)
    (hX : Cartesian N w X) (hCovers : Covers w H det J)
    (hCover : ∀ y b, (Project.FirstOrderSemantics.reduct M).mem y J →
      (Project.FirstOrderSemantics.reduct M).mem b alpha → ∃ v, Entry p y b v) :
    Complete w H N det alpha p := by
  intro g hg delta hd
  obtain ⟨bound,hbound,hCovers⟩ := hCovers g hg
  refine ⟨bound,hbound,?_⟩
  intro n hn hbn b hb
  obtain ⟨t,ht⟩ := KuratowskiZF.exists_code hM delta n
  have htX := (hX t).mpr ⟨delta,hd,n,hn,ht⟩
  obtain ⟨x,hx,_⟩ := hDet.1.1.2 t htX
  obtain ⟨y,hxy,_⟩ := ((hH g).mp hg).1.1.1.2 x (hDet.1.2 t x hx)
  obtain ⟨v,hv⟩ := hCover y b (hCovers delta n t x y ht hx hbn hxy) hb
  exact ⟨t,x,y,v,ht,hx,hxy,hv⟩

theorem fill_complete (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q root chain H N X reps det J alpha A p bit r : M.Carrier .set}
    (hH : Carrier D I mul q root H) (hDet : Detectors D I chain X reps det)
    (hX : Cartesian N w X) (hCovers : Covers w H det J)
    (hA : Cartesian J alpha A) (hFill : Fill A p bit r) : Complete w H N det alpha r := by
  apply complete_of_covered hM hH hDet hX hCovers
  intro y b hy hb
  obtain ⟨a,ha⟩ := KuratowskiZF.exists_code hM y b
  obtain ⟨v,hv⟩ := ConstructionCohenFill.subset_dom_fill hM hFill a ((hA a).mpr ⟨y,hy,b,hb,ha⟩)
  exact ⟨v,a,ha,hv⟩

/-- The actual countable extension used by good_dense after its distinguishing
bit bound is fixed. Existing values are retained, and all needed rows are
assigned for every representative after an internal finite initial segment. -/
theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q root chain H N X reps det J K C B S bit alpha p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hH : Carrier D I mul q root H) (hDet : Detectors D I chain X reps det)
    (hX : Cartesian N w X) (hCovers : Covers w H det J)
    (hJS : Small J w) (hJI : (Project.FirstOrderSemantics.reduct M).MemberSubset J I)
    (hAS : Small alpha w) (hAK : (Project.FirstOrderSemantics.reduct M).MemberSubset alpha K)
    (hC : Cartesian I K C) (hS : Cartesian C B S)
    (hb : (Project.FirstOrderSemantics.reduct M).mem bit B) (hp : Condition S w p) :
    ∃ A r, Cartesian J alpha A ∧ Small A w ∧ Condition S w r ∧ Fill A p bit r ∧
      (Project.FirstOrderSemantics.reduct M).MemberSubset p r ∧ Complete w H N det alpha r := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let P := KuratowskiZF.interpretation hM
  obtain ⟨A,hA⟩ := ForcingCohenCoordinates.exists_cartesian hM J alpha
  obtain ⟨id,hId⟩ := ZF.exists_identityBijection hZF P w
  have hInf : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal P w w :=
    ⟨ExistingCardinalBounds.omega_cardinal_l P hZF hw,id,hId.1⟩
  have hSmall := (ForcingSupportSize.native_small hM A w).mpr
    (ExistingCardinalBounds.infinite_product_l P hZF hw hInf
      ((ForcingSupportSize.native_small hM J w).mp hJS) ((ForcingSupportSize.native_small hM alpha w).mp hAS) hA)
  have hAC : (Project.FirstOrderSemantics.reduct M).MemberSubset A C := by
    intro a ha
    obtain ⟨y,hy,b,hb,hab⟩ := (hA a).mp ha
    exact (hC a).mpr ⟨y,hJI y hy,b,hAK b hb,hab⟩
  obtain ⟨r,hr,hFill⟩ := ConstructionCohenFill.exists_fill hM hw hS hAC hSmall hb hp
  exact ⟨A,r,hA,hSmall,hr,hFill,ConstructionCohenFill.fill_le hFill,
    fill_complete hM hH hDet hX hCovers hA hFill⟩

def complete {m : Nat} (w H N det alpha p : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (.mem (.bound 0) (.bound H.succ)) (.forallE (.imp (.mem (.bound 0) (.bound N.succ.succ)) (.existsE (.conj (.mem (.bound 0) (.bound w.succ.succ.succ)) (.forallE (.imp (.mem (.bound 0) (.bound w.succ.succ.succ.succ)) (.imp (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 0)) (.mem (.bound 1) (.bound 0))) (.forallE (.imp (.mem (.bound 0) (.bound alpha.succ.succ.succ.succ.succ)) (.existsE (.existsE (.existsE (.existsE (.conj (PureKuratowskiProject.code (.bound 3) (.bound 7) (.bound 5)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge det.succ.succ.succ.succ.succ.succ.succ.succ.succ 3 2)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 8 2 1)) (ConstructionCohenCompatibility.entry p.succ.succ.succ.succ.succ.succ.succ.succ.succ 1 4 0)))))))))))))))))))

theorem complete_freeClosed {m : Nat} (w H N det alpha p : Fin m) : (complete w H N det alpha p).FreeClosed := by
  simp -implicitDefEqProofs [complete,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    PureKuratowskiProject.code,Project.Formula.extensionalEq,ConstructionCohenCompatibility.entry_freeClosed]

theorem complete_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w H N det alpha p : Fin m) :
    Project.Formula.satisfies env (complete w H N det alpha p) ↔
      Complete (env.bound w) (env.bound H) (env.bound N) (env.bound det) (env.bound alpha) (env.bound p) := by
  simp only [complete,Complete,NatLe,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_disj_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    KuratowskiZF.code_correct hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,ConstructionCohenCompatibility.entry_semantics hM]
  rfl

def constructionSentence {m : Nat} (w D I mul q root chain H N X reps det J K C B S bit alpha p : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ConstructionGermDetectors.detectors D I chain X reps det) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian N w X)) (.imp (ConstructionGermDetectorSites.coversFormula w H det J) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small J w)) (.imp (Project.Formula.subset (.bound J) (.bound I)) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small alpha w)) (.imp (Project.Formula.subset (.bound alpha) (.bound K)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K C)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian C B S)) (.imp (.mem (.bound bit) (.bound B)) (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S w p)) (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian J.succ.succ alpha.succ.succ 1)) (.conj (ProjectSyntax.encode id (ForcingSupportSize.small 1 w.succ.succ)) (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ.succ w.succ.succ 0)) (.conj (ConstructionCohenFill.fill 1 p.succ.succ bit.succ.succ 0) (.conj (Project.Formula.subset (.bound p.succ.succ) (.bound 0)) (complete w.succ.succ H.succ.succ N.succ.succ det.succ.succ alpha.succ.succ 0)))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,
      Project.Formula.subset,ConstructionGermCosets.carrier_freeClosed,ConstructionGermDetectors.detectors_freeClosed,
      ConstructionGermDetectorSites.coversFormula_freeClosed,ConstructionCohenFill.fill_freeClosed,complete_freeClosed]

theorem construction_models {m : Nat} (w D I mul q root chain H N X reps det J K C B S bit alpha p : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence w D I mul q root chain H N X reps det J K C B S bit alpha p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w D I mul q root chain H N X reps det J K C B S bit alpha p)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_subset_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    ForcingSupportSize.small_semantics (M := M),ConstructionGermCosets.carrier_semantics hM,
    ConstructionGermDetectors.detectors_semantics hM,ConstructionGermDetectorSites.coversFormula_semantics hM,
    ConstructionCohenFill.fill_semantics hM,complete_semantics hM]
  exact construction hM

theorem construction_kernel_certificate {m : Nat} (w D I mul q root chain H N X reps det J K C B S bit alpha p : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (constructionSentence w D I mul q root chain H N X reps det J K C B S bit alpha p)) :=
  ModelTransfer.derives (fun _ hM => construction_models w D I mul q root chain H N X reps det J K C B S bit alpha p hM)

theorem relative_kernel_certificate {m : Nat} (w D I mul q root chain H N X reps det J K C B S bit alpha p : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (constructionSentence w D I mul q root chain H N X reps det J K C B S bit alpha p))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  apply ConstructibleGround.relative_models hM (constructionSentence w D I mul q root chain H N X reps det J K C B S bit alpha p)
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hL)
    (constructionSentence w D I mul q root chain H N X reps det J K C B S bit alpha p)).mp (construction_models w D I mul q root chain H N X reps det J K C B S bit alpha p hL)

end PPAC.Migration.ConstructionGermComplete
