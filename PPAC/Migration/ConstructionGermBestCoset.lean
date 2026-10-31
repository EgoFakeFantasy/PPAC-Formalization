/- Pinned GermSelectors.bestCoset/minimal/covariance. Minimize actual
pattern values in the SAME fixed internal wellorder; use the existing native
unique-minimum interface. Injectivity makes the selected germ class unique. -/
import PPAC.Migration.ConstructionGermLeastBound
import PPAC.Migration.InternalWellOrderChoice

namespace PPAC.Migration.ConstructionGermBestCoset
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (Permutation CompositionGraph function_input function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Best (G order F c : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem c G ∧ ∃ P, PureKuratowski.PairMember M c P F ∧
    ∀ d Q, PureKuratowski.PairMember M d Q F → ¬ PureKuratowski.PairMember M Q P order

def best {m : Nat} (G order F c : Fin m) : Project.Formula 1 m :=
  .conj (.mem (.bound c) (.bound G)) (.existsE
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ c.succ 0))
      (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ 1 0))
        (.neg (ProjectSyntax.encode id (Source.SetLanguage.edge order.succ.succ.succ 0 2))))))))

theorem best_freeClosed {m : Nat} (G order F c : Fin m) : (best G order F c).FreeClosed := by
  simp -implicitDefEqProofs [best,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem best_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (G order F c : Fin m) :
    Project.Formula.satisfies env (best G order F c) ↔ Best (env.bound G) (env.bound order) (env.bound F) (env.bound c) := by
  simp only [best,Best,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

theorem exists_best (hM : FirstOrder.Theory.Models M nativeZF) {G T O order F : M.Carrier .set}
    (hF : MapsTo G T F) (hTO : (Project.FirstOrderSemantics.reduct M).MemberSubset T O)
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) order O)
    (hNonempty : ∃ c, (Project.FirstOrderSemantics.reduct M).mem c G) : ∃ c, Best G order F c := by
  have hNative := (ForcingSupportSize.native_mapsTo hM G T F).mp hF
  obtain ⟨image,hImage⟩ := ZF.exists_range_of_setFunction (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) hNative.1 hNative.2.1
  have hImageO : (Project.FirstOrderSemantics.reduct M).MemberSubset image O := by
    intro P hP
    obtain ⟨c,hcP⟩ := (hImage P).mp hP
    exact hTO P (hF.2 c P hcP)
  obtain ⟨c,hc⟩ := hNonempty
  obtain ⟨P,hcP,_⟩ := hF.1.2 c hc
  obtain ⟨least,hLeast,_⟩ := InternalWellOrderChoice.unique_minimum hM hOrder hImageO ⟨P,(hImage P).mpr ⟨c,hcP⟩⟩
  obtain ⟨hLeastImage,hMin⟩ := (InternalWellOrderChoice.least_graph hM order image least).mp hLeast
  obtain ⟨best,hBest⟩ := (hImage least).mp hLeastImage
  exact ⟨best,function_input hF.1 hBest,least,hBest,fun d Q hdQ => hMin Q ((hImage Q).mpr ⟨d,hdQ⟩)⟩

theorem best_unique (hM : FirstOrder.Theory.Models M nativeZF) {G T O order F c d : M.Carrier .set}
    (hF : Injection G T F) (hTO : (Project.FirstOrderSemantics.reduct M).MemberSubset T O)
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) order O)
    (hc : Best G order F c) (hd : Best G order F d) : c = d := by
  obtain ⟨_,P,hcP,hMinP⟩ := hc
  obtain ⟨_,Q,hdQ,hMinQ⟩ := hd
  rcases hOrder.linear.2.2 P (hTO P (hF.1.2 c P hcP)) Q (hTO Q (hF.1.2 d Q hdQ)) with eq | lt | gt
  · have e := (ModelTransfer.extensionality hM).eq_of_same_members P Q eq
    subst Q
    exact hF.2 c d P hcP hdQ
  · exact (hMinQ c P hcP lt).elim
  · exact (hMinP d Q hdQ gt).elim

theorem best_moved {G T F Q act order c e : M.Carrier .set}
    (hQ : MapsTo G T Q) (hAct : Permutation G act) (hComp : CompositionGraph G Q act F)
    (hc : Best G order F c) (hce : PureKuratowski.PairMember M c e act) : Best G order Q e := by
  obtain ⟨_,P,hcP,hMin⟩ := hc
  obtain ⟨_,e',hce',he'P⟩ := (hComp c P).mp hcP
  have eq := function_unique hAct.1.1 hce' hce
  subst e'
  refine ⟨hAct.1.2 c e hce,P,he'P,?_⟩
  intro d V hdV
  obtain ⟨b,hb,hbd⟩ := hAct.2.2 d (function_input hQ.1 hdV)
  exact hMin b V ((hComp b V).mpr ⟨hb,d,hbd,hdV⟩)

theorem graph_covariance (hM : FirstOrder.Theory.Models M nativeZF) {G T O order F Q act c e : M.Carrier .set}
    (hF : Injection G T F) (hQ : MapsTo G T Q)
    (hTO : (Project.FirstOrderSemantics.reduct M).MemberSubset T O)
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) order O)
    (hAct : Permutation G act) (hComp : CompositionGraph G Q act F)
    (hc : Best G order F c) (he : Best G order Q e) : PureKuratowski.PairMember M c e act := by
  obtain ⟨e',hce',_⟩ := hAct.1.1.2 c hc.1
  have hBest := best_moved hQ hAct hComp hc hce'
  have hQInj := (ConstructionGermPatternCovariance.injection_iff hF.1 hQ hAct hComp).mpr hF
  have eq := best_unique hM hQInj hTO hOrder hBest he
  exact eq ▸ hce'

theorem pattern_covariance (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act O order c e : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul unit)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul) (hq : Injection D I q)
    (hH : ConstructionGermCosets.Carrier D I mul q root H) (hG : ConstructionGermCosets.Classes w D chain H G)
    (hDet : MapsTo X I det) (hpi : (Project.FirstOrderSemantics.reduct M).mem pi H)
    (hMove : ConstructionCohenCompatibility.Moved pi R U) (hAct : ConstructionGermLeftAction.Action w D I chain H G pi act)
    (hF : ConstructionGermPattern.Pattern w D chain H G N alpha B A E T det R pr F)
    (hQ : ConstructionGermPattern.Pattern w D chain H G N alpha B A E T det U pr Q)
    (hInj : Injection G T F) (hTO : (Project.FirstOrderSemantics.reduct M).MemberSubset T O)
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) order O)
    (hc : Best G order F c) (he : Best G order Q e) : PureKuratowski.PairMember M c e act :=
  graph_covariance hM hInj hQ.1 hTO hOrder hAct.1
    (ConstructionGermPatternCovariance.pattern_covariance hM hm hJ hq hH hG hDet hpi hMove hAct hF hQ) hc he


def existenceSentence {m : Nat} (G T O order F : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo F G T)) (.imp (Project.Formula.subset (.bound T) (.bound O)) (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound O)) (.imp (.existsE (.mem (.bound 0) (.bound G.succ))) (.existsE (best G.succ order.succ F.succ 0))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.subset,best_freeClosed]

theorem existence_models {m : Nat} (G T O order F : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (existenceSentence G T O order F)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (existenceSentence G T O order F)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound,best_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,ForcingSupportSize.mapsTo_semantics (M := M)]
  exact exists_best hM

theorem existence_kernel_certificate {m : Nat} (G T O order F : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (existenceSentence G T O order F)) :=
  ModelTransfer.derives (fun _ hM => existence_models G T O order F hM)

def uniquenessSentence {m : Nat} (G T O order F c d : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection F G T)) (.imp (Project.Formula.subset (.bound T) (.bound O)) (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound O)) (.imp (best G order F c) (.imp (best G order F d) (Project.Formula.extensionalEq (.bound c) (.bound d)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.subset,best_freeClosed,Project.Formula.extensionalEq]

theorem uniqueness_models {m : Nat} (G T O order F c d : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (uniquenessSentence G T O order F c d)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (uniquenessSentence G T O order F c d)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound,best_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ForcingSupportSize.injection_semantics (M := M)]
  exact best_unique hM

theorem uniqueness_kernel_certificate {m : Nat} (G T O order F c d : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (uniquenessSentence G T O order F c d)) :=
  ModelTransfer.derives (fun _ hM => uniqueness_models G T O order F c d hM)

def covarianceSentence {m : Nat} (w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act O order c e : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul unit)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q D I)) (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ConstructionGermCosets.classes w D chain H G) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo det X I)) (.imp (.mem (.bound pi) (.bound H)) (.imp (ConstructionCohenCompatibility.moved pi R U) (.imp (ConstructionGermLeftAction.action w D I chain H G pi act) (.imp (ConstructionGermPattern.pattern w D chain H G N alpha B A E T det R pr F) (.imp (ConstructionGermPattern.pattern w D chain H G N alpha B A E T det U pr Q) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection F G T)) (.imp (Project.Formula.subset (.bound T) (.bound O)) (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound O)) (.imp (best G order F c) (.imp (best G order Q e) (ProjectSyntax.encode id (Source.SetLanguage.edge act c e))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.subset,best_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionGermCosets.carrier_freeClosed,ConstructionGermCosets.classes_freeClosed,ConstructionCohenCompatibility.moved_freeClosed,ConstructionGermLeftAction.action_freeClosed,ConstructionGermPattern.pattern_freeClosed]

theorem covariance_models {m : Nat} (w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act O order c e : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (covarianceSentence w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act O order c e)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (covarianceSentence w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act O order c e)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound,best_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ForcingSupportSize.injection_semantics (M := M),ConstructionGermCosets.carrier_semantics hM,ConstructionGermCosets.classes_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),Project.Formula.satisfies_mem_iff,ConstructionCohenCompatibility.moved_semantics hM,ConstructionGermLeftAction.action_semantics hM,ConstructionGermPattern.pattern_semantics hM,KuratowskiZF.source_edge]
  exact pattern_covariance hM

theorem covariance_kernel_certificate {m : Nat} (w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act O order c e : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (covarianceSentence w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act O order c e)) :=
  ModelTransfer.derives (fun _ hM => covariance_models w D I mul unit q root chain H G N X alpha B A E T det pi R U pr F Q act O order c e hM)

end PPAC.Migration.ConstructionGermBestCoset
