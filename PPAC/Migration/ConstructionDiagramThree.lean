/- Pinned DiagramPlacements.common_extension_three:470.
Encode the source three diagrams as an actual internal ordinal-three family;
consume the existing whole-carrier finite amalgamation without a new backend. -/
import PPAC.Migration.ConstructionDiagramAmalgamation

namespace PPAC.Migration.ConstructionDiagramThree
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (Injection Small)
open ConstructionDiagramPlacements (ExactOverlap)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem three_members (hM : FirstOrder.Theory.Models M nativeZF)
    {w one two three : M.Carrier .set} (hd : ConstructionBaseWeights.Digits w one two three) :
    ∃ zero, zero ≠ one ∧ zero ≠ two ∧ one ≠ two ∧
      ∀ x, (Project.FirstOrderSemantics.reduct M).mem x three ↔ x = zero ∨ x = one ∨ x = two := by
  obtain ⟨zero,hz,hOne⟩ := hd.2.2.2.1
  have hExt := ModelTransfer.extensionality hM
  have hOneMem x : (Project.FirstOrderSemantics.reduct M).mem x one ↔ x = zero := by
    constructor
    · intro h
      rcases (hOne x).mp h with h | h
      · exact False.elim (hz x h)
      · exact hExt.eq_of_same_members x zero h
    · intro h
      subst x
      exact hOne.predecessor_mem
  have hTwoMem x : (Project.FirstOrderSemantics.reduct M).mem x two ↔ x = zero ∨ x = one := by
    constructor
    · intro h
      rcases (hd.2.2.2.2.1 x).mp h with h | h
      · exact Or.inl ((hOneMem x).mp h)
      · exact Or.inr (hExt.eq_of_same_members x one h)
    · rintro (h | h)
      · exact (hd.2.2.2.2.1 x).mpr (Or.inl ((hOneMem x).mpr h))
      · subst x
        exact hd.2.2.2.2.1.predecessor_mem
  have h01 : zero ≠ one := fun h => hz zero (h.symm ▸ hOne.predecessor_mem)
  have h02 : zero ≠ two := fun h => hz one (h.symm ▸ hd.2.2.2.2.1.predecessor_mem)
  have h12 : one ≠ two := by
    intro h
    have hi := KP.mem_irrefl_d (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) one
    exact hi (h.symm ▸ hd.2.2.2.2.1.predecessor_mem)
  refine ⟨zero,h01,h02,h12,fun x => ?_⟩
  constructor
  · intro h
    rcases (hd.2.2.2.2.2 x).mp h with h | h
    · rcases (hTwoMem x).mp h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (hExt.eq_of_same_members x two h))
  · rintro (h | h | h)
    · exact (hd.2.2.2.2.2 x).mpr (Or.inl ((hTwoMem x).mpr (Or.inl h)))
    · exact (hd.2.2.2.2.2 x).mpr (Or.inl ((hTwoMem x).mpr (Or.inr h)))
    · subst x
      exact hd.2.2.2.2.2.predecessor_mem

theorem three_family (hM : FirstOrder.Theory.Models M nativeZF)
    {n zero one two D I mul r s t : M.Carrier .set}
    (h01 : zero ≠ one) (h02 : zero ≠ two) (h12 : one ≠ two)
    (hN : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i n ↔ i = zero ∨ i = one ∨ i = two)
    (hr : Injection D I r) (hs : Injection D I s) (ht : Injection D I t)
    (hrs : ExactOverlap D I mul r s) (hrt : ExactOverlap D I mul r t)
    (hst : ExactOverlap D I mul s t) :
    ∃ F, ConstructionDiagramPrescription.Family n D I F ∧
      ConstructionDiagramPrescription.ExactFamily n D I mul F ∧
      PureKuratowski.PairMember M zero r F ∧ PureKuratowski.PairMember M one s F ∧
      PureKuratowski.PairMember M two t F := by
  have hKP := ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)
  obtain ⟨zr,hzr⟩ := KuratowskiZF.exists_code hM zero r
  obtain ⟨os,hos⟩ := KuratowskiZF.exists_code hM one s
  obtain ⟨tt,htt⟩ := KuratowskiZF.exists_code hM two t
  obtain ⟨pair,hPair⟩ := KP.exists_pair hKP zr os
  obtain ⟨F,hF⟩ := KP.exists_insert hKP pair tt
  have hMem p : (Project.FirstOrderSemantics.reduct M).mem p F ↔ p = zr ∨ p = os ∨ p = tt := by
    rw [hF p,hPair p]
    exact or_assoc
  have hEdges i d : PureKuratowski.PairMember M i d F ↔
      (i = zero ∧ d = r) ∨ (i = one ∧ d = s) ∨ (i = two ∧ d = t) := by
    constructor
    · rintro ⟨p,hp,hm⟩
      rcases (hMem p).mp hm with h | h | h
      · subst p
        exact Or.inl (PureKuratowski.code_injective hp hzr)
      · subst p
        exact Or.inr (Or.inl (PureKuratowski.code_injective hp hos))
      · subst p
        exact Or.inr (Or.inr (PureKuratowski.code_injective hp htt))
    · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      · exact ⟨zr,hzr,(hMem zr).mpr (Or.inl rfl)⟩
      · exact ⟨os,hos,(hMem os).mpr (Or.inr (Or.inl rfl))⟩
      · exact ⟨tt,htt,(hMem tt).mpr (Or.inr (Or.inr rfl))⟩
  have hRow0 d : PureKuratowski.PairMember M zero d F ↔ d = r := by
    simpa only [h01,h02,not_false_eq_true,eq_self, false_and,true_and,false_or,or_false] using hEdges zero d
  have hRow1 d : PureKuratowski.PairMember M one d F ↔ d = s := by
    simpa only [Ne.symm h01,h12,not_false_eq_true,eq_self, false_and,true_and,false_or,or_false] using hEdges one d
  have hRow2 d : PureKuratowski.PairMember M two d F ↔ d = t := by
    simpa only [Ne.symm h02,Ne.symm h12,not_false_eq_true,eq_self, false_and,true_and,false_or,or_false] using hEdges two d
  have hFamily : ConstructionDiagramPrescription.Family n D I F := by
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro p hp
      rcases (hMem p).mp hp with h | h | h
      · subst p
        exact ⟨zero,r,(hN zero).mpr (Or.inl rfl),hzr⟩
      · subst p
        exact ⟨one,s,(hN one).mpr (Or.inr (Or.inl rfl)),hos⟩
      · subst p
        exact ⟨two,t,(hN two).mpr (Or.inr (Or.inr rfl)),htt⟩
    · intro i hi
      rcases (hN i).mp hi with rfl | rfl | rfl
      · exact ⟨r,(hRow0 r).mpr rfl,fun d hd => (hRow0 d).mp hd⟩
      · exact ⟨s,(hRow1 s).mpr rfl,fun d hd => (hRow1 d).mp hd⟩
      · exact ⟨t,(hRow2 t).mpr rfl,fun d hd => (hRow2 d).mp hd⟩
    · intro i d hd
      rcases (hEdges i d).mp hd with ⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩
      · exact hr
      · exact hs
      · exact ht
  have hExact : ConstructionDiagramPrescription.ExactFamily n D I mul F := by
    intro i j a b hi hj hij hai hbj
    rcases (hN i).mp hi with rfl | rfl | rfl <;>
      rcases (hN j).mp hj with rfl | rfl | rfl
    · exact False.elim (hij rfl)
    · rw [(hRow0 a).mp hai,(hRow1 b).mp hbj]; exact hrs
    · rw [(hRow0 a).mp hai,(hRow2 b).mp hbj]; exact hrt
    · rw [(hRow1 a).mp hai,(hRow0 b).mp hbj]; exact ConstructionDiagramPlacements.exactOverlap_symm hrs
    · exact False.elim (hij rfl)
    · rw [(hRow1 a).mp hai,(hRow2 b).mp hbj]; exact hst
    · rw [(hRow2 a).mp hai,(hRow0 b).mp hbj]; exact ConstructionDiagramPlacements.exactOverlap_symm hrt
    · rw [(hRow2 a).mp hai,(hRow1 b).mp hbj]; exact ConstructionDiagramPlacements.exactOverlap_symm hst
    · exact False.elim (hij rfl)
  exact ⟨F,hFamily,hExact,(hRow0 r).mpr rfl,(hRow1 s).mpr rfl,(hRow2 t).mpr rfl⟩

theorem common_extension_three (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w mu history kappa D mul e mark H C incoming base I r s t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hI : (Project.FirstOrderSemantics.reduct M).IsHartogsNumber (KuratowskiZF.interpretation hM) I mu)
    (hD : Small D mu)
    (hMergers : ConstructionSaturationMergers.AllMergers w history kappa)
    (hRow : ConstructionTowerHistory.Row history kappa D mul e mark H C incoming base kappa)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hr : Injection D I r) (hs : Injection D I s) (ht : Injection D I t)
    (hrs : ExactOverlap D I mul r s) (hrt : ExactOverlap D I mul r t)
    (hst : ExactOverlap D I mul s t) :
    ∃ q, Injection D I q ∧ ForcingDiagramOrder.Le D mul q r ∧
      ForcingDiagramOrder.Le D mul q s ∧ ForcingDiagramOrder.Le D mul q t := by
  obtain ⟨one,two,three,hd⟩ := ConstructionBaseWeights.digits_exists hw
  obtain ⟨zero,h01,h02,h12,hN⟩ := three_members hM hd
  obtain ⟨F,hFamily,hExact,h0,h1,h2⟩ := three_family hM h01 h02 h12 hN hr hs ht hrs hrt hst
  obtain ⟨P,identity,roots,q,hq⟩ := ConstructionDiagramAmalgamation.amalgamate hM hChoice
    hw hMu hI hD hMergers hRow hd.2.2.1 hm hFamily hExact
  have hCommon := hq.2.2.2.2.2.2.2
  exact ⟨q,hCommon.1,hCommon.2 zero r ((hN zero).mpr (Or.inl rfl)) h0,
    hCommon.2 one s ((hN one).mpr (Or.inr (Or.inl rfl))) h1,
    hCommon.2 two t ((hN two).mpr (Or.inr (Or.inr rfl))) h2⟩

def lowerBound {m : Nat} (D I mul r s t q : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.injection q D I))
    (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.le D mul q r))
      (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.le D mul q s))
        (ProjectSyntax.encode id (ForcingDiagramOrder.le D mul q t))))

theorem lowerBound_freeClosed {m : Nat} (D I mul r s t q : Fin m) :
    (lowerBound D I mul r s t q).FreeClosed := by
  simp -implicitDefEqProofs [lowerBound,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem lowerBound_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul r s t q : Fin m) :
    Project.Formula.satisfies env (lowerBound D I mul r s t q) ↔
      Injection (env.bound D) (env.bound I) (env.bound q) ∧
        ForcingDiagramOrder.Le (env.bound D) (env.bound mul) (env.bound q) (env.bound r) ∧
        ForcingDiagramOrder.Le (env.bound D) (env.bound mul) (env.bound q) (env.bound s) ∧
        ForcingDiagramOrder.Le (env.bound D) (env.bound mul) (env.bound q) (env.bound t) := by
  simp only [lowerBound,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.le_semantics (M := M)]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 16
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 16))) (.imp (Project.Formula.isInfiniteCardinal
    PureKuratowskiProject.convention (.bound (0 : Fin 16)) (.bound 1)) (.imp
    (ConstructionSaturationIndex.hartogs (1 : Fin 16) 12) (.imp (ProjectSyntax.encode id
    (ForcingSupportSize.small (4 : Fin 16) 1)) (.imp (ConstructionSaturationMergers.allMergers (0 : Fin
    16) 2 3) (.imp (ConstructionTowerHistory.row (2 : Fin 16) 3 4 5 6 7 8 9 10 11 3) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (4 : Fin 16) 5 6)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.injection (13 : Fin 16) 4 12)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.injection (14 : Fin 16) 4 12)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.injection (15 : Fin 16) 4 12)) (.imp
    (ConstructionDiagramPlacements.exactOverlap (4 : Fin 16) 12 5 13 14) (.imp
    (ConstructionDiagramPlacements.exactOverlap (4 : Fin 16) 12 5 13 15) (.imp
    (ConstructionDiagramPlacements.exactOverlap (4 : Fin 16) 12 5 14 15) (.existsE (lowerBound (4 : Fin
    16).succ (12 : Fin 16).succ (5 : Fin 16).succ (13 : Fin 16).succ (14 : Fin 16).succ (15 : Fin
    16).succ 0)))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      Project.Formula.isInfiniteCardinal,ConstructionSaturationIndex.hartogs_freeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,
      ConstructionDiagramPlacements.exactOverlap_freeClosed,lowerBound_freeClosed]

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
    ForcingSupportSize.injection_semantics (M := M),ConstructionDiagramPlacements.exactOverlap_semantics hM,
    lowerBound_semantics hM,Project.Term.eval_bound]
  exact fun hw hMu hI hD hMergers hRow hm hr hs ht hrs hrt hst =>
    common_extension_three hM hChoice hw hMu hI hD hMergers hRow hm hr hs ht hrs hrt hst

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

end PPAC.Migration.ConstructionDiagramThree
