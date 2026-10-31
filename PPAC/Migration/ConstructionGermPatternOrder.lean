/- Fixed source WellOrderingRel on pattern objects. The full pattern space
at each internal alpha is unique. Collection and Union produce ONE bounding
set for every alpha in K, independent of row data and Cohen conditions.
Reuse the accepted ordinal-enumeration/order proof; object Choice is
supplied only inside the existing L interpretation. -/
import PPAC.Migration.ConstructionGermBestCoset
import PPAC.Migration.ConstructionScheduleOrder

namespace PPAC.Migration.ConstructionGermPatternOrder
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionGermEventual (Space Classes)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def PatternSpace (w N B alpha T : M.Carrier .set) : Prop := ∃ A S E,
  Space alpha B A ∧ Space w A S ∧ Classes w S E ∧ Space N E T

def patternSpace {m : Nat} (w N B alpha T : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.conj (ConstructionGermEventual.space alpha.succ.succ.succ B.succ.succ.succ 2)
    (.conj (ConstructionGermEventual.space w.succ.succ.succ 2 1)
      (.conj (ConstructionGermEventual.classes w.succ.succ.succ 1 0)
        (ConstructionGermEventual.space N.succ.succ.succ 0 T.succ.succ.succ))))))

theorem patternSpace_freeClosed {m : Nat} (w N B alpha T : Fin m) : (patternSpace w N B alpha T).FreeClosed := by
  simp -implicitDefEqProofs [patternSpace,Definitional.Formula.FreeClosed,ConstructionGermEventual.space_freeClosed,ConstructionGermEventual.classes_freeClosed]

theorem patternSpace_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w N B alpha T : Fin m) :
    Project.Formula.satisfies env (patternSpace w N B alpha T) ↔
      PatternSpace (env.bound w) (env.bound N) (env.bound B) (env.bound alpha) (env.bound T) := by
  simp only [patternSpace,PatternSpace,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionGermEventual.space_semantics hM,ConstructionGermEventual.classes_semantics hM]
  rfl

theorem function_space_unique (hM : FirstOrder.Theory.Models M nativeZF) {A B S T : M.Carrier .set}
    (hS : Space A B S) (hT : Space A B T) : S = T :=
  (ModelTransfer.extensionality hM).eq_of_same_members S T (fun f => (hS f).trans (hT f).symm)

theorem pattern_space_unique (hM : FirstOrder.Theory.Models M nativeZF) {w N B alpha T U : M.Carrier .set}
    (hT : PatternSpace w N B alpha T) (hU : PatternSpace w N B alpha U) : T = U := by
  obtain ⟨A,S,E,hA,hS,hE,hT⟩ := hT
  obtain ⟨A',S',E',hA',hS',hE',hU⟩ := hU
  have ea := function_space_unique hM hA' hA
  subst A'
  have es := function_space_unique hM hS' hS
  subst S'
  have ee := (ModelTransfer.extensionality hM).eq_of_same_members E' E (fun C => (hE' C).trans (hE C).symm)
  subst E'
  exact function_space_unique hM hT hU

theorem exists_pattern_space (hM : FirstOrder.Theory.Models M nativeZF)
    {w : M.Carrier .set} (N B alpha : M.Carrier .set)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) : ∃ T, PatternSpace w N B alpha T := by
  obtain ⟨A,hA⟩ := ZF.exists_functionSpace (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) alpha B
  obtain ⟨S,E,_,hS,_,hE,_,_⟩ := ConstructionGermEventual.construction hM A hw
  obtain ⟨T,hT⟩ := ZF.exists_functionSpace (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) N E
  exact ⟨T,A,S,E,(fun f => (hA f).trans (ForcingSupportSize.native_mapsTo hM alpha B f).symm),hS,hE,
    (fun f => (hT f).trans (ForcingSupportSize.native_mapsTo hM N E f).symm)⟩

def Covers (w N B K O : M.Carrier .set) : Prop := ∀ alpha T,
  (Project.FirstOrderSemantics.reduct M).mem alpha K → PatternSpace w N B alpha T →
    (Project.FirstOrderSemantics.reduct M).MemberSubset T O

def covers {m : Nat} (w N B K O : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.imp (.mem (.bound 1) (.bound K.succ.succ))
    (.imp (patternSpace w.succ.succ N.succ.succ B.succ.succ 1 0)
      (Project.Formula.subset (.bound 0) (.bound O.succ.succ)))))

theorem covers_freeClosed {m : Nat} (w N B K O : Fin m) : (covers w N B K O).FreeClosed := by
  simp -implicitDefEqProofs [covers,Definitional.Formula.FreeClosed,patternSpace_freeClosed,Project.Formula.subset]

theorem covers_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w N B K O : Fin m) :
    Project.Formula.satisfies env (covers w N B K O) ↔
      Covers (env.bound w) (env.bound N) (env.bound B) (env.bound K) (env.bound O) := by
  simp only [covers,Covers,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,patternSpace_semantics hM]
  rfl

theorem exists_cover (hM : FirstOrder.Theory.Models M nativeZF)
    {w : M.Carrier .set} (N B K : M.Carrier .set)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) : ∃ O, Covers w N B K O := by
  let schema : Project.BinarySchema 3 := { body := patternSpace 2 3 4 1 0, freeClosed := patternSpace_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases w (Fin.cases N (fun _ => B)), free := fun _ => K }
  have he alpha T : schema.denote env alpha T ↔ PatternSpace w N B alpha T :=
    patternSpace_semantics hM ((env.push alpha).push T) 2 3 4 1 0
  obtain ⟨family,hFamily⟩ := ZF.collection_exists_d (ModelTransfer.project_models_iff.mp hM) schema env K (by
    intro alpha _
    obtain ⟨T,hT⟩ := exists_pattern_space hM N B alpha hw
    exact ⟨T,(he alpha T).mpr hT⟩)
  obtain ⟨O,hO⟩ := KP.exists_union (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) family
  refine ⟨O,?_⟩
  intro alpha T ha hT P hP
  obtain ⟨U,hU,hSpaceU⟩ := hFamily alpha ha
  have eq := pattern_space_unique hM ((he alpha U).mp hSpaceU) hT
  subst U
  exact (hO P).mpr ⟨T,hU,hP⟩

/-- Exact retained proof body of ConstructionScheduleOrder.exists_product_order;
only its unused product-specific parameters are removed. -/
theorem exists_order (hM : FirstOrder.Theory.Models M nativeZF)
    (hc : ConstructionDirectedCardinality.Choice (M := M)) (A : M.Carrier .set) :
    ∃ r, (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) r A := by
  let N := Project.FirstOrderSemantics.reduct M
  let I := KuratowskiZF.interpretation hM
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨κ,F,hκ,hF,hOnto⟩ := ExistingOrdinalEnumeration.ordinal_enum_l
    (ConstructionDirectedCardinality.models_zfc hM hc) I A
  obtain ⟨rank,hrank⟩ := ZF.exists_rightInverseInjection_of_surjection_from_ordinal hZF I hκ hF hOnto
  let env : SetTheory.Env N 1 := ⟨fun _ => rank,fun _ => A⟩
  obtain ⟨r,hr,hg⟩ := ZF.exists_setRelationOn_of_denote hZF I
    (Project.BinarySchema.transportedOrdinalMembership PureKuratowskiProject.convention) env A
  have rel x y : N.PairMember I x y r ↔ N.mem x A ∧ N.mem y A ∧
      ∃ a b, N.PairMember I x a rank ∧ N.PairMember I y b rank ∧ N.mem a b := by
    rw [hg x y,Project.Formula.denote_transportedOrdinalMembership_iff I]
  refine ⟨r,⟨⟨hr.1,⟨⟨?_,?_⟩,?_⟩⟩,?_⟩⟩
  · intro x _ hx
    obtain ⟨_,_,a,b,ha,hb,hab⟩ := (rel x x).mp hx
    have eq := hrank.1.1.2 x a b ha hb
    subst b
    exact hκ.wellOrder.linear.irrefl a (hrank.1.output_mem_of_pairMember ha) hab
  · intro x hx y hy z hz hxy hyz
    obtain ⟨_,_,a,b,ha,hb,hab⟩ := (rel x y).mp hxy
    obtain ⟨_,_,b',c,hb',hc,hbc⟩ := (rel y z).mp hyz
    have eq := hrank.1.1.2 y b b' hb hb'
    subst b'
    exact (rel x z).mpr ⟨hx,hz,a,c,ha,hc,hκ.wellOrder.linear.trans
      a (hrank.1.output_mem_of_pairMember ha) b (hrank.1.output_mem_of_pairMember hb)
      c (hrank.1.output_mem_of_pairMember hc) hab hbc⟩
  · intro x hx y hy
    obtain ⟨a,ha,he⟩ := hrank.1.2.2 x hx
    obtain ⟨b,hb,hf⟩ := hrank.1.2.2 y hy
    rcases hκ.wellOrder.linear.compare a ha b hb with eq | lt | gt
    · have eq' := hZF.1.eq_of_same_members a b eq
      subst b
      have exy := hrank.2 x y a he hf
      subst y
      exact Or.inl (fun _ => Iff.rfl)
    · exact Or.inr (Or.inl ((rel x y).mpr ⟨hx,hy,a,b,he,hf,lt⟩))
    · exact Or.inr (Or.inr ((rel y x).mpr ⟨hy,hx,b,a,hf,he,gt⟩))
  · intro X hX hne
    let schema : Project.UnarySchema 2 := { body := .existsE (.conj (.mem .newest (.bound 2))
      (Project.Formula.orderedPairMem PureKuratowskiProject.convention .newest (.bound 1) (.bound 3))) }
    let ρ : SetTheory.Env N 2 := ⟨Fin.cases X (fun _ => rank),fun _ => X⟩
    obtain ⟨B,hB⟩ := ZF.separation_exists_d hZF schema ρ κ
    have hb a : N.mem a B ↔ N.mem a κ ∧ ∃ x, N.mem x X ∧ N.PairMember I x a rank := by
      rw [hB a]
      simp only [schema,Project.Formula.satisfies_exists_iff,
        Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
        Project.Formula.satisfies_orderedPairMem_iff I]
      rfl
    obtain ⟨x,hx⟩ := hne
    obtain ⟨a,ha,he⟩ := hrank.1.2.2 x (hX x hx)
    obtain ⟨a,ha,hmin⟩ := hκ.wellOrder.least B (fun a ha => ((hb a).mp ha).1)
      ⟨a,(hb a).mpr ⟨ha,x,hx,he⟩⟩
    obtain ⟨_,x,hx,he⟩ := (hb a).mp ha
    refine ⟨x,hx,?_⟩
    intro y hy
    obtain ⟨b,hbκ,hf⟩ := hrank.1.2.2 y (hX y hy)
    rcases hmin b ((hb b).mpr ⟨hbκ,y,hy,hf⟩) with eq | lt
    · have eq' := hZF.1.eq_of_same_members a b eq
      subst b
      have exy := hrank.2 x y a he hf
      subst y
      exact Or.inl (fun _ => Iff.rfl)
    · exact Or.inr ((rel x y).mpr ⟨hX x hx,hX y hy,a,b,he,hf,lt⟩)

theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    (hc : ConstructionDirectedCardinality.Choice (M := M)) {w : M.Carrier .set} (N B K : M.Carrier .set)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) : ∃ O order,
      Covers w N B K O ∧ (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) order O := by
  obtain ⟨O,hO⟩ := exists_cover hM N B K hw
  obtain ⟨order,hOrder⟩ := exists_order hM hc O
  exact ⟨O,order,hO,hOrder⟩


def coverSentence {m : Nat} (w N B K : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w))
    (.existsE (covers w.succ N.succ B.succ K.succ 0)))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,covers_freeClosed]

theorem cover_models {m : Nat} (w N B K : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (coverSentence w N B K)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (coverSentence w N B K)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,covers_semantics hM]
  exact exists_cover hM _ _ _

theorem cover_kernel_certificate {m : Nat} (w N B K : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (coverSentence w N B K)) :=
  ModelTransfer.derives (fun _ hM => cover_models w N B K hM)

def constructionSentence {m : Nat} (w N B K : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w))
    (.existsE (.existsE (.conj (covers w.succ.succ N.succ.succ B.succ.succ K.succ.succ 1)
      (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound 0) (.bound 1))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,covers_freeClosed]

theorem construction_models {m : Nat} (w N B K : Fin m) (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence w N B K)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w N B K)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,covers_semantics hM,
    Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM)]
  exact construction hM hChoice _ _ _

theorem construction_kernel_certificate {m : Nat} (w N B K : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (constructionSentence w N B K))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence w N B K)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence w N B K)).mp (construction_models w N B K hL hChoice)


end PPAC.Migration.ConstructionGermPatternOrder
