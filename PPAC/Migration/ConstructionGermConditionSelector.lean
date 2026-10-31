/- Actual internal conditionSelector graph on ALL good Cohen conditions.
The domain is separated from the existing full condition carrier. The graph
uses Selected totality and uniqueness, so there is no additional choice.
Its common pattern order is supplied by the accepted L construction. -/
import PPAC.Migration.ConstructionGermSelected

namespace PPAC.Migration.ConstructionGermConditionSelector
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo)
open ForcingCohenConditions (Condition)
open ConstructionGermSelected (Selected)
open ConstructionGermPatternOrder (Covers)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Domain (w D chain H G N K C B lo hi det S P : M.Carrier .set) : Prop := ∀ p,
  (Project.FirstOrderSemantics.reduct M).mem p P ↔ Condition S w p ∧ ConstructionGermGoodDense.Good w D chain H G N K C B lo hi det p

def domain {m : Nat} (w D chain H G N K C B lo hi det S P : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound P.succ))
    (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ w.succ 0))
      (ConstructionGermGoodDense.good w.succ D.succ chain.succ H.succ G.succ N.succ K.succ C.succ B.succ lo.succ hi.succ det.succ 0)))

theorem domain_freeClosed {m : Nat} (w D chain H G N K C B lo hi det S P : Fin m) :
    (domain w D chain H G N K C B lo hi det S P).FreeClosed := by
  simp -implicitDefEqProofs [domain,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionGermGoodDense.good_freeClosed]

theorem domain_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D chain H G N K C B lo hi det S P : Fin m) :
    Project.Formula.satisfies env (domain w D chain H G N K C B lo hi det S P) ↔
      Domain (env.bound w) (env.bound D) (env.bound chain) (env.bound H) (env.bound G) (env.bound N) (env.bound K)
        (env.bound C) (env.bound B) (env.bound lo) (env.bound hi) (env.bound det) (env.bound S) (env.bound P) := by
  simp only [domain,Domain,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingCohenConditions.condition_semantics (M := M),ConstructionGermGoodDense.good_semantics hM]
  rfl

theorem exists_domain (hM : FirstOrder.Theory.Models M nativeZF) (w D chain H G N K C B lo hi det S : M.Carrier .set) :
    ∃ P, Domain w D chain H G N K C B lo hi det S P := by
  obtain ⟨All,hAll⟩ := ForcingCohenConditions.exists_carrier hM S w
  let schema : Project.UnarySchema 12 := {
    body := ConstructionGermGoodDense.good 1 2 3 4 5 6 7 8 9 10 11 12 0,
    freeClosed := ConstructionGermGoodDense.good_freeClosed 1 2 3 4 5 6 7 8 9 10 11 12 0 }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 12 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases chain (Fin.cases H (Fin.cases G (Fin.cases N (Fin.cases K
      (Fin.cases C (Fin.cases B (Fin.cases lo (Fin.cases hi (fun _ => det))))))))))), free := fun _ => S }
  have he p : schema.denote env p ↔ ConstructionGermGoodDense.Good w D chain H G N K C B lo hi det p :=
    ConstructionGermGoodDense.good_semantics hM (env.push p) 1 2 3 4 5 6 7 8 9 10 11 12 0
  obtain ⟨P,hP⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env All
  exact ⟨P,fun p => (hP p).trans (and_congr (hAll p) (he p))⟩

def Selector (w D chain H G N K C B lo hi det order S P f : M.Carrier .set) : Prop :=
  Domain w D chain H G N K C B lo hi det S P ∧ MapsTo P G f ∧ ∀ p c,
    PureKuratowski.PairMember M p c f ↔ Condition S w p ∧ Selected w D chain H G N K C B lo hi det order p c

def selector {m : Nat} (w D chain H G N K C B lo hi det order S P f : Fin m) : Project.Formula 1 m :=
  .conj (domain w D chain H G N K C B lo hi det S P)
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo f P G))
      (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ 1 0))
        (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ.succ w.succ.succ 1))
          (ConstructionGermSelected.selected w.succ.succ D.succ.succ chain.succ.succ H.succ.succ G.succ.succ N.succ.succ K.succ.succ
            C.succ.succ B.succ.succ lo.succ.succ hi.succ.succ det.succ.succ order.succ.succ 1 0))))))

theorem selector_freeClosed {m : Nat} (w D chain H G N K C B lo hi det order S P f : Fin m) :
    (selector w D chain H G N K C B lo hi det order S P f).FreeClosed := by
  simp -implicitDefEqProofs [selector,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,domain_freeClosed,ConstructionGermSelected.selected_freeClosed]

theorem selector_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D chain H G N K C B lo hi det order S P f : Fin m) :
    Project.Formula.satisfies env (selector w D chain H G N K C B lo hi det order S P f) ↔
      Selector (env.bound w) (env.bound D) (env.bound chain) (env.bound H) (env.bound G) (env.bound N) (env.bound K)
        (env.bound C) (env.bound B) (env.bound lo) (env.bound hi) (env.bound det) (env.bound order) (env.bound S) (env.bound P) (env.bound f) := by
  simp only [selector,Selector,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    domain_semantics hM,ConstructionGermSelected.selected_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingCohenConditions.condition_semantics (M := M),KuratowskiZF.source_edge]
  rfl

theorem exists_selector (hM : FirstOrder.Theory.Models M nativeZF)
    {w D chain H G N K C B lo hi det order O S : M.Carrier .set}
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal K) (hCover : Covers w N B K O)
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) order O)
    (hNonempty : ∃ c, (Project.FirstOrderSemantics.reduct M).mem c G) :
    ∃ P f, Selector w D chain H G N K C B lo hi det order S P f := by
  obtain ⟨P,hP⟩ := exists_domain hM w D chain H G N K C B lo hi det S
  let schema : Project.BinarySchema 13 := {
    body := ConstructionGermSelected.selected 2 3 4 5 6 7 8 9 10 11 12 13 14 1 0,
    freeClosed := ConstructionGermSelected.selected_freeClosed 2 3 4 5 6 7 8 9 10 11 12 13 14 1 0 }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 13 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases chain (Fin.cases H (Fin.cases G (Fin.cases N (Fin.cases K
      (Fin.cases C (Fin.cases B (Fin.cases lo (Fin.cases hi (Fin.cases det (fun _ => order)))))))))))), free := fun _ => S }
  have he p c : schema.denote env p c ↔ Selected w D chain H G N K C B lo hi det order p c :=
    ConstructionGermSelected.selected_semantics hM ((env.push p).push c) 2 3 4 5 6 7 8 9 10 11 12 13 14 1 0
  obtain ⟨f,hf,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := P) (target := G) (by
      intro p hp
      obtain ⟨c,hc⟩ := ConstructionGermSelected.exists_selected hM hK hCover hOrder hNonempty ((hP p).mp hp).2
      exact ⟨c,(he p c).mpr hc⟩)
    (fun p _ c d hc hd => ConstructionGermSelected.selected_unique hM hK hCover hOrder ((he p c).mp hc) ((he p d).mp hd))
    (fun p c _ hc => ConstructionGermSelected.selected_mem ((he p c).mp hc))
  refine ⟨P,f,hP,(ForcingSupportSize.native_mapsTo hM P G f).mpr hf,?_⟩
  intro p c
  apply (hEdge p c).trans
  constructor
  · rintro ⟨hp,hc⟩
    exact ⟨((hP p).mp hp).1,(he p c).mp hc⟩
  · rintro ⟨hp,hc⟩
    exact ⟨(hP p).mpr ⟨hp,hc.1⟩,(he p c).mpr hc⟩

theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w D chain H G N K C B lo hi det S : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal K)
    (hNonempty : ∃ c, (Project.FirstOrderSemantics.reduct M).mem c G) :
    ∃ O order P f, Covers w N B K O ∧
      (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) order O ∧
        Selector w D chain H G N K C B lo hi det order S P f := by
  obtain ⟨O,order,hCover,hOrder⟩ := ConstructionGermPatternOrder.construction hM hChoice N B K hw
  obtain ⟨P,f,hf⟩ := exists_selector (S := S) hM hK hCover hOrder hNonempty
  exact ⟨O,order,P,f,hCover,hOrder,hf⟩

def existenceSentence {m : Nat} (w D chain H G N K C B lo hi det order O S : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOrdinal (.bound K)) (.imp (ConstructionGermPatternOrder.covers w N B K O) (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound O)) (.imp (.existsE (.mem (.bound 0) (.bound G.succ))) (.existsE (.existsE (selector w.succ.succ D.succ.succ chain.succ.succ H.succ.succ G.succ.succ N.succ.succ K.succ.succ C.succ.succ B.succ.succ lo.succ.succ hi.succ.succ det.succ.succ order.succ.succ S.succ.succ 1 0)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOrdinal,ConstructionGermPatternOrder.covers_freeClosed,selector_freeClosed]

theorem existence_models {m : Nat} (w D chain H G N K C B lo hi det order O S : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (existenceSentence w D chain H G N K C B lo hi det order O S)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (existenceSentence w D chain H G N K C B lo hi det order O S)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOrdinal_iff,ConstructionGermPatternOrder.covers_semantics hM,Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,selector_semantics hM]
  exact exists_selector hM

theorem existence_kernel_certificate {m : Nat} (w D chain H G N K C B lo hi det order O S : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (existenceSentence w D chain H G N K C B lo hi det order O S)) :=
  ModelTransfer.derives (fun _ hM => existence_models w D chain H G N K C B lo hi det order O S hM)

def constructionSentence {m : Nat} (w D chain H G N K C B lo hi det S : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isOrdinal (.bound K)) (.imp (.existsE (.mem (.bound 0) (.bound G.succ))) (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionGermPatternOrder.covers w.succ.succ.succ.succ N.succ.succ.succ.succ B.succ.succ.succ.succ K.succ.succ.succ.succ 3) (.conj (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound 2) (.bound 3)) (selector w.succ.succ.succ.succ D.succ.succ.succ.succ chain.succ.succ.succ.succ H.succ.succ.succ.succ G.succ.succ.succ.succ N.succ.succ.succ.succ K.succ.succ.succ.succ C.succ.succ.succ.succ B.succ.succ.succ.succ lo.succ.succ.succ.succ hi.succ.succ.succ.succ det.succ.succ.succ.succ 2 S.succ.succ.succ.succ 1 0))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.isOrdinal,ConstructionGermPatternOrder.covers_freeClosed,selector_freeClosed]

theorem construction_models {m : Nat} (w D chain H G N K C B lo hi det S : Fin m) (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence w D chain H G N K C B lo hi det S)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w D chain H G N K C B lo hi det S)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isOrdinal_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_conj_iff,ConstructionGermPatternOrder.covers_semantics hM,Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),selector_semantics hM]
  exact construction hM hChoice

theorem construction_kernel_certificate {m : Nat} (w D chain H G N K C B lo hi det S : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (constructionSentence w D chain H G N K C B lo hi det S))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence w D chain H G N K C B lo hi det S)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence w D chain H G N K C B lo hi det S)).mp (construction_models w D chain H G N K C B lo hi det S hL hChoice)

end PPAC.Migration.ConstructionGermConditionSelector
