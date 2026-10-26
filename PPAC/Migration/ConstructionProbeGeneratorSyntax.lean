/- Pure membership existence certificate for the source generator map and old gate. -/
import PPAC.Migration.ConstructionProbeGenerator
import PPAC.Migration.ConstructionProbeOldEmbeddingSyntax

namespace PPAC.Migration.ConstructionProbeGeneratorSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeGenerator ConstructionProbeOldEmbedding ConstructionProbeWordMonoid
open ConstructionProbeWord (WordCarrier)
open ConstructionProbeAlphabet (Alphabet)
open ConstructionProbeRawAction (HeadDiv)
open ConstructionProbeLetterAction (LetterAct)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo)
open ConstructionBaseMonoid (Divides)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def GeneratorLaws (w D S zero mul A b W E G K : M.Carrier .set) : Prop :=
  (∀ s gen input y, PureKuratowski.PairMember M s gen K → (Project.FirstOrderSemantics.reduct M).mem input W →
    (Product G gen input y ↔ LetterAct w D S zero mul A b W E s input y)) ∧
  (∀ s gen z ob oz, PureKuratowski.PairMember M s gen K → PureKuratowski.PairMember M s z E →
    Old zero D b ob → Old zero D z oz → Product G gen ob oz) ∧
  (∀ x ox s t gs gt, Old zero D x ox → PureKuratowski.PairMember M s gs K →
    PureKuratowski.PairMember M t gt K → Product A x s t → Product G ox gs gt) ∧
  (∀ s gen input y, PureKuratowski.PairMember M s gen K → (Project.FirstOrderSemantics.reduct M).mem input W →
    ¬ HeadDiv w D S zero mul A b input → Cons w D S s input y → Product G gen input y) ∧
  (∀ s gen z y oy, PureKuratowski.PairMember M s gen K → PureKuratowski.PairMember M s z E →
    Old zero D y oy → (Divides W G gen oy ↔ Divides D mul z y))

theorem generator_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit K : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hUnit : Old zero D e unit) (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hK : MapsTo S W K) (hGraph : GeneratorGraph w D S unit K) :
    GeneratorLaws w D S zero mul A b W E G K := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro s gen input y hgen hi
    exact generator_mul_iff hM hw hz hzw hm hAlpha hW hb hUnit hG ((hGraph s gen).mp hgen) (hK.2 s gen hgen) hi
  · intro s gen z ob oz hgen hzE hob hoz
    exact generator_mul_b hM hw hz hzw hm hAlpha hW hb hUnit hG ((hGraph s gen).mp hgen) (hK.2 s gen hgen) hzE hob hoz
  · intro x ox s t gs gt hx hgs hgt hact
    exact old_mul_generator hM hw hz hzw hm hAlpha hW hb hG hx ((hGraph s gs).mp hgs)
      ((hGraph t gt).mp hgt) (hK.2 s gs hgs) hact
  · intro s gen input y hgen hi hnot hy
    exact generator_mul_of_not_headDiv hM hw hz hzw hm hAlpha hW hb hUnit hG
      ((hGraph s gen).mp hgen) (hK.2 s gen hgen) hi hnot hy
  · intro s gen z y oy hgen hzE hy
    exact generator_dvd_old_iff hM hw hz hzw hm hAlpha hW hb hUnit hG
      ((hGraph s gen).mp hgen) (hK.2 s gen hgen) hzE hy

def generatorGraph {m : Nat} (w D S unit K : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge K.succ.succ 1 0)) (cons
    w.succ.succ D.succ.succ S.succ.succ 1 unit.succ.succ 0))))

theorem generatorGraph_freeClosed {m : Nat} (w D S unit K : Fin m) :
    (generatorGraph w D S unit K).FreeClosed := by
  simp -implicitDefEqProofs [generatorGraph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,cons_freeClosed]

theorem generatorGraph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S unit K : Fin m) :
    Project.Formula.satisfies env (generatorGraph w D S unit K) ↔
      GeneratorGraph (env.bound w) (env.bound D) (env.bound S) (env.bound unit) (env.bound K) := by
  simp only [generatorGraph,GeneratorGraph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,cons_semantics hM]
  rfl

def generatorLaws {m : Nat} (w D S zero mul A b W E G K : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    K.succ.succ.succ.succ 3 2)) (.imp (.mem (.bound 1) (.bound W.succ.succ.succ.succ)) (.iff
    (ProjectSyntax.encode id (ForcingDiagramOrder.product G.succ.succ.succ.succ 2 1 0))
    (ConstructionProbeLetterAction.letterAct w.succ.succ.succ.succ D.succ.succ.succ.succ S.succ.succ.succ.succ
    zero.succ.succ.succ.succ mul.succ.succ.succ.succ A.succ.succ.succ.succ b.succ.succ.succ.succ
    W.succ.succ.succ.succ E.succ.succ.succ.succ 3 1 0)))))))) (.conj (.forallE (.forallE (.forallE (.forallE
    (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge K.succ.succ.succ.succ.succ 4 3)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge E.succ.succ.succ.succ.succ 4 2)) (.imp (old
    zero.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ b.succ.succ.succ.succ.succ 1) (.imp (old
    zero.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ 2 0) (ProjectSyntax.encode id
    (ForcingDiagramOrder.product G.succ.succ.succ.succ.succ 3 1 0))))))))))) (.conj (.forallE (.forallE
    (.forallE (.forallE (.forallE (.forallE (.imp (old zero.succ.succ.succ.succ.succ.succ
    D.succ.succ.succ.succ.succ.succ 5 4) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    K.succ.succ.succ.succ.succ.succ 3 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    K.succ.succ.succ.succ.succ.succ 2 0)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
    A.succ.succ.succ.succ.succ.succ 5 3 2)) (ProjectSyntax.encode id (ForcingDiagramOrder.product
    G.succ.succ.succ.succ.succ.succ 4 1 0)))))))))))) (.conj (.forallE (.forallE (.forallE (.forallE (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge K.succ.succ.succ.succ 3 2)) (.imp (.mem (.bound 1) (.bound
    W.succ.succ.succ.succ)) (.imp (.neg (ConstructionProbeRawActionSyntax.headDiv w.succ.succ.succ.succ
    D.succ.succ.succ.succ S.succ.succ.succ.succ zero.succ.succ.succ.succ mul.succ.succ.succ.succ
    A.succ.succ.succ.succ b.succ.succ.succ.succ 1)) (.imp (cons w.succ.succ.succ.succ D.succ.succ.succ.succ
    S.succ.succ.succ.succ 3 1 0) (ProjectSyntax.encode id (ForcingDiagramOrder.product G.succ.succ.succ.succ 2 1
    0)))))))))) (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge K.succ.succ.succ.succ.succ 4 3)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge E.succ.succ.succ.succ.succ 4 2)) (.imp (old zero.succ.succ.succ.succ.succ
    D.succ.succ.succ.succ.succ 1 0) (.iff (ProjectSyntax.encode id (ConstructionBaseMonoid.divides
    W.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ 3 0)) (ProjectSyntax.encode id
    (ConstructionBaseMonoid.divides D.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ 2 1)))))))))))))))

theorem generatorLaws_freeClosed {m : Nat} (w D S zero mul A b W E G K : Fin m) :
    (generatorLaws w D S zero mul A b W E G K).FreeClosed := by
  simp -implicitDefEqProofs [generatorLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    old_freeClosed,cons_freeClosed,ConstructionProbeLetterAction.letterAct_freeClosed,
    ConstructionProbeRawActionSyntax.headDiv_freeClosed]

theorem generatorLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A b W E G K : Fin m) :
    Project.Formula.satisfies env (generatorLaws w D S zero mul A b W E G K) ↔
      GeneratorLaws (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul) (env.bound A)
        (env.bound b) (env.bound W) (env.bound E) (env.bound G) (env.bound K) := by
  simp only [generatorLaws,GeneratorLaws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramOrder.product_semantics (M := M),ConstructionBaseMonoid.divides_semantics (M := M),
    old_semantics hM,cons_semantics hM,ConstructionProbeLetterAction.letterAct_semantics hM,
    ConstructionProbeRawActionSyntax.headDiv_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 10
    (.imp (Project.Formula.isOmega (.bound 0)) (.imp (Project.Formula.isEmpty (.bound 3)) (.imp (.mem (.bound 3)
    (.bound 0)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 10) 4 8)) (.imp
    (ConstructionProbeAlphabet.alphabet (1 : Fin 10) 4 8 2 9 5 7) (.imp (.mem (.bound 6) (.bound 1)) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.conical (1 : Fin 10) 4 8)) (.imp (.neg
    (Project.Formula.extensionalEq (.bound 6) (.bound 8))) (.existsE (.existsE (.existsE (.existsE (.existsE
    (.existsE (.conj (ConstructionProbeWord.wordCarrier 6 7 8 10 11 12 5) (.conj (old 9 7 14 4) (.conj
    (ConstructionProbeLetters.representatives 5 5 3) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo
    2 3 5)) (.conj (ConstructionProbeWordMonoidSyntax.multiplicationGraph 6 7 8 9 10 11 12 5 13 2) (.conj
    (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid 5 2 4)) (.conj (ProjectSyntax.encode id
    (ForcingDiagramPoset.conical 5 2 4)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection 1 7 5))
    (.conj (ConstructionProbeOldEmbeddingSyntax.oldGraph 9 7 1) (.conj
    (ConstructionProbeOldEmbeddingSyntax.embeddingLaws 6 7 8 9 10 11 5 2 14 4 1) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo 0 8 5)) (.conj (generatorGraph 6 7 8 4 0) (generatorLaws 6 7 8 9 10 11 12 5 13 2
    0)))))))))))))))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isEmpty,
    Project.Formula.extensionalEq,ProjectSyntax.freeClosed,ConstructionProbeAlphabet.alphabet_freeClosed,
    ConstructionProbeWord.wordCarrier_freeClosed,old_freeClosed,ConstructionProbeLetters.representatives_freeClosed,
    ConstructionProbeWordMonoidSyntax.multiplicationGraph_freeClosed,
    ConstructionProbeOldEmbeddingSyntax.oldGraph_freeClosed,ConstructionProbeOldEmbeddingSyntax.embeddingLaws_freeClosed,
    generatorGraph_freeClosed,generatorLaws_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    ConstructionProbeAlphabet.alphabet_semantics hM,ConstructionProbeWord.wordCarrier_semantics hM,
    old_semantics hM,ConstructionProbeLetters.representatives_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ConstructionProbeWordMonoidSyntax.multiplicationGraph_semantics hM,
    ConstructionProbeOldEmbeddingSyntax.oldGraph_semantics hM,ConstructionProbeOldEmbeddingSyntax.embeddingLaws_semantics hM,
    generatorGraph_semantics hM,generatorLaws_semantics hM]
  intro hw hz hzw hm hAlpha hb hc hne
  obtain ⟨W,hW⟩ := ConstructionProbeWord.exists_word_carrier hM hw (bound 1) (bound 2) (bound 4) (bound 5) (bound 6)
  obtain ⟨unit,hUnit⟩ := exists_old hM hm.1.1 (zero := bound 3)
  obtain ⟨J,G,hJ,hG,hgraph⟩ := exists_multiplication hM hw hz hzw hm hAlpha hW hb
  obtain ⟨H,hH,hOldGraph⟩ := exists_old_graph hM hz hzw hW
  obtain ⟨K,hK,hGenGraph⟩ := exists_generator_graph hM hw hz hzw hc hW hb hne hUnit
  exact ⟨W,unit,J,G,H,K,hW,hUnit,hJ,hG,hgraph,monoid_laws hM hw hz hzw hm hAlpha hW hb hUnit hgraph,
    word_conical hM hw hz hzw hc hAlpha hW hUnit hgraph,hH,hOldGraph,
    ConstructionProbeOldEmbeddingSyntax.embedding_laws hM hw hz hzw hm hAlpha hW hb hUnit hgraph hOldGraph,
    hK,hGenGraph,generator_laws hM hw hz hzw hm hAlpha hW hb hUnit hgraph hK hGenGraph⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeGeneratorSyntax
