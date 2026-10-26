/- Native pure-set certificate for source oldHom, factor/divisibility reflection and conical Word. -/
import PPAC.Migration.ConstructionProbeOldEmbedding

namespace PPAC.Migration.ConstructionProbeOldEmbeddingSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeOldEmbedding ConstructionProbeWordMonoid
open ConstructionProbeWord (WordCarrier)
open ConstructionProbeAlphabet (Alphabet)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
open ConstructionBaseMonoid (Divides)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def EmbeddingLaws (w D S zero mul A W G e unit H : M.Carrier .set) : Prop :=
  PureKuratowski.PairMember M e unit H ∧
  (∀ x y z ox oy oz, PureKuratowski.PairMember M x ox H → PureKuratowski.PairMember M y oy H →
    PureKuratowski.PairMember M z oz H → Product mul x y z → Product G ox oy oz) ∧
  (∀ x y ox oy input, PureKuratowski.PairMember M x ox H → PureKuratowski.PairMember M y oy H →
    (Project.FirstOrderSemantics.reduct M).mem input W →
      (Product G ox input oy ↔ ∃ z, Old zero D z input ∧ Product mul x z y)) ∧
  (∀ x y ox oy, PureKuratowski.PairMember M x ox H → PureKuratowski.PairMember M y oy H →
    (Divides W G ox oy ↔ Divides D mul x y)) ∧
  (∀ x ox q, PureKuratowski.PairMember M x ox H → (Project.FirstOrderSemantics.reduct M).mem q W →
    (Divides W G ox q ↔ ConstructionProbeRawAction.HeadDiv w D S zero mul A x q))

theorem embedding_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W E e I G unit H : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hAlpha : Alphabet D mul e S I A E)
    (hW : WordCarrier w D S mul A b W) (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hUnit : Old zero D e unit) (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hH : OldGraph zero D H) : EmbeddingLaws w D S zero mul A W G e unit H := by
  refine ⟨(hH e unit).mpr hUnit,?_,?_,?_,?_⟩
  · intro x y z ox oy oz hx hy hzv hp
    exact old_mul hM hw hz hzw hm hAlpha hW hb hG ((hH x ox).mp hx) ((hH y oy).mp hy) ((hH z oz).mp hzv) hp
  · intro x y ox oy input hx hy hi
    exact old_mul_eq_old_iff hM hw hz hzw hm hAlpha hW hb hG ((hH x ox).mp hx) ((hH y oy).mp hy) hi
  · intro x y ox oy hx hy
    exact old_dvd_old_iff hM hw hz hzw hm hAlpha hW hb hG ((hH x ox).mp hx) ((hH y oy).mp hy)
  · intro x ox q hx hq
    exact old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hb hG ((hH x ox).mp hx) hq

def oldGraph {m : Nat} (zero D H : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ 1 0)) (old zero.succ.succ D.succ.succ 1 0))))

theorem oldGraph_freeClosed {m : Nat} (zero D H : Fin m) : (oldGraph zero D H).FreeClosed := by
  simp -implicitDefEqProofs [oldGraph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,old_freeClosed]

theorem oldGraph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (zero D H : Fin m) :
    Project.Formula.satisfies env (oldGraph zero D H) ↔ OldGraph (env.bound zero) (env.bound D) (env.bound H) := by
  simp only [oldGraph,OldGraph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,old_semantics hM]
  rfl

def embeddingLaws {m : Nat} (w D S zero mul A W G e unit H : Fin m) : Project.Formula 1 m :=
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge H e unit)) (.conj (.forallE (.forallE (.forallE
    (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    H.succ.succ.succ.succ.succ.succ 5 2)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    H.succ.succ.succ.succ.succ.succ 4 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    H.succ.succ.succ.succ.succ.succ 3 0)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
    mul.succ.succ.succ.succ.succ.succ 5 4 3)) (ProjectSyntax.encode id (ForcingDiagramOrder.product
    G.succ.succ.succ.succ.succ.succ 2 1 0)))))))))))) (.conj (.forallE (.forallE (.forallE (.forallE (.forallE
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ.succ 4 2)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ.succ 3 1)) (.imp (.mem (.bound 0)
    (.bound W.succ.succ.succ.succ.succ)) (.iff (ProjectSyntax.encode id (ForcingDiagramOrder.product
    G.succ.succ.succ.succ.succ 2 0 1)) (.existsE (.conj (old zero.succ.succ.succ.succ.succ.succ
    D.succ.succ.succ.succ.succ.succ 0 1) (ProjectSyntax.encode id (ForcingDiagramOrder.product
    mul.succ.succ.succ.succ.succ.succ 5 0 4))))))))))))) (.conj (.forallE (.forallE (.forallE (.forallE (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ 3 1)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge H.succ.succ.succ.succ 2 0)) (.iff (ProjectSyntax.encode id
    (ConstructionBaseMonoid.divides W.succ.succ.succ.succ G.succ.succ.succ.succ 1 0)) (ProjectSyntax.encode id
    (ConstructionBaseMonoid.divides D.succ.succ.succ.succ mul.succ.succ.succ.succ 3 2))))))))) (.forallE
    (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ 2 1)) (.imp
    (.mem (.bound 0) (.bound W.succ.succ.succ)) (.iff (ProjectSyntax.encode id (ConstructionBaseMonoid.divides
    W.succ.succ.succ G.succ.succ.succ 1 0)) (ConstructionProbeRawActionSyntax.headDiv w.succ.succ.succ
    D.succ.succ.succ S.succ.succ.succ zero.succ.succ.succ mul.succ.succ.succ A.succ.succ.succ 2 0)))))))))))

theorem embeddingLaws_freeClosed {m : Nat} (w D S zero mul A W G e unit H : Fin m) :
    (embeddingLaws w D S zero mul A W G e unit H).FreeClosed := by
  simp -implicitDefEqProofs [embeddingLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    old_freeClosed,ConstructionProbeRawActionSyntax.headDiv_freeClosed]

theorem embeddingLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A W G e unit H : Fin m) :
    Project.Formula.satisfies env (embeddingLaws w D S zero mul A W G e unit H) ↔
      EmbeddingLaws (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul) (env.bound A)
        (env.bound W) (env.bound G) (env.bound e) (env.bound unit) (env.bound H) := by
  simp only [embeddingLaws,EmbeddingLaws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramOrder.product_semantics (M := M),ConstructionBaseMonoid.divides_semantics (M := M),
    old_semantics hM,ConstructionProbeRawActionSyntax.headDiv_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 10
    (.imp (Project.Formula.isOmega (.bound 0)) (.imp (Project.Formula.isEmpty (.bound 3)) (.imp (.mem (.bound
    3) (.bound 0)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 10) 4 8))
    (.imp (ConstructionProbeAlphabet.alphabet (1 : Fin 10) 4 8 2 9 5 7) (.imp (.mem (.bound 6) (.bound 1))
    (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionProbeWord.wordCarrier 5 6 7 9 10 11
    4) (.conj (old 8 6 13 3) (.conj (ConstructionProbeLetters.representatives 4 4 2) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 1 2 4)) (.conj
    (ConstructionProbeWordMonoidSyntax.multiplicationGraph 5 6 7 8 9 10 11 4 12 1) (.conj
    (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid 4 1 3)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.injection 0 6 4)) (.conj (oldGraph 8 6 0) (.conj (embeddingLaws 5 6 7 8 9 10 4 1 13 3
    0) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical 6 9 13)) (ProjectSyntax.encode id
    (ForcingDiagramPoset.conical 4 1 3)))))))))))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isEmpty,
    ProjectSyntax.freeClosed,ConstructionProbeAlphabet.alphabet_freeClosed,ConstructionProbeWord.wordCarrier_freeClosed,
    old_freeClosed,ConstructionProbeLetters.representatives_freeClosed,
    ConstructionProbeWordMonoidSyntax.multiplicationGraph_freeClosed,oldGraph_freeClosed,embeddingLaws_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    ConstructionProbeAlphabet.alphabet_semantics hM,ConstructionProbeWord.wordCarrier_semantics hM,
    old_semantics hM,ConstructionProbeLetters.representatives_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ConstructionProbeWordMonoidSyntax.multiplicationGraph_semantics hM,oldGraph_semantics hM,embeddingLaws_semantics hM]
  intro hw hz hzw hm hAlpha hb
  obtain ⟨W,hW⟩ := ConstructionProbeWord.exists_word_carrier hM hw (bound 1) (bound 2) (bound 4) (bound 5) (bound 6)
  obtain ⟨unit,hUnit⟩ := exists_old hM hm.1.1 (zero := bound 3)
  obtain ⟨J,G,hJ,hG,hgraph⟩ := exists_multiplication hM hw hz hzw hm hAlpha hW hb
  obtain ⟨H,hH,hOldGraph⟩ := exists_old_graph hM hz hzw hW
  exact ⟨W,unit,J,G,H,hW,hUnit,hJ,hG,hgraph,monoid_laws hM hw hz hzw hm hAlpha hW hb hUnit hgraph,
    hH,hOldGraph,embedding_laws hM hw hz hzw hm hAlpha hW hb hUnit hgraph hOldGraph,
    fun hc => word_conical hM hw hz hzw hc hAlpha hW hUnit hgraph⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeOldEmbeddingSyntax
