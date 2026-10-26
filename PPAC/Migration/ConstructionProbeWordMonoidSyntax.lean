/- Pure membership certificate for the actual source Word left-cancel monoid. -/
import PPAC.Migration.ConstructionProbeWordMonoid

namespace PPAC.Migration.ConstructionProbeWordMonoidSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeWordMonoid
open ConstructionProbeWord (WordCarrier)
open ForcingDiagramOrder (Product product product_semantics)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def multiplicationGraph {m : Nat} (w D S zero mul A b W E G : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.iff (ProjectSyntax.encode id (product G.succ.succ.succ 2 1 0))
    (.conj (.mem (.bound 2) (.bound W.succ.succ.succ))
      (ConstructionProbeEvaluationSyntax.eval w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ zero.succ.succ.succ mul.succ.succ.succ A.succ.succ.succ b.succ.succ.succ W.succ.succ.succ E.succ.succ.succ 2 1 0)))))

theorem multiplicationGraph_freeClosed {m : Nat} (w D S zero mul A b W E G : Fin m) :
    (multiplicationGraph w D S zero mul A b W E G).FreeClosed := by
  simp -implicitDefEqProofs [multiplicationGraph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionProbeEvaluationSyntax.eval_freeClosed]

theorem multiplicationGraph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A b W E G : Fin m) :
    Project.Formula.satisfies env (multiplicationGraph w D S zero mul A b W E G) ↔
      MultiplicationGraph hM (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul)
        (env.bound A) (env.bound b) (env.bound W) (env.bound E) (env.bound G) := by
  simp only [multiplicationGraph,MultiplicationGraph,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    product_semantics (M := M),ConstructionProbeEvaluationSyntax.eval_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 10
    (.imp (Project.Formula.isOmega (.bound 0)) (.imp (Project.Formula.isEmpty (.bound 3)) (.imp (.mem
      (.bound 3) (.bound 0)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 :
      Fin 10) 4 8)) (.imp (ConstructionProbeAlphabet.alphabet (1 : Fin 10) 4 8 2 9 5 7) (.imp (.mem
      (.bound 6) (.bound 1)) (.existsE (.existsE (.existsE (.existsE (.conj
      (ConstructionProbeWord.wordCarrier (4 : Fin 14) 5 6 8 9 10 3) (.conj (old (7 : Fin 14) 5 12 2)
      (.conj (ConstructionProbeLetters.representatives (3 : Fin 14) 3 1) (.conj (ProjectSyntax.encode id
      (Source.SetLanguage.mapsTo (0 : Fin 14) 1 3)) (.conj (multiplicationGraph (4 : Fin 14) 5 6 7 8 9 10
      3 11 0) (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (3 : Fin 14) 0
      2)))))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isEmpty,
    ProjectSyntax.freeClosed,ConstructionProbeAlphabet.alphabet_freeClosed,ConstructionProbeWord.wordCarrier_freeClosed,
    old_freeClosed,ConstructionProbeLetters.representatives_freeClosed,multiplicationGraph_freeClosed]

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
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeAlphabet.alphabet_semantics hM,
    ConstructionProbeWord.wordCarrier_semantics hM,old_semantics hM,ConstructionProbeLetters.representatives_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),multiplicationGraph_semantics hM]
  intro hw hz hzw hm hAlpha hb
  obtain ⟨W,hW⟩ := ConstructionProbeWord.exists_word_carrier hM hw (bound 1) (bound 2) (bound 4) (bound 5) (bound 6)
  obtain ⟨unit,hUnit⟩ := exists_old hM hm.1.1 (zero := bound 3)
  obtain ⟨J,G,hJ,hG,hgraph⟩ := exists_multiplication hM hw hz hzw hm hAlpha hW hb
  exact ⟨W,unit,J,G,hW,hUnit,hJ,hG,hgraph,monoid_laws hM hw hz hzw hm hAlpha hW hb hUnit hgraph⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeWordMonoidSyntax
