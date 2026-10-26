/- Native certificate for actual indexed probes and Path.presentedHom_ext. -/
import PPAC.Migration.ConstructionProbeIndexedGenerators

namespace PPAC.Migration.ConstructionProbeIndexedGeneratorsSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeLiftHom ConstructionProbeHomExt
open ConstructionProbeHomExtSyntax ConstructionProbeLiftHomSyntax
open ConstructionProbeIndexedGenerators
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def probeGraph {m : Nat} (w projection e K P : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge P.succ.succ 1 0))
    (.conj (.mem (.bound 1) (.bound w.succ.succ)) (probe projection.succ.succ e.succ.succ K.succ.succ 1 0))))

theorem probeGraph_freeClosed {m : Nat} (w projection e K P : Fin m) : (probeGraph w projection e K P).FreeClosed := by
  simp -implicitDefEqProofs [probeGraph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,probe_freeClosed]

theorem probeGraph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w projection e K P : Fin m) :
    Project.Formula.satisfies env (probeGraph w projection e K P) ↔
      ProbeGraph (env.bound w) (env.bound projection) (env.bound e) (env.bound K) (env.bound P) := by
  simp only [probeGraph,ProbeGraph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,probe_semantics hM]
  rfl

def IndexedHomExt (zero D W G P : M.Carrier .set) : Prop := ∀ N J mulN F H,
  MapsTo J N mulN → MapsTo W N F → MapsTo W N H →
  PreservesProducts G mulN F → PreservesProducts G mulN H →
  (∀ x q, Old zero D x q → AgreeAt q F H) →
  (∀ i q, PureKuratowski.PairMember M i q P → AgreeAt q F H) → F = H

def indexedHomExt {m : Nat} (zero D W G P : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 2
    3 4)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 1 W.succ.succ.succ.succ.succ 4)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 0 W.succ.succ.succ.succ.succ 4)) (.imp
    (preservesProducts G.succ.succ.succ.succ.succ 2 1) (.imp (preservesProducts G.succ.succ.succ.succ.succ 2 0)
    (.imp (oldAgreement zero.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ 1 0) (.imp (generatorAgreement
    P.succ.succ.succ.succ.succ 1 0) (Project.Formula.extensionalEq (.bound 1) (.bound 0))))))))))))))

theorem indexedHomExt_freeClosed {m : Nat} (zero D W G P : Fin m) : (indexedHomExt zero D W G P).FreeClosed := by
  simp -implicitDefEqProofs [indexedHomExt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    preservesProducts_freeClosed,oldAgreement_freeClosed,generatorAgreement_freeClosed,Project.Formula.extensionalEq]

theorem indexedHomExt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (zero D W G P : Fin m) :
    Project.Formula.satisfies env (indexedHomExt zero D W G P) ↔
      IndexedHomExt (env.bound zero) (env.bound D) (env.bound W) (env.bound G) (env.bound P) := by
  simp only [indexedHomExt,IndexedHomExt,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),
    preservesProducts_semantics hM,oldAgreement_semantics hM,generatorAgreement_semantics hM,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl

/-- Construct the indexed probe graph and prove its homomorphism-determination property. -/
def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 17
    (.imp (Project.Formula.isOmega (.bound 0)) (.imp (Project.Formula.isEmpty (.bound 3)) (.imp (.mem (.bound 3)
    (.bound 0)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 17) 4 9)) (.imp
    (ConstructionProbeAlphabet.alphabet (1 : Fin 17) 4 9 2 10 5 8) (.imp (ConstructionProbeWord.wordCarrier (0 :
    Fin 17) 1 2 4 5 6 7) (.imp (.mem (.bound 6) (.bound 1)) (.imp (old (3 : Fin 17) 1 9 12) (.imp
    (ConstructionProbeWordMonoidSyntax.multiplicationGraph (0 : Fin 17) 1 2 3 4 5 6 7 8 11) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (13 : Fin 17) 2 7)) (.imp
    (ConstructionProbeGeneratorSyntax.generatorGraph (0 : Fin 17) 1 2 12 13) (.imp
    (ConstructionProbeLetters.representatives (0 : Fin 17) 1 14) (.imp (ConstructionProbeLetters.letters (0 :
    Fin 17) 1 4 15 14 2) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (16 : Fin 17) 14 2)) (.imp
    (ConstructionProbeLetters.projectionGraph (0 : Fin 17) 1 4 15 14 16) (.imp
    (ConstructionProbeAction.actionTable (1 : Fin 17) 4 16 5) (.existsE (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo 0 1 8)) (.conj (probeGraph 1 17 10 14 0) (indexedHomExt 4 2 8 12
    0))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isEmpty,
      ProjectSyntax.freeClosed,ConstructionProbeAlphabet.alphabet_freeClosed,
      ConstructionProbeWord.wordCarrier_freeClosed,old_freeClosed,
      ConstructionProbeWordMonoidSyntax.multiplicationGraph_freeClosed,
      ConstructionProbeGeneratorSyntax.generatorGraph_freeClosed,ConstructionProbeLetters.representatives_freeClosed,
      ConstructionProbeLetters.letters_freeClosed,ConstructionProbeLetters.projectionGraph_freeClosed,
      ConstructionProbeAction.actionTable_freeClosed,probeGraph_freeClosed,indexedHomExt_freeClosed]

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
    ConstructionProbeWord.wordCarrier_semantics hM,old_semantics hM,
    ConstructionProbeWordMonoidSyntax.multiplicationGraph_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbeGeneratorSyntax.generatorGraph_semantics hM,
    ConstructionProbeLetters.representatives_semantics hM,ConstructionProbeLetters.letters_semantics hM,
    ConstructionProbeLetters.projectionGraph_semantics hM,ConstructionProbeAction.actionTable_semantics hM,
    probeGraph_semantics hM,indexedHomExt_semantics hM]
  intro hw hz hzw hm hAlpha hW hb hUnit hG hK hGen hC hLetters hp hProjection hAction
  obtain ⟨P,hP,hProbe⟩ := exists_probe_graph hM hC hp hm.1.1 hK
  refine ⟨P,hP,hProbe,?_⟩
  intro N J mulN F H hMul hF hH hFP hHP hOld hNew
  exact presentedHom_ext hM hw hz hzw hm hAlpha hW hb hUnit hG hK hGen hC hLetters hp
    hProjection hAction hP hProbe hMul hF hH hFP hHP hOld hNew

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeIndexedGeneratorsSyntax
