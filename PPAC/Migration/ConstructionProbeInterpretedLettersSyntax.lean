/- Actual quotient interpretation from adjacent relations, in the native object kernel. -/
import PPAC.Migration.ConstructionProbeInterpretedLetters

namespace PPAC.Migration.ConstructionProbeInterpretedLettersSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeInterpretedLetters ConstructionProbePresentationTransitions
open ConstructionProbePresentationTransitionsSyntax ConstructionProbeLiftHomSyntax
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def interpretationGraph {m : Nat} (S f p mulN projection Q : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge Q.succ.succ 1 0))
    (.conj (.mem (.bound 1) (.bound S.succ.succ)) (value f.succ.succ p.succ.succ mulN.succ.succ projection.succ.succ 1 0))))

theorem interpretationGraph_freeClosed {m : Nat} (S f p mulN projection Q : Fin m) :
    (interpretationGraph S f p mulN projection Q).FreeClosed := by
  simp -implicitDefEqProofs [interpretationGraph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,value_freeClosed]

theorem interpretationGraph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (S f p mulN projection Q : Fin m) :
    Project.Formula.satisfies env (interpretationGraph S f p mulN projection Q) ↔
      InterpretationGraph (env.bound S) (env.bound f) (env.bound p) (env.bound mulN) (env.bound projection) (env.bound Q) := by
  simp only [interpretationGraph,InterpretationGraph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,value_semantics hM]
  rfl

def representativeLaw {m : Nat} (f p mulN projection Q : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
    (ForcingDiagramOrder.product projection.succ.succ.succ.succ.succ.succ 5 4 3)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ 4 2)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge p.succ.succ.succ.succ.succ.succ 5 1)) (.iff (ProjectSyntax.encode id
    (Source.SetLanguage.edge Q.succ.succ.succ.succ.succ.succ 3 0)) (ProjectSyntax.encode id
    (ForcingDiagramOrder.product mulN.succ.succ.succ.succ.succ.succ 2 1 0))))))))))))

theorem representativeLaw_freeClosed {m : Nat} (f p mulN projection Q : Fin m) :
    (representativeLaw f p mulN projection Q).FreeClosed := by
  simp -implicitDefEqProofs [representativeLaw,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem representativeLaw_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (f p mulN projection Q : Fin m) :
    Project.Formula.satisfies env (representativeLaw f p mulN projection Q) ↔
      (∀ i x s fx pi y, ForcingDiagramOrder.Product (env.bound projection) i x s →
        PureKuratowski.PairMember M x fx (env.bound f) → PureKuratowski.PairMember M i pi (env.bound p) →
        (PureKuratowski.PairMember M s y (env.bound Q) ↔ ForcingDiagramOrder.Product (env.bound mulN) fx pi y)) := by
  simp only [representativeLaw,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_iff_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramOrder.product_semantics (M := M),KuratowskiZF.source_edge]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 18
    (.imp (Project.Formula.isOmega (.bound 0)) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 18) 2 3)) (.imp (ConstructionProbePath.path (0 : Fin 18) 1 2
    3 4 5 6) (.imp (ConstructionProbePath.factorTable (0 : Fin 18) 1 2 6 7) (.imp
    (ConstructionProbeLetters.representatives (0 : Fin 18) 1 8) (.imp (ConstructionProbeLetters.letters (0 : Fin
    18) 1 2 7 8 9) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (10 : Fin 18) 8 9)) (.imp
    (ConstructionProbeLetters.projectionGraph (0 : Fin 18) 1 2 7 8 10) (.imp
    (ConstructionProbeLetters.equalityLaw (0 : Fin 18) 1 2 7 10) (.imp (ConstructionProbeAction.actionTable (1 :
    Fin 18) 2 10 11) (.imp (ConstructionProbeLetters.representatives (12 : Fin 18) 12 13) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (15 : Fin 18) 13 12)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (16 : Fin 18) 1 12)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo
    (17 : Fin 18) 0 12)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (16 : Fin 18) 3 14)) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.unit (12 : Fin 18) 15 14)) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.associative (12 : Fin 18) 15)) (.imp (preservesProducts (2 : Fin 18) 15 16) (.imp
    (adjacent (0 : Fin 18) 7 16 17 15) (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 0 10
    13)) (.conj (interpretationGraph 10 17 18 16 11 0) (.conj (representativeLaw 17 18 16 11 0) (equivariant 12
    17 0 16))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbePath.path_freeClosed,ConstructionProbePath.factorTable_freeClosed,
      ConstructionProbeLetters.representatives_freeClosed,ConstructionProbeLetters.letters_freeClosed,
      ConstructionProbeLetters.projectionGraph_freeClosed,ConstructionProbeLetters.equalityLaw_freeClosed,
      ConstructionProbeAction.actionTable_freeClosed,preservesProducts_freeClosed,adjacent_freeClosed,
      interpretationGraph_freeClosed,representativeLaw_freeClosed,equivariant_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbePath.path_semantics hM,
    ConstructionProbePath.factorTable_semantics hM,ConstructionProbeLetters.representatives_semantics hM,
    ConstructionProbeLetters.letters_semantics hM,ConstructionProbeLetters.projectionGraph_semantics hM,
    ConstructionProbeLetters.equalityLaw_semantics hM,ConstructionProbeAction.actionTable_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),KuratowskiZF.source_edge,
    ForcingDiagramPoset.unit_semantics (M := M),ForcingDiagramPoset.associative_semantics (M := M),
    preservesProducts_semantics hM,adjacent_semantics hM,interpretationGraph_semantics hM,
    representativeLaw_semantics hM,equivariant_semantics hM]
  intro hw hm hPath hFactor hC hS hProj hProjection hEq hAction hJ hMul hf hp hOne hUnit hAssoc hPres hAdj
  have hAll := transitions_from_adjacent hM hw hm hPath hFactor hf hp hOne hUnit hAssoc hPres hAdj
  obtain ⟨Q,hQ,hGraph⟩ := exists_interpretation hM hm hFactor hC hS hProjection hEq hJ hMul hf hp hAssoc hPres hAll
  refine ⟨Q,hQ,hGraph,?_,interpretation_equivariant hM hm hFactor hC hProj hEq hAction hJ hMul hf hp hAssoc hPres hAll hGraph⟩
  intro i x s fx pi y hxs hfx hpi
  exact interpretation_mk hM hm hFactor hProj hEq hJ hMul hf hp hAssoc hPres hAll hGraph hxs hfx hpi

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeInterpretedLettersSyntax
