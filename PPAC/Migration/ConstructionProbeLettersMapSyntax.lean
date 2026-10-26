import PPAC.Migration.ConstructionProbeLettersMap

namespace PPAC.Migration.ConstructionProbeLettersMapSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeLettersMap ConstructionProbePath ConstructionProbeLetters
open ConstructionProbeMappedPathSyntax ConstructionProbeLiftHomSyntax
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def graph {m : Nat} (S projection projectionN f g : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge g.succ.succ 1 0)) (.conj (.mem
  (.bound 1) (.bound S.succ.succ)) (value projection.succ.succ projectionN.succ.succ f.succ.succ 1 0)))))

theorem graph_freeClosed {m : Nat} (S projection projectionN f g : Fin m) :
    (graph S projection projectionN f g).FreeClosed := by
  simp -implicitDefEqProofs [graph, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed, value_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (S projection projectionN f g : Fin m) :
    Project.Formula.satisfies env (graph S projection projectionN f g) ↔
      Graph (env.bound S) (env.bound projection) (env.bound projectionN) (env.bound f) (env.bound g) := by
  simp only [graph, Graph, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_mem_iff, value_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM), KuratowskiZF.source_edge,
    Project.Term.eval_bound]
  rfl

def RepresentativeLaw (projection projectionN f g : M.Carrier .set) : Prop := ∀ i x fx s t,
  ForcingDiagramOrder.Product projection i x s → PureKuratowski.PairMember M x fx f →
    (PureKuratowski.PairMember M s t g ↔ ForcingDiagramOrder.Product projectionN i fx t)

def representativeLaw {m : Nat} (projection projectionN f g : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
  (ForcingDiagramOrder.product projection.succ.succ.succ.succ.succ 4 3 1)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ.succ 3 2)) (.iff (ProjectSyntax.encode id
  (Source.SetLanguage.edge g.succ.succ.succ.succ.succ 1 0)) (ProjectSyntax.encode id
  (ForcingDiagramOrder.product projectionN.succ.succ.succ.succ.succ 4 2 0))))))))))

theorem representativeLaw_freeClosed {m : Nat} (projection projectionN f g : Fin m) :
    (representativeLaw projection projectionN f g).FreeClosed := by
  simp -implicitDefEqProofs [representativeLaw, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed]

theorem representativeLaw_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (projection projectionN f g : Fin m) :
    Project.Formula.satisfies env (representativeLaw projection projectionN f g) ↔
      RepresentativeLaw (env.bound projection) (env.bound projectionN) (env.bound f) (env.bound g) := by
  simp only [representativeLaw, RepresentativeLaw, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM), KuratowskiZF.source_edge,
    ForcingDiagramOrder.product_semantics (M := M)]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 21
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 21) 3 5)) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (2 : Fin 21) 4 6)) (.imp (path (0 : Fin 21)
    1 3 5 7 8 10) (.imp (path (0 : Fin 21) 2 4 6 7 9 11) (.imp (factorTable (0 : Fin 21) 1 3 10 12) (.imp
    (factorTable (0 : Fin 21) 2 4 11 13) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (20 : Fin
    21) 1 2)) (.imp (preservesProducts (3 : Fin 21) 4 20) (.imp (factorMap (12 : Fin 21) 13 20) (.imp
    (representatives (0 : Fin 21) 1 14) (.imp (letters (0 : Fin 21) 1 3 12 14 16) (.imp (ProjectSyntax.encode
    id (Source.SetLanguage.mapsTo (18 : Fin 21) 14 16)) (.imp (projectionGraph (0 : Fin 21) 1 3 12 14 18)
    (.imp (equalityLaw (0 : Fin 21) 1 3 12 18) (.imp (representatives (0 : Fin 21) 2 15) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (19 : Fin 21) 15 17)) (.imp (equalityLaw (0 : Fin 21)
    2 4 13 19) (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 22) 17 18))
    (.conj (graph (17 : Fin 22) 19 20 21 0) (.conj (representativeLaw (19 : Fin 22) 20 21 0) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.injection (21 : Fin 22) 2 3)) (ProjectSyntax.encode id
    (Source.SetLanguage.injection (0 : Fin 22) 17 18))))))))))))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed,
    path_freeClosed, factorTable_freeClosed, factorMap_freeClosed, preservesProducts_freeClosed,
    representatives_freeClosed, letters_freeClosed, projectionGraph_freeClosed, equalityLaw_freeClosed,
    graph_freeClosed, representativeLaw_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M), ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M), path_semantics hM, factorTable_semantics hM,
    factorMap_semantics hM, preservesProducts_semantics hM, representatives_semantics hM,
    letters_semantics hM, projectionGraph_semantics hM, equalityLaw_semantics hM,
    graph_semantics hM, representativeLaw_semantics hM]
  intro hm hmN hp hpN hF hG hf hPres hmap hC hL hproj hProjection hEq hCN hprojN hEqN
  obtain ⟨g,hgm,hg⟩ := exists_graph hM hm hf hF hPres hmap hC hL hProjection hEq hCN hprojN hEqN
  refine ⟨g,hgm,hg,?_,?_⟩
  · intro i x fx s t hxs hfx
    exact map_letter hM hm hf hF hPres hmap hC hproj hEq hCN hprojN hEqN hg hxs hfx
  · intro hfi
    exact graph_injective hm hmN hp hpN hF hG hfi hPres hmap hEq hEqN hgm hg

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeLettersMapSyntax
