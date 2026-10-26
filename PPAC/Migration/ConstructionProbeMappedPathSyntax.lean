import PPAC.Migration.ConstructionProbeMappedPath

namespace PPAC.Migration.ConstructionProbeMappedPathSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeMappedPath ConstructionProbePath
open ConstructionProbeLiftHomSyntax
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def nodeMap {m : Nat} (node f mapped : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge mapped.succ.succ 1 0)) (.existsE
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge node.succ.succ.succ 2 0)) (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ 0 1)))))))

theorem nodeMap_freeClosed {m : Nat} (node f mapped : Fin m) : (nodeMap node f mapped).FreeClosed := by
  simp -implicitDefEqProofs [nodeMap, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed]

theorem nodeMap_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (node f mapped : Fin m) :
    Project.Formula.satisfies env (nodeMap node f mapped) ↔
      NodeMap (env.bound node) (env.bound f) (env.bound mapped) := by
  simp only [nodeMap, NodeMap, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge]
  rfl

def factorMap {m : Nat} (F G f : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
  F.succ.succ.succ.succ 3 2 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ.succ
  1 0)) (ProjectSyntax.encode id (ForcingDiagramOrder.product G.succ.succ.succ.succ 3 2 0))))))))

theorem factorMap_freeClosed {m : Nat} (F G f : Fin m) : (factorMap F G f).FreeClosed := by
  simp -implicitDefEqProofs [factorMap, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed]

theorem factorMap_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (F G f : Fin m) :
    Project.Formula.satisfies env (factorMap F G f) ↔
      FactorMap (env.bound F) (env.bound G) (env.bound f) := by
  simp only [factorMap, FactorMap, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge, ForcingDiagramOrder.product_semantics (M := M)]
  rfl

def terminalMap {m : Nat} (T U f : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge T.succ.succ.succ 2 1))
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ 1 0)) (ProjectSyntax.encode id
  (Source.SetLanguage.edge U.succ.succ.succ 2 0)))))))

theorem terminalMap_freeClosed {m : Nat} (T U f : Fin m) : (terminalMap T U f).FreeClosed := by
  simp -implicitDefEqProofs [terminalMap, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed]

theorem terminalMap_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (T U f : Fin m) :
    Project.Formula.satisfies env (terminalMap T U f) ↔
      TerminalMap (env.bound T) (env.bound U) (env.bound f) := by
  simp only [terminalMap, TerminalMap, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 14
    (.imp (path (0 : Fin 14) 1 2 3 4 5 6) (.imp (factorTable (0 : Fin 14) 1 2 6 7) (.imp (terminalTable (0 :
    Fin 14) 1 2 6 5 8) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (9 : Fin 14) 10
    11)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (12 : Fin 14) 1 9)) (.imp
    (preservesProducts (2 : Fin 14) 10 12) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (12 : Fin
    14) 3 11)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (12 : Fin 14) 5 13)) (.existsE
    (.existsE (.existsE (.existsE (.conj (nodeMap (10 : Fin 18) 16 3) (.conj (path (4 : Fin 18) 13 14 15 8 17
    3) (.conj (orderedPairs (4 : Fin 18) 2) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (1 :
    Fin 18) 2 13)) (.conj (factorTable (4 : Fin 18) 13 14 3 1) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (0 : Fin 18) 4 13)) (.conj (terminalTable (4 : Fin 18) 13 14 3 17 0) (.conj
    (factorMap (11 : Fin 18) 1 16) (terminalMap (12 : Fin 18) 0 16)))))))))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed,
    path_freeClosed, factorTable_freeClosed, terminalTable_freeClosed, orderedPairs_freeClosed,
    nodeMap_freeClosed, factorMap_freeClosed, terminalMap_freeClosed, preservesProducts_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM), KuratowskiZF.source_edge,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M), ForcingSupportSize.mapsTo_semantics (M := M),
    path_semantics hM, factorTable_semantics hM, terminalTable_semantics hM, orderedPairs_semantics hM,
    nodeMap_semantics hM, factorMap_semantics hM, terminalMap_semantics hM, preservesProducts_semantics hM]
  exact fun hp hF hT hmN hf hPres hOne ha => exists_mapped_path hM hp hF hT hmN hf hPres hOne ha

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeMappedPathSyntax
