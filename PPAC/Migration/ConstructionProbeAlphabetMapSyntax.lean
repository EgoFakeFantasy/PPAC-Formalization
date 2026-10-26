import PPAC.Migration.ConstructionProbeAlphabetMap

namespace PPAC.Migration.ConstructionProbeAlphabetMapSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeAlphabetMap ConstructionProbePath ConstructionProbeLetters ConstructionProbeTransitions
open ConstructionProbeMappedPathSyntax ConstructionProbeLiftHomSyntax ConstructionProbeLettersMapSyntax
open ConstructionProbeAction ConstructionProbeTarget ConstructionProbeAlphabet
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def factorConservation {m : Nat} (N mulN f : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  f.succ.succ.succ.succ.succ 4 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  f.succ.succ.succ.succ.succ 3 0)) (.imp (.mem (.bound 2) (.bound N.succ.succ.succ.succ.succ)) (.imp
  (ProjectSyntax.encode id (ForcingDiagramOrder.product mulN.succ.succ.succ.succ.succ 1 2 0)) (.existsE
  (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ 0 3))))))))))))

theorem factorConservation_freeClosed {m : Nat} (N mulN f : Fin m) : (factorConservation N mulN f).FreeClosed := by
  simp -implicitDefEqProofs [factorConservation, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed]

theorem factorConservation_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (N mulN f : Fin m) :
    Project.Formula.satisfies env (factorConservation N mulN f) ↔
      FactorConservation (env.bound N) (env.bound mulN) (env.bound f) := by
  simp only [factorConservation, FactorConservation, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM), KuratowskiZF.source_edge,
    Project.Formula.satisfies_mem_iff, Project.Term.eval_bound, Project.Formula.satisfies_exists_iff,
    ForcingDiagramOrder.product_semantics (M := M)]
  rfl

def actionMap {m : Nat} (A AN f g : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
  (ForcingDiagramOrder.product A.succ.succ.succ.succ.succ.succ 5 4 3)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ 5 2)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge g.succ.succ.succ.succ.succ.succ 4 1)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge g.succ.succ.succ.succ.succ.succ 3 0)) (ProjectSyntax.encode id
  (ForcingDiagramOrder.product AN.succ.succ.succ.succ.succ.succ 2 1 0))))))))))))

theorem actionMap_freeClosed {m : Nat} (A AN f g : Fin m) : (actionMap A AN f g).FreeClosed := by
  simp -implicitDefEqProofs [actionMap, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed]

theorem actionMap_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (A AN f g : Fin m) :
    Project.Formula.satisfies env (actionMap A AN f g) ↔
      ActionMap (env.bound A) (env.bound AN) (env.bound f) (env.bound g) := by
  simp only [actionMap, ActionMap, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM), KuratowskiZF.source_edge,
    ForcingDiagramOrder.product_semantics (M := M)]
  rfl

def exitMap {m : Nat} (E EN f g : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  E.succ.succ.succ.succ 3 2)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge g.succ.succ.succ.succ 3
  1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ.succ 2 0))
  (ProjectSyntax.encode id (Source.SetLanguage.edge EN.succ.succ.succ.succ 1 0)))))))))

theorem exitMap_freeClosed {m : Nat} (E EN f g : Fin m) : (exitMap E EN f g).FreeClosed := by
  simp -implicitDefEqProofs [exitMap, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed]

theorem exitMap_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (E EN f g : Fin m) :
    Project.Formula.satisfies env (exitMap E EN f g) ↔
      ExitMap (env.bound E) (env.bound EN) (env.bound f) (env.bound g) := by
  simp only [exitMap, ExitMap, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM), KuratowskiZF.source_edge]
  rfl

def coneMap {m : Nat} (S SN A AN f g : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  f.succ.succ.succ.succ 3 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge g.succ.succ.succ.succ 2
  0)) (.iff (inCone SN.succ.succ.succ.succ AN.succ.succ.succ.succ 1 0) (inCone S.succ.succ.succ.succ
  A.succ.succ.succ.succ 3 2))))))))

theorem coneMap_freeClosed {m : Nat} (S SN A AN f g : Fin m) : (coneMap S SN A AN f g).FreeClosed := by
  simp -implicitDefEqProofs [coneMap, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed, inCone_freeClosed]

theorem coneMap_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (S SN A AN f g : Fin m) :
    Project.Formula.satisfies env (coneMap S SN A AN f g) ↔
      ConeMap (env.bound S) (env.bound SN) (env.bound A) (env.bound AN) (env.bound f) (env.bound g) := by
  simp only [coneMap, ConeMap, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM), KuratowskiZF.source_edge,
    Project.Formula.satisfies_iff_iff, inCone_semantics hM]
  rfl

def alphabetSimulation {m : Nat} (S SN A AN E EN f g : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection g S SN)) (.conj (actionMap A AN f g) (.conj
  (exitMap E EN f g) (coneMap S SN A AN f g))))

theorem alphabetSimulation_freeClosed {m : Nat} (S SN A AN E EN f g : Fin m) : (alphabetSimulation S SN A AN E EN f g).FreeClosed := by
  simp -implicitDefEqProofs [alphabetSimulation, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed, actionMap_freeClosed, exitMap_freeClosed, coneMap_freeClosed]

theorem alphabetSimulation_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (S SN A AN E EN f g : Fin m) :
    Project.Formula.satisfies env (alphabetSimulation S SN A AN E EN f g) ↔
      AlphabetSimulation (env.bound S) (env.bound SN) (env.bound A) (env.bound AN) (env.bound E) (env.bound EN) (env.bound f) (env.bound g) := by
  simp only [alphabetSimulation, AlphabetSimulation, Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.injection_semantics (M := M), actionMap_semantics hM, exitMap_semantics hM, coneMap_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 31
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 31) 3 5)) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (2 : Fin 31) 4 6)) (.imp (path (0 : Fin 31)
    1 3 5 7 8 10) (.imp (path (0 : Fin 31) 2 4 6 7 9 11) (.imp (factorTable (0 : Fin 31) 1 3 10 12) (.imp
    (factorTable (0 : Fin 31) 2 4 11 13) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection (20 :
    Fin 31) 1 2)) (.imp (preservesProducts (3 : Fin 31) 4 20) (.imp (factorConservation (2 : Fin 31) 4 20)
    (.imp (factorMap (12 : Fin 31) 13 20) (.imp (representatives (0 : Fin 31) 1 14) (.imp (letters (0 : Fin
    31) 1 3 12 14 16) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (18 : Fin 31) 14 16)) (.imp
    (projectionGraph (0 : Fin 31) 1 3 12 14 18) (.imp (equalityLaw (0 : Fin 31) 1 3 12 18) (.imp
    (representatives (0 : Fin 31) 2 15) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (19 : Fin
    31) 15 17)) (.imp (equalityLaw (0 : Fin 31) 2 4 13 19) (.imp (meetsLaws (0 : Fin 31) 1 3 12) (.imp
    (meetsLaws (0 : Fin 31) 2 4 13) (.imp (actionTable (1 : Fin 31) 3 18 21) (.imp (actionTable (2 : Fin 31) 4
    19 22) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (23 : Fin 31) 0 1)) (.imp (terminalMap
    (23 : Fin 31) 24 20) (.imp (targetGraph (1 : Fin 31) 3 18 23 25) (.imp (targetGraph (2 : Fin 31) 4 19 24
    26) (.imp (exitGraph (3 : Fin 31) 25 27 29) (.imp (exitGraph (4 : Fin 31) 26 28 30) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (20 : Fin 31) 27 28)) (.existsE (.conj (graph (17 : Fin
    32) 19 20 21 0) (.conj (representativeLaw (19 : Fin 32) 20 21 0) (alphabetSimulation (17 : Fin 32) 18 22
    23 30 31 21 0)))))))))))))))))))))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed,
    path_freeClosed, factorTable_freeClosed, preservesProducts_freeClosed, factorConservation_freeClosed,
    factorMap_freeClosed, representatives_freeClosed, letters_freeClosed, projectionGraph_freeClosed,
    equalityLaw_freeClosed, meetsLaws_freeClosed, actionTable_freeClosed, terminalMap_freeClosed,
    targetGraph_freeClosed, exitGraph_freeClosed, graph_freeClosed, representativeLaw_freeClosed,
    alphabetSimulation_freeClosed]

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
    ForcingSupportSize.injection_semantics (M := M), path_semantics hM, factorTable_semantics hM,
    preservesProducts_semantics hM, factorConservation_semantics hM, factorMap_semantics hM,
    representatives_semantics hM, letters_semantics hM, projectionGraph_semantics hM,
    equalityLaw_semantics hM, meetsLaws_semantics hM, actionTable_semantics hM, terminalMap_semantics hM,
    targetGraph_semantics hM, exitGraph_semantics hM, graph_semantics hM, representativeLaw_semantics hM,
    alphabetSimulation_semantics hM]
  exact fun hm hmN hp hpN hF hG hf hPres hFactors hmap hC hL hproj hProjection hEq hCN hprojN hEqN
    hMeets hMeetsN hA hAN hT hTm hK hKN hE hEN hdf =>
      exists_alphabet_simulation hM hm hmN hp hpN hF hG hf hPres hFactors hmap hC hL hproj hProjection hEq
        hCN hprojN hEqN hMeets hMeetsN hA hAN hT hTm hK hKN hE hEN hdf

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeAlphabetMapSyntax
