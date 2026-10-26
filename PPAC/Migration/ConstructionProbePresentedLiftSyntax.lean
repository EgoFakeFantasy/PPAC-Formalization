/- Native object existence and uniqueness of the pinned indexed presented homomorphism. -/
import PPAC.Migration.ConstructionProbePresentedLift

namespace PPAC.Migration.ConstructionProbePresentedLiftSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbePresentedLift ConstructionProbeLiftHomSyntax
open ConstructionProbePresentationTransitionsSyntax ConstructionProbeIndexedGeneratorsSyntax
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def indexedExit {m : Nat} (terminal mul d b f p mulN : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge terminal.succ.succ.succ.succ.succ.succ 5 4)) (.imp (ProjectSyntax.encode id
    (ForcingDiagramOrder.product mul.succ.succ.succ.succ.succ.succ 4 d.succ.succ.succ.succ.succ.succ 3)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge p.succ.succ.succ.succ.succ.succ 5 2)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ
    b.succ.succ.succ.succ.succ.succ 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    f.succ.succ.succ.succ.succ.succ 3 0)) (ProjectSyntax.encode id (ForcingDiagramOrder.product
    mulN.succ.succ.succ.succ.succ.succ 2 1 0)))))))))))))

theorem indexedExit_freeClosed {m : Nat} (terminal mul d b f p mulN : Fin m) :
    (indexedExit terminal mul d b f p mulN).FreeClosed := by
  simp -implicitDefEqProofs [indexedExit,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem indexedExit_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (terminal mul d b f p mulN : Fin m) :
    Project.Formula.satisfies env (indexedExit terminal mul d b f p mulN) ↔
      IndexedExit (env.bound terminal) (env.bound mul) (env.bound d) (env.bound b) (env.bound f) (env.bound p) (env.bound mulN) := by
  simp only [indexedExit,IndexedExit,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramOrder.product_semantics (M := M),KuratowskiZF.source_edge]
  rfl

def presentedLaws {m : Nat} (zero D G mulN unit eN f p P L : Fin m) : Project.Formula 1 m :=
  .conj (basicLiftLaws zero D G mulN unit eN f L)
    (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge P.succ.succ.succ 2 1))
      (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge L.succ.succ.succ 1 0))
        (ProjectSyntax.encode id (Source.SetLanguage.edge p.succ.succ.succ 2 0)))))))

theorem presentedLaws_freeClosed {m : Nat} (zero D G mulN unit eN f p P L : Fin m) :
    (presentedLaws zero D G mulN unit eN f p P L).FreeClosed := by
  simp -implicitDefEqProofs [presentedLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,basicLiftLaws_freeClosed]

theorem presentedLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (zero D G mulN unit eN f p P L : Fin m) :
    Project.Formula.satisfies env (presentedLaws zero D G mulN unit eN f p P L) ↔
      PresentedLaws (env.bound zero) (env.bound D) (env.bound G) (env.bound mulN) (env.bound unit)
        (env.bound eN) (env.bound f) (env.bound p) (env.bound P) (env.bound L) := by
  simp only [presentedLaws,PresentedLaws,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,basicLiftLaws_semantics hM]
  rfl

def probeRelations {m : Nat} (zero D mul b d terminal factor P G : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge P.succ.succ.succ.succ.succ.succ 5 4)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge terminal.succ.succ.succ.succ.succ.succ 5 3)) (.imp (ProjectSyntax.encode id
    (ForcingDiagramOrder.product mul.succ.succ.succ.succ.succ.succ 3 d.succ.succ.succ.succ.succ.succ 2)) (.imp
    (old zero.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ b.succ.succ.succ.succ.succ.succ 1)
    (.imp (old zero.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ 2 0) (ProjectSyntax.encode id
    (ForcingDiagramOrder.product G.succ.succ.succ.succ.succ.succ 4 1 0))))))))))))) (.forallE (.forallE
    (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
    factor.succ.succ.succ.succ.succ.succ 5 4 3)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    P.succ.succ.succ.succ.succ.succ 5 2)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    P.succ.succ.succ.succ.succ.succ 4 1)) (.imp (old zero.succ.succ.succ.succ.succ.succ
    D.succ.succ.succ.succ.succ.succ 3 0) (ProjectSyntax.encode id (ForcingDiagramOrder.product
    G.succ.succ.succ.succ.succ.succ 0 1 2)))))))))))))

theorem probeRelations_freeClosed {m : Nat} (zero D mul b d terminal factor P G : Fin m) :
    (probeRelations zero D mul b d terminal factor P G).FreeClosed := by
  simp -implicitDefEqProofs [probeRelations,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,old_freeClosed]

theorem probeRelations_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (zero D mul b d terminal factor P G : Fin m) :
    Project.Formula.satisfies env (probeRelations zero D mul b d terminal factor P G) ↔
      ProbeRelations (env.bound zero) (env.bound D) (env.bound mul) (env.bound b) (env.bound d)
        (env.bound terminal) (env.bound factor) (env.bound P) (env.bound G) := by
  simp only [probeRelations,ProbeRelations,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramOrder.product_semantics (M := M),KuratowskiZF.source_edge,old_semantics hM]
  rfl

/-- The actual Word and probe graphs are the previously constructed source objects.
The lift is constructed here; no existence or uniqueness field is assumed. -/
def universalSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 29
    (.imp (Project.Formula.isOmega (.bound 0)) (.imp (Project.Formula.isEmpty (.bound 3)) (.imp (.mem (.bound 3)
    (.bound 0)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 29) 4 9)) (.imp
    (ConstructionProbeAlphabet.alphabet (1 : Fin 29) 4 9 2 10 5 8) (.imp (ConstructionProbeWord.wordCarrier (0 :
    Fin 29) 1 2 4 5 6 7) (.imp (.mem (.bound 6) (.bound 1)) (.imp (old (3 : Fin 29) 1 9 12) (.imp
    (ConstructionProbeWordMonoidSyntax.multiplicationGraph (0 : Fin 29) 1 2 3 4 5 6 7 8 11) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (13 : Fin 29) 2 7)) (.imp
    (ConstructionProbeGeneratorSyntax.generatorGraph (0 : Fin 29) 1 2 12 13) (.imp
    (ConstructionProbeLetters.representatives (0 : Fin 29) 1 14) (.imp (ConstructionProbeLetters.letters (0 :
    Fin 29) 1 4 15 14 2) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (16 : Fin 29) 14 2)) (.imp
    (ConstructionProbeLetters.projectionGraph (0 : Fin 29) 1 4 15 14 16) (.imp
    (ConstructionProbeLetters.equalityLaw (0 : Fin 29) 1 4 15 16) (.imp (ConstructionProbeAction.actionTable (1
    : Fin 29) 4 16 5) (.imp (ConstructionProbePath.path (0 : Fin 29) 1 4 9 3 25 24) (.imp
    (ConstructionProbePath.factorTable (0 : Fin 29) 1 4 24 15) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (17 : Fin 29) 0 7)) (.imp (probeGraph (0 : Fin 29) 16 9 13 17) (.imp
    (ConstructionProbeLetters.representatives (18 : Fin 29) 18 19) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (20 : Fin 29) 19 18)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo
    (22 : Fin 29) 1 18)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (23 : Fin 29) 0 18)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (22 : Fin 29) 9 21)) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.unit (18 : Fin 29) 20 21)) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.associative (18 : Fin 29) 20)) (.imp (preservesProducts (4 : Fin 29) 20 22) (.imp
    (adjacent (0 : Fin 29) 15 22 23 20) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (26 : Fin 29)
    0 1)) (.imp (ConstructionProbeTarget.targetGraph (1 : Fin 29) 4 16 26 27) (.imp
    (ConstructionProbeAlphabet.exitGraph (4 : Fin 29) 27 28 8) (.imp (.mem (.bound 28) (.bound 1)) (.imp
    (indexedExit (26 : Fin 29) 4 28 6 22 23 20) (.conj (probeRelations (3 : Fin 29) 1 4 6 28 26 15 17 11) (.existsE (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (0 : Fin 30) 8 19)) (.conj (presentedLaws (4 : Fin 30) 2 12 21 13 22 23 24 18 0)
    (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 31) 9 20)) (.imp (presentedLaws
    (5 : Fin 31) 3 13 22 14 23 24 25 19 0) (Project.Formula.extensionalEq (.bound 0) (.bound
    1))))))))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isEmpty,
      Project.Formula.extensionalEq,ProjectSyntax.freeClosed,ConstructionProbeAlphabet.alphabet_freeClosed,
      ConstructionProbeWord.wordCarrier_freeClosed,old_freeClosed,ConstructionProbeWordMonoidSyntax.multiplicationGraph_freeClosed,
      ConstructionProbeGeneratorSyntax.generatorGraph_freeClosed,ConstructionProbeLetters.representatives_freeClosed,
      ConstructionProbeLetters.letters_freeClosed,ConstructionProbeLetters.projectionGraph_freeClosed,
      ConstructionProbeLetters.equalityLaw_freeClosed,ConstructionProbeAction.actionTable_freeClosed,
      ConstructionProbePath.path_freeClosed,ConstructionProbePath.factorTable_freeClosed,probeGraph_freeClosed,
      preservesProducts_freeClosed,adjacent_freeClosed,ConstructionProbeTarget.targetGraph_freeClosed,
      ConstructionProbeAlphabet.exitGraph_freeClosed,indexedExit_freeClosed,presentedLaws_freeClosed,probeRelations_freeClosed]

theorem universal_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence universalSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) universalSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeAlphabet.alphabet_semantics hM,
    ConstructionProbeWord.wordCarrier_semantics hM,old_semantics hM,
    ConstructionProbeWordMonoidSyntax.multiplicationGraph_semantics hM,
    ConstructionProbeGeneratorSyntax.generatorGraph_semantics hM,ConstructionProbeLetters.representatives_semantics hM,
    ConstructionProbeLetters.letters_semantics hM,ConstructionProbeLetters.projectionGraph_semantics hM,
    ConstructionProbeLetters.equalityLaw_semantics hM,ConstructionProbeAction.actionTable_semantics hM,
    ConstructionProbePath.path_semantics hM,ConstructionProbePath.factorTable_semantics hM,probeGraph_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),KuratowskiZF.source_edge,
    ForcingDiagramPoset.unit_semantics (M := M),ForcingDiagramPoset.associative_semantics (M := M),
    preservesProducts_semantics hM,adjacent_semantics hM,ConstructionProbeTarget.targetGraph_semantics hM,
    ConstructionProbeAlphabet.exitGraph_semantics hM,indexedExit_semantics hM,presentedLaws_semantics hM,probeRelations_semantics hM]
  intro hw hz hzw hm hAlpha hW hb hUnit hG hK hGen hC hLetters hProj hProjection hEq hAction
    hPath hFactor hP hProbe hJ hMul hf hp hOne hUnitN hAssoc hPres hAdj hT hTarget hExit hd hExitRel
  refine ⟨probe_relations hM hw hz hzw hm hAlpha hW hb hUnit hG hK hGen hC hProj hEq hAction
    hPath hFactor hProbe hT hTarget hExit,?_⟩
  exact existsUnique_presentedHom hM hw hz hzw hm hAlpha hW hb hUnit hG hK hGen hC hLetters hProj
    hProjection hEq hAction hPath hFactor hP hProbe hJ hMul hf hp hOne hUnitN hAssoc hPres hAdj
    hT hTarget hExit hd hExitRel

theorem universal_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence universalSentence) := ModelTransfer.derives (fun _ hM => universal_models hM)

end PPAC.Migration.ConstructionProbePresentedLiftSyntax
