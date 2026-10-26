/- Pure-set native certificate for the actual simulated probe pushout. -/
import PPAC.Migration.ConstructionProbePushout

namespace PPAC.Migration.ConstructionProbePushoutSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbePushout
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def presentation {m : Nat} (w zero D mul e a b d node factor terminal target S C projection I act E W unit G K P O : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e)) (.conj
    (ConstructionProbeAlphabet.alphabet D mul e S I act E) (.conj (ConstructionProbeWord.wordCarrier w D S
    mul act b W) (.conj (.mem (.bound b) (.bound D)) (.conj (ConstructionProbeRaw.old zero D e unit) (.conj
    (ConstructionProbeWordMonoidSyntax.multiplicationGraph w D S zero mul act b W E G) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo K S W)) (.conj
    (ConstructionProbeGeneratorSyntax.generatorGraph w D S unit K) (.conj
    (ConstructionProbeLetters.representatives w D C) (.conj (ConstructionProbeLetters.letters w D mul factor
    C S) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo projection C S)) (.conj
    (ConstructionProbeLetters.projectionGraph w D mul factor C projection) (.conj
    (ConstructionProbeLetters.equalityLaw w D mul factor projection) (.conj
    (ConstructionProbeAction.actionTable D mul projection act) (.conj (ConstructionProbePath.path w D mul e
    zero a node) (.conj (ConstructionProbePath.factorTable w D mul node factor) (.conj (ProjectSyntax.encode
    id (Source.SetLanguage.mapsTo P w W)) (.conj (ConstructionProbeIndexedGeneratorsSyntax.probeGraph w
    projection e K P) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo terminal w D)) (.conj
    (ConstructionProbeTarget.targetGraph D mul projection terminal target) (.conj
    (ConstructionProbeAlphabet.exitGraph mul target d E) (.conj (.mem (.bound d) (.bound D)) (.conj
    (ConstructionProbeOldEmbeddingSyntax.oldGraph zero D O) (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo O D W)))))))))))))))))))))))))

theorem presentation_freeClosed {m : Nat} (w zero D mul e a b d node factor terminal target S C projection I act E W unit G K P O : Fin m) :
    (presentation w zero D mul e a b d node factor terminal target S C projection I act E W unit G K P O).FreeClosed := by
  simp -implicitDefEqProofs [presentation,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionProbeAlphabet.alphabet_freeClosed,
    ConstructionProbeWord.wordCarrier_freeClosed,
    ConstructionProbeRaw.old_freeClosed,
    ConstructionProbeWordMonoidSyntax.multiplicationGraph_freeClosed,
    ConstructionProbeGeneratorSyntax.generatorGraph_freeClosed,
    ConstructionProbeLetters.representatives_freeClosed,
    ConstructionProbeLetters.letters_freeClosed,
    ConstructionProbeLetters.projectionGraph_freeClosed,
    ConstructionProbeLetters.equalityLaw_freeClosed,
    ConstructionProbeAction.actionTable_freeClosed,
    ConstructionProbePath.path_freeClosed,
    ConstructionProbePath.factorTable_freeClosed,
    ConstructionProbeIndexedGeneratorsSyntax.probeGraph_freeClosed,
    ConstructionProbeTarget.targetGraph_freeClosed,
    ConstructionProbeAlphabet.exitGraph_freeClosed,
    ConstructionProbeOldEmbeddingSyntax.oldGraph_freeClosed]

theorem presentation_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero D mul e a b d node factor terminal target S C projection I act E W unit G K P O : Fin m) :
    Project.Formula.satisfies env (presentation w zero D mul e a b d node factor terminal target S C projection I act E W unit G K P O) ↔
      Presentation hM (env.bound w) (env.bound zero) (env.bound D) (env.bound mul) (env.bound e) (env.bound a) (env.bound b) (env.bound d) (env.bound node) (env.bound factor) (env.bound terminal) (env.bound target) (env.bound S) (env.bound C) (env.bound projection) (env.bound I) (env.bound act) (env.bound E) (env.bound W) (env.bound unit) (env.bound G) (env.bound K) (env.bound P) (env.bound O) := by
  simp only [presentation,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ConstructionProbeAlphabet.alphabet_semantics hM,
    ConstructionProbeWord.wordCarrier_semantics hM,
    ConstructionProbeRaw.old_semantics hM,
    ConstructionProbeWordMonoidSyntax.multiplicationGraph_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionProbeGeneratorSyntax.generatorGraph_semantics hM,
    ConstructionProbeLetters.representatives_semantics hM,
    ConstructionProbeLetters.letters_semantics hM,
    ConstructionProbeLetters.projectionGraph_semantics hM,
    ConstructionProbeLetters.equalityLaw_semantics hM,
    ConstructionProbeAction.actionTable_semantics hM,
    ConstructionProbePath.path_semantics hM,
    ConstructionProbePath.factorTable_semantics hM,
    ConstructionProbeIndexedGeneratorsSyntax.probeGraph_semantics hM,
    ConstructionProbeTarget.targetGraph_semantics hM,
    ConstructionProbeAlphabet.exitGraph_semantics hM,
    ConstructionProbeOldEmbeddingSyntax.oldGraph_semantics hM]
  constructor
  · rintro ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23⟩
    exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23⟩
  · intro h
    exact ⟨h.monoid,h.alphabet,h.word,h.b_mem,h.old_unit,h.multiplication,h.generators_map,h.generators,h.representatives,h.letters,h.projection_map,h.projection_law,h.equality,h.action,h.path,h.factors,h.probes_map,h.probes,h.terminals_map,h.target_law,h.exit_law,h.d_mem,h.old_graph,h.old_map⟩

def hom {m : Nat} (D N mul mulN e eN F : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo F D N))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge F e eN))
      (ConstructionProbeLiftHomSyntax.preservesProducts mul mulN F))

theorem hom_freeClosed {m : Nat} (D N mul mulN e eN F : Fin m) : (hom D N mul mulN e eN F).FreeClosed := by
  simp -implicitDefEqProofs [hom,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeLiftHomSyntax.preservesProducts_freeClosed]

theorem hom_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D N mul mulN e eN F : Fin m) :
    Project.Formula.satisfies env (hom D N mul mulN e eN F) ↔
      Hom (env.bound D) (env.bound N) (env.bound mul) (env.bound mulN) (env.bound e) (env.bound eN) (env.bound F) := by
  simp only [hom,Hom,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbeLiftHomSyntax.preservesProducts_semantics hM]
  rfl

def squareComm {m : Nat} (O f s t : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    O.succ.succ.succ.succ 3 2)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    f.succ.succ.succ.succ 3 1)) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge
    s.succ.succ.succ.succ 2 0)) (ProjectSyntax.encode id (Source.SetLanguage.edge t.succ.succ.succ.succ 1
    0)))))))))

theorem squareComm_freeClosed {m : Nat} (O f s t : Fin m) : (squareComm O f s t).FreeClosed := by
  simp -implicitDefEqProofs [squareComm,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem squareComm_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (O f s t : Fin m) :
    Project.Formula.satisfies env (squareComm O f s t) ↔ SquareComm (env.bound O) (env.bound f) (env.bound s) (env.bound t) := by
  simp only [squareComm,SquareComm,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_iff_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def isPushout {m : Nat} (N W WN mulN G GN eN unit unitN O f H ON : Fin m) : Project.Formula 1 m :=
  (.conj (squareComm O f H ON) (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp
    (ConstructionProbeLetters.representatives 5 5 4) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo 3 4 5)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.unit 5 3 2))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.associative 5 3)) (.imp (hom
    W.succ.succ.succ.succ.succ.succ 5 G.succ.succ.succ.succ.succ.succ 3 unit.succ.succ.succ.succ.succ.succ 2
    1) (.imp (hom N.succ.succ.succ.succ.succ.succ 5 mulN.succ.succ.succ.succ.succ.succ 3
    eN.succ.succ.succ.succ.succ.succ 2 0) (.imp (squareComm O.succ.succ.succ.succ.succ.succ
    f.succ.succ.succ.succ.succ.succ 1 0) (.existsE (.conj (hom WN.succ.succ.succ.succ.succ.succ.succ 6
    GN.succ.succ.succ.succ.succ.succ.succ 4 unitN.succ.succ.succ.succ.succ.succ.succ 3 0) (.conj
    (ConstructionProbeMappedPathSyntax.nodeMap H.succ.succ.succ.succ.succ.succ.succ 0 2) (.conj
    (ConstructionProbeMappedPathSyntax.nodeMap ON.succ.succ.succ.succ.succ.succ.succ 0 1) (.forallE (.imp
    (hom WN.succ.succ.succ.succ.succ.succ.succ.succ 7 GN.succ.succ.succ.succ.succ.succ.succ.succ 5
    unitN.succ.succ.succ.succ.succ.succ.succ.succ 4 0) (.imp (ConstructionProbeMappedPathSyntax.nodeMap
    H.succ.succ.succ.succ.succ.succ.succ.succ 0 3) (.imp (ConstructionProbeMappedPathSyntax.nodeMap
    ON.succ.succ.succ.succ.succ.succ.succ.succ 0 2) (Project.Formula.extensionalEq (.bound 0) (.bound
    1))))))))))))))))))))))))

theorem isPushout_freeClosed {m : Nat} (N W WN mulN G GN eN unit unitN O f H ON : Fin m) :
    (isPushout N W WN mulN G GN eN unit unitN O f H ON).FreeClosed := by
  simp -implicitDefEqProofs [isPushout,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    squareComm_freeClosed,hom_freeClosed,ConstructionProbeLetters.representatives_freeClosed,
    ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,Project.Formula.extensionalEq]

theorem isPushout_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (N W WN mulN G GN eN unit unitN O f H ON : Fin m) :
    Project.Formula.satisfies env (isPushout N W WN mulN G GN eN unit unitN O f H ON) ↔
      IsPushout (env.bound N) (env.bound W) (env.bound WN) (env.bound mulN) (env.bound G) (env.bound GN) (env.bound eN) (env.bound unit) (env.bound unitN) (env.bound O) (env.bound f) (env.bound H) (env.bound ON) := by
  simp only [isPushout,IsPushout,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionProbeLetters.representatives_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingDiagramPoset.unit_semantics (M := M),ForcingDiagramPoset.associative_semantics (M := M),
    hom_semantics hM,squareComm_semantics hM,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 48
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 48))) (.imp (Project.Formula.isEmpty (.bound (1 : Fin
    48))) (.imp (.mem (.bound (1 : Fin 48)) (.bound (0 : Fin 48))) (.imp (presentation (0 : Fin 48) (1 : Fin
    48) (2 : Fin 48) (3 : Fin 48) (4 : Fin 48) (5 : Fin 48) (6 : Fin 48) (7 : Fin 48) (8 : Fin 48) (9 : Fin
    48) (10 : Fin 48) (11 : Fin 48) (12 : Fin 48) (13 : Fin 48) (14 : Fin 48) (15 : Fin 48) (16 : Fin 48)
    (17 : Fin 48) (18 : Fin 48) (19 : Fin 48) (20 : Fin 48) (21 : Fin 48) (22 : Fin 48) (23 : Fin 48)) (.imp
    (presentation (0 : Fin 48) (1 : Fin 48) (24 : Fin 48) (25 : Fin 48) (26 : Fin 48) (27 : Fin 48) (28 :
    Fin 48) (29 : Fin 48) (30 : Fin 48) (31 : Fin 48) (32 : Fin 48) (33 : Fin 48) (34 : Fin 48) (35 : Fin
    48) (36 : Fin 48) (37 : Fin 48) (38 : Fin 48) (39 : Fin 48) (40 : Fin 48) (41 : Fin 48) (42 : Fin 48)
    (43 : Fin 48) (44 : Fin 48) (45 : Fin 48)) (.imp (ConstructionProbeConservativeSyntax.conservative (2 :
    Fin 48) (24 : Fin 48) (3 : Fin 48) (25 : Fin 48) (46 : Fin 48)) (.imp
    (ConstructionProbeLiftHomSyntax.preservesProducts (3 : Fin 48) (25 : Fin 48) (46 : Fin 48)) (.imp
    (ConstructionProbeAlphabetMapSyntax.alphabetSimulation (12 : Fin 48) (34 : Fin 48) (16 : Fin 48) (38 :
    Fin 48) (17 : Fin 48) (39 : Fin 48) (46 : Fin 48) (47 : Fin 48)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge (46 : Fin 48) (6 : Fin 48) (28 : Fin 48))) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge (46 : Fin 48) (4 : Fin 48) (26 : Fin 48))) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge (46 : Fin 48) (7 : Fin 48) (29 : Fin 48))) (.imp
    (ConstructionProbeMappedPathSyntax.factorMap (9 : Fin 48) (31 : Fin 48) (46 : Fin 48)) (.imp
    (ConstructionProbeMappedPathSyntax.terminalMap (10 : Fin 48) (32 : Fin 48) (46 : Fin 48)) (.imp
    (ConstructionProbeSharedIntersections.conditionalJoins (2 : Fin 48) (3 : Fin 48)) (.imp
    (ConstructionProbeConservativeSyntax.conservative (2 : Fin 48) (18 : Fin 48) (3 : Fin 48) (20 : Fin 48)
    (23 : Fin 48)) (.imp (ConstructionProbeConservativeSyntax.conservative (24 : Fin 48) (40 : Fin 48) (25 :
    Fin 48) (42 : Fin 48) (45 : Fin 48)) (.imp (ConstructionProbeLettersMapSyntax.graph (12 : Fin 48) (14 :
    Fin 48) (36 : Fin 48) (46 : Fin 48) (47 : Fin 48)) (.existsE (.conj
    (ConstructionProbeWordTransport.wordGraph (1 : Fin 49) (3 : Fin 49) (13 : Fin 49) (35 : Fin 49) (47 :
    Fin 49) (48 : Fin 49) (19 : Fin 49) (0 : Fin 49)) (.conj (hom (19 : Fin 49) (41 : Fin 49) (21 : Fin 49)
    (43 : Fin 49) (20 : Fin 49) (42 : Fin 49) (0 : Fin 49)) (.conj
    (ConstructionProbeConservativeSyntax.conservative (19 : Fin 49) (41 : Fin 49) (21 : Fin 49) (43 : Fin
    49) (0 : Fin 49)) (.conj (ConstructionProbeSimulation.endpointLaws (47 : Fin 49) (0 : Fin 49) (24 : Fin
    49) (46 : Fin 49) (23 : Fin 49) (45 : Fin 49)) (isPushout (25 : Fin 49) (19 : Fin 49) (41 : Fin 49) (26
    : Fin 49) (21 : Fin 49) (43 : Fin 49) (27 : Fin 49) (20 : Fin 49) (42 : Fin 49) (24 : Fin 49) (47 : Fin
    49) (0 : Fin 49) (46 : Fin 49))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isEmpty,
      presentation_freeClosed,
      ConstructionProbeConservativeSyntax.conservative_freeClosed,
      ConstructionProbeLiftHomSyntax.preservesProducts_freeClosed,
      ConstructionProbeAlphabetMapSyntax.alphabetSimulation_freeClosed,
      ConstructionProbeMappedPathSyntax.factorMap_freeClosed,
      ConstructionProbeMappedPathSyntax.terminalMap_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ConstructionProbeLettersMapSyntax.graph_freeClosed,
      ConstructionProbeWordTransport.wordGraph_freeClosed,
      hom_freeClosed,
      ConstructionProbeSimulation.endpointLaws_freeClosed,
      isPushout_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    presentation_semantics hM,
    ConstructionProbeConservativeSyntax.conservative_semantics hM,
    ConstructionProbeLiftHomSyntax.preservesProducts_semantics hM,
    ConstructionProbeAlphabetMapSyntax.alphabetSimulation_semantics hM,
    ConstructionProbeMappedPathSyntax.factorMap_semantics hM,
    ConstructionProbeMappedPathSyntax.terminalMap_semantics hM,
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ConstructionProbeLettersMapSyntax.graph_semantics hM,
    ConstructionProbeWordTransport.wordGraph_semantics hM,
    hom_semantics hM,
    ConstructionProbeSimulation.endpointLaws_semantics hM,
    isPushout_semantics hM]
  intro hw hz hzw hA hB hf hPres hAlphabet hb hOne hd hFactor hTerminal hJ hOldA hOldB hLetters
  exact exists_pushout hA hB hw hz hzw hf hPres hAlphabet hb hOne hd hFactor hTerminal hJ hOldA hOldB hLetters

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbePushoutSyntax
