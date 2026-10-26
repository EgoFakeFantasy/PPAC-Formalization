/- Native pure-set certificate for the pinned liftHom into every internal monoid. -/
import PPAC.Migration.ConstructionProbeLiftHom
import PPAC.Migration.ConstructionProbeGeneratorSyntax

namespace PPAC.Migration.ConstructionProbeLiftHomSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeLiftHom
open ConstructionProbeHomEvaluation (Eval)
open ConstructionProbeHomEvaluationSyntax (LiftGraph)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def preservesProducts {m : Nat} (mul mulN F : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
    (ForcingDiagramOrder.product mul.succ.succ.succ.succ.succ.succ 5 4 3)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge F.succ.succ.succ.succ.succ.succ 5 2)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge F.succ.succ.succ.succ.succ.succ 4 1)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge F.succ.succ.succ.succ.succ.succ 3 0)) (ProjectSyntax.encode id
    (ForcingDiagramOrder.product mulN.succ.succ.succ.succ.succ.succ 2 1 0))))))))))))

theorem preservesProducts_freeClosed {m : Nat} (mul mulN F : Fin m) :
    (preservesProducts mul mulN F).FreeClosed := by
  simp -implicitDefEqProofs [preservesProducts,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem preservesProducts_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (mul mulN F : Fin m) :
    Project.Formula.satisfies env (preservesProducts mul mulN F) ↔
      PreservesProducts (env.bound mul) (env.bound mulN) (env.bound F) := by
  simp only [preservesProducts, PreservesProducts, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge, ForcingDiagramOrder.product_semantics (M := M)]
  rfl

def equivariant {m : Nat} (A F Q mulN : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
    (ForcingDiagramOrder.product A.succ.succ.succ.succ.succ.succ 5 4 3)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge F.succ.succ.succ.succ.succ.succ 5 2)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge Q.succ.succ.succ.succ.succ.succ 4 1)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge Q.succ.succ.succ.succ.succ.succ 3 0)) (ProjectSyntax.encode id
    (ForcingDiagramOrder.product mulN.succ.succ.succ.succ.succ.succ 2 1 0))))))))))))

theorem equivariant_freeClosed {m : Nat} (A F Q mulN : Fin m) :
    (equivariant A F Q mulN).FreeClosed := by
  simp -implicitDefEqProofs [equivariant,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem equivariant_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (A F Q mulN : Fin m) :
    Project.Formula.satisfies env (equivariant A F Q mulN) ↔
      Equivariant (env.bound A) (env.bound F) (env.bound Q) (env.bound mulN) := by
  simp only [equivariant, Equivariant, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge, ForcingDiagramOrder.product_semantics (M := M)]
  rfl

def exitCompatible {m : Nat} (b E F Q mulN : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    E.succ.succ.succ.succ.succ 4 3)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    Q.succ.succ.succ.succ.succ 4 2)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    F.succ.succ.succ.succ.succ b.succ.succ.succ.succ.succ 1)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge F.succ.succ.succ.succ.succ 3 0)) (ProjectSyntax.encode id
    (ForcingDiagramOrder.product mulN.succ.succ.succ.succ.succ 2 1 0)))))))))))

theorem exitCompatible_freeClosed {m : Nat} (b E F Q mulN : Fin m) :
    (exitCompatible b E F Q mulN).FreeClosed := by
  simp -implicitDefEqProofs [exitCompatible,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem exitCompatible_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (b E F Q mulN : Fin m) :
    Project.Formula.satisfies env (exitCompatible b E F Q mulN) ↔
      ExitCompatible (env.bound b) (env.bound E) (env.bound F) (env.bound Q) (env.bound mulN) := by
  simp only [exitCompatible, ExitCompatible, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff, GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge, ForcingDiagramOrder.product_semantics (M := M)]
  rfl

def liftGraph {m : Nat} (w D S N mulN F Q W L : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge L.succ.succ 1 0)) (.conj (.mem
    (.bound 1) (.bound W.succ.succ)) (ConstructionProbeHomEvaluationSyntax.eval w.succ.succ D.succ.succ
    S.succ.succ N.succ.succ mulN.succ.succ F.succ.succ Q.succ.succ 1 0)))))

theorem liftGraph_freeClosed {m : Nat} (w D S N mulN F Q W L : Fin m) :
    (liftGraph w D S N mulN F Q W L).FreeClosed := by
  simp -implicitDefEqProofs [liftGraph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeHomEvaluationSyntax.eval_freeClosed]

theorem liftGraph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S N mulN F Q W L : Fin m) :
    Project.Formula.satisfies env (liftGraph w D S N mulN F Q W L) ↔
      LiftGraph hM (env.bound w) (env.bound D) (env.bound S) (env.bound N) (env.bound mulN) (env.bound F) (env.bound Q) (env.bound W) (env.bound L) := by
  simp only [liftGraph, LiftGraph, Project.Formula.satisfies_forall_iff, GodelDefRecursion.encode_semantics
    (ModelTransfer.extensionality hM), KuratowskiZF.source_edge, Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff, Project.Formula.satisfies_mem_iff, Project.Term.eval_bound,
    ConstructionProbeHomEvaluationSyntax.eval_semantics hM]
  rfl

def basicLiftLaws {m : Nat} (zero D G mulN unit eN F L : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge L unit eN)) (.conj (preservesProducts G mulN L)
    (.forallE (.forallE (.forallE (.imp (old zero.succ.succ.succ D.succ.succ.succ 2 1) (.iff
    (ProjectSyntax.encode id (Source.SetLanguage.edge L.succ.succ.succ 1 0)) (ProjectSyntax.encode id
    (Source.SetLanguage.edge F.succ.succ.succ 2 0)))))))))

theorem basicLiftLaws_freeClosed {m : Nat} (zero D G mulN unit eN F L : Fin m) :
    (basicLiftLaws zero D G mulN unit eN F L).FreeClosed := by
  simp -implicitDefEqProofs [basicLiftLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,preservesProducts_freeClosed,old_freeClosed]

theorem basicLiftLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (zero D G mulN unit eN F L : Fin m) :
    Project.Formula.satisfies env (basicLiftLaws zero D G mulN unit eN F L) ↔
      BasicLiftLaws (env.bound zero) (env.bound D) (env.bound G) (env.bound mulN) (env.bound unit) (env.bound eN) (env.bound F) (env.bound L) := by
  simp only [basicLiftLaws,BasicLiftLaws,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    preservesProducts_semantics hM,old_semantics hM]
  rfl

def liftLaws {m : Nat} (zero D G mulN unit eN F Q K L : Fin m) : Project.Formula 1 m :=
  (.conj (basicLiftLaws zero D G mulN unit eN F L) (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge K.succ.succ.succ 2 1)) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge
    L.succ.succ.succ 1 0)) (ProjectSyntax.encode id (Source.SetLanguage.edge Q.succ.succ.succ 2 0))))))))

theorem liftLaws_freeClosed {m : Nat} (zero D G mulN unit eN F Q K L : Fin m) :
    (liftLaws zero D G mulN unit eN F Q K L).FreeClosed := by
  simp -implicitDefEqProofs [liftLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,basicLiftLaws_freeClosed]

theorem liftLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (zero D G mulN unit eN F Q K L : Fin m) :
    Project.Formula.satisfies env (liftLaws zero D G mulN unit eN F Q K L) ↔
      LiftLaws (env.bound zero) (env.bound D) (env.bound G) (env.bound mulN) (env.bound unit) (env.bound eN) (env.bound F) (env.bound Q) (env.bound K) (env.bound L) := by
  simp only [liftLaws,LiftLaws,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,basicLiftLaws_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 16
    (.imp (Project.Formula.isOmega (.bound 0)) (.imp (Project.Formula.isEmpty (.bound 3)) (.imp (.mem (.bound 3)
    (.bound 0)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 16) 4 8)) (.imp
    (ConstructionProbeAlphabet.alphabet (1 : Fin 16) 4 8 2 9 5 7) (.imp (.mem (.bound 6) (.bound 1)) (.imp
    (ConstructionProbeLetters.representatives (10 : Fin 16) 10 11) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (12 : Fin 16) 11 10)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.unit
    (10 : Fin 16) 12 13)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.associative (10 : Fin 16) 12))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (14 : Fin 16) 1 10)) (.imp (ProjectSyntax.encode
    id (Source.SetLanguage.mapsTo (15 : Fin 16) 2 10)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    (14 : Fin 16) 8 13)) (.imp (preservesProducts (4 : Fin 16) 12 14) (.imp (equivariant (5 : Fin 16) 14 15 12)
    (.imp (exitCompatible (6 : Fin 16) 7 14 15 12) (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
    (ConstructionProbeWord.wordCarrier 5 6 7 9 10 11 4) (.conj (old 8 6 13 3) (.conj
    (ConstructionProbeLetters.representatives 4 4 2) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo
    1 2 4)) (.conj (ConstructionProbeWordMonoidSyntax.multiplicationGraph 5 6 7 8 9 10 11 4 12 1) (.conj
    (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid 4 1 3)) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo 0 4 15)) (.conj (liftGraph 5 6 7 15 17 19 20 4 0) (.conj (basicLiftLaws 8 6 1 17
    3 18 19 0) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical 6 9 13)) (.imp (.neg
    (Project.Formula.extensionalEq (.bound 11) (.bound 13))) (.existsE (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo 0 8 5)) (.conj (ConstructionProbeGeneratorSyntax.generatorGraph 6 7 8 4 0)
    (liftLaws 9 7 2 18 4 19 20 21 0 1))))))))))))))))))))))))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isEmpty,
    Project.Formula.extensionalEq,ProjectSyntax.freeClosed,ConstructionProbeAlphabet.alphabet_freeClosed,
    ConstructionProbeWord.wordCarrier_freeClosed,old_freeClosed,ConstructionProbeLetters.representatives_freeClosed,
    ConstructionProbeWordMonoidSyntax.multiplicationGraph_freeClosed,ConstructionProbeGeneratorSyntax.generatorGraph_freeClosed,
    preservesProducts_freeClosed,equivariant_freeClosed,exitCompatible_freeClosed,liftGraph_freeClosed,basicLiftLaws_freeClosed,liftLaws_freeClosed]

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
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    ForcingDiagramPoset.unit_semantics (M := M),ForcingDiagramPoset.associative_semantics (M := M),
    ConstructionProbeAlphabet.alphabet_semantics hM,ConstructionProbeWord.wordCarrier_semantics hM,
    old_semantics hM,ConstructionProbeLetters.representatives_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionProbeWordMonoidSyntax.multiplicationGraph_semantics hM,ConstructionProbeGeneratorSyntax.generatorGraph_semantics hM,
    preservesProducts_semantics hM,equivariant_semantics hM,exitCompatible_semantics hM,liftGraph_semantics hM,
    basicLiftLaws_semantics hM,liftLaws_semantics hM]
  intro hw hz hzw hm hAlpha hb hJN hMul hUnitN hAssoc hF hQ hOne hPres hEq hExit
  obtain ⟨W,hW⟩ := ConstructionProbeWord.exists_word_carrier hM hw (bound 1) (bound 2) (bound 4) (bound 5) (bound 6)
  obtain ⟨unit,hUnit⟩ := exists_old hM hm.1.1 (zero := bound 3)
  obtain ⟨J,G,hJ,hG,hgraph⟩ := ConstructionProbeWordMonoid.exists_multiplication hM hw hz hzw hm hAlpha hW hb
  obtain ⟨L,hL,hLift⟩ := ConstructionProbeHomEvaluationSyntax.exists_lift_graph hM hw hJN hMul hF hQ hW
  refine ⟨W,unit,J,G,L,hW,hUnit,hJ,hG,hgraph,
    ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hb hUnit hgraph,hL,hLift,
    basic_lift_laws hM hw hz hzw hJN hMul hF hQ hAssoc hPres hEq hExit hAlpha.2.2.2.1
      hW hb hUnit hOne hgraph hLift,?_⟩
  intro hc hne
  obtain ⟨K,hK,hGen⟩ := ConstructionProbeGenerator.exists_generator_graph hM hw hz hzw hc hW hb hne hUnit
  exact ⟨K,hK,hGen,lift_laws hM hw hz hzw hJN hMul hF hQ hUnitN hAssoc hPres hEq hExit hAlpha.2.2.2.1
    hW hb hUnit hOne hgraph hK hGen hLift⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeLiftHomSyntax
