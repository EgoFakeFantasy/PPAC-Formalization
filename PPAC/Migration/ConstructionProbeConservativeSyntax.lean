import PPAC.Migration.ConstructionProbeConservative

namespace PPAC.Migration.ConstructionProbeConservativeSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeConservative
open ConstructionProbeCones (joinProperty joinProperty_freeClosed joinProperty_semantics coneLaws coneLaws_freeClosed coneLaws_semantics)
open ConstructionProbeAlphabetMapSyntax (factorConservation factorConservation_freeClosed factorConservation_semantics)
open ConstructionProbeOldEmbeddingSyntax (oldGraph oldGraph_freeClosed oldGraph_semantics embeddingLaws embeddingLaws_freeClosed embeddingLaws_semantics)
open ConstructionProbeWord (wordCarrier wordCarrier_freeClosed wordCarrier_semantics)
open ConstructionProbeRaw (old old_freeClosed old_semantics)
open ConstructionProbeAlphabet (alphabet alphabet_freeClosed alphabet_semantics)
open ConstructionProbeWordMonoidSyntax (multiplicationGraph multiplicationGraph_freeClosed multiplicationGraph_semantics)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}


def intersections {m : Nat} (D N mul mulN f : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ 5 2)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ 4 1)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ 3 0)) (.imp (joinProperty
  D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ 5 4 3) (joinProperty
  N.succ.succ.succ.succ.succ.succ mulN.succ.succ.succ.succ.succ.succ 2 1 0)))))))))))


theorem intersections_freeClosed {m : Nat} (D N mul mulN f : Fin m) : (intersections D N mul mulN f).FreeClosed := by
  simp -implicitDefEqProofs [intersections,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,joinProperty_freeClosed]

theorem intersections_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D N mul mulN f : Fin m) :
    Project.Formula.satisfies env (intersections D N mul mulN f) ↔
      Intersections (env.bound D) (env.bound N) (env.bound mul) (env.bound mulN) (env.bound f) := by
  simp only [intersections,Intersections,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,joinProperty_semantics hM]
  rfl


def common {m : Nat} (D N mul mulN f : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  f.succ.succ.succ.succ 3 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  f.succ.succ.succ.succ 2 0)) (.imp (.existsE (.conj (.mem (.bound 0) (.bound
  N.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (ConstructionBaseMonoid.divides
  N.succ.succ.succ.succ.succ mulN.succ.succ.succ.succ.succ 2 0)) (ProjectSyntax.encode id
  (ConstructionBaseMonoid.divides N.succ.succ.succ.succ.succ mulN.succ.succ.succ.succ.succ 1 0)))))
  (.existsE (.conj (.mem (.bound 0) (.bound D.succ.succ.succ.succ.succ)) (.conj
  (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ 4 0)) (ProjectSyntax.encode id (ConstructionBaseMonoid.divides
  D.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ 3 0))))))))))))


theorem common_freeClosed {m : Nat} (D N mul mulN f : Fin m) : (common D N mul mulN f).FreeClosed := by
  simp -implicitDefEqProofs [common,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem common_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D N mul mulN f : Fin m) :
    Project.Formula.satisfies env (common D N mul mulN f) ↔
      Common (env.bound D) (env.bound N) (env.bound mul) (env.bound mulN) (env.bound f) := by
  simp only [common,Common,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,ConstructionBaseMonoid.divides_semantics (M := M)]
  rfl

def conservative {m : Nat} (D N mul mulN f : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.injection f D N))
    (.conj (factorConservation N mulN f) (.conj (intersections D N mul mulN f) (common D N mul mulN f)))

theorem conservative_freeClosed {m : Nat} (D N mul mulN f : Fin m) : (conservative D N mul mulN f).FreeClosed := by
  simp -implicitDefEqProofs [conservative,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    factorConservation_freeClosed,intersections_freeClosed,common_freeClosed]

theorem conservative_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D N mul mulN f : Fin m) :
    Project.Formula.satisfies env (conservative D N mul mulN f) ↔
      Conservative (env.bound D) (env.bound N) (env.bound mul) (env.bound mulN) (env.bound f) := by
  simp only [conservative,Conservative,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.injection_semantics (M := M),
    factorConservation_semantics hM,intersections_semantics hM,common_semantics hM]
  rfl


def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 16
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 16))) (.imp (Project.Formula.isEmpty (.bound (3
    : Fin 16))) (.imp (.mem (.bound (3 : Fin 16)) (.bound (0 : Fin 16))) (.imp (ProjectSyntax.encode
    id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 16) (4 : Fin 16) (9 : Fin 16))) (.imp
    (alphabet (1 : Fin 16) (4 : Fin 16) (9 : Fin 16) (2 : Fin 16) (10 : Fin 16) (5 : Fin 16) (8 :
    Fin 16)) (.imp (wordCarrier (0 : Fin 16) (1 : Fin 16) (2 : Fin 16) (4 : Fin 16) (5 : Fin 16) (6
    : Fin 16) (7 : Fin 16)) (.imp (.mem (.bound (6 : Fin 16)) (.bound (1 : Fin 16))) (.imp
    (multiplicationGraph (0 : Fin 16) (1 : Fin 16) (2 : Fin 16) (3 : Fin 16) (4 : Fin 16) (5 : Fin
    16) (6 : Fin 16) (7 : Fin 16) (8 : Fin 16) (11 : Fin 16)) (.imp (old (3 : Fin 16) (1 : Fin 16)
    (9 : Fin 16) (12 : Fin 16)) (.imp (coneLaws (0 : Fin 16) (1 : Fin 16) (4 : Fin 16) (9 : Fin 16)
    (3 : Fin 16) (13 : Fin 16) (14 : Fin 16) (2 : Fin 16) (15 : Fin 16) (5 : Fin 16)) (.existsE
    (.conj (oldGraph (4 : Fin 17) (2 : Fin 17) 0) (.conj (embeddingLaws (1 : Fin 17) (2 : Fin 17) (3
    : Fin 17) (4 : Fin 17) (5 : Fin 17) (6 : Fin 17) (8 : Fin 17) (12 : Fin 17) (10 : Fin 17) (13 :
    Fin 17) 0) (conservative (2 : Fin 17) (8 : Fin 17) (5 : Fin 17) (12 : Fin 17) 0))))))))))))))

  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.isEmpty,alphabet_freeClosed,wordCarrier_freeClosed,multiplicationGraph_freeClosed,old_freeClosed,
    coneLaws_freeClosed,oldGraph_freeClosed,embeddingLaws_freeClosed,conservative_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    alphabet_semantics hM,wordCarrier_semantics hM,multiplicationGraph_semantics hM,old_semantics hM,coneLaws_semantics hM,
    oldGraph_semantics hM,embeddingLaws_semantics hM,conservative_semantics hM]
  exact fun hw hz hzw hm hAlpha hW hb hG hUnit hCone => exists_conservative_old hM hw hz hzw hm hAlpha hW hb hG hUnit hCone

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeConservativeSyntax
