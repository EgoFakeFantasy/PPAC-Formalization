/- Pure membership version of the pinned Word.hom_ext theorem. -/
import PPAC.Migration.ConstructionProbeHomExt

namespace PPAC.Migration.ConstructionProbeHomExtSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeHomExt ConstructionProbeLiftHomSyntax
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def oldAgreement {m : Nat} (zero D F H : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.imp (old zero.succ.succ D.succ.succ 1 0) (agreeAt 0 F.succ.succ H.succ.succ)))

theorem oldAgreement_freeClosed {m : Nat} (zero D F H : Fin m) : (oldAgreement zero D F H).FreeClosed := by
  simp -implicitDefEqProofs [oldAgreement,Definitional.Formula.FreeClosed,old_freeClosed,agreeAt_freeClosed]

theorem oldAgreement_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (zero D F H : Fin m) :
    Project.Formula.satisfies env (oldAgreement zero D F H) ↔
      (∀ x q, Old (env.bound zero) (env.bound D) x q → AgreeAt q (env.bound F) (env.bound H)) := by
  simp only [oldAgreement,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    old_semantics hM,agreeAt_semantics hM]
  rfl

def generatorAgreement {m : Nat} (K F H : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge K.succ.succ 1 0))
    (agreeAt 0 F.succ.succ H.succ.succ)))

theorem generatorAgreement_freeClosed {m : Nat} (K F H : Fin m) : (generatorAgreement K F H).FreeClosed := by
  simp -implicitDefEqProofs [generatorAgreement,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,agreeAt_freeClosed]

theorem generatorAgreement_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (K F H : Fin m) :
    Project.Formula.satisfies env (generatorAgreement K F H) ↔
      (∀ s q, PureKuratowski.PairMember M s q (env.bound K) → AgreeAt q (env.bound F) (env.bound H)) := by
  simp only [generatorAgreement,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,agreeAt_semantics hM]
  rfl

/-- Actual source Word/multiplication/generator graphs; target multiplication is single-valued.
No target cancellation or externally standard length is assumed. -/
def homExtSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 19
    (.imp (Project.Formula.isOmega (.bound 0)) (.imp (Project.Formula.isEmpty (.bound 3)) (.imp (.mem (.bound 3)
    (.bound 0)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 19) 4 9)) (.imp
    (ConstructionProbeAlphabet.alphabet (1 : Fin 19) 4 9 2 10 5 8) (.imp (ConstructionProbeWord.wordCarrier (0 :
    Fin 19) 1 2 4 5 6 7) (.imp (.mem (.bound 6) (.bound 1)) (.imp (old (3 : Fin 19) 1 9 12) (.imp
    (ConstructionProbeWordMonoidSyntax.multiplicationGraph (0 : Fin 19) 1 2 3 4 5 6 7 8 11) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (13 : Fin 19) 2 7)) (.imp
    (ConstructionProbeGeneratorSyntax.generatorGraph (0 : Fin 19) 1 2 12 13) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (16 : Fin 19) 15 14)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo
    (17 : Fin 19) 7 14)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (18 : Fin 19) 7 14)) (.imp
    (preservesProducts (11 : Fin 19) 16 17) (.imp (preservesProducts (11 : Fin 19) 16 18) (.imp (oldAgreement (3
    : Fin 19) 1 17 18) (.imp (generatorAgreement (13 : Fin 19) 17 18) (Project.Formula.extensionalEq (.bound 17)
    (.bound 18))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isEmpty,
      Project.Formula.extensionalEq,ProjectSyntax.freeClosed,ConstructionProbeAlphabet.alphabet_freeClosed,
      ConstructionProbeWord.wordCarrier_freeClosed,old_freeClosed,
      ConstructionProbeWordMonoidSyntax.multiplicationGraph_freeClosed,
      ConstructionProbeGeneratorSyntax.generatorGraph_freeClosed,preservesProducts_freeClosed,
      oldAgreement_freeClosed,generatorAgreement_freeClosed]

theorem homExt_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence homExtSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) homExtSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeAlphabet.alphabet_semantics hM,
    ConstructionProbeWord.wordCarrier_semantics hM,old_semantics hM,
    ConstructionProbeWordMonoidSyntax.multiplicationGraph_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),ConstructionProbeGeneratorSyntax.generatorGraph_semantics hM,
    preservesProducts_semantics hM,oldAgreement_semantics hM,generatorAgreement_semantics hM]
  intro hw hz hzw hm hAlpha hW hb hUnit hG hK hGen hMul hF hH hFP hHP hOld hNew
  exact hom_ext hM hw hz hzw hm hAlpha hW hb hUnit hG hK hGen hMul hF hH hFP hHP hOld hNew

theorem homExt_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence homExtSentence) := ModelTransfer.derives (fun _ hM => homExt_models hM)

end PPAC.Migration.ConstructionProbeHomExtSyntax
