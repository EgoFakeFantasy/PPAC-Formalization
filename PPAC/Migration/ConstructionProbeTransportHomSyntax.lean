import PPAC.Migration.ConstructionProbeTransportHom

namespace PPAC.Migration.ConstructionProbeTransportHomSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeTransportHom
open ConstructionProbeWordTransport (wordGraph wordGraph_freeClosed wordGraph_semantics)
open ConstructionProbeWord (wordCarrier wordCarrier_freeClosed wordCarrier_semantics)
open ConstructionProbeRaw (old old_freeClosed old_semantics)
open ConstructionProbeAlphabet (alphabet alphabet_freeClosed alphabet_semantics)
open ConstructionProbeAlphabetMapSyntax (alphabetSimulation alphabetSimulation_freeClosed alphabetSimulation_semantics
  factorConservation factorConservation_freeClosed factorConservation_semantics)
open ConstructionProbeLiftHomSyntax (preservesProducts preservesProducts_freeClosed preservesProducts_semantics)
open ConstructionProbeWordMonoidSyntax (multiplicationGraph multiplicationGraph_freeClosed multiplicationGraph_semantics)
open ConstructionProbeWordQuotient (quotientValue quotientValue_freeClosed quotientValue_semantics)
open ConstructionProbeLetterAction (letterAct letterAct_freeClosed letterAct_semantics)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}


def reductionLaws {m : Nat} (w D N S SN zero mul mulN A AN b fb W WN E EN f g H : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ 5 4)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge H.succ.succ.succ.succ.succ.succ 3 2)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge H.succ.succ.succ.succ.succ.succ 1 0)) (.imp (quotientValue
  w.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ
  A.succ.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ.succ 5 3 1) (quotientValue
  w.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ SN.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ mulN.succ.succ.succ.succ.succ.succ
  AN.succ.succ.succ.succ.succ.succ WN.succ.succ.succ.succ.succ.succ 4 2 0))))))))))) (.forallE
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge g.succ.succ.succ.succ.succ.succ 5 4)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge H.succ.succ.succ.succ.succ.succ 3 2)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge H.succ.succ.succ.succ.succ.succ 1 0)) (.imp (letterAct
  w.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ
  A.succ.succ.succ.succ.succ.succ b.succ.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ.succ
  E.succ.succ.succ.succ.succ.succ 5 3 1) (letterAct w.succ.succ.succ.succ.succ.succ
  N.succ.succ.succ.succ.succ.succ SN.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ mulN.succ.succ.succ.succ.succ.succ
  AN.succ.succ.succ.succ.succ.succ fb.succ.succ.succ.succ.succ.succ WN.succ.succ.succ.succ.succ.succ
  EN.succ.succ.succ.succ.succ.succ 4 2 0))))))))))))


theorem reductionLaws_freeClosed {m : Nat} (w D N S SN zero mul mulN A AN b fb W WN E EN f g H : Fin m) :
    (reductionLaws w D N S SN zero mul mulN A AN b fb W WN E EN f g H).FreeClosed := by
  simp -implicitDefEqProofs [reductionLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    quotientValue_freeClosed,letterAct_freeClosed]

theorem reductionLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D N S SN zero mul mulN A AN b fb W WN E EN f g H : Fin m) :
    Project.Formula.satisfies env (reductionLaws w D N S SN zero mul mulN A AN b fb W WN E EN f g H) ↔
      ReductionLaws (env.bound w) (env.bound D) (env.bound N) (env.bound S) (env.bound SN) (env.bound zero)
        (env.bound mul) (env.bound mulN) (env.bound A) (env.bound AN) (env.bound b) (env.bound fb)
        (env.bound W) (env.bound WN) (env.bound E) (env.bound EN) (env.bound f) (env.bound g) (env.bound H) := by
  simp only [reductionLaws,ReductionLaws,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    quotientValue_semantics hM,letterAct_semantics hM]
  rfl


def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 26
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 26))) (.imp (Project.Formula.isEmpty (.bound (5
    : Fin 26))) (.imp (.mem (.bound (5 : Fin 26)) (.bound (0 : Fin 26))) (.imp (ProjectSyntax.encode
    id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 26) (6 : Fin 26) (16 : Fin 26))) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (2 : Fin 26) (7 : Fin 26) (17 :
    Fin 26))) (.imp (alphabet (1 : Fin 26) (6 : Fin 26) (16 : Fin 26) (3 : Fin 26) (18 : Fin 26) (8
    : Fin 26) (20 : Fin 26)) (.imp (alphabet (2 : Fin 26) (7 : Fin 26) (17 : Fin 26) (4 : Fin 26)
    (19 : Fin 26) (9 : Fin 26) (21 : Fin 26)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.injection (12 : Fin 26) (1 : Fin 26) (2 : Fin 26))) (.imp (preservesProducts
    (6 : Fin 26) (7 : Fin 26) (12 : Fin 26)) (.imp (factorConservation (2 : Fin 26) (7 : Fin 26) (12
    : Fin 26)) (.imp (alphabetSimulation (3 : Fin 26) (4 : Fin 26) (8 : Fin 26) (9 : Fin 26) (20 :
    Fin 26) (21 : Fin 26) (12 : Fin 26) (13 : Fin 26)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.edge (12 : Fin 26) (10 : Fin 26) (11 : Fin 26))) (.imp (ProjectSyntax.encode
    id (Source.SetLanguage.edge (12 : Fin 26) (16 : Fin 26) (17 : Fin 26))) (.imp (wordCarrier (0 :
    Fin 26) (1 : Fin 26) (3 : Fin 26) (6 : Fin 26) (8 : Fin 26) (10 : Fin 26) (14 : Fin 26)) (.imp
    (wordCarrier (0 : Fin 26) (2 : Fin 26) (4 : Fin 26) (7 : Fin 26) (9 : Fin 26) (11 : Fin 26) (15
    : Fin 26)) (.imp (multiplicationGraph (0 : Fin 26) (1 : Fin 26) (3 : Fin 26) (5 : Fin 26) (6 :
    Fin 26) (8 : Fin 26) (10 : Fin 26) (14 : Fin 26) (20 : Fin 26) (22 : Fin 26)) (.imp
    (multiplicationGraph (0 : Fin 26) (2 : Fin 26) (4 : Fin 26) (5 : Fin 26) (7 : Fin 26) (9 : Fin
    26) (11 : Fin 26) (15 : Fin 26) (21 : Fin 26) (23 : Fin 26)) (.imp (old (5 : Fin 26) (1 : Fin
    26) (16 : Fin 26) (24 : Fin 26)) (.imp (old (5 : Fin 26) (2 : Fin 26) (17 : Fin 26) (25 : Fin
    26)) (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection 0 (15 : Fin 27) (16
    : Fin 27))) (.conj (wordGraph (1 : Fin 27) (2 : Fin 27) (4 : Fin 27) (5 : Fin 27) (13 : Fin 27)
    (14 : Fin 27) (15 : Fin 27) 0) (.conj (preservesProducts (23 : Fin 27) (24 : Fin 27) 0) (.conj
    (ProjectSyntax.encode id (Source.SetLanguage.edge 0 (25 : Fin 27) (26 : Fin 27))) (reductionLaws
    (1 : Fin 27) (2 : Fin 27) (3 : Fin 27) (4 : Fin 27) (5 : Fin 27) (6 : Fin 27) (7 : Fin 27) (8 :
    Fin 27) (9 : Fin 27) (10 : Fin 27) (11 : Fin 27) (12 : Fin 27) (15 : Fin 27) (16 : Fin 27) (21 :
    Fin 27) (22 : Fin 27) (13 : Fin 27) (14 : Fin 27) 0)))))))))))))))))))))))))

  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.isEmpty,alphabet_freeClosed,preservesProducts_freeClosed,factorConservation_freeClosed,
    alphabetSimulation_freeClosed,wordCarrier_freeClosed,multiplicationGraph_freeClosed,old_freeClosed,
    wordGraph_freeClosed,reductionLaws_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.injection_semantics (M := M),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),alphabet_semantics hM,preservesProducts_semantics hM,
    factorConservation_semantics hM,alphabetSimulation_semantics hM,KuratowskiZF.source_edge,
    wordCarrier_semantics hM,multiplicationGraph_semantics hM,old_semantics hM,wordGraph_semantics hM,reductionLaws_semantics hM]
  exact fun hw hz hzw hm hmN hAlpha hAlphaN hf hPres hFactors hAlphabet hb hOne hW hWN hG hGN hUnit hUnitN =>
    exists_transport_hom hM hw hz hzw hm hmN hAlpha hAlphaN hf hPres hFactors hAlphabet hb hOne hW hWN hG hGN hUnit hUnitN

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeTransportHomSyntax
