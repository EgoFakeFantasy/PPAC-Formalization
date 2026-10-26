import PPAC.Migration.ConstructionProbeRawTransport
import PPAC.Migration.ConstructionProbeRawActionSyntax

namespace PPAC.Migration.ConstructionProbeRawTransportSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRawTransport
open ConstructionProbeRaw (Raw Carrier carrier carrier_freeClosed carrier_semantics old old_freeClosed old_semantics cons cons_freeClosed cons_semantics)
open ConstructionProbeRawActionSyntax (oldAct oldAct_freeClosed oldAct_semantics headDiv headDiv_freeClosed headDiv_semantics)
open ConstructionProbeReduced (reduced reduced_freeClosed reduced_semantics)
open ConstructionProbeMappedPathSyntax (nodeMap nodeMap_freeClosed nodeMap_semantics)
open ConstructionProbeAlphabetMapSyntax (alphabetSimulation alphabetSimulation_freeClosed alphabetSimulation_semantics factorConservation factorConservation_freeClosed factorConservation_semantics)
open ConstructionProbeLiftHomSyntax (preservesProducts preservesProducts_freeClosed preservesProducts_semantics)
open ForcingSupportSize (MapsTo Injection)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}


def value {m : Nat} (w D S SN f g q r : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (.mem (.bound 4) (.bound
  w.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 3 4
  S.succ.succ.succ.succ.succ)) (.conj (.mem (.bound 2) (.bound D.succ.succ.succ.succ.succ)) (.conj
  (ProjectSyntax.encode id (PairSyntax.ordered q.succ.succ.succ.succ.succ 3 2)) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 1 4 SN.succ.succ.succ.succ.succ)) (.conj
  (ProjectSyntax.encode id (PairSyntax.ordered r.succ.succ.succ.succ.succ 1 0)) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ.succ.succ 2 0)) (nodeMap 3
  g.succ.succ.succ.succ.succ 1)))))))))))))


theorem value_freeClosed {m : Nat} (w D S SN f g q r : Fin m) : (value w D S SN f g q r).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,nodeMap_freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S SN f g q r : Fin m) :
    Project.Formula.satisfies env (value w D S SN f g q r) ↔
      Value (env.bound w) (env.bound D) (env.bound S) (env.bound SN) (env.bound f) (env.bound g) (env.bound q) (env.bound r) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_code,
    KuratowskiZF.source_edge,ForcingSupportSize.mapsTo_semantics (M := M),nodeMap_semantics hM]
  rfl


def graph {m : Nat} (w D S SN f g H : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ 1 0))
  (value w.succ.succ D.succ.succ S.succ.succ SN.succ.succ f.succ.succ g.succ.succ 1 0))))


theorem graph_freeClosed {m : Nat} (w D S SN f g H : Fin m) : (graph w D S SN f g H).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,value_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S SN f g H : Fin m) :
    Project.Formula.satisfies env (graph w D S SN f g H) ↔
      Graph (env.bound w) (env.bound D) (env.bound S) (env.bound SN) (env.bound f) (env.bound g) (env.bound H) := by
  simp only [graph,Graph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,value_semantics hM]
  rfl

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN f g R RN : M.Carrier .set} (hf : MapsTo D N f) (hg : MapsTo S SN g)
    (hR : Carrier w D S R) (hRN : Carrier w N SN RN) :
    ∃ H, MapsTo R RN H ∧ Graph w D S SN f g H := by
  let schema : Project.BinarySchema 6 := {
    body := value 2 3 4 5 6 7 1 0
    freeClosed := value_freeClosed _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 6 :=
    { bound := Fin.cases w (Fin.cases D (Fin.cases S (Fin.cases SN (Fin.cases f (fun _ => g))))),
      free := fun _ => w }
  have he (q r) : schema.denote env q r ↔ Value w D S SN f g q r :=
    value_semantics hM ((env.push q).push r) 2 3 4 5 6 7 1 0
  obtain ⟨H,hH,hedge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := R) (target := RN) (by
      intro q hq
      obtain ⟨r,hr⟩ := value_total hM hf hg ((hR q).mp hq)
      exact ⟨r,(he q r).mpr hr⟩) (by
      intro q _ r r' hr hr'
      exact value_unique hM hf ((he q r).mp hr) ((he q r').mp hr')) (by
      intro q r _ hr
      exact (hRN r).mpr (value_raw hf ((he q r).mp hr)).2)
  refine ⟨H,(ForcingSupportSize.native_mapsTo hM R RN H).mpr hH,fun q r => (hedge q r).trans ?_⟩
  exact ⟨fun h => (he q r).mp h.2,fun h => ⟨(hR q).mpr (value_raw hf h).1,(he q r).mpr h⟩⟩


def constructorLaws {m : Nat} (w D N S SN zero f g H : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ 3 2)) (.imp (old zero.succ.succ.succ.succ
  D.succ.succ.succ.succ 3 1) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  H.succ.succ.succ.succ 1 0)) (old zero.succ.succ.succ.succ N.succ.succ.succ.succ 2 0))))))))
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge g.succ.succ.succ.succ.succ.succ 5 4)) (.imp (cons
  w.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ.succ 5
  3 1) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ.succ.succ 3 2))
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ.succ.succ 1 0))
  (cons w.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ
  SN.succ.succ.succ.succ.succ.succ 4 2 0))))))))))))


theorem constructorLaws_freeClosed {m : Nat} (w D N S SN zero f g H : Fin m) :
    (constructorLaws w D N S SN zero f g H).FreeClosed := by
  simp -implicitDefEqProofs [constructorLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    old_freeClosed,cons_freeClosed]

theorem constructorLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D N S SN zero f g H : Fin m) :
    Project.Formula.satisfies env (constructorLaws w D N S SN zero f g H) ↔
      ConstructorLaws (env.bound w) (env.bound D) (env.bound N) (env.bound S) (env.bound SN)
        (env.bound zero) (env.bound f) (env.bound g) (env.bound H) := by
  simp only [constructorLaws,ConstructorLaws,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    old_semantics hM,cons_semantics hM]
  rfl


def simulationLaws {m : Nat} (w D N S SN zero mul mulN A AN f H : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ 3 2)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge H.succ.succ.succ.succ 1 0)) (.conj (.iff (headDiv w.succ.succ.succ.succ
  N.succ.succ.succ.succ SN.succ.succ.succ.succ zero.succ.succ.succ.succ mulN.succ.succ.succ.succ
  AN.succ.succ.succ.succ 2 0) (headDiv w.succ.succ.succ.succ D.succ.succ.succ.succ
  S.succ.succ.succ.succ zero.succ.succ.succ.succ mul.succ.succ.succ.succ A.succ.succ.succ.succ 3 1))
  (.iff (reduced w.succ.succ.succ.succ N.succ.succ.succ.succ SN.succ.succ.succ.succ
  mulN.succ.succ.succ.succ AN.succ.succ.succ.succ 2 0) (reduced w.succ.succ.succ.succ
  D.succ.succ.succ.succ S.succ.succ.succ.succ mul.succ.succ.succ.succ A.succ.succ.succ.succ 3
  1))))))))) (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode
  id (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ 5 4)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge H.succ.succ.succ.succ.succ.succ 3 2)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge H.succ.succ.succ.succ.succ.succ 1 0)) (.imp (oldAct
  w.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ
  A.succ.succ.succ.succ.succ.succ 5 3 1) (oldAct w.succ.succ.succ.succ.succ.succ
  N.succ.succ.succ.succ.succ.succ SN.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ mulN.succ.succ.succ.succ.succ.succ
  AN.succ.succ.succ.succ.succ.succ 4 2 0))))))))))))


theorem simulationLaws_freeClosed {m : Nat} (w D N S SN zero mul mulN A AN f H : Fin m) :
    (simulationLaws w D N S SN zero mul mulN A AN f H).FreeClosed := by
  simp -implicitDefEqProofs [simulationLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    headDiv_freeClosed,reduced_freeClosed,oldAct_freeClosed]

theorem simulationLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D N S SN zero mul mulN A AN f H : Fin m) :
    Project.Formula.satisfies env (simulationLaws w D N S SN zero mul mulN A AN f H) ↔
      SimulationLaws (env.bound w) (env.bound D) (env.bound N) (env.bound S) (env.bound SN)
        (env.bound zero) (env.bound mul) (env.bound mulN) (env.bound A) (env.bound AN)
        (env.bound f) (env.bound H) := by
  simp only [simulationLaws,SimulationLaws,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    headDiv_semantics hM,reduced_semantics hM,oldAct_semantics hM]
  rfl


def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 10
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 10))) (.imp (Project.Formula.isEmpty (.bound (5 :
    Fin 10))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (6 : Fin 10) (1 : Fin 10) (2 :
    Fin 10))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (7 : Fin 10) (3 : Fin 10) (4 :
    Fin 10))) (.imp (carrier (0 : Fin 10) (1 : Fin 10) (3 : Fin 10) (8 : Fin 10)) (.imp (carrier (0 :
    Fin 10) (2 : Fin 10) (4 : Fin 10) (9 : Fin 10)) (.existsE (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo 0 (9 : Fin 11) (10 : Fin 11))) (.conj (graph (1 : Fin 11) (2 : Fin 11)
    (4 : Fin 11) (5 : Fin 11) (7 : Fin 11) (8 : Fin 11) 0) (.conj (constructorLaws (1 : Fin 11) (2 :
    Fin 11) (3 : Fin 11) (4 : Fin 11) (5 : Fin 11) (6 : Fin 11) (7 : Fin 11) (8 : Fin 11) 0) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.injection (7 : Fin 11) (2 : Fin 11) (3 : Fin 11)))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection (8 : Fin 11) (4 : Fin 11) (5 : Fin
    11))) (ProjectSyntax.encode id (Source.SetLanguage.injection 0 (9 : Fin 11) (10 : Fin
    11)))))))))))))))

  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.isEmpty,carrier_freeClosed,graph_freeClosed,constructorLaws_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),carrier_semantics hM,graph_semantics hM,constructorLaws_semantics hM]
  intro hw hz hf hg hR hRN
  obtain ⟨H,hH,hG⟩ := exists_graph hM hf hg hR hRN
  refine ⟨H,hH,hG,constructor_laws hM hw hz hf hg hG,?_⟩
  intro hfi hgi
  exact ⟨hH,fun q q' r hq hq' => value_injective hM hfi hgi ((hG q r).mp hq) ((hG q' r).mp hq')⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)


def simulationSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 17
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 17))) (.imp (Project.Formula.isEmpty (.bound (5 :
    Fin 17))) (.imp (.mem (.bound (5 : Fin 17)) (.bound (0 : Fin 17))) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 17) (6 : Fin 17) (13 : Fin 17))) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (2 : Fin 17) (7 : Fin 17) (14 : Fin
    17))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection (10 : Fin 17) (1 : Fin 17) (2 :
    Fin 17))) (.imp (preservesProducts (6 : Fin 17) (7 : Fin 17) (10 : Fin 17)) (.imp
    (factorConservation (2 : Fin 17) (7 : Fin 17) (10 : Fin 17)) (.imp (alphabetSimulation (3 : Fin
    17) (4 : Fin 17) (8 : Fin 17) (9 : Fin 17) (15 : Fin 17) (16 : Fin 17) (10 : Fin 17) (11 : Fin
    17)) (.imp (graph (0 : Fin 17) (1 : Fin 17) (3 : Fin 17) (4 : Fin 17) (10 : Fin 17) (11 : Fin 17)
    (12 : Fin 17)) (simulationLaws (0 : Fin 17) (1 : Fin 17) (2 : Fin 17) (3 : Fin 17) (4 : Fin 17) (5
    : Fin 17) (6 : Fin 17) (7 : Fin 17) (8 : Fin 17) (9 : Fin 17) (10 : Fin 17) (12 :
    Fin 17))))))))))))

  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.isEmpty,preservesProducts_freeClosed,factorConservation_freeClosed,alphabetSimulation_freeClosed,
    graph_freeClosed,simulationLaws_freeClosed]

theorem simulation_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence simulationSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) simulationSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.injection_semantics (M := M),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),preservesProducts_semantics hM,
    factorConservation_semantics hM,alphabetSimulation_semantics hM,graph_semantics hM,simulationLaws_semantics hM]
  intro hw hz hzw hm hmN hf hPres hFactors hAlphabet hG
  exact simulation_laws hM hw hz hzw hf.1 hAlphabet.1.1
    (ConstructionProbeAlphabetMap.division_reflection hm hmN hf hPres hFactors) hAlphabet.2.2.2
    hPres hAlphabet.2.1 hG

theorem simulation_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence simulationSentence) := ModelTransfer.derives (fun _ hM => simulation_models hM)

end PPAC.Migration.ConstructionProbeRawTransportSyntax
