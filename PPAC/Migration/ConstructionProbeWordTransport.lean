/- Pinned ProbePresentations.Word.transport: restrict the actual Raw transport
map to the existing reduced-word carrier. Native restriction, not a new word
encoding, supplies the graph. Multiplicativity is supplied by ConstructionProbeTransportHom. -/
import PPAC.Migration.ConstructionProbeRawTransportSyntax

namespace PPAC.Migration.ConstructionProbeWordTransport
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRawTransport
open ConstructionProbeWord (WordCarrier word_raw wordCarrier wordCarrier_freeClosed wordCarrier_semantics)
open ConstructionProbeAlphabetMap (DivisionReflection ConeMap ActionMap)
open ConstructionProbeLiftHom (PreservesProducts)
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def WordGraph (w D S SN f g W H : M.Carrier .set) : Prop := ∀ q r,
  PureKuratowski.PairMember M q r H ↔
    (Project.FirstOrderSemantics.reduct M).mem q W ∧ Value w D S SN f g q r

theorem exists_transport (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN zero mul mulN A AN b fb f g W WN : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hf : Injection D N f) (hg : Injection S SN g)
    (hDiv : DivisionReflection D N mul mulN f) (hCone : ConeMap S SN A AN f g)
    (hPres : PreservesProducts mul mulN f) (hAct : ActionMap A AN f g)
    (hb : PureKuratowski.PairMember M b fb f)
    (hW : WordCarrier w D S mul A b W) (hWN : WordCarrier w N SN mulN AN fb WN) :
    ∃ H, Injection W WN H ∧ WordGraph w D S SN f g W H ∧
      ConstructorLaws w D N S SN zero f g H ∧ SimulationLaws w D N S SN zero mul mulN A AN f H := by
  obtain ⟨R,hR⟩ := ConstructionProbeRaw.exists_carrier hM hw D S
  obtain ⟨RN,hRN⟩ := ConstructionProbeRaw.exists_carrier hM hw N SN
  obtain ⟨F,hF,hGraph⟩ := ConstructionProbeRawTransportSyntax.exists_graph hM hf.1 hg.1 hR hRN
  obtain ⟨H,hRestr⟩ := ZF.exists_restriction (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) F W
  have hG : WordGraph w D S SN f g W H := fun q r =>
    (hRestr.2 q r).trans (and_congr_right (fun _ => hGraph q r))
  have hMap : MapsTo W WN H := by
    apply (ForcingSupportSize.native_mapsTo hM W WN H).mpr
    refine ⟨⟨hRestr.1,?_⟩,?_,?_⟩
    · intro q r r' hr hr'
      exact function_unique hF.1 ((hRestr.2 q r).mp hr).2 ((hRestr.2 q r').mp hr').2
    · intro q
      constructor
      · intro hq
        obtain ⟨r,hr,_⟩ := hF.1.2 q ((hR q).mpr (word_raw hW hq))
        exact ⟨r,(hRestr.2 q r).mpr ⟨hq,hr⟩⟩
      · rintro ⟨r,hr⟩
        exact ((hRestr.2 q r).mp hr).1
    · intro q hq
      obtain ⟨r,hr,_⟩ := hF.1.2 q ((hR q).mpr (word_raw hW hq))
      have hv := (hGraph q r).mp hr
      exact ⟨r,(hWN r).mpr ((reduced_transport hM hw hf.1 hg.1 hDiv hCone hb hv).mpr ((hW q).mp hq)),
        (hRestr.2 q r).mpr ⟨hq,hr⟩⟩
  refine ⟨H,⟨hMap,?_⟩,hG,?_,?_⟩
  · intro q q' r hq hq'
    exact value_injective hM hf hg ((hG q r).mp hq).2 ((hG q' r).mp hq').2
  · exact ⟨fun _ _ _ _ hfx hx hqr => transport_old hM hz hf.1 hx hfx ((hG _ _).mp hqr).2,
      fun _ _ _ _ _ _ hgs hcons ht hq => transport_cons hM hw hf.1 hg.1 hcons hgs
        ((hG _ _).mp ht).2 ((hG _ _).mp hq).2⟩
  · exact ⟨fun _ _ _ _ ha hqr =>
      ⟨headDiv_transport hM hw hz hzw hf.1 hg.1 hDiv hCone ha ((hG _ _).mp hqr).2,
        reduced_transport hM hw hf.1 hg.1 hDiv hCone ha ((hG _ _).mp hqr).2⟩,
      fun _ _ _ _ _ _ ha hqr hqr' hact => transport_oldAct hM hw hz hf.1 hg.1 hPres hAct ha
        ((hG _ _).mp hqr).2 ((hG _ _).mp hqr').2 hact⟩

def wordGraph {m : Nat} (w D S SN f g W H : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ 1 0))
    (.conj (.mem (.bound 1) (.bound W.succ.succ))
      (ConstructionProbeRawTransportSyntax.value w.succ.succ D.succ.succ S.succ.succ SN.succ.succ
        f.succ.succ g.succ.succ 1 0))))

theorem wordGraph_freeClosed {m : Nat} (w D S SN f g W H : Fin m) : (wordGraph w D S SN f g W H).FreeClosed := by
  simp -implicitDefEqProofs [wordGraph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionProbeRawTransportSyntax.value_freeClosed]

theorem wordGraph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S SN f g W H : Fin m) :
    Project.Formula.satisfies env (wordGraph w D S SN f g W H) ↔
      WordGraph (env.bound w) (env.bound D) (env.bound S) (env.bound SN)
        (env.bound f) (env.bound g) (env.bound W) (env.bound H) := by
  simp only [wordGraph,WordGraph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionProbeRawTransportSyntax.value_semantics hM]
  rfl



open ConstructionProbeAlphabetMapSyntax (factorConservation factorConservation_freeClosed factorConservation_semantics
  alphabetSimulation alphabetSimulation_freeClosed alphabetSimulation_semantics)
open ConstructionProbeLiftHomSyntax (preservesProducts preservesProducts_freeClosed preservesProducts_semantics)
open ConstructionProbeRawTransportSyntax (constructorLaws constructorLaws_freeClosed constructorLaws_semantics
  simulationLaws simulationLaws_freeClosed simulationLaws_semantics)

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 20
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 20))) (.imp (Project.Formula.isEmpty (.bound (5
    : Fin 20))) (.imp (.mem (.bound (5 : Fin 20)) (.bound (0 : Fin 20))) (.imp (ProjectSyntax.encode
    id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 20) (6 : Fin 20) (16 : Fin 20))) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (2 : Fin 20) (7 : Fin 20) (17 :
    Fin 20))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection (12 : Fin 20) (1 : Fin
    20) (2 : Fin 20))) (.imp (preservesProducts (6 : Fin 20) (7 : Fin 20) (12 : Fin 20)) (.imp
    (factorConservation (2 : Fin 20) (7 : Fin 20) (12 : Fin 20)) (.imp (alphabetSimulation (3 : Fin
    20) (4 : Fin 20) (8 : Fin 20) (9 : Fin 20) (18 : Fin 20) (19 : Fin 20) (12 : Fin 20) (13 : Fin
    20)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (12 : Fin 20) (10 : Fin 20) (11 :
    Fin 20))) (.imp (wordCarrier (0 : Fin 20) (1 : Fin 20) (3 : Fin 20) (6 : Fin 20) (8 : Fin 20)
    (10 : Fin 20) (14 : Fin 20)) (.imp (wordCarrier (0 : Fin 20) (2 : Fin 20) (4 : Fin 20) (7 : Fin
    20) (9 : Fin 20) (11 : Fin 20) (15 : Fin 20)) (.existsE (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.injection 0 (15 : Fin 21) (16 : Fin 21))) (.conj (wordGraph (1 : Fin 21) (2
    : Fin 21) (4 : Fin 21) (5 : Fin 21) (13 : Fin 21) (14 : Fin 21) (15 : Fin 21) 0) (.conj
    (constructorLaws (1 : Fin 21) (2 : Fin 21) (3 : Fin 21) (4 : Fin 21) (5 : Fin 21) (6 : Fin 21)
    (13 : Fin 21) (14 : Fin 21) 0) (simulationLaws (1 : Fin 21) (2 : Fin 21) (3 : Fin 21) (4 : Fin
    21) (5 : Fin 21) (6 : Fin 21) (7 : Fin 21) (8 : Fin 21) (9 : Fin 21) (10 : Fin 21) (13 : Fin 21)
    0)))))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.isEmpty,preservesProducts_freeClosed,factorConservation_freeClosed,alphabetSimulation_freeClosed,
    wordCarrier_freeClosed,wordGraph_freeClosed,constructorLaws_freeClosed,simulationLaws_freeClosed]

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
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),preservesProducts_semantics hM,
    factorConservation_semantics hM,alphabetSimulation_semantics hM,KuratowskiZF.source_edge,
    wordCarrier_semantics hM,wordGraph_semantics hM,constructorLaws_semantics hM,simulationLaws_semantics hM]
  intro hw hz hzw hm hmN hf hPres hFactors hAlphabet hb hW hWN
  exact exists_transport hM hw hz hzw hf hAlphabet.1
    (ConstructionProbeAlphabetMap.division_reflection hm hmN hf hPres hFactors) hAlphabet.2.2.2
    hPres hAlphabet.2.1 hb hW hWN

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeWordTransport
