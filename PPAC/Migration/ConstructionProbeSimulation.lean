/- Pinned ProbePresentations.Path.simulation_old/simulation_probe and their
assembly with simulation_conservative. Use the actual old, generator, indexed
probe and Word graphs, not an arbitrary map satisfying the desired equations.
Consumer: Construction.ConservativeCells.Probe.simulation. -/
import PPAC.Migration.ConstructionProbeConservativeSimulation
import PPAC.Migration.ConstructionProbeIndexedGeneratorsSyntax

namespace PPAC.Migration.ConstructionProbeSimulation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeRawAction ConstructionProbeGates
open ConstructionProbeWord (WordCarrier word_raw)
open ConstructionProbeOldEmbedding (OldGraph old_dvd_iff_headDiv)
open ConstructionProbeWordMonoid (MultiplicationGraph)
open ConstructionProbeAlphabet (Alphabet)
open ConstructionProbeAlphabetMap (AlphabetSimulation FactorConservation DivisionReflection)
open ConstructionProbeConservative (Conservative)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionProbeLiftHom (PreservesProducts)
open ConstructionProbeWordTransport (WordGraph)
open ConstructionBaseMonoid (Divides)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (function_input)
open ConstructionProbeGenerator (GeneratorGraph)
open ConstructionProbeIndexedGenerators (ProbeGraph)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem simulation_old (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN zero f g H W WN O ON x fx q Q : M.Carrier .set}
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hf : MapsTo D N f) (hH : MapsTo W WN H) (hOmap : MapsTo D W O)
    (hGraph : WordGraph w D S SN f g W H) (hO : OldGraph zero D O) (hON : OldGraph zero N ON)
    (hfx : PureKuratowski.PairMember M x fx f) (hq : PureKuratowski.PairMember M x q O)
    (hQ : PureKuratowski.PairMember M fx Q ON) : PureKuratowski.PairMember M q Q H := by
  obtain ⟨R,hR,_⟩ := hH.1.2 q (hOmap.2 x q hq)
  have hOld := ConstructionProbeRawTransport.transport_old hM hz hf ((hO x q).mp hq) hfx ((hGraph q R).mp hR).2
  exact (old_unique hM hOld ((hON fx Q).mp hQ)) ▸ hR

theorem simulation_generator (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN f g H W WN unit unitN K KN s t q Q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hf : MapsTo D N f) (hg : MapsTo S SN g) (hH : MapsTo W WN H)
    (hGraph : WordGraph w D S SN f g W H) (hUnit : PureKuratowski.PairMember M unit unitN H)
    (hK : MapsTo S W K) (hGen : GeneratorGraph w D S unit K) (hGenN : GeneratorGraph w N SN unitN KN)
    (hst : PureKuratowski.PairMember M s t g) (hq : PureKuratowski.PairMember M s q K)
    (hQ : PureKuratowski.PairMember M t Q KN) : PureKuratowski.PairMember M q Q H := by
  obtain ⟨R,hR,_⟩ := hH.1.2 q (hK.2 s q hq)
  have hCons := ConstructionProbeRawTransport.transport_cons hM hw hf hg ((hGen s q).mp hq) hst
    ((hGraph unit unitN).mp hUnit).2 ((hGraph q R).mp hR).2
  exact (cons_unique hM hw hCons ((hGenN t Q).mp hQ)) ▸ hR

theorem simulation_probe (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN f g H W WN e eN unit unitN K KN projection projectionN P PN i q Q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hf : MapsTo D N f) (hg : MapsTo S SN g) (hH : MapsTo W WN H)
    (hGraph : WordGraph w D S SN f g W H) (hUnit : PureKuratowski.PairMember M unit unitN H)
    (hK : MapsTo S W K) (hGen : GeneratorGraph w D S unit K) (hGenN : GeneratorGraph w N SN unitN KN)
    (hLetters : ConstructionProbeLettersMap.Graph S projection projectionN f g)
    (hOne : PureKuratowski.PairMember M e eN f)
    (hP : ProbeGraph w projection e K P) (hPN : ProbeGraph w projectionN eN KN PN)
    (hq : PureKuratowski.PairMember M i q P) (hQ : PureKuratowski.PairMember M i Q PN) :
    PureKuratowski.PairMember M q Q H := by
  obtain ⟨_,s,his,hsq⟩ := (hP i q).mp hq
  obtain ⟨_,t,hit,htQ⟩ := (hPN i Q).mp hQ
  have hst := (hLetters s t).mpr ⟨function_input hK.1 hsq,i,e,eN,his,hOne,hit⟩
  exact simulation_generator hM hw hf hg hH hGraph hUnit hK hGen hGenN hst hsq htQ

def EndpointLaws (f H O ON P PN : M.Carrier .set) : Prop :=
  (∀ x fx q Q, PureKuratowski.PairMember M x fx f → PureKuratowski.PairMember M x q O →
    PureKuratowski.PairMember M fx Q ON → PureKuratowski.PairMember M q Q H) ∧
  (∀ i q Q, PureKuratowski.PairMember M i q P → PureKuratowski.PairMember M i Q PN →
    PureKuratowski.PairMember M q Q H)

theorem exists_simulation (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN zero mul mulN A AN b fb f g W WN E EN e eN I IN G GN unit unitN O ON projection projectionN K KN P PN : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hAlpha : Alphabet D mul e S I A E) (hAlphaN : Alphabet N mulN eN SN IN AN EN)
    (hf : Conservative D N mul mulN f) (hPres : PreservesProducts mul mulN f)
    (hAlphabet : AlphabetSimulation S SN A AN E EN f g) (hb : PureKuratowski.PairMember M b fb f) (hOne : PureKuratowski.PairMember M e eN f)
    (hW : WordCarrier w D S mul A b W) (hWN : WordCarrier w N SN mulN AN fb WN)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hGN : MultiplicationGraph hM w N SN zero mulN AN fb WN EN GN)
    (hUnit : Old zero D e unit) (hUnitN : Old zero N eN unitN)
    (hO : OldGraph zero D O) (hON : OldGraph zero N ON)
    (hJ : ConditionalJoins D mul) (hA : Conservative D W mul G O) (hC : Conservative N WN mulN GN ON)
    (hK : MapsTo S W K) (hGen : GeneratorGraph w D S unit K) (hGenN : GeneratorGraph w N SN unitN KN)
    (hLetters : ConstructionProbeLettersMap.Graph S projection projectionN f g)
    (hP : ProbeGraph w projection e K P) (hPN : ProbeGraph w projectionN eN KN PN) :
    ∃ H, WordGraph w D S SN f g W H ∧ PreservesProducts G GN H ∧
      PureKuratowski.PairMember M unit unitN H ∧ Conservative W WN G GN H ∧ EndpointLaws f H O ON P PN := by
  obtain ⟨H,hGraph,hMul,hOneH,hCons⟩ := ConstructionProbeConservativeSimulation.exists_transport_conservative hM
    hw hz hzw hm hmN hAlpha hAlphaN hf hPres hAlphabet hb hOne hW hWN hG hGN hUnit hUnitN hO hON hJ hA hC
  refine ⟨H,hGraph,hMul,hOneH,hCons,?_,?_⟩
  · intro x fx q Q hfx hq hQ
    exact simulation_old hM hz hf.1.1 hCons.1.1 hA.1.1 hGraph hO hON hfx hq hQ
  · intro i q Q hq hQ
    exact simulation_probe hM hw hf.1.1 hAlphabet.1.1 hCons.1.1 hGraph hOneH hK hGen hGenN hLetters hOne hP hPN hq hQ

def endpointLaws {m : Nat} (f H O ON P PN : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  f.succ.succ.succ.succ 3 2)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  O.succ.succ.succ.succ 3 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  ON.succ.succ.succ.succ 2 0)) (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ.succ 1
  0))))))))) (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  P.succ.succ.succ 2 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge PN.succ.succ.succ 2 0))
  (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ 1 0))))))))

theorem endpointLaws_freeClosed {m : Nat} (f H O ON P PN : Fin m) :
    (endpointLaws f H O ON P PN).FreeClosed := by
  simp -implicitDefEqProofs [endpointLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem endpointLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (f H O ON P PN : Fin m) :
    Project.Formula.satisfies env (endpointLaws f H O ON P PN) ↔
      EndpointLaws (env.bound f) (env.bound H) (env.bound O) (env.bound ON) (env.bound P) (env.bound PN) := by
  simp only [endpointLaws,EndpointLaws,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

open ConstructionProbeAlphabet (alphabet alphabet_freeClosed alphabet_semantics)
open ConstructionProbeAlphabetMapSyntax (alphabetSimulation alphabetSimulation_freeClosed alphabetSimulation_semantics)
open ConstructionProbeConservativeSyntax (conservative conservative_freeClosed conservative_semantics)
open ConstructionProbeOldEmbeddingSyntax (oldGraph oldGraph_freeClosed oldGraph_semantics)
open ConstructionProbeWordMonoidSyntax (multiplicationGraph multiplicationGraph_freeClosed multiplicationGraph_semantics)
open ConstructionProbeLiftHomSyntax (preservesProducts preservesProducts_freeClosed preservesProducts_semantics)
open ConstructionProbeWord (wordCarrier wordCarrier_freeClosed wordCarrier_semantics)
open ConstructionProbeWordTransport (wordGraph wordGraph_freeClosed wordGraph_semantics)
open ConstructionProbeSharedIntersections (conditionalJoins conditionalJoins_freeClosed conditionalJoins_semantics)

open ConstructionProbeGeneratorSyntax (generatorGraph generatorGraph_freeClosed generatorGraph_semantics)
open ConstructionProbeIndexedGeneratorsSyntax (probeGraph probeGraph_freeClosed probeGraph_semantics)
open ConstructionProbeLettersMapSyntax (graph graph_freeClosed graph_semantics)

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 34
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 34))) (.imp (Project.Formula.isEmpty (.bound (5 : Fin
    34))) (.imp (.mem (.bound (5 : Fin 34)) (.bound (0 : Fin 34))) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 34) (6 : Fin 34) (18 : Fin 34))) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (2 : Fin 34) (7 : Fin 34) (19 : Fin
    34))) (.imp (alphabet (1 : Fin 34) (6 : Fin 34) (18 : Fin 34) (3 : Fin 34) (20 : Fin 34) (8 : Fin 34)
    (16 : Fin 34)) (.imp (alphabet (2 : Fin 34) (7 : Fin 34) (19 : Fin 34) (4 : Fin 34) (21 : Fin 34) (9
    : Fin 34) (17 : Fin 34)) (.imp (conservative (1 : Fin 34) (2 : Fin 34) (6 : Fin 34) (7 : Fin 34) (12
    : Fin 34)) (.imp (preservesProducts (6 : Fin 34) (7 : Fin 34) (12 : Fin 34)) (.imp
    (alphabetSimulation (3 : Fin 34) (4 : Fin 34) (8 : Fin 34) (9 : Fin 34) (16 : Fin 34) (17 : Fin 34)
    (12 : Fin 34) (13 : Fin 34)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (12 : Fin 34)
    (10 : Fin 34) (11 : Fin 34))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (12 : Fin 34)
    (18 : Fin 34) (19 : Fin 34))) (.imp (wordCarrier (0 : Fin 34) (1 : Fin 34) (3 : Fin 34) (6 : Fin 34)
    (8 : Fin 34) (10 : Fin 34) (14 : Fin 34)) (.imp (wordCarrier (0 : Fin 34) (2 : Fin 34) (4 : Fin 34)
    (7 : Fin 34) (9 : Fin 34) (11 : Fin 34) (15 : Fin 34)) (.imp (multiplicationGraph (0 : Fin 34) (1 :
    Fin 34) (3 : Fin 34) (5 : Fin 34) (6 : Fin 34) (8 : Fin 34) (10 : Fin 34) (14 : Fin 34) (16 : Fin 34)
    (22 : Fin 34)) (.imp (multiplicationGraph (0 : Fin 34) (2 : Fin 34) (4 : Fin 34) (5 : Fin 34) (7 :
    Fin 34) (9 : Fin 34) (11 : Fin 34) (15 : Fin 34) (17 : Fin 34) (23 : Fin 34)) (.imp (old (5 : Fin 34)
    (1 : Fin 34) (18 : Fin 34) (24 : Fin 34)) (.imp (old (5 : Fin 34) (2 : Fin 34) (19 : Fin 34) (25 :
    Fin 34)) (.imp (oldGraph (5 : Fin 34) (1 : Fin 34) (26 : Fin 34)) (.imp (oldGraph (5 : Fin 34) (2 :
    Fin 34) (27 : Fin 34)) (.imp (conditionalJoins (1 : Fin 34) (6 : Fin 34)) (.imp (conservative (1 :
    Fin 34) (14 : Fin 34) (6 : Fin 34) (22 : Fin 34) (26 : Fin 34)) (.imp (conservative (2 : Fin 34) (15
    : Fin 34) (7 : Fin 34) (23 : Fin 34) (27 : Fin 34)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.mapsTo (30 : Fin 34) (3 : Fin 34) (14 : Fin 34))) (.imp (generatorGraph (0 : Fin
    34) (1 : Fin 34) (3 : Fin 34) (24 : Fin 34) (30 : Fin 34)) (.imp (generatorGraph (0 : Fin 34) (2 :
    Fin 34) (4 : Fin 34) (25 : Fin 34) (31 : Fin 34)) (.imp (graph (3 : Fin 34) (28 : Fin 34) (29 : Fin
    34) (12 : Fin 34) (13 : Fin 34)) (.imp (probeGraph (0 : Fin 34) (28 : Fin 34) (18 : Fin 34) (30 : Fin
    34) (32 : Fin 34)) (.imp (probeGraph (0 : Fin 34) (29 : Fin 34) (19 : Fin 34) (31 : Fin 34) (33 : Fin
    34)) (.existsE (.conj (wordGraph (0 : Fin 34).succ (1 : Fin 34).succ (3 : Fin 34).succ (4 : Fin
    34).succ (12 : Fin 34).succ (13 : Fin 34).succ (14 : Fin 34).succ 0) (.conj (preservesProducts (22 :
    Fin 34).succ (23 : Fin 34).succ 0) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 0 (24 :
    Fin 34).succ (25 : Fin 34).succ)) (.conj (conservative (14 : Fin 34).succ (15 : Fin 34).succ (22 :
    Fin 34).succ (23 : Fin 34).succ 0) (endpointLaws (12 : Fin 34).succ 0 (26 : Fin 34).succ (27 : Fin
    34).succ (32 : Fin 34).succ (33 : Fin 34).succ)))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isEmpty,
      alphabet_freeClosed,alphabetSimulation_freeClosed,conservative_freeClosed,preservesProducts_freeClosed,
      wordCarrier_freeClosed,multiplicationGraph_freeClosed,old_freeClosed,wordGraph_freeClosed,oldGraph_freeClosed,
      conditionalJoins_freeClosed,generatorGraph_freeClosed,graph_freeClosed,probeGraph_freeClosed,endpointLaws_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    alphabet_semantics hM,alphabetSimulation_semantics hM,conservative_semantics hM,preservesProducts_semantics hM,
    wordCarrier_semantics hM,multiplicationGraph_semantics hM,old_semantics hM,wordGraph_semantics hM,
    oldGraph_semantics hM,conditionalJoins_semantics hM,generatorGraph_semantics hM,graph_semantics hM,
    probeGraph_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),endpointLaws_semantics hM]
  exact fun hw hz hzw hm hmN hAlpha hAlphaN hf hPres hAlphabet hb hOne hW hWN hG hGN hUnit hUnitN hO hON hJ hA hC hK hGen hGenN hLetters hP hPN =>
    exists_simulation hM hw hz hzw hm hmN hAlpha hAlphaN hf hPres hAlphabet hb hOne hW hWN hG hGN hUnit hUnitN hO hON hJ hA hC hK hGen hGenN hLetters hP hPN

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeSimulation
