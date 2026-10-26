/- Pinned ProbePresentations.Word.transport_conservative:572-587.
Builds all four fields from the actual transported Word graph and the source
factor/common-below proofs. The existence endpoint constructs H via the already
proved transportHom, rather than assuming its conservative simulation. -/
import PPAC.Migration.ConstructionProbeTransportCommon

namespace PPAC.Migration.ConstructionProbeConservativeSimulation
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
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem transport_conservative (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN zero mul mulN A AN b fb f g H W WN E EN e eN I IN G GN unit unitN O ON : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hAlpha : Alphabet D mul e S I A E) (hAlphaN : Alphabet N mulN eN SN IN AN EN)
    (hf : Conservative D N mul mulN f) (hPres : PreservesProducts mul mulN f)
    (hAlphabet : AlphabetSimulation S SN A AN E EN f g) (hb : PureKuratowski.PairMember M b fb f)
    (hW : WordCarrier w D S mul A b W) (hWN : WordCarrier w N SN mulN AN fb WN)
    (hG : MultiplicationGraph hM w D S zero mul A b W E G)
    (hGN : MultiplicationGraph hM w N SN zero mulN AN fb WN EN GN)
    (hUnit : Old zero D e unit) (hUnitN : Old zero N eN unitN)
    (hH : Injection W WN H) (hGraph : WordGraph w D S SN f g W H) (hMul : PreservesProducts G GN H)
    (hO : OldGraph zero D O) (hON : OldGraph zero N ON)
    (hJ : ConditionalJoins D mul) (hA : Conservative D W mul G O) (hC : Conservative N WN mulN GN ON) :
    Conservative W WN G GN H := by
  have hFactors := ConstructionProbeTransportFactors.factor_conservation hM hw hz hzw hm hmN hAlpha hAlphaN
    hf hPres hAlphabet hb hW hWN hG hGN hUnit hUnitN hH hGraph hMul hO hON hJ hA hC
  have hDiv := ConstructionProbeTransportFactors.transport_dvd_iff hM hw hz hzw hm hmN hAlpha hAlphaN
    hf hPres hAlphabet hb hW hWN hG hGN hUnit hUnitN hH hGraph hMul hO hON hJ hA hC
  have hBelow := ConstructionProbeTransportCommon.transport_common_below hM hw hz hzw hm hmN hAlpha hAlphaN
    hf hPres hAlphabet hb hW hWN hG hGN hUnit hUnitN hH.1 hGraph hO hON hJ hA hC
  have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW (function_input hf.1.1.1 hb) hUnit hG
  have hmWN := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hmN hAlphaN hWN (hf.1.1.2 b fb hb) hUnitN hGN
  refine ⟨hH,hFactors,?_,?_⟩
  · intro x y j X Y J hX hY hJmap hJoin q hq
    constructor
    · rintro ⟨hxq,hyq⟩
      obtain ⟨k,K,hk,hK,hxk,hyk,hKq⟩ := hBelow x (word_raw hW (function_input hH.1.1 hX)) y X Y q hX hY hq hxq hyq
      exact divides_trans hmWN (hH.1.2 j J hJmap) ((hDiv j k J K hJmap hK).mpr ((hJoin k hk).mp ⟨hxk,hyk⟩)) hKq
    · intro hJq
      have hjW := function_input hH.1.1 hJmap
      have hxyj := (hJoin j hjW).mpr ⟨unit,hmW.1.1,((hmW.1.2 j hjW j).2).mpr rfl⟩
      exact ⟨divides_trans hmWN (hH.1.2 x X hX) ((hDiv x j X J hX hJmap).mpr hxyj.1) hJq,
        divides_trans hmWN (hH.1.2 y Y hY) ((hDiv y j Y J hY hJmap).mpr hxyj.2) hJq⟩
  · intro x y X Y hX hY hCommon
    obtain ⟨q,hq,hxq,hyq⟩ := hCommon
    obtain ⟨j,J,hj,_,hxj,hyj,_⟩ := hBelow x (word_raw hW (function_input hH.1.1 hX)) y X Y q hX hY hq hxq hyq
    exact ⟨j,hj,hxj,hyj⟩

theorem exists_transport_conservative (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N S SN zero mul mulN A AN b fb f g W WN E EN e eN I IN G GN unit unitN O ON : M.Carrier .set}
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
    (hJ : ConditionalJoins D mul) (hA : Conservative D W mul G O) (hC : Conservative N WN mulN GN ON) :
    ∃ H, WordGraph w D S SN f g W H ∧ PreservesProducts G GN H ∧
      PureKuratowski.PairMember M unit unitN H ∧ Conservative W WN G GN H := by
  obtain ⟨H,hH,hGraph,hMul,hOneH,_⟩ := ConstructionProbeTransportHom.exists_transport_hom hM hw hz hzw hm hmN hAlpha hAlphaN
    hf.1 hPres hf.2.1 hAlphabet hb hOne hW hWN hG hGN hUnit hUnitN
  exact ⟨H,hGraph,hMul,hOneH,transport_conservative hM hw hz hzw hm hmN hAlpha hAlphaN hf hPres hAlphabet hb
    hW hWN hG hGN hUnit hUnitN hH hGraph hMul hO hON hJ hA hC⟩

open ConstructionProbeAlphabet (alphabet alphabet_freeClosed alphabet_semantics)
open ConstructionProbeAlphabetMapSyntax (alphabetSimulation alphabetSimulation_freeClosed alphabetSimulation_semantics)
open ConstructionProbeConservativeSyntax (conservative conservative_freeClosed conservative_semantics)
open ConstructionProbeOldEmbeddingSyntax (oldGraph oldGraph_freeClosed oldGraph_semantics)
open ConstructionProbeWordMonoidSyntax (multiplicationGraph multiplicationGraph_freeClosed multiplicationGraph_semantics)
open ConstructionProbeLiftHomSyntax (preservesProducts preservesProducts_freeClosed preservesProducts_semantics)
open ConstructionProbeWord (wordCarrier wordCarrier_freeClosed wordCarrier_semantics)
open ConstructionProbeWordTransport (wordGraph wordGraph_freeClosed wordGraph_semantics)
open ConstructionProbeSharedIntersections (conditionalJoins conditionalJoins_freeClosed conditionalJoins_semantics)

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 28
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 28))) (.imp (Project.Formula.isEmpty (.bound (5 : Fin
    28))) (.imp (.mem (.bound (5 : Fin 28)) (.bound (0 : Fin 28))) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 28) (6 : Fin 28) (18 : Fin 28))) (.imp
    (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (2 : Fin 28) (7 : Fin 28) (19 : Fin 28)))
    (.imp (alphabet (1 : Fin 28) (6 : Fin 28) (18 : Fin 28) (3 : Fin 28) (20 : Fin 28) (8 : Fin 28) (16 : Fin
    28)) (.imp (alphabet (2 : Fin 28) (7 : Fin 28) (19 : Fin 28) (4 : Fin 28) (21 : Fin 28) (9 : Fin 28) (17 :
    Fin 28)) (.imp (conservative (1 : Fin 28) (2 : Fin 28) (6 : Fin 28) (7 : Fin 28) (12 : Fin 28)) (.imp
    (preservesProducts (6 : Fin 28) (7 : Fin 28) (12 : Fin 28)) (.imp (alphabetSimulation (3 : Fin 28) (4 :
    Fin 28) (8 : Fin 28) (9 : Fin 28) (16 : Fin 28) (17 : Fin 28) (12 : Fin 28) (13 : Fin 28)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (12 : Fin 28) (10 : Fin 28) (11 : Fin 28))) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge (12 : Fin 28) (18 : Fin 28) (19 : Fin 28))) (.imp
    (wordCarrier (0 : Fin 28) (1 : Fin 28) (3 : Fin 28) (6 : Fin 28) (8 : Fin 28) (10 : Fin 28) (14 : Fin 28))
    (.imp (wordCarrier (0 : Fin 28) (2 : Fin 28) (4 : Fin 28) (7 : Fin 28) (9 : Fin 28) (11 : Fin 28) (15 :
    Fin 28)) (.imp (multiplicationGraph (0 : Fin 28) (1 : Fin 28) (3 : Fin 28) (5 : Fin 28) (6 : Fin 28) (8 :
    Fin 28) (10 : Fin 28) (14 : Fin 28) (16 : Fin 28) (22 : Fin 28)) (.imp (multiplicationGraph (0 : Fin 28)
    (2 : Fin 28) (4 : Fin 28) (5 : Fin 28) (7 : Fin 28) (9 : Fin 28) (11 : Fin 28) (15 : Fin 28) (17 : Fin 28)
    (23 : Fin 28)) (.imp (old (5 : Fin 28) (1 : Fin 28) (18 : Fin 28) (24 : Fin 28)) (.imp (old (5 : Fin 28)
    (2 : Fin 28) (19 : Fin 28) (25 : Fin 28)) (.imp (oldGraph (5 : Fin 28) (1 : Fin 28) (26 : Fin 28)) (.imp
    (oldGraph (5 : Fin 28) (2 : Fin 28) (27 : Fin 28)) (.imp (conditionalJoins (1 : Fin 28) (6 : Fin 28))
    (.imp (conservative (1 : Fin 28) (14 : Fin 28) (6 : Fin 28) (22 : Fin 28) (26 : Fin 28)) (.imp
    (conservative (2 : Fin 28) (15 : Fin 28) (7 : Fin 28) (23 : Fin 28) (27 : Fin 28)) (.existsE (.conj
    (wordGraph (0 : Fin 28).succ (1 : Fin 28).succ (3 : Fin 28).succ (4 : Fin 28).succ (12 : Fin 28).succ (13
    : Fin 28).succ (14 : Fin 28).succ 0) (.conj (preservesProducts (22 : Fin 28).succ (23 : Fin 28).succ 0)
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 0 (24 : Fin 28).succ (25 : Fin 28).succ))
    (conservative (14 : Fin 28).succ (15 : Fin 28).succ (22 : Fin 28).succ (23 : Fin 28).succ
    0))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isEmpty,
      alphabet_freeClosed,alphabetSimulation_freeClosed,conservative_freeClosed,preservesProducts_freeClosed,
      wordCarrier_freeClosed,multiplicationGraph_freeClosed,old_freeClosed,wordGraph_freeClosed,oldGraph_freeClosed,
      conditionalJoins_freeClosed]

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
    oldGraph_semantics hM,conditionalJoins_semantics hM]
  exact fun hw hz hzw hm hmN hAlpha hAlphaN hf hPres hAlphabet hb hOne hW hWN hG hGN hUnit hUnitN hO hON hJ hA hC =>
    exists_transport_conservative hM hw hz hzw hm hmN hAlpha hAlphaN hf hPres hAlphabet hb hOne hW hWN hG hGN hUnit hUnitN hO hON hJ hA hC

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeConservativeSimulation
