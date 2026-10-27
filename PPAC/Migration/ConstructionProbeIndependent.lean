/- Pinned MonoidRounds.ProbeData.probe_gate / independent, using the SAME
normal forms retained by ConstructionOperationSource and the actual tower.
The common-right-multiple quantifier ranges over the entire internal W. -/
import PPAC.Migration.ConstructionRoundSource
import PPAC.Migration.ConstructionProbeGates

namespace PPAC.Migration.ConstructionProbeIndependent
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw ConstructionProbeRawAction ConstructionProbeGates
open ConstructionProbeOldEmbedding
open ConstructionBaseMonoid (Divides)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Instantiate the source suffix gate at the actual zero-index generator.
The same letter also gives the complete old profile, not just freshness. -/
theorem zero_gate (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero mark a b node W G unit gen S A E projection KG P ex : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e)
    (hmark : (Project.FirstOrderSemantics.reduct M).mem mark D)
    (hPath : ConstructionProbePath.Path w D mul e zero a node)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D) (hbne : b ≠ e)
    (hSource : ConstructionOperationSource.Alpha w D mul e zero mark a node S A E projection)
    (hW : ConstructionProbeWord.WordCarrier w D S mul A b W)
    (hUnit : Old zero D e unit)
    (hG : ConstructionProbeWordMonoid.MultiplicationGraph hM w D S zero mul A b W E G)
    (hGen : ConstructionProbeGenerator.GeneratorGraph w D S unit KG)
    (hProbe : ConstructionProbeIndexedGenerators.ProbeGraph w projection e KG P)
    (hgen : PureKuratowski.PairMember M zero gen P) (hEx : Product mul a mark ex) :
    ∃ s, Cons w D S s unit gen ∧ Gate w D S zero mul A W G gen s ex ∧
      ∀ x, (Project.FirstOrderSemantics.reduct M).mem x D →
        (HeadDiv w D S zero mul A x gen ↔ ConstructionProbeCones.InitialProfile w D mul node x) := by
  obtain ⟨I,K,factor,T,CRep,hAlpha,hCone,hK,hFactor,hT,hTerminal,hTarget,hExit,
    hRep,hProjectionMap,hLetters,hProjection,hAction⟩ := hSource
  obtain ⟨_,s,hproj,hsg⟩ := (hProbe zero gen).mp hgen
  have hCons := (hGen s gen).mp hsg
  obtain ⟨t,ht,_⟩ := hT.1.2 zero hzw
  have hta := ConstructionProbePath.terminal_zero hm hPath.1 hPath.2.2.1
    ((hTerminal zero t).mp ht).2
  subst t
  have hsa : PureKuratowski.PairMember M s a K :=
    (hTarget.1 zero e a s a hproj ht).mpr ((hm.1.2 a hPath.2.1 a).1.mpr rfl)
  have hexit := (hExit s ex).mpr ⟨a,hsa,hEx⟩
  have hexD := ConstructionProbeTransitions.product_closed hm hPath.2.1 hmark hEx
  have hUnitW := old_word hM hz hzw hW hUnit
  have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hb hUnit hG
  have hGate := gate_of_suffix_intersection hM hw hz hzw hm hAlpha hW hb hG hUnit hCons hUnitW
    (ConstructionProbeGenerator.not_headDiv_unit hz hc hb hbne hUnit) hm.1.1
    ((hm.1.2 b hb b).2.mpr rfl) hexit ((hm.1.2 ex hexD ex).2.mpr rfl)
    (fun z hzW => and_iff_right ⟨z,hzW,(hmW.1.2 z hzW z).1.mpr rfl⟩)
  refine ⟨s,hCons,hGate,fun x hx => ?_⟩
  exact (headDiv_of_head_eq_some hM hw hz ⟨unit,hCons⟩).trans
    (hCone.2.2.2.2.2 x s hx hproj)

/-- Literal ProbeData.independent on the original chosen W/G/O/gen.
No restriction of z to old elements or externally finite words is made. -/
theorem independent (hM : FirstOrder.Theory.Models M nativeZF)
    {w D mul e zero mark a b node W G unit O gen x ex ox oex z : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e)
    (hmark : (Project.FirstOrderSemantics.reduct M).mem mark D)
    (hSource : ConstructionOperationSource.Probe hM w D mul e zero mark a b node W G unit O gen)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D) (hEx : Product mul a mark ex)
    (hox : PureKuratowski.PairMember M x ox O) (hoex : PureKuratowski.PairMember M ex oex O)
    (hzW : (Project.FirstOrderSemantics.reduct M).mem z W)
    (hxex : Divides D mul x ex) (hxa : ¬ Divides D mul x a) :
    (Divides W G ox z ∧ Divides W G gen z) ↔ Divides W G oex z := by
  obtain ⟨hPath,hb,hbne,S,A,E,projection,KG,P,hAlphaSource,hW,hUnit,hG,hOld,
    hKG,hGen,hP,hProbe,hgen⟩ := hSource
  obtain ⟨s,hCons,hGate,hProfile⟩ := zero_gate hM hw hz hzw hm hc hmark hPath hb hbne
    hAlphaSource hW hUnit hG hGen hProbe hgen hEx
  obtain ⟨I,K,factor,T,CRep,hAlpha,_⟩ := hAlphaSource
  have hox' := (hOld x ox).mp hox
  have hoex' := (hOld ex oex).mp hoex
  have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hm hAlpha hW hb hUnit hG
  have hgenW := hP.2 zero gen hgen
  have hNot : ¬ HeadDiv w D S zero mul A x gen := by
    intro h
    obtain ⟨i,n,hi,hin,hxn⟩ := (hProfile x hx).mp h
    obtain ⟨t,⟨n',hin',htD,hnt⟩⟩ := hPath.2.2.2.2 i hi
    have he := ForcingConditionGraphs.function_unique hPath.1.1 hin' hin
    subst n'
    exact hxa (divides_trans hm hx hxn ⟨t,htD,hnt⟩)
  have hInt := gate_old_intersection hM hw hz hGate ⟨unit,hCons⟩ hNot hzW
  have hxz := old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hb hG hox' hzW
  have hexz := old_dvd_iff_headDiv hM hw hz hzw hm hAlpha hW hb hG hoex' hzW
  constructor
  · rintro ⟨h1,h2⟩
    exact hexz.mpr ((hInt.mp ⟨hxz.mp h1,h2⟩).2)
  · intro h
    have hexD := hoex'.1
    have hxx : Divides D mul x ex := hxex
    have hHeadEx : HeadDiv w D S zero mul A ex oex :=
      (headDiv_old_iff hz hoex').mpr ⟨e,hm.1.1,(hm.1.2 ex hexD ex).2.mpr rfl⟩
    have hoexW := old_word hM hz hzw hW hoex'
    have hgenex := ((hGate oex hoexW).mpr hHeadEx).1
    obtain ⟨v,hv,hxv⟩ := hxx
    obtain ⟨ov,hov⟩ := exists_old hM (zero := zero) hv
    have hoxex : Divides W G ox oex := ⟨ov,old_word hM hz hzw hW hov,
      old_mul hM hw hz hzw hm hAlpha hW hb hG hox' hov hoex' hxv⟩
    exact ⟨divides_trans hmW (old_word hM hz hzw hW hox') hoxex h,
      divides_trans hmW hgenW hgenex h⟩


/-- The complete cone equation, for all internal x and z. -/
def Independent (D mul a ex W G O gen : M.Carrier .set) : Prop :=
  ∀ x ox oex z, (Project.FirstOrderSemantics.reduct M).mem x D →
    PureKuratowski.PairMember M x ox O → PureKuratowski.PairMember M ex oex O →
    (Project.FirstOrderSemantics.reduct M).mem z W →
    Divides D mul x ex → ¬ Divides D mul x a →
    ((Divides W G ox z ∧ Divides W G gen z) ↔ Divides W G oex z)

def independentCone {m : Nat} (D mul a ex W G O gen : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (3 : Fin (m+4))) (.bound D.succ.succ.succ.succ))
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge O.succ.succ.succ.succ (3 : Fin (m+4)) (2 : Fin
  (m+4)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge O.succ.succ.succ.succ
  ex.succ.succ.succ.succ (1 : Fin (m+4)))) (.imp (.mem (.bound (0 : Fin (m+4))) (.bound
  W.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (ConstructionBaseMonoid.divides
  D.succ.succ.succ.succ mul.succ.succ.succ.succ (3 : Fin (m+4)) ex.succ.succ.succ.succ)) (.imp (.neg
  (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ.succ.succ mul.succ.succ.succ.succ (3
  : Fin (m+4)) a.succ.succ.succ.succ))) (.iff (.conj (ProjectSyntax.encode id
  (ConstructionBaseMonoid.divides W.succ.succ.succ.succ G.succ.succ.succ.succ (2 : Fin (m+4)) (0 : Fin
  (m+4)))) (ProjectSyntax.encode id (ConstructionBaseMonoid.divides W.succ.succ.succ.succ
  G.succ.succ.succ.succ gen.succ.succ.succ.succ (0 : Fin (m+4))))) (ProjectSyntax.encode id
  (ConstructionBaseMonoid.divides W.succ.succ.succ.succ G.succ.succ.succ.succ (1 : Fin (m+4)) (0 : Fin
  (m+4)))))))))))))))

theorem independentCone_freeClosed {m : Nat} (D mul a ex W G O gen : Fin m) :
    (independentCone D mul a ex W G O gen).FreeClosed := by
  simp -implicitDefEqProofs [independentCone,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem independentCone_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul a ex W G O gen : Fin m) :
    Project.Formula.satisfies env (independentCone D mul a ex W G O gen) ↔ Independent (env.bound D) (env.bound mul) (env.bound a) (env.bound ex) (env.bound W) (env.bound G) (env.bound O) (env.bound gen) := by
  simp only [independentCone,Independent,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionBaseMonoid.divides_semantics (M := M)]
  rfl


def independentSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 15 (.imp (Project.Formula.isOmega (.bound (0 : Fin 15))) (.imp
    (Project.Formula.isEmpty (.bound (4 : Fin 15))) (.imp (.mem (.bound (4 : Fin 15)) (.bound (0 : Fin 15)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 15) (2 : Fin 15) (3 : Fin
    15))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical (1 : Fin 15) (2 : Fin 15) (3 : Fin
    15))) (.imp (.mem (.bound (5 : Fin 15)) (.bound (1 : Fin 15))) (.imp (ConstructionOperationSource.probe
    (0 : Fin 15) (1 : Fin 15) (2 : Fin 15) (3 : Fin 15) (4 : Fin 15) (5 : Fin 15) (6 : Fin 15) (7 : Fin 15)
    (8 : Fin 15) (9 : Fin 15) (10 : Fin 15) (11 : Fin 15) (12 : Fin 15) (13 : Fin 15)) (.imp
    (ProjectSyntax.encode id (ForcingDiagramOrder.product (2 : Fin 15) (6 : Fin 15) (5 : Fin 15) (14 : Fin
    15))) (independentCone (1 : Fin 15) (2 : Fin 15) (6 : Fin 15) (14 : Fin 15) (9 : Fin 15) (10 : Fin 15)
    (12 : Fin 15) (13 : Fin 15)))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isEmpty,ConstructionOperationSource.probe_freeClosed,
      independentCone_freeClosed]

theorem independent_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence independentSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) independentSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingDiagramPoset.conical_semantics (M := M),ConstructionOperationSource.probe_semantics hM,
    ForcingDiagramOrder.product_semantics (M := M),independentCone_semantics hM]
  exact fun hw hz hzw hm hc hmark hSource hEx x ox oex z hx hox hoex hzW hxex hxa =>
    independent hM hw hz hzw hm hc hmark hSource hx hEx hox hoex hzW hxex hxa

theorem independent_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence independentSentence) := ModelTransfer.derives (fun _ hM => independent_models hM)


/-- Consequence for the actual mapped request, preserving all chosen fields. -/
def Realized (N mulN markN f W G O gen a b node : M.Carrier .set) : Prop :=
  ∃ fa fb mapped, PureKuratowski.PairMember M a fa f ∧ PureKuratowski.PairMember M b fb f ∧
    ConstructionProbeMappedPath.NodeMap node f mapped ∧
    ∀ ex, Product mulN fa markN ex → Independent N mulN fa ex W G O gen

/-- Consume exactly the Provenance stored in Candidate/Extended/SuccessorAt.
The Merger branch is excluded by the existing original request code theorem. -/
theorem of_provenance (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one request N mulN eN markN f W G unit O gen a b node : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid N mulN eN) (hc : Conical N mulN eN)
    (hmark : (Project.FirstOrderSemantics.reduct M).mem markN N)
    (hne : zero ≠ one) (hCode : ConstructionRequestSchedule.ProbeCode zero a b node request)
    (hSource : ConstructionRoundSource.Provenance hM w zero one request N mulN eN markN f W G unit O gen) :
    Realized N mulN markN f W G O gen a b node := by
  rcases hSource with ⟨a',b',node',fa,fb,mapped,hCode',hfa,hfb,hMap,hProbe⟩ | ⟨n,P,PN,hCode',_⟩
  · obtain ⟨ea,eb,en⟩ := ConstructionRequestSchedule.probe_code_injective hCode hCode'
    subst a'; subst b'; subst node'
    exact ⟨fa,fb,mapped,hfa,hfb,hMap,
      fun ex hEx x ox oex z hx hox hoex hzW hxex hxa =>
        independent hM hw hz hzw hm hc hmark hProbe hx hEx hox hoex hzW hxex hxa⟩
  · exact False.elim (ConstructionRequestSchedule.code_disjoint hne hCode hCode')

def realized {m : Nat} (N mulN markN f W G O gen a b node : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ
  a.succ.succ.succ (2 : Fin (m+3)))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  f.succ.succ.succ b.succ.succ.succ (1 : Fin (m+3)))) (.conj (ConstructionProbeMappedPathSyntax.nodeMap
  node.succ.succ.succ f.succ.succ.succ (0 : Fin (m+3))) (.forallE (.imp (ProjectSyntax.encode id
  (ForcingDiagramOrder.product mulN.succ.succ.succ.succ (2 : Fin (m+3)).succ markN.succ.succ.succ.succ (0 :
  Fin (m+4)))) (independentCone N.succ.succ.succ.succ mulN.succ.succ.succ.succ (2 : Fin (m+3)).succ (0 : Fin
  (m+4)) W.succ.succ.succ.succ G.succ.succ.succ.succ O.succ.succ.succ.succ gen.succ.succ.succ.succ)))))))))

theorem realized_freeClosed {m : Nat} (N mulN markN f W G O gen a b node : Fin m) :
    (realized N mulN markN f W G O gen a b node).FreeClosed := by
  simp -implicitDefEqProofs [realized,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,independentCone_freeClosed]

theorem realized_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (N mulN markN f W G O gen a b node : Fin m) :
    Project.Formula.satisfies env (realized N mulN markN f W G O gen a b node) ↔ Realized (env.bound N) (env.bound mulN) (env.bound markN) (env.bound f) (env.bound W) (env.bound G) (env.bound O) (env.bound gen) (env.bound a) (env.bound b) (env.bound node) := by
  simp only [realized,Realized,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingDiagramOrder.product_semantics (M := M),ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,independentCone_semantics hM]
  rfl


def realizedSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 17 (.imp (Project.Formula.isOmega (.bound (0 : Fin 17))) (.imp
    (Project.Formula.isEmpty (.bound (1 : Fin 17))) (.imp (.mem (.bound (1 : Fin 17)) (.bound (0 : Fin 17)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (4 : Fin 17) (5 : Fin 17) (6 : Fin
    17))) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical (4 : Fin 17) (5 : Fin 17) (6 : Fin
    17))) (.imp (.mem (.bound (7 : Fin 17)) (.bound (4 : Fin 17))) (.imp (.neg
    (Project.Formula.extensionalEq (.bound (1 : Fin 17)) (.bound (2 : Fin 17)))) (.imp
    (ConstructionRequestSchedule.probeCode (1 : Fin 17) (14 : Fin 17) (15 : Fin 17) (16 : Fin 17) (3 : Fin
    17)) (.imp (ConstructionRoundSource.provenance (0 : Fin 17) (1 : Fin 17) (2 : Fin 17) (3 : Fin 17) (4 :
    Fin 17) (5 : Fin 17) (6 : Fin 17) (7 : Fin 17) (8 : Fin 17) (9 : Fin 17) (10 : Fin 17) (11 : Fin 17) (12
    : Fin 17) (13 : Fin 17)) (realized (4 : Fin 17) (5 : Fin 17) (7 : Fin 17) (8 : Fin 17) (9 : Fin 17) (10
    : Fin 17) (12 : Fin 17) (13 : Fin 17) (14 : Fin 17) (15 : Fin 17) (16 : Fin 17))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isEmpty,Project.Formula.extensionalEq,
      ConstructionRequestSchedule.probeCode_freeClosed,ConstructionRoundSource.provenance_freeClosed,
      realized_freeClosed]

theorem realized_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence realizedSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) realizedSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingDiagramPoset.conical_semantics (M := M),ConstructionRequestSchedule.probeCode_semantics hM,
    ConstructionRoundSource.provenance_semantics hM,realized_semantics hM]
  exact fun hw hz hzw hm hc hmark hne hCode hSource =>
    of_provenance hM hw hz hzw hm hc hmark hne hCode hSource

theorem realized_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence realizedSentence) := ModelTransfer.derives (fun _ hM => realized_models hM)

end PPAC.Migration.ConstructionProbeIndependent
