/- Pinned CellTowers.Probe.exists_preimage and Merger.exists_preimage.
Actual consumer: CellCuts.CellTower.restrict_selected.
Reuse native range/inverse constructors, the accepted reflect_path and
valid_of_map proofs. Produce the actual internal node/table graphs. -/
import PPAC.Migration.ConstructionSaturationPrescriptionStage
import PPAC.Migration.ConstructionProbePushoutSyntax

namespace PPAC.Migration.ConstructionCellPreimage
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (function_input function_unique)
open ConstructionProbeConservative (Conservative)
open ConstructionProbePushout (Hom)
open ConstructionProbePath (Path)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionMergerRelations (Start Prescription Valid)
open ConstructionMergerPrescriptionMap (Graph Mapped)
open ConstructionRequestCarrier (WellFormed)
open ForcingDiagramPoset (LeftCancelMonoid)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The same native range/inverse construction already used by the private
ConstructionDiagramCoverage.range_inverse; no choice of preimages is needed. -/
theorem range_inverse (hM : FirstOrder.Theory.Models M nativeZF)
    {D N f : M.Carrier .set} (hf : Injection D N f) :
    ∃ R inv, (∀ y, (Project.FirstOrderSemantics.reduct M).mem y R ↔
      ∃ x, PureKuratowski.PairMember M x y f) ∧ MapsTo R D inv ∧
      ∀ y x, PureKuratowski.PairMember M y x inv ↔ PureKuratowski.PairMember M x y f := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  have hn := (ForcingSupportSize.native_injection hM D N f).mp hf
  obtain ⟨R,hR⟩ := ZF.exists_range_of_setFunction hZF pair hn.1.1 hn.1.2.1
  have hb : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo pair f D R := by
    refine ⟨⟨⟨hn.1.1,hn.1.2.1,?_⟩,hn.2⟩,?_⟩
    · intro x hx
      obtain ⟨y,_,hxy⟩ := hn.1.2.2 x hx
      exact ⟨y,(hR y).mpr ⟨x,hxy⟩,hxy⟩
    · intro y hy
      obtain ⟨x,hxy⟩ := (hR y).mp hy
      exact ⟨x,hn.1.input_mem_of_pairMember hxy,hxy⟩
  obtain ⟨inv,hi,he⟩ := ZF.exists_inverseBijectionWithPairs hZF pair hb
  exact ⟨R,inv,hR,(ForcingSupportSize.native_mapsTo hM R D inv).mpr hi.1.1,he⟩

/-- Exactly the three displayed parameters and every internal path node. -/
def ProbeCovered (f a b c node : M.Carrier .set) : Prop :=
  (∃ x, PureKuratowski.PairMember M x a f) ∧
  (∃ x, PureKuratowski.PairMember M x b f) ∧
  (∃ x, PureKuratowski.PairMember M x c f) ∧
  ∀ i y, PureKuratowski.PairMember M i y node → ∃ x, PureKuratowski.PairMember M x y f

/-- Produce the whole original probe, including its actual path graph and
both nonunit parameters; the original countable path is not truncated. -/
theorem probe_preimage (hM : FirstOrder.Theory.Models M nativeZF)
    {w D N mul mulN e eN zero a b c node f : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hf : Conservative D N mul mulN f) (hHom : Hom D N mul mulN e eN f)
    (hPath : Path w N mulN eN zero a node)
    (hb : b ≠ eN) (hc : c ≠ eN) (hCovered : ProbeCovered f a b c node) :
    ∃ a0 b0 c0 node0, PureKuratowski.PairMember M a0 a f ∧
      PureKuratowski.PairMember M b0 b f ∧ PureKuratowski.PairMember M c0 c f ∧
      NodeMap node0 f node ∧ Path w D mul e zero a0 node0 ∧
      (Project.FirstOrderSemantics.reduct M).mem b0 D ∧ b0 ≠ e ∧
      (Project.FirstOrderSemantics.reduct M).mem c0 D ∧ c0 ≠ e := by
  obtain ⟨a0,ha⟩ := hCovered.1
  obtain ⟨b0,hb0⟩ := hCovered.2.1
  obtain ⟨c0,hc0⟩ := hCovered.2.2.1
  obtain ⟨R,inv,hR,hInv,hInvEdges⟩ := range_inverse hM hf.1
  have hNodeR : MapsTo w R node :=
    ⟨hPath.1.1,fun i y hiy => (hR y).mpr (hCovered.2.2.2 i y hiy)⟩
  obtain ⟨node0,hNode0,hPull⟩ := ConstructionProbeMappedPath.exists_node_map hM hNodeR hInv
  have hBack : NodeMap node0 f node := by
    intro i y
    constructor
    · intro hiy
      obtain ⟨x,hyx,_⟩ := hInv.1.2 y (hNodeR.2 i y hiy)
      exact ⟨x,(hPull i x).mpr ⟨y,hiy,hyx⟩,(hInvEdges y x).mp hyx⟩
    · rintro ⟨x,hix,hxy⟩
      obtain ⟨y',hiy',hy'x⟩ := (hPull i x).mp hix
      exact (function_unique hHom.1.1 ((hInvEdges y' x).mp hy'x) hxy) ▸ hiy'
  refine ⟨a0,b0,c0,node0,ha,hb0,hc0,hBack,
    ConstructionSaturationProbeStage.reflect_path hm hmN hf hHom.2.2 hHom.2.1 ha hNode0 hBack hPath,
    function_input hHom.1.1 hb0,?_,function_input hHom.1.1 hc0,?_⟩
  · intro he
    exact hb (function_unique hHom.1.1 (he ▸ hb0) hHom.2.1)
  · intro he
    exact hc (function_unique hHom.1.1 (he ▸ hc0) hHom.2.1)

/-- Every displayed start coordinate has an actual preimage. Absent starts,
diagonals and the empty index set keep their original representation. -/
def MergerCovered (P f : M.Carrier .set) : Prop := ∀ i j a b,
  Start P i j a b → (∃ x, PureKuratowski.PairMember M x a f) ∧
    (∃ y, PureKuratowski.PairMember M y b f)

/-- Produce the literal preimage table, reflect its existing Valid property,
and prove that mapping it forward recovers the entire original set graph. -/
theorem merger_preimage (hM : FirstOrder.Theory.Models M nativeZF)
    {n D N mul mulN e eN P f : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hmN : LeftCancelMonoid N mulN eN)
    (hf : Conservative D N mul mulN f) (hHom : Hom D N mul mulN e eN f)
    (hWell : WellFormed n N P) (hP : Prescription n N P) (hValid : Valid n N mulN P)
    (hCovered : MergerCovered P f) :
    ∃ P0, WellFormed n D P0 ∧ Prescription n D P0 ∧ Valid n D mul P0 ∧ Graph P0 f P := by
  obtain ⟨R,inv,hR,hInv,hInvEdges⟩ := range_inverse hM hf.1
  have hPR : Prescription n R P := by
    refine ⟨?_,hP.2⟩
    intro i j a b hStart
    have hi := hP.1 i j a b hStart
    have hc := hCovered i j a b hStart
    exact ⟨hi.1,hi.2.1,(hR a).mpr hc.1,(hR b).mpr hc.2⟩
  obtain ⟨P0,hPull⟩ := ConstructionMergerPrescriptionMap.exists_graph hM hPR hInv
  have hMapped := ConstructionMergerPrescriptionMap.mapped hM hPull
  have hP0 := ConstructionMergerPrescriptionMap.prescription hPR hInv hMapped
  have hBack : Mapped P0 f P := by
    intro i j a b
    constructor
    · intro hStart
      obtain ⟨ha,hb⟩ := hCovered i j a b hStart
      obtain ⟨a0,haa0,_⟩ := hInv.1.2 a ((hR a).mpr ha)
      obtain ⟨b0,hbb0,_⟩ := hInv.1.2 b ((hR b).mpr hb)
      exact ⟨a0,b0,(hMapped i j a0 b0).mpr ⟨a,b,hStart,haa0,hbb0⟩,
        (hInvEdges a a0).mp haa0,(hInvEdges b b0).mp hbb0⟩
    · rintro ⟨a0,b0,hStart,ha0a,hb0b⟩
      obtain ⟨a',b',hOld,ha'a0,hb'b0⟩ := (hMapped i j a0 b0).mp hStart
      have ea := function_unique hHom.1.1 ((hInvEdges a' a0).mp ha'a0) ha0a
      have eb := function_unique hHom.1.1 ((hInvEdges b' b0).mp hb'b0) hb0b
      exact ea ▸ eb ▸ hOld
  exact ⟨P0,ConstructionRequestCarrier.wellFormed_of_graph hPull hP0,hP0,
    ConstructionMergerPrescriptionMap.valid_of_map hm hmN hP0 hf hHom.2.2 hBack hValid,
    ConstructionSaturationPrescriptionStage.graph_of_mapped hM hWell hBack⟩

def inRange {m : Nat} (f y : Fin m) : Project.Formula 1 m :=
  .existsE (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ 0 y.succ))

theorem inRange_freeClosed {m : Nat} (f y : Fin m) : (inRange f y).FreeClosed := by
  simp -implicitDefEqProofs [inRange,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem inRange_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (f y : Fin m) :
    Project.Formula.satisfies env (inRange f y) ↔ ∃ x, PureKuratowski.PairMember M x (env.bound y) (env.bound f) := by
  simp only [inRange,Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def probeCovered {m : Nat} (f a b c node : Fin m) : Project.Formula 1 m :=
    (.conj (inRange f a) (.conj (inRange f b) (.conj (inRange f c) (.forallE (.forallE (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.edge node.succ.succ 1 0)) (inRange f.succ.succ 0)))))))

theorem probeCovered_freeClosed {m : Nat} (f a b c node : Fin m) : (probeCovered f a b c node).FreeClosed := by
  simp -implicitDefEqProofs [probeCovered,Definitional.Formula.FreeClosed,inRange_freeClosed,ProjectSyntax.freeClosed]

theorem probeCovered_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (f a b c node : Fin m) :
    Project.Formula.satisfies env (probeCovered f a b c node) ↔
      ProbeCovered (env.bound f) (env.bound a) (env.bound b) (env.bound c) (env.bound node) := by
  simp only [probeCovered,ProbeCovered,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,inRange_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def mergerCovered {m : Nat} (P f : Fin m) : Project.Formula 1 m :=
    (.forallE (.forallE (.forallE (.forallE (.imp (ConstructionMergerRelations.start P.succ.succ.succ.succ 3 2
    1 0) (.conj (inRange f.succ.succ.succ.succ 1) (inRange f.succ.succ.succ.succ 0)))))))

theorem mergerCovered_freeClosed {m : Nat} (P f : Fin m) : (mergerCovered P f).FreeClosed := by
  simp -implicitDefEqProofs [mergerCovered,Definitional.Formula.FreeClosed,inRange_freeClosed,ConstructionMergerRelations.start_freeClosed]

theorem mergerCovered_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (P f : Fin m) :
    Project.Formula.satisfies env (mergerCovered P f) ↔
      MergerCovered (env.bound P) (env.bound f) := by
  simp only [mergerCovered,MergerCovered,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,inRange_semantics hM,
    ConstructionMergerRelations.start_semantics hM]
  rfl

def probeSentence {m : Nat} (w D N mul mulN e eN zero a b c node f : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e)) (.imp (ProjectSyntax.encode
    id (ForcingDiagramPoset.leftCancelMonoid N mulN eN)) (.imp
    (ConstructionProbeConservativeSyntax.conservative D N mul mulN f) (.imp
    (ConstructionProbePushoutSyntax.hom D N mul mulN e eN f) (.imp (ConstructionProbePath.path w N mulN eN
    zero a node) (.imp (.neg (Project.Formula.extensionalEq (.bound b) (.bound eN))) (.imp (.neg
    (Project.Formula.extensionalEq (.bound c) (.bound eN))) (.imp (probeCovered f a b c node) (.existsE
    (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
    f.succ.succ.succ.succ 3 a.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
    f.succ.succ.succ.succ 2 b.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
    f.succ.succ.succ.succ 1 c.succ.succ.succ.succ)) (.conj (ConstructionProbeMappedPathSyntax.nodeMap 0
    f.succ.succ.succ.succ node.succ.succ.succ.succ) (.conj (ConstructionProbePath.path w.succ.succ.succ.succ
    D.succ.succ.succ.succ mul.succ.succ.succ.succ e.succ.succ.succ.succ zero.succ.succ.succ.succ 3 0) (.conj
    (.mem (.bound 2) (.bound D.succ.succ.succ.succ)) (.conj (.neg (Project.Formula.extensionalEq (.bound 2)
    (.bound e.succ.succ.succ.succ))) (.conj (.mem (.bound 1) (.bound D.succ.succ.succ.succ)) (.neg
    (Project.Formula.extensionalEq (.bound 1) (.bound e.succ.succ.succ.succ)))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [
      Definitional.Formula.FreeClosed,
      ProjectSyntax.freeClosed,
      ConstructionProbeConservativeSyntax.conservative_freeClosed,
      ConstructionProbePushoutSyntax.hom_freeClosed,
      ConstructionProbePath.path_freeClosed,
      Project.Formula.extensionalEq,
      probeCovered_freeClosed,
      ConstructionProbeMappedPathSyntax.nodeMap_freeClosed]

theorem probe_models {m : Nat} (w D N mul mulN e eN zero a b c node f : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (probeSentence w D N mul mulN e eN zero a b c node f)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (probeSentence w D N mul mulN e eN zero a b c node f)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ConstructionProbeConservativeSyntax.conservative_semantics hM,
    ConstructionProbePushoutSyntax.hom_semantics hM,
    ConstructionProbePath.path_semantics hM,
    Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    probeCovered_semantics hM,
    ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,
    KuratowskiZF.source_edge,
    Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound]
  exact probe_preimage hM

theorem probe_kernel_certificate {m : Nat} (w D N mul mulN e eN zero a b c node f : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (probeSentence w D N mul mulN e eN zero a b c node f)) :=
  ModelTransfer.derives (fun _ hM => probe_models w D N mul mulN e eN zero a b c node f hM)

def mergerSentence {m : Nat} (n D N mul mulN e eN P f : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e)) (.imp (ProjectSyntax.encode
    id (ForcingDiagramPoset.leftCancelMonoid N mulN eN)) (.imp
    (ConstructionProbeConservativeSyntax.conservative D N mul mulN f) (.imp
    (ConstructionProbePushoutSyntax.hom D N mul mulN e eN f) (.imp (ConstructionRequestCarrier.wellFormed n N
    P) (.imp (ConstructionMergerRelations.prescription n N P) (.imp (ConstructionMergerRelations.valid n N
    mulN P) (.imp (mergerCovered P f) (.existsE (.conj (ConstructionRequestCarrier.wellFormed n.succ D.succ 0)
    (.conj (ConstructionMergerRelations.prescription n.succ D.succ 0) (.conj
    (ConstructionMergerRelations.valid n.succ D.succ mul.succ 0)
    (ConstructionMergerPrescriptionMapSyntax.graph 0 f.succ P.succ)))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [
      Definitional.Formula.FreeClosed,
      ProjectSyntax.freeClosed,
      ConstructionProbeConservativeSyntax.conservative_freeClosed,
      ConstructionProbePushoutSyntax.hom_freeClosed,
      ConstructionRequestCarrier.wellFormed_freeClosed,
      ConstructionMergerRelations.prescription_freeClosed,
      ConstructionMergerRelations.valid_freeClosed,
      mergerCovered_freeClosed,
      ConstructionMergerPrescriptionMapSyntax.graph_freeClosed]

theorem merger_models {m : Nat} (n D N mul mulN e eN P f : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (mergerSentence n D N mul mulN e eN P f)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (mergerSentence n D N mul mulN e eN P f)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ConstructionProbeConservativeSyntax.conservative_semantics hM,
    ConstructionProbePushoutSyntax.hom_semantics hM,
    ConstructionRequestCarrier.wellFormed_semantics hM,
    ConstructionMergerRelations.prescription_semantics hM,
    ConstructionMergerRelations.valid_semantics hM,
    mergerCovered_semantics hM,
    ConstructionMergerPrescriptionMapSyntax.graph_semantics hM]
  exact merger_preimage hM

theorem merger_kernel_certificate {m : Nat} (n D N mul mulN e eN P f : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (mergerSentence n D N mul mulN e eN P f)) :=
  ModelTransfer.derives (fun _ hM => merger_models n D N mul mulN e eN P f hM)

end PPAC.Migration.ConstructionCellPreimage
