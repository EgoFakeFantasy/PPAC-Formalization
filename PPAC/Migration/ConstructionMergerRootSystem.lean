/- Pinned CompleteRounds.snoc_cones_disjoint / root_system / cone_realization.
Reuse existing internal normal forms, word induction and snoc_cone_intersection.
RootSystem quantifies every actual extension element, not only old factors. -/
import PPAC.Migration.ConstructionRoundSource
import PPAC.Migration.ConstructionMergerWordCones

namespace PPAC.Migration.ConstructionMergerRootSystem
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw (Raw Carrier Old Cons)
open ConstructionProbeLetters (Representatives)
open ConstructionMergerCopyCones (Reaches)
open ConstructionMergerWordAction (ActionTable)
open ConstructionMergerWordProduct (Laws)
open ConstructionMergerWordCones
open ConstructionMergerWordDivisibility (snoc_dvd_snoc_iff)
open ConstructionMergerRelations (Start)
open ConstructionBaseMonoid (AdditionGraph Divides)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def disjointAt {m : Nat} (W G x y z : Fin m) : Project.Formula 1 m :=
  .neg (.conj (ProjectSyntax.encode id (ConstructionBaseMonoid.divides W G x z))
    (ProjectSyntax.encode id (ConstructionBaseMonoid.divides W G y z)))

theorem disjointAt_freeClosed {m : Nat} (W G x y z : Fin m) : (disjointAt W G x y z).FreeClosed := by
  simp -implicitDefEqProofs [disjointAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem disjointAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (W G x y z : Fin m) :
    Project.Formula.satisfies env (disjointAt W G x y z) ↔
      ¬ (Divides (env.bound W) (env.bound G) (env.bound x) (env.bound z) ∧
        Divides (env.bound W) (env.bound G) (env.bound y) (env.bound z)) := by
  simp only [disjointAt,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionBaseMonoid.divides_semantics (M := M)]
  rfl

/-- Original disjoint branch; induction is the existing definable INTERNAL raw induction. -/
theorem snoc_cones_disjoint (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A W B G T plus s t pref rs rt : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D L W) (hB : Representatives W W B) (hG : MapsTo B W G)
    (hAdd : AdditionGraph hM w plus) (hTable : ActionTable w D L zero mul A T)
    (hLaws : Laws w D L zero T G) (hS : Cons w D L s pref rs) (hT : Cons w D L t pref rt)
    (hst : ∀ d, (Project.FirstOrderSemantics.reduct M).mem d L →
      ¬ (Reaches D A s d ∧ Reaches D A t d)) :
    ∀ z, (Project.FirstOrderSemantics.reduct M).mem z W → ¬ (Divides W G rs z ∧ Divides W G rt z) := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 := {
    bound := fun i => match i with | 0 => W | 1 => G | 2 => rs | _ => rt,
    free := fun _ => w }
  let p : Project.UnarySchema 4 := {
    body := disjointAt 1 2 3 4 0
    freeClosed := disjointAt_freeClosed _ _ _ _ _ }
  have he (z) : p.denote env z ↔ ¬ (Divides W G rs z ∧ Divides W G rt z) :=
    disjointAt_semantics hM (env.push z) 1 2 3 4 0
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro m z hOld
    apply (he z).mpr
    exact fun h => snoc_not_dvd_old hM hw hz hzw hW hB hG hTable hLaws hS hOld h.1) (by
    intro d a z hCons ih
    apply (he z).mpr
    rw [snoc_dvd_snoc_iff hM hw hz hzw hW hTable hLaws hS hCons,
      snoc_dvd_snoc_iff hM hw hz hzw hW hTable hLaws hT hCons]
    by_cases hEq : pref = a
    · subst a
      have hd : (Project.FirstOrderSemantics.reduct M).mem d L := by
        obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hd,_,_,_⟩ := hCons
        exact hd
      have hsNo := snoc_not_dvd_prefix hM hw hz hzw hW hAdd hTable hLaws hS
      have htNo := snoc_not_dvd_prefix hM hw hz hzw hW hAdd hTable hLaws hT
      simpa only [hsNo,htNo,false_or,true_and] using hst d hd
    · simpa only [hEq,false_and,or_false] using (he a).mp ih)
  exact fun z hzW => (he z).mp (hAll z ((hW z).mp hzW))

/-- Exact source RootSystem for P mapped by O, on the SAME W/G/roots.
Absent starts mean disjoint cones; present starts have one common value and
its cone is exactly the intersection, for all internal extension elements. -/
def RootSystem (n P W G O roots : M.Carrier .set) : Prop :=
  ∀ i j ri rj, (Project.FirstOrderSemantics.reduct M).mem i n →
    (Project.FirstOrderSemantics.reduct M).mem j n → i ≠ j →
    PureKuratowski.PairMember M i ri roots → PureKuratowski.PairMember M j rj roots →
    ((¬ ∃ a b, Start P i j a b) → ∀ z, (Project.FirstOrderSemantics.reduct M).mem z W →
      ¬ (Divides W G ri z ∧ Divides W G rj z)) ∧
    (∀ a b, Start P i j a b → ∃ oa ob q,
      PureKuratowski.PairMember M a oa O ∧ PureKuratowski.PairMember M b ob O ∧
      Product G ri oa q ∧ Product G rj ob q ∧ ConstructionProbeCones.JoinProperty W G ri rj q)

/-- Assemble the complete source cone_realization from its already constructed data. -/
theorem root_system (hM : FirstOrder.Theory.Models M nativeZF)
    {w n D mul e zero P W G unit O roots : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e)
    (hSource : ConstructionOperationSource.Merger w n D mul e zero P W G unit O roots) :
    RootSystem n P W G O roots := by
  obtain ⟨hP,hValid,C,L,projection,K,A,I,T,B,hC,hp,hL,hProjection,hEq,hK,hA,
    hCopyTable,hFree,hCopy,hW,hI,hT,hTable,hWordFree,hB,hG,hLaws,hUnit,hOld,hRoots,hRootLaws⟩ := hSource
  obtain ⟨plus,hAdd⟩ := ConstructionBaseMonoid.exists_additionGraph hM hw
  intro i j ri rj hi hj hij hri hrj
  obtain ⟨ci,hci,hRi⟩ := (hRoots i ri).mp hri
  obtain ⟨cj,hcj,hRj⟩ := (hRoots j rj).mp hrj
  constructor
  · intro hNone
    apply snoc_cones_disjoint hM hw hz hzw hW hB hG hAdd hTable hLaws hRi hRj
    intro d hd hBoth
    obtain ⟨m,em,hmD,hem,hmd⟩ := (ConstructionMergerCopyCones.reaches_copy_iff hm hC hp hCopy hci).mp hBoth.1
    obtain ⟨k,ek,hkD,hek,hkd⟩ := (ConstructionMergerCopyCones.reaches_copy_iff hm hC hp hCopy hcj).mp hBoth.2
    have hRel := (ConstructionMergerCopies.copy_eq_iff hEq hmd hkd).mp rfl
    rcases hRel.2.2.2.2 with ⟨he,_⟩ | ⟨_,a,b,t,hStart,_⟩
    · exact hij he
    · exact hNone ⟨a,b,hStart⟩
  · intro a b hStart
    have hSpec := hP.1 i j a b hStart
    have ha := hSpec.2.2.1
    have hb := hSpec.2.2.2
    obtain ⟨ca,hcaL,hca⟩ := ConstructionProbeAction.projected hM hC hp hi ha
    obtain ⟨cb,hcbL,hcb⟩ := ConstructionProbeAction.projected hM hC hp hj hb
    obtain ⟨q,hq⟩ := ConstructionProbeRaw.exists_cons hM hw hcaL (ConstructionProbeRaw.old_raw hM hz hzw hUnit)
    obtain ⟨qj,hqj⟩ := ConstructionProbeRaw.exists_cons hM hw hcbL (ConstructionProbeRaw.old_raw hM hz hzw hUnit)
    obtain ⟨oa,hoa⟩ := ConstructionProbeRaw.exists_old hM (zero := zero) ha
    obtain ⟨ob,hob⟩ := ConstructionProbeRaw.exists_old hM (zero := zero) hb
    have hOa := (hOld a oa).mpr hoa
    have hOb := (hOld b ob).mpr hob
    have hprodI := (hRootLaws.1 i ri a oa q hri hOa).mpr ⟨ca,hca,hq⟩
    have hprodJ := (hRootLaws.1 j rj b ob qj hrj hOb).mpr ⟨cb,hcb,hqj⟩
    have hRel : ConstructionMergerRelations.CopyRel n D mul P i a j b :=
      ⟨hi,ha,hj,hb,Or.inr ⟨hij,a,b,e,hStart,hm.1.1,
        (hm.1.2 a ha a).2.mpr rfl,(hm.1.2 b hb b).2.mpr rfl⟩⟩
    have hEqQ := (hRootLaws.2.1 i j a b ri rj oa ob q qj hri hrj hOa hOb hprodI hprodJ).mpr hRel
    subst qj
    refine ⟨oa,ob,q,hOa,hOb,hprodI,hprodJ,?_⟩
    apply snoc_cone_intersection hM hw hz hzw hW hB hG hAdd hTable hLaws hRi hRj hq
    intro d hd
    have hOverlap := ConstructionMergerCopyCones.overlap_cone_intersection hM hm hP hC hp hEq hCopy hij hStart hci hcj (z := d)
    constructor
    · intro hBoth
      obtain ⟨t,atv,bt,ht,hat,hbt,_,_,hatd⟩ := hOverlap.mp hBoth
      exact (ConstructionMergerCopyCones.reaches_copy_iff hm hC hp hCopy hca).mpr ⟨t,atv,ht,hat,hatd⟩
    · intro hReach
      obtain ⟨t,atv,ht,hat,hatd⟩ := (ConstructionMergerCopyCones.reaches_copy_iff hm hC hp hCopy hca).mp hReach
      obtain ⟨bt,hbtD,hbt⟩ := (hm.2.1 b hb).1 t ht
      have hatD := ConstructionMergerRelations.product_range hm ha ht hat
      exact hOverlap.mpr ⟨t,atv,bt,ht,hat,hbt,
        ⟨atv,hatD,(hm.1.2 atv hatD atv).1.mpr rfl⟩,
        ⟨bt,hbtD,(hm.1.2 bt hbtD bt).1.mpr rfl⟩,hatd⟩


def rootSystem {m : Nat} (n P W G O roots : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (3 : Fin (m+4))) (.bound n.succ.succ.succ.succ))
  (.imp (.mem (.bound (2 : Fin (m+4))) (.bound n.succ.succ.succ.succ)) (.imp (.neg
  (Project.Formula.extensionalEq (.bound (3 : Fin (m+4))) (.bound (2 : Fin (m+4))))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge roots.succ.succ.succ.succ (3 : Fin (m+4)) (1 : Fin
  (m+4)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge roots.succ.succ.succ.succ (2 : Fin (m+4))
  (0 : Fin (m+4)))) (.conj (.imp (.neg (.existsE (.existsE (ConstructionMergerRelations.start
  P.succ.succ.succ.succ.succ.succ (3 : Fin (m+4)).succ.succ (2 : Fin (m+4)).succ.succ (1 : Fin (m+6)) (0 :
  Fin (m+6)))))) (.forallE (.imp (.mem (.bound (0 : Fin (m+5))) (.bound W.succ.succ.succ.succ.succ)) (.neg
  (.conj (ProjectSyntax.encode id (ConstructionBaseMonoid.divides W.succ.succ.succ.succ.succ
  G.succ.succ.succ.succ.succ (1 : Fin (m+4)).succ (0 : Fin (m+5)))) (ProjectSyntax.encode id
  (ConstructionBaseMonoid.divides W.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ (0 : Fin (m+4)).succ
  (0 : Fin (m+5))))))))) (.forallE (.forallE (.imp (ConstructionMergerRelations.start
  P.succ.succ.succ.succ.succ.succ (3 : Fin (m+4)).succ.succ (2 : Fin (m+4)).succ.succ (1 : Fin (m+6)) (0 :
  Fin (m+6))) (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  O.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin (m+6)).succ.succ.succ (2 : Fin (m+9)))) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge O.succ.succ.succ.succ.succ.succ.succ.succ.succ (0 : Fin
  (m+6)).succ.succ.succ (1 : Fin (m+9)))) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product
  G.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin (m+4)).succ.succ.succ.succ.succ (2 : Fin (m+9)) (0
  : Fin (m+9)))) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product
  G.succ.succ.succ.succ.succ.succ.succ.succ.succ (0 : Fin (m+4)).succ.succ.succ.succ.succ (1 : Fin (m+9)) (0
  : Fin (m+9)))) (ConstructionProbeCones.joinProperty W.succ.succ.succ.succ.succ.succ.succ.succ.succ
  G.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin (m+4)).succ.succ.succ.succ.succ (0 : Fin
  (m+4)).succ.succ.succ.succ.succ (0 : Fin (m+9)))))))))))))))))))))))

theorem rootSystem_freeClosed {m : Nat} (n P W G O roots : Fin m) :
    (rootSystem n P W G O roots).FreeClosed := by
  simp -implicitDefEqProofs [rootSystem,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq,ConstructionMergerRelations.start_freeClosed,ConstructionProbeCones.joinProperty_freeClosed]

theorem rootSystem_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n P W G O roots : Fin m) :
    Project.Formula.satisfies env (rootSystem n P W G O roots) ↔ RootSystem (env.bound n) (env.bound P) (env.bound W) (env.bound G) (env.bound O) (env.bound roots) := by
  simp only [rootSystem,RootSystem,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ConstructionMergerRelations.start_semantics hM,ForcingDiagramOrder.product_semantics (M := M),ConstructionBaseMonoid.divides_semantics (M := M),ConstructionProbeCones.joinProperty_semantics hM]
  rfl


def rootSystemSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 12 (.imp (Project.Formula.isOmega (.bound (0 : Fin 12))) (.imp
    (Project.Formula.isEmpty (.bound (5 : Fin 12))) (.imp (.mem (.bound (5 : Fin 12)) (.bound (0 : Fin 12)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (2 : Fin 12) (3 : Fin 12) (4 : Fin
    12))) (.imp (ConstructionOperationSource.merger (0 : Fin 12) (1 : Fin 12) (2 : Fin 12) (3 : Fin 12) (4 :
    Fin 12) (5 : Fin 12) (6 : Fin 12) (7 : Fin 12) (8 : Fin 12) (9 : Fin 12) (10 : Fin 12) (11 : Fin 12))
    (rootSystem (1 : Fin 12) (6 : Fin 12) (7 : Fin 12) (8 : Fin 12) (10 : Fin 12) (11 : Fin 12))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isEmpty,ConstructionOperationSource.merger_freeClosed,rootSystem_freeClosed]

theorem rootSystem_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence rootSystemSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) rootSystemSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionOperationSource.merger_semantics hM,rootSystem_semantics hM]
  exact fun hw hz hzw hm hSource => root_system hM hw hz hzw hm hSource

theorem rootSystem_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence rootSystemSentence) := ModelTransfer.derives (fun _ hM => rootSystem_models hM)

/-- The actual mapped P and roots used by the selected successor. -/
def Realized (n P f W G O roots : M.Carrier .set) : Prop :=
  ∃ PN, ConstructionMergerPrescriptionMap.Graph P f PN ∧ RootSystem n PN W G O roots

theorem of_provenance (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one request N mulN eN markN f W G unit O roots n P : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ v, ¬ (Project.FirstOrderSemantics.reduct M).mem v zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid N mulN eN) (hne : zero ≠ one)
    (hCode : ConstructionRequestSchedule.MergerCode one n P request)
    (hSource : ConstructionRoundSource.Provenance hM w zero one request N mulN eN markN f W G unit O roots) :
    Realized n P f W G O roots := by
  rcases hSource with ⟨a,b,node,fa,fb,mapped,hCode',_⟩ | ⟨n',P',PN,hCode',hGraph,hMerger⟩
  · exact False.elim (ConstructionRequestSchedule.code_disjoint hne hCode' hCode)
  · obtain ⟨en,ep⟩ := ConstructionRequestSchedule.merger_code_injective hCode hCode'
    subst n'; subst P'
    exact ⟨PN,hGraph,root_system hM hw hz hzw hm hMerger⟩

def realized {m : Nat} (n P f W G O roots : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (ConstructionMergerPrescriptionMapSyntax.graph P.succ f.succ (0 : Fin (m+1))) (rootSystem
  n.succ (0 : Fin (m+1)) W.succ G.succ O.succ roots.succ)))

theorem realized_freeClosed {m : Nat} (n P f W G O roots : Fin m) :
    (realized n P f W G O roots).FreeClosed := by
  simp -implicitDefEqProofs [realized,Definitional.Formula.FreeClosed,ConstructionMergerPrescriptionMapSyntax.graph_freeClosed,rootSystem_freeClosed]

theorem realized_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n P f W G O roots : Fin m) :
    Project.Formula.satisfies env (realized n P f W G O roots) ↔ Realized (env.bound n) (env.bound P) (env.bound f) (env.bound W) (env.bound G) (env.bound O) (env.bound roots) := by
  simp only [realized,Realized,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    
    ConstructionMergerPrescriptionMapSyntax.graph_semantics hM,rootSystem_semantics hM]
  rfl


def realizedSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 16 (.imp (Project.Formula.isOmega (.bound (0 : Fin 16))) (.imp
    (Project.Formula.isEmpty (.bound (1 : Fin 16))) (.imp (.mem (.bound (1 : Fin 16)) (.bound (0 : Fin 16)))
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (4 : Fin 16) (5 : Fin 16) (6 : Fin
    16))) (.imp (.neg (Project.Formula.extensionalEq (.bound (1 : Fin 16)) (.bound (2 : Fin 16)))) (.imp
    (ConstructionRequestSchedule.mergerCode (2 : Fin 16) (14 : Fin 16) (15 : Fin 16) (3 : Fin 16)) (.imp
    (ConstructionRoundSource.provenance (0 : Fin 16) (1 : Fin 16) (2 : Fin 16) (3 : Fin 16) (4 : Fin 16) (5
    : Fin 16) (6 : Fin 16) (7 : Fin 16) (8 : Fin 16) (9 : Fin 16) (10 : Fin 16) (11 : Fin 16) (12 : Fin 16)
    (13 : Fin 16)) (realized (14 : Fin 16) (15 : Fin 16) (8 : Fin 16) (9 : Fin 16) (10 : Fin 16) (12 : Fin
    16) (13 : Fin 16))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isEmpty,Project.Formula.extensionalEq,ConstructionRequestSchedule.mergerCode_freeClosed,ConstructionRoundSource.provenance_freeClosed,realized_freeClosed]

theorem realized_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence realizedSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) realizedSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ConstructionRequestSchedule.mergerCode_semantics hM,ConstructionRoundSource.provenance_semantics hM,realized_semantics hM]
  exact fun hw hz hzw hm hne hCode hSource => of_provenance hM hw hz hzw hm hne hCode hSource

theorem realized_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence realizedSentence) := ModelTransfer.derives (fun _ hM => realized_models hM)

end PPAC.Migration.ConstructionMergerRootSystem
