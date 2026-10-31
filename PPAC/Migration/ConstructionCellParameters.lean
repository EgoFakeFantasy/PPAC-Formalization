/- Pinned ConservativeCells.Probe.parameters/countable:250-252 and
Merger.parameters/countable:321-334. Consumer: actual Attachment dependency
graph construction/countability, then selected successor and global tower.
Use native graphs and existing donor countable-image/product/union bounds. -/
import PPAC.Migration.ConstructionAttachmentDependencies
import PPAC.Migration.ConstructionCellPreimage

namespace PPAC.Migration.ConstructionCellParameters
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Small)
open ForcingConditionGraphs (function_input function_unique)
open ForcingSupportedNames (Range)
open ConstructionRealCuts (Subset)
open ConstructionMergerRelations (Start Prescription)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem omega_small (hM : FirstOrder.Theory.Models M nativeZF) (w : M.Carrier .set) : Small w w := by
  obtain ⟨f,hf⟩ := ZF.exists_identityBijection (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) w
  exact (ForcingSupportSize.native_small hM w w).mpr ⟨f,hf.1⟩

theorem nat_small (hM : FirstOrder.Theory.Models M nativeZF) {w n : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) : Small n w :=
  ForcingSupportSize.small_subset hM (fun z hz => hw.transitive (ModelTransfer.project_models_iff.mp hM) n hn z hz) (omega_small hM w)

/-- Actual full range, bounded by the old carrier and by internal omega. -/
theorem range_small (hM : FirstOrder.Theory.Models M nativeZF)
    {w I D f : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hf : MapsTo I D f) (hI : Small I w) : ∃ R, Range I f R ∧ Subset R D ∧ Small R w := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  have hn := (ForcingSupportSize.native_mapsTo hM I D f).mp hf
  obtain ⟨R,hR⟩ := ZF.exists_range_of_setFunction hZF pair hn.1 hn.2.1
  have hr : Range I f R := fun z => ⟨fun hz => by
      obtain ⟨i,hiz⟩ := (hR z).mp hz
      exact ⟨i,hn.input_mem_of_pairMember hiz,hiz⟩,
    fun ⟨i,_,hiz⟩ => (hR z).mpr ⟨i,hiz⟩⟩
  have hToR : (Project.FirstOrderSemantics.reduct M).IsSetFunctionFromTo pair f I R :=
    ⟨hn.1,hn.2.1,fun i hi => by
      obtain ⟨z,_,hiz⟩ := hn.2.2 i hi
      exact ⟨z,(hr z).mpr ⟨i,hi,hiz⟩,hiz⟩⟩
  refine ⟨R,hr,?_,(ForcingSupportSize.native_small hM R w).mpr
    (ExistingOrdinalImage.ordinal_image_bound_l pair hZF (hw.isOrdinal hZF)
      ((ForcingSupportSize.native_small hM I w).mp hI) hToR (fun z hz => (hr z).mp hz))⟩
  intro z hz
  obtain ⟨i,_,hiz⟩ := (hr z).mp hz
  exact hf.2 i z hiz

def ProbeParameters (a b d node parameters : M.Carrier .set) : Prop := ∀ z,
  (Project.FirstOrderSemantics.reduct M).mem z parameters ↔
    z = a ∨ z = b ∨ z = d ∨ ∃ i, PureKuratowski.PairMember M i z node

def probeParameters {m : Nat} (a b d node parameters : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound parameters.succ))
    (.disj (Project.Formula.extensionalEq (.bound 0) (.bound a.succ))
      (.disj (Project.Formula.extensionalEq (.bound 0) (.bound b.succ))
        (.disj (Project.Formula.extensionalEq (.bound 0) (.bound d.succ))
          (.existsE (ProjectSyntax.encode id (Source.SetLanguage.edge node.succ.succ 0 1)))))))

theorem probeParameters_freeClosed {m : Nat} (a b d node parameters : Fin m) :
    (probeParameters a b d node parameters).FreeClosed := by
  simp [probeParameters,Definitional.Formula.FreeClosed,Project.Formula.extensionalEq,ProjectSyntax.freeClosed]

theorem probeParameters_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (a b d node parameters : Fin m) :
    Project.Formula.satisfies env (probeParameters a b d node parameters) ↔
      ProbeParameters (env.bound a) (env.bound b) (env.bound d) (env.bound node) (env.bound parameters) := by
  simp only [probeParameters,ProbeParameters,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_exists_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

theorem exists_probe_parameters (hM : FirstOrder.Theory.Models M nativeZF)
    {w D a b d node : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hn : MapsTo w D node)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a D)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b D)
    (hd : (Project.FirstOrderSemantics.reduct M).mem d D) :
    ∃ parameters, ProbeParameters a b d node parameters ∧ Subset parameters D ∧ Small parameters w := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hKP := ZF.modelsKP hZF
  obtain ⟨R,hR,_,hSmall⟩ := range_small hM hw hn (omega_small hM w)
  obtain ⟨R1,h1⟩ := KP.exists_insert hKP R d
  obtain ⟨R2,h2⟩ := KP.exists_insert hKP R1 b
  obtain ⟨parameters,h3⟩ := KP.exists_insert hKP R2 a
  have hParam : ProbeParameters a b d node parameters := by
    intro z
    constructor
    · intro hz
      rcases (h3 z).mp hz with hz | hz
      · rcases (h2 z).mp hz with hz | hz
        · rcases (h1 z).mp hz with hz | hz
          · obtain ⟨i,_,hiz⟩ := (hR z).mp hz
            exact Or.inr (Or.inr (Or.inr ⟨i,hiz⟩))
          · exact Or.inr (Or.inr (Or.inl hz))
        · exact Or.inr (Or.inl hz)
      · exact Or.inl hz
    · rintro (hz | hz | hz | ⟨i,hiz⟩)
      · exact (h3 z).mpr (Or.inr hz)
      · exact (h3 z).mpr (Or.inl ((h2 z).mpr (Or.inr hz)))
      · exact (h3 z).mpr (Or.inl ((h2 z).mpr (Or.inl ((h1 z).mpr (Or.inr hz)))))
      · exact (h3 z).mpr (Or.inl ((h2 z).mpr (Or.inl ((h1 z).mpr (Or.inl
          ((hR z).mpr ⟨i,function_input hn.1 hiz,hiz⟩))))))
  refine ⟨parameters,hParam,?_,(ForcingSupportSize.native_small hM parameters w).mpr
    (ZF.countable_insert_l (KuratowskiZF.interpretation hM) hZF hw
      (ZF.countable_insert_l (KuratowskiZF.interpretation hM) hZF hw
        (ZF.countable_insert_l (KuratowskiZF.interpretation hM) hZF hw
          ((ForcingSupportSize.native_small hM R w).mp hSmall) h1) h2) h3)⟩
  intro z hz
  rcases (hParam z).mp hz with rfl | rfl | rfl | ⟨i,hiz⟩
  · exact ha
  · exact hb
  · exact hd
  · exact hn.2 i z hiz

/-- Source getD(1,1) coordinate; defaults bound the range but never enter
MergerParameters unless they occur in a displayed start. -/
def Side (left : Bool) (P e i j z : M.Carrier .set) : Prop :=
  (∃ a b, Start P i j a b ∧ z = if left then a else b) ∨
    (¬ ∃ a b, Start P i j a b) ∧ z = e

def side {m : Nat} (left : Bool) (P e i j z : Fin m) : Project.Formula 1 m :=
  .disj (.existsE (.existsE (.conj (ConstructionMergerRelations.start P.succ.succ i.succ.succ j.succ.succ 1 0)
    (Project.Formula.extensionalEq (.bound z.succ.succ) (.bound (if left then 1 else 0))))))
    (.conj (.neg (.existsE (.existsE (ConstructionMergerRelations.start P.succ.succ i.succ.succ j.succ.succ 1 0))))
      (Project.Formula.extensionalEq (.bound z) (.bound e)))

theorem side_freeClosed {m : Nat} (left : Bool) (P e i j z : Fin m) : (side left P e i j z).FreeClosed := by
  simp [side,Definitional.Formula.FreeClosed,ConstructionMergerRelations.start_freeClosed,Project.Formula.extensionalEq]

theorem side_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (left : Bool) (P e i j z : Fin m) :
    Project.Formula.satisfies env (side left P e i j z) ↔
      Side left (env.bound P) (env.bound e) (env.bound i) (env.bound j) (env.bound z) := by
  cases left <;> simp only [side,Side,Bool.false_eq_true,if_false,if_true,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Term.eval_bound,ConstructionMergerRelations.start_semantics hM] <;> rfl

def Coordinate (left : Bool) (P e q z : M.Carrier .set) : Prop :=
  ∃ i j, PureKuratowski.Code M q i j ∧ Side left P e i j z

def coordinate {m : Nat} (left : Bool) (P e q z : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (PureKuratowskiProject.code (.bound q.succ.succ) (.bound 1) (.bound 0))
    (side left P.succ.succ e.succ.succ 1 0 z.succ.succ)))

theorem coordinate_freeClosed {m : Nat} (left : Bool) (P e q z : Fin m) : (coordinate left P e q z).FreeClosed := by
  simp -implicitDefEqProofs [coordinate,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,side_freeClosed]

theorem coordinate_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (left : Bool) (P e q z : Fin m) :
    Project.Formula.satisfies env (coordinate left P e q z) ↔
      Coordinate left (env.bound P) (env.bound e) (env.bound q) (env.bound z) := by
  simp only [coordinate,Coordinate,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Term.eval_bound,KuratowskiZF.code_correct hM,side_semantics hM]
  rfl

theorem coordinate_unique {n D P e q z t : M.Carrier .set} (left : Bool)
    (hP : Prescription n D P) (hz : Coordinate left P e q z) (ht : Coordinate left P e q t) : z = t := by
  obtain ⟨i,j,hq,hz⟩ := hz
  obtain ⟨i',j',hq',ht⟩ := ht
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq hq'
  rcases hz with ⟨a,b,hs,hz⟩ | ⟨hn,hz⟩
  · rcases ht with ⟨a',b',hs',ht⟩ | ⟨hn,ht⟩
    · obtain ⟨rfl,rfl⟩ := hP.2 i j a b a' b' hs hs'
      exact hz.trans ht.symm
    · exact (hn ⟨a,b,hs⟩).elim
  · rcases ht with ⟨a,b,hs,_⟩ | ⟨_,ht⟩
    · exact (hn ⟨a,b,hs⟩).elim
    · exact hz.trans ht.symm

theorem exists_coordinate_graph (hM : FirstOrder.Theory.Models M nativeZF) (left : Bool)
    {n D P e B : M.Carrier .set} (hP : Prescription n D P)
    (he : (Project.FirstOrderSemantics.reduct M).mem e D)
    (hB : (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) B n n) :
    ∃ F, MapsTo B D F ∧ ∀ q z, PureKuratowski.PairMember M q z F ↔
      (Project.FirstOrderSemantics.reduct M).mem q B ∧ Coordinate left P e q z := by
  let schema : Project.BinarySchema 2 := {
    body := coordinate left 2 3 1 0
    freeClosed := coordinate_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases P (fun _ => e), free := fun _ => D }
  have hc q z : schema.denote env q z ↔ Coordinate left P e q z :=
    coordinate_semantics hM ((env.push q).push z) left 2 3 1 0
  obtain ⟨F,hF,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := B) (target := D) (by
      intro q hq
      obtain ⟨i,_,j,_,hcode⟩ := (hB q).mp hq
      classical
      by_cases hs : ∃ a b, Start P i j a b
      · obtain ⟨a,b,hs⟩ := hs
        exact ⟨if left then a else b,(hc q _).mpr ⟨i,j,hcode,Or.inl ⟨a,b,hs,rfl⟩⟩⟩
      · exact ⟨e,(hc q e).mpr ⟨i,j,hcode,Or.inr ⟨hs,rfl⟩⟩⟩)
    (fun q _ z t hz ht => coordinate_unique left hP ((hc q z).mp hz) ((hc q t).mp ht)) (by
      intro q z _ hz
      obtain ⟨i,j,_,hz⟩ := (hc q z).mp hz
      rcases hz with ⟨a,b,hs,rfl⟩ | ⟨_,rfl⟩
      · have hAB := hP.1 i j a b hs
        cases left
        · exact hAB.2.2.2
        · exact hAB.2.2.1
      · exact he)
  exact ⟨F,(ForcingSupportSize.native_mapsTo hM B D F).mpr hF,
    fun q z => (hGraph q z).trans (and_congr_right fun _ => hc q z)⟩

def MergerMember (P z : M.Carrier .set) : Prop := ∃ i j a b,
  Start P i j a b ∧ (z = a ∨ z = b)

def mergerMember {m : Nat} (P z : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.existsE
    (.conj (ConstructionMergerRelations.start P.succ.succ.succ.succ 3 2 1 0)
      (.disj (Project.Formula.extensionalEq (.bound z.succ.succ.succ.succ) (.bound 1))
        (Project.Formula.extensionalEq (.bound z.succ.succ.succ.succ) (.bound 0)))))))

theorem mergerMember_freeClosed {m : Nat} (P z : Fin m) : (mergerMember P z).FreeClosed := by
  simp [mergerMember,Definitional.Formula.FreeClosed,ConstructionMergerRelations.start_freeClosed,Project.Formula.extensionalEq]

theorem mergerMember_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (P z : Fin m) :
    Project.Formula.satisfies env (mergerMember P z) ↔ MergerMember (env.bound P) (env.bound z) := by
  simp only [mergerMember,MergerMember,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ConstructionMergerRelations.start_semantics hM]
  rfl

def MergerParameters (P parameters : M.Carrier .set) : Prop := ∀ z,
  (Project.FirstOrderSemantics.reduct M).mem z parameters ↔ MergerMember P z

def mergerParameters {m : Nat} (P parameters : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound parameters.succ)) (mergerMember P.succ 0))

theorem mergerParameters_freeClosed {m : Nat} (P parameters : Fin m) : (mergerParameters P parameters).FreeClosed := by
  simp [mergerParameters,Definitional.Formula.FreeClosed,mergerMember_freeClosed]

theorem mergerParameters_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (P parameters : Fin m) :
    Project.Formula.satisfies env (mergerParameters P parameters) ↔ MergerParameters (env.bound P) (env.bound parameters) := by
  simp only [mergerParameters,MergerParameters,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,mergerMember_semantics hM]
  rfl

theorem exists_merger_parameters (hM : FirstOrder.Theory.Models M nativeZF)
    {w n D P e : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) (hP : Prescription n D P)
    (he : (Project.FirstOrderSemantics.reduct M).mem e D) :
    ∃ parameters, MergerParameters P parameters ∧ Subset parameters D ∧ Small parameters w := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨B,hB⟩ := ZF.exists_cartesianProduct hZF pair n n
  have hww := (ForcingSupportSize.native_small hM w w).mp (omega_small hM w)
  have hInf : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal pair w w :=
    ⟨ExistingCardinalBounds.omega_cardinal_l pair hZF hw,hww⟩
  have hnSmall := (ForcingSupportSize.native_small hM n w).mp (nat_small hM hw hn)
  have hBSmall := (ForcingSupportSize.native_small hM B w).mpr
    (ExistingCardinalBounds.infinite_product_l pair hZF hw hInf hnSmall hnSmall hB)
  obtain ⟨F,hF,hFG⟩ := exists_coordinate_graph hM true hP he hB
  obtain ⟨G,hG,hGG⟩ := exists_coordinate_graph hM false hP he hB
  obtain ⟨R,hR,_,hRS⟩ := range_small hM hw hF hBSmall
  obtain ⟨S,hS,_,hSS⟩ := range_small hM hw hG hBSmall
  obtain ⟨U,hU⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) R S
  have hUS := (ForcingSupportSize.native_small hM U w).mpr
    (ExistingCardinalBounds.infinite_union_two_l pair hZF hw hInf
      ((ForcingSupportSize.native_small hM R w).mp hRS) ((ForcingSupportSize.native_small hM S w).mp hSS) hU)
  let schema : Project.UnarySchema 1 := {
    body := mergerMember 1 0
    freeClosed := mergerMember_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 := {bound := fun _ => P,free := fun _ => D}
  obtain ⟨parameters,hParam⟩ := ZF.separation_exists_d hZF schema env D
  have hp z : (Project.FirstOrderSemantics.reduct M).mem z parameters ↔ MergerMember P z := by
    have hm := mergerMember_semantics hM (env.push z) 1 0
    refine (hParam z).trans ⟨fun h => hm.mp h.2,?_⟩
    intro h
    obtain ⟨i,j,a,b,hStart,hz⟩ := h
    have hab := hP.1 i j a b hStart
    refine ⟨hz.elim (fun heq => heq.symm ▸ hab.2.2.1) (fun heq => heq.symm ▸ hab.2.2.2),?_⟩
    exact hm.mpr ⟨i,j,a,b,hStart,hz⟩
  refine ⟨parameters,hp,fun z hz => ((hParam z).mp hz).1,ForcingSupportSize.small_subset hM (B := U) ?_ hUS⟩
  intro z hz
  obtain ⟨i,j,a,b,hStart,hz⟩ := (hp z).mp hz
  have hab := hP.1 i j a b hStart
  obtain ⟨q,hq⟩ := pair.total i j
  have hqB := (hB q).mpr ⟨i,hab.1,j,hab.2.1,hq⟩
  rcases hz with hza | hzb
  · subst z
    exact (hU a).mpr (Or.inl ((hR a).mpr ⟨q,hqB,(hFG q a).mpr
      ⟨hqB,i,j,hq,Or.inl ⟨a,b,hStart,rfl⟩⟩⟩))
  · subst z
    exact (hU b).mpr (Or.inr ((hS b).mpr ⟨q,hqB,(hGG q b).mpr
      ⟨hqB,i,j,hq,Or.inl ⟨a,b,hStart,rfl⟩⟩⟩))

/-- Same actual endpoint and local dependency graph, now with the parameter
and generator countability inputs discharged by the two actual cell cases. -/
def Result (w D I W V H e O P F R parameters old generators C deps : M.Carrier .set) : Prop :=
  ConstructionAttachmentCoefficients.ImageResult w D I W V H e O P F R old generators ∧
    Subset parameters D ∧ Small parameters w ∧ Small I w ∧
    ConstructionAttachmentDependencies.Supports w D I V H e old generators R C ∧
    ConstructionAttachmentDependencies.Graph D I generators parameters R C deps ∧
    ConstructionCountableConservativeHull.Dependencies w R deps

theorem exists_result (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w D I W V H e O P F R parameters old generators : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hA : ConstructionAttachmentCoefficients.ImageResult w D I W V H e O P F R old generators)
    (hSourceGen : MapsTo I W P) (hParams : Subset parameters D) (hSmall : Small parameters w) (hI : Small I w) :
    ∃ C deps, Result w D I W V H e O P F R parameters old generators C deps := by
  have hCopy := hA
  obtain ⟨hRange,hRV,hDR,_,_,_,hGen,hNode,_⟩ := hCopy
  obtain ⟨C,deps,hC,hG⟩ := ConstructionAttachmentDependencies.exists_for_attachment hM hOrder hA
    (fun z hz => hRV z (hDR z (hParams z hz)))
  have hGenR : MapsTo I R generators := ⟨hGen.1,fun i z hiz => by
    obtain ⟨y,hiy,hyz⟩ := (hNode i z).mp hiz
    exact (hRange z).mpr ⟨y,hSourceGen.2 i y hiy,hyz⟩⟩
  have hCount := ConstructionAttachmentDependencies.countable_rows hM hw hC hG hGen hI hSmall
  refine ⟨C,deps,hA,hParams,hSmall,hI,hC,hG,hG.1,?_⟩
  intro x Y hxy
  refine ⟨?_,hCount x Y hxy⟩
  intro z hz
  have hRow := ((hG.2 x Y).mp hxy).2
  rcases ((hRow z).mp hz).2 with hz | ⟨i,_,hiz⟩ | ⟨S,hxS,hz⟩
  · exact hDR z (hParams z hz)
  · exact hGenR.2 i z hiz
  · exact hDR z (((hC.2 x S).mp hxS).2.1.1 z hz)

theorem actual_probe (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O V H eV F R : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hA : ConstructionProbePushout.Presentation hM w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O)
    (hF : ConstructionProbePushout.Hom W V G H unit eV F)
    (hFixed : ConstructionAttachmentCoefficients.OldFixed O F) (hRange : Range W F R) :
    ∃ parameters old generators supports deps, ProbeParameters a b d node parameters ∧
      Result w D w W V H eV O P F R parameters old generators supports deps := by
  obtain ⟨parameters,hParam,hPD,hPS⟩ := exists_probe_parameters hM hw hA.path.1 hA.path.2.1 hA.b_mem hA.d_mem
  obtain ⟨R',old,generators,hResult⟩ := ConstructionAttachmentCoefficients.probe_image hM hA hw hz hzw hF hFixed
  have hSame := ConstructionAttachmentCoefficients.image_at_range hM hResult hRange
  obtain ⟨supports,deps,hData⟩ := exists_result hM hOrder hw hSame hA.probes_map hPD hPS (omega_small hM w)
  exact ⟨parameters,old,generators,supports,deps,hParam,hData⟩

theorem actual_merger (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    {w n zero D mul e P C L projection A W T B G unit O roots V H eV F R : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hA : ConstructionMergerPushout.Presentation w n zero D mul e P C L projection A W T B G unit O roots)
    (hF : ConstructionProbePushout.Hom W V G H unit eV F)
    (hFixed : ConstructionAttachmentCoefficients.OldFixed O F) (hRange : Range W F R) :
    ∃ parameters old generators supports deps, MergerParameters P parameters ∧
      Result w D n W V H eV O roots F R parameters old generators supports deps := by
  obtain ⟨parameters,hParam,hPD,hPS⟩ := exists_merger_parameters hM hw hn hA.prescription hA.monoid.1.1
  obtain ⟨R',old,generators,hResult⟩ := ConstructionAttachmentCoefficients.merger_image hM hA hw hz hzw hF hFixed
  have hSame := ConstructionAttachmentCoefficients.image_at_range hM hResult hRange
  obtain ⟨supports,deps,hData⟩ := exists_result hM hOrder hw hSame hA.roots_map hPD hPS (nat_small hM hw hn)
  exact ⟨parameters,old,generators,supports,deps,hParam,hData⟩

def result {m : Nat} (w D I W V H e O P F R parameters old generators C deps : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionAttachmentCoefficients.imageResult w D I W V H e O P F R old generators)
      (.conj (Project.Formula.subset (.bound parameters) (.bound D))
      (.conj (ProjectSyntax.encode id (ForcingSupportSize.small parameters w))
      (.conj (ProjectSyntax.encode id (ForcingSupportSize.small I w))
      (.conj (ConstructionAttachmentDependencies.supports w D I V H e old generators R C)
      (.conj (ConstructionAttachmentDependencies.graph D I generators parameters R C deps)
      (ConstructionCountableConservativeHull.dependencies w R deps)))))))

theorem result_freeClosed {m : Nat} (w D I W V H e O P F R parameters old generators C deps : Fin m) :
    (result w D I W V H e O P F R parameters old generators C deps).FreeClosed := by
  simp [result,Definitional.Formula.FreeClosed,Project.Formula.subset,ProjectSyntax.freeClosed,
    ConstructionAttachmentCoefficients.imageResult_freeClosed,ConstructionAttachmentDependencies.supports_freeClosed,
    ConstructionAttachmentDependencies.graph_freeClosed,ConstructionCountableConservativeHull.dependencies_freeClosed]

theorem result_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D I W V H e O P F R parameters old generators C deps : Fin m) :
    Project.Formula.satisfies env (result w D I W V H e O P F R parameters old generators C deps) ↔
      Result (env.bound w) (env.bound D) (env.bound I) (env.bound W) (env.bound V) (env.bound H) (env.bound e) (env.bound O) (env.bound P) (env.bound F) (env.bound R) (env.bound parameters) (env.bound old) (env.bound generators) (env.bound C) (env.bound deps) := by
  simp only [result,Result,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_subset_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ConstructionAttachmentCoefficients.imageResult_semantics hM,
    ConstructionAttachmentDependencies.supports_semantics hM,ConstructionAttachmentDependencies.graph_semantics hM,
    ConstructionCountableConservativeHull.dependencies_semantics hM]
  rfl

/-- The actual probe supplies all parameter/index countability witnesses. -/
def probeSentence {m : Nat} (w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O V H eV F R : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOmega (.bound w))
      (.imp (Project.Formula.isEmpty (.bound zero))
      (.imp (.mem (.bound zero) (.bound w))
      (.imp (ConstructionProbePushoutSyntax.presentation w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O)
      (.imp (ConstructionProbePushoutSyntax.hom W V G H unit eV F)
      (.imp (ConstructionAttachmentCoefficients.oldFixed O F)
      (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range W F R))
      (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (probeParameters a.succ.succ.succ.succ.succ b.succ.succ.succ.succ.succ d.succ.succ.succ.succ.succ node.succ.succ.succ.succ.succ 4)
      (result w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ w.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ H.succ.succ.succ.succ.succ eV.succ.succ.succ.succ.succ O.succ.succ.succ.succ.succ P.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ 4 3 2 1 0))))))))))))))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.isInductive,
      Project.Formula.isEmpty,Project.Formula.isSuccessor,ProjectSyntax.freeClosed,
      ConstructionProbePushoutSyntax.presentation_freeClosed,ConstructionProbePushoutSyntax.hom_freeClosed,
      ConstructionAttachmentCoefficients.oldFixed_freeClosed,probeParameters_freeClosed,result_freeClosed]

theorem probe_models {m : Nat} (w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O V H eV F R : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M))) :
    (Project.fo_sentence (probeSentence w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O V H eV F R)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (probeSentence w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O V H eV F R)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionProbePushoutSyntax.presentation_semantics hM,ConstructionProbePushoutSyntax.hom_semantics hM,
    ConstructionAttachmentCoefficients.oldFixed_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportedNames.range_semantics (M := M),probeParameters_semantics hM,result_semantics hM]
  exact actual_probe hM hOrder

theorem probe_kernel_certificate {m : Nat} (w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O V H eV F R : Fin m) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (probeSentence w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O V H eV F R))) := by
  apply ModelTransfer.derives
  intro M hM
  apply ConstructibleGround.relative_models hM (probeSentence w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O V H eV F R)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality (ConstructibleSource.model_zf hM)) (probeSentence w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O V H eV F R)).mp
    (probe_models w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O V H eV F R (ConstructibleSource.model_zf hM) (ConstructionRoundSelection.l_order hM))

/-- The actual merger supplies all parameter/index countability witnesses. -/
def mergerSentence {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots V H eV F R : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOmega (.bound w))
      (.imp (.mem (.bound n) (.bound w))
      (.imp (Project.Formula.isEmpty (.bound zero))
      (.imp (.mem (.bound zero) (.bound w))
      (.imp (ConstructionMergerPushout.presentation w n zero D mul e P C L projection A W T B G unit O roots)
      (.imp (ConstructionProbePushoutSyntax.hom W V G H unit eV F)
      (.imp (ConstructionAttachmentCoefficients.oldFixed O F)
      (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range W F R))
      (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (mergerParameters P.succ.succ.succ.succ.succ 4)
      (result w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ n.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ H.succ.succ.succ.succ.succ eV.succ.succ.succ.succ.succ O.succ.succ.succ.succ.succ roots.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ 4 3 2 1 0)))))))))))))))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.isInductive,
      Project.Formula.isEmpty,Project.Formula.isSuccessor,ProjectSyntax.freeClosed,
      ConstructionMergerPushout.presentation_freeClosed,ConstructionProbePushoutSyntax.hom_freeClosed,
      ConstructionAttachmentCoefficients.oldFixed_freeClosed,mergerParameters_freeClosed,result_freeClosed]

theorem merger_models {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots V H eV F R : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M))) :
    (Project.fo_sentence (mergerSentence w n zero D mul e P C L projection A W T B G unit O roots V H eV F R)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (mergerSentence w n zero D mul e P C L projection A W T B G unit O roots V H eV F R)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionMergerPushout.presentation_semantics hM,ConstructionProbePushoutSyntax.hom_semantics hM,
    ConstructionAttachmentCoefficients.oldFixed_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportedNames.range_semantics (M := M),mergerParameters_semantics hM,result_semantics hM]
  exact actual_merger hM hOrder

theorem merger_kernel_certificate {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots V H eV F R : Fin m) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (mergerSentence w n zero D mul e P C L projection A W T B G unit O roots V H eV F R))) := by
  apply ModelTransfer.derives
  intro M hM
  apply ConstructibleGround.relative_models hM (mergerSentence w n zero D mul e P C L projection A W T B G unit O roots V H eV F R)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality (ConstructibleSource.model_zf hM)) (mergerSentence w n zero D mul e P C L projection A W T B G unit O roots V H eV F R)).mp
    (merger_models w n zero D mul e P C L projection A W T B G unit O roots V H eV F R (ConstructibleSource.model_zf hM) (ConstructionRoundSelection.l_order hM))

end PPAC.Migration.ConstructionCellParameters
