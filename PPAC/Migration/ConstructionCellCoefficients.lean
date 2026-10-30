/- Pinned ConservativeCells.Cell.finite_coefficients.
Internal finite sets are witnessed by an actual surjection from an internal
natural ordinal. Union uses existing ZF ordinal addition and function graphs;
the ZFC-only PureSequenceConcatenation wrapper is not assumed. -/
import PPAC.Migration.ConstructionCellGeneration
import PPAC.Migration.ExistingOrdinalImage
import YesMetaZFC.SetTheory.Ord.Arithmetic.Comparison

namespace PPAC.Migration.ConstructionCellCoefficients
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionCellGeneration
open ConstructionRealCuts (Subset)
open ForcingSupportSize (MapsTo Small)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Internal finite enumeration, allowing repetitions, with exact range S. -/
def Finite (w S : M.Carrier .set) : Prop := ∃ n f,
  (Project.FirstOrderSemantics.reduct M).mem n w ∧ MapsTo n S f ∧
    ∀ x, (Project.FirstOrderSemantics.reduct M).mem x S →
      ∃ i, (Project.FirstOrderSemantics.reduct M).mem i n ∧ PureKuratowski.PairMember M i x f

def finite {m : Nat} (w S : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (.mem (.bound 1) (.bound w.succ.succ))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 0 1 S.succ.succ))
      (.forallE (.imp (.mem (.bound 0) (.bound S.succ.succ.succ))
        (.existsE (.conj (.mem (.bound 0) (.bound 3))
          (ProjectSyntax.encode id (Source.SetLanguage.edge 2 0 1)))))))))

theorem finite_freeClosed {m : Nat} (w S : Fin m) : (finite w S).FreeClosed := by
  simp [finite,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem finite_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w S : Fin m) :
    Project.Formula.satisfies env (finite w S) ↔ Finite (env.bound w) (env.bound S) := by
  simp only [finite,Finite,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.mapsTo_semantics (M := M),KuratowskiZF.source_edge]
  rfl

/-- The enumeration implies an actual injection into an internal natural;
reuse the pinned donor's least-preimage ordinal-image bound, without Choice. -/
theorem finite_bound (hM : FirstOrder.Theory.Models M nativeZF) {w S : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hS : Finite w S) :
    ∃ n, (Project.FirstOrderSemantics.reduct M).mem n w ∧ Small S n := by
  obtain ⟨n,f,hn,hf,hs⟩ := hS
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨ident,hIdent⟩ := ZF.exists_identityBijection hZF I n
  exact ⟨n,hn,(ForcingSupportSize.native_small hM S n).mpr
    (ExistingOrdinalImage.ordinal_image_bound_l I hZF (hw.members_areOrdinals hZF n hn)
      ⟨ident,hIdent.1⟩
      ((ForcingSupportSize.native_mapsTo hM n S f).mp hf) hs)⟩

theorem finite_empty (hM : FirstOrder.Theory.Models M nativeZF) {w zero : M.Carrier .set}
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w) : Finite w zero := by
  have hf : MapsTo zero zero zero := ConstructionProbeRaw.maps_of_sequence hM
    (SetTheory.Structure.IsSequenceOfLength.empty (KuratowskiZF.interpretation hM) hz)
    (by intro i y h; obtain ⟨p,_,hp⟩ := h; exact (hz p hp).elim)
  exact ⟨zero,zero,hzw,hf,fun x hx => (hz x hx).elim⟩

theorem finite_singleton (hM : FirstOrder.Theory.Models M nativeZF) {w zero a S : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hS : ∀ x, (Project.FirstOrderSemantics.reduct M).mem x S ↔ x = a) : Finite w S := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨one,hOne,hOneW⟩ := hw.1.2 zero hzw
  obtain ⟨f,hf,hGraph⟩ := (SetTheory.Structure.IsSequenceOfLength.empty
    (KuratowskiZF.interpretation hM) hz).exists_append (ZF.modelsKP hZF)
    (KuratowskiZF.interpretation hM) (value := a) (hw.members_areOrdinals hZF one hOneW) hOne
  have hMap : MapsTo one S f := ConstructionProbeRaw.maps_of_sequence hM hf (by
    intro i x hx
    rcases (hGraph i x).mp hx with ⟨p,_,hp⟩ | ⟨_,hxa⟩
    · exact (hz p hp).elim
    · exact (hS x).mpr hxa)
  refine ⟨one,f,hOneW,hMap,?_⟩
  intro x hx
  have he := (hS x).mp hx
  subst x
  exact ⟨zero,hOne.predecessor_mem,(hGraph zero a).mpr (Or.inr ⟨rfl,rfl⟩)⟩

/-- The native-ZF selector underlying the existing concatenation proof. -/
def ConcatValue (hM : FirstOrder.Theory.Models M nativeZF) (n m f g i x : M.Carrier .set) : Prop :=
  ((Project.FirstOrderSemantics.reduct M).mem i n ∧ PureKuratowski.PairMember M i x f) ∨
    ∃ j, (Project.FirstOrderSemantics.reduct M).mem j m ∧
      (Project.FirstOrderSemantics.reduct M).IsOrdinalAddition (KuratowskiZF.interpretation hM) i n j ∧
      PureKuratowski.PairMember M j x g

def concatValue {k : Nat} (n m f g i x : Fin k) : Project.Formula 1 k :=
  .disj (.conj (.mem (.bound i) (.bound n)) (ProjectSyntax.encode id (Source.SetLanguage.edge f i x)))
    (.existsE (.conj (.mem (.bound 0) (.bound m.succ))
      (.conj (Project.Formula.isOrdinalAddition PureKuratowskiProject.convention (.bound i.succ) (.bound n.succ) (.bound 0))
        (ProjectSyntax.encode id (Source.SetLanguage.edge g.succ 0 x.succ)))))

theorem concatValue_freeClosed {k : Nat} (n m f g i x : Fin k) : (concatValue n m f g i x).FreeClosed := by
  simp -implicitDefEqProofs [concatValue,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem concatValue_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k) (n m f g i x : Fin k) :
    Project.Formula.satisfies env (concatValue n m f g i x) ↔
      ConcatValue hM (env.bound n) (env.bound m) (env.bound f) (env.bound g) (env.bound i) (env.bound x) := by
  simp only [concatValue,ConcatValue,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isOrdinalAddition_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

/-- Only the finite-union fact used by source closure_induction. -/
theorem finite_union (hM : FirstOrder.Theory.Models M nativeZF) {w S T U : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hS : Finite w S) (hT : Finite w T)
    (hU : ∀ x, (Project.FirstOrderSemantics.reduct M).mem x U ↔
      (Project.FirstOrderSemantics.reduct M).mem x S ∨ (Project.FirstOrderSemantics.reduct M).mem x T) : Finite w U := by
  obtain ⟨n,f,hn,hf,hfs⟩ := hS
  obtain ⟨m,g,hm,hg,hgs⟩ := hT
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  have hnO := hw.members_areOrdinals hZF n hn
  have hmO := hw.members_areOrdinals hZF m hm
  obtain ⟨len,hLen,_⟩ := ZF.ordinalAddition_existsUnique hZF I n hmO
  have hLenW := ZF.ordinalAddition_mem_omega hZF I hw hn hm hLen
  have hParts i := ZF.ordinalAddition_mem_iff hZF I (value := i) hmO hLen
  have hDisjoint {i j} (hi : (Project.FirstOrderSemantics.reduct M).mem i n)
      (hj : (Project.FirstOrderSemantics.reduct M).mem j m)
      (hAdd : (Project.FirstOrderSemantics.reduct M).IsOrdinalAddition I i n j) : False := by
    have hjO := hw.members_areOrdinals hZF j (hw.transitive hZF m hm j hj)
    rcases ZF.ordinalAddition_left_eq_or_mem hZF I hjO hAdd with he | hni
    · exact hnO.wellOrder.linear.irrefl n (he ▸ hi) (he ▸ hi)
    · have hSelf := hnO.transitive i hi n hni
      exact hnO.wellOrder.linear.irrefl n hSelf hSelf
  let schema : Project.BinarySchema 4 := {
    body := concatValue 2 3 4 5 1 0
    freeClosed := concatValue_freeClosed _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 := {
    bound := Fin.cases n (Fin.cases m (Fin.cases f (fun _ => g)))
    free := fun _ => w }
  have he i x : schema.denote env i x ↔ ConcatValue hM n m f g i x :=
    concatValue_semantics hM ((env.push i).push x) 2 3 4 5 1 0
  obtain ⟨F,hF,hFG⟩ := ZF.exists_setFunctionFromTo_of_denote hZF I schema env (source := len) (target := U) (by
    intro i hi
    rcases (hParts i).mp hi with hiN | ⟨j,hj,hAdd⟩
    · obtain ⟨x,hix,_⟩ := hf.1.2 i hiN
      exact ⟨x,(he i x).mpr (Or.inl ⟨hiN,hix⟩)⟩
    · obtain ⟨x,hjx,_⟩ := hg.1.2 j hj
      exact ⟨x,(he i x).mpr (Or.inr ⟨j,hj,hAdd,hjx⟩)⟩) (by
    intro i _ x y hx hy
    rcases (he i x).mp hx with ⟨hi,hix⟩ | ⟨j,hj,hAdd,hjx⟩
    · rcases (he i y).mp hy with ⟨_,hiy⟩ | ⟨j,hj,hAdd,_⟩
      · exact ForcingConditionGraphs.function_unique hf.1 hix hiy
      · exact (hDisjoint hi hj hAdd).elim
    · rcases (he i y).mp hy with ⟨hi,_⟩ | ⟨k,hk,hAddK,hky⟩
      · exact (hDisjoint hi hj hAdd).elim
      · have hjO := hw.members_areOrdinals hZF j (hw.transitive hZF m hm j hj)
        have hkO := hw.members_areOrdinals hZF k (hw.transitive hZF m hm k hk)
        have hjk := ZF.ordinalAddition_right_injective hZF I hnO hjO hkO hAdd hAddK
        subst k
        exact ForcingConditionGraphs.function_unique hg.1 hjx hky) (by
    intro i x _ hx
    rcases (he i x).mp hx with ⟨_,hix⟩ | ⟨j,_,_,hjx⟩
    · exact (hU x).mpr (Or.inl (hf.2 i x hix))
    · exact (hU x).mpr (Or.inr (hg.2 j x hjx)))
  refine ⟨len,F,hLenW,(ForcingSupportSize.native_mapsTo hM len U F).mpr hF,?_⟩
  intro x hx
  rcases (hU x).mp hx with hxS | hxT
  · obtain ⟨i,hi,hix⟩ := hfs x hxS
    have hiL := (hParts i).mpr (Or.inl hi)
    exact ⟨i,hiL,(hFG i x).mpr ⟨hiL,(he i x).mpr (Or.inl ⟨hi,hix⟩)⟩⟩
  · obtain ⟨j,hj,hjx⟩ := hgs x hxT
    obtain ⟨i,hAdd,_⟩ := ZF.ordinalAddition_existsUnique hZF I n (hw.members_areOrdinals hZF j (hw.transitive hZF m hm j hj))
    have hiL := (hParts i).mpr (Or.inr ⟨j,hj,hAdd⟩)
    exact ⟨i,hiL,(hFG i x).mpr ⟨hiL,(he i x).mpr (Or.inr ⟨j,hj,hAdd,hjx⟩)⟩⟩

/-- Exact source conclusion: only the old coefficients are finite. -/
def Coefficients (w D I W G unit O P x : M.Carrier .set) : Prop := ∃ S,
  Subset S D ∧ Finite w S ∧ ClosureMember I W G unit O P S x

def coefficients {m : Nat} (w D I W G unit O P x : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (Project.Formula.subset (.bound 0) (.bound D.succ))
    (.conj (finite w.succ 0) (closureMember I.succ W.succ G.succ unit.succ O.succ P.succ 0 x.succ)))

theorem coefficients_freeClosed {m : Nat} (w D I W G unit O P x : Fin m) :
    (coefficients w D I W G unit O P x).FreeClosed := by
  simp [coefficients,Definitional.Formula.FreeClosed,Project.Formula.subset,
    finite_freeClosed,closureMember_freeClosed]

theorem coefficients_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D I W G unit O P x : Fin m) :
    Project.Formula.satisfies env (coefficients w D I W G unit O P x) ↔
      Coefficients (env.bound w) (env.bound D) (env.bound I) (env.bound W) (env.bound G)
        (env.bound unit) (env.bound O) (env.bound P) (env.bound x) := by
  simp only [coefficients,Coefficients,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_subset_iff,
    Project.Term.eval_bound,finite_semantics hM,closureMember_semantics hM]
  rfl

/-- The source closure induction, realized as Separation on the actual carrier.
The four branches are old singleton, new empty, unit empty, and finite union. -/
theorem finite_coefficients (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I W G unit O P x : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hWhole : Submonoid W G unit W) (hO : MapsTo D W O) (hP : MapsTo I W P)
    (hx : ClosureMember I W G unit O P D x) : Coefficients w D I W G unit O P x := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨zero,hZero,hZeroW⟩ := hw.1.1
  have hZeroFinite := finite_empty hM hZero hZeroW
  have hZeroD : Subset zero D := fun a ha => (hZero a ha).elim
  let schema : Project.UnarySchema 8 := {
    body := coefficients 1 2 3 4 5 6 7 8 0
    freeClosed := coefficients_freeClosed _ _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 8 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases I (Fin.cases W (Fin.cases G (Fin.cases unit (Fin.cases O (fun _ => P)))))))
    free := fun _ => W }
  obtain ⟨A,hA⟩ := ZF.separation_exists_d hZF schema env W
  have hAiff y : (Project.FirstOrderSemantics.reduct M).mem y A ↔ Coefficients w D I W G unit O P y := by
    have he : schema.denote env y ↔ Coefficients w D I W G unit O P y :=
      coefficients_semantics hM (env.push y) 1 2 3 4 5 6 7 8 0
    refine (hA y).trans ⟨fun h => he.mp h.2,?_⟩
    intro h
    obtain ⟨S,hSD,hFin,hC⟩ := h
    exact ⟨hC.1,he.mpr ⟨S,hSD,hFin,hC⟩⟩
  have hSub : Submonoid W G unit A := by
    refine ⟨?_,?_,?_⟩
    · intro y hy
      obtain ⟨S,_,_,hy⟩ := (hAiff y).mp hy
      exact hy.1
    · exact (hAiff unit).mpr ⟨zero,hZeroD,hZeroFinite,hWhole.2.1,fun _ hs _ _ => hs.2.1⟩
    · intro y z yz hy hz hProd
      obtain ⟨S,hSD,hS,hyC⟩ := (hAiff y).mp hy
      obtain ⟨T,hTD,hT,hzC⟩ := (hAiff z).mp hz
      obtain ⟨U,hU⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) S T
      have hSU : Subset S U := fun a ha => (hU a).mpr (Or.inl ha)
      have hTU : Subset T U := fun a ha => (hU a).mpr (Or.inr ha)
      have hyU := closure_mono hSU hyC
      have hzU := closure_mono hTU hzC
      refine (hAiff yz).mpr ⟨U,?_,finite_union hM hw hS hT hU,
        hWhole.2.2 y z yz hyC.1 hzC.1 hProd,?_⟩
      · intro a ha
        exact ((hU a).mp ha).elim (hSD a) (hTD a)
      · intro S' hs ho hn
        exact hs.2.2 y z yz (hyU.2 S' hs ho hn) (hzU.2 S' hs ho hn) hProd
  have hOld : ImageIn D O A := by
    intro a y ha hay
    obtain ⟨S,hS⟩ := KP.exists_singleton (ZF.modelsKP hZF) a
    refine (hAiff y).mpr ⟨S,?_,finite_singleton hM hw hZero hZeroW hS,hO.2 a y hay,?_⟩
    · intro b hb
      exact (hS b).mp hb ▸ ha
    · intro S' _ ho _
      exact ho a y ((hS a).mpr rfl) hay
  have hNew : MapsTo I A P := by
    refine ⟨hP.1,?_⟩
    intro i y hiy
    exact (hAiff y).mpr ⟨zero,hZeroD,hZeroFinite,hP.2 i y hiy,fun _ _ _ hn => hn.2 i y hiy⟩
  exact (hAiff x).mp (hx.2 A hSub hOld hNew)

/-- Explicit finite cardinal bound on the same coefficient set. -/
theorem coefficients_bound (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I W G unit O P x : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hx : Coefficients w D I W G unit O P x) :
    ∃ S n, Subset S D ∧ (Project.FirstOrderSemantics.reduct M).mem n w ∧ Small S n ∧
      Finite w S ∧ ClosureMember I W G unit O P S x := by
  obtain ⟨S,hSD,hS,hC⟩ := hx
  obtain ⟨n,hn,hSmall⟩ := finite_bound hM hw hS
  exact ⟨S,n,hSD,hn,hSmall,hS,hC⟩

theorem merger_coefficients (hM : FirstOrder.Theory.Models M nativeZF)
    {w n zero D mul e P C L projection A W T B G unit O roots x : M.Carrier .set}
    (hA : ConstructionMergerPushout.Presentation w n zero D mul e P C L projection A W T B G unit O roots)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x W) : Coefficients w D n W G unit O roots x := by
  have hWhole : Submonoid W G unit W := ⟨fun _ h => h,hA.unit_law.1,?_⟩
  · exact finite_coefficients hM hw hWhole hA.old_hom.1 hA.roots_map
      (mem_closure (merger_generated hM hA hw hz hzw) hA.old_hom.1 hx)
  · intro a b c ha hb hProd
    obtain ⟨pair,hPair,hpc⟩ := hProd
    exact hA.product_map.2 pair c hpc

theorem probe_coefficients (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O x : M.Carrier .set}
    (hA : ConstructionProbePushout.Presentation hM w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x W) : Coefficients w D w W G unit O P x := by
  have hm := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hA.monoid hA.alphabet hA.word hA.b_mem hA.old_unit hA.multiplication
  have hWhole : Submonoid W G unit W := ⟨fun _ h => h,hm.1.1,
    fun a b c ha hb hProd => ConstructionMergerRelations.product_range hm ha hb hProd⟩
  exact finite_coefficients hM hw hWhole hA.old_map hA.probes_map
    (mem_closure (probe_generated hM hA hw hz hzw) hA.old_map hx)

/-- Both finite witnesses refer to the same actual coefficient set. -/
def boundedCoefficients {m : Nat} (w D I W G unit O P x : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (Project.Formula.subset (.bound 1) (.bound D.succ.succ))
    (.conj (.mem (.bound 0) (.bound w.succ.succ))
      (.conj (ProjectSyntax.encode id (ForcingSupportSize.small 1 0))
        (.conj (finite w.succ.succ 1)
          (closureMember I.succ.succ W.succ.succ G.succ.succ unit.succ.succ O.succ.succ P.succ.succ 1 x.succ.succ))))))

theorem boundedCoefficients_freeClosed {m : Nat} (w D I W G unit O P x : Fin m) :
    (boundedCoefficients w D I W G unit O P x).FreeClosed := by
  simp [boundedCoefficients,Definitional.Formula.FreeClosed,Project.Formula.subset,
    ProjectSyntax.freeClosed,finite_freeClosed,closureMember_freeClosed]

theorem boundedCoefficients_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D I W G unit O P x : Fin m) :
    Project.Formula.satisfies env (boundedCoefficients w D I W G unit O P x) ↔
      ∃ S n, Subset S (env.bound D) ∧ (Project.FirstOrderSemantics.reduct M).mem n (env.bound w) ∧
        Small S n ∧ Finite (env.bound w) S ∧ ClosureMember (env.bound I) (env.bound W) (env.bound G)
          (env.bound unit) (env.bound O) (env.bound P) S (env.bound x) := by
  simp only [boundedCoefficients,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_subset_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,finite_semantics hM,closureMember_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.small_semantics (M := M)]
  rfl

/-- Literal finite old coefficients for every internal cell element, including
nonstandard internal words. The complete new-generator image is unchanged. -/
def mergerSentence {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero))
      (.imp (.mem (.bound zero) (.bound w)) (.imp (ConstructionMergerPushout.presentation w n zero D mul e P C L projection A W T B G unit O roots)
        (.forallE (.imp (.mem (.bound 0) (.bound W.succ))
          (boundedCoefficients w.succ D.succ n.succ W.succ G.succ unit.succ O.succ roots.succ 0)))))))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.isInductive,
      Project.Formula.isSuccessor,Project.Formula.isEmpty,ConstructionMergerPushout.presentation_freeClosed,
      boundedCoefficients_freeClosed]

theorem merger_models {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (mergerSentence w n zero D mul e P C L projection A W T B G unit O roots)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (mergerSentence w n zero D mul e P C L projection A W T B G unit O roots)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_forall_iff,ConstructionMergerPushout.presentation_semantics hM,boundedCoefficients_semantics hM]
  intro hw hz hzw hA x hx
  exact coefficients_bound hM hw (merger_coefficients hM hA hw hz hzw hx)

theorem merger_kernel_certificate {m : Nat} (w n zero D mul e P C L projection A W T B G unit O roots : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (mergerSentence w n zero D mul e P C L projection A W T B G unit O roots)) :=
  ModelTransfer.derives (fun _ hM => merger_models w n zero D mul e P C L projection A W T B G unit O roots hM)

/-- Literal finite old coefficients for every internal cell element, including
nonstandard internal words. The complete new-generator image is unchanged. -/
def probeSentence {m : Nat} (w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero))
      (.imp (.mem (.bound zero) (.bound w)) (.imp (ConstructionProbePushoutSyntax.presentation w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O)
        (.forallE (.imp (.mem (.bound 0) (.bound W.succ))
          (boundedCoefficients w.succ D.succ w.succ W.succ G.succ unit.succ O.succ P.succ 0)))))))
  freeClosed := by
    simp [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.isInductive,
      Project.Formula.isSuccessor,Project.Formula.isEmpty,ConstructionProbePushoutSyntax.presentation_freeClosed,
      boundedCoefficients_freeClosed]

theorem probe_models {m : Nat} (w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (probeSentence w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (probeSentence w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_forall_iff,ConstructionProbePushoutSyntax.presentation_semantics hM,boundedCoefficients_semantics hM]
  intro hw hz hzw hA x hx
  exact coefficients_bound hM hw (probe_coefficients hM hA hw hz hzw hx)

theorem probe_kernel_certificate {m : Nat} (w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (probeSentence w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O)) :=
  ModelTransfer.derives (fun _ hM => probe_models w zero D mul e a b d node factor terminal target L C projection I act E W unit G K P O hM)

end PPAC.Migration.ConstructionCellCoefficients
