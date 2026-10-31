/- Pinned ConcreteQuotients.countable_quotient_of_cells: source tail cosets.
Actual internal eventual agreement is identified with inverse(pi)*sigma fixing
a chain tail. Classes and their full quotient are constructed as sets. -/
import PPAC.Migration.ConstructionCountableAlignments

namespace PPAC.Migration.ConstructionGermCosets
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingConditionGraphs (Permutation CompositionGraph InverseGraph function_input function_unique)
open ForcingSupportSize (MapsTo Injection Small)
open ForcingSupportedNames (Range)
open ConstructionComponentCarrier (Code)
open ConstructionComponentCofinal (Chain)
open ConstructionFractionOrder (NatLe)
open ConstructionRealCuts (Subset)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Agree (A pi sigma : M.Carrier .set) : Prop := ∀ x y,
  (Project.FirstOrderSemantics.reduct M).mem x A →
    (PureKuratowski.PairMember M x y pi ↔ PureKuratowski.PairMember M x y sigma)

def Same (w D chain pi sigma : M.Carrier .set) : Prop :=
  ∃ N v r a U A, (Project.FirstOrderSemantics.reduct M).mem N w ∧
    PureKuratowski.PairMember M N v chain ∧ Code v r a U ∧ Range D r A ∧ Agree A pi sigma

theorem stage_range (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain i v : M.Carrier .set}
    (hC : Chain w D I mul q zero root vertices chain) (hiv : PureKuratowski.PairMember M i v chain) :
    ∃ r a U A, Code v r a U ∧ Range D r A ∧ Subset A I := by
  obtain ⟨_,_,_,r,a,U,_,hv,_,hr,_⟩ := hC.2.2.2.1 i v hiv
  have hNative := (ForcingSupportSize.native_injection hM D I r).mp hr.1
  obtain ⟨A,hA⟩ := ZF.exists_range_of_setFunction (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) hNative.1.1 hNative.1.2.1
  have hRange : Range D r A := fun x => ⟨fun hx => by
    obtain ⟨k,hkx⟩ := (hA x).mp hx
    exact ⟨k,hNative.1.input_mem_of_pairMember hkx,hkx⟩,
    fun ⟨k,_,hkx⟩ => (hA x).mpr ⟨k,hkx⟩⟩
  exact ⟨r,a,U,A,hv,hRange,ForcingTailGroup.range_subset hr.1 hRange⟩

theorem stage_range_subset {w D I mul q zero root vertices chain i v r a U A : M.Carrier .set}
    (hC : Chain w D I mul q zero root vertices chain) (hiv : PureKuratowski.PairMember M i v chain)
    (hCode : Code v r a U) (hA : Range D r A) : Subset A I := by
  obtain ⟨_,_,_,r',a',U',_,hv,_,hr,_⟩ := hC.2.2.2.1 i v hiv
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hv hCode
  exact ForcingTailGroup.range_subset hr.1 hA

theorem agree_later {w D I mul q zero root vertices chain N i vN v rN aN UN r a U AN A pi sigma : M.Carrier .set}
    (hC : Chain w D I mul q zero root vertices chain) (hNi : NatLe N i)
    (hNv : PureKuratowski.PairMember M N vN chain) (hiv : PureKuratowski.PairMember M i v chain)
    (hCodeN : Code vN rN aN UN) (hCode : Code v r a U) (hAN : Range D rN AN) (hA : Range D r A)
    (hAgree : Agree AN pi sigma) : Agree A pi sigma := by
  obtain ⟨n,rN',aN',UN',r',a',U',hCodeN',hCode',hrN,_,hArrow⟩ := hC.2.2.1 N i vN v hNi hNv hiv
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hCodeN' hCodeN
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hCode' hCode
  intro x y hx
  exact hAgree x y ((hAN x).mpr (ConstructionDescentPlacement.range_antitone
    ⟨n,hrN.2.2.1 n hArrow.1,hArrow.2.1⟩ ((hA x).mp hx)))

theorem same_refl (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain pi : M.Carrier .set}
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hC : Chain w D I mul q zero root vertices chain) : Same w D chain pi pi := by
  obtain ⟨r,a,U,A,hCode,hA,_⟩ := stage_range hM hC hC.2.1
  exact ⟨zero,root,r,a,U,A,hzw,hC.2.1,hCode,hA,fun _ _ _ => Iff.rfl⟩

theorem same_symm {w D chain pi sigma : M.Carrier .set} (h : Same w D chain pi sigma) :
    Same w D chain sigma pi := by
  obtain ⟨N,v,r,a,U,A,hN,hv,hCode,hA,hAgree⟩ := h
  exact ⟨N,v,r,a,U,A,hN,hv,hCode,hA,fun x y hx => (hAgree x y hx).symm⟩

theorem same_trans (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain pi sigma tau : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hC : Chain w D I mul q zero root vertices chain)
    (h : Same w D chain pi sigma) (h' : Same w D chain sigma tau) : Same w D chain pi tau := by
  obtain ⟨N,vN,rN,aN,UN,AN,hN,hNv,hCodeN,hAN,hAgreeN⟩ := h
  obtain ⟨i,v,r,a,U,A,hi,hiv,hCode,hA,hAgree⟩ := h'
  rcases ConstructionFractionOrder.nat_compare hM hw hN hi with he | hNi | hiN
  · have hN' := agree_later hC (Or.inl he) hNv hiv hCodeN hCode hAN hA hAgreeN
    exact ⟨i,v,r,a,U,A,hi,hiv,hCode,hA,fun x y hx => (hN' x y hx).trans (hAgree x y hx)⟩
  · have hN' := agree_later hC (Or.inr hNi) hNv hiv hCodeN hCode hAN hA hAgreeN
    exact ⟨i,v,r,a,U,A,hi,hiv,hCode,hA,fun x y hx => (hN' x y hx).trans (hAgree x y hx)⟩
  · have hi' := agree_later hC (Or.inr hiN) hiv hNv hCode hCodeN hA hAN hAgree
    exact ⟨N,vN,rN,aN,UN,AN,hN,hNv,hCodeN,hAN,fun x y hx => (hAgreeN x y hx).trans (hi' x y hx)⟩

/-- Exact original quotient relation, for the actual inverse and product
permutation graphs; no weaker quotient of selected alignments is substituted. -/
theorem same_iff_tail {w D I mul q zero root vertices chain pi sigma inv diff : M.Carrier .set}
    (hC : Chain w D I mul q zero root vertices chain)
    (hp : Permutation I pi) (hs : Permutation I sigma)
    (hInv : InverseGraph pi inv) (hComp : CompositionGraph I inv sigma diff) :
    Same w D chain pi sigma ↔ ForcingTailCovariance.TailFixes w D diff chain := by
  constructor
  · rintro ⟨N,v,r,a,U,A,hN,hv,hCode,hA,hAgree⟩
    refine ⟨N,v,r,a,U,A,hN,hv,hCode,hA,?_⟩
    intro x hx
    have hxI := stage_range_subset hC hv hCode hA x hx
    obtain ⟨y,hxy,_⟩ := hp.1.1.2 x hxI
    exact (hComp x x).mpr ⟨hxI,y,(hAgree x y hx).mp hxy,(hInv x y).mp hxy⟩
  · rintro ⟨N,v,r,a,U,A,hN,hv,hCode,hA,hFix⟩
    refine ⟨N,v,r,a,U,A,hN,hv,hCode,hA,?_⟩
    intro x y hx
    obtain ⟨_,z,hxz,hzx⟩ := (hComp x x).mp (hFix x hx)
    have hpz := (hInv x z).mpr hzx
    constructor
    · intro hxy
      have he := function_unique hp.1.1 hxy hpz
      exact he.symm ▸ hxz
    · intro hxy
      have he := function_unique hs.1.1 hxy hxz
      exact he.symm ▸ hpz

theorem same_of_alignment (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain pi sigma i x : M.Carrier .set}
    (hC : Chain w D I mul q zero root vertices chain)
    (hp : Permutation I pi) (hs : Permutation I sigma)
    (ha : ForcingGermAlignments.Alignment D I mul q root chain pi i x)
    (hb : ForcingGermAlignments.Alignment D I mul q root chain sigma i x) : Same w D chain pi sigma := by
  obtain ⟨inv,hi,hInv⟩ := ForcingConditionGraphs.exists_inverse hM hp
  obtain ⟨diff,_,hComp⟩ := ForcingConditionGraphs.exists_composition hM hi hs
  exact (same_iff_tail hC hp hs hInv hComp).mpr (ForcingGermAlignments.same_alignment_tail hM hC hp hInv hComp ha hb)

def Carrier (D I mul q root H : M.Carrier .set) : Prop := ∀ pi,
  (Project.FirstOrderSemantics.reduct M).mem pi H ↔ ConstructionCountableAlignments.Stabilizes D I mul q root pi

def Class (w D chain H pi C : M.Carrier .set) : Prop := ∀ sigma,
  (Project.FirstOrderSemantics.reduct M).mem sigma C ↔
    (Project.FirstOrderSemantics.reduct M).mem sigma H ∧ Same w D chain pi sigma

def Classes (w D chain H Q : M.Carrier .set) : Prop := ∀ C,
  (Project.FirstOrderSemantics.reduct M).mem C Q ↔ ∃ pi,
    (Project.FirstOrderSemantics.reduct M).mem pi H ∧ Class w D chain H pi C

def Projection (w D chain H pr : M.Carrier .set) : Prop := ∀ pi C,
  PureKuratowski.PairMember M pi C pr ↔ (Project.FirstOrderSemantics.reduct M).mem pi H ∧ Class w D chain H pi C

def agree {m : Nat} (A pi sigma : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (.mem (.bound 1) (.bound A.succ.succ)) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge pi.succ.succ 1 0)) (ProjectSyntax.encode id (Source.SetLanguage.edge sigma.succ.succ 1 0))))))

theorem agree_freeClosed {m : Nat} (A pi sigma : Fin m) : (agree A pi sigma).FreeClosed := by
  simp -implicitDefEqProofs [agree,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem agree_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (A pi sigma : Fin m) :
    Project.Formula.satisfies env (agree A pi sigma) ↔ Agree (env.bound A) (env.bound pi) (env.bound sigma) := by
  simp only [agree,Agree,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def same {m : Nat} (w D chain pi sigma : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (.mem (.bound 5) (.bound w.succ.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge chain.succ.succ.succ.succ.succ.succ 5 4)) (.conj (ConstructionComponentCarrier.code 4 3 2 1) (.conj (ProjectSyntax.encode id (ForcingSupportedNames.range D.succ.succ.succ.succ.succ.succ 3 0)) (agree 0 pi.succ.succ.succ.succ.succ.succ sigma.succ.succ.succ.succ.succ.succ)))))))))))

theorem same_freeClosed {m : Nat} (w D chain pi sigma : Fin m) : (same w D chain pi sigma).FreeClosed := by
  simp -implicitDefEqProofs [same,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,agree_freeClosed,ConstructionComponentCarrier.code_freeClosed]

theorem same_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D chain pi sigma : Fin m) :
    Project.Formula.satisfies env (same w D chain pi sigma) ↔ Same (env.bound w) (env.bound D) (env.bound chain) (env.bound pi) (env.bound sigma) := by
  simp only [same,Same,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionComponentCarrier.code_semantics hM,ForcingSupportedNames.range_semantics (M := M),agree_semantics hM]
  rfl

def carrier {m : Nat} (D I mul q root H : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound 0) (.bound H.succ)) (ConstructionCountableAlignments.stabilizes D.succ I.succ mul.succ q.succ root.succ 0)))

theorem carrier_freeClosed {m : Nat} (D I mul q root H : Fin m) : (carrier D I mul q root H).FreeClosed := by
  simp -implicitDefEqProofs [carrier,Definitional.Formula.FreeClosed,ConstructionCountableAlignments.stabilizes_freeClosed]

theorem carrier_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q root H : Fin m) :
    Project.Formula.satisfies env (carrier D I mul q root H) ↔ Carrier (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound root) (env.bound H) := by
  simp only [carrier,Carrier,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ConstructionCountableAlignments.stabilizes_semantics hM]
  rfl

def eqClass {m : Nat} (w D chain H pi C : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound 0) (.bound C.succ)) (.conj (.mem (.bound 0) (.bound H.succ)) (same w.succ D.succ chain.succ pi.succ 0))))

theorem eqClass_freeClosed {m : Nat} (w D chain H pi C : Fin m) : (eqClass w D chain H pi C).FreeClosed := by
  simp -implicitDefEqProofs [eqClass,Definitional.Formula.FreeClosed,same_freeClosed]

theorem eqClass_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D chain H pi C : Fin m) :
    Project.Formula.satisfies env (eqClass w D chain H pi C) ↔ Class (env.bound w) (env.bound D) (env.bound chain) (env.bound H) (env.bound pi) (env.bound C) := by
  simp only [eqClass,Class,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,same_semantics hM]
  rfl

def classes {m : Nat} (w D chain H Q : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound 0) (.bound Q.succ)) (.existsE (.conj (.mem (.bound 0) (.bound H.succ.succ)) (eqClass w.succ.succ D.succ.succ chain.succ.succ H.succ.succ 0 1)))))

theorem classes_freeClosed {m : Nat} (w D chain H Q : Fin m) : (classes w D chain H Q).FreeClosed := by
  simp -implicitDefEqProofs [classes,Definitional.Formula.FreeClosed,eqClass_freeClosed]

theorem classes_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D chain H Q : Fin m) :
    Project.Formula.satisfies env (classes w D chain H Q) ↔ Classes (env.bound w) (env.bound D) (env.bound chain) (env.bound H) (env.bound Q) := by
  simp only [classes,Classes,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,eqClass_semantics hM]
  rfl

def projection {m : Nat} (w D chain H pr : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge pr.succ.succ 1 0)) (.conj (.mem (.bound 1) (.bound H.succ.succ)) (eqClass w.succ.succ D.succ.succ chain.succ.succ H.succ.succ 1 0)))))

theorem projection_freeClosed {m : Nat} (w D chain H pr : Fin m) : (projection w D chain H pr).FreeClosed := by
  simp -implicitDefEqProofs [projection,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,eqClass_freeClosed]

theorem projection_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D chain H pr : Fin m) :
    Project.Formula.satisfies env (projection w D chain H pr) ↔ Projection (env.bound w) (env.bound D) (env.bound chain) (env.bound H) (env.bound pr) := by
  simp only [projection,Projection,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,eqClass_semantics hM]
  rfl

theorem exists_carrier (hM : FirstOrder.Theory.Models M nativeZF) (D I mul q root : M.Carrier .set) :
    ∃ H, Carrier D I mul q root H := by
  obtain ⟨G,hG⟩ := ForcingLabelPermutations.exists_carrier hM I
  let schema : Project.UnarySchema 5 := {
    body := ConstructionCountableAlignments.stabilizes 1 2 3 4 5 0
    freeClosed := ConstructionCountableAlignments.stabilizes_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 := {
    bound := Fin.cases D (Fin.cases I (Fin.cases mul (Fin.cases q (fun _ => root)))), free := fun _ => D }
  have he pi : schema.denote env pi ↔ ConstructionCountableAlignments.Stabilizes D I mul q root pi :=
    ConstructionCountableAlignments.stabilizes_semantics hM (env.push pi) 1 2 3 4 5 0
  obtain ⟨H,hH⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env G
  exact ⟨H,fun pi => ⟨fun hp => (he pi).mp ((hH pi).mp hp).2,
    fun hp => (hH pi).mpr ⟨(hG pi).mpr hp.1,(he pi).mpr hp⟩⟩⟩

theorem exists_class (hM : FirstOrder.Theory.Models M nativeZF) (w D chain H pi : M.Carrier .set) :
    ∃ C, Class w D chain H pi C := by
  let schema : Project.UnarySchema 4 := { body := same 1 2 3 4 0, freeClosed := same_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases chain (fun _ => pi))), free := fun _ => D }
  have he sigma : schema.denote env sigma ↔ Same w D chain pi sigma :=
    same_semantics hM (env.push sigma) 1 2 3 4 0
  obtain ⟨C,hC⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env H
  exact ⟨C,fun sigma => (hC sigma).trans (and_congr Iff.rfl (he sigma))⟩

theorem class_unique (hM : FirstOrder.Theory.Models M nativeZF) {w D chain H pi C E : M.Carrier .set}
    (hC : Class w D chain H pi C) (hE : Class w D chain H pi E) : C = E :=
  (ModelTransfer.extensionality hM).eq_of_same_members C E (fun sigma => (hC sigma).trans (hE sigma).symm)

theorem class_eq_of_same (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain H pi sigma C E : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hChain : Chain w D I mul q zero root vertices chain)
    (hC : Class w D chain H pi C) (hE : Class w D chain H sigma E)
    (hSame : Same w D chain pi sigma) : C = E := by
  apply (ModelTransfer.extensionality hM).eq_of_same_members C E
  intro tau
  rw [hC tau,hE tau]
  exact and_congr_right (fun _ => ⟨fun h => same_trans hM hw hChain (same_symm hSame) h,
    fun h => same_trans hM hw hChain hSame h⟩)

theorem class_eq_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain H pi sigma C E : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hChain : Chain w D I mul q zero root vertices chain)
    (hsigma : (Project.FirstOrderSemantics.reduct M).mem sigma H)
    (hC : Class w D chain H pi C) (hE : Class w D chain H sigma E) :
    C = E ↔ Same w D chain pi sigma := by
  constructor
  · rintro rfl
    exact ((hC sigma).mp ((hE sigma).mpr ⟨hsigma,same_refl hM hzw hChain⟩)).2
  · exact class_eq_of_same hM hw hChain hC hE

theorem exists_quotient (hM : FirstOrder.Theory.Models M nativeZF) (w D chain H : M.Carrier .set) :
    ∃ Q pr, MapsTo H Q pr ∧ Classes w D chain H Q ∧ Projection w D chain H pr := by
  let schema : Project.BinarySchema 4 := { body := eqClass 2 3 4 5 1 0, freeClosed := eqClass_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases chain (fun _ => H))), free := fun _ => D }
  have he pi C : schema.denote env pi C ↔ Class w D chain H pi C :=
    eqClass_semantics hM ((env.push pi).push C) 2 3 4 5 1 0
  have ht : ∀ pi, (Project.FirstOrderSemantics.reduct M).mem pi H → ∃ C, schema.denote env pi C := by
    intro pi _
    obtain ⟨C,hC⟩ := exists_class hM w D chain H pi
    exact ⟨C,(he pi C).mpr hC⟩
  have hu : ∀ pi C E, schema.denote env pi C → schema.denote env pi E → C = E :=
    fun pi C E hC hE => class_unique hM ((he pi C).mp hC) ((he pi E).mp hE)
  obtain ⟨Q,hQ⟩ := ZF.exists_functionalImage (ModelTransfer.project_models_iff.mp hM) schema env H ht hu
  obtain ⟨pr,hpr,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env ht (fun pi _ C E hC hE => hu pi C E hC hE)
    (fun pi C hp hC => (hQ C).mpr ⟨pi,hp,hC⟩)
  refine ⟨Q,pr,(ForcingSupportSize.native_mapsTo hM H Q pr).mpr hpr,?_,?_⟩
  · intro C
    exact (hQ C).trans ⟨fun ⟨pi,hp,hC⟩ => ⟨pi,hp,(he pi C).mp hC⟩,
      fun ⟨pi,hp,hC⟩ => ⟨pi,hp,(he pi C).mpr hC⟩⟩
  · exact fun pi C => (hEdge pi C).trans (and_congr Iff.rfl (he pi C))

/-- An actual alignment pair codes the whole coset of its permutation. -/
def CodeFor (w D I mul q root chain H p C : M.Carrier .set) : Prop :=
  ∃ pi, (Project.FirstOrderSemantics.reduct M).mem pi H ∧
    ConstructionCountableAlignments.Point D I mul q root chain pi p ∧ Class w D chain H pi C

def codeFor {m : Nat} (w D I mul q root chain H p C : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (.mem (.bound 0) (.bound H.succ))
    (.conj (ConstructionCountableAlignments.point D.succ I.succ mul.succ q.succ root.succ chain.succ 0 p.succ)
      (eqClass w.succ D.succ chain.succ H.succ 0 C.succ)))

theorem codeFor_freeClosed {m : Nat} (w D I mul q root chain H p C : Fin m) :
    (codeFor w D I mul q root chain H p C).FreeClosed := by
  simp -implicitDefEqProofs [codeFor,Definitional.Formula.FreeClosed,ConstructionCountableAlignments.point_freeClosed,eqClass_freeClosed]

theorem codeFor_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D I mul q root chain H p C : Fin m) :
    Project.Formula.satisfies env (codeFor w D I mul q root chain H p C) ↔
      CodeFor (env.bound w) (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound root) (env.bound chain) (env.bound H) (env.bound p) (env.bound C) := by
  simp only [codeFor,CodeFor,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ConstructionCountableAlignments.point_semantics hM,eqClass_semantics hM]
  rfl

theorem code_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain H p C E : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hChain : Chain w D I mul q zero root vertices chain) (hH : Carrier D I mul q root H)
    (hC : CodeFor w D I mul q root chain H p C) (hE : CodeFor w D I mul q root chain H p E) : C = E := by
  obtain ⟨pi,hpi,⟨i,x,hpx,ha⟩,hC⟩ := hC
  obtain ⟨sigma,hsigma,⟨j,y,hpy,hb⟩,hE⟩ := hE
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hpx hpy
  exact class_eq_of_same hM hw hChain hC hE
    (same_of_alignment hM hChain ((hH pi).mp hpi).1 ((hH sigma).mp hsigma).1 ha hb)

/-- The full quotient is the image of the actual subset of omega times
base consisting of alignment codes. Reuse the existing least-preimage bound. -/
theorem countable (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain H Q base : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hChain : Chain w D I mul q zero root vertices chain)
    (hH : Carrier D I mul q root H) (hQ : Classes w D chain H Q)
    (hb : Small base w) (hAligned : ConstructionCountableAlignments.Aligned w D I mul q root chain base) : Small Q w := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let P := KuratowskiZF.interpretation hM
  obtain ⟨pairs,hPairs⟩ := ZF.exists_cartesianProduct hZF P w base
  obtain ⟨id,hId⟩ := ZF.exists_identityBijection hZF P w
  have hwc := ExistingCardinalBounds.omega_cardinal_l P hZF hw
  have hInfinite : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal P w w := ⟨hwc,id,hId.1⟩
  have hPairsSmall := ExistingCardinalBounds.infinite_product_l P hZF hw hInfinite ⟨id,hId.1⟩
    ((ForcingSupportSize.native_small hM base w).mp hb) hPairs
  let schema : Project.BinarySchema 8 := { body := codeFor 2 3 4 5 6 7 8 9 1 0, freeClosed := codeFor_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 8 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases I (Fin.cases mul
      (Fin.cases q (Fin.cases root (Fin.cases chain (fun _ => H))))))), free := fun _ => D }
  have he p C : schema.denote env p C ↔ CodeFor w D I mul q root chain H p C :=
    codeFor_semantics hM ((env.push p).push C) 2 3 4 5 6 7 8 9 1 0
  let domain : Project.UnarySchema 8 := { body := .existsE schema.body, freeClosed := by simp -implicitDefEqProofs [schema,Definitional.Formula.FreeClosed,codeFor_freeClosed] }
  have hd p : domain.denote env p ↔ ∃ C, CodeFor w D I mul q root chain H p C := by
    change Project.Formula.satisfies (env.push p) (.existsE schema.body) ↔ _
    rw [Project.Formula.satisfies_exists_iff]
    exact exists_congr (fun C => he p C)
  obtain ⟨codes,hCodes⟩ := ZF.separation_exists_d hZF domain env pairs
  have hCodes' p : (Project.FirstOrderSemantics.reduct M).mem p codes ↔
      (Project.FirstOrderSemantics.reduct M).mem p pairs ∧ ∃ C, CodeFor w D I mul q root chain H p C :=
    (hCodes p).trans (and_congr Iff.rfl (hd p))
  obtain ⟨f,hf,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote hZF P schema env (source := codes) (target := Q)
    (by intro p hp; obtain ⟨C,hC⟩ := ((hCodes' p).mp hp).2; exact ⟨C,(he p C).mpr hC⟩)
    (fun p _ C E hC hE => code_unique hM hw hChain hH ((he p C).mp hC) ((he p E).mp hE))
    (by intro p C _ hC; obtain ⟨pi,hpi,_,hClass⟩ := (he p C).mp hC; exact (hQ C).mpr ⟨pi,hpi,hClass⟩)
  have hSmall := ForcingSupportSize.small_subset hM (fun p hp => ((hCodes' p).mp hp).1)
    ((ForcingSupportSize.native_small hM pairs w).mpr hPairsSmall)
  apply ConstructionProbeCardinality.indexed_quotient_bound hM hwc.1 hSmall
    ((ForcingSupportSize.native_mapsTo hM codes Q f).mpr hf)
  intro C hCQ
  obtain ⟨pi,hpi,hClass⟩ := (hQ C).mp hCQ
  obtain ⟨i,x,hi,hx,ha⟩ := hAligned pi ((hH pi).mp hpi)
  obtain ⟨p,hpx⟩ := KuratowskiZF.exists_code hM i x
  have hCode : CodeFor w D I mul q root chain H p C := ⟨pi,hpi,⟨i,x,hpx,ha⟩,hClass⟩
  have hp := (hCodes' p).mpr ⟨(hPairs p).mpr ⟨i,hi,x,hx,hpx⟩,C,hCode⟩
  exact ⟨p,hp,(hEdge p C).mpr ⟨hp,(he p C).mpr hCode⟩⟩

/-- The quotient projection identifies exactly original tail cosets. -/
def Exact (w D I chain pr : M.Carrier .set) : Prop := ∀ pi sigma C E inv diff,
  PureKuratowski.PairMember M pi C pr → PureKuratowski.PairMember M sigma E pr →
  InverseGraph pi inv → CompositionGraph I inv sigma diff →
    (C = E ↔ ForcingTailCovariance.TailFixes w D diff chain)

def Result (w D I mul q root chain H Q pr : M.Carrier .set) : Prop :=
  Carrier D I mul q root H ∧ MapsTo H Q pr ∧ Classes w D chain H Q ∧
    Projection w D chain H pr ∧ Small Q w ∧ Exact w D I chain pr

theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain base : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hChain : Chain w D I mul q zero root vertices chain)
    (hb : Small base w) (hAligned : ConstructionCountableAlignments.Aligned w D I mul q root chain base) :
    ∃ H Q pr, Result w D I mul q root chain H Q pr := by
  obtain ⟨H,hH⟩ := exists_carrier hM D I mul q root
  obtain ⟨Q,pr,hMap,hQ,hProjection⟩ := exists_quotient hM w D chain H
  refine ⟨H,Q,pr,hH,hMap,hQ,hProjection,countable hM hw hChain hH hQ hb hAligned,?_⟩
  intro pi sigma C E inv diff hp hs hi hc
  obtain ⟨hpi,hC⟩ := (hProjection pi C).mp hp
  obtain ⟨hsigma,hE⟩ := (hProjection sigma E).mp hs
  exact (class_eq_iff hM hw hzw hChain hsigma hC hE).trans
    (same_iff_tail hChain ((hH pi).mp hpi).1 ((hH sigma).mp hsigma).1 hi hc)

def exactFormula {m : Nat} (w D I chain pr : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge pr.succ.succ.succ.succ.succ.succ 5 3)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge pr.succ.succ.succ.succ.succ.succ 4 2)) (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.inverseGraph 5 1)) (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph I.succ.succ.succ.succ.succ.succ 1 4 0)) (.iff (Project.Formula.extensionalEq (.bound 3) (.bound 2)) (ForcingTailCovariance.tailFixes w.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ 0 chain.succ.succ.succ.succ.succ.succ))))))))))))

theorem exactFormula_freeClosed {m : Nat} (w D I chain pr : Fin m) : (exactFormula w D I chain pr).FreeClosed := by
  simp -implicitDefEqProofs [exactFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq,ForcingTailCovariance.tailFixes_freeClosed]

theorem exactFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D I chain pr : Fin m) :
    Project.Formula.satisfies env (exactFormula w D I chain pr) ↔ Exact (env.bound w) (env.bound D) (env.bound I) (env.bound chain) (env.bound pr) := by
  simp only [exactFormula,Exact,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingConditionGraphs.inverseGraph_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),ForcingTailCovariance.tailFixes_semantics hM]
  rfl

def resultFormula {m : Nat} (w D I mul q root chain H Q pr : Fin m) : Project.Formula 1 m :=
  (.conj (carrier D I mul q root H) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo pr H Q)) (.conj (classes w D chain H Q) (.conj (projection w D chain H pr) (.conj (ProjectSyntax.encode id (ForcingSupportSize.small Q w)) (exactFormula w D I chain pr))))))

theorem resultFormula_freeClosed {m : Nat} (w D I mul q root chain H Q pr : Fin m) : (resultFormula w D I mul q root chain H Q pr).FreeClosed := by
  simp -implicitDefEqProofs [resultFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,carrier_freeClosed,classes_freeClosed,projection_freeClosed,exactFormula_freeClosed]

theorem resultFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D I mul q root chain H Q pr : Fin m) :
    Project.Formula.satisfies env (resultFormula w D I mul q root chain H Q pr) ↔ Result (env.bound w) (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound root) (env.bound chain) (env.bound H) (env.bound Q) (env.bound pr) := by
  simp only [resultFormula,Result,Project.Formula.satisfies_conj_iff,carrier_semantics hM,classes_semantics hM,projection_semantics hM,exactFormula_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),ForcingSupportSize.small_semantics (M := M)]
  rfl

end PPAC.Migration.ConstructionGermCosets
