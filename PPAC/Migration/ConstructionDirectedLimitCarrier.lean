/- Pinned DirectLimits.ConservativeLimit.of:19 / of_map:29 / of_injective:62.
Construct the ACTUAL varying-carrier disjoint sum, common-future classes and
projection using existing coordinate_bound/Union/Cartesian/Separation,
functionalImage and native function constructors. Source-specific adaptation
of accepted MergerCopies proof pattern; NO generic quotient framework,
chosen representatives, injective-transition premise or omega restriction.
Consumer: SAME carrier's multiplication and conservative/weighted direct limit. -/
import PPAC.Migration.ConstructionDirectedSystem
import PPAC.Migration.ConstructionProbeHomEvaluation

namespace PPAC.Migration.ConstructionDirectedLimitCarrier
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionDirectedSystem
open ForcingSupportSize (MapsTo Injection)
open ForcingDiagramOrder (Product product product_semantics)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Representatives (J Domains C : M.Carrier .set) : Prop := ∀ p,
  (Project.FirstOrderSemantics.reduct M).mem p C ↔
    ∃ i x, At J Domains i x ∧ PureKuratowski.Code M p i x

def representatives {m : Nat} (J Domains C : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound C.succ)) (.existsE (.existsE
    (.conj (atStage J.succ.succ.succ Domains.succ.succ.succ 1 0)
      (PureKuratowskiProject.code (.bound 2) (.bound 1) (.bound 0))))))

theorem representatives_freeClosed {m : Nat} (J Domains C : Fin m) : (representatives J Domains C).FreeClosed := by
  simp -implicitDefEqProofs [representatives,Definitional.Formula.FreeClosed,atStage_freeClosed,PureKuratowskiProject.code]

theorem representatives_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains C : Fin m) :
    Project.Formula.satisfies env (representatives J Domains C) ↔
      Representatives (env.bound J) (env.bound Domains) (env.bound C) := by
  simp only [representatives,Representatives,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Term.eval_bound,atStage_semantics hM,KuratowskiZF.code_correct hM]
  rfl

theorem exists_representatives (hM : FirstOrder.Theory.Models M nativeZF) (J Domains : M.Carrier .set) :
    ∃ C, Representatives J Domains C := by
  obtain ⟨B,hB⟩ := ForcingMapConditions.coordinate_bound hM Domains
  obtain ⟨U,hU⟩ := KP.exists_union (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) B
  obtain ⟨prod,hprod⟩ := ZF.exists_cartesianProduct (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) J U
  let schema : Project.UnarySchema 2 := {
    body := .existsE (.existsE (.conj (atStage 3 4 1 0)
      (PureKuratowskiProject.code (.bound 2) (.bound 1) (.bound 0))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,atStage_freeClosed,PureKuratowskiProject.code] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases J (fun _ => Domains), free := fun _ => J }
  have he (p) : schema.denote env p ↔ ∃ i x, At J Domains i x ∧ PureKuratowski.Code M p i x := by
    simp only [Project.UnarySchema.denote,schema,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
      atStage_semantics hM,KuratowskiZF.code_correct hM,Project.Term.eval_bound]
    rfl
  obtain ⟨C,hC⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env prod
  refine ⟨C,fun p => ?_⟩
  constructor
  · exact fun hp => (he p).mp ((hC p).mp hp).2
  · intro hp
    have hpCopy := hp
    obtain ⟨i,x,⟨hi,D,hD,hx⟩,hcode⟩ := hpCopy
    have hxU := (hU x).mpr ⟨D,(hB i D hD).2,hx⟩
    exact (hC p).mpr ⟨(hprod p).mpr ⟨i,hi,x,hxU,hcode⟩,(he p).mpr hp⟩

def Related (J E Domains F p q : M.Carrier .set) : Prop := ∃ i x j y,
  PureKuratowski.Code M p i x ∧ PureKuratowski.Code M q j y ∧ Meets J E Domains F i x j y

theorem related_refl {J E Domains F C p : M.Carrier .set} (hC : Representatives J Domains C)
    (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p C) : Related J E Domains F p p := by
  obtain ⟨i,x,hx,hcode⟩ := (hC p).mp hp
  exact ⟨i,x,i,x,hcode,hcode,meets_refl hE hT hx⟩

theorem related_symm {J E Domains F p q : M.Carrier .set}
    (h : Related J E Domains F p q) : Related J E Domains F q p := by
  obtain ⟨i,x,j,y,hp,hq,hxy⟩ := h
  exact ⟨j,y,i,x,hq,hp,meets_symm hxy⟩

theorem related_trans {J E Domains F p q r : M.Carrier .set}
    (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hpq : Related J E Domains F p q) (hqr : Related J E Domains F q r) : Related J E Domains F p r := by
  obtain ⟨i,x,j,y,hp,hq,hxy⟩ := hpq
  obtain ⟨j',y',k,z,hq',hr,hyz⟩ := hqr
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq hq'
  exact ⟨i,x,k,z,hp,hr,meets_trans hE hT hxy hyz⟩

def related {m : Nat} (J E Domains F p q : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.existsE (.conj
    (PureKuratowskiProject.code (.bound p.succ.succ.succ.succ) (.bound 3) (.bound 2))
    (.conj (PureKuratowskiProject.code (.bound q.succ.succ.succ.succ) (.bound 1) (.bound 0))
      (meets J.succ.succ.succ.succ E.succ.succ.succ.succ Domains.succ.succ.succ.succ F.succ.succ.succ.succ 3 2 1 0))))))

theorem related_freeClosed {m : Nat} (J E Domains F p q : Fin m) : (related J E Domains F p q).FreeClosed := by
  simp -implicitDefEqProofs [related,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,meets_freeClosed]

theorem related_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Domains F p q : Fin m) :
    Project.Formula.satisfies env (related J E Domains F p q) ↔
      Related (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound p) (env.bound q) := by
  simp only [related,Related,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    KuratowskiZF.code_correct hM,Project.Term.eval_bound,meets_semantics hM]
  rfl

def Class (J E Domains F C p c : M.Carrier .set) : Prop := ∀ q,
  (Project.FirstOrderSemantics.reduct M).mem q c ↔
    (Project.FirstOrderSemantics.reduct M).mem q C ∧ Related J E Domains F p q

def eqClass {m : Nat} (J E Domains F C p c : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound c.succ))
    (.conj (.mem (.bound 0) (.bound C.succ)) (related J.succ E.succ Domains.succ F.succ p.succ 0)))

theorem eqClass_freeClosed {m : Nat} (J E Domains F C p c : Fin m) : (eqClass J E Domains F C p c).FreeClosed := by
  simp -implicitDefEqProofs [eqClass,Definitional.Formula.FreeClosed,related_freeClosed]

theorem eqClass_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Domains F C p c : Fin m) :
    Project.Formula.satisfies env (eqClass J E Domains F C p c) ↔
      Class (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound C) (env.bound p) (env.bound c) := by
  simp only [eqClass,Class,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,related_semantics hM]
  rfl

theorem exists_class (hM : FirstOrder.Theory.Models M nativeZF) (J E Domains F C p : M.Carrier .set) :
    ∃ c, Class J E Domains F C p c := by
  let schema : Project.UnarySchema 5 := { body := related 1 2 3 4 5 0, freeClosed := related_freeClosed _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 :=
    { bound := Fin.cases J (Fin.cases E (Fin.cases Domains (Fin.cases F (fun _ => p)))), free := fun _ => J }
  obtain ⟨c,hc⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env C
  exact ⟨c,fun q => (hc q).trans (and_congr_right fun _ => related_semantics hM (env.push q) 1 2 3 4 5 0)⟩

theorem class_unique (hM : FirstOrder.Theory.Models M nativeZF) {J E Domains F C p c d : M.Carrier .set}
    (hc : Class J E Domains F C p c) (hd : Class J E Domains F C p d) : c = d :=
  (ModelTransfer.extensionality hM).eq_of_same_members c d (fun q => (hc q).trans (hd q).symm)

theorem class_eq_iff (hM : FirstOrder.Theory.Models M nativeZF) {J E Domains F C p q c d : M.Carrier .set}
    (hC : Representatives J Domains C) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q C)
    (hc : Class J E Domains F C p c) (hd : Class J E Domains F C q d) :
    c = d ↔ Related J E Domains F p q := by
  constructor
  · intro he
    have hself := (hd q).mpr ⟨hq,related_refl hC hE hT hq⟩
    exact ((hc q).mp (he.symm ▸ hself)).2
  · intro hpq
    apply (ModelTransfer.extensionality hM).eq_of_same_members
    intro r
    rw [hc r,hd r]
    exact and_congr_right fun _ => ⟨fun h => related_trans hE hT (related_symm hpq) h,
      fun h => related_trans hE hT hpq h⟩

def Carrier (J E Domains F C L : M.Carrier .set) : Prop := ∀ c,
  (Project.FirstOrderSemantics.reduct M).mem c L ↔
    ∃ p, (Project.FirstOrderSemantics.reduct M).mem p C ∧ Class J E Domains F C p c

theorem exists_carrier (hM : FirstOrder.Theory.Models M nativeZF) (J E Domains F C : M.Carrier .set) :
    ∃ L, Carrier J E Domains F C L := by
  let schema : Project.BinarySchema 5 := { body := eqClass 2 3 4 5 6 1 0, freeClosed := eqClass_freeClosed _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 :=
    { bound := Fin.cases J (Fin.cases E (Fin.cases Domains (Fin.cases F (fun _ => C)))), free := fun _ => J }
  have he : ∀ p c, schema.denote env p c ↔ Class J E Domains F C p c :=
    fun p c => eqClass_semantics hM ((env.push p).push c) 2 3 4 5 6 1 0
  obtain ⟨L,hL⟩ := ZF.exists_functionalImage (ModelTransfer.project_models_iff.mp hM) schema env C (by
    intro p _
    obtain ⟨c,hc⟩ := exists_class hM J E Domains F C p
    exact ⟨c,(he p c).mpr hc⟩) (by
    intro p c d hc hd
    exact class_unique hM ((he p c).mp hc) ((he p d).mp hd))
  exact ⟨L,fun c => (hL c).trans ⟨fun ⟨p,hp,hc⟩ => ⟨p,hp,(he p c).mp hc⟩,
    fun ⟨p,hp,hc⟩ => ⟨p,hp,(he p c).mpr hc⟩⟩⟩

def Projection (J E Domains F C projection : M.Carrier .set) : Prop := ∀ p c,
  PureKuratowski.PairMember M p c projection ↔
    (Project.FirstOrderSemantics.reduct M).mem p C ∧ Class J E Domains F C p c

theorem exists_projection (hM : FirstOrder.Theory.Models M nativeZF) {J E Domains F C L : M.Carrier .set}
    (hL : Carrier J E Domains F C L) : ∃ projection, MapsTo C L projection ∧ Projection J E Domains F C projection := by
  let schema : Project.BinarySchema 5 := { body := eqClass 2 3 4 5 6 1 0, freeClosed := eqClass_freeClosed _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 :=
    { bound := Fin.cases J (Fin.cases E (Fin.cases Domains (Fin.cases F (fun _ => C)))), free := fun _ => J }
  have he : ∀ p c, schema.denote env p c ↔ Class J E Domains F C p c :=
    fun p c => eqClass_semantics hM ((env.push p).push c) 2 3 4 5 6 1 0
  obtain ⟨projection,hp,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := C) (target := L) (by
      intro p _
      obtain ⟨c,hc⟩ := exists_class hM J E Domains F C p
      exact ⟨c,(he p c).mpr hc⟩) (by
      intro p _ c d hc hd
      exact class_unique hM ((he p c).mp hc) ((he p d).mp hd)) (by
      intro p c hp hc
      exact (hL c).mpr ⟨p,hp,(he p c).mp hc⟩)
  exact ⟨projection,(ForcingSupportSize.native_mapsTo hM C L projection).mpr hp,
    fun p c => (hgraph p c).trans (and_congr_right fun _ => he p c)⟩

def EqualityLaw (J E Domains F projection : M.Carrier .set) : Prop := ∀ p q c d,
  PureKuratowski.PairMember M p c projection → PureKuratowski.PairMember M q d projection →
    (c = d ↔ Related J E Domains F p q)

theorem equality_law (hM : FirstOrder.Theory.Models M nativeZF) {J E Domains F C projection : M.Carrier .set}
    (hC : Representatives J Domains C) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hp : Projection J E Domains F C projection) : EqualityLaw J E Domains F projection := by
  intro p q c d hpc hqd
  obtain ⟨_,hc⟩ := (hp p c).mp hpc
  obtain ⟨hqC,hd⟩ := (hp q d).mp hqd
  exact class_eq_iff hM hC hE hT hqC hc hd

theorem related_codes_iff {J E Domains F p q i x j y : M.Carrier .set}
    (hp : PureKuratowski.Code M p i x) (hq : PureKuratowski.Code M q j y) :
    Related J E Domains F p q ↔ Meets J E Domains F i x j y := by
  constructor
  · rintro ⟨i',x',j',y',hp',hq',h⟩
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hq hq'
    exact h
  · exact fun h => ⟨i,x,j,y,hp,hq,h⟩

theorem projected_eq_iff {J E Domains F projection i x j y c d : M.Carrier .set}
    (hE : EqualityLaw J E Domains F projection)
    (hc : ForcingDiagramOrder.Product projection i x c) (hd : ForcingDiagramOrder.Product projection j y d) :
    c = d ↔ Meets J E Domains F i x j y := by
  obtain ⟨p,hp,hpc⟩ := hc
  obtain ⟨q,hq,hqd⟩ := hd
  exact (hE p q c d hpc hqd).trans (related_codes_iff hp hq)

theorem projection_onto {J E Domains F C L projection : M.Carrier .set}
    (hL : Carrier J E Domains F C L) (hp : Projection J E Domains F C projection)
    {c : M.Carrier .set} (hc : (Project.FirstOrderSemantics.reduct M).mem c L) :
    ∃ p, (Project.FirstOrderSemantics.reduct M).mem p C ∧ PureKuratowski.PairMember M p c projection := by
  obtain ⟨p,hpC,hclass⟩ := (hL c).mp hc
  exact ⟨p,hpC,(hp p c).mpr ⟨hpC,hclass⟩⟩

theorem projected_indices {J Domains C L projection i x c : M.Carrier .set}
    (hC : Representatives J Domains C) (hp : MapsTo C L projection) (hc : Product projection i x c) :
    At J Domains i x := by
  obtain ⟨p,hcode,hpc⟩ := hc
  obtain ⟨i',x',hx,hcode'⟩ := (hC p).mp (ForcingConditionGraphs.function_input hp.1 hpc)
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
  exact hx

theorem projected_total (hM : FirstOrder.Theory.Models M nativeZF) {J Domains C L projection i x : M.Carrier .set}
    (hC : Representatives J Domains C) (hp : MapsTo C L projection) (hx : At J Domains i x) :
    ∃ c, (Project.FirstOrderSemantics.reduct M).mem c L ∧ Product projection i x c := by
  obtain ⟨p,hcode⟩ := KuratowskiZF.exists_code hM i x
  obtain ⟨c,hpc,_⟩ := hp.1.2 p ((hC p).mpr ⟨i,x,hx,hcode⟩)
  exact ⟨c,hp.2 p c hpc,p,hcode,hpc⟩

theorem representative {J E Domains F C L projection c : M.Carrier .set}
    (hC : Representatives J Domains C) (hL : Carrier J E Domains F C L)
    (hp : Projection J E Domains F C projection) (hc : (Project.FirstOrderSemantics.reduct M).mem c L) :
    ∃ i x, At J Domains i x ∧ Product projection i x c := by
  obtain ⟨p,hpC,hpc⟩ := projection_onto hL hp hc
  obtain ⟨i,x,hx,hcode⟩ := (hC p).mp hpC
  exact ⟨i,x,hx,p,hcode,hpc⟩

/-- Source of_map, with the SAME actually produced quotient classes. -/
theorem of_map {J E Domains F projection i j x y a b : M.Carrier .set}
    (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hEq : EqualityLaw J E Domains F projection)
    (hij : PureKuratowski.PairMember M i j E) (hxy : Transition J Domains F i j x y)
    (ha : Product projection i x a) (hb : Product projection j y b) : a = b :=
  (projected_eq_iff hEq ha hb).mpr (transition_meets hE hT hij hxy)

/-- Source of_injective, derived exactly from the actual transition injections. -/
theorem of_injective {J E Domains F C L projection i x y c : M.Carrier .set}
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hI : InjectiveTransitions J E Domains F) (hEq : EqualityLaw J E Domains F projection)
    (hx : Product projection i x c) (hy : Product projection i y c) : x = y :=
  (meets_same_iff hE hT hI (projected_indices hC hp hx)).mp ((projected_eq_iff hEq hx hy).mp rfl)

/-- Move an ACTUAL representative to a later stage, retaining its SAME class. -/
theorem projected_later (hM : FirstOrder.Theory.Models M nativeZF)
    {J E Domains F C L projection i j x c : M.Carrier .set}
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hEq : EqualityLaw J E Domains F projection)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j J)
    (hij : PureKuratowski.PairMember M i j E) (hx : Product projection i x c) :
    ∃ y, At J Domains j y ∧ Transition J Domains F i j x y ∧ Product projection j y c := by
  obtain ⟨y,hxy⟩ := hT.1 i j x (projected_indices hC hp hx) hj hij
  obtain ⟨d,_,hyd⟩ := projected_total hM hC hp hxy.2.1
  have he := of_map hE hT hEq hij hxy hx hyd
  exact ⟨y,hxy.2.1,hxy,he.symm ▸ hyd⟩

/-- Source DirectLimit.induction2/common-stage representation, constructed. -/
theorem common_stage_pair (hM : FirstOrder.Theory.Models M nativeZF)
    {J E Domains F C L projection a b : M.Carrier .set}
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a L) (hb : (Project.FirstOrderSemantics.reduct M).mem b L) :
    ∃ k x y, At J Domains k x ∧ At J Domains k y ∧ Product projection k x a ∧ Product projection k y b := by
  obtain ⟨i,x,hx,hxa⟩ := representative hC hL hP ha
  obtain ⟨j,y,hy,hyb⟩ := representative hC hL hP hb
  obtain ⟨k,hk,hik,hjk⟩ := hE.2.2 i j hx.1 hy.1
  obtain ⟨x',hx',_,hxa'⟩ := projected_later hM hC hp hE hT hEq hk hik hxa
  obtain ⟨y',hy',_,hyb'⟩ := projected_later hM hC hp hE hT hEq hk hjk hyb
  exact ⟨k,x',y',hx',hy',hxa',hyb'⟩

/-- Source DirectLimit.induction3 used by cancellation and associativity. -/
theorem common_stage_three (hM : FirstOrder.Theory.Models M nativeZF)
    {J E Domains F C L projection a b c : M.Carrier .set}
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hL : Carrier J E Domains F C L) (hP : Projection J E Domains F C projection)
    (hEq : EqualityLaw J E Domains F projection)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a L) (hb : (Project.FirstOrderSemantics.reduct M).mem b L)
    (hc : (Project.FirstOrderSemantics.reduct M).mem c L) :
    ∃ k x y z, At J Domains k x ∧ At J Domains k y ∧ At J Domains k z ∧
      Product projection k x a ∧ Product projection k y b ∧ Product projection k z c := by
  obtain ⟨i,x,y,hx,hy,hxa,hyb⟩ := common_stage_pair hM hC hp hE hT hL hP hEq ha hb
  obtain ⟨j,z,hz,hzc⟩ := representative hC hL hP hc
  obtain ⟨k,hk,hik,hjk⟩ := hE.2.2 i j hx.1 hz.1
  obtain ⟨x',hx',_,hxa'⟩ := projected_later hM hC hp hE hT hEq hk hik hxa
  obtain ⟨y',hy',_,hyb'⟩ := projected_later hM hC hp hE hT hEq hk hik hyb
  obtain ⟨z',hz',_,hzc'⟩ := projected_later hM hC hp hE hT hEq hk hjk hzc
  exact ⟨k,x',y',z',hx',hy',hz',hxa',hyb',hzc'⟩

theorem exists_stage_map (hM : FirstOrder.Theory.Models M nativeZF)
    {J E Domains F C L projection i D : M.Carrier .set}
    (hC : Representatives J Domains C) (hp : MapsTo C L projection)
    (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hEq : EqualityLaw J E Domains F projection)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i J) (hD : PureKuratowski.PairMember M i D Domains) :
    ∃ f, MapsTo D L f ∧ (∀ x z, PureKuratowski.PairMember M x z f ↔
      (Project.FirstOrderSemantics.reduct M).mem x D ∧ Product projection i x z) ∧
      (InjectiveTransitions J E Domains F → Injection D L f) := by
  let schema : Project.BinarySchema 2 := {
    body := ProjectSyntax.encode id (product 2 3 1 0)
    freeClosed := ProjectSyntax.freeClosed id _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases projection (fun _ => i), free := fun _ => projection }
  have he (x z) : schema.denote env x z ↔ Product projection i x z := by
    simp only [Project.BinarySchema.denote,schema,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
      product_semantics (M := M)]
    rfl
  obtain ⟨f,hf,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := D) (target := L) (by
      intro x hx
      obtain ⟨z,_,hz⟩ := projected_total hM hC hp ⟨hi,D,hD,hx⟩
      exact ⟨z,(he x z).mpr hz⟩) (by
      intro x _ y z hy hz
      exact ConstructionProbeHomEvaluation.product_unique hM hp ((he x y).mp hy) ((he x z).mp hz)) (by
      intro x z _ hz
      obtain ⟨p,_,hpz⟩ := (he x z).mp hz
      exact hp.2 p z hpz)
  have hfMaps := (ForcingSupportSize.native_mapsTo hM D L f).mpr hf
  have hGraph' : ∀ x z, PureKuratowski.PairMember M x z f ↔
      (Project.FirstOrderSemantics.reduct M).mem x D ∧ Product projection i x z :=
    fun x z => (hGraph x z).trans (and_congr_right fun _ => he x z)
  refine ⟨f,hfMaps,hGraph',fun hI => ⟨hfMaps,?_⟩⟩
  intro x y z hx hy
  exact of_injective hC hp hE hT hI hEq ((hGraph' x z).mp hx).2 ((hGraph' y z).mp hy).2

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    (J E Domains F : M.Carrier .set) (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F) :
    ∃ C L projection, Representatives J Domains C ∧ MapsTo C L projection ∧ Carrier J E Domains F C L ∧
      Projection J E Domains F C projection ∧ EqualityLaw J E Domains F projection ∧
      (∀ i x, At J Domains i x → ∃ c, (Project.FirstOrderSemantics.reduct M).mem c L ∧ Product projection i x c) ∧
      (∀ c, (Project.FirstOrderSemantics.reduct M).mem c L → ∃ i x, At J Domains i x ∧ Product projection i x c) ∧
      (∀ i j x y a b, PureKuratowski.PairMember M i j E → Transition J Domains F i j x y →
        Product projection i x a → Product projection j y b → a = b) ∧
      (InjectiveTransitions J E Domains F → ∀ i x y c, Product projection i x c → Product projection i y c → x = y) ∧
      (∀ a b, (Project.FirstOrderSemantics.reduct M).mem a L → (Project.FirstOrderSemantics.reduct M).mem b L →
        ∃ k x y, At J Domains k x ∧ At J Domains k y ∧ Product projection k x a ∧ Product projection k y b) ∧
      (∀ a b c, (Project.FirstOrderSemantics.reduct M).mem a L → (Project.FirstOrderSemantics.reduct M).mem b L →
        (Project.FirstOrderSemantics.reduct M).mem c L → ∃ k x y z, At J Domains k x ∧ At J Domains k y ∧ At J Domains k z ∧
          Product projection k x a ∧ Product projection k y b ∧ Product projection k z c) ∧
      ∀ i D, (Project.FirstOrderSemantics.reduct M).mem i J → PureKuratowski.PairMember M i D Domains →
        ∃ f, MapsTo D L f ∧ (∀ x z, PureKuratowski.PairMember M x z f ↔
          (Project.FirstOrderSemantics.reduct M).mem x D ∧ Product projection i x z) ∧
          (InjectiveTransitions J E Domains F → Injection D L f) := by
  obtain ⟨C,hC⟩ := exists_representatives hM J Domains
  obtain ⟨L,hL⟩ := exists_carrier hM J E Domains F C
  obtain ⟨projection,hp,hProjection⟩ := exists_projection hM hL
  have hEq := equality_law hM hC hE hT hProjection
  exact ⟨C,L,projection,hC,hp,hL,hProjection,hEq,
    fun _ _ hx => projected_total hM hC hp hx,
    fun _ hc => representative hC hL hProjection hc,
    fun _ _ _ _ _ _ hij hxy ha hb => of_map hE hT hEq hij hxy ha hb,
    fun hI _ _ _ _ hx hy => of_injective hC hp hE hT hI hEq hx hy,
    fun _ _ ha hb => common_stage_pair hM hC hp hE hT hL hProjection hEq ha hb,
    fun _ _ _ ha hb hc => common_stage_three hM hC hp hE hT hL hProjection hEq ha hb hc,
    fun _ _ hi hD => exists_stage_map hM hC hp hE hT hEq hi hD⟩

def carrier {m : Nat} (J E Domains F C L : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound 0) (.bound L.succ)) (.existsE (.conj (.mem (.bound 0) (.bound C.succ.succ))
    (eqClass J.succ.succ E.succ.succ Domains.succ.succ F.succ.succ C.succ.succ 0 1)))))

theorem carrier_freeClosed {m : Nat} (J E Domains F C L : Fin m) : (carrier J E Domains F C L).FreeClosed := by
  simp -implicitDefEqProofs [carrier,Definitional.Formula.FreeClosed,eqClass_freeClosed]

theorem carrier_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Domains F C L : Fin m) :
    Project.Formula.satisfies env (carrier J E Domains F C L) ↔
      Carrier (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound C) (env.bound L) := by
  simp only [carrier, Carrier, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_iff_iff,
    Project.Term.eval_bound, Project.Formula.satisfies_exists_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, eqClass_semantics hM]
  rfl

def projectionGraph {m : Nat} (J E Domains F C projection : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge projection.succ.succ 1 0)) (.conj
    (.mem (.bound 1) (.bound C.succ.succ)) (eqClass J.succ.succ E.succ.succ Domains.succ.succ F.succ.succ
    C.succ.succ 1 0)))))

theorem projectionGraph_freeClosed {m : Nat} (J E Domains F C projection : Fin m) : (projectionGraph J E Domains F C projection).FreeClosed := by
  simp -implicitDefEqProofs [projectionGraph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,eqClass_freeClosed]

theorem projectionGraph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Domains F C projection : Fin m) :
    Project.Formula.satisfies env (projectionGraph J E Domains F C projection) ↔
      Projection (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound C) (env.bound projection) := by
  simp only [projectionGraph, Projection, Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff, Project.Term.eval_bound, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff, GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge, eqClass_semantics hM]
  rfl

def equalityLaw {m : Nat} (J E Domains F projection : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    projection.succ.succ.succ.succ 3 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
    projection.succ.succ.succ.succ 2 0)) (.iff (Project.Formula.extensionalEq (.bound 1) (.bound 0)) (related J.succ.succ.succ.succ
    E.succ.succ.succ.succ Domains.succ.succ.succ.succ F.succ.succ.succ.succ 3 2))))))))

theorem equalityLaw_freeClosed {m : Nat} (J E Domains F projection : Fin m) : (equalityLaw J E Domains F projection).FreeClosed := by
  simp -implicitDefEqProofs [equalityLaw,Project.Formula.extensionalEq,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,related_freeClosed]

theorem equalityLaw_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Domains F projection : Fin m) :
    Project.Formula.satisfies env (equalityLaw J E Domains F projection) ↔
      EqualityLaw (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound projection) := by
  simp only [equalityLaw, EqualityLaw, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_iff_iff,
    Project.Term.eval_bound, Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_extensionalEq_iff_eq
    (ModelTransfer.extensionality hM), GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge, related_semantics hM]
  rfl

end PPAC.Migration.ConstructionDirectedLimitCarrier
