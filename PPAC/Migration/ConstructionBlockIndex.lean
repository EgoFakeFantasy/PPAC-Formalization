/- Pinned BlockTowers.BlockIndex.Interior/Index: the exact dependent sum
of the fixed actual inner ordinals, ordered outer-first, with a final top.
Use native sets, relation construction and internal least elements, never
host WellFoundedLT. The existing WithTop order constructor is reused. -/
import PPAC.Migration.ConstructionBlockTraces

namespace PPAC.Migration.ConstructionBlockIndex
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingConditionGraphs (FunctionOn function_input function_unique)
open ConstructionTowerHistory (Row Field Chart)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Fibers (kappa Indices : M.Carrier .set) : Prop :=
  FunctionOn kappa Indices ∧ ∀ i J, PureKuratowski.PairMember M i J Indices →
    (Project.FirstOrderSemantics.reduct M).IsOrdinal J

def Point (kappa Indices p : M.Carrier .set) : Prop :=
  ∃ i J j, (Project.FirstOrderSemantics.reduct M).mem i kappa ∧
    PureKuratowski.PairMember M i J Indices ∧ (Project.FirstOrderSemantics.reduct M).mem j J ∧
    PureKuratowski.Code M p i j

def Carrier (kappa Indices A : M.Carrier .set) : Prop :=
  ∀ p, (Project.FirstOrderSemantics.reduct M).mem p A ↔ Point kappa Indices p

def Lex (p q : M.Carrier .set) : Prop :=
  ∃ i j k l, PureKuratowski.Code M p i j ∧ PureKuratowski.Code M q k l ∧
    ((Project.FirstOrderSemantics.reduct M).mem i k ∨ i = k ∧ (Project.FirstOrderSemantics.reduct M).mem j l)

def Hit (X i j : M.Carrier .set) : Prop :=
  ∃ p, (Project.FirstOrderSemantics.reduct M).mem p X ∧ PureKuratowski.Code M p i j

def Order (A r : M.Carrier .set) : Prop :=
  ∀ p q, PureKuratowski.PairMember M p q r ↔
    (Project.FirstOrderSemantics.reduct M).mem p A ∧
    (Project.FirstOrderSemantics.reduct M).mem q A ∧ Lex p q

theorem lex_pair {p q i j k l : M.Carrier .set}
    (hp : PureKuratowski.Code M p i j) (hq : PureKuratowski.Code M q k l) :
    Lex p q ↔ (Project.FirstOrderSemantics.reduct M).mem i k ∨
      i = k ∧ (Project.FirstOrderSemantics.reduct M).mem j l := by
  constructor
  · rintro ⟨i',j',k',l',hp',hq',h⟩
    obtain ⟨ei,ej⟩ := PureKuratowski.code_injective hp' hp
    obtain ⟨ek,el⟩ := PureKuratowski.code_injective hq' hq
    subst i' j' k' l'
    exact h
  · exact fun h => ⟨i,j,k,l,hp,hq,h⟩

def point {m : Nat} (kappa Indices p : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.conj (.mem (.bound 2) (.bound kappa.succ.succ.succ)) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge Indices.succ.succ.succ 2 1)) (.conj (.mem (.bound 0)
  (.bound 1)) (PureKuratowskiProject.code (.bound p.succ.succ.succ) (.bound 2) (.bound 0))))))))

theorem point_freeClosed {m : Nat} (kappa Indices p : Fin m) :
    (point kappa Indices p).FreeClosed := by
  simp -implicitDefEqProofs [point,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,PureKuratowskiProject.code]

theorem point_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (kappa Indices p : Fin m) :
    Project.Formula.satisfies env (point kappa Indices p) ↔
      Point (env.bound kappa) (env.bound Indices) (env.bound p) := by
  simp only [point,Point,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,KuratowskiZF.code_correct hM]
  rfl

def lex {m : Nat} (p q : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.conj (PureKuratowskiProject.code (.bound p.succ.succ.succ.succ)
  (.bound 3) (.bound 2)) (.conj (PureKuratowskiProject.code (.bound q.succ.succ.succ.succ) (.bound 1) (.bound
  0)) (.disj (.mem (.bound 3) (.bound 1)) (.conj (Project.Formula.extensionalEq (.bound 3) (.bound 1)) (.mem
  (.bound 2) (.bound 0))))))))))

theorem lex_freeClosed {m : Nat} (p q : Fin m) :
    (lex p q).FreeClosed := by
  simp -implicitDefEqProofs [lex,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,Project.Formula.extensionalEq]

theorem lex_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (p q : Fin m) :
    Project.Formula.satisfies env (lex p q) ↔
      Lex (env.bound p) (env.bound q) := by
  simp only [lex,Lex,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,KuratowskiZF.code_correct hM,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl

def hit {m : Nat} (X i j : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (.mem (.bound 0) (.bound X.succ)) (PureKuratowskiProject.code (.bound 0) (.bound i.succ)
  (.bound j.succ))))

theorem hit_freeClosed {m : Nat} (X i j : Fin m) :
    (hit X i j).FreeClosed := by
  simp -implicitDefEqProofs [hit,Definitional.Formula.FreeClosed,PureKuratowskiProject.code]

theorem hit_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (X i j : Fin m) :
    Project.Formula.satisfies env (hit X i j) ↔
      Hit (env.bound X) (env.bound i) (env.bound j) := by
  simp only [hit,Hit,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,KuratowskiZF.code_correct hM]
  rfl

theorem exists_carrier (hM : FirstOrder.Theory.Models M nativeZF)
    {kappa Indices : M.Carrier .set} (hI : FunctionOn kappa Indices) :
    ∃ A, Carrier kappa Indices A := by
  let N := Project.FirstOrderSemantics.reduct M
  let pair := KuratowskiZF.interpretation hM
  have hZF := ModelTransfer.project_models_iff.mp hM
  have hFn : N.IsSetFunction pair Indices := by
    refine ⟨?_,fun _ _ _ h h' => function_unique hI h h'⟩
    intro p hp
    obtain ⟨i,J,_,hc⟩ := hI.1 p hp
    exact ⟨i,J,hc⟩
  have hDom : N.IsDomainOf pair kappa Indices := by
    intro i
    exact ⟨fun hi => by obtain ⟨J,hJ,_⟩ := hI.2 i hi; exact ⟨J,hJ⟩,
      fun ⟨J,hJ⟩ => function_input hI hJ⟩
  obtain ⟨range,hRange⟩ := ZF.exists_range_of_setFunction hZF pair hFn hDom
  obtain ⟨U,hU⟩ := KP.exists_union (ZF.modelsKP hZF) range
  obtain ⟨B,hB⟩ := ZF.exists_cartesianProduct hZF pair kappa U
  let schema : Project.UnarySchema 2 := {
    body := point 1 2 0
    freeClosed := point_freeClosed .. }
  let env : SetTheory.Env N 2 := {bound := Fin.cases kappa (fun _ => Indices),free := fun _ => kappa}
  have he p : schema.denote env p ↔ Point kappa Indices p := point_semantics hM (env.push p) 1 2 0
  have hb p (hp : Point kappa Indices p) : N.mem p B := by
    obtain ⟨i,J,j,hi,hJ,hj,hcode⟩ := hp
    exact (hB p).mpr ⟨i,hi,j,(hU j).mpr ⟨J,(hRange J).mpr ⟨i,hJ⟩,hj⟩,hcode⟩
  obtain ⟨A,hA⟩ := ZF.separation_exists_d hZF schema env B
  exact ⟨A,fun p => ⟨fun hp => (he p).mp ((hA p).mp hp).2,
    fun hp => (hA p).mpr ⟨hb p hp,(he p).mpr hp⟩⟩⟩

theorem exists_order (hM : FirstOrder.Theory.Models M nativeZF)
    {kappa Indices A : M.Carrier .set}
    (hk : (Project.FirstOrderSemantics.reduct M).IsOrdinal kappa)
    (hI : Fibers kappa Indices) (hA : Carrier kappa Indices A) :
    ∃ r, (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) r A ∧
      Order A r := by
  let N := Project.FirstOrderSemantics.reduct M
  have hZF := ModelTransfer.project_models_iff.mp hM
  let schema : Project.BinarySchema 0 := {body := lex 1 0,freeClosed := lex_freeClosed ..}
  let env : SetTheory.Env N 0 := {bound := Fin.elim0,free := fun _ => A}
  have he p q : schema.denote env p q ↔ Lex p q := lex_semantics hM ((env.push p).push q) 1 0
  obtain ⟨r,hRel,hGraph⟩ := ZF.exists_setRelationOn_of_denote hZF (KuratowskiZF.interpretation hM) schema env A
  have rel : Order A r := fun p q =>
    (hGraph p q).trans (and_congr_right fun _ => and_congr_right fun _ => he p q)
  refine ⟨r,⟨⟨hRel.1,⟨⟨?_,?_⟩,?_⟩⟩,?_⟩,rel⟩
  · intro p hp hpp
    obtain ⟨i,J,j,hi,hJ,hj,hpcode⟩ := (hA p).mp hp
    rcases (lex_pair hpcode hpcode).mp ((rel p p).mp hpp).2.2 with h | ⟨_,h⟩
    · exact hk.wellOrder.linear.irrefl i hi h
    · exact (hI.2 i J hJ).wellOrder.linear.irrefl j hj h
  · intro p hp q hq t ht hpq hqt
    obtain ⟨i,J,j,hi,hJ,hj,hpc⟩ := (hA p).mp hp
    obtain ⟨k,K,l,hk',hK,hl,hqc⟩ := (hA q).mp hq
    obtain ⟨a,B,b,ha,hB,hb,htc⟩ := (hA t).mp ht
    have h1 := (lex_pair hpc hqc).mp ((rel p q).mp hpq).2.2
    have h2 := (lex_pair hqc htc).mp ((rel q t).mp hqt).2.2
    apply (rel p t).mpr
    refine ⟨hp,ht,(lex_pair hpc htc).mpr ?_⟩
    rcases h1 with hik | ⟨eik,hjl⟩
    · rcases h2 with hka | ⟨eka,_⟩
      · exact Or.inl (hk.wellOrder.linear.trans i hi k hk' a ha hik hka)
      · exact Or.inl (eka ▸ hik)
    · subst k
      rcases h2 with hia | ⟨eia,hlb⟩
      · exact Or.inl hia
      · subst a
        have eK := function_unique hI.1 hK hJ
        have eB := function_unique hI.1 hB hJ
        subst K B
        exact Or.inr ⟨rfl,(hI.2 i J hJ).wellOrder.linear.trans j hj l hl b hb hjl hlb⟩
  · intro p hp q hq
    obtain ⟨i,J,j,hi,hJ,hj,hpc⟩ := (hA p).mp hp
    obtain ⟨k,K,l,hk',hK,hl,hqc⟩ := (hA q).mp hq
    rcases hk.wellOrder.linear.compare i hi k hk' with eq | hik | hki
    · have eik := (ModelTransfer.extensionality hM).eq_of_same_members i k eq
      subst k
      have eK := function_unique hI.1 hK hJ
      subst K
      rcases (hI.2 i J hJ).wellOrder.linear.compare j hj l hl with eq | hjl | hlj
      · have ejl := (ModelTransfer.extensionality hM).eq_of_same_members j l eq
        subst l
        have epq := KuratowskiZF.code_unique hM hpc hqc
        subst q
        exact Or.inl (fun _ => Iff.rfl)
      · exact Or.inr (Or.inl ((rel p q).mpr ⟨hp,hq,(lex_pair hpc hqc).mpr (Or.inr ⟨rfl,hjl⟩)⟩))
      · exact Or.inr (Or.inr ((rel q p).mpr ⟨hq,hp,(lex_pair hqc hpc).mpr (Or.inr ⟨rfl,hlj⟩)⟩))
    · exact Or.inr (Or.inl ((rel p q).mpr ⟨hp,hq,(lex_pair hpc hqc).mpr (Or.inl hik)⟩))
    · exact Or.inr (Or.inr ((rel q p).mpr ⟨hq,hp,(lex_pair hqc hpc).mpr (Or.inl hki)⟩))
  · intro X hXA hXne
    let outer : Project.UnarySchema 1 := {
      body := .existsE (hit 2 1 0)
      freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,hit_freeClosed] }
    let rho : SetTheory.Env N 1 := {bound := fun _ => X,free := fun _ => X}
    have ho i : outer.denote rho i ↔ ∃ j, Hit X i j := by
      simp only [Project.UnarySchema.denote,outer,Project.Formula.satisfies_exists_iff,hit_semantics hM]
      rfl
    obtain ⟨B,hB⟩ := ZF.separation_exists_d hZF outer rho kappa
    have hb i : N.mem i B ↔ N.mem i kappa ∧ ∃ j, Hit X i j := (hB i).trans (and_congr_right fun _ => ho i)
    have hBne : ∃ i, N.mem i B := by
      obtain ⟨p,hp⟩ := hXne
      obtain ⟨i,J,j,hi,_,_,hpc⟩ := (hA p).mp (hXA p hp)
      exact ⟨i,(hb i).mpr ⟨hi,j,p,hp,hpc⟩⟩
    obtain ⟨i,hi,hmin⟩ := hk.wellOrder.least B (fun i hi => ((hb i).mp hi).1) hBne
    obtain ⟨hiK,j,p,hp,hpc⟩ := (hb i).mp hi
    obtain ⟨i',J,j',_,hJ,hj,hpc'⟩ := (hA p).mp (hXA p hp)
    obtain ⟨ei,ej⟩ := PureKuratowski.code_injective hpc' hpc
    subst i' j'
    let inner : Project.UnarySchema 2 := {body := hit 1 2 0,freeClosed := hit_freeClosed ..}
    let eta : SetTheory.Env N 2 := {bound := Fin.cases X (fun _ => i),free := fun _ => X}
    have hiEq j : inner.denote eta j ↔ Hit X i j := hit_semantics hM (eta.push j) 1 2 0
    obtain ⟨C,hC⟩ := ZF.separation_exists_d hZF inner eta J
    have hc j : N.mem j C ↔ N.mem j J ∧ Hit X i j := (hC j).trans (and_congr_right fun _ => hiEq j)
    obtain ⟨j0,hj0,hinnerMin⟩ := (hI.2 i J hJ).wellOrder.least C
      (fun j hj => ((hc j).mp hj).1) ⟨j,(hc j).mpr ⟨hj,p,hp,hpc⟩⟩
    obtain ⟨_,p0,hp0,hp0c⟩ := (hc j0).mp hj0
    refine ⟨p0,hp0,?_⟩
    intro q hq
    obtain ⟨k,K,l,hk',hK,hl,hqc⟩ := (hA q).mp (hXA q hq)
    have hkB : N.mem k B := (hb k).mpr ⟨hk',l,q,hq,hqc⟩
    rcases hmin k hkB with eq | hik
    · have eik := (ModelTransfer.extensionality hM).eq_of_same_members i k eq
      subst k
      have eK := function_unique hI.1 hK hJ
      subst K
      have hlC : N.mem l C := (hc l).mpr ⟨hl,q,hq,hqc⟩
      rcases hinnerMin l hlC with eq | hjl
      · have ejl := (ModelTransfer.extensionality hM).eq_of_same_members j0 l eq
        subst l
        have epq := KuratowskiZF.code_unique hM hp0c hqc
        subst q
        exact Or.inl (fun _ => Iff.rfl)
      · exact Or.inr ((rel p0 q).mpr ⟨hXA p0 hp0,hXA q hq,(lex_pair hp0c hqc).mpr (Or.inr ⟨rfl,hjl⟩)⟩)
    · exact Or.inr ((rel p0 q).mpr ⟨hXA p0 hp0,hXA q hq,(lex_pair hp0c hqc).mpr (Or.inl hik)⟩)

/-- Extract the actual inner ordinal from each fixed trace. Reuse the
existing field syntax/uniqueness and native functional-image constructor. -/
theorem exists_indices (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top zero one K mu history F kappa traces : M.Carrier .set}
    (hf : ConstructionBlockTraces.Family hM w Q R top zero one K mu history F kappa traces) :
    ∃ Indices, Chart 0 kappa traces Indices ∧ Fibers kappa Indices := by
  let schema : Project.BinarySchema 1 := {
    body := ConstructionTowerHistory.field 0 2 1 0
    freeClosed := ConstructionTowerHistory.field_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 := {
    bound := fun _ => traces,free := fun _ => kappa }
  have he i J : schema.denote env i J ↔ Field 0 traces i J :=
    ConstructionTowerHistory.field_semantics hM 0 ((env.push i).push J) 2 1 0
  have ht : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i kappa → ∃ J, schema.denote env i J := by
    intro i hi
    obtain ⟨J,Schedule,last,inner,Finner,Steps,Events,Roots,L,hRow⟩ := ConstructionBlockTraces.family_row hM hf hi
    exact ⟨J,(he i J).mpr ⟨J,Schedule,last,inner,Finner,Steps,Events,Roots,L,hRow,rfl⟩⟩
  have hu : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i kappa → ∀ J K,
      schema.denote env i J → schema.denote env i K → J = K :=
    fun _ _ _ _ hJ hK => ConstructionTowerHistory.field_unique 0 hf.1 ((he _ _).mp hJ) ((he _ _).mp hK)
  obtain ⟨A,hA⟩ := ZF.exists_functionalImageOn (ModelTransfer.project_models_iff.mp hM) schema env kappa ht hu
  obtain ⟨Indices,hIndices,hGraph⟩ := ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) schema env ht hu
    (fun i J hi hJ => (hA J).mpr ⟨i,hi,hJ⟩)
  have hChart : Chart 0 kappa traces Indices :=
    ⟨((ForcingSupportSize.native_mapsTo hM kappa A Indices).mpr hIndices).1,
      fun i J => (hGraph i J).trans (and_congr_right fun _ => he i J)⟩
  refine ⟨Indices,hChart,hChart.1,?_⟩
  intro i J hJi
  obtain ⟨_,D,Schedule,last,inner,Finner,Steps,Events,Roots,L,hRow,eq⟩ := (hChart.2 i J).mp hJi
  change J = D at eq
  subst D
  obtain ⟨code,hcode,hPack⟩ := hRow
  have hAt := ((hf.2 i code).mp hcode).2.1
  obtain ⟨j,raw,Requests,N,mulN,eN,markN,HN,CN,L0,f,W,G,unitW,markW,HW,CW,NewOut,baseW,O,
    _,_,_,_,_,_,_,_,hTrace⟩ := hAt
  obtain ⟨u,A0,I,indexTop,default,oldSchedule,oldPlace,r,order,J',collapse,inverse,Schedule',Place,last',
    inner',P,Finner',Steps',Events',Roots',L',hPack',hCtx,_⟩ := hTrace
  have eqJ := (ConstructionRoundSelection.pack_injective hPack hPack').1
  subst J'
  obtain ⟨_,_,_,_,_,_,_,_,_,hJ,_,_⟩ := hCtx
  exact hJ

def Data (hM : FirstOrder.Theory.Models M nativeZF)
    (kappa traces Indices A r I R : M.Carrier .set) : Prop :=
  Chart 0 kappa traces Indices ∧ Fibers kappa Indices ∧ Carrier kappa Indices A ∧
    (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) r A ∧
    Order A r ∧ ForcingWithTopCarrier.Carrier A I ∧
    (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) R I ∧
    ∀ x y, PureKuratowski.PairMember M x y R ↔
      (Project.FirstOrderSemantics.reduct M).mem x I ∧ (Project.FirstOrderSemantics.reduct M).mem y I ∧
      ConstructionScheduleOrder.Lt r x y

theorem exists_index (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top zero one K mu history F kappa traces : M.Carrier .set}
    (hk : (Project.FirstOrderSemantics.reduct M).IsOrdinal kappa)
    (hf : ConstructionBlockTraces.Family hM w Q R top zero one K mu history F kappa traces) :
    ∃ Indices A r I order, Data hM kappa traces Indices A r I order := by
  obtain ⟨Indices,hChart,hFibers⟩ := exists_indices hM hf
  obtain ⟨A,hA⟩ := exists_carrier hM hFibers.1
  obtain ⟨r,hr,hGraph⟩ := exists_order hM hk hFibers hA
  obtain ⟨I,hI⟩ := ForcingWithTopCarrier.exists_carrier hM A
  obtain ⟨order,hOrder,hOrderGraph⟩ := ConstructionScheduleOrder.exists_index_order hM hI hr
  exact ⟨Indices,A,r,I,order,hChart,hFibers,hA,hr,hGraph,hI,hOrder,hOrderGraph⟩

/-- Connect the same actual outer recursion all the way to the dependent index. -/
theorem recursive_index (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C zero one u K mu B history P F kappa : M.Carrier .set}
    (hCtx : ConstructionSaturationIterationCases.Context hM w Q R top D mul e mark H C zero one u K mu B)
    (hRec : ConstructionSaturationIteration.Recursive hM w Q R top D mul e mark H C zero one K mu B B history)
    (hF : ConstructionTowerTransitions.Matrix B history zero P F)
    (hk : (Project.FirstOrderSemantics.reduct M).mem kappa B) :
    ∃ traces Indices A r I order,
      ConstructionBlockTraces.Family hM w Q R top zero one K mu history F kappa traces ∧
      Data hM kappa traces Indices A r I order := by
  obtain ⟨traces,hf⟩ := ConstructionBlockTraces.recursive_family hM hOrder hChoice hCtx hRec hF hk
  have hCopy := hCtx
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hB,_⟩ := hCopy
  obtain ⟨Indices,A,r,I,order,hData⟩ := exists_index hM (hB.mem hk) hf
  exact ⟨traces,Indices,A,r,I,order,hf,hData⟩

def fibers {m : Nat} (kappa Indices : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn Indices kappa)) (.forallE (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Indices.succ.succ 1 0)) (Project.Formula.isOrdinal (.bound
  0))))))

theorem fibers_freeClosed {m : Nat} (kappa Indices : Fin m) :
    (fibers kappa Indices).FreeClosed := by
  simp -implicitDefEqProofs [fibers,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem fibers_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (kappa Indices : Fin m) :
    Project.Formula.satisfies env (fibers kappa Indices) ↔
      Fibers (env.bound kappa) (env.bound Indices) := by
  simp only [fibers,Fibers,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOrdinal_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConditionGraphs.functionOn_semantics (M := M),KuratowskiZF.source_edge]
  rfl

def carrier {m : Nat} (kappa Indices A : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound 0) (.bound A.succ)) (point kappa.succ Indices.succ 0)))

theorem carrier_freeClosed {m : Nat} (kappa Indices A : Fin m) :
    (carrier kappa Indices A).FreeClosed := by
  simp -implicitDefEqProofs [carrier,Definitional.Formula.FreeClosed,point_freeClosed]

theorem carrier_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (kappa Indices A : Fin m) :
    Project.Formula.satisfies env (carrier kappa Indices A) ↔
      Carrier (env.bound kappa) (env.bound Indices) (env.bound A) := by
  simp only [carrier,Carrier,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,point_semantics hM]
  rfl

def order {m : Nat} (A r : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge r.succ.succ 1 0)) (.conj (.mem
  (.bound 1) (.bound A.succ.succ)) (.conj (.mem (.bound 0) (.bound A.succ.succ)) (lex 1 0))))))

theorem order_freeClosed {m : Nat} (A r : Fin m) :
    (order A r).FreeClosed := by
  simp -implicitDefEqProofs [order,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,lex_freeClosed]

theorem order_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (A r : Fin m) :
    Project.Formula.satisfies env (order A r) ↔
      Order (env.bound A) (env.bound r) := by
  simp only [order,Order,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,lex_semantics hM]
  rfl

def data {m : Nat} (kappa traces Indices A r I R : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionTowerHistory.chart 0 kappa traces Indices) (.conj (fibers kappa Indices) (.conj (carrier
  kappa Indices A) (.conj (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound r)
  (.bound A)) (.conj (order A r) (.conj (ProjectSyntax.encode id (ForcingWithTopCarrier.carrier A I)) (.conj
  (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound R) (.bound I)) (.forallE
  (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge R.succ.succ 1 0)) (.conj (.mem (.bound 1)
  (.bound I.succ.succ)) (.conj (.mem (.bound 0) (.bound I.succ.succ)) (ConstructionScheduleOrder.lt r.succ.succ
  1 0)))))))))))))

theorem data_freeClosed {m : Nat} (kappa traces Indices A r I R : Fin m) :
    (data kappa traces Indices A r I R).FreeClosed := by
  simp -implicitDefEqProofs [data,Definitional.Formula.FreeClosed,ConstructionTowerHistory.chart_freeClosed,fibers_freeClosed,carrier_freeClosed,order_freeClosed,ProjectSyntax.freeClosed,ConstructionScheduleOrder.lt_freeClosed]

theorem data_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (kappa traces Indices A r I R : Fin m) :
    Project.Formula.satisfies env (data kappa traces Indices A r I R) ↔
      Data hM (env.bound kappa) (env.bound traces) (env.bound Indices) (env.bound A) (env.bound r) (env.bound I) (env.bound R) := by
  simp only [data,Data,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ConstructionTowerHistory.chart_semantics hM 0,fibers_semantics hM,carrier_semantics hM,order_semantics hM,Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingWithTopCarrier.carrier_semantics (M := M),KuratowskiZF.source_edge,ConstructionScheduleOrder.lt_semantics hM]
  rfl

def constructionSentence {m : Nat} (w Q R top zero one K mu history F kappa traces : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOrdinal (.bound kappa)) (.imp (ConstructionBlockTraces.family w Q R top zero one K mu
    history F kappa traces) (.existsE (.existsE (.existsE (.existsE (.existsE (data kappa.succ.succ.succ.succ.succ
    traces.succ.succ.succ.succ.succ 4 3 2 1 0))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionBlockTraces.family_freeClosed,data_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat} (w Q R top zero one K mu history F kappa traces : Fin m) :
    (Project.fo_sentence (constructionSentence w Q R top zero one K mu history F kappa traces)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w Q R top zero one K mu history F kappa traces)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isOrdinal_iff,Project.Term.eval_bound,
    ConstructionBlockTraces.family_semantics hM,data_semantics hM]
  exact exists_index hM

theorem construction_kernel_certificate {m : Nat} (w Q R top zero one K mu history F kappa traces : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence w Q R top zero one K mu history F kappa traces)) := by
  apply ModelTransfer.derives
  intro M hM
  exact construction_models hM w Q R top zero one K mu history F kappa traces

def recursiveSentence {m : Nat} (w Q R top D mul e mark H C zero one u K mu B history P F kappa : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ConstructionSaturationIterationCases.context w Q R top D mul e mark H C zero one u K mu B) (.imp
    (ConstructionSaturationIteration.recursive w Q R top D mul e mark H C zero one K mu B B history) (.imp
    (ConstructionTowerTransitions.matrix B history zero P F) (.imp (.mem (.bound kappa) (.bound B)) (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionBlockTraces.family
    w.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ.succ
    top.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ one.succ.succ.succ.succ.succ.succ
    K.succ.succ.succ.succ.succ.succ mu.succ.succ.succ.succ.succ.succ history.succ.succ.succ.succ.succ.succ
    F.succ.succ.succ.succ.succ.succ kappa.succ.succ.succ.succ.succ.succ 5) (data
    kappa.succ.succ.succ.succ.succ.succ 5 4 3 2 1 0))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ConstructionSaturationIterationCases.context_freeClosed,ConstructionSaturationIteration.recursive_freeClosed,
      ConstructionTowerTransitions.matrix_freeClosed,ConstructionBlockTraces.family_freeClosed,data_freeClosed]

theorem recursive_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {m : Nat} (w Q R top D mul e mark H C zero one u K mu B history P F kappa : Fin m) :
    (Project.fo_sentence (recursiveSentence w Q R top D mul e mark H C zero one u K mu B history P F kappa)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (recursiveSentence w Q R top D mul e mark H C zero one u K mu B history P F kappa)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionSaturationIterationCases.context_semantics hM,ConstructionSaturationIteration.recursive_semantics hM,
    ConstructionTowerTransitions.matrix_semantics hM,ConstructionBlockTraces.family_semantics hM,data_semantics hM]
  exact recursive_index hM hOrder hChoice

theorem recursive_kernel_certificate {m : Nat} (w Q R top D mul e mark H C zero one u K mu B history P F kappa : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (recursiveSentence w Q R top D mul e mark H C zero one u K mu B history P F kappa))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let z := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => z }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (recursiveSentence w Q R top D mul e mark H C zero one u K mu B history P F kappa)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (recursiveSentence w Q R top D mul e mark H C zero one u K mu B history P F kappa)).mp
    (recursive_models hL (ConstructionRoundSelection.l_order hM) hChoice w Q R top D mul e mark H C zero one u K mu B history P F kappa)

end PPAC.Migration.ConstructionBlockIndex
