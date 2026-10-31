/- Pinned CellReorder.Subobject.Square.union. Collect the unique local
pushout lifts by the existing native functional-image/function constructors,
then consume the SAME actual-union lift. All target monoids remain internal
and arbitrary. Consumer: future_cut's limit branch. -/
import PPAC.Migration.ConstructionSubobjectUnion

namespace PPAC.Migration.ConstructionUnionPushout
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbePushout (Hom SquareComm IsPushout)
open ConstructionProbeMappedPath (NodeMap)
open ConstructionConservativeHull (Closure ProductGraph)
open ConstructionCellRestriction (Stages)
open ConstructionSubobjectUnion (Union Cocone Compatible Restricts)
open ConstructionSelectedCellRestriction (Base)
open ConstructionRealCuts (Subset)
open ConstructionDirectedSystem (IndexLaws)
open ConstructionBlockStages (MonotoneImages)
open ConstructionDirectedWeightData (WeightFamily)
open ForcingConditionGraphs (FunctionOn IdentityGraph function_input function_unique)
open ForcingSupportSize (MapsTo)
open ForcingDiagramPoset (LeftCancelMonoid Conical Unit Associative)
open ConstructionProbeLetters (Representatives)
open ConstructionProbeConservative (Conservative)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Equality of graph values on the actual subobject. -/
def Agree (D f g : M.Carrier .set) : Prop := ∀ x y,
  (Project.FirstOrderSemantics.reduct M).mem x D →
  (PureKuratowski.PairMember M x y f ↔ PureKuratowski.PairMember M x y g)

theorem agree_of_node {D inc lift f : M.Carrier .set}
    (hId : IdentityGraph D inc) (hFac : NodeMap inc lift f) : Agree D lift f := by
  intro x y hx
  constructor
  · intro hxy
    exact (hFac x y).mpr ⟨x,(hId x x).mpr ⟨hx,rfl⟩,hxy⟩
  · intro hxy
    obtain ⟨z,hxz,hzy⟩ := (hFac x y).mp hxy
    obtain ⟨_,rfl⟩ := (hId x z).mp hxz
    exact hzy

theorem node_of_agree {D Q inc lift f : M.Carrier .set}
    (hId : IdentityGraph D inc) (hf : MapsTo D Q f) (hAgree : Agree D lift f) : NodeMap inc lift f := by
  intro x y
  constructor
  · intro hxy
    have hx := function_input hf.1 hxy
    exact ⟨x,(hId x x).mpr ⟨hx,rfl⟩,(hAgree x y hx).mpr hxy⟩
  · rintro ⟨z,hxz,hzy⟩
    obtain ⟨hx,rfl⟩ := (hId x z).mp hxz
    exact (hAgree x y hx).mp hzy

/-- Literal native restriction of a supplied Hom to a subobject. -/
theorem restrict_hom (hM : FirstOrder.Theory.Models M nativeZF)
    {D U GD GU GV e Q GQ uQ f : M.Carrier .set}
    (hSub : Subset D U) (he : (Project.FirstOrderSemantics.reduct M).mem e D)
    (hGD : ProductGraph D GV GD) (hGU : ProductGraph U GV GU)
    (hf : Hom U Q GU GQ e uQ f) : ∃ r, Hom D Q GD GQ e uQ r ∧
      ∀ x y, PureKuratowski.PairMember M x y r ↔
        (Project.FirstOrderSemantics.reduct M).mem x D ∧ PureKuratowski.PairMember M x y f := by
  obtain ⟨r,hr⟩ := ZF.exists_restriction (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) f D
  have hMap : MapsTo D Q r := by
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro z hz
      obtain ⟨x,y,hxy⟩ := hr.1 z hz
      exact ⟨x,y,((hr.2 x y).mp ⟨z,hxy,hz⟩).1,hxy⟩
    · intro x hx
      obtain ⟨y,hxy,_⟩ := hf.1.1.2 x (hSub x hx)
      exact ⟨y,(hr.2 x y).mpr ⟨hx,hxy⟩,fun z hxz => function_unique hf.1.1 ((hr.2 x z).mp hxz).2 hxy⟩
    · intro x y hxy
      exact hf.1.2 x y ((hr.2 x y).mp hxy).2
  refine ⟨r,⟨hMap,(hr.2 e uQ).mpr ⟨he,hf.2.1⟩,?_⟩,hr.2⟩
  intro x y z fx fy fz hp hx hy hz
  have hProduct := ConstructionCellRestriction.product_factor hGD hGU hSub
  exact hf.2.2 x y z fx fy fz ((hProduct x y z).mp hp).2.2
    ((hr.2 x fx).mp hx).2 ((hr.2 y fy).mp hy).2 ((hr.2 z fz).mp hz).2

/-- SAME carrier/multiplication families and literal inclusion graphs of the
local source squares. No family of lifts is assumed. -/
def Family (K Bs Ds BMs DMs A C GC GV e ia ic : M.Carrier .set) : Prop :=
  FunctionOn K Bs ∧ FunctionOn K Ds ∧ FunctionOn K BMs ∧ FunctionOn K DMs ∧ Subset A C ∧
  ∀ i Bi Di GBi GDi, (Project.FirstOrderSemantics.reduct M).mem i K →
    PureKuratowski.PairMember M i Bi Bs → PureKuratowski.PairMember M i Di Ds →
    PureKuratowski.PairMember M i GBi BMs → PureKuratowski.PairMember M i GDi DMs →
    Subset A Bi ∧ Subset Bi Di ∧ Subset C Di ∧ ProductGraph Bi GV GBi ∧ ProductGraph Di GV GDi ∧
    ∃ ibi, FunctionOn Bi ibi ∧ IdentityGraph Bi ibi ∧ IsPushout C Bi Di GC GBi GDi e e e ia ia ibi ic

/-- Unique lift on one actual stage, expressed without a chosen witness. -/
def LocalLift (Bs Ds BMs DMs C e Q GQ uQ b c i lift : M.Carrier .set) : Prop :=
  ∃ Bi Di GBi GDi, PureKuratowski.PairMember M i Bi Bs ∧ PureKuratowski.PairMember M i Di Ds ∧
    PureKuratowski.PairMember M i GBi BMs ∧ PureKuratowski.PairMember M i GDi DMs ∧
    Hom Di Q GDi GQ e uQ lift ∧ Agree Bi lift b ∧ Agree C lift c ∧
    ∀ other, Hom Di Q GDi GQ e uQ other → Agree Bi other b → Agree C other c → other = lift

theorem local_exists (hM : FirstOrder.Theory.Models M nativeZF)
    {V GV e K Bs Ds BMs DMs A B C GC GB ia ic Q J GQ uQ b c i : M.Carrier .set}
    (hF : Family K Bs Ds BMs DMs A C GC GV e ia ic)
    (hBs : Stages V GV e Bs) (hB : Union K Bs B) (hGB : ProductGraph B GV GB)
    (hIa : IdentityGraph A ia) (hIc : IdentityGraph C ic)
    (hQ : Representatives Q Q J) (hGQ : MapsTo J Q GQ) (hUnit : Unit Q GQ uQ) (hAssoc : Associative Q GQ)
    (hb : Hom B Q GB GQ e uQ b) (hc : Hom C Q GC GQ e uQ c) (hComm : SquareComm ia ia b c)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i K) :
    ∃ lift, LocalLift Bs Ds BMs DMs C e Q GQ uQ b c i lift := by
  obtain ⟨Bi,hBi,_⟩ := hF.1.2 i hi
  obtain ⟨Di,hDi,_⟩ := hF.2.1.2 i hi
  obtain ⟨GBi,hGBi,_⟩ := hF.2.2.1.2 i hi
  obtain ⟨GDi,hGDi,_⟩ := hF.2.2.2.1.2 i hi
  obtain ⟨hAB,hBD,hCD,hPB,hPD,ibi,_,hIbi,hP⟩ := hF.2.2.2.2.2 i Bi Di GBi GDi hi hBi hDi hGBi hGDi
  obtain ⟨br,hbr,hbrEq⟩ := restrict_hom hM (fun x hx => (hB x).mpr ⟨i,Bi,hi,hBi,hx⟩)
    (hBs i Bi hBi).2.1 hPB hGB hb
  have hCommR : SquareComm ia ia br c := by
    intro x q fx y hxq hxf
    obtain ⟨hxA,rfl⟩ := (hIa x q).mp hxq
    obtain ⟨_,rfl⟩ := (hIa x fx).mp hxf
    exact (hbrEq x y).trans ⟨fun h => (hComm x x x y hxq hxf).mp h.2,
      fun h => ⟨hAB x hxA,(hComm x x x y hxq hxf).mpr h⟩⟩
  obtain ⟨lift,hLift,hLeft,hRight,hUnique⟩ := hP.2 Q J GQ uQ br c hQ hGQ hUnit hAssoc hbr hc hCommR
  have hAgreeB : Agree Bi lift b := by
    intro x y hx
    exact (agree_of_node hIbi hLeft x y hx).trans ((hbrEq x y).trans ⟨And.right,fun h => ⟨hx,h⟩⟩)
  have hAgreeC := agree_of_node hIc hRight
  refine ⟨lift,Bi,Di,GBi,GDi,hBi,hDi,hGBi,hGDi,hLift,hAgreeB,hAgreeC,?_⟩
  intro other hOther hOtherB hOtherC
  apply hUnique other hOther
  · apply node_of_agree hIbi hbr.1
    intro x y hx
    exact (hOtherB x y hx).trans ((hbrEq x y).trans ⟨And.right,fun h => ⟨hx,h⟩⟩).symm
  · exact node_of_agree hIc hc.1 hOtherC

theorem local_unique {K Bs Ds BMs DMs C e Q GQ uQ b c i l r : M.Carrier .set}
    (hBs : FunctionOn K Bs) (hDs : FunctionOn K Ds) (hBM : FunctionOn K BMs) (hDM : FunctionOn K DMs)
    (hl : LocalLift Bs Ds BMs DMs C e Q GQ uQ b c i l)
    (hr : LocalLift Bs Ds BMs DMs C e Q GQ uQ b c i r) : l = r := by
  obtain ⟨Bi,Di,GBi,GDi,hBi,hDi,hGBi,hGDi,hL,hLB,hLC,_⟩ := hl
  obtain ⟨Bj,Dj,GBj,GDj,hBj,hDj,hGBj,hGDj,_,_,_,hUnique⟩ := hr
  have eB := function_unique hBs hBi hBj
  have eD := function_unique hDs hDi hDj
  have eGB := function_unique hBM hGBi hGBj
  have eGD := function_unique hDM hGDi hGDj
  subst Bj Dj GBj GDj
  exact hUnique l hL hLB hLC

def agree {m : Nat} (D f g : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (.mem (.bound 1) (.bound D.succ.succ)) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ 1 0)) (ProjectSyntax.encode id (Source.SetLanguage.edge g.succ.succ 1 0))))))

theorem agree_freeClosed {m : Nat} (D f g : Fin m) : (agree D f g).FreeClosed := by
  simp -implicitDefEqProofs [agree,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem agree_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D f g : Fin m) :
    Project.Formula.satisfies env (agree D f g) ↔ Agree (env.bound D) (env.bound f) (env.bound g) := by
  simp only [agree,Agree,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_iff_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def localLift {m : Nat} (Bs Ds BMs DMs C e Q GQ uQ b c i lift : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge Bs.succ.succ.succ.succ i.succ.succ.succ.succ 3)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge Ds.succ.succ.succ.succ i.succ.succ.succ.succ 2)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge BMs.succ.succ.succ.succ i.succ.succ.succ.succ 1)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge DMs.succ.succ.succ.succ i.succ.succ.succ.succ 0)) (.conj (ConstructionProbePushoutSyntax.hom 2 Q.succ.succ.succ.succ 0 GQ.succ.succ.succ.succ e.succ.succ.succ.succ uQ.succ.succ.succ.succ lift.succ.succ.succ.succ) (.conj (agree 3 lift.succ.succ.succ.succ b.succ.succ.succ.succ) (.conj (agree C.succ.succ.succ.succ lift.succ.succ.succ.succ c.succ.succ.succ.succ) (.forallE (.imp (ConstructionProbePushoutSyntax.hom 3 Q.succ.succ.succ.succ.succ 1 GQ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ uQ.succ.succ.succ.succ.succ 0) (.imp (agree 4 0 b.succ.succ.succ.succ.succ) (.imp (agree C.succ.succ.succ.succ.succ 0 c.succ.succ.succ.succ.succ) (Project.Formula.extensionalEq (.bound 0) (.bound lift.succ.succ.succ.succ.succ)))))))))))))))))

theorem localLift_freeClosed {m : Nat} (Bs Ds BMs DMs C e Q GQ uQ b c i lift : Fin m) :
    (localLift Bs Ds BMs DMs C e Q GQ uQ b c i lift).FreeClosed := by
  simp -implicitDefEqProofs [localLift,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionProbePushoutSyntax.hom_freeClosed,agree_freeClosed,Project.Formula.extensionalEq]

theorem localLift_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (Bs Ds BMs DMs C e Q GQ uQ b c i lift : Fin m) :
    Project.Formula.satisfies env (localLift Bs Ds BMs DMs C e Q GQ uQ b c i lift) ↔ LocalLift (env.bound Bs) (env.bound Ds) (env.bound BMs) (env.bound DMs) (env.bound C) (env.bound e) (env.bound Q) (env.bound GQ) (env.bound uQ) (env.bound b) (env.bound c) (env.bound i) (env.bound lift) := by
  simp only [localLift,LocalLift,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionProbePushoutSyntax.hom_semantics hM,agree_semantics hM,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  rfl

def LiftFamily (K Bs Ds BMs DMs C e Q GQ uQ b c Legs : M.Carrier .set) : Prop :=
  FunctionOn K Legs ∧ ∀ i lift, PureKuratowski.PairMember M i lift Legs ↔
    (Project.FirstOrderSemantics.reduct M).mem i K ∧ LocalLift Bs Ds BMs DMs C e Q GQ uQ b c i lift

/-- Collection uses a definable unique value, never a host choice function. -/
theorem exists_family (hM : FirstOrder.Theory.Models M nativeZF)
    {V GV e K Bs Ds BMs DMs A B C GC GB ia ic Q J GQ uQ b c : M.Carrier .set}
    (hF : Family K Bs Ds BMs DMs A C GC GV e ia ic)
    (hBs : Stages V GV e Bs) (hB : Union K Bs B) (hGB : ProductGraph B GV GB)
    (hIa : IdentityGraph A ia) (hIc : IdentityGraph C ic)
    (hQ : Representatives Q Q J) (hGQ : MapsTo J Q GQ) (hUnit : Unit Q GQ uQ) (hAssoc : Associative Q GQ)
    (hb : Hom B Q GB GQ e uQ b) (hc : Hom C Q GC GQ e uQ c) (hComm : SquareComm ia ia b c) :
    ∃ Legs, LiftFamily K Bs Ds BMs DMs C e Q GQ uQ b c Legs := by
  let schema : Project.BinarySchema 11 := {
    body := localLift 2 3 4 5 6 7 8 9 10 11 12 1 0
    freeClosed := localLift_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 11 := {
    bound := Fin.cases Bs (Fin.cases Ds (Fin.cases BMs (Fin.cases DMs (Fin.cases C
      (Fin.cases e (Fin.cases Q (Fin.cases GQ (Fin.cases uQ (Fin.cases b (fun _ => c))))))))))
    free := fun _ => K }
  have he i lift : schema.denote env i lift ↔ LocalLift Bs Ds BMs DMs C e Q GQ uQ b c i lift :=
    localLift_semantics hM ((env.push i).push lift) 2 3 4 5 6 7 8 9 10 11 12 1 0
  have htotal : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i K → ∃ lift, schema.denote env i lift := by
    intro i hi
    obtain ⟨lift,hl⟩ := local_exists hM hF hBs hB hGB hIa hIc hQ hGQ hUnit hAssoc hb hc hComm hi
    exact ⟨lift,(he i lift).mpr hl⟩
  have hunique : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i K → ∀ l r,
      schema.denote env i l → schema.denote env i r → l = r :=
    fun _ _ _ _ hl hr => local_unique hF.1 hF.2.1 hF.2.2.1 hF.2.2.2.1 ((he _ _).mp hl) ((he _ _).mp hr)
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨images,himages⟩ := ZF.exists_functionalImageOn hZF schema env K htotal hunique
  obtain ⟨Legs,hLegs,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (KuratowskiZF.interpretation hM)
    schema env htotal hunique (fun i lift hi hl => (himages lift).mpr ⟨i,hi,hl⟩)
  exact ⟨Legs,((ForcingSupportSize.native_mapsTo hM K images Legs).mpr hLegs).1,
    fun i lift => (hgraph i lift).trans (and_congr_right fun _ => he i lift)⟩

/-- Read a local lift at the SAME stage and multiplication graphs. -/
theorem local_at {K Bs Ds BMs DMs C e Q GQ uQ b c i lift Bi Di GBi GDi : M.Carrier .set}
    (hBs : FunctionOn K Bs) (hDs : FunctionOn K Ds) (hBM : FunctionOn K BMs) (hDM : FunctionOn K DMs)
    (hl : LocalLift Bs Ds BMs DMs C e Q GQ uQ b c i lift)
    (hBi : PureKuratowski.PairMember M i Bi Bs) (hDi : PureKuratowski.PairMember M i Di Ds)
    (hGBi : PureKuratowski.PairMember M i GBi BMs) (hGDi : PureKuratowski.PairMember M i GDi DMs) :
    Hom Di Q GDi GQ e uQ lift ∧ Agree Bi lift b ∧ Agree C lift c ∧
    ∀ other, Hom Di Q GDi GQ e uQ other → Agree Bi other b → Agree C other c → other = lift := by
  obtain ⟨Bj,Dj,GBj,GDj,hBj,hDj,hGBj,hGDj,hRest⟩ := hl
  have eB := function_unique hBs hBi hBj
  have eD := function_unique hDs hDi hDj
  have eGB := function_unique hBM hGBi hGBj
  have eGD := function_unique hDM hGDi hGDj
  subst Bj Dj GBj GDj
  exact hRest

theorem family_cocone {K Bs Ds BMs DMs A C GC GV e ia ic Q GQ uQ b c Legs : M.Carrier .set}
    (hF : Family K Bs Ds BMs DMs A C GC GV e ia ic)
    (hL : LiftFamily K Bs Ds BMs DMs C e Q GQ uQ b c Legs) : Cocone K Ds DMs Legs GV e Q GQ uQ := by
  have hat : ∀ i Di GDi li, (Project.FirstOrderSemantics.reduct M).mem i K →
      PureKuratowski.PairMember M i Di Ds → PureKuratowski.PairMember M i GDi DMs →
      PureKuratowski.PairMember M i li Legs → ProductGraph Di GV GDi ∧ Hom Di Q GDi GQ e uQ li := by
    intro i Di GDi li hi hDi hGDi hli
    obtain ⟨Bi,hBi,_⟩ := hF.1.2 i hi
    obtain ⟨GBi,hGBi,_⟩ := hF.2.2.1.2 i hi
    have hl := local_at hF.1 hF.2.1 hF.2.2.1 hF.2.2.2.1 ((hL.2 i li).mp hli).2 hBi hDi hGBi hGDi
    exact ⟨(hF.2.2.2.2.2 i Bi Di GBi GDi hi hBi hDi hGBi hGDi).2.2.2.2.1,hl.1⟩
  refine ⟨hF.2.2.2.1,⟨hL.1,?_⟩,hat⟩
  intro i Di li hi hDi hli
  obtain ⟨GDi,hGDi,_⟩ := hF.2.2.2.1.2 i hi
  exact (hat i Di GDi li hi hDi hGDi hli).2.1

/-- Source ht: uniqueness at i compares the restriction of the lift at j. -/
theorem family_compatible (hM : FirstOrder.Theory.Models M nativeZF)
    {V GV e K E Bs Ds BMs DMs A C GC ia ic Q GQ uQ b c Legs : M.Carrier .set}
    (hF : Family K Bs Ds BMs DMs A C GC GV e ia ic)
    (hDs : Stages V GV e Ds) (hBM : MonotoneImages K E Bs) (hDM : MonotoneImages K E Ds)
    (hL : LiftFamily K Bs Ds BMs DMs C e Q GQ uQ b c Legs) : Compatible K E Ds Legs := by
  intro i j Di li lj x y hi hj hij hDi hli hlj hx hxy
  obtain ⟨Bi,Dii,GBi,GDi,hBi,hDii,hGBi,hGDi,hLi,hLiB,hLiC,hUnique⟩ := ((hL.2 i li).mp hli).2
  obtain ⟨Bj,Dj,GBj,GDj,hBj,hDj,hGBj,hGDj,hLj,hLjB,hLjC,_⟩ := ((hL.2 j lj).mp hlj).2
  have eD := function_unique hF.2.1 hDi hDii
  subst Dii
  obtain ⟨_,hBD,hCD,_,hPD,_⟩ := hF.2.2.2.2.2 i Bi Di GBi GDi hi hBi hDi hGBi hGDi
  have hPDj := (hF.2.2.2.2.2 j Bj Dj GBj GDj hj hBj hDj hGBj hGDj).2.2.2.2.1
  obtain ⟨r,hr,hrEq⟩ := restrict_hom hM (hDM i j Di Dj hi hj hij hDi hDj)
    (hDs i Di hDi).2.1 hPD hPDj hLj
  have hRB : Agree Bi r b := by
    intro z q hz
    exact (hrEq z q).trans ⟨fun h => (hLjB z q (hBM i j Bi Bj hi hj hij hBi hBj z hz)).mp h.2,
      fun h => ⟨hBD z hz,(hLjB z q (hBM i j Bi Bj hi hj hij hBi hBj z hz)).mpr h⟩⟩
  have hRC : Agree C r c := by
    intro z q hz
    exact (hrEq z q).trans ⟨fun h => (hLjC z q hz).mp h.2,fun h => ⟨hCD z hz,(hLjC z q hz).mpr h⟩⟩
  have er := hUnique r hr hRB hRC
  subst r
  exact ((hrEq x y).mp hxy).2


theorem union_subsets {K Bs Ds BMs DMs A B C D GC GV e ia ic : M.Carrier .set}
    (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i K)
    (hF : Family K Bs Ds BMs DMs A C GC GV e ia ic) (hB : Union K Bs B) (hD : Union K Ds D) :
    Subset A B ∧ Subset A C ∧ Subset B D ∧ Subset C D := by
  obtain ⟨i,hi⟩ := hne
  obtain ⟨Bi,hBi,_⟩ := hF.1.2 i hi
  obtain ⟨Di,hDi,_⟩ := hF.2.1.2 i hi
  obtain ⟨GBi,hGBi,_⟩ := hF.2.2.1.2 i hi
  obtain ⟨GDi,hGDi,_⟩ := hF.2.2.2.1.2 i hi
  have hStage := hF.2.2.2.2.2 i Bi Di GBi GDi hi hBi hDi hGBi hGDi
  refine ⟨fun x hx => (hB x).mpr ⟨i,Bi,hi,hBi,hStage.1 x hx⟩,hF.2.2.2.2.1,?_,
    fun x hx => (hD x).mpr ⟨i,Di,hi,hDi,hStage.2.2.1 x hx⟩⟩
  intro x hx
  obtain ⟨j,Bj,hj,hBj,hxBj⟩ := (hB x).mp hx
  obtain ⟨Dj,hDj,_⟩ := hF.2.1.2 j hj
  obtain ⟨GBj,hGBj,_⟩ := hF.2.2.1.2 j hj
  obtain ⟨GDj,hGDj,_⟩ := hF.2.2.2.1.2 j hj
  exact (hD x).mpr ⟨j,Dj,hj,hDj,(hF.2.2.2.2.2 j Bj Dj GBj GDj hj hBj hDj hGBj hGDj).2.1 x hxBj⟩

/-- The full arbitrary-target pushout of the actual unions. -/
theorem union_pushout (hM : FirstOrder.Theory.Models M nativeZF)
    {V GV e K E Bs Ds BMs DMs A B C D GB GC GD ia ib ic : M.Carrier .set}
    (hE : IndexLaws K E) (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i K)
    (hF : Family K Bs Ds BMs DMs A C GC GV e ia ic)
    (hBs : Stages V GV e Bs) (hDs : Stages V GV e Ds)
    (hBM : MonotoneImages K E Bs) (hDM : MonotoneImages K E Ds)
    (hB : Union K Bs B) (hD : Union K Ds D)
    (hGB : ProductGraph B GV GB) (hGD : ProductGraph D GV GD)
    (hIa : IdentityGraph A ia) (hIb : IdentityGraph B ib) (hIc : IdentityGraph C ic) :
    IsPushout C B D GC GB GD e e e ia ia ib ic := by
  have hAB := (union_subsets hne hF hB hD).1
  refine ⟨?_,?_⟩
  · intro x q fx y hxq hxf
    obtain ⟨hx,rfl⟩ := (hIa x q).mp hxq
    obtain ⟨_,rfl⟩ := (hIa x fx).mp hxf
    exact (hIb x y).trans ((and_congr_left fun _ => ⟨fun _ => hF.2.2.2.2.1 x hx,fun _ => hAB x hx⟩).trans (hIc x y).symm)
  intro Q J GQ uQ b c hQ hGQ hUnit hAssoc hb hc hComm
  obtain ⟨Legs,hL⟩ := exists_family hM hF hBs hB hGB hIa hIc hQ hGQ hUnit hAssoc hb hc hComm
  have hCocone := family_cocone hF hL
  have hCompat := family_compatible hM hF hDs hBM hDM hL
  obtain ⟨lift,hLift,_,hR,hUnique⟩ := ConstructionSubobjectUnion.universal_lift
    hM hE hne hF.2.1 hDM hDs hCocone hCompat hD hGD
  have hAgreeB : Agree B lift b := by
    intro x y hx
    obtain ⟨i,Bi,hi,hBi,hxBi⟩ := (hB x).mp hx
    obtain ⟨Di,hDi,_⟩ := hF.2.1.2 i hi
    obtain ⟨GBi,hGBi,_⟩ := hF.2.2.1.2 i hi
    obtain ⟨GDi,hGDi,_⟩ := hF.2.2.2.1.2 i hi
    obtain ⟨li,hli,_⟩ := hL.1.2 i hi
    have hl := local_at hF.1 hF.2.1 hF.2.2.1 hF.2.2.2.1 ((hL.2 i li).mp hli).2 hBi hDi hGBi hGDi
    have hBD := (hF.2.2.2.2.2 i Bi Di GBi GDi hi hBi hDi hGBi hGDi).2.1
    exact (hR i Di li x y hi hDi hli (hBD x hxBi)).trans (hl.2.1 x y hxBi)
  have hAgreeC : Agree C lift c := by
    obtain ⟨i,hi⟩ := hne
    obtain ⟨li,hli,_⟩ := hL.1.2 i hi
    obtain ⟨Bi,Di,GBi,GDi,hBi,hDi,hGBi,hGDi,_,_,hlC,_⟩ := ((hL.2 i li).mp hli).2
    have hCD := (hF.2.2.2.2.2 i Bi Di GBi GDi hi hBi hDi hGBi hGDi).2.2.1
    intro x y hx
    exact (hR i Di li x y hi hDi hli (hCD x hx)).trans (hlC x y hx)
  refine ⟨lift,hLift,node_of_agree hIb hb.1 hAgreeB,node_of_agree hIc hc.1 hAgreeC,?_⟩
  intro other hOther hOtherB hOtherC
  apply hUnique other hOther
  intro i Di li x y hi hDi hli hx
  obtain ⟨Bi,Dii,GBi,GDi,hBi,hDii,hGBi,hGDi,_,_,_,hLocalUnique⟩ := ((hL.2 i li).mp hli).2
  have eD := function_unique hF.2.1 hDi hDii
  subst Dii
  obtain ⟨_,hBD,hCD,_,hPD,_⟩ := hF.2.2.2.2.2 i Bi Di GBi GDi hi hBi hDi hGBi hGDi
  obtain ⟨r,hr,hrEq⟩ := restrict_hom hM (fun z hz => (hD z).mpr ⟨i,Di,hi,hDi,hz⟩)
    (hDs i Di hDi).2.1 hPD hGD hOther
  have hRB : Agree Bi r b := by
    intro z q hz
    have hzB := (hB z).mpr ⟨i,Bi,hi,hBi,hz⟩
    exact (hrEq z q).trans ⟨fun h => (agree_of_node hIb hOtherB z q hzB).mp h.2,
      fun h => ⟨hBD z hz,(agree_of_node hIb hOtherB z q hzB).mpr h⟩⟩
  have hRC : Agree C r c := by
    intro z q hz
    exact (hrEq z q).trans ⟨fun h => (agree_of_node hIc hOtherC z q hz).mp h.2,
      fun h => ⟨hCD z hz,(agree_of_node hIc hOtherC z q hz).mpr h⟩⟩
  have er := hLocalUnique r hr hRB hRC
  subst r
  exact ⟨fun h => (hrEq x y).mpr ⟨hx,h⟩,fun h => ((hrEq x y).mp h).2⟩

/-- Reuse the existing conservative-subobject inclusion theorem. -/
theorem base_inclusion {V GV e S PS GS iS D PD GD iD : M.Carrier .set}
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins V GV)
    (hS : Base V GV e S PS GS iS) (hD : Base V GV e D PD GD iD) (hSub : Subset S D) :
    Hom S D GS GD e e iS ∧ Conservative S D GS GD iS := by
  obtain ⟨hClosedS,_,_,hGS,_,_,hIdS,hHomS,_,_⟩ := hS
  obtain ⟨hClosedD,_,_,hGD,hMD,hCD,_,_,_,hJD⟩ := hD
  have hClosed := ConstructionSelectedCellRestriction.cut_closed hv hc hJ hClosedD hGD hClosedS
    (fun x => ⟨fun hx => ⟨hx,hSub x hx⟩,And.left⟩)
  exact ConstructionCellRestriction.identity_inclusion hMD hCD hJD hClosed
    (ConstructionCellRestriction.product_factor hGS hGD hSub) hHomS.1.1 hIdS

/-- Full source Square: four actual typed conservative inclusions plus pushout. -/
def Square (A B C D GA GB GC GD e ia ib ic : M.Carrier .set) : Prop :=
  Subset A B ∧ Subset A C ∧ Subset B D ∧ Subset C D ∧
  Hom A B GA GB e e ia ∧ Conservative A B GA GB ia ∧
  Hom A C GA GC e e ia ∧ Conservative A C GA GC ia ∧
  Hom B D GB GD e e ib ∧ Conservative B D GB GD ib ∧
  Hom C D GC GD e e ic ∧ Conservative C D GC GD ic ∧
  IsPushout C B D GC GB GD e e e ia ia ib ic

theorem union_square (hM : FirstOrder.Theory.Models M nativeZF)
    {V GV e K E Bs Ds BMs DMs A B C D PA PB PC PD GA GB GC GD ia ib ic idD : M.Carrier .set}
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins V GV)
    (hE : IndexLaws K E) (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i K)
    (hF : Family K Bs Ds BMs DMs A C GC GV e ia ic)
    (hBs : Stages V GV e Bs) (hDs : Stages V GV e Ds)
    (hBM : MonotoneImages K E Bs) (hDM : MonotoneImages K E Ds)
    (hB : Union K Bs B) (hD : Union K Ds D)
    (hBaseA : Base V GV e A PA GA ia) (hBaseB : Base V GV e B PB GB ib)
    (hBaseC : Base V GV e C PC GC ic) (hBaseD : Base V GV e D PD GD idD) :
    Square A B C D GA GB GC GD e ia ib ic := by
  obtain ⟨hAB,hAC,hBD,hCD⟩ := union_subsets hne hF hB hD
  obtain ⟨homAB,consAB⟩ := base_inclusion hv hc hJ hBaseA hBaseB hAB
  obtain ⟨homAC,consAC⟩ := base_inclusion hv hc hJ hBaseA hBaseC hAC
  obtain ⟨homBD,consBD⟩ := base_inclusion hv hc hJ hBaseB hBaseD hBD
  obtain ⟨homCD,consCD⟩ := base_inclusion hv hc hJ hBaseC hBaseD hCD
  refine ⟨hAB,hAC,hBD,hCD,homAB,consAB,homAC,consAC,homBD,consBD,homCD,consCD,?_⟩
  exact union_pushout hM hE hne hF hBs hDs hBM hDM hB hD
    hBaseB.2.2.2.1 hBaseD.2.2.2.1 hBaseA.2.2.2.2.2.2.1 hBaseB.2.2.2.2.2.2.1 hBaseC.2.2.2.2.2.2.1

def family {m : Nat} (K Bs Ds BMs DMs A C GC GV e ia ic : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn Bs K)) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.functionOn Ds K)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn BMs K)) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.functionOn DMs K)) (.conj (Project.Formula.subset (.bound A) (.bound
  C)) (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 4) (.bound K.succ.succ.succ.succ.succ))
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Bs.succ.succ.succ.succ.succ 4 3)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Ds.succ.succ.succ.succ.succ 4 2)) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge BMs.succ.succ.succ.succ.succ 4 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  DMs.succ.succ.succ.succ.succ 4 0)) (.conj (Project.Formula.subset (.bound A.succ.succ.succ.succ.succ) (.bound 3))
  (.conj (Project.Formula.subset (.bound 3) (.bound 2)) (.conj (Project.Formula.subset (.bound
  C.succ.succ.succ.succ.succ) (.bound 2)) (.conj (ConstructionConservativeHull.productGraph 3
  GV.succ.succ.succ.succ.succ 1) (.conj (ConstructionConservativeHull.productGraph 2 GV.succ.succ.succ.succ.succ 0)
  (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn 0 4)) (.conj (ProjectSyntax.encode id
  (ForcingConditionGraphs.identityGraph 4 0)) (ConstructionProbePushoutSyntax.isPushout
  C.succ.succ.succ.succ.succ.succ 4 3 GC.succ.succ.succ.succ.succ.succ 2 1 e.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ ia.succ.succ.succ.succ.succ.succ
  ia.succ.succ.succ.succ.succ.succ 0 ic.succ.succ.succ.succ.succ.succ))))))))))))))))))))))))

theorem family_freeClosed {m : Nat} (K Bs Ds BMs DMs A C GC GV e ia ic : Fin m) :
    (family K Bs Ds BMs DMs A C GC GV e ia ic).FreeClosed := by
  simp -implicitDefEqProofs [family,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.subset,ConstructionConservativeHull.productGraph_freeClosed,ConstructionProbePushoutSyntax.isPushout_freeClosed]

theorem family_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (K Bs Ds BMs DMs A C GC GV e ia ic : Fin m) :
    Project.Formula.satisfies env (family K Bs Ds BMs DMs A C GC GV e ia ic) ↔ Family (env.bound K) (env.bound Bs) (env.bound Ds) (env.bound BMs) (env.bound DMs) (env.bound A) (env.bound C) (env.bound GC) (env.bound GV) (env.bound e) (env.bound ia) (env.bound ic) := by
  simp only [family,Family,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConditionGraphs.functionOn_semantics (M := M),ForcingConditionGraphs.identityGraph_semantics (M := M),KuratowskiZF.source_edge,ConstructionConservativeHull.productGraph_semantics hM,ConstructionProbePushoutSyntax.isPushout_semantics hM]
  rfl

def square {m : Nat} (A B C D GA GB GC GD e ia ib ic : Fin m) : Project.Formula 1 m :=
  (.conj (Project.Formula.subset (.bound A) (.bound B)) (.conj (Project.Formula.subset (.bound A) (.bound C)) (.conj
  (Project.Formula.subset (.bound B) (.bound D)) (.conj (Project.Formula.subset (.bound C) (.bound D)) (.conj
  (ConstructionProbePushoutSyntax.hom A B GA GB e e ia) (.conj (ConstructionProbeConservativeSyntax.conservative A B
  GA GB ia) (.conj (ConstructionProbePushoutSyntax.hom A C GA GC e e ia) (.conj
  (ConstructionProbeConservativeSyntax.conservative A C GA GC ia) (.conj (ConstructionProbePushoutSyntax.hom B D GB GD
  e e ib) (.conj (ConstructionProbeConservativeSyntax.conservative B D GB GD ib) (.conj
  (ConstructionProbePushoutSyntax.hom C D GC GD e e ic) (.conj (ConstructionProbeConservativeSyntax.conservative C D
  GC GD ic) (ConstructionProbePushoutSyntax.isPushout C B D GC GB GD e e e ia ia ib ic)))))))))))))

theorem square_freeClosed {m : Nat} (A B C D GA GB GC GD e ia ib ic : Fin m) :
    (square A B C D GA GB GC GD e ia ib ic).FreeClosed := by
  simp -implicitDefEqProofs [square,Definitional.Formula.FreeClosed,Project.Formula.subset,ConstructionProbePushoutSyntax.hom_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,ConstructionProbePushoutSyntax.isPushout_freeClosed]

theorem square_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (A B C D GA GB GC GD e ia ib ic : Fin m) :
    Project.Formula.satisfies env (square A B C D GA GB GC GD e ia ib ic) ↔ Square (env.bound A) (env.bound B) (env.bound C) (env.bound D) (env.bound GA) (env.bound GB) (env.bound GC) (env.bound GD) (env.bound e) (env.bound ia) (env.bound ib) (env.bound ic) := by
  simp only [square,Square,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,ConstructionProbePushoutSyntax.hom_semantics hM,ConstructionProbeConservativeSyntax.conservative_semantics hM,ConstructionProbePushoutSyntax.isPushout_semantics hM]

/-- Native pure-set sentence for the pinned Square.union, with every source edge. -/
def unionSentence {m : Nat} (V GV e K E Bs Ds BMs DMs A B C D PA PB PC PD GA GB GC GD ia ib ic idD : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.conical V GV e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV) (.imp
    (ConstructionDirectedSystem.indexLaws K E) (.imp (.existsE (.mem (.bound 0) (.bound K.succ))) (.imp (family K Bs Ds
    BMs DMs A C GC GV e ia ic) (.imp (ConstructionCellRestriction.stages V GV e Bs) (.imp
    (ConstructionCellRestriction.stages V GV e Ds) (.imp (ConstructionBlockStages.monotoneImages K E Bs) (.imp
    (ConstructionBlockStages.monotoneImages K E Ds) (.imp (ConstructionSubobjectUnion.unionFormula K Bs B) (.imp
    (ConstructionSubobjectUnion.unionFormula K Ds D) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e A PA
    GA ia) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e B PB GB ib) (.imp
    (ConstructionSelectedCellRestriction.baseFormula V GV e C PC GC ic) (.imp
    (ConstructionSelectedCellRestriction.baseFormula V GV e D PD GD idD) (square A B C D GA GB GC GD e ia ib
    ic)))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionDirectedSystem.indexLaws_freeClosed,family_freeClosed,ConstructionCellRestriction.stages_freeClosed,ConstructionBlockStages.monotoneImages_freeClosed,ConstructionSubobjectUnion.unionFormula_freeClosed,ConstructionSelectedCellRestriction.baseFormula_freeClosed,square_freeClosed]

theorem union_models {m : Nat} (V GV e K E Bs Ds BMs DMs A B C D PA PB PC PD GA GB GC GD ia ib ic idD : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (unionSentence V GV e K E Bs Ds BMs DMs A B C D PA PB PC PD GA GB GC GD ia ib ic idD)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (unionSentence V GV e K E Bs Ds BMs DMs A B C D PA PB PC PD GA GB GC GD ia ib ic idD)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionDirectedSystem.indexLaws_semantics hM,family_semantics hM,ConstructionCellRestriction.stages_semantics hM,ConstructionBlockStages.monotoneImages_semantics hM,ConstructionSubobjectUnion.unionFormula_semantics hM,ConstructionSelectedCellRestriction.baseFormula_semantics hM,square_semantics hM]
  exact union_square hM

theorem union_kernel_certificate {m : Nat} (V GV e K E Bs Ds BMs DMs A B C D PA PB PC PD GA GB GC GD ia ib ic idD : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (unionSentence V GV e K E Bs Ds BMs DMs A B C D PA PB PC PD GA GB GC GD ia ib ic idD)) :=
  ModelTransfer.derives (fun _ hM => union_models V GV e K E Bs Ds BMs DMs A B C D PA PB PC PD GA GB GC GD ia ib ic idD hM)

end PPAC.Migration.ConstructionUnionPushout
