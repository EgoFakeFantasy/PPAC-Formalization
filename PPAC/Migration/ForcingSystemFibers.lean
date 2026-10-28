/- Pinned AvailableRecords.restrict_range_iff/available_sub_iff/availability_sub/
Fiber/fiberRestrict_bijective:385-467. Actual restriction maps on exact fibers,
using existing System laws, availability, ideal contraction and reconstruction.
No independent chosen fiber bijection or assigned ideal is substituted. -/
import PPAC.Migration.ForcingSystemAvailability

namespace PPAC.Migration.ForcingSystemFibers
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingSupportSize (MapsTo Injection)
open ForcingDiagramOrder (Sub Product)
open ForcingDiagramPoset (LeftCancelMonoid)
open ConstructionIdealProbes (ConeIdeal)
open ConstructionIdealContraction (Contract)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ForcingSystemAvailability (Available Carrier)
open ForcingProductSymmetry (orderFormula)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem available_iff_at_sub (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul diagrams objImage objects S mapImage maps r s Os n z f x : M.Carrier .set}
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams)
    (hObj : MapsTo diagrams objImage objects) (hMaps : MapsTo S mapImage maps)
    (hs : PureKuratowski.PairMember M s Os objects) (hSub : Sub D mul r n s)
    (hz : PureKuratowski.Code M z s r) (hf : PureKuratowski.PairMember M z f maps) :
    Available D mul objects maps r x n ↔
      ∃ y, (Project.FirstOrderSemantics.reduct M).mem y Os ∧ PureKuratowski.PairMember M y x f := by
  constructor
  · rintro ⟨s',Os',z',f',y,hSub',hs',hz',hf',hy,hyx⟩
    have hsi := (hDiagrams s).mp (ForcingConditionGraphs.function_input hObj.1 hs)
    have hsi' := (hDiagrams s').mp (ForcingConditionGraphs.function_input hObj.1 hs')
    have es := ConstructionComponentVertices.sub_eq hM hsi hsi' hSub hSub'
    subst s'
    have eO := ForcingConditionGraphs.function_unique hObj.1 hs hs'
    subst Os'
    have ez := KuratowskiZF.code_unique hM hz hz'
    subst z'
    have ef := ForcingConditionGraphs.function_unique hMaps.1 hf hf'
    subst f'
    exact ⟨y,hy,hyx⟩
  · rintro ⟨y,hy,hyx⟩
    exact ⟨s,Os,z,f,y,hSub,hs,hz,hf,hy,hyx⟩

theorem available_sub_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e diagrams objImage objects S mapImage maps r s Or Os n m nm z f y x : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams)
    (hObj : MapsTo diagrams objImage objects)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S)
    (hMaps : MapsTo S mapImage maps) (hSys : ForcingEligibleSystem.System D objects maps)
    (hr : PureKuratowski.PairMember M r Or objects) (hs : PureKuratowski.PairMember M s Os objects)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n D)
    (hmD : (Project.FirstOrderSemantics.reduct M).mem m D) (hnm : Product mul n m nm)
    (hSub : Sub D mul r n s) (hz : PureKuratowski.Code M z s r)
    (hf : PureKuratowski.PairMember M z f maps) (hyx : PureKuratowski.PairMember M y x f) :
    Available D mul objects maps s y m ↔ Available D mul objects maps r x nm := by
  have hsI := (hDiagrams s).mp (ForcingConditionGraphs.function_input hObj.1 hs)
  obtain ⟨t,htI,hT⟩ := ForcingDiagramOrder.exists_sub hM (hm.2.1 m hmD) hsI
  obtain ⟨Ot,hOt,_⟩ := hObj.1.2 t ((hDiagrams t).mpr htI)
  have hRT := ForcingDiagramPoset.sub_sub hm hn hmD hnm hSub hT
  have hnmD := ConstructionProbeTransitions.product_closed hm hn hmD hnm
  obtain ⟨zt,g,hzt,hg,_⟩ := ForcingSystemAvailability.exists_map hM hObj hS hMaps hSys hs hOt ⟨m,hmD,hT⟩
  obtain ⟨zr,h,hzr,hh,_⟩ := ForcingSystemAvailability.exists_map hM hObj hS hMaps hSys hr hOt ⟨nm,hnmD,hRT⟩
  rw [available_iff_at_sub hM hDiagrams hObj hMaps hOt hT hzt hg,
    available_iff_at_sub hM hDiagrams hObj hMaps hOt hRT hzr hh]
  have hcomp := hSys.2.2.1 t s r Ot Os Or zt z zr g f h hOt hs hr hzt hz hzr hg hf hh
  have hinj := (hSys.2.2.2.1 s r Os Or z f hs hr hz hf).2
  constructor
  · rintro ⟨v,hv,hvy⟩
    exact ⟨v,hv,(hcomp v x).mpr ⟨hv,y,hvy,hyx⟩⟩
  · rintro ⟨v,hv,hvx⟩
    obtain ⟨_,w,hvw,hwx⟩ := (hcomp v x).mp hvx
    exact ⟨v,hv,(hinj w y x hwx hyx) ▸ hvw⟩

theorem availability_sub (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e diagrams objImage objects S mapImage maps r s Or Os a n c z f y x U V : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams)
    (hObj : MapsTo diagrams objImage objects)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S)
    (hMaps : MapsTo S mapImage maps) (hSys : ForcingEligibleSystem.System D objects maps)
    (hr : PureKuratowski.PairMember M r Or objects) (hs : PureKuratowski.PairMember M s Os objects)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n D)
    (hc : (Project.FirstOrderSemantics.reduct M).mem c D) (hnc : Product mul n c a)
    (hSub : Sub D mul r n s) (hz : PureKuratowski.Code M z s r)
    (hf : PureKuratowski.PairMember M z f maps) (hyx : PureKuratowski.PairMember M y x f)
    (hU : Carrier D mul objects maps r x a U) (hV : Carrier D mul objects maps s y c V) :
    Contract D mul n U V := by
  intro m
  constructor
  · intro hmV
    obtain ⟨hmD,hmc,hmAvail⟩ := (hV m).mp hmV
    obtain ⟨nm,hnmD,hnm⟩ := (hm.2.1 n hn).1 m hmD
    exact ⟨hmD,nm,hnm,(hU nm).mpr ⟨hnmD,
      (ConstructionProbeConditionalJoins.left_mul_dvd_iff hm hn hmD hc hnm hnc).mpr hmc,
      (available_sub_iff hM hm hDiagrams hObj hS hMaps hSys hr hs hn hmD hnm hSub hz hf hyx).mp hmAvail⟩⟩
  · rintro ⟨hmD,nm,hnm,hnmU⟩
    obtain ⟨_,hnma,hnmAvail⟩ := (hU nm).mp hnmU
    exact (hV m).mpr ⟨hmD,
      (ConstructionProbeConditionalJoins.left_mul_dvd_iff hm hn hmD hc hnm hnc).mp hnma,
      (available_sub_iff hM hm hDiagrams hObj hS hMaps hSys hr hs hn hmD hnm hSub hz hf hyx).mpr hnmAvail⟩

def Fiber (D mul objects maps r Or a U X : M.Carrier .set) : Prop :=
  ∀ x, (Project.FirstOrderSemantics.reduct M).mem x X ↔
    (Project.FirstOrderSemantics.reduct M).mem x Or ∧ Carrier D mul objects maps r x a U

def fiber {m : Nat} (D mul objects maps r Or a U X : Fin m) : Formula m :=
  .all ((Formula.mem (Fin.last m) X.castSucc).iff ((Formula.mem (Fin.last m) Or.castSucc).conj
    (ForcingSystemAvailability.carrier D.castSucc mul.castSucc objects.castSucc maps.castSucc
      r.castSucc (Fin.last m) a.castSucc U.castSucc)))

theorem fiber_semantics {m : Nat} (env : Fin m → M.Carrier .set) (D mul objects maps r Or a U X : Fin m) :
    Formula.Realize (Project.FirstOrderSemantics.reduct M).mem env (fiber D mul objects maps r Or a U X) ↔
      Fiber (env D) (env mul) (env objects) (env maps) (env r) (env Or) (env a) (env U) (env X) := by
  simp only [fiber,Fiber,Source.Formula.iff,Formula.Realize,ForcingSystemAvailability.carrier_semantics (M := M),
    Fin.lastCases_last,Fin.lastCases_castSucc]
  exact ⟨fun h x => ⟨(h x).1,(h x).2⟩,fun h x => ⟨(h x).mp,(h x).mpr⟩⟩

theorem exists_fiber (hM : FirstOrder.Theory.Models M nativeZF)
    (D mul objects maps r Or a U : M.Carrier .set) :
    ∃ X, Fiber D mul objects maps r Or a U X := by
  let schema : Project.UnarySchema 7 := {
    body := ProjectSyntax.encode id (ForcingSystemAvailability.carrier (1 : Fin 8) 2 3 4 5 0 6 7)
    freeClosed := ProjectSyntax.freeClosed _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 7 := {
    bound := Fin.cases D (Fin.cases mul (Fin.cases objects (Fin.cases maps (Fin.cases r (Fin.cases a (fun _ => U)))))),
    free := fun _ => Or }
  obtain ⟨X,hX⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env Or
  refine ⟨X,fun x => ?_⟩
  simpa only [schema,env,Project.UnarySchema.denote,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSystemAvailability.carrier_semantics (M := M)] using! hX x

theorem fiber_bijection (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e diagrams objImage objects S mapImage maps r s Or Os a n c z f U V X Y : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hJ : ConditionalJoins D mul)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams)
    (hObj : MapsTo diagrams objImage objects)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S)
    (hMaps : MapsTo S mapImage maps) (hSys : ForcingEligibleSystem.System D objects maps)
    (hr : PureKuratowski.PairMember M r Or objects) (hs : PureKuratowski.PairMember M s Os objects)
    (hc : (Project.FirstOrderSemantics.reduct M).mem c D) (hnc : Product mul n c a)
    (hSub : Sub D mul r n s) (hz : PureKuratowski.Code M z s r)
    (hf : PureKuratowski.PairMember M z f maps)
    (hU : ConeIdeal D mul a U) (hnU : (Project.FirstOrderSemantics.reduct M).mem n U)
    (hV : Contract D mul n U V)
    (hX : Fiber D mul objects maps r Or a U X) (hY : Fiber D mul objects maps s Os c V Y) :
    ∃ b, Injection Y X b ∧ ForcingEligibleRestriction.Restricts b f Y ∧
      ∀ x, (Project.FirstOrderSemantics.reduct M).mem x X →
        ∃ y, (Project.FirstOrderSemantics.reduct M).mem y Y ∧ PureKuratowski.PairMember M y x b := by
  have hn := hU.1 n hnU
  have hMap := hSys.1 s r Os Or z f hs hr hz hf
  have hInj := hSys.2.2.2.1 s r Os Or z f hs hr hz hf
  have hImage : ∀ y x, (Project.FirstOrderSemantics.reduct M).mem y Y →
      PureKuratowski.PairMember M y x f → (Project.FirstOrderSemantics.reduct M).mem x X := by
    intro y x hy hyx
    obtain ⟨hyOs,hVy⟩ := (hY y).mp hy
    have hxOr := hMap.2 y x hyx
    obtain ⟨Ux,hUx⟩ := ForcingSystemAvailability.exists_carrier hM D mul objects maps r x a
    have hUxIdeal := ForcingSystemAvailability.carrier_ideal hM hm hDiagrams hObj hS hMaps hSys hr hxOr hU.2.1 hUx
    have hnUx := (hUx n).mpr ⟨hn,⟨c,hc,hnc⟩,s,Os,z,f,y,hSub,hs,hz,hf,hyOs,hyx⟩
    have hContract := availability_sub hM hm hDiagrams hObj hS hMaps hSys hr hs hn hc hnc hSub hz hf hyx hUx hVy
    have he := ConstructionIdealContraction.eq_of_contract_eq hM hm hJ hUxIdeal hU hnUx hnU hContract hV rfl
    exact (hX x).mpr ⟨hxOr,he ▸ hUx⟩
  obtain ⟨b,hb⟩ := ZF.exists_restriction (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) f Y
  have hEdge : ForcingEligibleRestriction.Restricts b f Y := fun x y => (hb.2 x y).trans and_comm
  have hB : MapsTo Y X b := by
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro row hrow
      obtain ⟨y,x,hcode⟩ := hb.1 row hrow
      exact ⟨y,x,((hb.2 y x).mp ⟨row,hcode,hrow⟩).1,hcode⟩
    · intro y hy
      obtain ⟨x,hyx,_⟩ := hMap.1.2 y ((hY y).mp hy).1
      exact ⟨x,(hEdge y x).mpr ⟨hyx,hy⟩,
        fun x' hx' => ForcingConditionGraphs.function_unique hMap.1 ((hEdge y x').mp hx').1 hyx⟩
    · intro y x hyx
      obtain ⟨hyx,hy⟩ := (hEdge y x).mp hyx
      exact hImage y x hy hyx
  refine ⟨b,ForcingEligibleRestriction.restrict_injective hInj hEdge hB,hEdge,?_⟩
  intro x hx
  obtain ⟨_,hUx⟩ := (hX x).mp hx
  have hnAvail := ((hUx n).mp hnU).2.2
  obtain ⟨y,hy,hyx⟩ := (available_iff_at_sub hM hDiagrams hObj hMaps hs hSub hz hf).mp hnAvail
  obtain ⟨Vy,hVy⟩ := ForcingSystemAvailability.exists_carrier hM D mul objects maps s y c
  have hContract := availability_sub hM hm hDiagrams hObj hS hMaps hSys hr hs hn hc hnc hSub hz hf hyx hUx hVy
  have he := ConstructionIdealContraction.contract_unique hM hV hContract
  have hyY := (hY y).mpr ⟨hy,he.symm ▸ hVy⟩
  exact ⟨y,hyY,(hEdge y x).mpr ⟨hyx,hyY⟩⟩

def AllFibers (D mul objects maps : M.Carrier .set) : Prop :=
  ∀ r s Or Os a n c U z f, PureKuratowski.PairMember M r Or objects →
    PureKuratowski.PairMember M s Os objects →
    (Project.FirstOrderSemantics.reduct M).mem c D → Product mul n c a → Sub D mul r n s →
    PureKuratowski.Code M z s r → PureKuratowski.PairMember M z f maps →
    ConeIdeal D mul a U → (Project.FirstOrderSemantics.reduct M).mem n U →
    ∃ V X Y b, Contract D mul n U V ∧ Fiber D mul objects maps r Or a U X ∧
      Fiber D mul objects maps s Os c V Y ∧ Injection Y X b ∧
      ForcingEligibleRestriction.Restricts b f Y ∧
      ∀ x, (Project.FirstOrderSemantics.reduct M).mem x X →
        ∃ y, (Project.FirstOrderSemantics.reduct M).mem y Y ∧ PureKuratowski.PairMember M y x b

theorem all_fibers (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e diagrams objImage objects S mapImage maps : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hJ : ConditionalJoins D mul)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams)
    (hObj : MapsTo diagrams objImage objects)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S)
    (hMaps : MapsTo S mapImage maps) (hSys : ForcingEligibleSystem.System D objects maps) :
    AllFibers D mul objects maps := by
  intro r s Or Os a n c U z f hr hs hc hnc hSub hz hf hU hnU
  obtain ⟨V,hV⟩ := ConstructionIdealContraction.exists_contract hM D mul n U
  obtain ⟨X,hX⟩ := exists_fiber hM D mul objects maps r Or a U
  obtain ⟨Y,hY⟩ := exists_fiber hM D mul objects maps s Os c V
  obtain ⟨b,hb,hEdge,hOnto⟩ := fiber_bijection hM hm hJ hDiagrams hObj hS hMaps hSys hr hs hc hnc hSub hz hf hU hnU hV hX hY
  exact ⟨V,X,Y,b,hV,hX,hY,hb,hEdge,hOnto⟩

def allFibers {m : Nat} (D mul objects maps : Fin m) : Project.Formula 1 m :=
  let up : Fin m → Fin (m+10) := fun i => i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  let r : Fin (m+10) := 9
  let s : Fin (m+10) := 8
  let Or : Fin (m+10) := 7
  let Os : Fin (m+10) := 6
  let a : Fin (m+10) := 5
  let n : Fin (m+10) := 4
  let c : Fin (m+10) := 3
  let U : Fin (m+10) := 2
  let z : Fin (m+10) := 1
  let f : Fin (m+10) := 0
  let V : Fin (m+14) := 3
  let X : Fin (m+14) := 2
  let Y : Fin (m+14) := 1
  let b : Fin (m+14) := 0
  .forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE ((.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up objects) r Or)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up objects) s Os)) (.imp (.mem (.bound c) (.bound (up D))) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product (up mul) n c a)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (up D) (up mul) r n s)) (.imp (ProjectSyntax.encode id (PairSyntax.ordered z s r)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (up maps) z f)) (.imp (ConstructionIdealProbes.coneIdeal (up D) (up mul) a U) (.imp (.mem (.bound n) (.bound U)) (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionIdealContraction.contract ((up D)).succ.succ.succ.succ ((up mul)).succ.succ.succ.succ (n).succ.succ.succ.succ (U).succ.succ.succ.succ V) (.conj (ProjectSyntax.encode id (fiber ((up D)).succ.succ.succ.succ ((up mul)).succ.succ.succ.succ ((up objects)).succ.succ.succ.succ ((up maps)).succ.succ.succ.succ (r).succ.succ.succ.succ (Or).succ.succ.succ.succ (a).succ.succ.succ.succ (U).succ.succ.succ.succ X)) (.conj (ProjectSyntax.encode id (fiber ((up D)).succ.succ.succ.succ ((up mul)).succ.succ.succ.succ ((up objects)).succ.succ.succ.succ ((up maps)).succ.succ.succ.succ (s).succ.succ.succ.succ (Os).succ.succ.succ.succ (c).succ.succ.succ.succ V Y)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection b Y X)) (.conj (ProjectSyntax.encode id (RestrictionSyntax.edgeLaw b (f).succ.succ.succ.succ Y)) (.forallE (.imp (.mem (.bound 0) (.bound X.succ)) (.existsE (.conj (.mem (.bound 0) (.bound Y.succ.succ)) (ProjectSyntax.encode id (Source.SetLanguage.edge b.succ.succ 0 1))))))))))))))))))))))))))))))))))

theorem allFibers_freeClosed {m : Nat} (D mul objects maps : Fin m) :
    (allFibers D mul objects maps).FreeClosed := by
  simp -implicitDefEqProofs [allFibers,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionIdealProbes.coneIdeal_freeClosed,ConstructionIdealContraction.contract_freeClosed]

theorem allFibers_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul objects maps : Fin m) :
    Project.Formula.satisfies env (allFibers D mul objects maps) ↔
      AllFibers (env.bound D) (env.bound mul) (env.bound objects) (env.bound maps) := by
  simp only [allFibers,AllFibers,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,KuratowskiZF.source_code,
    ForcingDiagramOrder.product_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    ConstructionIdealProbes.coneIdeal_semantics hM,ConstructionIdealContraction.contract_semantics hM,
    fiber_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingEligibleRestriction.edgeLaw_semantics (M := M),Project.Term.eval_bound]
  rfl

def systemSentence {k : Nat} (D I mul e diagrams objImage objects S mapImage maps : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier D I diagrams)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage)) (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows D mul diagrams S)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps S mapImage)) (.imp (ForcingEligibleSystem.system D objects maps) (allFibers D mul objects maps))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,
      ForcingEligibleSystem.system_freeClosed,allFibers_freeClosed]

theorem system_models {k : Nat} (D I mul e diagrams objImage objects S mapImage maps : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (systemSentence D I mul e diagrams objImage objects S mapImage maps)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (systemSentence D I mul e diagrams objImage objects S mapImage maps)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingEligibleMapFamily.arrows_semantics (M := M),
    ForcingEligibleSystem.system_semantics hM,allFibers_semantics hM]
  exact fun hm hJ hDiagrams hObj hS hMaps hSys => all_fibers hM hm hJ hDiagrams hObj hS hMaps hSys

theorem system_kernel_certificate {k : Nat} (D I mul e diagrams objImage objects S mapImage maps : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (systemSentence D I mul e diagrams objImage objects S mapImage maps)) :=
  ModelTransfer.derives (fun _ hM => system_models D I mul e diagrams objImage objects S mapImage maps hM)

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E : Fin k) : Project.Sentence where
  formula :=
    let up : Fin k → Fin (k+5) := fun i => i.succ.succ.succ.succ.succ
    let objImage : Fin (k+5) := 4
    let objects : Fin (k+5) := 3
    let S : Fin (k+5) := 2
    let mapImage : Fin (k+5) := 1
    let maps : Fin (k+5) := 0
    Project.Formula.forallClosure k
      (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w) (.bound mu)) (.imp (ConstructionSaturationIndex.hartogs mu I) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (rho 0) mu)) (.imp (ConstructionSaturationMergers.allMergers w history kappa) (.imp (ConstructionTowerHistory.row history kappa (rho 0) mul e mark H C incoming base kappa) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins (rho 0) mul) (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6))) (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.carrier I G)) (.imp (ProjectSyntax.encode id (ForcingSupportFilter.filter I G mu F)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn c K)) (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty t)) (.imp (ProjectSyntax.encode id (ForcingLabelSet.labelSet (rho 6) I K c t b labels)) (.imp (ProjectSyntax.encode id (ForcingLabelBound.labelBound (rho 6) I K c t b nameBound)) (.imp (ProjectSyntax.encode id (ForcingLocalAtomic.cohenFilter (rho 3) g)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q (rho 0) I)) (.imp (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0) q Aq)) (.imp (ProjectSyntax.encode id (ForcingLabelPermutations.fixing G Aq fixingQ)) (.imp (ProjectSyntax.encode id (ForcingEquivariantMix.fixedAll rho fixingQ E)) (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects (up (rho 4)) objImage)) (.conj (ProjectSyntax.encode id (ForcingEligibleFamily.family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) up (fun i => up (rho i)) (up G) (up F) (up mul) (up g) (up q) (up nameBound) (up labels) (up E) (up (rho 4)) objects)) (.conj (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows (up (rho 0)) (up mul) (up (rho 4)) S)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps S mapImage)) (.conj (ProjectSyntax.encode id (ForcingEligibleMapFamily.family (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) up (fun i => up (rho i)) (up G) (up F) (up mul) (up g) (up q) (up nameBound) (up labels) (up E) S maps)) (.conj (ForcingEligibleSystem.system (up (rho 0)) objects maps) (.conj (ForcingSystemAvailability.allIdeals (up (rho 0)) (up mul) objects maps) (allFibers (up (rho 0)) (up mul) objects maps)))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      Project.Formula.isOmega,Project.Formula.isInfiniteCardinal,
      ConstructionSaturationIndex.hartogs_freeClosed,ProjectSyntax.freeClosed,
      ConstructionSaturationMergers.allMergers_freeClosed,ConstructionTowerHistory.row_freeClosed,
      ForcingEligibleSystem.system_freeClosed,ForcingSystemAvailability.allIdeals_freeClosed,allFibers_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionSaturationIndex.hartogs_semantics hM,
    ForcingSupportSize.small_semantics (M := M),
    ConstructionSaturationMergers.allMergers_semantics hM,
    ConstructionTowerHistory.row_semantics hM,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingProductFamily.presentation_semantics (M := M),
    ForcingLabelPermutations.carrier_semantics (M := M),
    ForcingSupportFilter.filter_semantics (M := M),
    ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingWithTopCarrier.empty_semantics (M := M),
    ForcingLabelSet.labelSet_semantics (M := M),
    ForcingLabelBound.labelBound_semantics (M := M),
    ForcingLocalAtomic.cohenFilter_semantics (M := M),
    ForcingSupportSize.injection_semantics (M := M),
    ForcingSupportedNames.range_semantics (M := M),
    ForcingLabelPermutations.fixing_semantics (M := M),
    ForcingSupportedNames.supported_semantics (M := M),
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingEligibleFamily.family_semantics (M := M),
    ForcingEligibleMapFamily.arrows_semantics (M := M),
    ForcingEligibleMapFamily.family_semantics (M := M),
    ForcingEligibleSystem.system_semantics hM,ForcingSystemAvailability.allIdeals_semantics hM,allFibers_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  intro hw hMu hI hD hMergers hRow hm hJ hp hG hFilter hc ht hLabels hBound hg hq hRangeQ hFixQ hE
  obtain ⟨objImage,objects,hObjMap,hObj⟩ := ForcingEligibleFamily.exists_family hM
    (orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) bound rho G F mul g q nameBound labels E I (rho 4)
    hp.2.2.2.1
  obtain ⟨S,hS⟩ := ForcingEligibleMapFamily.exists_arrows hM bound (rho 0) mul (rho 4)
  obtain ⟨mapImage,maps,hMap,hMaps⟩ := ForcingEligibleMapFamily.exists_family hM bound rho G F mul
    I K B w e g q nameBound labels E S hm hp hg hS
  have hSys := ForcingEligibleSystem.system_of_families hM hChoice bound rho G F mul
    hw hMu hI hD hMergers hRow hm hp hG hFilter hc ht hLabels hBound hg hq hRangeQ hFixQ hE hObj hS hMaps
  exact ⟨objImage,objects,S,mapImage,maps,hObjMap,hObj,hS,hMap,hMaps,hSys,
    ForcingSystemAvailability.all_ideals hM hm hp.2.2.2.1 hObjMap hS hMap hSys,
    all_fibers hM hm hJ hp.2.2.2.1 hObjMap hS hMap hSys⟩

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let zero := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => zero }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence rho w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E)).mp
      (construction_models rho w mu history kappa e mark H C incoming base I K B G F mul c t b labels nameBound g q Aq fixingQ E hL hChoice)


def contractionSentence {k : Nat} (D I mul e diagrams objImage objects S mapImage maps r s Or Os a n c z f y x U V : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e)) (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier D I diagrams)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage)) (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows D mul diagrams S)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps S mapImage)) (.imp (ForcingEligibleSystem.system D objects maps) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge objects r Or)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge objects s Os)) (.imp (.mem (.bound n) (.bound D)) (.imp (.mem (.bound c) (.bound D)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product mul n c a)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub D mul r n s)) (.imp (ProjectSyntax.encode id (PairSyntax.ordered z s r)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge maps z f)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge f y x)) (.imp (ProjectSyntax.encode id (ForcingSystemAvailability.carrier D mul objects maps r x a U)) (.imp (ProjectSyntax.encode id (ForcingSystemAvailability.carrier D mul objects maps s y c V)) (ConstructionIdealContraction.contract D mul n U V))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ForcingEligibleSystem.system_freeClosed,ConstructionIdealContraction.contract_freeClosed]

theorem contraction_models {k : Nat} (D I mul e diagrams objImage objects S mapImage maps r s Or Os a n c z f y x U V : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (contractionSentence D I mul e diagrams objImage objects S mapImage maps r s Or Os a n c z f y x U V)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (contractionSentence D I mul e diagrams objImage objects S mapImage maps r s Or Os a n c z f y x U V)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingEligibleSystem.system_semantics hM,
    KuratowskiZF.source_edge,KuratowskiZF.source_code,
    ForcingDiagramOrder.product_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    ForcingSystemAvailability.carrier_semantics (M := M),ConstructionIdealContraction.contract_semantics hM]
  exact fun hm hDiagrams hObj hS hMaps hSys hr hs hn hc hnc hSub hz hf hyx hU hV =>
    availability_sub hM hm hDiagrams hObj hS hMaps hSys hr hs hn hc hnc hSub hz hf hyx hU hV

theorem contraction_kernel_certificate {k : Nat} (D I mul e diagrams objImage objects S mapImage maps r s Or Os a n c z f y x U V : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (contractionSentence D I mul e diagrams objImage objects S mapImage maps r s Or Os a n c z f y x U V)) :=
  ModelTransfer.derives (fun _ hM => contraction_models D I mul e diagrams objImage objects S mapImage maps r s Or Os a n c z f y x U V hM)

end PPAC.Migration.ForcingSystemFibers
