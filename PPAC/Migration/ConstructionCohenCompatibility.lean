/- Pinned DiagramPlacements.Condition compatibility consumers:400-449.
Actual internal Cohen graphs, labels/support, restriction and moved-copy union.
Reuse native Separation/functions, the existing ordinal image bound and
the existing TWO coordinate lifts; no Choice or new graph backend. -/
import PPAC.Migration.ForcingCohenOrderAction
import PPAC.Migration.ConstructionPlacementTriple
import PPAC.Migration.ExistingOrdinalImage

namespace PPAC.Migration.ConstructionCohenCompatibility
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingCohenCoordinates (Cartesian Graph)
open ForcingCohenConditions (Condition Functional)
open ForcingConditionGraphs (Permutation)
open ForcingSupportSize (Small)
open ConstructionPlacementTriple (ImageAt)
open ConstructionPlacementPasting (AgreesOn)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Label (z i : M.Carrier .set) : Prop :=
  ∃ a k b, PureKuratowski.Code M z a b ∧ PureKuratowski.Code M a i k

def Entry (p i k b : M.Carrier .set) : Prop :=
  ∃ a, PureKuratowski.Code M a i k ∧ PureKuratowski.PairMember M a b p

def Support (p H : M.Carrier .set) : Prop :=
  ∀ i, (Project.FirstOrderSemantics.reduct M).mem i H ↔ ∃ k b, Entry p i k b

def Within (p V : M.Carrier .set) : Prop :=
  ∀ i k b, Entry p i k b → (Project.FirstOrderSemantics.reduct M).mem i V

def Restricted (A p q : M.Carrier .set) : Prop :=
  ∀ z, (Project.FirstOrderSemantics.reduct M).mem z q ↔
    (Project.FirstOrderSemantics.reduct M).mem z p ∧
      ∃ i, Label z i ∧ (Project.FirstOrderSemantics.reduct M).mem i A

def Moved (pi p q : M.Carrier .set) : Prop :=
  ∀ j k b, Entry q j k b ↔ ∃ i, PureKuratowski.PairMember M i j pi ∧ Entry p i k b

def Compatible (p q : M.Carrier .set) : Prop :=
  ∀ a b c, PureKuratowski.PairMember M a b p → PureKuratowski.PairMember M a c q → b = c

def Trigger (pi V c A : M.Carrier .set) : Prop :=
  ∀ j, ImageAt pi V j → (∃ k b, Entry c j k b) → ImageAt pi A j

def Overlap (pi rho V A : M.Carrier .set) : Prop :=
  ∀ j, ImageAt pi V j → ImageAt rho V j → ImageAt pi A j

theorem label_unique {z i j : M.Carrier .set} (hi : Label z i) (hj : Label z j) : i = j := by
  obtain ⟨a,k,b,hz,ha⟩ := hi
  obtain ⟨a',k',b',hz',ha'⟩ := hj
  obtain ⟨rfl,_⟩ := PureKuratowski.code_injective hz hz'
  exact (PureKuratowski.code_injective ha ha').1

theorem label_member {p i : M.Carrier .set} :
    (∃ z, (Project.FirstOrderSemantics.reduct M).mem z p ∧ Label z i) ↔ ∃ k b, Entry p i k b := by
  constructor
  · rintro ⟨z,hz,a,k,b,hCode,hCoord⟩
    exact ⟨k,b,a,hCoord,z,hCode,hz⟩
  · rintro ⟨k,b,a,hCoord,z,hCode,hz⟩
    exact ⟨z,hz,a,k,b,hCode,hCoord⟩

theorem entry_functional (hM : FirstOrder.Theory.Models M nativeZF)
    {p i k b c : M.Carrier .set} (hp : Functional p)
    (hb : Entry p i k b) (hc : Entry p i k c) : b = c := by
  obtain ⟨a,ha,hb⟩ := hb
  obtain ⟨a',ha',hc⟩ := hc
  have he := KuratowskiZF.code_unique hM ha' ha
  exact hp a b c hb (he ▸ hc)

theorem entry_typed {I K C B S w p i k b : M.Carrier .set}
    (hC : Cartesian I K C) (hS : Cartesian C B S) (hp : Condition S w p) (he : Entry p i k b) :
    (Project.FirstOrderSemantics.reduct M).mem i I ∧
      (Project.FirstOrderSemantics.reduct M).mem k K ∧ (Project.FirstOrderSemantics.reduct M).mem b B := by
  obtain ⟨a,ha,z,hz,hzp⟩ := he
  obtain ⟨a',haC,b',hb,hz'⟩ := (hS z).mp (hp.1 z hzp)
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
  obtain ⟨i',hi,k',hk,ha'⟩ := (hC a).mp haC
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective ha ha'
  exact ⟨hi,hk,hb⟩

theorem entries_ext (hM : FirstOrder.Theory.Models M nativeZF)
    {I K C B S w p q : M.Carrier .set} (hC : Cartesian I K C) (hS : Cartesian C B S)
    (hp : Condition S w p) (hq : Condition S w q)
    (he : ∀ i k b, Entry p i k b ↔ Entry q i k b) : p = q := by
  apply (ModelTransfer.extensionality hM).eq_of_same_members p q
  intro z
  have forward {p q : M.Carrier .set} (hp : Condition S w p)
      (he : ∀ i k b, Entry p i k b → Entry q i k b)
      (hz : (Project.FirstOrderSemantics.reduct M).mem z p) :
      (Project.FirstOrderSemantics.reduct M).mem z q := by
    obtain ⟨a,ha,b,hb,hzab⟩ := (hS z).mp (hp.1 z hz)
    obtain ⟨i,hi,k,hk,haik⟩ := (hC a).mp ha
    obtain ⟨a',ha',z',hz',hz'q⟩ := he i k b ⟨a,haik,z,hzab,hz⟩
    have hEqA := KuratowskiZF.code_unique hM ha' haik
    subst a'
    have hEqZ := KuratowskiZF.code_unique hM hz' hzab
    exact hEqZ ▸ hz'q
  exact ⟨forward hp (fun i k b => (he i k b).mp),
    forward hq (fun i k b => (he i k b).mpr)⟩

def label {m : Nat} (z i : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.conj
    (PureKuratowskiProject.code (.bound z.succ.succ.succ) (.bound 2) (.bound 0))
    (PureKuratowskiProject.code (.bound 2) (.bound i.succ.succ.succ) (.bound 1)))))

theorem label_freeClosed {m : Nat} (z i : Fin m) : (label z i).FreeClosed := by
  simp -implicitDefEqProofs [label,Definitional.Formula.FreeClosed,PureKuratowskiProject.code]

theorem label_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (z i : Fin m) :
    Project.Formula.satisfies env (label z i) ↔ Label (env.bound z) (env.bound i) := by
  simp only [label,Label,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    KuratowskiZF.code_correct hM,Project.Term.eval_bound]
  rfl

theorem exists_support (hM : FirstOrder.Theory.Models M nativeZF)
    {I K C B S w p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hC : Cartesian I K C) (hS : Cartesian C B S) (hp : Condition S w p) :
    ∃ H, Support p H ∧ (Project.FirstOrderSemantics.reduct M).MemberSubset H I ∧ Small H w := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 := { bound := fun _ => p, free := fun _ => p }
  let schema : Project.UnarySchema 1 := {
    body := .existsE (.conj (.mem (.bound 0) (.bound 2)) (label 0 1))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,label_freeClosed] }
  obtain ⟨H,hH⟩ := ZF.separation_exists_d hZF schema env I
  have hHMem i : (Project.FirstOrderSemantics.reduct M).mem i H ↔
      (Project.FirstOrderSemantics.reduct M).mem i I ∧ ∃ k b, Entry p i k b := by
    have hSchema : schema.denote env i ↔ ∃ z, (Project.FirstOrderSemantics.reduct M).mem z p ∧ Label z i := by
      simp only [Project.UnarySchema.denote,schema,Project.Formula.satisfies_exists_iff,
        Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,label_semantics hM,Project.Term.eval_bound]
      rfl
    exact (hH i).trans (and_congr Iff.rfl (hSchema.trans label_member))
  have hSupport : Support p H := by
    intro i
    exact ⟨fun h => ((hHMem i).mp h).2,fun h => (hHMem i).mpr ⟨by
      obtain ⟨k,b,he⟩ := h; exact (entry_typed hC hS hp he).1,h⟩⟩
  let emptyEnv : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 0 :=
    { bound := Fin.elim0, free := fun _ => p }
  let projection : Project.BinarySchema 0 := { body := label 1 0, freeClosed := label_freeClosed _ _ }
  have hProjection z i : projection.denote emptyEnv z i ↔ Label z i := by
    simpa only [Project.BinarySchema.denote,projection] using! label_semantics hM ((emptyEnv.push z).push i) 1 0
  have hTotal z (hz : (Project.FirstOrderSemantics.reduct M).mem z p) : ∃ i, Label z i := by
    obtain ⟨a,ha,b,_,hz⟩ := (hS z).mp (hp.1 z hz)
    obtain ⟨i,_,k,_,ha⟩ := (hC a).mp ha
    exact ⟨i,a,k,b,hz,ha⟩
  obtain ⟨F,hF,hEdges⟩ := ZF.exists_setFunctionFromTo_of_denote hZF pair projection emptyEnv
    (source := p) (target := H) (by
      intro z hz; obtain ⟨i,hi⟩ := hTotal z hz; exact ⟨i,(hProjection z i).mpr hi⟩)
    (fun z _ i j hi hj => label_unique ((hProjection z i).mp hi) ((hProjection z j).mp hj))
    (fun z i hz hi => (hSupport i).mpr (label_member.mp ⟨z,hz,(hProjection z i).mp hi⟩))
  have hSurj : (Project.FirstOrderSemantics.reduct M).IsSetSurjectiveOnto pair F p H := by
    intro i hi
    obtain ⟨z,hz,hl⟩ := label_member.mpr ((hSupport i).mp hi)
    exact ⟨z,hz,(hEdges z i).mpr ⟨hz,(hProjection z i).mpr hl⟩⟩
  exact ⟨H,hSupport,fun i hi => ((hHMem i).mp hi).1,
    (ForcingSupportSize.native_small hM H w).mpr
      (ExistingOrdinalImage.ordinal_image_bound_l pair hZF
        (ExistingCardinalBounds.omega_cardinal_l pair hZF hw).1
        ((ForcingSupportSize.native_small hM p w).mp hp.2.2) hF hSurj)⟩

theorem restricted_entry {A p q i k b : M.Carrier .set} (h : Restricted A p q) :
    Entry q i k b ↔ Entry p i k b ∧ (Project.FirstOrderSemantics.reduct M).mem i A := by
  constructor
  · rintro ⟨a,ha,z,hz,hzq⟩
    obtain ⟨hzp,j,hl,hj⟩ := (h z).mp hzq
    have he := label_unique hl ⟨a,k,b,hz,ha⟩
    exact ⟨⟨a,ha,z,hz,hzp⟩,he ▸ hj⟩
  · rintro ⟨⟨a,ha,z,hz,hzp⟩,hi⟩
    exact ⟨a,ha,z,hz,(h z).mpr ⟨hzp,i,⟨a,k,b,hz,ha⟩,hi⟩⟩

theorem exists_restrict (hM : FirstOrder.Theory.Models M nativeZF)
    {S w p : M.Carrier .set} (hp : Condition S w p) (A : M.Carrier .set) :
    ∃ q, Condition S w q ∧ Restricted A p q ∧ Within q A := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 := { bound := fun _ => A, free := fun _ => p }
  let schema : Project.UnarySchema 1 := {
    body := .existsE (.conj (label 1 0) (.mem (.bound 0) (.bound 2)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,label_freeClosed] }
  obtain ⟨q,hq⟩ := ZF.separation_exists_d hZF schema env p
  have hRestr : Restricted A p q := by
    intro z
    have hSchema : schema.denote env z ↔ ∃ i, Label z i ∧ (Project.FirstOrderSemantics.reduct M).mem i A := by
      simp only [Project.UnarySchema.denote,schema,Project.Formula.satisfies_exists_iff,
        Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,label_semantics hM,Project.Term.eval_bound]
      rfl
    exact (hq z).trans (and_congr Iff.rfl hSchema)
  have hSub : (Project.FirstOrderSemantics.reduct M).MemberSubset q p := fun z hz => ((hRestr z).mp hz).1
  refine ⟨q,⟨fun z hz => hp.1 z (hSub z hz),?_,ForcingSupportSize.small_subset hM hSub hp.2.2⟩,
    hRestr,fun i k b he => (restricted_entry hRestr).mp he |>.2⟩
  intro a b c hab hac
  exact hp.2.1 a b c (by obtain ⟨z,hz,hm⟩ := hab; exact ⟨z,hz,hSub z hm⟩)
    (by obtain ⟨z,hz,hm⟩ := hac; exact ⟨z,hz,hSub z hm⟩)

theorem moved_of_image (hM : FirstOrder.Theory.Models M nativeZF)
    {I K C B S w pi f g p q : M.Carrier .set}
    (hC : Cartesian I K C) (hS : Cartesian C B S)
    (hf : Graph C pi f) (hg : Graph S f g) (hp : Condition S w p)
    (him : ForcingStabilizerTransport.Image g p q) : Moved pi p q := by
  intro j k b
  constructor
  · rintro ⟨a,ha,hab⟩
    obtain ⟨x,hxa,hxb⟩ := (ForcingCohenConditions.image_edge hM hg hp.1 him a b).mp hab
    obtain ⟨_,i,k',j',hx,hij,ha'⟩ := (hf x a).mp hxa
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective ha' ha
    exact ⟨i,hij,x,hx,hxb⟩
  · rintro ⟨i,hij,x,hx,hxb⟩
    obtain ⟨a,ha⟩ := KuratowskiZF.exists_code hM j k
    have hiK := entry_typed hC hS hp ⟨x,hx,hxb⟩
    have hxC := (hC x).mpr ⟨i,hiK.1,k,hiK.2.1,hx⟩
    exact ⟨a,ha,(ForcingCohenConditions.image_edge hM hg hp.1 him a b).mpr
      ⟨x,(hf x a).mpr ⟨hxC,i,k,j,hx,hij,ha⟩,hxb⟩⟩

theorem exists_moved (hM : FirstOrder.Theory.Models M nativeZF)
    {I K C B S w pi p : M.Carrier .set}
    (hC : Cartesian I K C) (hS : Cartesian C B S) (hpi : Permutation I pi) (hp : Condition S w p) :
    ∃ f g q, Permutation C f ∧ Graph C pi f ∧ Permutation S g ∧ Graph S f g ∧
      Condition S w q ∧ ForcingStabilizerTransport.Image g p q ∧ Moved pi p q := by
  obtain ⟨f,hf,hfg⟩ := ForcingCohenCoordinates.exists_lift hM hC hpi
  obtain ⟨g,hg,hgg⟩ := ForcingCohenCoordinates.exists_lift hM hS hf
  obtain ⟨q,hq,hCondition⟩ := ForcingCohenConditions.exists_permute hM hf hg hgg hp
  exact ⟨f,g,q,hf,hfg,hg,hgg,hCondition,hq,moved_of_image hM hC hS hfg hgg hp hq⟩

theorem permute_eq_of_agree (hM : FirstOrder.Theory.Models M nativeZF)
    {I K C B S w H p pi rho q r : M.Carrier .set}
    (hC : Cartesian I K C) (hS : Cartesian C B S)
    (hpi : Permutation I pi) (hrho : Permutation I rho)
    (hp : Condition S w p) (hq : Condition S w q) (hr : Condition S w r)
    (hH : Support p H) (hAgree : AgreesOn H pi rho)
    (hmq : Moved pi p q) (hmr : Moved rho p r) : q = r := by
  apply entries_ext hM hC hS hq hr
  intro j k b
  rw [hmq j k b,hmr j k b]
  constructor
  · rintro ⟨i,hij,he⟩
    have hi := (hH i).mpr ⟨k,b,he⟩
    obtain ⟨z,hiz,_⟩ := hrho.1.1.2 i (entry_typed hC hS hp he).1
    have heq := ForcingConditionGraphs.function_unique hpi.1.1 hij (hAgree i z hi hiz)
    exact ⟨i,by simpa only [heq] using hiz,he⟩
  · rintro ⟨i,hij,he⟩
    exact ⟨i,hAgree i j ((hH i).mpr ⟨k,b,he⟩) hij,he⟩

theorem compatible_of_entries {I K C B S w p q : M.Carrier .set}
    (hC : Cartesian I K C) (hS : Cartesian C B S) (hp : Condition S w p)
    (h : ∀ i k b c, Entry p i k b → Entry q i k c → b = c) : Compatible p q := by
  intro a b c hab hac
  obtain ⟨z,hz,hzp⟩ := hab
  obtain ⟨a',haC,b',_,hz'⟩ := (hS z).mp (hp.1 z hzp)
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
  obtain ⟨i,_,k,_,ha⟩ := (hC a).mp haC
  exact h i k b c ⟨a,ha,z,hz,hzp⟩ ⟨a,ha,hac⟩

theorem compatible_permute_of_trigger (hM : FirstOrder.Theory.Models M nativeZF)
    {I K C B S w A V d c pi delta movedDelta movedD : M.Carrier .set}
    (hC : Cartesian I K C) (hS : Cartesian C B S) (hpi : Permutation I pi)
    (hc : Condition S w c) (hd : Within d V) (hTrigger : Trigger pi V c A)
    (hRestr : Restricted A d delta) (hMoveDelta : Moved pi delta movedDelta)
    (hMoveD : Moved pi d movedD)
    (hLower : (Project.FirstOrderSemantics.reduct M).MemberSubset movedDelta c) : Compatible c movedD := by
  apply compatible_of_entries hC hS hc
  intro j k b e hb he
  obtain ⟨i,hij,hdEntry⟩ := (hMoveD j k e).mp he
  obtain ⟨a,ha,haj⟩ := hTrigger j ⟨i,hd i k e hdEntry,hij⟩ ⟨k,b,hb⟩
  have hai := hpi.2.1 a i j haj hij
  have hiA : (Project.FirstOrderSemantics.reduct M).mem i A := hai ▸ ha
  have hDeltaEntry := (restricted_entry hRestr).mpr ⟨hdEntry,hiA⟩
  obtain ⟨x,hx,z,hz,hm⟩ := (hMoveDelta j k e).mpr ⟨i,hij,hDeltaEntry⟩
  exact entry_functional hM hc.2.1 hb ⟨x,hx,z,hz,hLower z hm⟩

theorem compatible_permutes_of_overlap (hM : FirstOrder.Theory.Models M nativeZF)
    {I K C B S w A V d pi rho movedP movedR : M.Carrier .set}
    (hC : Cartesian I K C) (hS : Cartesian C B S)
    (hpi : Permutation I pi) (hrho : Permutation I rho)
    (hp : Condition S w movedP) (hd : Functional d) (hV : Within d V)
    (hOverlap : Overlap pi rho V A) (hAgree : AgreesOn A pi rho)
    (hMoveP : Moved pi d movedP) (hMoveR : Moved rho d movedR) : Compatible movedP movedR := by
  apply compatible_of_entries hC hS hp
  intro j k b c hb hc
  obtain ⟨i,hij,hib⟩ := (hMoveP j k b).mp hb
  obtain ⟨l,hlj,hlc⟩ := (hMoveR j k c).mp hc
  obtain ⟨a,ha,haj⟩ := hOverlap j ⟨i,hV i k b hib,hij⟩ ⟨l,hV l k c hlc,hlj⟩
  have hai := hpi.2.1 a i j haj hij
  have hiA : (Project.FirstOrderSemantics.reduct M).mem i A := hai ▸ ha
  obtain ⟨z,hiz,_⟩ := hrho.1.1.2 i (ForcingConditionGraphs.function_input hpi.1.1 hij)
  -- Actual rho edge at i is already supplied by its agreement on A.
  have hiRho : PureKuratowski.PairMember M i j rho := by
    have hrhoij := hAgree i z hiA hiz
    have hEq := ForcingConditionGraphs.function_unique hpi.1.1 hij hrhoij
    exact hEq ▸ hiz
  have hil := hrho.2.1 i l j hiRho hlj
  exact entry_functional hM hd hib (hil.symm ▸ hlc)

theorem compatible_union_left {p q r s : M.Carrier .set}
    (hUnion : ConstructionPlacementPasting.Union r p q)
    (hps : Compatible p s) (hqs : Compatible q s) : Compatible r s := by
  intro a b c hab hac
  obtain ⟨z,hz,hzr⟩ := hab
  rcases (hUnion z).mp hzr with h | h
  · exact hps a b c ⟨z,hz,h⟩ hac
  · exact hqs a b c ⟨z,hz,h⟩ hac

theorem exists_union (hM : FirstOrder.Theory.Models M nativeZF)
    {S w p q : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hp : Condition S w p) (hq : Condition S w q) (hc : Compatible p q) :
    ∃ r, Condition S w r ∧ ConstructionPlacementPasting.Union r p q ∧
      (Project.FirstOrderSemantics.reduct M).MemberSubset p r ∧
      (Project.FirstOrderSemantics.reduct M).MemberSubset q r := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨r,hUnion⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) p q
  obtain ⟨id,hId⟩ := ZF.exists_identityBijection hZF pair w
  have hwInfinite : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal pair w w :=
    ⟨ExistingCardinalBounds.omega_cardinal_l pair hZF hw,⟨id,hId.1⟩⟩
  have hSmall : Small r w := (ForcingSupportSize.native_small hM r w).mpr
    (ExistingCardinalBounds.infinite_union_two_l pair hZF hw hwInfinite
      ((ForcingSupportSize.native_small hM p w).mp hp.2.2)
      ((ForcingSupportSize.native_small hM q w).mp hq.2.2) hUnion)
  refine ⟨r,⟨fun z hz => ((hUnion z).mp hz).elim (hp.1 z) (hq.1 z),?_,hSmall⟩,hUnion,
    fun z hz => (hUnion z).mpr (Or.inl hz),fun z hz => (hUnion z).mpr (Or.inr hz)⟩
  intro a b c hab hac
  obtain ⟨z,hz,hzr⟩ := hab
  obtain ⟨t,ht,htr⟩ := hac
  rcases (hUnion z).mp hzr with hzp | hzq <;> rcases (hUnion t).mp htr with htp | htq
  · exact hp.2.1 a b c ⟨z,hz,hzp⟩ ⟨t,ht,htp⟩
  · exact hc a b c ⟨z,hz,hzp⟩ ⟨t,ht,htq⟩
  · exact (hc a c b ⟨t,ht,htp⟩ ⟨z,hz,hzq⟩).symm
  · exact hq.2.1 a b c ⟨z,hz,hzq⟩ ⟨t,ht,htq⟩

def LowerThree (S w c p q r : M.Carrier .set) : Prop :=
  Condition S w r ∧ (Project.FirstOrderSemantics.reduct M).MemberSubset c r ∧
    (Project.FirstOrderSemantics.reduct M).MemberSubset p r ∧
    (Project.FirstOrderSemantics.reduct M).MemberSubset q r

theorem lower_three (hM : FirstOrder.Theory.Models M nativeZF)
    {S w c p q : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hc : Condition S w c) (hp : Condition S w p) (hq : Condition S w q)
    (hcp : Compatible c p) (hcq : Compatible c q) (hpq : Compatible p q) :
    ∃ r, LowerThree S w c p q r := by
  obtain ⟨b,hb,hUnionB,hcb,hpb⟩ := exists_union hM hw hc hp hcp
  obtain ⟨a,ha,_,hba,hqa⟩ := exists_union hM hw hb hq (compatible_union_left hUnionB hcq hpq)
  exact ⟨a,ha,fun z hz => hba z (hcb z hz),fun z hz => hba z (hpb z hz),hqa⟩

def ComparisonInputs (I K C B S w A E V pi rho d c delta deltaP deltaR dP dR : M.Carrier .set) : Prop :=
  Cartesian I K C ∧ Cartesian C B S ∧ Permutation I pi ∧ Permutation I rho ∧
    Condition S w d ∧ Condition S w c ∧ Condition S w dP ∧ Condition S w dR ∧ Within d V ∧
    Restricted A d delta ∧ Moved pi delta deltaP ∧ Moved rho delta deltaR ∧
    Moved pi d dP ∧ Moved rho d dR ∧ Trigger pi V c A ∧ Trigger rho V c A ∧
    Overlap pi rho V E ∧ AgreesOn E pi rho ∧
    (Project.FirstOrderSemantics.reduct M).MemberSubset deltaP c ∧
    (Project.FirstOrderSemantics.reduct M).MemberSubset deltaR c

theorem comparison (hM : FirstOrder.Theory.Models M nativeZF)
    {I K C B S w A E V pi rho d c delta deltaP deltaR dP dR : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (h : ComparisonInputs I K C B S w A E V pi rho d c delta deltaP deltaR dP dR) :
    ∃ r, LowerThree S w c dP dR r := by
  obtain ⟨hC,hS,hpi,hrho,hd,hc,hdP,hdR,hV,hRestr,hDeltaP,hDeltaR,hDP,hDR,
    hTriggerP,hTriggerR,hOverlap,hAgree,hLowerP,hLowerR⟩ := h
  exact lower_three hM hw hc hdP hdR
    (compatible_permute_of_trigger hM hC hS hpi hc hV hTriggerP hRestr hDeltaP hDP hLowerP)
    (compatible_permute_of_trigger hM hC hS hrho hc hV hTriggerR hRestr hDeltaR hDR hLowerR)
    (compatible_permutes_of_overlap hM hC hS hpi hrho hdP hd.2.1 hV hOverlap hAgree hDP hDR)

def entry {m : Nat} (p i k b : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (PureKuratowskiProject.code (.bound 0) (.bound i.succ) (.bound k.succ))
    (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 0) (.bound b.succ) (.bound p.succ)))

theorem entry_freeClosed {m : Nat} (p i k b : Fin m) : (entry p i k b).FreeClosed := by
  simp -implicitDefEqProofs [entry,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,Project.Formula.orderedPairMem_freeClosed]

theorem entry_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (p i k b : Fin m) :
    Project.Formula.satisfies env (entry p i k b) ↔ Entry (env.bound p) (env.bound i) (env.bound k) (env.bound b) := by
  simp only [entry,Entry,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    KuratowskiZF.code_correct hM,Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),
    Project.Term.eval_bound]
  rfl

def support {m : Nat} (p H : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound H.succ))
    (.existsE (.existsE (entry p.succ.succ.succ 2 1 0))))

theorem support_freeClosed {m : Nat} (p H : Fin m) : (support p H).FreeClosed := by
  simp -implicitDefEqProofs [support,Definitional.Formula.FreeClosed,entry_freeClosed]

theorem support_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (p H : Fin m) :
    Project.Formula.satisfies env (support p H) ↔ Support (env.bound p) (env.bound H) := by
  simp only [support,Support,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_exists_iff,entry_semantics hM,Project.Term.eval_bound]
  rfl

def within {m : Nat} (p V : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.imp (entry p.succ.succ.succ 2 1 0)
    (.mem (.bound 2) (.bound V.succ.succ.succ)))))

theorem within_freeClosed {m : Nat} (p V : Fin m) : (within p V).FreeClosed := by
  simp -implicitDefEqProofs [within,Definitional.Formula.FreeClosed,entry_freeClosed]

theorem within_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (p V : Fin m) :
    Project.Formula.satisfies env (within p V) ↔ Within (env.bound p) (env.bound V) := by
  simp only [within,Within,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,entry_semantics hM,Project.Term.eval_bound]
  rfl

def restricted {m : Nat} (A p q : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound q.succ))
    (.conj (.mem (.bound 0) (.bound p.succ))
      (.existsE (.conj (label 1 0) (.mem (.bound 0) (.bound A.succ.succ))))))

theorem restricted_freeClosed {m : Nat} (A p q : Fin m) : (restricted A p q).FreeClosed := by
  simp -implicitDefEqProofs [restricted,Definitional.Formula.FreeClosed,label_freeClosed]

theorem restricted_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (A p q : Fin m) :
    Project.Formula.satisfies env (restricted A p q) ↔ Restricted (env.bound A) (env.bound p) (env.bound q) := by
  simp only [restricted,Restricted,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_exists_iff,label_semantics hM,Project.Term.eval_bound]
  rfl

def moved {m : Nat} (pi p q : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.iff (entry q.succ.succ.succ 2 1 0)
    (.existsE (.conj
      (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 0) (.bound 3) (.bound pi.succ.succ.succ.succ))
      (entry p.succ.succ.succ.succ 0 2 1))))))

theorem moved_freeClosed {m : Nat} (pi p q : Fin m) : (moved pi p q).FreeClosed := by
  simp -implicitDefEqProofs [moved,Definitional.Formula.FreeClosed,entry_freeClosed,Project.Formula.orderedPairMem_freeClosed]

theorem moved_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (pi p q : Fin m) :
    Project.Formula.satisfies env (moved pi p q) ↔ Moved (env.bound pi) (env.bound p) (env.bound q) := by
  simp only [moved,Moved,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,entry_semantics hM,
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound]
  rfl

def trigger {m : Nat} (pi V c A : Fin m) : Project.Formula 1 m :=
  .forallE (.imp (ConstructionPlacementTriple.imageAt pi.succ V.succ 0)
    (.imp (.existsE (.existsE (entry c.succ.succ.succ 2 1 0)))
      (ConstructionPlacementTriple.imageAt pi.succ A.succ 0)))

theorem trigger_freeClosed {m : Nat} (pi V c A : Fin m) : (trigger pi V c A).FreeClosed := by
  simp -implicitDefEqProofs [trigger,Definitional.Formula.FreeClosed,ConstructionPlacementTriple.imageAt_freeClosed,entry_freeClosed]

theorem trigger_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (pi V c A : Fin m) :
    Project.Formula.satisfies env (trigger pi V c A) ↔
      Trigger (env.bound pi) (env.bound V) (env.bound c) (env.bound A) := by
  simp only [trigger,Trigger,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    ConstructionPlacementTriple.imageAt_semantics hM,Project.Formula.satisfies_exists_iff,entry_semantics hM]
  rfl

def overlap {m : Nat} (pi rho V A : Fin m) : Project.Formula 1 m :=
  .forallE (.imp (ConstructionPlacementTriple.imageAt pi.succ V.succ 0)
    (.imp (ConstructionPlacementTriple.imageAt rho.succ V.succ 0)
      (ConstructionPlacementTriple.imageAt pi.succ A.succ 0)))

theorem overlap_freeClosed {m : Nat} (pi rho V A : Fin m) : (overlap pi rho V A).FreeClosed := by
  simp -implicitDefEqProofs [overlap,Definitional.Formula.FreeClosed,ConstructionPlacementTriple.imageAt_freeClosed]

theorem overlap_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (pi rho V A : Fin m) :
    Project.Formula.satisfies env (overlap pi rho V A) ↔
      Overlap (env.bound pi) (env.bound rho) (env.bound V) (env.bound A) := by
  simp only [overlap,Overlap,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    ConstructionPlacementTriple.imageAt_semantics hM]
  rfl

def lowerThree {m : Nat} (S w c p q r : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (ForcingCohenConditions.condition S w r))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.subset c r))
      (.conj (ProjectSyntax.encode id (Source.SetLanguage.subset p r))
        (ProjectSyntax.encode id (Source.SetLanguage.subset q r))))

theorem lowerThree_freeClosed {m : Nat} (S w c p q r : Fin m) : (lowerThree S w c p q r).FreeClosed := by
  simp -implicitDefEqProofs [lowerThree,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem lowerThree_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (S w c p q r : Fin m) :
    Project.Formula.satisfies env (lowerThree S w c p q r) ↔
      LowerThree (env.bound S) (env.bound w) (env.bound c) (env.bound p) (env.bound q) (env.bound r) := by
  simp only [lowerThree,LowerThree,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenConditions.condition_semantics (M := M),ForcingLabelPermutations.subset_semantics (M := M)]
  rfl

def comparisonInputs {m : Nat} (I K C B S w A E V pi rho d c delta deltaP deltaR dP dR : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K C)) (.conj (ProjectSyntax.encode id
    (ForcingCohenCoordinates.cartesian C B S)) (.conj (ProjectSyntax.encode id
    (ForcingConditionGraphs.permutation I pi)) (.conj (ProjectSyntax.encode id
    (ForcingConditionGraphs.permutation I rho)) (.conj (ProjectSyntax.encode id
    (ForcingCohenConditions.condition S w d)) (.conj (ProjectSyntax.encode id
    (ForcingCohenConditions.condition S w c)) (.conj (ProjectSyntax.encode id
    (ForcingCohenConditions.condition S w dP)) (.conj (ProjectSyntax.encode id
    (ForcingCohenConditions.condition S w dR)) (.conj (within d V) (.conj (restricted A d delta) (.conj
    (moved pi delta deltaP) (.conj (moved rho delta deltaR) (.conj (moved pi d dP) (.conj (moved rho d dR)
    (.conj (trigger pi V c A) (.conj (trigger rho V c A) (.conj (overlap pi rho V E) (.conj
    (ConstructionPlacementPasting.agreesOn E pi rho) (.conj (ProjectSyntax.encode id
    (Source.SetLanguage.subset deltaP c)) (ProjectSyntax.encode id (Source.SetLanguage.subset deltaR
    c)))))))))))))))))))))

theorem comparisonInputs_freeClosed {m : Nat} (I K C B S w A E V pi rho d c delta deltaP deltaR dP dR : Fin m) :
    (comparisonInputs I K C B S w A E V pi rho d c delta deltaP deltaR dP dR).FreeClosed := by
  simp -implicitDefEqProofs [comparisonInputs,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    within_freeClosed,restricted_freeClosed,moved_freeClosed,trigger_freeClosed,overlap_freeClosed,
    ConstructionPlacementPasting.agreesOn_freeClosed]

theorem comparisonInputs_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m)
    (I K C B S w A E V pi rho d c delta deltaP deltaR dP dR : Fin m) :
    Project.Formula.satisfies env (comparisonInputs I K C B S w A E V pi rho d c delta deltaP deltaR dP dR) ↔
      ComparisonInputs (env.bound I) (env.bound K) (env.bound C) (env.bound B) (env.bound S) (env.bound w)
        (env.bound A) (env.bound E) (env.bound V) (env.bound pi) (env.bound rho) (env.bound d) (env.bound c)
        (env.bound delta) (env.bound deltaP) (env.bound deltaR) (env.bound dP) (env.bound dR) := by
  simp only [comparisonInputs,ComparisonInputs,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingConditionGraphs.permutation_semantics (M := M),
    ForcingCohenConditions.condition_semantics (M := M),ForcingLabelPermutations.subset_semantics (M := M),
    within_semantics hM,restricted_semantics hM,moved_semantics hM,trigger_semantics hM,overlap_semantics hM,
    ConstructionPlacementPasting.agreesOn_semantics hM]
  rfl

def supportResult {m : Nat} (I S w p A H q : Fin m) : Project.Formula 1 m :=
  (.conj (support p H) (.conj (ProjectSyntax.encode id (Source.SetLanguage.subset H I)) (.conj
    (ProjectSyntax.encode id (ForcingSupportSize.small H w)) (.conj (ProjectSyntax.encode id
    (ForcingCohenConditions.condition S w q)) (.conj (restricted A p q) (within q A))))))

theorem supportResult_freeClosed {m : Nat} (I S w p A H q : Fin m) : (supportResult I S w p A H q).FreeClosed := by
  simp -implicitDefEqProofs [supportResult,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    support_freeClosed,restricted_freeClosed,within_freeClosed]

theorem supportResult_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (I S w p A H q : Fin m) :
    Project.Formula.satisfies env (supportResult I S w p A H q) ↔
      Support (env.bound p) (env.bound H) ∧
      (Project.FirstOrderSemantics.reduct M).MemberSubset (env.bound H) (env.bound I) ∧
      Small (env.bound H) (env.bound w) ∧ Condition (env.bound S) (env.bound w) (env.bound q) ∧
      Restricted (env.bound A) (env.bound p) (env.bound q) ∧ Within (env.bound q) (env.bound A) := by
  simp only [supportResult,Project.Formula.satisfies_conj_iff,support_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingLabelPermutations.subset_semantics (M := M),ForcingSupportSize.small_semantics (M := M),
    ForcingCohenConditions.condition_semantics (M := M),restricted_semantics hM,within_semantics hM]
  rfl

def movementResult {m : Nat} (C S w pi p f g q : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation C f)) (.conj (ProjectSyntax.encode id
    (ForcingCohenCoordinates.graph C pi f)) (.conj (ProjectSyntax.encode id
    (ForcingConditionGraphs.permutation S g)) (.conj (ProjectSyntax.encode id (ForcingCohenCoordinates.graph
    S f g)) (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition S w q)) (.conj
    (ProjectSyntax.encode id (ForcingStabilizerTransport.image g p q)) (moved pi p q)))))))

theorem movementResult_freeClosed {m : Nat} (C S w pi p f g q : Fin m) : (movementResult C S w pi p f g q).FreeClosed := by
  simp -implicitDefEqProofs [movementResult,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,moved_freeClosed]

theorem movementResult_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (C S w pi p f g q : Fin m) :
    Project.Formula.satisfies env (movementResult C S w pi p f g q) ↔
      Permutation (env.bound C) (env.bound f) ∧ Graph (env.bound C) (env.bound pi) (env.bound f) ∧
      Permutation (env.bound S) (env.bound g) ∧ Graph (env.bound S) (env.bound f) (env.bound g) ∧
      Condition (env.bound S) (env.bound w) (env.bound q) ∧
      ForcingStabilizerTransport.Image (env.bound g) (env.bound p) (env.bound q) ∧
      Moved (env.bound pi) (env.bound p) (env.bound q) := by
  simp only [movementResult,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingCohenCoordinates.graph_semantics (M := M),
    ForcingCohenConditions.condition_semantics (M := M),ForcingStabilizerTransport.image_semantics (M := M),moved_semantics hM]
  rfl

def supportSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 8
    (.imp (Project.Formula.isOmega (.bound (5 : Fin 8))) (.imp (ProjectSyntax.encode id
    (ForcingCohenCoordinates.cartesian (0 : Fin 8) 1 2)) (.imp (ProjectSyntax.encode id
    (ForcingCohenCoordinates.cartesian (2 : Fin 8) 3 4)) (.imp (ProjectSyntax.encode id
    (ForcingCohenConditions.condition (4 : Fin 8) 5 6)) (.existsE (.existsE (supportResult (0 : Fin
    8).succ.succ (4 : Fin 8).succ.succ (5 : Fin 8).succ.succ (6 : Fin 8).succ.succ (7 : Fin 8).succ.succ 1
    0)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      ProjectSyntax.freeClosed,supportResult_freeClosed]

theorem support_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence supportSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) supportSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isOmega_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    supportResult_semantics hM,Project.Term.eval_bound]
  intro hw hC hS hp
  obtain ⟨H,hH,hSub,hSmall⟩ := exists_support hM hw hC hS hp
  obtain ⟨q,hq,hRestr,hWithin⟩ := exists_restrict hM hp (bound 7)
  exact ⟨H,q,hH,hSub,hSmall,hq,hRestr,hWithin⟩

theorem support_kernel_certificate : FirstOrder.Derives nativeZF [] (Project.fo_sentence supportSentence) :=
  ModelTransfer.derives (fun _ hM => support_models hM)

def movementSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 8
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (0 : Fin 8) 1 2)) (.imp
    (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (2 : Fin 8) 3 4)) (.imp
    (ProjectSyntax.encode id (ForcingConditionGraphs.permutation (0 : Fin 8) 6)) (.imp (ProjectSyntax.encode
    id (ForcingCohenConditions.condition (4 : Fin 8) 5 7)) (.existsE (.existsE (.existsE (movementResult (2
    : Fin 8).succ.succ.succ (4 : Fin 8).succ.succ.succ (5 : Fin 8).succ.succ.succ (6 : Fin 8).succ.succ.succ
    (7 : Fin 8).succ.succ.succ 2 1 0))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,movementResult_freeClosed]

theorem movement_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence movementSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) movementSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingConditionGraphs.permutation_semantics (M := M),
    ForcingCohenConditions.condition_semantics (M := M),movementResult_semantics hM]
  exact fun hC hS hpi hp => exists_moved hM hC hS hpi hp

theorem movement_kernel_certificate : FirstOrder.Derives nativeZF [] (Project.fo_sentence movementSentence) :=
  ModelTransfer.derives (fun _ hM => movement_models hM)

def agreementSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 12
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (0 : Fin 12) 1 2)) (.imp
    (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (2 : Fin 12) 3 4)) (.imp
    (ProjectSyntax.encode id (ForcingConditionGraphs.permutation (0 : Fin 12) 8)) (.imp
    (ProjectSyntax.encode id (ForcingConditionGraphs.permutation (0 : Fin 12) 9)) (.imp
    (ProjectSyntax.encode id (ForcingCohenConditions.condition (4 : Fin 12) 5 7)) (.imp
    (ProjectSyntax.encode id (ForcingCohenConditions.condition (4 : Fin 12) 5 10)) (.imp
    (ProjectSyntax.encode id (ForcingCohenConditions.condition (4 : Fin 12) 5 11)) (.imp (support (7 : Fin
    12) 6) (.imp (ConstructionPlacementPasting.agreesOn (6 : Fin 12) 8 9) (.imp (moved (8 : Fin 12) 7 10)
    (.imp (moved (9 : Fin 12) 7 11) (Project.Formula.extensionalEq (.bound (10 : Fin 12)) (.bound 11)))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      support_freeClosed,ConstructionPlacementPasting.agreesOn_freeClosed,moved_freeClosed,Project.Formula.extensionalEq]

theorem agreement_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence agreementSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) agreementSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.project_models_iff.mp hM).1,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingConditionGraphs.permutation_semantics (M := M),
    ForcingCohenConditions.condition_semantics (M := M),support_semantics hM,
    ConstructionPlacementPasting.agreesOn_semantics hM,moved_semantics hM,Project.Term.eval_bound]
  exact fun hC hS hpi hrho hp hq hr hSupport hAgree hMoveQ hMoveR =>
    permute_eq_of_agree hM hC hS hpi hrho hp hq hr hSupport hAgree hMoveQ hMoveR

theorem agreement_kernel_certificate : FirstOrder.Derives nativeZF [] (Project.fo_sentence agreementSentence) :=
  ModelTransfer.derives (fun _ hM => agreement_models hM)

def comparisonSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 18
    (.imp (Project.Formula.isOmega (.bound (5 : Fin 18)))
      (.imp (comparisonInputs (0 : Fin 18) 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17)
        (.existsE (lowerThree (4 : Fin 18).succ (5 : Fin 18).succ (12 : Fin 18).succ
          (16 : Fin 18).succ (17 : Fin 18).succ 0))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,
      comparisonInputs_freeClosed,lowerThree_freeClosed]

theorem comparison_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence comparisonSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) comparisonSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isOmega_iff,comparisonInputs_semantics hM,lowerThree_semantics hM,Project.Term.eval_bound]
  exact fun hw h => comparison hM hw h

theorem comparison_kernel_certificate : FirstOrder.Derives nativeZF [] (Project.fo_sentence comparisonSentence) :=
  ModelTransfer.derives (fun _ hM => comparison_models hM)

end PPAC.Migration.ConstructionCohenCompatibility
