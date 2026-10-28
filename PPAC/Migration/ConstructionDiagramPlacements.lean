/- Actual source Diagram consumers:
DiagramPlacements.permutation_over_root / range_inter_sub;
Diagrams.equal_iff_of_common_sub -> exists_overlap_prescription -> amalgamate.
Reuse full internal injection/sub/composition graphs and previous extensions.
No diagram, label value or permutation is a Type-level chosen function. -/
import PPAC.Migration.ConstructionPlacementTriple

namespace PPAC.Migration.ConstructionDiagramPlacements
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (Small Injection)
open ForcingConditionGraphs (Permutation CompositionGraph)
open ForcingDiagramOrder (Sub Product LeftInjection)
open ConstructionBaseMonoid (Divides)
open ConstructionPlacementTriple (ImageAt)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def RangeIntersection (D r s p : M.Carrier .set) : Prop :=
  ∀ z, ImageAt r D z ∧ ImageAt s D z ↔ ImageAt p D z

def ConeEquality (D mul a b c : M.Carrier .set) : Prop :=
  ∀ x, (Project.FirstOrderSemantics.reduct M).mem x D →
    (Divides D mul a x ∧ Divides D mul b x ↔ Divides D mul c x)

def LabelCones (D mul r s a b : M.Carrier .set) : Prop :=
  ∀ x y, (Project.FirstOrderSemantics.reduct M).mem x D →
    (Project.FirstOrderSemantics.reduct M).mem y D →
    ((∃ z, PureKuratowski.PairMember M x z r ∧ PureKuratowski.PairMember M y z s) ↔
      ∃ t, (Project.FirstOrderSemantics.reduct M).mem t D ∧ Product mul a t x ∧ Product mul b t y)

def FixesRange (D p pi : M.Carrier .set) : Prop :=
  ∀ z, ImageAt p D z → PureKuratowski.PairMember M z z pi

theorem sub_range {D mul r a s z : M.Carrier .set} (h : Sub D mul r a s) :
    ImageAt s D z ↔ ∃ x, (Project.FirstOrderSemantics.reduct M).mem x D ∧
      Divides D mul a x ∧ PureKuratowski.PairMember M x z r := by
  constructor
  · rintro ⟨t,ht,htz⟩
    obtain ⟨_,x,hx,hat,hxz⟩ := (h t z).mp htz
    exact ⟨x,hx,⟨t,ht,hat⟩,hxz⟩
  · rintro ⟨x,hx,⟨t,ht,hat⟩,hxz⟩
    exact ⟨t,ht,(h t z).mpr ⟨ht,x,hx,hat,hxz⟩⟩

theorem range_inter_sub {D I mul r sa sb sc a b c : M.Carrier .set}
    (hr : Injection D I r) (ha : Sub D mul r a sa) (hb : Sub D mul r b sb)
    (hc : Sub D mul r c sc) (hCones : ConeEquality D mul a b c) :
    RangeIntersection D sa sb sc := by
  intro z
  constructor
  · rintro ⟨hzA,hzB⟩
    obtain ⟨x,hx,hax,hxz⟩ := (sub_range ha).mp hzA
    obtain ⟨y,_,hby,hyz⟩ := (sub_range hb).mp hzB
    have he := hr.2 x y z hxz hyz
    subst y
    exact (sub_range hc).mpr ⟨x,hx,(hCones x hx).mp ⟨hax,hby⟩,hxz⟩
  · intro hz
    obtain ⟨x,hx,hcx,hxz⟩ := (sub_range hc).mp hz
    obtain ⟨hax,hbx⟩ := (hCones x hx).mpr hcx
    exact ⟨(sub_range ha).mpr ⟨x,hx,hax,hxz⟩,(sub_range hb).mpr ⟨x,hx,hbx,hxz⟩⟩

/-- Exact source label equality iff the GIVEN common right-cone parameter,
used to construct the original literal optional prescription, not its closure. -/
theorem equal_iff_of_common_sub {D I mul r s a b p : M.Carrier .set}
    (hr : Injection D I r) (hs : Injection D I s) (hp : Injection D I p)
    (ha : Sub D mul r a p) (hb : Sub D mul s b p)
    (hInter : RangeIntersection D r s p) : LabelCones D mul r s a b := by
  intro x y hx hy
  constructor
  · rintro ⟨z,hxz,hyz⟩
    obtain ⟨t,ht,htz⟩ := (hInter z).mp ⟨⟨x,hx,hxz⟩,⟨y,hy,hyz⟩⟩
    obtain ⟨_,u,_,hau,huz⟩ := (ha t z).mp htz
    obtain ⟨_,v,_,hbv,hvz⟩ := (hb t z).mp htz
    have he := hr.2 u x z huz hxz
    have hf := hs.2 v y z hvz hyz
    exact ⟨t,ht,he ▸ hau,hf ▸ hbv⟩
  · rintro ⟨t,ht,hat,hbt⟩
    obtain ⟨z,hxz,_⟩ := hr.1.1.2 x hx
    obtain ⟨v,hyv,_⟩ := hs.1.1.2 y hy
    have hpz := (ha t z).mpr ⟨ht,x,hx,hat,hxz⟩
    have hpv := (hb t v).mpr ⟨ht,y,hy,hbt,hyv⟩
    have he := ForcingConditionGraphs.function_unique hp.1.1 hpz hpv
    exact ⟨z,hxz,by simpa only [he] using hyv⟩

/-- Retain the existing native range/bijection/inverse certificates for the
actual diagram. All construction below uses original native graph functions. -/
theorem between_diagrams (hM : FirstOrder.Theory.Models M nativeZF)
    {D I s t mu : M.Carrier .set} (hs : Injection D I s) (ht : Injection D I t) (hSmall : Small D mu) :
    ∃ S f, (Project.FirstOrderSemantics.reduct M).MemberSubset S I ∧ Small S mu ∧
      (Project.FirstOrderSemantics.reduct M).IsSetInjectionFromTo (KuratowskiZF.interpretation hM) f S I ∧
      ∀ x y z, PureKuratowski.PairMember M x y s → PureKuratowski.PairMember M x z t →
        PureKuratowski.PairMember M y z f := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  have hS := (ForcingSupportSize.native_injection hM D I s).mp hs
  have hT := (ForcingSupportSize.native_injection hM D I t).mp ht
  obtain ⟨S,hRange⟩ := ZF.exists_range_of_setFunction hZF pair hS.1.1 hS.1.2.1
  have hBij : (Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo pair s D S := by
    refine ⟨⟨⟨hS.1.1,hS.1.2.1,?_⟩,hS.2⟩,?_⟩
    · intro x hx
      obtain ⟨y,_,hxy⟩ := hS.1.2.2 x hx
      exact ⟨y,(hRange y).mpr ⟨x,hxy⟩,hxy⟩
    · intro y hy
      obtain ⟨x,hxy⟩ := (hRange y).mp hy
      exact ⟨x,hS.1.input_mem_of_pairMember hxy,hxy⟩
  obtain ⟨inverse,hInverse,hInvEdges⟩ := ZF.exists_inverseBijectionWithPairs hZF pair hBij
  obtain ⟨toMu,hToMu⟩ := (ForcingSupportSize.native_small hM D mu).mp hSmall
  have hSize : Small S mu := (ForcingSupportSize.native_small hM S mu).mpr
    (ZF.exists_compositionInjection hZF pair hInverse.1 hToMu)
  obtain ⟨f,hf,he⟩ := ZF.exists_compositionFunction hZF pair hInverse.1.1 hT.1
  have hInj : (Project.FirstOrderSemantics.reduct M).IsSetInjectionFromTo pair f S I := by
    refine ⟨hf,?_⟩
    intro y z v hy hz
    obtain ⟨_,x,hyx,hxv⟩ := (he y v).mp hy
    obtain ⟨_,u,hzu,huv⟩ := (he z v).mp hz
    have hxu := hT.2 x u v hxv huv
    subst u
    exact hInverse.1.2 y z x hyx hzu
  have hSub : (Project.FirstOrderSemantics.reduct M).MemberSubset S I := by
    intro y hy
    obtain ⟨x,hxy⟩ := (hRange y).mp hy
    exact hS.1.output_mem_of_pairMember hxy
  refine ⟨S,f,hSub,hSize,hInj,?_⟩
  intro x y z hxy hxz
  exact (he y z).mpr ⟨(hRange y).mpr ⟨x,hxy⟩,x,(hInvEdges y x).mpr hxy,hxz⟩

/-- Source permutation_over_root at the infinite budget used by concrete T.
The SAME position b in BOTH subdiagrams is retained explicitly. -/
theorem permutation_over_root (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w mu D I mul s t p b : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hMu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hLarge : ¬ Small I mu) (hSmall : Small D mu)
    (hs : Injection D I s) (ht : Injection D I t)
    (hLeft : LeftInjection D mul b) (hSubS : Sub D mul s b p) (hSubT : Sub D mul t b p) :
    ∃ pi, Permutation I pi ∧ CompositionGraph D pi s t ∧ FixesRange D p pi := by
  obtain ⟨S,f,hSI,hSize,hf,hMatch⟩ := between_diagrams hM hs ht hSmall
  obtain ⟨pi,hpi,hExt⟩ := ConstructionPlacementExtensions.extend_permutation hM hChoice
    hw hMu hLarge hSI hSize hf
  have hGraph : CompositionGraph D pi s t := by
    intro x z
    constructor
    · intro hxz
      have hx := ForcingConditionGraphs.function_input ht.1.1 hxz
      obtain ⟨y,hxy,_⟩ := hs.1.1.2 x hx
      exact ⟨hx,y,hxy,hExt y z (hMatch x y z hxy hxz)⟩
    · rintro ⟨hx,y,hxy,hyz⟩
      obtain ⟨v,hxv,_⟩ := ht.1.1.2 x hx
      have hyv := hExt y v (hMatch x y v hxy hxv)
      have he := ForcingConditionGraphs.function_unique hpi.1.1 hyz hyv
      simpa only [he] using hxv
  refine ⟨pi,hpi,hGraph,?_⟩
  rintro z ⟨x,hx,hxz⟩
  obtain ⟨_,n,hn,hbn,hnz⟩ := (hSubS x z).mp hxz
  obtain ⟨_,m,_,hbm,hmz⟩ := (hSubT x z).mp hxz
  have he := hLeft.2.1 x n m hx hbn hbm
  subst m
  obtain ⟨_,y,hny,hyz⟩ := (hGraph n z).mp hmz
  have hf := ForcingConditionGraphs.function_unique hs.1.1 hny hnz
  exact hf ▸ hyz

/-- Original ExactOverlap: either disjoint ranges, or the exact range of
a common subdiagram at specified internal positions. -/
def ExactOverlap (D I mul r s : M.Carrier .set) : Prop :=
  (∀ z, ¬ (ImageAt r D z ∧ ImageAt s D z)) ∨
    ∃ a b p, (Project.FirstOrderSemantics.reduct M).mem a D ∧
      (Project.FirstOrderSemantics.reduct M).mem b D ∧ Injection D I p ∧
      Sub D mul r a p ∧ Sub D mul s b p ∧ RangeIntersection D r s p

theorem exactOverlap_symm {D I mul r s : M.Carrier .set}
    (h : ExactOverlap D I mul r s) : ExactOverlap D I mul s r := by
  rcases h with h | ⟨a,b,p,ha,hb,hp,hr,hs,hInter⟩
  · exact Or.inl (fun z hz => h z ⟨hz.2,hz.1⟩)
  · exact Or.inr ⟨b,a,p,hb,ha,hp,hs,hr,fun z => by
      have hi := hInter z
      exact ⟨fun hz => hi.mp ⟨hz.2,hz.1⟩,fun hz => by obtain ⟨hr,hs⟩ := hi.mpr hz; exact ⟨hs,hr⟩⟩⟩

theorem exactOverlap_of_common {D I mul r s p : M.Carrier .set}
    (hp : Injection D I p) (hr : ForcingDiagramOrder.Le D mul r p)
    (hs : ForcingDiagramOrder.Le D mul s p) (hInter : RangeIntersection D r s p) :
    ExactOverlap D I mul r s := by
  obtain ⟨a,ha,hra⟩ := hr
  obtain ⟨b,hb,hsb⟩ := hs
  exact Or.inr ⟨a,b,p,ha,hb,hp,hra,hsb,hInter⟩

def AgreesOnRange (D r pi rho : M.Carrier .set) : Prop :=
  ∀ y, ImageAt r D y → ∀ z,
    (PureKuratowski.PairMember M y z pi ↔ PureKuratowski.PairMember M y z rho)

theorem permute_eq_of_agree (hM : FirstOrder.Theory.Models M nativeZF)
    {D I r pi rho s t : M.Carrier .set}
    (hs : Injection D I s) (ht : Injection D I t)
    (hpi : CompositionGraph D pi r s) (hrho : CompositionGraph D rho r t)
    (hAgree : AgreesOnRange D r pi rho) : s = t := by
  apply ForcingDiagramPoset.injection_ext hM hs ht
  intro x z
  constructor
  · intro hxz
    obtain ⟨hx,y,hxy,hyz⟩ := (hpi x z).mp hxz
    exact (hrho x z).mpr ⟨hx,y,hxy,(hAgree y ⟨x,hx,hxy⟩ z).mp hyz⟩
  · intro hxz
    obtain ⟨hx,y,hxy,hyz⟩ := (hrho x z).mp hxz
    exact (hpi x z).mpr ⟨hx,y,hxy,(hAgree y ⟨x,hx,hxy⟩ z).mpr hyz⟩

def rangeIntersection {m : Nat} (D r s p : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.conj (ConstructionPlacementTriple.imageAt r.succ D.succ 0)
    (ConstructionPlacementTriple.imageAt s.succ D.succ 0)) (ConstructionPlacementTriple.imageAt p.succ D.succ 0))

theorem rangeIntersection_freeClosed {m : Nat} (D r s p : Fin m) : (rangeIntersection D r s p).FreeClosed := by
  simp -implicitDefEqProofs [rangeIntersection,Definitional.Formula.FreeClosed,ConstructionPlacementTriple.imageAt_freeClosed]

theorem rangeIntersection_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D r s p : Fin m) :
    Project.Formula.satisfies env (rangeIntersection D r s p) ↔
      RangeIntersection (env.bound D) (env.bound r) (env.bound s) (env.bound p) := by
  simp only [rangeIntersection,RangeIntersection,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,ConstructionPlacementTriple.imageAt_semantics hM]
  rfl

def coneEquality {m : Nat} (D mul a b c : Fin m) : Project.Formula 1 m :=
  .forallE (.imp (.mem (.bound 0) (.bound D.succ))
    (.iff (.conj (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ mul.succ a.succ 0))
      (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ mul.succ b.succ 0)))
      (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ mul.succ c.succ 0))))

theorem coneEquality_freeClosed {m : Nat} (D mul a b c : Fin m) : (coneEquality D mul a b c).FreeClosed := by
  simp -implicitDefEqProofs [coneEquality,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem coneEquality_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul a b c : Fin m) :
    Project.Formula.satisfies env (coneEquality D mul a b c) ↔
      ConeEquality (env.bound D) (env.bound mul) (env.bound a) (env.bound b) (env.bound c) := by
  simp only [coneEquality,ConeEquality,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionBaseMonoid.divides_semantics (M := M),Project.Term.eval_bound]
  rfl

def labelCones {m : Nat} (D mul r s a b : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.imp (.mem (.bound 1) (.bound D.succ.succ))
    (.imp (.mem (.bound 0) (.bound D.succ.succ))
      (.iff (.existsE (.conj
        (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 2) (.bound 0) (.bound r.succ.succ.succ))
        (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) (.bound 0) (.bound s.succ.succ.succ))))
        (.existsE (.conj (.mem (.bound 0) (.bound D.succ.succ.succ))
          (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product mul.succ.succ.succ a.succ.succ.succ 0 2))
            (ProjectSyntax.encode id (ForcingDiagramOrder.product mul.succ.succ.succ b.succ.succ.succ 0 1)))))))))

theorem labelCones_freeClosed {m : Nat} (D mul r s a b : Fin m) : (labelCones D mul r s a b).FreeClosed := by
  simp -implicitDefEqProofs [labelCones,Definitional.Formula.FreeClosed,
    Project.Formula.orderedPairMem_freeClosed,ProjectSyntax.freeClosed]

theorem labelCones_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul r s a b : Fin m) :
    Project.Formula.satisfies env (labelCones D mul r s a b) ↔
      LabelCones (env.bound D) (env.bound mul) (env.bound r) (env.bound s) (env.bound a) (env.bound b) := by
  simp only [labelCones,LabelCones,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramOrder.product_semantics (M := M),Project.Term.eval_bound]
  rfl

def fixesRange {m : Nat} (D p pi : Fin m) : Project.Formula 1 m :=
  .forallE (.imp (ConstructionPlacementTriple.imageAt p.succ D.succ 0)
    (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 0) (.bound 0) (.bound pi.succ)))

theorem fixesRange_freeClosed {m : Nat} (D p pi : Fin m) : (fixesRange D p pi).FreeClosed := by
  simp -implicitDefEqProofs [fixesRange,Definitional.Formula.FreeClosed,
    ConstructionPlacementTriple.imageAt_freeClosed,Project.Formula.orderedPairMem_freeClosed]

theorem fixesRange_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D p pi : Fin m) :
    Project.Formula.satisfies env (fixesRange D p pi) ↔
      FixesRange (env.bound D) (env.bound p) (env.bound pi) := by
  simp only [fixesRange,FixesRange,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    ConstructionPlacementTriple.imageAt_semantics hM,
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound]
  rfl

def exactOverlap {m : Nat} (D I mul r s : Fin m) : Project.Formula 1 m :=
  .disj (.forallE (.neg (.conj (ConstructionPlacementTriple.imageAt r.succ D.succ 0)
    (ConstructionPlacementTriple.imageAt s.succ D.succ 0))))
    (.existsE (.existsE (.existsE (.conj (.mem (.bound 2) (.bound D.succ.succ.succ))
      (.conj (.mem (.bound 1) (.bound D.succ.succ.succ))
        (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection 0 D.succ.succ.succ I.succ.succ.succ))
          (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.sub D.succ.succ.succ mul.succ.succ.succ r.succ.succ.succ 2 0))
            (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.sub D.succ.succ.succ mul.succ.succ.succ s.succ.succ.succ 1 0))
              (rangeIntersection D.succ.succ.succ r.succ.succ.succ s.succ.succ.succ 0)))))))))

theorem exactOverlap_freeClosed {m : Nat} (D I mul r s : Fin m) : (exactOverlap D I mul r s).FreeClosed := by
  simp -implicitDefEqProofs [exactOverlap,Definitional.Formula.FreeClosed,
    ConstructionPlacementTriple.imageAt_freeClosed,ProjectSyntax.freeClosed,rangeIntersection_freeClosed]

theorem exactOverlap_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul r s : Fin m) :
    Project.Formula.satisfies env (exactOverlap D I mul r s) ↔
      ExactOverlap (env.bound D) (env.bound I) (env.bound mul) (env.bound r) (env.bound s) := by
  simp only [exactOverlap,ExactOverlap,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,
    ConstructionPlacementTriple.imageAt_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    rangeIntersection_semantics hM,Project.Term.eval_bound]
  rfl

def agreesOnRange {m : Nat} (D r pi rho : Fin m) : Project.Formula 1 m :=
  .forallE (.imp (ConstructionPlacementTriple.imageAt r.succ D.succ 0)
    (.forallE (.iff
      (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) (.bound 0) (.bound pi.succ.succ))
      (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) (.bound 0) (.bound rho.succ.succ)))))

theorem agreesOnRange_freeClosed {m : Nat} (D r pi rho : Fin m) : (agreesOnRange D r pi rho).FreeClosed := by
  simp -implicitDefEqProofs [agreesOnRange,Definitional.Formula.FreeClosed,
    ConstructionPlacementTriple.imageAt_freeClosed,Project.Formula.orderedPairMem_freeClosed]

theorem agreesOnRange_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D r pi rho : Fin m) :
    Project.Formula.satisfies env (agreesOnRange D r pi rho) ↔
      AgreesOnRange (env.bound D) (env.bound r) (env.bound pi) (env.bound rho) := by
  simp only [agreesOnRange,AgreesOnRange,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_iff_iff,ConstructionPlacementTriple.imageAt_semantics hM,
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),Project.Term.eval_bound]
  rfl

def rangeSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 10
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection (3 : Fin 10) 0 1)) (.imp
    (ProjectSyntax.encode id (ForcingDiagramOrder.sub (0 : Fin 10) 2 3 7 4)) (.imp (ProjectSyntax.encode id
    (ForcingDiagramOrder.sub (0 : Fin 10) 2 3 8 5)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub
    (0 : Fin 10) 2 3 9 6)) (.imp (coneEquality (0 : Fin 10) 2 7 8 9) (rangeIntersection (0 : Fin 10) 4 5
    6))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      coneEquality_freeClosed,rangeIntersection_freeClosed]

theorem range_models (hM : FirstOrder.Theory.Models M nativeZF)
    :
    (Project.fo_sentence rangeSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) rangeSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    coneEquality_semantics hM,rangeIntersection_semantics hM]
  exact fun hr ha hb hc h => range_inter_sub hr ha hb hc h

theorem range_kernel_certificate : FirstOrder.Derives nativeZF [] (Project.fo_sentence rangeSentence) :=
  ModelTransfer.derives (fun _ hM => range_models hM)

def commonSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 8
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection (3 : Fin 8) 0 1)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.injection (4 : Fin 8) 0 1)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.injection (7 : Fin 8) 0 1)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub
    (0 : Fin 8) 2 3 5 7)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub (0 : Fin 8) 2 4 6 7))
    (.imp (rangeIntersection (0 : Fin 8) 3 4 7) (labelCones (0 : Fin 8) 2 3 4 5 6)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      rangeIntersection_freeClosed,labelCones_freeClosed]

theorem common_models (hM : FirstOrder.Theory.Models M nativeZF)
    :
    (Project.fo_sentence commonSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) commonSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    rangeIntersection_semantics hM,labelCones_semantics hM]
  exact fun hr hs hp ha hb h => equal_iff_of_common_sub hr hs hp ha hb h

theorem common_kernel_certificate : FirstOrder.Derives nativeZF [] (Project.fo_sentence commonSentence) :=
  ModelTransfer.derives (fun _ hM => common_models hM)

def overlapSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 6
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection (3 : Fin 6) 0 1)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.injection (4 : Fin 6) 0 1)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.injection (5 : Fin 6) 0 1)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.le
    (0 : Fin 6) 2 3 5)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.le (0 : Fin 6) 2 4 5)) (.imp
    (rangeIntersection (0 : Fin 6) 3 4 5) (exactOverlap (0 : Fin 6) 1 2 3 4)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      rangeIntersection_freeClosed,exactOverlap_freeClosed]

theorem overlap_models (hM : FirstOrder.Theory.Models M nativeZF)
    :
    (Project.fo_sentence overlapSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) overlapSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.injection_semantics (M := M),ForcingDiagramOrder.le_semantics (M := M),
    rangeIntersection_semantics hM,exactOverlap_semantics hM]
  exact fun _ _ hp hr hs h => exactOverlap_of_common hp hr hs h

theorem overlap_kernel_certificate : FirstOrder.Derives nativeZF [] (Project.fo_sentence overlapSentence) :=
  ModelTransfer.derives (fun _ hM => overlap_models hM)

def agreeSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 7
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection (2 : Fin 7) 0 1)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.injection (5 : Fin 7) 0 1)) (.imp (ProjectSyntax.encode id
    (Source.SetLanguage.injection (6 : Fin 7) 0 1)) (.imp (ProjectSyntax.encode id
    (ForcingConditionGraphs.permutation (1 : Fin 7) 3)) (.imp (ProjectSyntax.encode id
    (ForcingConditionGraphs.permutation (1 : Fin 7) 4)) (.imp (ProjectSyntax.encode id
    (ForcingConditionGraphs.compositionGraph (0 : Fin 7) 3 2 5)) (.imp (ProjectSyntax.encode id
    (ForcingConditionGraphs.compositionGraph (0 : Fin 7) 4 2 6)) (.imp (agreesOnRange (0 : Fin 7) 2 3 4)
    (Project.Formula.extensionalEq (.bound (5 : Fin 7)) (.bound 6))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      agreesOnRange_freeClosed,Project.Formula.extensionalEq]

theorem agree_models (hM : FirstOrder.Theory.Models M nativeZF)
    :
    (Project.fo_sentence agreeSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) agreeSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.injection_semantics (M := M),ForcingConditionGraphs.permutation_semantics (M := M),
    ForcingConditionGraphs.compositionGraph_semantics (M := M),agreesOnRange_semantics hM,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  exact fun _ hs ht _ _ hpi hrho h => permute_eq_of_agree hM hs ht hpi hrho h

theorem agree_kernel_certificate : FirstOrder.Derives nativeZF [] (Project.fo_sentence agreeSentence) :=
  ModelTransfer.derives (fun _ hM => agree_models hM)

def rootSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 9
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 9))) (.imp (Project.Formula.isInfiniteCardinal
    PureKuratowskiProject.convention (.bound (0 : Fin 9)) (.bound 1)) (.imp (.neg (ProjectSyntax.encode id
    (ForcingSupportSize.small (3 : Fin 9) 1))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (2 :
    Fin 9) 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection (5 : Fin 9) 2 3)) (.imp
    (ProjectSyntax.encode id (Source.SetLanguage.injection (6 : Fin 9) 2 3)) (.imp (ProjectSyntax.encode id
    (ForcingDiagramOrder.leftInjection (2 : Fin 9) 4 8)) (.imp (ProjectSyntax.encode id
    (ForcingDiagramOrder.sub (2 : Fin 9) 4 5 8 7)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.sub
    (2 : Fin 9) 4 6 8 7)) (.existsE (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation (3 :
    Fin 9).succ 0)) (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph (2 : Fin
    9).succ 0 (5 : Fin 9).succ (6 : Fin 9).succ)) (fixesRange (2 : Fin 9).succ (7 : Fin 9).succ
    0)))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isInfiniteCardinal,fixesRange_freeClosed]

theorem root_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence rootSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) rootSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isInfiniteCardinal_iff
      (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingDiagramOrder.leftInjection_semantics (M := M),ForcingDiagramOrder.sub_semantics (M := M),
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    fixesRange_semantics hM,Project.Term.eval_bound]
  exact fun hw hMu hLarge hSmall hs ht hLeft hSubS hSubT => permutation_over_root hM hChoice hw hMu hLarge hSmall hs ht hLeft hSubS hSubT

theorem root_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative rootSentence)) := by
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
  apply ConstructibleGround.relative_models hM rootSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) rootSentence).mp (root_models hL hChoice)

end PPAC.Migration.ConstructionDiagramPlacements
