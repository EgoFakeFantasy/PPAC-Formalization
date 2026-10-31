/- Pinned GermSelectors.TailData.detector_exists/detector_mem/detector_moved/
detector_fixed_eventually and StableSelectors.representative_eventually.
The existing internal uniformization constructs actual representative and
detector function graphs. Consumer: concrete component_selector_dense. -/
import PPAC.Migration.ConstructionCountableGerms
import PPAC.Migration.ExistingSmallUnion

namespace PPAC.Migration.ConstructionGermDetectors
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (function_input function_unique)
open ForcingSupportedNames (Range)
open ConstructionComponentCarrier (Code)
open ConstructionComponentCofinal (Chain)
open ConstructionGermCosets (Same Carrier Class Classes)
open ConstructionFractionOrder (NatLe)
open ForcingTailCovariance (TailFixes)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Point (D chain n x : M.Carrier .set) : Prop := ∃ v r a U A,
  PureKuratowski.PairMember M n v chain ∧ Code v r a U ∧ Range D r A ∧
    (Project.FirstOrderSemantics.reduct M).mem x A

def Representatives (H Q reps : M.Carrier .set) : Prop := MapsTo Q H reps ∧
  ∀ C pi, PureKuratowski.PairMember M C pi reps → (Project.FirstOrderSemantics.reduct M).mem pi C

def Nonidentity (w D chain Q reps N : M.Carrier .set) : Prop := ∀ C,
  (Project.FirstOrderSemantics.reduct M).mem C N ↔
    (Project.FirstOrderSemantics.reduct M).mem C Q ∧ ∃ pi,
      PureKuratowski.PairMember M C pi reps ∧ ¬ TailFixes w D pi chain

def Detects (D chain reps p x : M.Carrier .set) : Prop := ∃ C n pi y,
  PureKuratowski.Code M p C n ∧ PureKuratowski.PairMember M C pi reps ∧
    Point D chain n x ∧ PureKuratowski.PairMember M x y pi ∧ y ≠ x

def Detectors (D I chain X reps det : M.Carrier .set) : Prop := MapsTo X I det ∧
  ∀ p x, PureKuratowski.PairMember M p x det → Detects D chain reps p x

def point {m : Nat} (D chain n x : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge chain.succ.succ.succ.succ.succ n.succ.succ.succ.succ.succ 4)) (.conj (ConstructionComponentCarrier.code 4 3 2 1) (.conj (ProjectSyntax.encode id (ForcingSupportedNames.range D.succ.succ.succ.succ.succ 3 0)) (.mem (.bound x.succ.succ.succ.succ.succ) (.bound 0))))))))))

theorem point_freeClosed {m : Nat} (D chain n x : Fin m) : (point D chain n x).FreeClosed := by
  simp -implicitDefEqProofs [point,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionComponentCarrier.code_freeClosed]

theorem point_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D chain n x : Fin m) :
    Project.Formula.satisfies env (point D chain n x) ↔ Point (env.bound D) (env.bound chain) (env.bound n) (env.bound x) := by
  simp only [point,Point,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,ConstructionComponentCarrier.code_semantics hM,ForcingSupportedNames.range_semantics (M := M)]
  rfl

def representatives {m : Nat} (H Q reps : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo reps Q H))
    (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge reps.succ.succ 1 0))
      (.mem (.bound 0) (.bound 1)))))

theorem representatives_freeClosed {m : Nat} (H Q reps : Fin m) : (representatives H Q reps).FreeClosed := by
  simp -implicitDefEqProofs [representatives,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem representatives_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (H Q reps : Fin m) :
    Project.Formula.satisfies env (representatives H Q reps) ↔ Representatives (env.bound H) (env.bound Q) (env.bound reps) := by
  simp only [representatives,Representatives,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingSupportSize.mapsTo_semantics (M := M)]
  rfl

def nonidentity {m : Nat} (w D chain Q reps N : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound N.succ)) (.conj (.mem (.bound 0) (.bound Q.succ))
    (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge reps.succ.succ 1 0))
      (.neg (ForcingTailCovariance.tailFixes w.succ.succ D.succ.succ 0 chain.succ.succ))))))

theorem nonidentity_freeClosed {m : Nat} (w D chain Q reps N : Fin m) : (nonidentity w D chain Q reps N).FreeClosed := by
  simp -implicitDefEqProofs [nonidentity,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ForcingTailCovariance.tailFixes_freeClosed]

theorem nonidentity_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D chain Q reps N : Fin m) :
    Project.Formula.satisfies env (nonidentity w D chain Q reps N) ↔ Nonidentity (env.bound w) (env.bound D) (env.bound chain) (env.bound Q) (env.bound reps) (env.bound N) := by
  simp only [nonidentity,Nonidentity,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,ForcingTailCovariance.tailFixes_semantics hM]
  rfl

def detects {m : Nat} (D chain reps p x : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.existsE
    (.conj (PureKuratowskiProject.code (.bound p.succ.succ.succ.succ) (.bound 3) (.bound 2))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge reps.succ.succ.succ.succ 3 1))
    (.conj (point D.succ.succ.succ.succ chain.succ.succ.succ.succ 2 x.succ.succ.succ.succ)
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 1 x.succ.succ.succ.succ 0))
      (.neg (Project.Formula.extensionalEq (.bound 0) (.bound x.succ.succ.succ.succ))))))))))

theorem detects_freeClosed {m : Nat} (D chain reps p x : Fin m) : (detects D chain reps p x).FreeClosed := by
  simp -implicitDefEqProofs [detects,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,point_freeClosed,PureKuratowskiProject.code,Project.Formula.extensionalEq]

theorem detects_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D chain reps p x : Fin m) :
    Project.Formula.satisfies env (detects D chain reps p x) ↔ Detects (env.bound D) (env.bound chain) (env.bound reps) (env.bound p) (env.bound x) := by
  simp only [detects,Detects,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Term.eval_bound,KuratowskiZF.code_correct hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,point_semantics hM]
  rfl

def detectors {m : Nat} (D I chain X reps det : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo det X I))
    (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge det.succ.succ 1 0))
      (detects D.succ.succ chain.succ.succ reps.succ.succ 1 0))))

theorem detectors_freeClosed {m : Nat} (D I chain X reps det : Fin m) : (detectors D I chain X reps det).FreeClosed := by
  simp -implicitDefEqProofs [detectors,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,detects_freeClosed]

theorem detectors_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I chain X reps det : Fin m) :
    Project.Formula.satisfies env (detectors D I chain X reps det) ↔ Detectors (env.bound D) (env.bound I) (env.bound chain) (env.bound X) (env.bound reps) (env.bound det) := by
  simp only [detectors,Detectors,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,ForcingSupportSize.mapsTo_semantics (M := M),detects_semantics hM]
  rfl

theorem exists_representatives (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w D I mul q zero root vertices chain H Q : M.Carrier .set}
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hC : Chain w D I mul q zero root vertices chain) (hQ : Classes w D chain H Q) :
    ∃ reps, Representatives H Q reps := by
  let schema : Project.BinarySchema 0 := { body := .mem (.bound 0) (.bound 1), freeClosed := by simp [Definitional.Formula.FreeClosed] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 0 := { bound := Fin.elim0, free := fun _ => D }
  have he C pi : schema.denote env C pi ↔ (Project.FirstOrderSemantics.reduct M).mem pi C := by
    simp [Project.BinarySchema.denote,schema,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,SetTheory.Env.push]
    rfl
  obtain ⟨reps,hr,hmem⟩ := ExistingSmallUnion.uniformize_formula_l (KuratowskiZF.interpretation hM)
    (ConstructionDirectedCardinality.models_zfc hM hChoice) schema env (X := Q) (Y := H) (by
      intro C hCQ
      obtain ⟨pi,hpi,hClass⟩ := (hQ C).mp hCQ
      exact ⟨pi,hpi,(he C pi).mpr ((hClass pi).mpr ⟨hpi,ConstructionGermCosets.same_refl hM hzw hC⟩)⟩)
  exact ⟨reps,(ForcingSupportSize.native_mapsTo hM Q H reps).mpr hr,fun C pi hp => (he C pi).mp (hmem C pi hp)⟩

theorem exists_nonidentity (hM : FirstOrder.Theory.Models M nativeZF) (w D chain Q reps : M.Carrier .set) :
    ∃ N, Nonidentity w D chain Q reps N := by
  let schema : Project.UnarySchema 4 := {
    body := .existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 5 1 0))
      (.neg (ForcingTailCovariance.tailFixes 2 3 0 4)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ForcingTailCovariance.tailFixes_freeClosed] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases chain (fun _ => reps))), free := fun _ => D }
  have he C : schema.denote env C ↔ ∃ pi, PureKuratowski.PairMember M C pi reps ∧ ¬ TailFixes w D pi chain := by
    simp only [Project.UnarySchema.denote,schema,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
      Project.Formula.satisfies_neg_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
      KuratowskiZF.source_edge,ForcingTailCovariance.tailFixes_semantics hM]
    rfl
  obtain ⟨N,hN⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env Q
  exact ⟨N,fun C => (hN C).trans (and_congr_right fun _ => he C)⟩

theorem detector_exists (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain H Q reps N X p : M.Carrier .set}
    (hC : Chain w D I mul q zero root vertices chain) (hH : Carrier D I mul q root H)
    (hReps : Representatives H Q reps) (hN : Nonidentity w D chain Q reps N)
    (hX : (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) X N w)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p X) :
    ∃ x, (Project.FirstOrderSemantics.reduct M).mem x I ∧ Detects D chain reps p x := by
  classical
  obtain ⟨C,hCN,n,hn,hp⟩ := (hX p).mp hp
  obtain ⟨_,pi,hpi,hnot⟩ := (hN C).mp hCN
  have hPerm := ((hH pi).mp (hReps.1.2 C pi hpi)).1
  obtain ⟨v,hv,_⟩ := hC.1.1.2 n hn
  obtain ⟨r,a,U,A,hCode,hA,hAI⟩ := ConstructionGermCosets.stage_range hM hC hv
  have hx : ∃ x, (Project.FirstOrderSemantics.reduct M).mem x A ∧ ¬ PureKuratowski.PairMember M x x pi := by
    apply Classical.byContradiction
    intro hnone
    apply hnot
    refine ⟨n,v,r,a,U,A,hn,hv,hCode,hA,?_⟩
    intro x hx
    apply Classical.byContradiction
    intro hbad
    exact hnone ⟨x,hx,hbad⟩
  obtain ⟨x,hx,hxx⟩ := hx
  obtain ⟨y,hxy,_⟩ := hPerm.1.1.2 x (hAI x hx)
  exact ⟨x,hAI x hx,C,n,pi,y,hp,hpi,⟨v,r,a,U,A,hv,hCode,hA,hx⟩,hxy,
    fun he => hxx (he ▸ hxy)⟩

theorem exists_detectors (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w D I mul q zero root vertices chain H Q reps N X : M.Carrier .set}
    (hC : Chain w D I mul q zero root vertices chain) (hH : Carrier D I mul q root H)
    (hReps : Representatives H Q reps) (hN : Nonidentity w D chain Q reps N)
    (hX : (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) X N w) :
    ∃ det, Detectors D I chain X reps det := by
  let schema : Project.BinarySchema 3 := { body := detects 2 3 4 1 0, freeClosed := detects_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases D (Fin.cases chain (fun _ => reps)), free := fun _ => D }
  have he p x : schema.denote env p x ↔ Detects D chain reps p x :=
    detects_semantics hM ((env.push p).push x) 2 3 4 1 0
  obtain ⟨det,hd,hedge⟩ := ExistingSmallUnion.uniformize_formula_l (KuratowskiZF.interpretation hM)
    (ConstructionDirectedCardinality.models_zfc hM hChoice) schema env (X := X) (Y := I) (by
      intro p hp
      obtain ⟨x,hx,hdet⟩ := detector_exists hM hC hH hReps hN hX hp
      exact ⟨x,hx,(he p x).mpr hdet⟩)
  exact ⟨det,(ForcingSupportSize.native_mapsTo hM X I det).mpr hd,fun p x hx => (he p x).mp (hedge p x hx)⟩

theorem point_fixed {w D I mul q zero root vertices chain pi N n x : M.Carrier .set}
    (hC : Chain w D I mul q zero root vertices chain)
    {vN rN aN UN AN : M.Carrier .set}
    (hNv : PureKuratowski.PairMember M N vN chain) (hCodeN : Code vN rN aN UN)
    (hAN : Range D rN AN) (hFix : ForcingLabelPermutations.Fixes AN pi)
    (hNn : NatLe N n) (hx : Point D chain n x) : PureKuratowski.PairMember M x x pi := by
  obtain ⟨v,r,a,U,A,hv,hCode,hA,hx⟩ := hx
  exact ForcingTailGroup.fixes_later hC hNn hNv hv hCodeN hCode hAN hA hFix x hx

theorem point_agree {w D I mul q zero root vertices chain pi sigma N n x y : M.Carrier .set}
    (hC : Chain w D I mul q zero root vertices chain)
    {vN rN aN UN AN : M.Carrier .set}
    (hNv : PureKuratowski.PairMember M N vN chain) (hCodeN : Code vN rN aN UN)
    (hAN : Range D rN AN) (hAgree : ConstructionGermCosets.Agree AN pi sigma)
    (hNn : NatLe N n) (hx : Point D chain n x) :
    (PureKuratowski.PairMember M x y pi ↔ PureKuratowski.PairMember M x y sigma) := by
  obtain ⟨v,r,a,U,A,hv,hCode,hA,hx⟩ := hx
  exact ConstructionGermCosets.agree_later hC hNn hNv hv hCodeN hCode hAN hA hAgree x y hx

/-- Eventual fixation is a property of the coset, independent of the chosen representative. -/
theorem tail_of_same (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain pi sigma : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hC : Chain w D I mul q zero root vertices chain)
    (hSame : Same w D chain pi sigma) (hFix : TailFixes w D pi chain) : TailFixes w D sigma chain := by
  obtain ⟨N,vN,rN,aN,UN,AN,hN,hNv,hCodeN,hAN,hAgree⟩ := hSame
  obtain ⟨n,v,r,a,U,A,hn,hv,hCode,hA,hFix⟩ := hFix
  rcases ConstructionFractionOrder.nat_compare hM hw hN hn with he | hNn | hnN
  · refine ⟨n,v,r,a,U,A,hn,hv,hCode,hA,?_⟩
    intro x hx
    exact (point_agree hC hNv hCodeN hAN hAgree (Or.inl he) ⟨v,r,a,U,A,hv,hCode,hA,hx⟩).mp (hFix x hx)
  · refine ⟨n,v,r,a,U,A,hn,hv,hCode,hA,?_⟩
    intro x hx
    exact (point_agree hC hNv hCodeN hAN hAgree (Or.inr hNn) ⟨v,r,a,U,A,hv,hCode,hA,hx⟩).mp (hFix x hx)
  · refine ⟨N,vN,rN,aN,UN,AN,hN,hNv,hCodeN,hAN,?_⟩
    intro x hx
    exact (hAgree x x hx).mp (point_fixed hC hv hCode hA hFix (Or.inr hnN) ⟨vN,rN,aN,UN,AN,hNv,hCodeN,hAN,hx⟩)

theorem nonidentity_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain H Q reps N C pi : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hC : Chain w D I mul q zero root vertices chain)
    (hReps : Representatives H Q reps) (hN : Nonidentity w D chain Q reps N)
    (hCQ : (Project.FirstOrderSemantics.reduct M).mem C Q) (hClass : Class w D chain H pi C) :
    (Project.FirstOrderSemantics.reduct M).mem C N ↔ ¬ TailFixes w D pi chain := by
  obtain ⟨rep,hrep,_⟩ := hReps.1.1.2 C hCQ
  have hSame := ((hClass rep).mp (hReps.2 C rep hrep)).2
  have he : TailFixes w D pi chain ↔ TailFixes w D rep chain :=
    ⟨tail_of_same hM hw hC hSame,tail_of_same hM hw hC (ConstructionGermCosets.same_symm hSame)⟩
  constructor
  · intro hn
    obtain ⟨_,other,hother,hnot⟩ := (hN C).mp hn
    have eq := function_unique hReps.1.1 hother hrep
    subst other
    exact fun h => hnot (he.mp h)
  · intro hnot
    exact (hN C).mpr ⟨hCQ,rep,hrep,fun h => hnot (he.mpr h)⟩

/-- Source detector_fixed_eventually, for every internal natural index. -/
theorem fixed_eventually {w D I mul q zero root vertices chain X reps det pi : M.Carrier .set}
    (hC : Chain w D I mul q zero root vertices chain) (hDet : Detectors D I chain X reps det)
    (hFix : TailFixes w D pi chain) :
    ∃ N, (Project.FirstOrderSemantics.reduct M).mem N w ∧ ∀ C n p x,
      PureKuratowski.Code M p C n → PureKuratowski.PairMember M p x det → NatLe N n →
        PureKuratowski.PairMember M x x pi := by
  obtain ⟨N,vN,rN,aN,UN,AN,hN,hNv,hCodeN,hAN,hFix⟩ := hFix
  refine ⟨N,hN,?_⟩
  intro C n p x hpn hx hNn
  obtain ⟨C',n',rep,y,hp,_,hPoint,_,_⟩ := hDet.2 p x hx
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hpn hp
  exact point_fixed hC hNv hCodeN hAN hFix hNn hPoint

/-- Source representative_eventually/rawPattern_congr: same coset gives
identical actions on every detector sequence after one common internal bound. -/
theorem same_eventually {w D I mul q zero root vertices chain X reps det pi sigma : M.Carrier .set}
    (hC : Chain w D I mul q zero root vertices chain) (hDet : Detectors D I chain X reps det)
    (hSame : Same w D chain pi sigma) :
    ∃ N, (Project.FirstOrderSemantics.reduct M).mem N w ∧ ∀ C n p x y,
      PureKuratowski.Code M p C n → PureKuratowski.PairMember M p x det → NatLe N n →
        (PureKuratowski.PairMember M x y pi ↔ PureKuratowski.PairMember M x y sigma) := by
  obtain ⟨N,vN,rN,aN,UN,AN,hN,hNv,hCodeN,hAN,hAgree⟩ := hSame
  refine ⟨N,hN,?_⟩
  intro C n p x y hpn hx hNn
  obtain ⟨C',n',rep,z,hp,_,hPoint,_,_⟩ := hDet.2 p x hx
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hpn hp
  exact point_agree hC hNv hCodeN hAN hAgree hNn hPoint

def Laws (w D chain det : M.Carrier .set) : Prop :=
  (∀ pi, TailFixes w D pi chain → ∃ N, (Project.FirstOrderSemantics.reduct M).mem N w ∧ ∀ C n p x,
    PureKuratowski.Code M p C n → PureKuratowski.PairMember M p x det → NatLe N n → PureKuratowski.PairMember M x x pi) ∧
  (∀ pi sigma, Same w D chain pi sigma → ∃ N, (Project.FirstOrderSemantics.reduct M).mem N w ∧ ∀ C n p x y,
    PureKuratowski.Code M p C n → PureKuratowski.PairMember M p x det → NatLe N n →
      (PureKuratowski.PairMember M x y pi ↔ PureKuratowski.PairMember M x y sigma))

def laws {m : Nat} (w D chain det : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.imp (ForcingTailCovariance.tailFixes w.succ D.succ 0 chain.succ) (.existsE (.conj (.mem (.bound 0) (.bound w.succ.succ)) (.forallE (.forallE (.forallE (.forallE (.imp (PureKuratowskiProject.code (.bound 1) (.bound 3) (.bound 2)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge det.succ.succ.succ.succ.succ.succ 1 0)) (.imp (.disj (Project.Formula.extensionalEq (.bound 4) (.bound 2)) (.mem (.bound 4) (.bound 2))) (ProjectSyntax.encode id (Source.SetLanguage.edge 5 0 0))))))))))))) (.forallE (.forallE (.imp (ConstructionGermCosets.same w.succ.succ D.succ.succ chain.succ.succ 1 0) (.existsE (.conj (.mem (.bound 0) (.bound w.succ.succ.succ)) (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (PureKuratowskiProject.code (.bound 2) (.bound 4) (.bound 3)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge det.succ.succ.succ.succ.succ.succ.succ.succ 2 1)) (.imp (.disj (Project.Formula.extensionalEq (.bound 5) (.bound 3)) (.mem (.bound 5) (.bound 3))) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge 7 1 0)) (ProjectSyntax.encode id (Source.SetLanguage.edge 6 1 0)))))))))))))))))

theorem laws_freeClosed {m : Nat} (w D chain det : Fin m) : (laws w D chain det).FreeClosed := by
  simp -implicitDefEqProofs [laws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    PureKuratowskiProject.code,Project.Formula.extensionalEq,ForcingTailCovariance.tailFixes_freeClosed,ConstructionGermCosets.same_freeClosed]

theorem laws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D chain det : Fin m) :
    Project.Formula.satisfies env (laws w D chain det) ↔ Laws (env.bound w) (env.bound D) (env.bound chain) (env.bound det) := by
  simp only [laws,Laws,NatLe,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Term.eval_bound,KuratowskiZF.code_correct hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge,ForcingTailCovariance.tailFixes_semantics hM,ConstructionGermCosets.same_semantics hM]
  rfl

theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w D I mul q zero root vertices chain H Q : M.Carrier .set}
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hC : Chain w D I mul q zero root vertices chain)
    (hH : Carrier D I mul q root H) (hQ : Classes w D chain H Q) :
    ∃ reps N X det, Representatives H Q reps ∧ Nonidentity w D chain Q reps N ∧
      (Project.FirstOrderSemantics.reduct M).IsCartesianProduct (KuratowskiZF.interpretation hM) X N w ∧
      Detectors D I chain X reps det ∧ Laws w D chain det := by
  obtain ⟨reps,hReps⟩ := exists_representatives hM hChoice hzw hC hQ
  obtain ⟨N,hN⟩ := exists_nonidentity hM w D chain Q reps
  obtain ⟨X,hX⟩ := ZF.exists_cartesianProduct (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) N w
  obtain ⟨det,hDet⟩ := exists_detectors hM hChoice hC hH hReps hN hX
  exact ⟨reps,N,X,det,hReps,hN,hX,hDet,fun _ hp => fixed_eventually hC hDet hp,
    fun _ _ he => same_eventually hC hDet he⟩

def constructionSentence {m : Nat} (w D I mul q zero root vertices chain H Q : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (.mem (.bound zero) (.bound w)) (.imp (ConstructionComponentCofinal.chain w D I mul q zero root vertices chain) (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ConstructionGermCosets.classes w D chain H Q) (.existsE (.existsE (.existsE (.existsE (.conj (representatives H.succ.succ.succ.succ Q.succ.succ.succ.succ 3) (.conj (nonidentity w.succ.succ.succ.succ D.succ.succ.succ.succ chain.succ.succ.succ.succ Q.succ.succ.succ.succ 3 2) (.conj (Project.Formula.isCartesianProduct PureKuratowskiProject.convention (.bound 1) (.bound 2) (.bound w.succ.succ.succ.succ)) (.conj (detectors D.succ.succ.succ.succ I.succ.succ.succ.succ chain.succ.succ.succ.succ 1 3 0) (laws w.succ.succ.succ.succ D.succ.succ.succ.succ chain.succ.succ.succ.succ 0)))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ConstructionGermCosets.carrier_freeClosed,ConstructionGermCosets.classes_freeClosed,
      representatives_freeClosed,nonidentity_freeClosed,detectors_freeClosed,laws_freeClosed,Project.Formula.isCartesianProduct]

theorem construction_models {m : Nat} (w D I mul q zero root vertices chain H Q : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence w D I mul q zero root vertices chain H Q)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w D I mul q zero root vertices chain H Q)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isCartesianProduct_iff (KuratowskiZF.interpretation hM),
    ConstructionComponentCofinal.chain_semantics hM,ConstructionGermCosets.carrier_semantics hM,ConstructionGermCosets.classes_semantics hM,
    representatives_semantics hM,nonidentity_semantics hM,detectors_semantics hM,laws_semantics hM]
  exact construction hM hChoice

theorem construction_kernel_certificate {m : Nat} (w D I mul q zero root vertices chain H Q : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (constructionSentence w D I mul q zero root vertices chain H Q))) := by
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
  apply ConstructibleGround.relative_models hM (constructionSentence w D I mul q zero root vertices chain H Q)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence w D I mul q zero root vertices chain H Q)).mp (construction_models w D I mul q zero root vertices chain H Q hL hChoice)

end PPAC.Migration.ConstructionGermDetectors
